const std = @import("std");
const os = std.os;
// We'll have to make var out of these so we can reassign them in the testing
const stdin = std.io.getStdIn();
const ArrayList = std.ArrayList;
const assert = std.debug.assert;
const debug = @import("config").debug;

// var gpa = std.heap.GeneralPurposeAllocator(.{}){};
// const allocator = gpa.allocator();

const invalid_position: u64 = std.math.maxInt(u64);
const invalid_minimum: u64 = std.math.maxInt(u64);
const invalid_break_value: u64 = std.math.maxInt(u64);
const invalid_limit: u64 = std.math.maxInt(u64);
const RestartSchedulerType = enum {
    never_restart,
    always_restart,
    fixed_restart,
    reluctant_restart,
    geometric_restart,
    arithmetic_restart,
};
const AlgorithmType = enum {
    random_algorithm,
    focused_algorithm,
    walksat_algorithm,
    probsat_algorithm,
};
const Clause = struct {
    id: u64,
    pos: u64,
    literals: []i64,
};

const Watch = struct {
    binary: bool,
    blocking: i64,
    clause: *Clause,
};
const Stats = struct {
    added: u64 = 0,
    break_visited: u64 = 0,
    broken_clauses: u64 = 0,
    flipped: u64 = 0,
    made_clauses: u64 = 0,
    make_visited: u64 = 0,
    parsed: u64 = 0,
    random_walks: u64 = 0,
    restarts: u64 = 0,
    score_visited: u64 = 0,
};

const usage =
    \\usage: babywalk [ -h ] [ <input> ]
    \\
    \\where '<option>' is one of the following
    \\
    \\  -h  print this command line option summary
    \\  -n  do not print satisfying assignment (model)
    \\  -v  increase verbosity level
    \\  -q  disable all messages
    \\  -l  enable logging for debugging
    \\  --random   random literal algorithm
    \\  --focused  focused random walk algorithm
    \\  --walksat  WalkSAT algorithm
    \\  --probsat  ProbSAT algorithm
    \\
    \\  -f <flips>        limit total number of flips
    \\  -s <seed>         use '<seed>' to initialize random number generator
    \\  -t <seconds>      limit to this number of seconds
    \\  --thank <string>  hash '<string>' to random number generator seed
    \\
    \\  --always-restart      restart after each flip
    \\  --never-restart       never schedule restarts
    \\  --fixed-restart       fixed constant restart interval
    \\  --reluctant-restart   restart interval doubled reluctantly
    \\  --geometric-restart   restart interval with geometric increase
    \\  --arithmetic-restart  restart interval with arithmetic increase
    \\
    \\and '<input>' is the path to a file with a formula in DIMACS format. If
    \\'<input>' is '-' we read from '<stdin>', which is also the default. We
    \\use 'bzip2', 'gzip' and 'xz' to decompress and compress '.bz2', '.gz' or
    \\'.xz' files.
;

fn lit2Idx(lit: i64) usize {
    if (lit < 0) {
        return @as(usize, @intCast(-lit * 2 - 2));
    } else {
        return @as(usize, @intCast(lit * 2 - 1));
    }
}

var global_solver: ?*Solver = null;

const Solver = struct {
    allocator: std.mem.Allocator,
    start_time: f64 = 0,
    // Global state of the preprocessor
    variables: i64 = 0,
    found_empty_clause: bool = false,
    clauses: ArrayList(*Clause),
    occurrences: []ArrayList(*Clause) = &.{},
    watches: []ArrayList(Watch) = &.{},
    parsing_finished: bool = false,
    trail: ArrayList(i64),
    simplified: ArrayList(i64),
    unsimplified: ArrayList(i64),
    min_break_value_literals: ArrayList(i64),
    values: []i2 = &.{},
    marks: []bool = &.{},
    forced: []bool = &.{},
    propagated: u64 = 0,
    unsatisfied: ArrayList(*Clause),
    limit: u64 = invalid_limit,
    next_unsatisfied: u64 = 0,
    generator: u64 = 0,
    minimum: u64 = invalid_minimum,
    best: u64 = invalid_minimum,
    minimum_restarts: u64 = 0,
    minimum_flipped: u64 = 0,
    terminate: bool = false,
    termination_signal: c_int = 0,
    restart_scheduler: RestartSchedulerType = .reluctant_restart,
    base_restart_interval: u64 = 0,
    restart_interval: u64 = 0,
    next_restart: u64 = 0,
    reluctant_state: [2]u64 = .{ 1, 1 },
    algorithm: AlgorithmType = .walksat_algorithm,
    input_path: []const u8 = "<stdin>",
    input_path_seen: bool = false,
    lineno: u64 = 1,
    verbosity: i32 = 0,
    do_not_print_model: bool = false,
    thank_string: []const u8 = "",
    thank_string_seen: bool = false,
    stats: Stats = .{},
    stdout_writer: std.fs.File.Writer,
    stderr_writer: std.fs.File.Writer,
    // for debugging
    start_of_clause_lineno: u64 = 0,
    original_literals: ArrayList(i64),
    original_lineno: ArrayList(u64),
    table: ArrayList(f64),
    table_epsilon: f64 = 0,
    buffer_len: usize = 0,
    buffer: [256]u8,
    scores: ArrayList(f64),

    pub fn init(alloc: std.mem.Allocator) !Solver {
        return Solver{
            .allocator = alloc,
            // dynamic containers that need `init(allocator)`
            .clauses = std.ArrayList(*Clause).init(alloc),
            .unsatisfied = std.ArrayList(*Clause).init(alloc),
            .trail = std.ArrayList(i64).init(alloc),
            .simplified = std.ArrayList(i64).init(alloc),
            .unsimplified = std.ArrayList(i64).init(alloc),
            .min_break_value_literals = std.ArrayList(i64).init(alloc),
            .original_literals = std.ArrayList(i64).init(alloc),
            .original_lineno = std.ArrayList(u64).init(alloc),
            .scores = std.ArrayList(f64).init(alloc),
            .table = std.ArrayList(f64).init(alloc),
            .buffer = [_]u8{0} ** 256,
            .stdout_writer = std.io.getStdOut().writer(),
            .stderr_writer = std.io.getStdErr().writer(),
        };
    }
    pub fn deinit(self: *Solver) void {
        const A = self.allocator;

        // free clause-level buffers
        for (self.clauses.items) |c| {
            A.free(c.literals);
            A.destroy(c);
        }
        self.clauses.deinit();

        // dynamic ArrayLists
        self.unsatisfied.deinit();
        self.trail.deinit();
        self.simplified.deinit();
        self.unsimplified.deinit();
        self.min_break_value_literals.deinit();
        self.original_literals.deinit();
        self.original_lineno.deinit();
        self.scores.deinit();
        self.table.deinit();

        // per-literal containers
        for (self.occurrences) |*occ| occ.deinit();
        for (self.watches) |*wat| wat.deinit();
        if (self.occurrences.len != 0) A.free(self.occurrences);
        if (self.watches.len != 0) A.free(self.watches);

        // raw slices (values, marks, forced)
        if (self.values.len != 0) A.free(self.values);
        if (self.marks.len != 0) A.free(self.marks);
        if (self.forced.len != 0) A.free(self.forced);
    }
};
fn options(solver: *Solver, args: [][:0]u8) !void {
    var limit_string: []const u8 = undefined;
    var limit_string_seen = false;
    var seed_string: []const u8 = undefined;
    var seed_string_seen = false;
    var timeout_string: []const u8 = undefined;
    var timeout_string_seen = false;
    var restart_string_seen = false;
    var i: usize = 1; // the 0-th argument is the executable path
    while (i != args.len) : (i += 1) {
        var arg = args[i];
        if (std.mem.eql(u8, arg, "-h")) {
            try solver.stdout_writer.print("{s}\n", .{usage});
            return error.Help;
        } else if (std.mem.eql(u8, arg, "-v")) {
            solver.verbosity += @intFromBool(solver.verbosity != std.math.maxInt(i32));
        } else if (std.mem.eql(u8, arg, "-q")) {
            solver.verbosity = -1;
        } else if (std.mem.eql(u8, arg, "-f")) {
            i += 1;
            if (i == args.len) {
                try solver.stderr_writer.writeAll("argument to '-f' missing. (try '-h')\n");
                return error.OptionsError;
            }
            arg = args[i];
            if (limit_string_seen) {
                try solver.stderr_writer.print("multiple '-f' options ('-f {s}' and '-f {s})\n", .{ limit_string, arg });
                return error.OptionsError;
            }
            solver.limit = try std.fmt.parseUnsigned(u64, arg, 10);
            limit_string = arg;
            limit_string_seen = true;
        } else if (std.mem.eql(u8, arg, "-s")) {
            i += 1;
            if (i == args.len) {
                try solver.stderr_writer.writeAll("argument to '-s' missing. (try '-h')\n");
                return error.OptionsError;
            }
            arg = args[i];
            if (seed_string_seen) {
                try solver.stderr_writer.print("multiple '-s' options ('-s {s}' and '-s {s}')\n", .{ seed_string, arg });
                return error.OptionsError;
            }
            if (solver.thank_string_seen) {
                try solver.stderr_writer.print("can't have '--thank {s}' and '-s {s}' simultaneously", .{ solver.thank_string, arg });
                return error.OptionsError;
            }
            solver.generator = try std.fmt.parseUnsigned(u64, arg, 10);
            seed_string = arg;
            seed_string_seen = true;
        } else if (std.mem.eql(u8, arg, "--thank")) {
            i += 1;
            if (i == args.len) {
                try solver.stderr_writer.writeAll("argument to '--thank' missing. (try '-h')\n");
                return error.OptionsError;
            }
            arg = args[i];
            if (solver.thank_string_seen) {
                try solver.stderr_writer.print("multiple '--thank' options ('--thank {s}' and '--thank {s}')", .{ solver.thank_string, arg });
                return error.OptionsError;
            }
            if (seed_string_seen) {
                try solver.stderr_writer.print("'-s {s}' and '--thank {s}'", .{ seed_string, arg });
                return error.OptionsError;
            }
            solver.thank_string = arg;
            solver.thank_string_seen = true;
        } else if (std.mem.eql(u8, arg, "-t")) {
            i += 1;
            if (i == args.len) {
                try solver.stderr_writer.writeAll("argument to '-t' missing. (try '-h')\n");
                return error.OptionsError;
            }
            arg = args[i];
            if (timeout_string_seen) {
                try solver.stderr_writer.print("multiple '-t' options ('-t {s}' and '-t {s}')\n", .{ timeout_string, arg });
                return error.OptionsError;
            }
            const seconds = try std.fmt.parseUnsigned(c_uint, arg, 10);
            _ = std.c.alarm(seconds);
            timeout_string = arg;
            timeout_string_seen = true;
        } else if (std.mem.eql(u8, arg, "-l")) {
            if (debug) {
                solver.verbosity = std.math.maxInt(i32);
            } else {
                try solver.stderr_writer.writeAll("invalid option '-l' (compiled without logging support)\n");
                return error.OptionsError;
            }
        } else if (std.mem.eql(u8, arg, "-n")) {
            solver.do_not_print_model = true;
        } else if (std.mem.eql(u8, arg, "--random")) {
            solver.algorithm = AlgorithmType.random_algorithm;
        } else if (std.mem.eql(u8, arg, "--focused")) {
            solver.algorithm = AlgorithmType.focused_algorithm;
        } else if (std.mem.eql(u8, arg, "--probsat")) {
            solver.algorithm = AlgorithmType.probsat_algorithm;
        } else if (std.mem.eql(u8, arg, "--walksat")) {
            solver.algorithm = AlgorithmType.walksat_algorithm;
        } else if (std.mem.eql(u8, arg, "--always-restart")) {
            if (restart_string_seen) {
                try solver.stderr_writer.writeAll("you cannot combine different restart schedules\n");
                return error.OptionsError;
            }
            solver.restart_scheduler = RestartSchedulerType.always_restart;
            restart_string_seen = true;
        } else if (std.mem.eql(u8, arg, "--never-restart")) {
            if (restart_string_seen) {
                try solver.stderr_writer.writeAll("you cannot combine different restart schedules\n");
                return error.OptionsError;
            }
            solver.restart_scheduler = RestartSchedulerType.never_restart;
            restart_string_seen = true;
        } else if (std.mem.eql(u8, arg, "--fixed-restart")) {
            if (restart_string_seen) {
                try solver.stderr_writer.writeAll("you cannot combine different restart schedules\n");
                return error.OptionsError;
            }
            solver.restart_scheduler = RestartSchedulerType.fixed_restart;
            restart_string_seen = true;
        } else if (std.mem.eql(u8, arg, "--reluctant-restart")) {
            if (restart_string_seen) {
                try solver.stderr_writer.writeAll("you cannot combine different restart schedules\n");
                return error.OptionsError;
            }
            solver.restart_scheduler = RestartSchedulerType.reluctant_restart;
            restart_string_seen = true;
        } else if (std.mem.eql(u8, arg, "--geometric-restart")) {
            if (restart_string_seen) {
                try solver.stderr_writer.writeAll("you cannot combine different restart schedules\n");
                return error.OptionsError;
            }
            solver.restart_scheduler = RestartSchedulerType.geometric_restart;
            restart_string_seen = true;
        } else if (std.mem.eql(u8, arg, "--arithmetic-restart")) {
            if (restart_string_seen) {
                try solver.stderr_writer.writeAll("you cannot combine different restart schedules\n");
                return error.OptionsError;
            }
            solver.restart_scheduler = RestartSchedulerType.arithmetic_restart;
            restart_string_seen = true;
        } else if (arg[0] == '-') {
            try solver.stderr_writer.print("invalid option '{s}' (try '-h')\n", .{arg});
            return error.OptionsError;
        } else if (!solver.input_path_seen) {
            solver.input_path = arg;
            solver.input_path_seen = true;
        } else {
            try solver.stderr_writer.print("too many file arguments '{s}' and '{s}'\n", .{ solver.input_path, arg });
            return error.OptionsError;
        }
    }
}

fn selectReaderAndParse(solver: *Solver) !void {
    if (!solver.input_path_seen or std.mem.eql(u8, solver.input_path, "-")) {
        const reader = stdin.reader();
        solver.input_path = "<stdin>";
        try parse(solver, reader);
    } else if (hasSuffix(solver.input_path, ".bz2")) {
        try solver.stderr_writer.writeAll("bzip2 not supported. sorry.\n");
        return error.UnsupportedInputFormat;
    } else if (hasSuffix(solver.input_path, ".gz")) {
        const file = try std.fs.cwd().openFile(solver.input_path, .{});
        defer file.close();
        var gzip_decompressor = std.compress.gzip.decompressor(file.reader());
        const reader = gzip_decompressor.reader();
        try parse(solver, reader);
    } else if (hasSuffix(solver.input_path, ".zst")) {
        const file = try std.fs.cwd().openFile(solver.input_path, .{});
        defer file.close();
        const buf = try solver.allocator.alloc(u8, std.compress.zstd.DecompressorOptions.default_window_buffer_len);
        defer solver.allocator.free(buf);
        const zstd_otps = std.compress.zstd.DecompressorOptions{ .verify_checksum = true, .window_buffer = buf };
        var zstd_decompressor = std.compress.zstd.decompressor(file.reader(), zstd_otps);
        const reader = zstd_decompressor.reader();
        try parse(solver, reader);
    } else if (hasSuffix(solver.input_path, ".xz")) {
        const file = try std.fs.cwd().openFile(solver.input_path, .{});
        defer file.close();
        var xz_decompressor = try std.compress.xz.decompress(solver.allocator, file.reader());
        defer xz_decompressor.deinit();
        const reader = xz_decompressor.reader();
        try parse(solver, reader);
    } else {
        const file = try std.fs.cwd().openFile(solver.input_path, .{});
        defer file.close();
        const reader = file.reader();
        try parse(solver, reader);
    }
}

fn parse(solver: *Solver, reader: anytype) !void {
    const start = getTimeInSeconds();
    try message(solver, "reading from '{s}'", .{solver.input_path});

    var ch = try next(solver, reader);
    while (ch == 'c') : (ch = try next(solver, reader)) {
        while (ch != '\n') : (ch = try next(solver, reader)) {
            if (ch == 0) {
                try solver.stderr_writer.writeAll("unexpected end-of-file in comment\n");
                return error.ParseError;
            }
        }
    }

    if (ch != 'p') {
        try solver.stderr_writer.print("expected comment or header, got {c} ({d})\n", .{ ch, ch });
        return error.ParseError;
    }
    const header = " cnf ";
    var p: []const u8 = header[0..];
    while (p.len > 0) {
        const c = p[0];
        p = p[1..];
        if (c != try next(solver, reader)) {
            try solver.stderr_writer.writeAll("invalid header\n");
            return error.ParseError;
        }
    }
    ch = try next(solver, reader);
    try expectDigit(ch);
    solver.variables = ch - '0';
    ch = try next(solver, reader);
    while (std.ascii.isDigit(ch)) : (ch = try next(solver, reader)) {
        if (std.math.maxInt(i64) / 10 < solver.variables) {
            try solver.stderr_writer.writeAll("too many variables specified in header");
            return error.ParseError;
        }
        solver.variables *= 10;
        const digit: i64 = (ch - '0');
        if (std.math.maxInt(i64) - digit < solver.variables) {
            try solver.stderr_writer.writeAll("too many variables specified in header");
            return error.ParseError;
        }
        solver.variables += digit;
    }
    if (ch != ' ') {
        try solver.stderr_writer.writeAll("extected white space");
        return error.ParseError;
    }
    ch = try next(solver, reader);
    try expectDigit(ch);
    var expected: i64 = ch - '0';
    ch = try next(solver, reader);
    while (std.ascii.isDigit(ch)) : (ch = try next(solver, reader)) {
        if (std.math.maxInt(i64) / 10 < expected) {
            try solver.stderr_writer.writeAll("too many clauses specified in header");
            return error.ParseError;
        }
        expected *= 10;
        const digit: i64 = (ch - '0');
        if (std.math.maxInt(i64) - digit < expected) {
            try solver.stderr_writer.writeAll("too many clauses specified in header");
            return error.ParseError;
        }
        expected += digit;
    }
    if (ch != '\n') {
        try solver.stderr_writer.writeAll("expected new-line");
        return error.ParseError;
    }
    try message(solver, "found 'p cnf {d} {d}' header", .{ solver.variables, expected });
    try initializeVariables(solver);
    var lit: i64 = 0;
    if (debug) {
        solver.start_of_clause_lineno = 0;
    }
    while (true) {
        ch = try next(solver, reader);
        if (ch == ' ' or ch == '\n') continue;
        if (ch == 0) break;
        var sign: i2 = 1;
        if (ch == '-') {
            ch = try next(solver, reader);
            sign = -1;
        }
        try expectDigit(ch);
        if (debug) {
            solver.start_of_clause_lineno = solver.lineno;
        }
        if (solver.stats.parsed == expected) {
            try solver.stderr_writer.writeAll("specified clauses exceeded\n");
            return error.ParseError;
        }
        lit = ch - '0';
        ch = try next(solver, reader);
        while (std.ascii.isDigit(ch)) : (ch = try next(solver, reader)) {
            if (std.math.maxInt(i64) / 10 < lit) {
                try solver.stderr_writer.writeAll("literal too large\n");
                return error.ParseError;
            }
            lit *= 10;
            const digit = ch - '0';
            if (std.math.maxInt(i64) - @as(i64, @intCast(digit)) < lit) {
                try solver.stderr_writer.writeAll("literal too large\n");
                return error.ParseError;
            }
            lit += digit;
        }
        if (ch != ' ' and ch != '\n') {
            try solver.stderr_writer.writeAll("expected white-space\n");
            return error.ParseError;
        }
        if (lit > solver.variables) {
            try solver.stderr_writer.print("invalid variable {d}\n", .{lit});
            return error.ParseError;
        }
        lit *= sign;
        if (debug) {
            try solver.original_literals.append(lit);
        }
        if (lit != 0) {
            try solver.unsimplified.append(lit);
        } else {
            solver.stats.parsed += 1;
            try logClause(solver, &solver.unsimplified.items, "parsed", .{});
            if (!solver.found_empty_clause and !tautologicalClause(solver, &solver.unsimplified)) {
                const did_simplify = try simplifyClause(solver, &solver.simplified, &solver.unsimplified);
                if (did_simplify) {
                    try logClause(solver, &solver.simplified.items, "simplified", .{});
                }
                var c = try newClause(solver, &solver.simplified);
                const size = c.literals.len;
                if (size == 0) {
                    assert(!solver.found_empty_clause);
                    try verbose(solver, 1, "found_empty_clause", .{});
                    solver.found_empty_clause = true;
                } else if (size == 1) {
                    const unit = c.literals[0];
                    try logClause(solver, &c.literals, "found unit", .{});
                    try rootLevelAssign(solver, unit, c);
                    const ok = try rootLevelPropagate(solver);
                    if (!ok) {
                        solver.found_empty_clause = true;
                        try verbose(solver, 1, "root-level propagation yields conflict", .{});
                        assert(solver.found_empty_clause);
                    }
                    solver.allocator.free(c.literals);
                    solver.allocator.destroy(c);
                }
            }
            solver.unsimplified.shrinkRetainingCapacity(0);
            if (debug) {
                try solver.original_lineno.append(solver.start_of_clause_lineno);
            }
        }
    }
    if (lit != 0) {
        try solver.stdout_writer.writeAll("zero missing\n");
        return error.ParseError;
    }
    if (solver.stats.parsed != expected) {
        try solver.stdout_writer.writeAll("clause missing\n");
        return error.ParseError;
    }

    try message(solver, "parsed {d} clauses in {d:.2} seconds", .{ solver.stats.parsed, getTimeInSeconds() - start });
    solver.parsing_finished = true;
}

fn simplify(solver: *Solver) !void {
    if (solver.found_empty_clause) return;
    for (0..2 * @as(usize, @intCast(solver.variables))) |i| {
        try solver.occurrences[i].resize(0);
        try solver.watches[i].resize(0);
    }
    const begin: [*]*Clause = solver.clauses.items.ptr;
    const end: [*]*Clause = solver.clauses.items.ptr + solver.clauses.items.len;
    var j = begin;
    var i = j;
    continue_with_next_clause: while (i != end) {
        j[0] = i[0];
        i += 1;
        var c = j[0];
        j += 1;
        try solver.simplified.resize(0);
        var new_size: usize = 0;
        for (c.literals) |lit| {
            const value = solver.values[lit2Idx(lit)];
            if (value > 0) {
                j -= 1;
                try deleteClause(solver, c);
                continue :continue_with_next_clause;
            }
            if (value == 0) try solver.simplified.append(lit);
        }
        new_size = solver.simplified.items.len;
        assert(new_size > 1);
        if (new_size < c.literals.len) {
            try logClause(solver, &c.literals, "unsimplified", .{});
            for (solver.simplified.items, 0..) |lit, idx| {
                c.literals[idx] = lit;
            }
            c.literals = try solver.allocator.realloc(c.literals, new_size);
            assert(c.literals.len == new_size);
            try logClause(solver, &c.literals, "simplified", .{});
        }
        try connectClause(solver, c);
    }
    try solver.clauses.resize((@intFromPtr(j) - @intFromPtr(begin)) / @sizeOf(*Clause));
    try solver.trail.resize(0);
    solver.propagated = 0;
    // assert(level == 0); // have not implemented level
}

fn message(solver: *Solver, comptime fmt: []const u8, args: anytype) !void {
    if (solver.verbosity < 0)
        return;
    try solver.stdout_writer.writeAll("c ");
    try solver.stdout_writer.print(fmt, args);
    try solver.stdout_writer.writeAll("\n");
}
fn banner(solver: *Solver) !void {
    try message(solver, "BabyWalk Local Search SAT Solver", .{});
}
fn verbose(solver: *Solver, trigger_at_v: i32, comptime fmt: []const u8, args: anytype) !void {
    if (trigger_at_v > solver.verbosity)
        return;
    try solver.stdout_writer.writeAll("c ");
    try solver.stdout_writer.print(fmt, args);
    try solver.stdout_writer.writeAll("\n");
}
fn catchSignal(sig: c_int) callconv(.C) void {
    if (global_solver) |solver| {
        solver.termination_signal = sig;
        solver.terminate = true;
        if (!solver.parsing_finished) {
            solver.stdout_writer.print("c terminated by {s}\n", .{describeSignal(global_solver.?)}) catch {};
            solver.deinit();
            std.process.abort();
        }
    }
}

fn setupSigaction(solver: *Solver) void {
    _ = solver;
    const action = os.linux.Sigaction{
        .handler = .{ .handler = catchSignal },
        .mask = os.linux.empty_sigset,
        .flags = 0,
    };
    _ = os.linux.sigaction(os.linux.SIG.ALRM, &action, null);
    _ = os.linux.sigaction(os.linux.SIG.INT, &action, null);
    _ = os.linux.sigaction(os.linux.SIG.SEGV, &action, null);
    _ = os.linux.sigaction(os.linux.SIG.TERM, &action, null);
}

fn goodbye(solver: *Solver, result: u8) !void {
    if (solver.thank_string_seen) {
        try message(solver, "{s}solved thanks to '{s}'", .{ if (result != 0) "" else "un", solver.thank_string });
    }
    try message(solver, "exit {d}", .{result});
}

/// We specify `reader` to be `anytype` to accunt for many types of
/// readers, compressed and uncompressed.
fn next(solver: *Solver, reader: anytype) !u8 {
    var ch = reader.readByte() catch 0;
    if (ch == '\r') {
        ch = reader.readByte() catch 0;
        if (ch != '\n') {
            try solver.stderr_writer.writeAll("expected new-line after carriage return\n");
            return error.NoNewLineAfterCarriageReturn;
        }
    }
    if (ch == '\n')
        solver.lineno += 1;
    return ch;
}

fn rootLevelPropagate(solver: *Solver) !bool {
    assert(!solver.found_empty_clause);
    while (solver.propagated != solver.trail.items.len) {
        const lit = solver.trail.items[solver.propagated];
        solver.propagated += 1;
        try log(solver, "root-level propagating {d}", .{lit});
        const not_lit = -lit;
        var ws = &solver.watches[lit2Idx(not_lit)];
        const begin = ws.items.ptr;
        const end = ws.items.ptr + ws.items.len;
        var i = begin;
        var j = i;
        while (i != end) {
            j[0] = i[0];
            i += 1;
            const w = j[0];
            j += 1;
            const blocking = w.blocking;
            const blocking_value = solver.values[lit2Idx(blocking)];
            if (blocking_value > 0) continue;
            const c = w.clause;
            if (w.binary) {
                if (blocking_value < 0) {
                    try logClause(solver, &c.literals, "root-level conflicting", .{});
                    return false;
                } else {
                    try rootLevelAssign(solver, blocking, c);
                }
            } else {
                assert(c.literals.len > 2);
                const literals = c.literals;
                const other = literals[0] ^ literals[1] ^ not_lit;
                const other_value = solver.values[lit2Idx(other)];
                if (other_value > 0) {
                    const tmp = j - 1; // We cannot do j[-1]
                    tmp[0].blocking = other;
                    continue;
                }
                var replacement: i64 = 0;
                var replacement_value: i2 = -1;
                var r = literals.ptr + 2;
                const end_literals = literals.ptr + literals.len;
                while (r != end_literals) : (r += 1) {
                    replacement = r[0];
                    replacement_value = solver.values[lit2Idx(replacement)];
                    if (replacement_value >= 0) break;
                }
                if (replacement_value >= 0) {
                    try logClause(solver, &c.literals, "unwatching {d}", .{not_lit});
                    literals[0] = other;
                    literals[1] = replacement;
                    r[0] = not_lit;
                    try watchLiteral(solver, replacement, other, c);
                } else if (other_value != 0) {
                    try logClause(solver, &c.literals, "root-level conflicting", .{});
                    return false;
                } else {
                    try rootLevelAssign(solver, other, c);
                }
            }
        }
        while (i != end) {
            assert(false); // Should be never reached
            j[0] = i[0];
            i += 1;
            j += 1;
        }
        try ws.resize((@intFromPtr(j) - @intFromPtr(begin)) / @sizeOf(*Watch));
    }
    return true;
}

fn rootLevelAssign(solver: *Solver, lit: i64, reason: *const Clause) !void {
    try logClause(solver, &reason.literals, "root-level assign with reason: '{d}'", .{lit});
    assert(solver.values[lit2Idx(lit)] == 0);
    assert(solver.values[lit2Idx(-lit)] == 0);
    solver.values[lit2Idx(lit)] = 1;
    solver.values[lit2Idx(-lit)] = -1;
    try solver.trail.append(lit);
    solver.forced[@abs(lit)] = true;
}

fn checkSimplified(solver: *Solver, cls: *ArrayList(i64)) void {
    for (cls.items) |lit| {
        assert(solver.values[lit2Idx(lit)] == 0);
        assert(solver.marks[lit2Idx(lit)] == false);
        assert(solver.marks[lit2Idx(-lit)] == false);
        solver.marks[lit2Idx(lit)] = true;
    }
    for (cls.items) |lit| {
        solver.marks[lit2Idx(lit)] = false;
    }
}

fn connectLiteral(solver: *Solver, lit: i64, cls: *Clause) !void {
    assert(cls.literals.len > 1);
    try logClause(solver, &cls.literals, "connectLiteral: {d}", .{lit});
    try solver.occurrences[lit2Idx(lit)].append(cls);
}

fn connectClause(solver: *Solver, cls: *Clause) !void {
    assert(cls.literals.len > 1);
    for (cls.literals) |lit| {
        try connectLiteral(solver, lit, cls);
    }
}

fn newClause(solver: *Solver, literals: *ArrayList(i64)) !*Clause {
    if (debug) {
        checkSimplified(literals);
    }
    var lits = try solver.allocator.alloc(i64, literals.items.len);
    for (literals.items, 0..) |lit, idx| {
        lits[idx] = lit;
    }
    try logClause(solver, &lits, "new", .{});
    solver.stats.added += 1;
    var cls = try solver.allocator.create(Clause);
    cls.id = solver.stats.added;
    cls.pos = invalid_position;
    cls.literals = lits;
    if (cls.literals.len > 1) {
        try solver.clauses.append(cls);
        try connectClause(solver, cls);
        try watchTwoNonFalseLiteralsInClause(solver, cls);
    }
    return cls;
}

fn watchLiteral(solver: *Solver, lit: i64, blocking: i64, cls: *Clause) !void {
    try logClause(solver, &cls.literals, "watching {d} with blocking literal {d} in", .{ lit, blocking });
    var ws = &solver.watches[lit2Idx(lit)];
    if (debug) {
        for (ws.items) |w| {
            assert(w.clause != cls);
        }
    }
    try ws.append(Watch{
        .binary = cls.literals.len == 2,
        .blocking = blocking,
        .clause = cls,
    });
}

fn watchTwoNonFalseLiteralsInClause(solver: *Solver, cls: *Clause) !void {
    assert(cls.literals.len > 1);
    try watchLiteral(solver, cls.literals[0], cls.literals[1], cls);
    try watchLiteral(solver, cls.literals[1], cls.literals[0], cls);
}

fn watchSatisfiedLiteral(solver: *Solver, lit: i64, cls: *Clause) !void {
    assert(solver.values[lit2Idx(lit)] > 0);
    assert(cls.literals.len > 1);
    const literals = cls.literals.ptr;
    const end = cls.literals.ptr + cls.literals.len;
    var l = literals;
    while (l[0] != lit) {
        assert(l != end);
        l += 1;
    }
    l[0] = literals[0];
    literals[0] = lit;
    const blocking = literals[1];
    try watchLiteral(solver, lit, blocking, cls);
}

fn logClause(solver: *Solver, cls: *const []i64, comptime format: []const u8, args: anytype) !void {
    if (debug) {
        const buf = try solver.allocator.alloc(u8, std.fmt.count(format, args));
        defer solver.allocator.free(buf);
        _ = try std.fmt.bufPrint(buf, format, args);
        if (solver.verbosity == std.math.maxInt(i32)) {
            try solver.stdout_writer.print("c LOG {s} ", .{buf});
            for (cls.*) |lit| {
                try solver.stdout_writer.print("{d} ", .{lit});
            }
            try solver.stdout_writer.writeAll("\n");
        }
    }
}

fn log(solver: *Solver, comptime fmt: []const u8, args: anytype) !void {
    if (debug) {
        if (solver.verbosity == std.math.maxInt(i32)) {
            try solver.stdout_writer.writeAll("c LOG ");
            try solver.stdout_writer.print(fmt, args);
            try solver.stdout_writer.writeAll("\n");
        }
    }
}

fn simplifyClause(solver: *Solver, dst: *ArrayList(i64), src: *ArrayList(i64)) !bool {
    dst.shrinkRetainingCapacity(0);
    for (src.items) |lit| {
        if (solver.marks[lit2Idx(lit)] == true) continue;
        if (solver.values[lit2Idx(lit)] < 0) continue;
        assert(solver.marks[lit2Idx(-lit)] == false);
        solver.marks[lit2Idx(lit)] = true;
        try dst.append(lit);
    }
    for (dst.items) |lit| {
        solver.marks[lit2Idx(lit)] = false;
    }
    return dst.items.len != src.items.len;
}

fn tautologicalClause(solver: *Solver, cls: *ArrayList(i64)) bool {
    var res = false;
    for (cls.items) |lit| {
        if (solver.marks[lit2Idx(lit)] == true) continue;
        if (solver.values[lit2Idx(lit)] > 0) {
            res = true;
            break;
        }
        if (solver.marks[lit2Idx(-lit)] == true) {
            res = true;
            break;
        }
        solver.marks[lit2Idx(lit)] = true;
    }
    for (cls.items) |lit| {
        solver.marks[lit2Idx(lit)] = false;
    }
    return res;
}

fn initializeVariables(solver: *Solver) !void {
    const v = @as(usize, @intCast(solver.variables));
    solver.occurrences = try solver.allocator.alloc(ArrayList(*Clause), 2 * v + 1);
    for (solver.occurrences) |*occ| {
        occ.* = ArrayList(*Clause).init(solver.allocator);
    }
    solver.watches = try solver.allocator.alloc(ArrayList(Watch), 2 * v + 1);
    for (solver.watches) |*wtch_lst| {
        wtch_lst.* = ArrayList(Watch).init(solver.allocator);
    }
    solver.marks = try solver.allocator.alloc(bool, 2 * v + 1);
    fill(bool, solver.marks, false);
    solver.values = try solver.allocator.alloc(i2, 2 * v + 1);
    fill(i2, solver.values, 0);
    solver.forced = try solver.allocator.alloc(bool, v + 1);
    fill(bool, solver.forced, false);
}

fn deleteClause(solver: *Solver, cls: *Clause) !void {
    try logClause(solver, &cls.literals, "delete", .{});
    solver.allocator.free(cls.literals);
    solver.allocator.destroy(cls);
}

fn next64(solver: *Solver) u64 {
    solver.generator = @mulWithOverflow(solver.generator, 6364136223846793005)[0];
    solver.generator = @addWithOverflow(solver.generator, 1442695040888963407)[0];
    assert(solver.generator != 0);
    return solver.generator;
}

fn initializeSeed(solver: *Solver) !void {
    if (solver.thank_string_seen) {
        for (solver.thank_string) |c| {
            solver.generator ^= c;
            _ = next64(solver);
        }
        try verbose(solver, 1, "hashed '{s}' to seed '{d}'", .{ solver.thank_string, solver.generator });
    }
    try message(solver, "seed {d}", .{solver.generator});
}

fn initializeRestart(solver: *Solver) !void {
    solver.restart_interval = 100 * @as(u64, @intCast(solver.variables));
    solver.base_restart_interval = solver.restart_interval;
    switch (solver.restart_scheduler) {
        .never_restart => {
            try message(solver, "never restart", .{});
        },
        .always_restart => {
            try message(solver, "always restart", .{});
        },
        .fixed_restart => {
            try message(solver, "fixed restart interval of {d}", .{solver.restart_interval});
        },
        .reluctant_restart => {
            try message(solver, "reluctant restart interval of {d}", .{solver.restart_interval});
        },
        .geometric_restart => {
            try message(solver, "geometric restart interval of {d}", .{solver.restart_interval});
        },
        .arithmetic_restart => {
            try message(solver, "arithmetic restart interval of {d}", .{solver.restart_interval});
        },
    }
    solver.next_restart = solver.stats.restarts + solver.restart_interval;
}

fn isTimeToRestart(solver: *Solver) !bool {
    if (solver.restart_scheduler == RestartSchedulerType.always_restart) return true;
    if (solver.restart_scheduler == RestartSchedulerType.never_restart) return false;
    if (solver.stats.flipped < solver.next_restart) return false;
    if (solver.restart_scheduler == RestartSchedulerType.arithmetic_restart) {
        solver.restart_interval += solver.base_restart_interval;
    } else if (solver.restart_scheduler == RestartSchedulerType.geometric_restart) {
        solver.restart_interval *= 2;
    } else if (solver.restart_scheduler == RestartSchedulerType.reluctant_restart) {
        var u = solver.reluctant_state[0];
        var v = solver.reluctant_state[1];
        if ((u & (~u + 1)) == v) {
            u += 1;
            v = 1;
        } else {
            v *= 2;
        }
        solver.restart_interval = v * solver.base_restart_interval;
        solver.reluctant_state[0] = u;
        solver.reluctant_state[1] = v;
        try verbose(solver, 3, "reluctant u: {d} v: {d}", .{ u, v });
    } else {
        assert(solver.restart_scheduler == RestartSchedulerType.fixed_restart);
    }
    solver.next_restart = solver.stats.flipped + solver.restart_interval;
    return true;
}

fn pickRandomFalsifiedLiteral(solver: *Solver) i64 {
    var res = pickModular(solver, @as(u64, @intCast(solver.variables))) + 1;
    while (solver.forced[res]) {
        res = pickModular(solver, @as(u64, @intCast(solver.variables))) + 1;
    }
    var res_int = @as(i64, @intCast(res));
    if (solver.values[lit2Idx(res_int)] > 0) {
        res_int = -res_int;
    }
    return res_int;
}

fn makeClauses(solver: *Solver, lit: i64) !void {
    if (solver.occurrences[lit2Idx(lit)].items.len < solver.unsatisfied.items.len) {
        try makeClausesAlongOccurrences(solver, lit);
    } else {
        try makeClausesAlongUnsatisfied(solver, lit);
    }
}

fn makeClausesAlongOccurrences(solver: *Solver, lit: i64) !void {
    var made: usize = 0;
    var visited: usize = 0;
    assert(solver.values[lit2Idx(lit)] > 0);
    const occs = solver.occurrences[lit2Idx(lit)];
    try log(solver, "making clauses with {d} along with {d} occurrences", .{ lit, occs.items.len });
    for (occs.items) |c| {
        const unsatisfied_size = solver.unsatisfied.items.len;
        if (unsatisfied_size == 0) break;
        visited += 1;
        if (c.pos >= unsatisfied_size) continue;
        assert(solver.unsatisfied.items[c.pos] == c);
        if (c.pos != unsatisfied_size - 1) {
            var d = solver.unsatisfied.getLast();
            d.pos = c.pos;
            solver.unsatisfied.items[d.pos] = d;
        }
        _ = solver.unsatisfied.pop();
        try makeClause(solver, c, lit);
        made += 1;
    }
    solver.stats.made_clauses += made;
    solver.stats.make_visited += visited;
    try log(solver, "made {d} clauses with flipped {d}", .{ made, lit });
}

fn makeClause(solver: *Solver, cls: *Clause, lit: i64) !void {
    try logClause(solver, &cls.literals, "made by {d}", .{lit});
    cls.pos = invalid_position;
    try watchSatisfiedLiteral(solver, lit, cls);
}

fn makeClausesAlongUnsatisfied(solver: *Solver, lit: i64) !void {
    try log(solver, "making clauses with {d} along {d} unsatisfied", .{ lit, solver.unsatisfied.items.len });
    assert(solver.values[lit2Idx(lit)] > 0);
    var made: usize = 0;
    var visited: usize = 0;
    const begin = solver.unsatisfied.items.ptr;
    const end = solver.unsatisfied.items.ptr + solver.unsatisfied.items.len;
    var j = begin;
    var i = j;
    while (i != end) {
        const c = i[0];
        i += 1;
        visited += 1;
        if (contains(c, lit)) {
            try makeClause(solver, c, lit);
            made += 1;
        } else if (i != j) {
            c.pos = (@intFromPtr(j) - @intFromPtr(begin)) / @sizeOf(*Clause);
            j[0] = c;
            j += 1;
        } else {
            j += 1;
        }
    }
    try solver.unsatisfied.resize((@intFromPtr(j) - @intFromPtr(begin)) / @sizeOf(*Clause));
    solver.stats.made_clauses += made;
    solver.stats.make_visited += visited;
    try log(solver, "made {d} clauses with flipped {d}", .{ made, lit });
}

fn breakClauses(solver: *Solver, lit: i64) !void {
    try log(solver, "breaking clauses with {d}", .{lit});
    assert(solver.values[lit2Idx(lit)] < 0);
    var broken: usize = 0;
    var visited: usize = 0;
    var ws = &solver.watches[lit2Idx(lit)];
    next_watch: for (ws.items) |w| {
        visited += 1;
        const c = w.clause;
        const literals = c.literals.ptr;
        const end = literals + c.literals.len;
        assert(literals[0] == lit);
        var l = literals + 1;
        while (l != end) : (l += 1) {
            const other = l[0];
            const other_value = solver.values[lit2Idx(other)];
            if (other_value > 0) {
                l[0] = lit;
                literals[0] = other;
                try watchLiteral(solver, other, lit, c);
                continue :next_watch;
            }
        }
        try breakClause(solver, c);
        broken += 1;
    }
    try ws.resize(0);
    solver.stats.broken_clauses += broken;
    solver.stats.break_visited += visited;
    try log(solver, "broken {d} clauses with flipped {d}", .{ broken, lit });
}

fn flipLiteral(solver: *Solver, lit: i64) !void {
    try log(solver, "flipping {d}", .{lit});
    assert(!solver.forced[@as(usize, @intCast(@abs(lit)))]);
    assert(solver.values[lit2Idx(lit)] < 0);
    solver.values[lit2Idx(-lit)] = -1;
    solver.values[lit2Idx(lit)] = 1;
    solver.stats.flipped += 1;
    try makeClauses(solver, lit);
    try breakClauses(solver, -lit);
    try updateMinimun(solver);
}

fn next32(solver: *Solver) u32 {
    const res: u32 = @truncate(next64(solver) >> 32);
    return res;
}

fn pickModular(solver: *Solver, mod: u64) u64 {
    assert(mod != 0);
    const tmp = next32(solver);
    const fraction = @as(f64, @floatFromInt(tmp)) / 4294967296.0;
    const res = @as(u64, @intFromFloat(@as(f64, @floatFromInt(mod)) * fraction));
    assert(res < mod);
    return res;
}

fn nextBool(solver: *Solver) bool {
    return next32(solver) < 2147483648;
}

fn satisfied(solver: *Solver, cls: *Clause) bool {
    for (cls.literals) |lit| {
        if (solver.values[lit2Idx(lit)] > 0) return true;
    }
    return false;
}

fn breakClause(solver: *Solver, cls: *Clause) !void {
    try logClause(solver, &cls.literals, "broken", .{});
    cls.pos = solver.unsatisfied.items.len;
    try solver.unsatisfied.append(cls);
}

fn restart(solver: *Solver) !void {
    try log(solver, "restarting", .{});
    solver.stats.restarts += 1;
    for (solver.watches) |*w| {
        try w.resize(0);
    }
    for (solver.unsatisfied.items) |c| {
        c.pos = invalid_position;
    }
    try solver.unsatisfied.resize(0);
    var idx: i64 = 1;
    while (idx <= solver.variables) : (idx += 1) {
        if (solver.forced[@as(usize, @intCast(idx))]) continue;
        const value: i2 = if (nextBool(solver)) -1 else 1;
        solver.values[lit2Idx(idx)] = value;
        solver.values[lit2Idx(-idx)] = -value;
        try log(solver, "assign {d} in restart", .{if (value < 0) -idx else idx});
    }
    var broken: usize = 0;
    var visited: usize = 0;
    next_watch: for (solver.clauses.items) |c| {
        visited += 1;
        assert(c.literals.len > 1);
        const literals = c.literals.ptr;
        const lit = literals[0];
        const lit_value = solver.values[lit2Idx(lit)];
        if (lit_value > 0) {
            const other = literals[1];
            try watchLiteral(solver, lit, other, c);
            continue :next_watch;
        } else {
            const end = literals + c.literals.len;
            var l = literals + 1;
            while (l != end) : (l += 1) {
                const other = l[0];
                const other_value = solver.values[lit2Idx(other)];
                if (other_value > 0) {
                    l[0] = lit;
                    literals[0] = other;
                    try watchLiteral(solver, other, lit, c);
                    continue :next_watch;
                }
            }
        }
        try breakClause(solver, c);
        broken += 1;
    }
    solver.stats.broken_clauses += broken;
    solver.stats.break_visited += visited;
    try verbose(solver, 2, "{d} clauses broken after restart {d} and {d} flipped", .{ solver.unsatisfied.items.len, solver.stats.restarts, solver.stats.flipped });
    solver.best = invalid_minimum;
    try updateMinimun(solver);
}

fn updateMinimun(solver: *Solver) !void {
    const unsatisfied_size = solver.unsatisfied.items.len;
    if (unsatisfied_size < solver.minimum) {
        solver.minimum = unsatisfied_size;
        solver.minimum_restarts = solver.stats.restarts;
        solver.minimum_flipped = solver.stats.flipped;
        try verbose(solver, 1, "minimum {d} unsatisfied clauses after {d} flipped variables and {d} restarts", .{ solver.minimum, solver.stats.flipped, solver.stats.restarts });
    }
    if (solver.restart_scheduler != RestartSchedulerType.always_restart and solver.restart_scheduler != RestartSchedulerType.never_restart) {
        if (unsatisfied_size < solver.best) {
            solver.best = unsatisfied_size;
            try verbose(solver, 3, "best {d} unsatisfied clauses after {d} flipped variables and {d} restarts", .{ solver.best, solver.stats.flipped, solver.stats.restarts });
        }
    }
}

fn randomLiteral(solver: *Solver) !void {
    try message(solver, "using random literal picking algorithm", .{});
    try restart(solver);
    while (solver.unsatisfied.items.len != 0 and solver.stats.flipped < solver.limit and !solver.terminate) {
        const is_time_to_restart = try isTimeToRestart(solver);
        if (is_time_to_restart) {
            try restart(solver);
        } else {
            const lit = pickRandomFalsifiedLiteral(solver);
            try flipLiteral(solver, lit);
        }
    }
}

fn focusedRandomWalk(solver: *Solver) !void {
    try message(solver, "using focused random walk algorithm", .{});
    try restart(solver);
    while (solver.unsatisfied.items.len != 0 and solver.stats.flipped < solver.limit and !solver.terminate) {
        const is_time_to_restart = try isTimeToRestart(solver);
        if (is_time_to_restart) {
            try restart(solver);
        } else {
            const c = try pickUnsatisfiedClause(solver);
            const lit = try pickRandomLiteralInUnsatisfiedClause(solver, c);
            try flipLiteral(solver, lit);
        }
    }
}

fn pickUnsatisfiedClause(solver: *Solver) !*Clause {
    var pos = solver.next_unsatisfied;
    solver.next_unsatisfied += 1;
    if (pos >= solver.unsatisfied.items.len) {
        pos = 0;
        solver.next_unsatisfied = 1;
    }
    const res = solver.unsatisfied.items[pos];
    try logClause(solver, &res.literals, "picked at position {d}", .{res.pos});
    return res;
}

fn pickRandomLiteralInUnsatisfiedClause(solver: *Solver, cls: *Clause) !i64 {
    assert(cls.literals.len < std.math.maxInt(usize));
    const pos = pickModular(solver, cls.literals.len);
    const res = cls.literals[pos];
    try log(solver, "random walk picked at position {d} literal {d}", .{ pos, res });
    solver.stats.random_walks += 1;
    return res;
}

fn walksat(solver: *Solver) !void {
    try message(solver, "using WALKSAT algorithm", .{});
    try restart(solver);
    while (solver.unsatisfied.items.len != 0 and solver.stats.flipped < solver.limit and !solver.terminate) {
        const is_time_to_restart = try isTimeToRestart(solver);
        if (is_time_to_restart) {
            try restart(solver);
        } else {
            const c = try pickUnsatisfiedClause(solver);
            const lit = try selectLiteralInUnsatisfiedClause(solver, c);
            try flipLiteral(solver, lit);
        }
    }
}

fn critical(solver: *Solver, cls: *Clause) bool {
    var unit: i64 = 0;
    for (cls.literals) |lit| {
        const value = solver.values[lit2Idx(lit)];
        if (value < 0) continue;
        assert(value > 0);
        if (unit != 0) {
            return false;
        }
        unit = lit;
    }
    return unit != 0;
}

fn breakValue(solver: *Solver, lit: i64, max: usize) !usize {
    assert(solver.values[lit2Idx(lit)] > 0);
    var res: usize = 0;
    var visited: usize = 0;
    next_watch: for (solver.watches[lit2Idx(lit)].items) |*w| {
        const blocking = w.blocking;
        assert(blocking != lit);
        if (solver.values[lit2Idx(blocking)] > 0) continue;
        if (!w.binary) {
            visited += 1;
            const c = w.clause;
            const literals = c.literals.ptr;
            const end = literals + c.literals.len;
            assert(literals[0] == lit);
            var l = literals + 1;
            while (l != end) : (l += 1) {
                const other = l[0];
                assert(other != lit);
                const other_value = solver.values[lit2Idx(other)];
                if (other_value > 0) {
                    w.blocking = other;
                    continue :next_watch;
                }
            }
        }
        res += 1;
        if (res == max) break;
    }
    solver.stats.score_visited += 1;
    try log(solver, "break-value {d} of literal {d}", .{ res, lit });
    return res;
}

/// Returns a random number in the range [0, 1]
fn nextDoubleInclusive(solver: *Solver) f64 {
    const res = @as(f64, @floatFromInt(next32(solver))) / 4294967295.0;
    return res;
}

/// Returns a random number in the range [0, 1)
fn nextDoubleExclusive(solver: *Solver) f64 {
    const res = @as(f64, @floatFromInt(next32(solver))) / 4294967296.0;
    return res;
}

fn selectLiteralInUnsatisfiedClause(solver: *Solver, cls: *Clause) !i64 {
    var min_break_value = @as(u64, @intCast(invalid_break_value));
    for (cls.literals) |lit| {
        const not_lit_break_value = try breakValue(solver, -lit, std.math.maxInt(usize));
        if (not_lit_break_value > min_break_value) continue;
        if (not_lit_break_value < min_break_value) {
            min_break_value = not_lit_break_value;
            try solver.min_break_value_literals.resize(0);
        }
        try solver.min_break_value_literals.append(lit);
    }
    try logClause(solver, &cls.literals, "minimum break value {d} in", .{min_break_value});
    if (min_break_value != 0) {
        const p = nextDoubleInclusive(solver);
        if (p < 0.57) { // Magic constant!
            try log(solver, "falling back to random literal in clause", .{});
            return pickRandomLiteralInUnsatisfiedClause(solver, cls);
        }
    }
    const min_break_value_literals_size = solver.min_break_value_literals.items.len;
    assert(min_break_value_literals_size <= std.math.maxInt(usize));
    const pos = pickModular(solver, min_break_value_literals_size);
    const res = solver.min_break_value_literals.items[pos];
    try log(solver, "picked at position {d} literal {d} with break-value {d}", .{ pos, res, min_break_value });
    return res;
}

fn probsat(solver: *Solver) !void {
    try message(solver, "using ProbSAT algorithm", .{});
    try initializeTable(solver);
    try restart(solver);
    while (solver.unsatisfied.items.len != 0 and solver.stats.flipped < solver.limit and !solver.terminate) {
        const c = try pickUnsatisfiedClause(solver);
        const lit = try sampleLiteralInUnsatisfiedClause(solver, c);
        try flipLiteral(solver, lit);
    }
}

fn initializeTable(solver: *Solver) !void {
    var n: f64 = 1;
    while (n != 0) {
        try solver.table.append(n);
        n *= 0.5;
    }
    assert(solver.table.items.len != 0);
    solver.table_epsilon = solver.table.items[solver.table.items.len - 1];
    try verbose(solver, 1, "initialized table of size {d} epsilon {d}", .{ solver.table.items.len, solver.table_epsilon });
}

fn sampleScore(solver: *Solver, lit: i64) !f64 {
    assert(solver.values[lit2Idx(lit)] < 0);
    const b = try breakValue(solver, -lit, std.math.maxInt(usize));
    const res: f64 = if (b < solver.table.items.len) solver.table.items[b] else solver.table_epsilon;
    try log(solver, "sample score {d} of {d} with capped break value {d}", .{ res, lit, b });
    return res;
}

fn sampleLiteralInUnsatisfiedClause(solver: *Solver, cls: *Clause) !i64 {
    var sum: f64 = 0;
    try solver.scores.resize(0);
    for (cls.literals) |lit| {
        const score = try sampleScore(solver, lit);
        try solver.scores.append(score);
        sum += score;
    }
    const sampled = sum * nextDoubleExclusive(solver);
    try log(solver, "sampled {d} {d:.2}% of sum {d}", .{ sampled, percentF(sampled, sum), sum });
    assert(sampled != sum);
    sum = 0;
    var res: i64 = 0;
    for (0..cls.literals.len) |i| {
        const lit = cls.literals[i];
        const score = solver.scores.items[i];
        sum += score;
        if (sum >= sampled) {
            res = lit;
            break;
        }
    }
    assert(res != 0);
    return res;
}

fn solve(solver: *Solver) !u8 {
    try initializeSeed(solver);
    if (solver.limit == invalid_position) {
        try message(solver, "unlimited number of flipped variables", .{});
    } else {
        try message(solver, "limit {d} on number of flipped variables", .{solver.limit});
    }
    try initializeRestart(solver);
    var res: u8 = 0;
    if (solver.found_empty_clause) {
        try solver.stdout_writer.writeAll("s UNSATISFIABLE\n");
        res = 20;
    } else {
        switch (solver.algorithm) {
            .random_algorithm => {
                try randomLiteral(solver);
            },
            .focused_algorithm => {
                try focusedRandomWalk(solver);
            },
            .walksat_algorithm => {
                try walksat(solver);
            },
            .probsat_algorithm => {
                try probsat(solver);
            },
        }
        try message(solver, "reached minimum {d} unsatisfied clauses after {d} flipped variables and {d} restarts", .{ solver.minimum, solver.minimum_flipped, solver.minimum_restarts });
        if (!solver.terminate and solver.unsatisfied.items.len == 0) {
            if (debug) {
                try checkOriginalClausesSatisfied(solver);
            }
            try solver.stdout_writer.writeAll("s SATISFIABLE\n");
            if (!solver.do_not_print_model) try printValues(solver);
            res = 10;
        } else {
            if (solver.terminate) {
                try solver.stdout_writer.print("c terminated by {s}\n", .{describeSignal(solver)});
            }
            try solver.stdout_writer.writeAll("s UNKNOWN\n");
            res = 0;
        }
    }
    return res;
}

fn describeSignal(solver: *Solver) []const u8 {
    switch (solver.termination_signal) {
        os.linux.SIG.INT => {
            return "stop signal (SIGINT)";
        },
        os.linux.SIG.KILL => {
            return "kill signal (SIGKILL)";
        },
        os.linux.SIG.SEGV => {
            return "segmentation fault signal (SIGSEGV)";
        },
        os.linux.SIG.TERM => {
            return "forced termination signal (SIGTERM)";
        },
        os.linux.SIG.ALRM => {
            return "timeout signal (SIGALRM)";
        },
        else => {
            return "unknown signal";
        },
    }
}

fn printValues(solver: *Solver) !void {
    for (1..@as(usize, @intCast(solver.variables)) + 1) |idx| {
        const i = @as(i64, @intCast(idx));
        const value = @as(i64, @intCast(solver.values[lit2Idx(i)]));
        if (value != 0) try printValue(solver, value * i);
    }
    try printValue(solver, 0);
    if (solver.buffer_len > 0) try flushBuffer(solver);
}

fn printValue(solver: *Solver, lit: i64) !void {
    var str: [32]u8 = undefined;
    const res = try std.fmt.bufPrint(&str, " {d}", .{lit});
    if (solver.buffer_len + res.len > 74) try flushBuffer(solver);
    for (res, solver.buffer_len..) |char, idx| {
        solver.buffer[idx] = char;
    }
    solver.buffer_len += res.len;
}

fn flushBuffer(solver: *Solver) !void {
    try solver.stdout_writer.writeAll("v");
    try solver.stdout_writer.print("{s}", .{solver.buffer[0..solver.buffer_len]});
    try solver.stdout_writer.writeAll("\n");
    solver.buffer_len = 0;
}

fn checkOriginalClausesSatisfied(solver: *Solver) !void {
    var start_of_last_clause: usize = 0;
    var is_satisfied: bool = false;
    var id: usize = 0;
    for (0..solver.original_literals.items.len) |i| {
        const lit = solver.original_literalsq.items[i];
        if (lit != 0) {
            if (solver.values[lit2Idx(lit)] > 0) {
                is_satisfied = true;
            }
        } else if (is_satisfied) {
            start_of_last_clause = i + 1;
            is_satisfied = false;
            id += 1;
        } else {
            try solver.stderr_writer.print("babywalk: fatal error: original clause[{d}] at line {d} unsatisfied:\n", .{ id + 1, solver.original_lineno.items[id] });
            for (start_of_last_clause..i) |j| {
                try solver.stderr_writer.print("{d} ", .{solver.original_literals.items[j]});
            }
            try solver.stderr_writer.writeAll("\n");
            return error.FatalError;
        }
    }
}
fn report(solver: *Solver) !void {
    if (solver.verbosity < 0) return;
    const elapsed = getTimeInSeconds() - solver.start_time;
    try solver.stdout_writer.print("c {s: <21} {d:13} {d:14.2} flipped/restart\n", .{ "restarts:", solver.stats.restarts, averageI(solver.stats.flipped, solver.stats.restarts) });
    try solver.stdout_writer.print("c {s: <21} {d:13} {d:14.2} per second\n", .{ "flipped-variables:", solver.stats.flipped, @as(f64, @floatFromInt(solver.stats.flipped)) / elapsed });
    try solver.stdout_writer.print("c {s: <21} {d:13} {d:14.2} % flipped\n", .{ "random-walks:", solver.stats.random_walks, percentI(solver.stats.random_walks, solver.stats.flipped) });
    try solver.stdout_writer.print("c {s: <21} {d:13} {d:14.2} per flip\n", .{ "made-clauses:", solver.stats.made_clauses, averageI(solver.stats.made_clauses, solver.stats.flipped) });
    try solver.stdout_writer.print("c {s: <21} {d:13} {d:14.2} per flip\n", .{ "make-visited:", solver.stats.make_visited, averageI(solver.stats.make_visited, solver.stats.flipped) });
    try solver.stdout_writer.print("c {s: <21} {d:13} {d:14.2} per flip\n", .{ "broken-clauses:", solver.stats.broken_clauses, averageI(solver.stats.broken_clauses, solver.stats.flipped) });
    try solver.stdout_writer.print("c {s: <21} {d:13} {d:14.2} per flip\n", .{ "break-visited:", solver.stats.break_visited, averageI(solver.stats.break_visited, solver.stats.flipped) });
    try solver.stdout_writer.print("c {s: <21} {d:28.2} seconds\n", .{ "process-time:", elapsed });
}

pub fn runSolver(solver: *Solver) !u8 {
    try banner(solver);
    try selectReaderAndParse(solver);
    try simplify(solver);
    const result = try solve(solver);
    try report(solver);
    try goodbye(solver, result);
    return result;
}

fn hasSuffix(str: []const u8, suffix: []const u8) bool {
    const k = str.len;
    const l = suffix.len;
    return k >= l and std.mem.eql(u8, str[(k - l)..k], suffix);
}

fn expectDigit(ch: u8) !void {
    if (!std.ascii.isDigit(ch)) {
        // TODO: Give error message
        return error.ParseError;
    }
}

fn getTimeInSeconds() f64 {
    const tm = std.time.microTimestamp();
    return @as(f64, @floatFromInt(tm)) / std.time.us_per_s;
}

fn fill(comptime T: type, arr: []T, elem: T) void {
    for (arr) |*item| {
        item.* = elem;
    }
}

fn contains(cls: *Clause, lit: i64) bool {
    for (cls.literals) |other| {
        if (other == lit) {
            return true;
        }
    }
    return false;
}

/// For integers
fn averageI(a: anytype, b: anytype) f64 {
    if (b == 0) {
        return 0;
    }
    return @as(f64, @floatFromInt(a)) / @as(f64, @floatFromInt(b));
}

/// For integers
fn percentI(a: anytype, b: anytype) f64 {
    return averageI(100 * a, b);
}

/// For floating point numbers
fn averageF(a: anytype, b: anytype) f64 {
    if (b == 0) {
        return 0;
    }
    return @as(f64, a) / @as(f64, b);
}

/// For floating point numbers
fn percentF(a: anytype, b: anytype) f64 {
    return averageF(100 * a, b);
}

pub fn main() !u8 {
    const allocator = std.heap.c_allocator;
    var solver = try Solver.init(allocator);
    defer solver.deinit();

    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

    options(&solver, args) catch |err| switch (err) {
        error.Help => return 0,
        else => return err,
    };

    return runSolver(&solver);
}

fn writeToFile(filename: []const u8, contents: []const u8) !void {
    const handle = try std.fs.cwd().createFile(filename, .{
        .truncate = false,
    });
    defer handle.close();
    _ = try handle.write(contents);
}

fn runTest(allocator: std.mem.Allocator, expected: u8, filename: []const u8) !void {
    const cnf_path = try std.fmt.allocPrint(allocator, "test/{s}.cnf", .{filename});
    defer allocator.free(cnf_path);
    const log_path = try std.fmt.allocPrint(allocator, "test/{s}.log", .{filename});
    defer allocator.free(log_path);
    const err_path = try std.fmt.allocPrint(allocator, "test/{s}.err", .{filename});
    defer allocator.free(err_path);
    const chm_path = try std.fmt.allocPrint(allocator, "test/{s}.chm", .{filename});
    defer allocator.free(chm_path);

    const out_file = try std.fs.cwd().createFile(log_path, .{ .truncate = true });
    defer out_file.close();
    const err_file = try std.fs.cwd().createFile(err_path, .{ .truncate = true });
    defer err_file.close();

    var solver = try Solver.init(allocator);
    defer solver.deinit();
    solver.stdout_writer = out_file.writer();
    solver.stderr_writer = err_file.writer();
    solver.input_path = cnf_path;
    solver.input_path_seen = true;

    const ret = try runSolver(&solver);

    if (ret != expected) return error.SATSolverWrongReturnCode;

    if (expected == 10) {
        const argv2 = [_][]const u8{ "zig-out/bin/checkmodel", cnf_path, log_path };
        const proc2 = try std.process.Child.run(.{
            .allocator = allocator,
            .argv = &argv2,
        });
        defer allocator.free(proc2.stdout);
        defer allocator.free(proc2.stderr);

        try writeToFile(chm_path, proc2.stdout);
        try writeToFile(err_path, proc2.stderr);
        if (proc2.term.Exited != 0) return error.CheckmodelWrongReturnCode;
    }
}

test "true" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 10, "true");
}

test "false" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 20, "false");
}

test "trivial" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 10, "trivial");
}

test "simp" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 10, "simp");
}

test "unit1" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 20, "unit1");
}

test "unit2" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 20, "unit2");
}

test "unit3" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 20, "unit3");
}

test "unit4" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 20, "unit4");
}

test "unit5" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 20, "unit5");
}

test "prime4" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 10, "prime4");
}

test "prime9" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 10, "prime9");
}

test "prime25" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 10, "prime25");
}

test "prime49" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 10, "prime49");
}

test "prime121" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 10, "prime121");
}

test "prime169" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 10, "prime169");
}

test "sqrt2809" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 10, "sqrt2809");
}

test "sqrt3481" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 10, "sqrt3481");
}

test "sqrt3721" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 10, "sqrt3721");
}

test "sqrt4489" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 10, "sqrt4489");
}

test "sqrt5041" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 10, "sqrt5041");
}

test "sqrt5329" {
    const allocator = std.testing.allocator;
    try runTest(allocator, 10, "sqrt5329");
}
