const std = @import("std");
const os = std.os;
const stdout = std.io.getStdOut();
const stderr = std.io.getStdErr();
const stdin = std.io.getStdIn();
const ArrayList = std.ArrayList;
const assert = std.debug.assert;
const debug = @import("config").debug;

var gpa = std.heap.GeneralPurposeAllocator(.{}){};
const allocator = gpa.allocator();

const usage =
    \\usage: babywalk [ -h ] [ <input> ]
    \\
    \\where '<option>' is one of the following
    \\
    \\  -h  print this command line option summary
    \\  -n  do not print satisfying assignment (model)
    \\  -v  increase verbosity level
    \\  -q  disable all messages
    \\  --random   random literal algorithm
    \\  --focused  focused random walk algorithm
    \\  --walksat  WalkSAT algorithm (not implemented)
    \\  --probsat  ProbSAT algorithm (not implemented)
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

const invalid_position = ~@as(u32, 0);
const invalid_minimum = ~@as(u32, 0);
const invalid_break_value = ~@as(u32, 0);
const invalid_limit = ~@as(u64, 0);

// Global state of the preprocessor
var variables: i64 = 0;
var found_empty_clause: bool = false;
var clauses = ArrayList(*clause).init(allocator);
var occurrences: ArrayWithOffset(*clause) = undefined;

pub fn ArrayWithOffset(comptime T: type) type {
    return struct {
        comptime T: type = u64,
        size: u64,
        offset: i64,
        data: []T,
        const Self = @This();
        fn init(size: u64, offset: i64) !Self {
            const data = try allocator.alloc(T, size);
            return Self{ .data = data, .size = size, .offset = offset };
        }
        fn fill(self: *Self, it: anytype) void {
            for (self.data) |*item| {
                item.* = it;
            }
        }
        fn get(self: *Self, idx: i64) T {
            assert(idx + self.offset < self.data.len);
            const new_idx = idx + self.offset;
            assert(new_idx >= 0);
            return self.data[@as(usize, @intCast(new_idx))];
        }
        fn set(self: *Self, idx: i64, it: T) void {
            assert(idx + self.offset < self.data.len);
            const new_idx = idx + self.offset;
            assert(new_idx >= 0);
            self.data[@as(usize, @intCast(new_idx))] = it;
        }
        fn deinit(self: *Self) void {
            allocator.free(self.data);
        }
    };
}

// Part of the state needed for parsing and unit propagation
var simplified = ArrayList(i64).init(allocator);
var unsimplified = ArrayList(i64).init(allocator);
var trail = ArrayList(i64).init(allocator);
var propagated = ArrayList(u64).init(allocator);
var values: ArrayWithOffset(i2) = undefined;
var marks: ArrayWithOffset(bool) = undefined;
var forced: ArrayWithOffset(bool) = undefined;

// The state of the local search solver
var unsatisfied = ArrayList(*clause).init(allocator);
var limit = invalid_limit;
var generator: u64 = 0;
var minimum = invalid_minimum;
var best = invalid_minimum;
var minimum_restarts: u64 = 0;
var minimum_flipped: u64 = 0;
var terminate: bool = false;
var termination_signal: c_int = 0;

const restart_scheduler_type = enum {
    never_restart,
    always_restart,
    fixed_restart,
    reluctant_restart,
    geometric_restart,
    arithmetic_restart,
};
var restart_scheduler = restart_scheduler_type.reluctant_restart;

var base_restart_interval: u64 = 0;
var reluctant_state = [2]u64{ 0, 0 };
var restart_interval: u64 = 0;
var next_restart: u64 = 0;

const algorithm_type = enum {
    random_algorithm,
    focused_algorithm,
    walksat_algorithm,
    probsat_algorithm,
};
var algorithm = algorithm_type.walksat_algorithm;

// Parsing state
var close_input: u2 = 0; // 0=stdin, 1=file, 2=pipe
var input_path: []const u8 = undefined;
var input_path_seen = false;
var file: std.fs.File = undefined;
var input_file: std.fs.File.Reader = undefined;
var lineno: u64 = 1;

// Global Flags
var verbosity: i32 = 0;
var do_not_print_model: bool = false;
var thank_string: []const u8 = undefined;
var thank_string_seen = false;

// Some statistics
var stats = struct {
    added: u64,
    parsed: u64,
    flipped: u64,
    restarts: u64,
    make_visited: u64,
    break_visited: u64,
    made_clauses: u64,
    broken_clauses: u64,
    random_walk: u64,
}{
    .added = 0,
    .parsed = 0,
    .flipped = 0,
    .restarts = 0,
    .make_visited = 0,
    .break_visited = 0,
    .made_clauses = 0,
    .broken_clauses = 0,
    .random_walk = 0,
};

// For debugging mode
var start_of_clause_lineno: u64 = 0;
var original_literals = ArrayList(i64).init(allocator);
var original_lineno = ArrayList(u64).init(allocator);

const clause = struct {
    id: u64,
    pos: u64,
    literals: ArrayList(i64),
    fn print(self: *clause) !void {
        for (self.literals.items) |lit| try stdout.writer().print("{d} ", .{lit});
        try stdout.writeAll("0\n");
    }
};

fn options(args: [][:0]u8) !void {
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
            try stdout.writer().print("{s}\n", .{usage});
            return error.Help;
        } else if (std.mem.eql(u8, arg, "-v")) {
            verbosity += @intFromBool(verbosity != std.math.maxInt(i32));
        } else if (std.mem.eql(u8, arg, "-q")) {
            verbosity = -1;
        } else if (std.mem.eql(u8, arg, "-f")) {
            i += 1;
            if (i == args.len) {
                try stderr.writeAll("argument to '-f' missing. (try '-h')\n");
                return error.OptionsError;
            }
            arg = args[i];
            if (limit_string_seen) {
                try stderr.writer().print("multiple '-f' options ('-f {s}' and '-f {s})\n", .{ limit_string, arg });
                return error.OptionsError;
            }
            limit = try std.fmt.parseUnsigned(u64, arg, 10);
            limit_string = arg;
            limit_string_seen = true;
        } else if (std.mem.eql(u8, arg, "-s")) {
            i += 1;
            if (i == args.len) {
                try stderr.writeAll("argument to '-s' missing. (try '-h')\n");
                return error.OptionsError;
            }
            arg = args[i];
            if (seed_string_seen) {
                try stderr.writer().print("multiple '-s' options ('-s {s}' and '-s {s}')\n", .{ seed_string, arg });
                return error.OptionsError;
            }
            if (thank_string_seen) {
                try stderr.writer().print("'--thank {s}' and '-s {s}'", .{ thank_string, arg });
                return error.OptionsError;
            }
            generator = try std.fmt.parseUnsigned(u64, arg, 10);
            seed_string = arg;
            seed_string_seen = true;
        } else if (std.mem.eql(u8, arg, "--thank")) {
            i += 1;
            if (i == args.len) {
                try stderr.writeAll("argument to '--thank' missing. (try '-h')\n");
                return error.OptionsError;
            }
            arg = args[i];
            if (thank_string_seen) {
                try stderr.writer().print("multiple '--thank' options ('--thank {s}' and '--thank {s}')", .{ thank_string, arg });
                return error.OptionsError;
            }
            if (seed_string_seen) {
                try stderr.writer().print("'-s {s}' and '--thank {s}'", .{ seed_string, arg });
                return error.OptionsError;
            }
            thank_string = arg;
            thank_string_seen = true;
        } else if (std.mem.eql(u8, arg, "-t")) {
            i += 1;
            if (i == args.len) {
                try stderr.writeAll("argument to '-t' missing. (try '-h')\n");
                return error.OptionsError;
            }
            arg = args[i];
            if (timeout_string_seen) {
                try stderr.writer().print("multiple '-t' options ('-t {s}' and '-t {s}')\n", .{ timeout_string, arg });
                return error.OptionsError;
            }
            const seconds = try std.fmt.parseUnsigned(c_uint, arg, 10);
            _ = std.c.alarm(seconds);
            timeout_string = arg;
            timeout_string_seen = true;
        } else if (std.mem.eql(u8, arg, "-l")) {
            if (debug) {
                verbosity = std.math.maxInt(i32);
            } else {
                try stderr.writeAll("invalid option '-l' (compiled without logging support)\n");
                return error.OptionsError;
            }
        } else if (std.mem.eql(u8, arg, "-n")) {
            do_not_print_model = true;
        } else if (std.mem.eql(u8, arg, "--random")) {
            algorithm = algorithm_type.random_algorithm;
        } else if (std.mem.eql(u8, arg, "--focused")) {
            algorithm = algorithm_type.focused_algorithm;
        } else if (std.mem.eql(u8, arg, "--probsat")) {
            algorithm = algorithm_type.probsat_algorithm;
        } else if (std.mem.eql(u8, arg, "--walksat")) {
            algorithm = algorithm_type.walksat_algorithm;
        } else if (std.mem.eql(u8, arg, "--always-restart")) {
            if (restart_string_seen) {
                try stderr.writeAll("you cannot combine different restart schedules\n");
                return error.OptionsError;
            }
            restart_scheduler = restart_scheduler_type.always_restart;
            restart_string_seen = true;
        } else if (std.mem.eql(u8, arg, "--never-restart")) {
            if (restart_string_seen) {
                try stderr.writeAll("you cannot combine different restart schedules\n");
                return error.OptionsError;
            }
            restart_scheduler = restart_scheduler_type.never_restart;
            restart_string_seen = true;
        } else if (std.mem.eql(u8, arg, "--fixed-restart")) {
            if (restart_string_seen) {
                try stderr.writeAll("you cannot combine different restart schedules\n");
                return error.OptionsError;
            }
            restart_scheduler = restart_scheduler_type.fixed_restart;
            restart_string_seen = true;
        } else if (std.mem.eql(u8, arg, "--reluctant-restart")) {
            if (restart_string_seen) {
                try stderr.writeAll("you cannot combine different restart schedules\n");
                return error.OptionsError;
            }
            restart_scheduler = restart_scheduler_type.reluctant_restart;
            restart_string_seen = true;
        } else if (std.mem.eql(u8, arg, "--geometric-restart")) {
            if (restart_string_seen) {
                try stderr.writeAll("you cannot combine different restart schedules\n");
                return error.OptionsError;
            }
            restart_scheduler = restart_scheduler_type.geometric_restart;
            restart_string_seen = true;
        } else if (std.mem.eql(u8, arg, "--arithmetic-restart")) {
            if (restart_string_seen) {
                try stderr.writeAll("you cannot combine different restart schedules\n");
                return error.OptionsError;
            }
            restart_scheduler = restart_scheduler_type.arithmetic_restart;
            restart_string_seen = true;
        } else if (arg[0] == '-') {
            try stderr.writer().print("invalid option '{s}' (try '-h')\n", .{arg});
            return error.OptionsError;
        } else if (!input_path_seen) {
            input_path = arg;
            input_path_seen = true;
        } else {
            try stderr.writer().print("too many file arguments '{s}' and '{s}'\n", .{ input_path, arg });
            return error.OptionsError;
        }
    }
}

fn message(comptime fmt: []const u8, args: anytype) !void {
    if (verbosity < 0)
        return;
    try stdout.writer().print(fmt, args);
    try stdout.writeAll("\n");
}

fn banner() !void {
    try message("BabyWalk Local Search SAT Solver", .{});
}

fn catchSignal(sig: c_int) callconv(.C) void {
    termination_signal = sig;
    terminate = true;
}

fn init() void {
    _ = os.linux.sigaction(os.linux.SIG.ALRM, &os.linux.Sigaction{
        .handler = .{ .handler = catchSignal },
        .mask = os.linux.empty_sigset,
        .flags = 0,
    }, null);
    // Interrupt signal catching is a little strange in terminal.
    // Not sure why. But it works.
    _ = os.linux.sigaction(os.linux.SIG.INT, &os.linux.Sigaction{
        .handler = .{ .handler = catchSignal },
        .mask = os.linux.empty_sigset,
        .flags = 0,
    }, null);
    // I get an error when I try to do the following and I don't know why
    // _ = os.linux.sigaction(os.linux.SIG.KILL, &os.linux.Sigaction{
    //     .handler = .{ .handler = catchSignal },
    //     .mask = os.linux.empty_sigset,
    //     .flags = 0,
    // }, null);
    _ = os.linux.sigaction(os.linux.SIG.SEGV, &os.linux.Sigaction{
        .handler = .{ .handler = catchSignal },
        .mask = os.linux.empty_sigset,
        .flags = 0,
    }, null);
    _ = os.linux.sigaction(os.linux.SIG.TERM, &os.linux.Sigaction{
        .handler = .{ .handler = catchSignal },
        .mask = os.linux.empty_sigset,
        .flags = 0,
    }, null);
}

fn hasSuffix(str: []const u8, suffix: []const u8) bool {
    const k = str.len;
    const l = suffix.len;
    return k >= l and std.mem.eql(u8, str[(k - l)..k], suffix);
}

fn next() !u8 {
    var ch = input_file.readByte() catch 0;
    if (ch == '\r') {
        ch = input_file.readByte() catch 0;
        if (ch != '\n') {
            try stderr.writeAll("expected new-line after carriage return\n");
            return error.NoNewLineAfterCarriageReturn;
        }
    }
    if (ch == '\n')
        lineno += 1;
    return ch;
}

fn expectDigit(ch: u8) !void {
    if (!std.ascii.isDigit(ch)) {
        try stderr.writeAll("extected digit");
        return error.ParseError;
    }
}

fn parse() !void {
    const start = std.time.timestamp();

    if (!input_path_seen or std.mem.eql(u8, input_path, "-")) {
        input_file = stdin.reader();
        input_path = "<stdin>";
        assert(close_input == 0);
    } else if (hasSuffix(input_path, ".bz2")) {
        close_input = 2;
        try stderr.writeAll("bzip2 not supported. sorry.\n");
        return error.UnsupportedInputFormat;
    } else if (hasSuffix(input_path, ".gz")) {
        close_input = 2;
        try stderr.writeAll("gz not supported. sorry.\n");
        return error.UnsupportedInputFormat;
    } else if (hasSuffix(input_path, ".xz")) {
        close_input = 2;
        try stderr.writeAll("xz not supported. sorry.\n");
        return error.UnsupportedInputFormat;
    } else {
        close_input = 1;
        file = try std.fs.cwd().openFile(input_path, .{});
        input_file = file.reader();
    }
    defer file.close();

    try message("reading from '{s}'", .{input_path});

    var ch = try next();
    while (ch == 'c') : (ch = try next()) {
        while (ch != '\n') : (ch = try next()) {
            if (ch == 0) {
                try stderr.writeAll("unexpected end-of-file in comment\n");
                return error.ParseError;
            }
        }
    }

    if (ch != 'p') {
        try stderr.writer().print("expected comment or header, got {c} ({d})\n", .{ ch, ch });
        return error.ParseError;
    }
    const header = " cnf ";
    var p: []const u8 = header[0..];
    while (p.len > 0) {
        const c = p[0];
        p = p[1..];
        if (c != try next()) {
            try stderr.writeAll("invalid header\n");
            return error.ParseError;
        }
    }
    ch = try next();
    try expectDigit(ch);
    variables = ch - '0';
    ch = try next();
    while (std.ascii.isDigit(ch)) : (ch = try next()) {
        if (std.math.maxInt(i64) / 10 < variables) {
            try stderr.writeAll("too many variables specified in header");
            return error.ParseError;
        }
        variables *= 10;
        const digit: i64 = (ch - '0');
        if (std.math.maxInt(i64) - digit < variables) {
            try stderr.writeAll("too many variables specified in header");
            return error.ParseError;
        }
        variables += digit;
    }
    if (ch != ' ') {
        try stderr.writeAll("extected white space");
        return error.ParseError;
    }
    ch = try next();
    try expectDigit(ch);
    var expected: i64 = ch - '0';
    ch = try next();
    while (std.ascii.isDigit(ch)) : (ch = try next()) {
        if (std.math.maxInt(i64) / 10 < expected) {
            try stderr.writeAll("too many clauses specified in header");
            return error.ParseError;
        }
        expected *= 10;
        const digit: i64 = (ch - '0');
        if (std.math.maxInt(i64) - digit < expected) {
            try stderr.writeAll("too many clauses specified in header");
            return error.ParseError;
        }
        expected += digit;
    }
    if (ch != '\n') {
        try stderr.writeAll("expected new-line");
        return error.ParseError;
    }
    try message("found 'p cnf {d} {d}' header", .{ variables, expected });
    try initializeVariables();
    var lit: i64 = 0;
    if (debug) {
        start_of_clause_lineno = 0;
    }
    while (true) {
        ch = try next();
        if (ch == ' ' or ch == '\n') continue;
        if (ch == 0) break;
        var sign: i2 = 1;
        if (ch == '-') {
            ch = try next();
            sign = -1;
        }
        try expectDigit(ch);
        if (debug) {
            start_of_clause_lineno = lineno;
        }
        if (stats.parsed == expected) {
            try stderr.writeAll("specified clauses exceeded\n");
            return error.ParseError;
        }
        lit = ch - '0';
        ch = try next();
        while (std.ascii.isDigit(ch)) : (ch = try next()) {
            if (std.math.maxInt(i64) / 10 < lit) {
                try stderr.writeAll("literal too large\n");
                return error.ParseError;
            }
            lit *= 10;
            const digit = ch - '0';
            if (std.math.maxInt(i64) - @as(i64, @intCast(digit)) < lit) {
                try stderr.writeAll("literal too large\n");
                return error.ParseError;
            }
            lit += digit;
        }
        if (ch != ' ' and ch != '\n') {
            try stderr.writeAll("expected white-space\n");
            return error.ParseError;
        }
        if (lit > variables) {
            try stderr.writer().print("invalid variable {d}\n", .{lit});
            return error.ParseError;
        }
        lit *= sign;
        if (debug) {
            try original_literals.append(lit);
        }
        if (lit != 0) {
            try unsimplified.append(lit);
        } else {
            stats.parsed += 1;
            try logClause(&unsimplified, "parsed");
            if (!found_empty_clause and !tautologicalClause(&unsimplified)) {
                const simpl = try simplifyClause(&simplified, &unsimplified);
                if (simpl) {
                    try logClause(&simplified, "simplified");
                }
                // TODO: add clause
            }
            try unsimplified.resize(0);
            if (debug) {
                try original_lineno.append(start_of_clause_lineno);
            }
        }
    }
    if (lit != 0) {
        try stdout.writeAll("zero missing\n");
        return error.ParseError;
    }
    if (stats.parsed != expected) {
        try stdout.writeAll("clause missing\n");
        return error.ParseError;
    }

    try message("parsed {d} clauses in {d:.2} seconds", .{ stats.parsed, std.time.timestamp() - start });
}

fn checkSimplified(cls: *ArrayList(i64)) void {
    for (cls.items) |lit| {
        assert(values.get(lit) == 0);
        assert(marks.get(lit) == false);
        assert(marks.get(-lit) == false);
        marks.set(lit, true);
    }
    for (cls.items) |lit| {
        marks.set(lit, true);
    }
}

fn connectLiteral(lit: i64, cls: *clause) void {
    assert(cls.literals.items.len > 1);
    logClause(cls, "connectLiteral"); // TODO: also print literal
    _ = lit; // TODO:
}

fn connectClause(cls: *clause) void {
    assert(cls.literals.items.len > 1);
    for (cls.literals.items) |lit| {
        connectLiteral(lit, cls);
    }
}

fn newClause(literals: *ArrayList(i64)) *clause {
    if (debug) {
        checkSimplified(literals);
    }
    const lits = try literals.clone(); // TODO: fix memory leak
    const cls = clause{ .id = stats.added, .pos = invalid_position, .literals = lits };
    stats.added += 1;
    logClause(lits, "new");
    if (lits.items.len > 1) {
        clauses.append(&cls);
    }
}

fn logClause(cls: *ArrayList(i64), msg: anytype) !void {
    if (debug) {
        if (verbosity == std.math.maxInt(i32)) {
            try stdout.writer().print("c LOG {s} ", .{msg});
            for (cls.items) |lit| {
                try stdout.writer().print("{d} ", .{lit});
            }
            try stdout.writeAll("\n");
        }
    }
}

fn simplifyClause(dst: *ArrayList(i64), src: *ArrayList(i64)) !bool {
    try dst.resize(0);
    for (src.items) |lit| {
        if (marks.get(lit) == true) continue;
        if (values.get(lit) < 0) continue;
        assert(marks.get(-lit) == false);
        marks.set(lit, true);
        try dst.append(lit);
    }
    for (dst.items) |lit| {
        marks.set(lit, false);
    }
    return dst.items.len != src.items.len;
}

fn tautologicalClause(cls: *ArrayList(i64)) bool {
    var res = false;
    for (cls.items) |lit| {
        if (marks.get(lit) == true) continue;
        if (values.get(lit) > 0) {
            res = true;
            break;
        }
        if (marks.get(-lit) == true) {
            res = true;
            break;
        }
        marks.set(lit, true);
    }
    for (cls.items) |lit| {
        marks.set(lit, false);
    }
    return res;
}

fn initializeVariables() !void {
    const v = @as(u64, @intCast(variables));
    occurrences = try ArrayWithOffset(*clause).init(2 * v + 1, variables);
    marks = try ArrayWithOffset(bool).init(2 * v + 1, variables);
    marks.fill(false);
    values = try ArrayWithOffset(i2).init(2 * v + 1, variables);
    values.fill(0);
    forced = try ArrayWithOffset(bool).init(v + 1, 0);
    forced.fill(false);
}

pub fn main() !u8 {
    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);
    options(args) catch |err| switch (err) {
        error.Help => return 0,
        else => return err,
    };
    try banner();
    init();
    try parse();
    defer {
        clauses.deinit();
        occurrences.deinit();
        marks.deinit();
        values.deinit();
        forced.deinit();
        simplified.deinit();
        unsimplified.deinit();
        if (debug) {
            original_literals.deinit();
            original_lineno.deinit();
        }
    }
    return 0;
}
