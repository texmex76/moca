const std = @import("std");
const os = std.os;
const stdout = std.io.getStdOut();
const stderr = std.io.getStdErr();
const stdin = std.io.getStdIn();
const ArrayList = std.ArrayList;
const assert = std.debug.assert;
const debug = @import("config").debug;

// var gpa = std.heap.GeneralPurposeAllocator(.{}){};
// const allocator = gpa.allocator();
const allocator = std.heap.c_allocator;

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

fn lit2Idx(lit: i64) usize {
    if (lit < 0) {
        return @as(usize, @intCast(-lit * 2 - 2));
    } else {
        return @as(usize, @intCast(lit * 2 - 1));
    }
}

var start_time: f64 = 0;
const invalid_position: u64 = std.math.maxInt(u64);
const invalid_minimum: u64 = std.math.maxInt(u64);
const invalid_break_value: u64 = std.math.maxInt(u64);
const invalid_limit: u64 = std.math.maxInt(u64);

// Global state of the preprocessor
var variables: i64 = 0;
var found_empty_clause: bool = false;
var clauses = ArrayList(clause).init(allocator);
var occurrences: []ArrayList(*clause) = undefined;

// Part of the state needed for parsing and unit propagation
var simplified = ArrayList(i64).init(allocator);
var unsimplified = ArrayList(i64).init(allocator);
var trail = ArrayList(i64).init(allocator);
var min_break_value_literals = ArrayList(i64).init(allocator);
var propagated: u64 = 0;
var values: []i2 = undefined;
var marks: []bool = undefined;
var forced: []bool = undefined;

// The state of the local search solver
var unsatisfied = ArrayList(*clause).init(allocator);
var limit = invalid_limit;
var next_unsatisfied: u64 = 0;
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
    random_walks: u64,
    score_visited: u64,
}{
    .added = 0,
    .parsed = 0,
    .flipped = 0,
    .restarts = 0,
    .make_visited = 0,
    .break_visited = 0,
    .made_clauses = 0,
    .broken_clauses = 0,
    .random_walks = 0,
    .score_visited = 0,
};

// For debugging mode
var start_of_clause_lineno: u64 = 0;
// TODO: only initialize them when in debugging is on
var original_literals = ArrayList(i64).init(allocator);
var original_lineno = ArrayList(u64).init(allocator);

const clause = struct {
    id: u64,
    pos: u64,
    literals: []i64,
    fn print(self: *clause) !void {
        for (self.literals) |lit| try stdout.writer().print("{d} ", .{lit});
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

fn verbose(trigger_at_v: i32, comptime fmt: []const u8, args: anytype) !void {
    if (trigger_at_v <= verbosity)
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
    const start = std.time.microTimestamp();

    if (!input_path_seen or std.mem.eql(u8, input_path, "-")) {
        input_file = stdin.reader();
        input_path = "<stdin>";
    } else if (hasSuffix(input_path, ".bz2")) {
        try stderr.writeAll("bzip2 not supported. sorry.\n");
        return error.UnsupportedInputFormat; // TODO: support bzip2
    } else if (hasSuffix(input_path, ".gz")) {
        try stderr.writeAll("gz not supported. sorry.\n");
        return error.UnsupportedInputFormat; // TODO: support gz
    } else if (hasSuffix(input_path, ".xz")) {
        try stderr.writeAll("xz not supported. sorry.\n");
        return error.UnsupportedInputFormat; // TODO: support xz
    } else {
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
            try logClause(&unsimplified.items, "parsed");
            if (!found_empty_clause and !tautologicalClause(&unsimplified)) {
                const did_simplify = try simplifyClause(&simplified, &unsimplified);
                if (did_simplify) {
                    try logClause(&simplified.items, "simplified");
                }
                var c = try newClause(&simplified);
                if (c.literals.len > 1) {
                    try clauses.append(c);
                    try connectClause(&c);
                }
                const size = c.literals.len;
                if (size == 0) {
                    assert(!found_empty_clause);
                    try verbose(1, "found_empty_clause", .{});
                    found_empty_clause = true;
                } else if (size == 1) {
                    const unit = c.literals[0];
                    try logClause(&c.literals, "found unit");
                    try rootLevelAssign(unit, &c);
                    const ok = try propagate();
                    if (!ok) {
                        try verbose(1, "root-level propagation yields conflict", .{});
                        assert(found_empty_clause);
                    }
                    allocator.free(c.literals);
                }
            }
            unsimplified.shrinkRetainingCapacity(0);
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

    try message("parsed {d} clauses in {d:.2} seconds", .{ stats.parsed, toSeconds(std.time.microTimestamp() - start) });
}

fn toSeconds(tm: i64) f64 {
    return @as(f64, @floatFromInt(tm)) / 1000;
}

fn propagate() !bool {
    assert(!found_empty_clause);
    while (propagated != trail.items.len) : (propagated += 1) {
        const lit = trail.items[propagated];
        try log("propagating {d}", .{lit});
        next_clause: for (occurrences[lit2Idx(-lit)].items) |c| {
            var unit: i64 = 0;
            for (c.literals) |other| {
                const value = values[lit2Idx(other)];
                if (value < 0) continue;
                if (value > 0) continue :next_clause;
                if (unit != 0) continue :next_clause;
                unit = other;
            }
            if (unit == 0) {
                try logClause(&c.literals, "conflicting");
                found_empty_clause = true;
                return false;
            }
            try rootLevelAssign(unit, c);
        }
    }
    return true;
}

fn rootLevelAssign(lit: i64, reason: *const clause) !void {
    try logClauseAndLit(&reason.literals, lit, "assign with reason");
    assert(values[lit2Idx(lit)] == 0);
    assert(values[lit2Idx(-lit)] == 0);
    values[lit2Idx(lit)] = 1;
    values[lit2Idx(-lit)] = -1;
    try trail.append(lit);
    forced[@abs(lit)] = true;
}

fn checkSimplified(cls: *ArrayList(i64)) void {
    for (cls.items) |lit| {
        assert(values[lit2Idx(lit)] == 0);
        assert(marks[lit2Idx(lit)] == false);
        assert(marks[lit2Idx(-lit)] == false);
        marks[lit2Idx(lit)] = true;
    }
    for (cls.items) |lit| {
        marks[lit2Idx(lit)] = false;
    }
}

fn connectLiteral(lit: i64, cls: *clause) !void {
    assert(cls.literals.len > 1);
    try logClauseAndLit(&cls.literals, lit, "connectLiteral");
    try occurrences[lit2Idx(lit)].append(cls);
}

fn connectClause(cls: *clause) !void {
    assert(cls.literals.len > 1);
    for (cls.literals) |lit| {
        try connectLiteral(lit, cls);
    }
}

fn newClause(literals: *ArrayList(i64)) !clause {
    if (debug) {
        checkSimplified(literals);
    }
    var lits = try allocator.alloc(i64, literals.items.len);
    for (literals.items, 0..) |lit, idx| {
        lits[idx] = lit;
    }
    try logClause(&lits, "new");
    stats.added += 1;
    return clause{ .id = stats.added, .pos = invalid_position, .literals = lits };
}

fn logClauseAndLit(cls: *const []i64, lit: i64, msg: anytype) !void {
    if (debug) {
        if (verbosity == std.math.maxInt(i32)) {
            try stdout.writer().print("c LOG {s} l: {d} c: ", .{ msg, lit });
            for (cls.*) |l| {
                try stdout.writer().print("{d} ", .{l});
            }
            try stdout.writeAll("\n");
        }
    }
}

fn logClause(cls: *const []i64, msg: anytype) !void {
    if (debug) {
        if (verbosity == std.math.maxInt(i32)) {
            try stdout.writer().print("c LOG {s} ", .{msg});
            for (cls.*) |lit| {
                try stdout.writer().print("{d} ", .{lit});
            }
            try stdout.writeAll("\n");
        }
    }
}

fn log(comptime fmt: []const u8, args: anytype) !void {
    if (debug) {
        if (verbosity == std.math.maxInt(i32)) {
            try stdout.writeAll("c LOG ");
            try stdout.writer().print(fmt, args);
            try stdout.writeAll("\n");
        }
    }
}

fn simplifyClause(dst: *ArrayList(i64), src: *ArrayList(i64)) !bool {
    dst.shrinkRetainingCapacity(0);
    for (src.items) |lit| {
        if (marks[lit2Idx(lit)] == true) continue;
        if (values[lit2Idx(lit)] < 0) continue;
        assert(marks[lit2Idx(-lit)] == false);
        marks[lit2Idx(lit)] = true;
        try dst.append(lit);
    }
    for (dst.items) |lit| {
        marks[lit2Idx(lit)] = false;
    }
    return dst.items.len != src.items.len;
}

fn tautologicalClause(cls: *ArrayList(i64)) bool {
    var res = false;
    for (cls.items) |lit| {
        if (marks[lit2Idx(lit)] == true) continue;
        if (values[lit2Idx(lit)] > 0) {
            res = true;
            break;
        }
        if (marks[lit2Idx(-lit)] == true) {
            res = true;
            break;
        }
        marks[lit2Idx(lit)] = true;
    }
    for (cls.items) |lit| {
        marks[lit2Idx(lit)] = false;
    }
    return res;
}

fn fill(comptime T: type, arr: []T, elem: T) void {
    for (arr) |*item| {
        item.* = elem;
    }
}

fn initializeVariables() !void {
    const v = @as(usize, @intCast(variables));
    occurrences = try allocator.alloc(ArrayList(*clause), 2 * v + 1);
    for (occurrences) |*occ| {
        occ.* = ArrayList(*clause).init(allocator);
    }
    marks = try allocator.alloc(bool, 2 * v + 1);
    fill(bool, marks, false);
    values = try allocator.alloc(i2, 2 * v + 1);
    fill(i2, values, 0);
    forced = try allocator.alloc(bool, v + 1);
    fill(bool, forced, false);
}

fn deleteClause(cls: *clause) !void {
    try logClause(&cls.literals, "delete");
    allocator.free(cls.literals);
}

fn simplify() !void {
    if (found_empty_clause) return;
    for (occurrences) |*list| {
        try list.resize(0);
    }
    const begin: [*]clause = clauses.items.ptr;
    const end: [*]clause = clauses.items.ptr + clauses.items.len - 1;
    var j = begin;
    var i = j;
    continue_with_next_clause: while (i != end) {
        j[0] = i[0];
        i += 1;
        var c = j[0];
        j += 1;
        try simplified.resize(0);
        var new_size: usize = 0;
        for (c.literals) |lit| {
            const value = values[lit2Idx(lit)];
            if (value > 0) {
                j -= 1;
                try deleteClause(&c);
                continue :continue_with_next_clause;
            }
            if (value == 0) try simplified.append(lit);
        }
        new_size = simplified.items.len;
        assert(new_size > 1);
        if (new_size < c.literals.len) {
            try logClause(&c.literals, "unsimplified");
            for (simplified.items, 0..) |lit, idx| {
                c.literals[idx] = lit;
            }
            c.literals = try allocator.realloc(c.literals, new_size);
            try logClause(&c.literals, "simplified");
        }
        try connectClause(&c);
    }
    try clauses.resize((@intFromPtr(j) - @intFromPtr(begin)) / @sizeOf(clause));
}

fn next64() u64 {
    generator = @mulWithOverflow(generator, 6364136223846793005)[0];
    generator = @addWithOverflow(generator, 1442695040888963407)[0];
    assert(generator != 0);
    return generator;
}

fn initializeSeed() !void {
    if (thank_string_seen) {
        for (thank_string) |c| {
            generator ^= c;
            _ = next64();
        }
        try verbose(1, "hashed '{s}' to seed '{d}'", .{ thank_string, generator });
    }
    try message("seed {d}", .{generator});
}

fn initializeRestart() !void {
    restart_interval = 100 * @as(u64, @intCast(variables));
    base_restart_interval = restart_interval;
    switch (restart_scheduler) {
        .never_restart => {
            try message("never restart", .{});
        },
        .always_restart => {
            try message("always restart", .{});
        },
        .fixed_restart => {
            try message("fixed restart interval of {d}", .{restart_interval});
        },
        .reluctant_restart => {
            try message("reluctant restart interval of {d}", .{restart_interval});
        },
        .geometric_restart => {
            try message("geometric restart interval of {d}", .{restart_interval});
        },
        .arithmetic_restart => {
            try message("arithmetic restart interval of {d}", .{restart_interval});
        },
    }
    next_restart = stats.restarts + restart_interval;
}

fn isTimeToRestart() bool {
    if (restart_scheduler == restart_scheduler_type.reluctant_restart) return true;
    if (restart_scheduler == restart_scheduler_type.never_restart) return false;
    if (stats.flipped < next_restart) return false;
    if (restart_scheduler == restart_scheduler_type.arithmetic_restart) {
        restart_interval += base_restart_interval;
    } else if (restart_scheduler == restart_scheduler_type.geometric_restart) {
        restart_interval *= 2;
    } else if (restart_scheduler == restart_scheduler_type.reluctant_restart) {
        var u = reluctant_state[0];
        var v = reluctant_state[1];
        if ((u & (~u + 1)) == v) {
            u += 1;
            v = 1;
        } else {
            v *= 2;
        }
        restart_interval = v * base_restart_interval;
        reluctant_state[0] = u;
        reluctant_state[1] = v;
    } else {
        assert(restart_scheduler == restart_scheduler_type.fixed_restart);
    }
    next_restart = stats.flipped + restart_interval;
    return true;
}

fn pickModular(mod: u64) u64 {
    assert(mod != 0);
    const tmp = next32();
    const fraction = @as(f64, @floatFromInt(tmp)) / 4294967296.0;
    const res = @as(u64, @intFromFloat(@as(f64, @floatFromInt(mod)) * fraction));
    assert(res < mod);
    return res;
}

fn pickRandomFalsifiedLiteral() i64 {
    var res = pickModular(@as(u64, @intCast(variables))) + 1;
    while (forced[res]) {
        res = pickModular(@as(u64, @intCast(variables))) + 1;
    }
    var res_int = @as(i64, @intCast(res));
    if (values[lit2Idx(res_int)] > 0) {
        res_int = -res_int;
    }
    return res_int;
}

fn makeClauses(lit: i64) !void {
    if (occurrences[lit2Idx(lit)].items.len < unsatisfied.items.len) {
        try makeClausesAlongOccurrences(lit);
    } else {
        try makeClausesAlongUnsatisfied(lit);
    }
}

fn makeClausesAlongOccurrences(lit: i64) !void {
    var made: usize = 0;
    var visited: usize = 0;
    assert(values[lit2Idx(lit)] > 0);
    const occs = occurrences[lit2Idx(lit)];
    try log("making clauses with {d} along with {d} occurrences", .{ lit, occs.items.len });
    for (occs.items) |c| {
        const unsatisfied_size = unsatisfied.items.len;
        if (unsatisfied_size == 0) break;
        visited += 1;
        if (c.pos >= unsatisfied_size) continue;
        assert(unsatisfied.items[c.pos] == c);
        if (c.pos != unsatisfied_size - 1) {
            var d = unsatisfied.getLast();
            d.pos = c.pos;
            unsatisfied.items[d.pos] = d;
        }
        _ = unsatisfied.pop();
        try makeClause(c);
        made += 1;
    }
    stats.made_clauses += made;
    stats.make_visited += visited;
    try log("made {d} clauses with flipped {d}", .{ made, lit });
}

fn makeClause(cls: *clause) !void {
    try logClause(&cls.literals, "made");
    cls.pos = invalid_position;
}

fn contains(cls: *clause, lit: i64) bool {
    for (cls.literals) |other| {
        if (other == lit) {
            return true;
        }
    }
    return false;
}

fn makeClausesAlongUnsatisfied(lit: i64) !void {
    try log("making clauses with {d} along {d} unsatisfied", .{ lit, unsatisfied.items.len });
    assert(values[lit2Idx(lit)] > 0);
    var made: usize = 0;
    var visited: usize = 0;
    const begin = unsatisfied.items.ptr;
    const end = unsatisfied.items.ptr + unsatisfied.items.len - 1;
    var j = begin;
    var i = j;
    while (i != end) {
        const c = i[0];
        i += 1;
        visited += 1;
        if (contains(c, lit)) {
            try makeClause(c);
            made += 1;
        } else if (i != j) {
            c.pos = (@intFromPtr(j) - @intFromPtr(begin)) / @sizeOf(clause);
            j[0] = c;
            j += 1;
        } else {
            j += 1;
        }
    }
    try unsatisfied.resize((@intFromPtr(j) - @intFromPtr(begin)) / @sizeOf(clause));
    stats.made_clauses += made;
    stats.make_visited += visited;
    try log("made {d} clauses with flipped {d}", .{ made, lit });
}

fn breakClauses(lit: i64) !void {
    try log("breaking clauses with {d}", .{lit});
    assert(values[lit2Idx(lit)] < 0);
    var broken: usize = 0;
    var visited: usize = 0;
    for (occurrences[lit2Idx(lit)].items) |c| {
        visited += 1;
        if (!satisfied(c)) {
            try breakClause(c);
            broken += 1;
        }
    }
    stats.broken_clauses += broken;
    stats.break_visited += visited;
    try log("broken {d} clauses with flipped {d}", .{ broken, lit });
}

fn flipLiteral(lit: i64) !void {
    try log("flipping {d}", .{lit});
    assert(!forced[@as(usize, @intCast(lit))]);
    assert(values[lit2Idx(lit)] < 0);
    values[lit2Idx(lit)] = -1;
    values[lit2Idx(-lit)] = 1;
    stats.flipped += 1;
    try makeClauses(lit);
    try breakClauses(-lit);
    try updateMinimun();
}

fn next32() u32 {
    const res: u32 = @truncate(next64() >> 32);
    return res;
}

fn nextBool() bool {
    return next32() < 2147483648;
}

fn satisfied(cls: *clause) bool {
    for (cls.literals) |lit| {
        if (values[lit2Idx(lit)] > 0) return true;
    }
    return false;
}

fn breakClause(cls: *clause) !void {
    try logClause(&cls.literals, "broken");
    cls.pos = unsatisfied.items.len;
    try unsatisfied.append(cls);
}

fn restart() !void {
    try log("restarting", .{});
    stats.restarts += 1;
    for (1..@as(usize, @intCast(variables)) + 1) |idx| {
        if (forced[idx]) continue;
        const value: i2 = if (nextBool()) -1 else 1;
        const i = @as(i64, @intCast(idx));
        values[lit2Idx(i)] = value;
        values[lit2Idx(-i)] = -value;
        try log("assign {d} in restart", .{if (value < 0) -i else i});
    }
    for (unsatisfied.items) |c| {
        c.pos = invalid_position;
    }
    try unsatisfied.resize(0);
    var broken: usize = 0;
    var visited: usize = 0;
    for (clauses.items) |*c| {
        visited += 1;
        if (!satisfied(c)) {
            try breakClause(c);
            broken += 1;
        }
    }
    stats.broken_clauses += broken;
    stats.break_visited += visited;
    try verbose(2, "{b} clauses broken after restart {d} and {d} flipped", .{ unsatisfied.items.len, stats.restarts, stats.flipped });
    best = invalid_minimum;
    try updateMinimun();
}

fn updateMinimun() !void {
    const unsatisfied_size = unsatisfied.items.len;
    if (unsatisfied_size < minimum) {
        minimum = unsatisfied_size;
        minimum_restarts = stats.restarts;
        minimum_flipped = stats.flipped;
        try verbose(1, "minimum {d} unsatisfied clauses after {d} flipped variables and {d} restarts", .{ minimum, stats.flipped, stats.restarts });
    }
    if (restart_scheduler != restart_scheduler_type.always_restart and restart_scheduler != restart_scheduler_type.never_restart) {
        if (unsatisfied_size < best) {
            best = unsatisfied_size;
            try verbose(3, "best {d} unsatisfied clauses after {d} flipped variables and {d} restarts", .{ best, stats.flipped, stats.restarts });
        }
    }
}

fn randomLiteral() !void {
    try message("using random literal picking algorithm", .{});
    try restart();
    while (unsatisfied.items.len != 0 and stats.flipped < limit and !terminate) {
        if (isTimeToRestart()) {
            try restart();
        } else {
            const lit = pickRandomFalsifiedLiteral();
            try flipLiteral(lit);
        }
    }
}

fn focusedRandomWalk() !void {
    try message("using focused random walk algorithm", .{});
    try restart();
    while (unsatisfied.items.len != 0 and stats.flipped < limit and !terminate) {
        if (isTimeToRestart()) {
            try restart();
        } else {
            const c = try pickUnsatisfiedClause();
            const lit = try pickRandomLiteralInUnsatisfiedClause(c);
            try flipLiteral(lit);
        }
    }
}

fn pickUnsatisfiedClause() !*clause {
    var pos = next_unsatisfied;
    next_unsatisfied += 1;
    if (pos >= unsatisfied.items.len) {
        pos = 0;
        next_unsatisfied = 1;
    }
    const res = unsatisfied.items[pos];
    try log("picked at position {d}", .{res});
    return res;
}

fn pickRandomLiteralInUnsatisfiedClause(cls: *clause) !i64 {
    assert(cls.literals.len < std.math.maxInt(usize));
    const pos = pickModular(cls.literals.len);
    const res = cls.literals[pos];
    try log("random walk picked at position {d} literal {d}", .{ pos, res });
    stats.random_walks += 1;
    return res;
}

fn walksat() !void {
    try message("using WALKSAT algorithm", .{});
    try restart();
    while (unsatisfied.items.len != 0 and stats.flipped < limit and !terminate) {
        if (isTimeToRestart()) {
            try restart();
        } else {
            const c = try pickUnsatisfiedClause();
            const lit = try selectLiteralInUnsatisfiedClause(c);
            try flipLiteral(lit);
        }
    }
}

fn critical(cls: *clause) bool {
    var unit: i64 = 0;
    for (cls.literals) |lit| {
        const value = values[lit2Idx(lit)];
        if (value < 0) continue;
        assert(value > 0);
        if (unit != 0) {
            return false;
        }
        unit = lit;
    }
    return unit != 0;
}

fn breakValue(lit: i64, max: usize) !usize {
    assert(values[lit2Idx(lit)] > 0);
    var res: usize = 0;
    // var visited = 0; // not used in C++ code
    for (occurrences[lit2Idx(lit)].items) |c| {
        // visited += 1;
        if (critical(c)) {
            res += 1;
            if (res == max) break;
        }
    }
    stats.score_visited += 1;
    try log("break-value {d} of literal {d}", .{ res, lit });
    return res;
}

fn nextDoubleInclusive() f64 {
    const res = @as(f64, @floatFromInt(next32())) / 4294967295.0;
    return res;
}

fn selectLiteralInUnsatisfiedClause(cls: *clause) !i64 {
    var min_break_value = @as(u64, @intCast(invalid_break_value));
    for (cls.literals) |lit| {
        const not_lit_break_value = try breakValue(-lit, std.math.maxInt(usize));
        if (not_lit_break_value > min_break_value) continue;
        if (not_lit_break_value < min_break_value) {
            min_break_value = not_lit_break_value;
            try min_break_value_literals.resize(0);
        }
        try min_break_value_literals.append(lit);
    }
    try logClause(&cls.literals, "minimum break value {d} in"); // TODO: min_break_value
    if (min_break_value != 0) {
        const p = nextDoubleInclusive();
        if (p < 0.57) { // Magic constant!
            try log("falling back to random literal in clause", .{});
            return pickRandomLiteralInUnsatisfiedClause(cls);
        }
    }
    const min_break_value_literals_size = min_break_value_literals.items.len;
    assert(min_break_value_literals_size <= std.math.maxInt(usize));
    const pos = pickModular(min_break_value_literals_size);
    const res = min_break_value_literals.items[pos];
    try log("picked at position {d} literal {d} with break-value {d}", .{ pos, res, min_break_value });
    return res;
}

fn probsat() !void {
    try message("using ProbSAT algorithm", .{});
    try restart();
    while (unsatisfied.items.len != 0 and stats.flipped < limit and !terminate) {
        const c = try pickUnsatisfiedClause();
        const lit = sampleLiteralInUnsatisfiedClause(c);
        try flipLiteral(lit);
    }
}

fn sampleLiteralInUnsatisfiedClause(cls: *clause) i64 {
    return cls.literals[0]; // TODO+ implement ProbSAT sampling
}

fn solve() !u8 {
    try initializeSeed();
    if (limit == invalid_position) {
        try message("unlimited number of flipped variables", .{});
    } else {
        try message("limit {d} on number of flipped variables", .{limit});
    }
    try initializeRestart();
    var res: u8 = 0;
    if (found_empty_clause) {
        try stdout.writeAll("s UNSATISFIABLE\n");
        res = 20;
    } else {
        switch (algorithm) {
            .random_algorithm => {
                try randomLiteral();
            },
            .focused_algorithm => {
                try focusedRandomWalk();
            },
            .walksat_algorithm => {
                try walksat();
            },
            .probsat_algorithm => {
                try probsat();
            },
        }
        try message("reached minimum {d} unsatisfied clauses after {d} flipped variables and {d} restarts", .{ minimum, minimum_flipped, minimum_restarts });
        if (!terminate and unsatisfied.items.len == 0) {
            if (debug) {
                try checkOriginalClausesSatisfied();
            }
            try stdout.writeAll("s SATISFIABLE\n");
            if (!do_not_print_model) try printValues();
            res = 10;
        } else {
            if (terminate) {
                try stdout.writer().print("c terminated by {s}\n", .{describeSignal(termination_signal)});
            }
            try stdout.writeAll("s UNKNOWN\n");
            res = 0;
        }
    }
    return res;
}

fn describeSignal(sig: c_int) []const u8 {
    switch (sig) {
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
            return "unknown";
        },
    }
}

var buffer: [256]u8 = undefined;
var buffer_len: usize = 0;

fn printValues() !void {
    for (1..@as(usize, @intCast(variables)) + 1) |idx| {
        const i = @as(i64, @intCast(idx));
        const value = @as(i64, @intCast(values[lit2Idx(i)]));
        if (value != 0) try printValue(value * i);
    }
    try printValue(0);
    if (buffer_len > 0) try flushBuffer();
}

fn printValue(lit: i64) !void {
    var str: [32]u8 = undefined;
    const res = try std.fmt.bufPrint(&str, " {d}", .{lit});
    if (buffer_len + res.len > 74) try flushBuffer();
    for (res, buffer_len..) |char, idx| {
        buffer[idx] = char;
    }
    buffer_len += res.len;
}

fn flushBuffer() !void {
    try stdout.writeAll("v");
    try stdout.writer().print("{s}", .{buffer[0..buffer_len]});
    try stdout.writeAll("\n");
    buffer_len = 0;
}

fn checkOriginalClausesSatisfied() !void {
    var start_of_last_clause: usize = 0;
    var is_satisfied: bool = false;
    var id: usize = 0;
    for (0..original_literals.items.len) |i| {
        const lit = original_literals.items[i];
        if (lit != 0) {
            if (values[lit2Idx(lit)] > 0) {
                is_satisfied = true;
            }
        } else if (is_satisfied) {
            start_of_last_clause = i + 1;
            is_satisfied = false;
            id += 1;
        } else {
            try stderr.writer().print("babywalk: fatal error: original clause[{d}] at line {d} unsatisfied:\n", .{ id + 1, original_lineno.items[id] });
            for (start_of_last_clause..i) |j| {
                try stderr.writer().print("{d} ", .{original_literals[j]});
            }
            try stderr.writer().print("\n");
            return error.FatalError;
        }
    }
}

fn average(a: anytype, b: anytype) f64 {
    if (b == 0) {
        return 0;
    }
    return @as(f64, @floatFromInt(a)) / @as(f64, @floatFromInt(b));
}

fn percent(a: anytype, b: anytype) f64 {
    return average(100 * a, b);
}

fn report() !void {
    if (verbosity < 0) return;
    const elapsed = toSeconds(std.time.microTimestamp()) - start_time;
    try stdout.writer().print("c {s: <21} {d:13} {d:14.2} flipped/restart\n", .{ "restarts:", stats.restarts, average(stats.flipped, stats.restarts) });
    try stdout.writer().print("c {s: <21} {d:13} {d:14.2} per second\n", .{ "flipped-variables:", stats.flipped, @as(f64, @floatFromInt(stats.flipped)) / elapsed });
    try stdout.writer().print("c {s: <21} {d:13} {d:14.2} % flipped\n", .{ "random-walks:", stats.random_walks, percent(stats.random_walks, stats.flipped) });
    try stdout.writer().print("c {s: <21} {d:13} {d:14.2} per flip\n", .{ "made-clauses:", stats.made_clauses, average(stats.made_clauses, stats.flipped) });
    try stdout.writer().print("c {s: <21} {d:13} {d:14.2} per flip\n", .{ "make-visited:", stats.make_visited, average(stats.make_visited, stats.flipped) });
    try stdout.writer().print("c {s: <21} {d:13} {d:14.2} per flip\n", .{ "broken-clauses:", stats.broken_clauses, average(stats.broken_clauses, stats.flipped) });
    try stdout.writer().print("c {s: <21} {d:13} {d:14.2} per flip\n", .{ "break-visited:", stats.break_visited, average(stats.break_visited, stats.flipped) });
    try stdout.writer().print("c {s: <21} {d:28.2} seconds\n", .{ "process-time:", elapsed });
}

fn goodbye(result: u8) !void {
    if (thank_string_seen) {
        try message("{s}solved thanks to '{s}'", .{ if (result != 0) "" else "un", thank_string });
    }
    try message("exit {d}", .{result});
}

pub fn main() !u8 {
    start_time = toSeconds(std.time.microTimestamp());
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
        for (clauses.items) |c| {
            allocator.free(c.literals);
        }
        clauses.deinit();
        for (occurrences) |*occ| {
            occ.deinit();
        }
        allocator.free(occurrences);
        allocator.free(marks);
        allocator.free(values);
        allocator.free(forced);
        simplified.deinit();
        unsimplified.deinit();
        original_literals.deinit();
        original_lineno.deinit();
        min_break_value_literals.deinit();
    }
    try simplify();
    const res = try solve();
    try report();
    try goodbye(res);
    return res;
}
