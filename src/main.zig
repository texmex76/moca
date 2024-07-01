const std = @import("std");
const stdout = std.io.getStdOut();
const stderr = std.io.getStdErr();
const ArrayList = std.ArrayList;

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
var clauses = ArrayList(*clause);
var occurrences = ArrayList(*clause);

// Part of the state needed for parsing and unit propagation
var simplified = ArrayList(i32);
var unsimplified = ArrayList(i32);
var trail = ArrayList(i32);
var propagated = ArrayList(u32);
var values = ArrayList(i2);
var marks = ArrayList(bool);
var forced = ArrayList(bool);

// The state of the local search solver
var unsatisfied = ArrayList(*clause);
var limit = invalid_limit;
var generator: u64 = 0;
var minimum = invalid_minimum;
var best = invalid_minimum;
var minimum_restarts: u64 = 0;
var minimum_flipped: u64 = 0;
var terminate: bool = false;
var termination_signal: i32 = 0;

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
var file = std.fs.File; // this is not going to work
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
};

const clause = struct {
    id: u32,
    pos: u32,
    literals: ArrayList(i32),
    fn print(self: *clause) !void {
        for (self.literals.items) |lit| try stdout.writer().print("{d} ", .{lit});
        try stdout.writeAll("0\n");
    }
};

fn options(allocator: anytype) !void {
    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

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
            const seconds = try std.fmt.parseUnsigned(u64, arg, 10);
            _ = seconds; // TODO: make timeout here
            timeout_string = arg;
            timeout_string_seen = true;
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

pub fn main() !u8 {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = gpa.allocator();
    options(allocator) catch |err| switch (err) {
        error.Help => {},
        else => return err,
    };
    return 0;
}
