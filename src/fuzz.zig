const std = @import("std");
const os = std.os;
const stdout = std.io.getStdOut();
const stderr = std.io.getStdErr();
const stdin = std.io.getStdIn();
const ArrayList = std.ArrayList;
const assert = std.debug.assert;
const debug = @import("config").debug;
const expect = @import("std").testing.expect;

const allocator = std.heap.c_allocator;

const options = [_][]const u8{ "-v", "-q", "--walksat", "--probsat", "-s", "-t", "--thank", "--never-restart", "--fixed-restart", "--reluctant-restart", "--geometric-restart", "--arithmetic-restart" };
// Removed: -f, --random (slow) --focused (slow) --always-restart (can't find a solution)
const options_with_arg = [_][]const u8{ "-s", "-t", "--thank" };
const equiv1 = [_][]const u8{
    "--walksat",
    "--probsat",
};
const equiv2 = [_][]const u8{ "--never-restart", "--fixed-restart", "--reluctant-restart", "--geometric-restart", "--arithmetic-restart" };
const equiv3 = [_][]const u8{
    "--thank",
    "-s",
};

fn contains(haystack: anytype, needle: []const u8) bool {
    for (haystack) |item| {
        if (std.mem.eql(u8, item, needle)) return true;
    }
    return false;
}

fn areEquivalent(opt1: []const u8, opt2: []const u8) bool {
    if (contains(equiv1, opt1) and contains(equiv1, opt2)) return true;
    if (contains(equiv2, opt1) and contains(equiv2, opt2)) return true;
    if (contains(equiv3, opt1) and contains(equiv3, opt2)) return true;
    return false;
}

fn illegalConfiguration(used_options: [][]const u8, option: []const u8) bool {
    for (used_options) |item| {
        if (std.mem.eql(u8, item, option)) return true;
        if (areEquivalent(item, option)) return true;
    }
    return false;
}

fn writeToFile(filename: []const u8, contents: []const u8) !void {
    const handle = try std.fs.cwd().createFile(filename, .{
        .truncate = true,
    });
    defer handle.close();
    _ = try handle.write(contents);
}

fn generateMocaOptions(timeout: u64) ![][]u8 {
    var used_options = std.ArrayList([]const u8).init(allocator);
    defer used_options.deinit();
    var rnd = std.Random.DefaultPrng.init(@as(u64, @intCast(std.time.milliTimestamp())));
    var moca_argv = try allocator.alloc([]u8, 1);
    moca_argv[0] = try std.fmt.allocPrint(allocator, "timeout", .{});

    moca_argv = try allocator.realloc(moca_argv, moca_argv.len + 1);
    moca_argv[moca_argv.len - 1] = try std.fmt.allocPrint(allocator, "{d}", .{timeout});

    moca_argv = try allocator.realloc(moca_argv, moca_argv.len + 1);
    moca_argv[moca_argv.len - 1] = try std.fmt.allocPrint(allocator, "zig-out/bin/moca", .{});

    var num_otps: usize = 0;
    while (num_otps < 2) : (num_otps += 1) {
        var rand_opt = options[rnd.next() % options.len];
        while (illegalConfiguration(used_options.items, rand_opt)) {
            rand_opt = options[rnd.next() % options.len];
        }
        try used_options.append(rand_opt);
        moca_argv = try allocator.realloc(moca_argv, moca_argv.len + 1);
        moca_argv[moca_argv.len - 1] = try allocator.alloc(u8, rand_opt.len);
        std.mem.copyForwards(u8, moca_argv[moca_argv.len - 1], rand_opt);

        // INFO: turned off right now
        // if (std.mem.eql(u8, "-f", rand_opt)) {
        //     // limit total number of flips
        //     moca_argv = try allocator.realloc(moca_argv, moca_argv.len + 1);
        //     const flips = rnd.next() % 1000 + 100;
        //     moca_argv[moca_argv.len - 1] = try std.fmt.allocPrint(allocator, "{d}", .{flips});
        //     continue;
        // }
        if (std.mem.eql(u8, "-s", rand_opt)) {
            // seed
            moca_argv = try allocator.realloc(moca_argv, moca_argv.len + 1);
            const seed = rnd.next();
            moca_argv[moca_argv.len - 1] = try std.fmt.allocPrint(allocator, "{d}", .{seed});
            continue;
        }
        if (std.mem.eql(u8, "-t", rand_opt)) {
            // limit number of seconds
            moca_argv = try allocator.realloc(moca_argv, moca_argv.len + 1);
            const time_limit = rnd.next() % 300 + 10;
            moca_argv[moca_argv.len - 1] = try std.fmt.allocPrint(allocator, "{d}", .{time_limit});
            continue;
        }
        if (std.mem.eql(u8, "--thank", rand_opt)) {
            // hash string to random number generator seed
            const len = rnd.next() % 70;
            var chars = std.ArrayList(u8).init(allocator);
            defer chars.deinit();
            while (chars.items.len < len) {
                try chars.append(@as(u8, @intCast(rnd.next() % (126 - 33) + 33)));
            }
            moca_argv = try allocator.realloc(moca_argv, moca_argv.len + 1);
            moca_argv[moca_argv.len - 1] = try allocator.alloc(u8, len);
            for (chars.items, 0..) |char, idx| {
                moca_argv[moca_argv.len - 1][idx] = char;
            }
            continue;
        }
    }

    moca_argv = try allocator.realloc(moca_argv, moca_argv.len + 1);
    moca_argv[moca_argv.len - 1] = try std.fmt.allocPrint(allocator, "/tmp/fuzz.cnf", .{});

    return moca_argv;
}

pub fn main() !u8 {
    try std.fs.cwd().makePath("zig-out/fuzz");
    try std.fs.cwd().makePath("zig-out/fuzz/timeout");

    var instance: u64 = 0;

    while (true) {
        const fuzz_argv = [_][]const u8{ "zig-out/bin/generate", "-p", "-k", "3", "100" };
        const fuzz_proc = try std.process.Child.run(.{
            .allocator = allocator,
            .argv = &fuzz_argv,
            .max_output_bytes = 100000 * 1024,
        });
        defer allocator.free(fuzz_proc.stdout);
        defer allocator.free(fuzz_proc.stderr);
        try writeToFile("/tmp/fuzz.cnf", fuzz_proc.stdout);

        try stdout.writer().print("Instance {d} ", .{instance});
        instance += 1;

        const moca_argv = try generateMocaOptions(10);
        for (moca_argv) |item| {
            try stdout.writer().print("{s} ", .{item});
        }
        try stdout.writer().print("\n", .{});
        defer {
            for (moca_argv) |item| {
                allocator.free(item);
            }
            allocator.free(moca_argv);
        }
        const moca_proc = try std.process.Child.run(.{
            .allocator = allocator,
            .argv = moca_argv,
            .max_output_bytes = 1000 * 1024,
        });
        defer allocator.free(moca_proc.stdout);
        defer allocator.free(moca_proc.stderr);
        try writeToFile("/tmp/fuzz.out", moca_proc.stdout);
        try writeToFile("/tmp/fuzz.err", moca_proc.stderr);

        switch (moca_proc.term.Exited) {
            10 => {
                const check_argv = [_][]const u8{ "zig-out/bin/checkmodel", "/tmp/fuzz.cnf", "/tmp/fuzz.out" };
                const check_proc = try std.process.Child.run(.{
                    .allocator = allocator,
                    .argv = &check_argv,
                });
                defer allocator.free(check_proc.stdout);
                defer allocator.free(check_proc.stderr);
                if (check_proc.term.Exited != 0) {
                    std.debug.print("Wrong model!\n", .{}); // TODO: write to fuzz dir
                    std.debug.print("Exit code: {d}\n", .{check_proc.term.Exited});
                    break;
                }
            },
            20 => {
                const cadical_argv = [_][]const u8{ "cadical", "tmp/fuzz.cnf" };
                const cadical_proc = try std.process.Child.run(.{
                    .allocator = allocator,
                    .argv = &cadical_argv,
                });
                defer allocator.free(cadical_proc.stdout);
                defer allocator.free(cadical_proc.stderr);
                if (cadical_proc.term.Exited != 20) {
                    std.debug.print("Cadical disagrees with moca!\n", .{}); // TODO: write to fuzz dir
                    std.debug.print("Exit code: {d}\n", .{cadical_proc.term.Exited});
                    break;
                }
            },
            124 => {
                std.debug.print("We have a timeout!\n", .{});
                std.debug.print("Exit code: {d}\n", .{moca_proc.term.Exited});
                break;
            },
            else => {
                std.debug.print("OMG, some unrecognized ERROR!!!!\n", .{});
                std.debug.print("Exit code: {d}\n", .{moca_proc.term.Exited});
                break;
            },
        }
    }
    return 0;
}
