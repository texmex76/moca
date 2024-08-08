const std = @import("std");
const os = std.os;
const stdout = std.io.getStdOut();
const stderr = std.io.getStdErr();
const stdin = std.io.getStdIn();
const ArrayList = std.ArrayList;
const assert = std.debug.assert;
const debug = @import("config").debug;
const expect = @import("std").testing.expect;

// var gpa = std.heap.GeneralPurposeAllocator(.{}){};
// const allocator = gpa.allocator();
const allocator = std.heap.c_allocator;

const options = [_][]const u8{ "-v", "-q", "--random", "--focused", "--walksat", "--probsat", "-f", "-s", "-t", "--thank", "--always-restart", "--never-restart", "--fixed-restart", "--reluctant-restart", "--geometric-restart", "--arithmetic-restart" };
const options_with_arg = [_][]const u8{ "-f", "-s", "-t", "--thank" };

fn writeToFile(filename: []const u8, contents: []const u8) !void {
    const handle = try std.fs.cwd().createFile(filename, .{
        .truncate = true,
    });
    defer handle.close();
    _ = try handle.write(contents);
}

pub fn main() !u8 {
    try std.fs.cwd().makePath("zig-out/fuzz");

    var instance: u64 = 0;
    var rnd = std.Random.DefaultPrng.init(std.time.nanoTimestamp());

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

        std.debug.print("Instance {d}\n", .{instance});
        instance += 1;

        var moca_argv = try allocator.alloc([]u8, 1);
        moca_argv[0] = try std.fmt.allocPrint(allocator, "zig-out/bin/moca", .{});

        const moca_proc = try std.process.Child.run(.{
            .allocator = allocator,
            .argv = &moca_argv,
            .max_output_bytes = 1000 * 1024,
        });
        defer allocator.free(moca_proc.stdout);
        defer allocator.free(moca_proc.stderr);

        if (moca_proc.term.Exited != 10) {
            std.debug.print("Ouch!\n", .{});
            break;
        }

        try writeToFile("/tmp/fuzz.log", moca_proc.stdout);
        const check_argv = [_][]const u8{ "zig-out/bin/checkmodel", "/tmp/fuzz.cnf", "/tmp/fuzz.log" };
        const check_proc = try std.process.Child.run(.{
            .allocator = allocator,
            .argv = &check_argv,
        });
        defer allocator.free(check_proc.stdout);
        defer allocator.free(check_proc.stderr);

        if (check_proc.term.Exited != 0) {
            std.debug.print("Wrong model!\n", .{});
            break;
        }
    }

    // put into moca
    // if error, cnfdd. else, continue
    // put into checkmodel
    // if error, put into error folder
    // in zig-out, have fuzz folder.
    // every file is just the seed that was used for cnfuzz.
    // The contents are either stderr or output from checkmodel
    return 0;
}
