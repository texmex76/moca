const std = @import("std");

pub fn build(b: *std.Build) void {
    // Main executable
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const exe = b.addExecutable(.{
        .name = "moca",
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    exe.linkSystemLibrary("c");

    // Options
    const options = b.addOptions();
    options.addOption(bool, "debug", b.option(bool, "debug", "Debug mode. This will enable logging.") orelse false);
    exe.root_module.addOptions("config", options);

    b.installArtifact(exe);
    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| {
        run_cmd.addArgs(args);
    }
    const run_step = b.step("run", "Run the moca local search solver");
    run_step.dependOn(&run_cmd.step);

    // Fuzz
    const fuzz_exe = b.addExecutable(.{
        .name = "fuzz",
        .root_source_file = b.path("src/fuzz.zig"),
        .target = target,
        .optimize = optimize,
    });
    fuzz_exe.linkLibC();
    b.installArtifact(fuzz_exe);
    const run_fuzz = b.addRunArtifact(fuzz_exe);
    run_fuzz.step.dependOn(b.getInstallStep());
    if (b.args) |args| {
        run_fuzz.addArgs(args);
    }
    const run_fuzz_step = b.step("fuzz", "Fuzz the local search solver");
    run_fuzz_step.dependOn(&run_fuzz.step);

    // Checkmodel
    const check_exe = b.addExecutable(.{
        .name = "checkmodel",
        .target = target,
    });
    check_exe.addCSourceFile(.{ .file = b.path("src/checkmodel.cpp") });
    check_exe.linkLibCpp();
    b.installArtifact(check_exe);
    const run_check_cmd = b.addRunArtifact(check_exe);
    run_check_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| {
        run_check_cmd.addArgs(args);
    }
    const run_check_step = b.step("check", "Run checkmodel");
    run_check_step.dependOn(&run_check_cmd.step);

    // Generate
    const gen_exe = b.addExecutable(.{
        .name = "generate",
        .target = target,
    });
    gen_exe.addCSourceFile(.{ .file = b.path("src/generate.cpp") });
    gen_exe.linkLibCpp();
    b.installArtifact(gen_exe);
    const run_gen_cmd = b.addRunArtifact(gen_exe);
    run_gen_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| {
        run_gen_cmd.addArgs(args);
    }
    const run_gen_step = b.step("gen", "Run generate");
    run_gen_step.dependOn(&run_gen_cmd.step);

    // Testing
    const exe_unit_tests = b.addTest(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    exe_unit_tests.linkSystemLibrary("c");
    exe_unit_tests.root_module.addOptions("config", options);
    const run_exe_unit_tests = b.addRunArtifact(exe_unit_tests);
    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_exe_unit_tests.step);
}
