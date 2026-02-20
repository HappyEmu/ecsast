use std::{fs, process::Command};

use cranelift_object::ObjectProduct;

pub fn link_program(
    program: ObjectProduct,
    output_path: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let obj_bytes = program.emit()?;
    let obj_path = format!("{output_path}.o");
    fs::write(&obj_path, obj_bytes)?;

    // Write and compile C runtime
    let rt_c_path = format!("{output_path}_rt.c");
    let rt_o_path = format!("{output_path}_rt.o");
    fs::write(&rt_c_path, RUNTIME_C)?;

    let status = Command::new("cc")
        .args(["-c", &rt_c_path, "-o", &rt_o_path])
        .status()?;

    if !status.success() {
        return Err("compiling runtime failed".into());
    }

    let status = Command::new("cc")
        .args([&obj_path, &rt_o_path, "-o", output_path, "-lm"])
        .status()?;

    if !status.success() {
        return Err("linking failed".into());
    }

    fs::remove_file(&obj_path)?;
    fs::remove_file(&rt_c_path)?;
    fs::remove_file(&rt_o_path)?;

    Ok(())
}

const RUNTIME_C: &str = r#"
#include <stdio.h>
#include <math.h>
void print_int(long n) { printf("%ld\n", n); }
void print_float(double n) { printf("%g\n", n); }
void print_str(const char *s, long len) { fwrite(s, 1, len, stdout); fputc('\n', stdout); }
static int g_argc;
static char **g_argv;
void ecsast_init_args(int argc, char **argv) { g_argc = argc; g_argv = argv; }
long ecsast_argc(void) { return g_argc; }
void ecsast_arg(long i, const char **out_ptr, long *out_len) {
    *out_ptr = g_argv[i];
    long len = 0; while (g_argv[i][len]) len++;
    *out_len = len;
}
long ecsast_ipow(long base, long exp) {
    long result = 1;
    while (exp > 0) {
        if (exp & 1) result *= base;
        base *= base;
        exp >>= 1;
    }
    return result;
}
double ecsast_fpow(double base, double exp) { return pow(base, exp); }
double ecsast_fmod(double a, double b) { return fmod(a, b); }
"#;
