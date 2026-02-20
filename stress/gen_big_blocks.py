#!/usr/bin/env python3
"""Generate a ~20,000 line .ecs stress test with ~50 functions having large bodies."""

import sys
import random

random.seed(42)

lines = []

NUM_FUNCS = 50
BODY_LINES_PER_FUNC = 350  # 50 * 350 = 17500 lines in functions
MAIN_BODY_LINES = 2000


def arith_expr(depth=0):
    """Generate a random arithmetic expression."""
    ops = ["+", "-", "*"]
    if depth > 2 or random.random() < 0.4:
        return str(random.randint(1, 1000))
    left = arith_expr(depth + 1)
    right = arith_expr(depth + 1)
    op = random.choice(ops)
    return f"({left} {op} {right})"


def gen_function_body(num_lines):
    """Generate a function body with local variables, arithmetic, and control flow."""
    body = []
    var_count = 0

    def new_var():
        nonlocal var_count
        var_count += 1
        return f"v{var_count}"

    # Initialize a few accumulators
    accums = []
    for _ in range(4):
        name = new_var()
        accums.append(name)
        body.append(f"    let {name}: int = 0;")

    i = 0
    while i < num_lines:
        choice = random.random()

        if choice < 0.35:
            name = new_var()
            expr = arith_expr()
            body.append(f"    let {name}: int = {expr};")
            acc = random.choice(accums)
            op = random.choice(["+", "-"])
            body.append(f"    {acc} = {acc} {op} {name};")
            i += 2

        elif choice < 0.55:
            cond_var = random.choice(accums)
            threshold = random.randint(-500, 500)
            name1 = new_var()
            name2 = new_var()
            block = [
                f"    if {cond_var} > {threshold} {{",
                f"        let {name1}: int = {arith_expr()};",
                f"        {cond_var} = {cond_var} + {name1};",
            ]
            for _ in range(random.randint(3, 8)):
                inner = new_var()
                block.append(f"        let {inner}: int = {arith_expr()};")
                block.append(f"        {cond_var} = {cond_var} - {inner};")
            block.append(f"    }} else {{")
            block.append(f"        let {name2}: int = {arith_expr()};")
            block.append(f"        {cond_var} = {cond_var} - {name2};")
            for _ in range(random.randint(2, 5)):
                inner = new_var()
                block.append(f"        let {inner}: int = {arith_expr()};")
                block.append(f"        {cond_var} = {cond_var} + {inner};")
            block.append(f"    }}")
            body.extend(block)
            i += len(block)

        elif choice < 0.70:
            loop_var = new_var()
            acc = random.choice(accums)
            iters = random.randint(3, 10)
            block = [
                f"    let {loop_var}: int = 0;",
                f"    while {loop_var} < {iters} {{",
            ]
            for _ in range(random.randint(2, 6)):
                inner = new_var()
                block.append(f"        let {inner}: int = {arith_expr()};")
                block.append(f"        {acc} = {acc} + {inner};")
            block.append(f"        {loop_var} = {loop_var} + 1;")
            block.append(f"    }}")
            body.extend(block)
            i += len(block)

        elif choice < 0.85:
            prev = random.choice(accums)
            chain_len = random.randint(4, 10)
            for _ in range(chain_len):
                name = new_var()
                op = random.choice(["+", "-", "*"])
                val = random.randint(1, 100)
                body.append(f"    let {name}: int = {prev} {op} {val};")
                prev = name
            acc = random.choice(accums)
            body.append(f"    {acc} = {acc} + {prev};")
            i += chain_len + 1

        else:
            acc = random.choice(accums)
            t1 = random.randint(-100, 100)
            t2 = random.randint(-100, 100)
            block = [
                f"    if {acc} > {t1} {{",
                f"        if {acc} < {t2} {{",
            ]
            for _ in range(random.randint(2, 5)):
                inner = new_var()
                block.append(f"            let {inner}: int = {arith_expr()};")
                block.append(f"            {acc} = {acc} + {inner};")
            block.append(f"        }} else {{")
            inner = new_var()
            block.append(f"            let {inner}: int = {arith_expr()};")
            block.append(f"            {acc} = {acc} - {inner};")
            block.append(f"        }}")
            block.append(f"    }}")
            body.extend(block)
            i += len(block)

    return body, accums


# Generate 50 functions
func_names = []

for fi in range(NUM_FUNCS):
    fname = f"compute_{fi}"
    func_names.append(fname)
    lines.append(f"fn {fname}(seed: int) -> int {{")
    body, accums = gen_function_body(BODY_LINES_PER_FUNC)
    lines.extend(body)
    lines.append(f"    {accums[0]} = {accums[0]} + seed;")
    ret = " + ".join(accums)
    lines.append(f"    return {ret};")
    lines.append(f"}}")
    lines.append(f"")

# Generate main
lines.append("fn main() {")
lines.append("    let total: int = 0;")
lines.append("    let temp: int = 0;")

for fname in func_names:
    seed = random.randint(1, 10000)
    lines.append(f"    temp = {fname}({seed});")
    lines.append(f"    total = total + temp;")

lines.append("")

# Main accumulators
accums_main = ["total", "temp"]
main_var_count = 0
for _ in range(3):
    main_var_count += 1
    name = f"m{main_var_count}"
    accums_main.append(name)
    lines.append(f"    let {name}: int = 0;")

remaining = MAIN_BODY_LINES - len(func_names) * 2
i = 0
while i < remaining:
    choice = random.random()

    if choice < 0.4:
        main_var_count += 1
        name = f"m{main_var_count}"
        expr = arith_expr()
        lines.append(f"    let {name}: int = {expr};")
        acc = random.choice(accums_main)
        op = random.choice(["+", "-"])
        lines.append(f"    {acc} = {acc} {op} {name};")
        i += 2

    elif choice < 0.6:
        acc = random.choice(accums_main)
        threshold = random.randint(-500, 500)
        main_var_count += 1
        n1 = f"m{main_var_count}"
        main_var_count += 1
        n2 = f"m{main_var_count}"
        block = [
            f"    if {acc} > {threshold} {{",
            f"        let {n1}: int = {arith_expr()};",
            f"        {acc} = {acc} + {n1};",
        ]
        for _ in range(random.randint(3, 6)):
            main_var_count += 1
            inner = f"m{main_var_count}"
            block.append(f"        let {inner}: int = {arith_expr()};")
            block.append(f"        {acc} = {acc} - {inner};")
        block.append(f"    }} else {{")
        block.append(f"        let {n2}: int = {arith_expr()};")
        block.append(f"        {acc} = {acc} - {n2};")
        block.append(f"    }}")
        lines.extend(block)
        i += len(block)

    elif choice < 0.75:
        main_var_count += 1
        loop_var = f"m{main_var_count}"
        acc = random.choice(accums_main)
        iters = random.randint(3, 8)
        block = [
            f"    let {loop_var}: int = 0;",
            f"    while {loop_var} < {iters} {{",
        ]
        for _ in range(random.randint(2, 4)):
            main_var_count += 1
            inner = f"m{main_var_count}"
            block.append(f"        let {inner}: int = {arith_expr()};")
            block.append(f"        {acc} = {acc} + {inner};")
        block.append(f"        {loop_var} = {loop_var} + 1;")
        block.append(f"    }}")
        lines.extend(block)
        i += len(block)

    else:
        prev = random.choice(accums_main)
        chain_len = random.randint(4, 8)
        for _ in range(chain_len):
            main_var_count += 1
            name = f"m{main_var_count}"
            op = random.choice(["+", "-", "*"])
            val = random.randint(1, 100)
            lines.append(f"    let {name}: int = {prev} {op} {val};")
            prev = name
        acc = random.choice(accums_main)
        lines.append(f"    {acc} = {acc} + {prev};")
        i += chain_len + 1

lines.append("")
lines.append("    print(total);")
lines.append("}")

output = "\n".join(lines) + "\n"
print(f"Generated: {len(lines)} lines", file=sys.stderr)

with open("stress/big_blocks.ecs", "w") as f:
    f.write(output)
