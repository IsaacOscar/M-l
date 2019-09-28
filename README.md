A prototype implementation of the Mμl multi-method programming language, as described in the paper "Mμl: The Power of Dynamic Multi-Methods", presented at the Workshop on Meta-Programming Techniques and Reflection (META’19).

# Instructions:
1. Install `racket`
2. install `brag` (using `raco pkg install brag`)
3. Run `racket paper-code.mμl` (or run racket on any other Mμl file)
5. Wait for your code to finish running, the implementation is quite slow, so be patient!

# Files:
1. `compiler.rkt`: a "compiler" that can be used with rackets `#lang` directive, it will lex, parse and desugar a Mμl file into an AST, that is then wrappep into racket code, that when executed will parse the Mμl ast to our redex implementation (see below).
2. `grammar.rkt`: the production rules for the grammar (written in brag)
3. `runtime.rkt`: the "runtime", a straightforward implementation of our reduction rules, written in PLT Redex.
4. `paper-code.mμl`: all the Mμl code in the paper, together with checks that expressions produce the correct values.

# Syntax:
The syntax is as shown in the paper, in addition:
* The first line of your file must be `#lang reader "compiler.rkt"`
* An identifier must start with a unicode letter, and can contain any number of extra letters, numbers or `-`s
* A string literal cannot contain any double quotation marks (`"`s), and does not recognise any escape sequences
* A single-line comment starts with `//` and ends at the next newline (a newline *must* be before the end of file)
* A multi-line comment starts with `/*` and ends at the next occurence `*/` (they do not nest)
* Any Unicode whitespace characters are ignored and only serve to sperate tokens.
* The entire file must be an expression, in particular, it must not end in a semicolon, or be empty.
