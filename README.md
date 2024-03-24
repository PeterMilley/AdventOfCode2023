# AdventOfCode2023
An incredibly overwrought way to solve Advent Of Code 2023.

I've never written my own toy language, and writing one to solve Advent Of Code has been a bucket list item for me for a long time.

The language implemented by this interpreter is a Scheme-like, I guess? It's a functional, interpreted language that I wouldn't wish on my worst enemy.

Seriously, this language isn't recommended for use by anyone, ever, except maybe actual functional language experts who want to laugh at me.

# language basics
Everything is an s-expression. Comments are delimited by square brackets.

Base types: 64-bit ints, strings, characters, booleans, and unit.

Compound types: NONE. Seriously. You have to roll your own out of functions! Except there's a tiny bit of support for lists, see below.

Keywords: `let`, `\\` (read 'lambda'), `macro`, 'if', 'trace', 'load', 'fail'.
When evaluating lambda functions, the args get evaluated first then bound to the lambda variables. When evaluating macros, the args are left as an unevaluated closure until needed.

Builtin functions: `print`, `itoa` (number to string), `strcat`, `ord` (char to number), `chr` (number to char), `chars` (string to list of chars) and `list` (convenience function to construct lists).

A "list" is a _function_ that acts as a right fold. The _only_ way to consume a list is with a right fold.

You've been warned. The error messages are atrocious and the performance is lousy. Don't use this for anything.
