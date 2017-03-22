veggies (for Verified GHC)
==========================

This repository contains an attempt to replace GHC’s code generator (i.e.
everything that comes between Core and LLVM IR) with a very naive and
straight-forward implementation that is so simple, we can prove it correct.

The correctness proof eventually ought to bridge the gap between CoreSpec (the
Haskell Core formalization) and VeLLVM (the verified LLVM project) in the
DeepSpec project.

Current state
-------------

Currently, it replaces the code generator with one that creates an empty LLVM
file. Interestingly, a lot of stuff still works (besides actually running the
code). This is because GHC never actually uses the resulting binaries, only the
`.hi` file, which gets created before code generation.

Installation
------------

 * Ensure that `ghc` is GHC version 8.0, and that `clang-3.9` is in your path.
 * Clone the repository
 * Run `./boot.sh some-directory`.
 * You can now use `some/directory/bin/veggies`.

Heap layout and calling convention
----------------------------------

Every object is a pointer (`i8*`, in the following also called `hs*`). Even unboxed values (`Int#`) are hidden
behind a pointer. This makes stuff very uniform.

Every heap object is of the form `{hs* code, … }`.

The two types of unevaluated closures are:

 * A thunk is represented as `{hs* code, hs*[] captured_vars}`.
   The tag is ignored.
   Even if the thunk does not capture a single variable, the allocated memory must allow for one (to override it with an indirection).
   The `code` is called with the pointer to the thunk as an argument. It will
   evaluate the expression, override the thunk with an indirection to the
   result, and return a pointer to the result.
 * An indirection is represented as `{hs* code, hs* indirectee}`.
   The `code` is called with the pointer to the indirection as an argument, and will simply call the code of that.

The code for value closures is always the same, and simply returns the pointer to the object.

 * A data constructor is represented as `{hs* code, i64 tag, hs*[] args}`, where the
   tag is positive and indicates which data constructor we have.
 * An `Int#` value is represented as `{hs* code, i64 val}`.
 * A function closure is represented as `{hs* code, hs*fun, i64 arity, hs*[] captured_vars}`, where the
   `fun` is a function pointer. The function expects the `captured_vars` pointer as the first argument, and `arity` further arguments of type `hs*[]`.

How are we handling over- and undersaturated functions so far? Not at all!



Contact
-------

Contact Joachim Breitner <<joachim@cis.upenn.edu>> if you have questions.
