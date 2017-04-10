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

All Haskell code in `ghc-prim`, `integer-gmp` and `base` compiles. What does
not work:

 * In out-of-memory (or out-of-stack?) situations, the program segfaults.
 * Many primitive operations and FFI calls are not implemented, and will abort
   the program with a descriptive message when used. Let me know if you are
   missing something specific. This includes all the `Integer` functions, so
   use `Int`.
 * At the moment, we implement call-by-name (thunks do not update themselves).
 * No garbage collection (it may be that this will not ever change).

The resulting programs will be much slower than with any other Haskell compiler
out there!

Installation
------------

 * Ensure that `ghc` is GHC version 8.0, and that `clang-4.0` is in your path.
 * Clone the repository
 * Run `./boot.sh some-directory`.
 * You can now use `some-directory/bin/veggies` like you would use `ghc`.

You can use it with `cabal` by passing `-w some-directory/bin/veggies` to
`cabal configure`.

Heap layout and calling convention
----------------------------------

Every object is a pointer (`%hs*`). Even unboxed values (`Int#`) are hidden
behind a pointer. This makes stuff very uniform.

Every heap object is of the form `{%hs* (%hs*)*, …}`, where the first field is
the *enter function*. It always returns something evaluated. Unlifted types,
who should not be entered, also have an enter function, but that one aborts the
program. This is for consistency and error checking.

The two types of unevaluated closures are:

 * A thunk is represented as `{%hs* (%hs*)* enter, [1 x %hs*] captured_variables}`.
   Even if the thunk does not capture a single variable, the allocated memory
   must allow for one (to override it with an indirection).
   The `enter` is called with the pointer to the thunk as an argument. It will
   evaluate the expression, override the thunk with an indirection to the
   result, and return a pointer to the result.
 * An indirection is represented as `{%hs* (%hs*)* enter, %hs* indirectee}`.
   The `enter` is called with the pointer to the indirection as an argument,
   and will simply call the code of that.

The enter function for value closures is always the same, and simply returns
the pointer to the object.

 * A data constructor is represented as `{%hs* (%hs*)* enter, i64 tag, [0 x
   %hs*] args}`, where the tag is positive and indicates which data constructor
   we have.
 * An `Int#` value is represented as `{%hs* (%hs*)* enter, i64 val}`. Similarly
   for other primitive values (`Char#`, `Addr#`).
 * A function closure is represented as `{%hs* (%hs*)* enter, %hs* (%hs*, [0 x
   %hs*])* fun, i64 arity, [0 x %hs*] captured_vars}`, where the `fun` is a
   function pointer. The function expects the closure as the first argument (to
   access the capture variables), and a pointer to precisely `arity` further
   arguments.

Every function call should go through `rts_call` which compares the number of
arguments with the arity of and either calls the function, possibly passing
left-over arguments to the result, or creates a PAP (partial application)
closure.


Contact
-------

Contact Joachim Breitner <<joachim@cis.upenn.edu>> if you have questions.
