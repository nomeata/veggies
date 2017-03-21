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


Contact
-------

Contact Joachim Breitner <<joachim@cis.upenn.edu>> if you have questions.
