---
title: Semantics of Boogie in K
author: 
    - Seth Poulsen (sethp3@illinois.edu)
    - Nishant Rodrigues (nishant2@illinois.edu)
---

This repository contains an executable formal semantics for the
[Boogie](https://github.com/boogie-org/boogie) intermediate verification
language, defined using the [K
Framework](http://www.kframework.org/index.php/Main_Page)

The semantics of Boogie were informally defined in the paper ["This is Boogie
2"](https://www.microsoft.com/en-us/research/publication/this-is-boogie-2-2/).
Our semantics follows the semantics as defined there as much as possible, adding
increased formality where the informal semantics are vague.

Eventually, we hope to support the full Boogie test suite, and use this
semantics both to verify the primary Boogie implementation, as well as to verify
correctness of the translation to Boogie from the higher-level languages that
use it (like
[Dafny](https://www.microsoft.com/en-us/research/project/dafny-a-language-and-program-verifier-for-functional-correctness/))

Currently Supported Features
============================

-   Integer data types
-   Control flow
-   Non-deterministic `if` statements
-   Non-deterministic `while` loops
-   Non-deterministic assignment of variables using `havoc`
-   Algebraic data types
-   Assertions
-   Loop invariants
-   Procedures

Not Yet Supported
=================

Data Types
----------

-   Maps
-   Bitvectors
-   Strings

Verification constructs
-----------------------

-   Axioms
-   Quantifiers (`forall` and `exists`) in assertions
-   the `call forall` construct
-   the `old` operator
-   marking specifications as `free`

Building
========

To build the semantics and run the tests, first install the
[ninja](https://ninja-build.org/) build system, and all the dependencies for the
K Framework as described on [their github
page](https://github.com/kframework/k). Then clone this repository and run

``` {.sh}
./build 
```

The build script will download and build the K Framework, then use it to build
and execute the Boogie semantics.

