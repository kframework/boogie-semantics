---
title: Semantics of Boogie in \K
author: 
    - Seth Poulsen (sethp3@illinois.edu)
    - Nishant Rodrigues (nishant2@illinois.edu)
header-include:  \newcommand{\K}{$\mathbb{K}$}
links-as-notes: true
---

\tableofcontents

Introduction
============

In this project, we present an executable formal semantics for
[Boogie](https://github.com/boogie-org/boogie), an intermediate
language for verification. We choose to implement this in the [\K
Framework] because of its semantics-first approach, and our belief that
this approach extends to verification languages.

The semantics of Boogie were informally defined in the paper ["This is Boogie
2"](https://www.microsoft.com/en-us/research/publication/this-is-boogie-2-2/).
Our semantics follows the semantics as defined there as much as possible, adding
increased formality where the informal semantics are vague.

Eventually, we hope to support the full Boogie test suite, and use this
semantics both to verify the primary Boogie tests, as well as to verify
correctness of the translation programs translated to Boogie from the
higher-level languages (such as [Dafny])

Our ultimate goal is, however, more ambitious. We aim to extend \K so
that we can derive annotation based verification engines directly from a
languages' \K semantics with minimal changes. This will do away with the
need for a translation of the source language to an intermediate language,
and with it the pitfalls of writing multiple implementations of the language.

[\K Framework]: http://www.kframework.org/index.php/Main_Page
[Dafny]: https://www.microsoft.com/en-us/research/project/dafny-a-language-and-program-verifier-for-functional-correctness/

Current support
===============

-   Integer and Boolean types
-   `assert` & `assume` statements
-   Traditional imperative control flow
-   `invariant`, `requires` and `ensures` specifications
-   `old()` expressions
-   Non-deterministic `if` statements and `while` loops
-   Non-deterministic assignment of variables using `havoc`
-   `call` statements

Building
========

To build the semantics and run the tests, first install the
[ninja](https://ninja-build.org/) build system, and all the dependencies for the
K Framework as described on [their github page][kframework-github]. Then clone this repository and run

``` {.sh}
./build 
```

The build script will download and build the K Framework, then use it to build
and execute the Boogie semantics.

[kframework-github]: https://github.com/kframework/k
