---
title: Semantics of Boogie in \K
author:
    - Seth Poulsen (sethp3@illinois.edu)
    - Nishant Rodrigues (nishant2@illinois.edu)
header-include:  \newcommand{\K}{$\mathbb{K}$}
links-as-notes: true
geometry: margin=1in
---

Introduction
============

In this project, we present an executable formal semantics for
[Boogie](https://github.com/boogie-org/boogie), an intermediate language for verification.
We choose to implement this in the [\K Framework] because of its semantics-first approach,
and our belief that this approach extends to verification languages.

Indeed, we believe that \K's approach removes the need for verification languages
and that we can implement verification constructs tailored to a language within
\K itself, with only a little effort beyond the language semantics itself.
This will do away with the
need for a translation of the source language to an intermediate language,
and with it the pitfalls of writing multiple implementations of the language.

To prove that we are in fact capable of everything Boogie is,
we define such an executable semantics for Boogie itself.
The semantics of Boogie were informally defined in the paper "[This is Boogie 2]".
Our semantics follows the semantics as defined there as much as possible,
adding increased formality where the informal semantics are vague. The section
numbering in the Syntax and Semantics listed in this document also follows the
section numbering from "This is Boogie 2." Since the

[This is Boogie 2]: https://www.microsoft.com/en-us/research/publication/this-is-boogie-2-2/
[\K Framework]: http://www.kframework.org/index.php/Main_Page

Organization
============

The source code of our semantics is organized as follows:

* [syntax.md] contains the formal grammar for the Boogie language.
* [boogie.md] contains the majority of the semantics.
* Since Boogie is a verification language, there are a few features
  that rely on a "meta-level" implementations.
  First, to present the results of verifying a program we must consider
  the result of all possible executions of our program
  (as opposed to a traditional language where we only care about a single execution trace).
  This is done in [driver/driver.md].

  Second, Boogie allows quantification.
  This involves symbolically executing our program, and considering all possible instantiations
  of the quantified variables.  This is done in [quantification.md]. 
 
Building
========

To build the semantics and run the tests, first install the
[ninja](https://ninja-build.org/) build system, and all the dependencies for the
K Framework as described on [their github page][kframework-github]. Then clone this repository and run

``` {.sh}
./build
```

The build script will download and build the \K Framework, then use it to build
and execute the Boogie semantics.

[kframework-github]: https://github.com/kframework/k

Running `./docker-dev` will also build a Docker image with all dependencies installed.

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

