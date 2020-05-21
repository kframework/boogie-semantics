Conclusion
==========

We have defined a formal semantics for a subset of Boogie, supporting many
nontrivial verification features. This semantics can be extended to a full
semantics of Boogie, to be used to verify the primary implementation of Boogie,
as well as the correctness of programs translated into Boogie from higher-level
languages such as Dafny.

Moving forward, we hope that verifications engines can be generated directly from
a languages' \K semantics, avoiding the many bugs that can occur when developers
implement their execution and verification semantics independently.
