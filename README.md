# Bishop – an agda2hs rewrite

This branch has the goal of rewriting Zachary Murray's formalisation of Bishop's analysis to make it compatible with `agda2hs` and therefore efficiently compilable. Actually, this is rather a demonstration of how to rewrite large libraries to be compatible with `agda2hs` (and the fact that this can be done).

It's done up until the definition of `e`. However, trying to calculate it does not terminate in reasonable time. The probable cause is that rational addition involves multiplying very large Integers, which is too time-consuming. This also means that Bishop's representation of reals is **not** suitable for usable exact-real arithmetic. See `investigation/investigation.txt` for details.
