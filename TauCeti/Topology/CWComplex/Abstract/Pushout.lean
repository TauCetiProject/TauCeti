/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.RelativeCellComplex.Pushout
public import TauCeti.Topology.CWComplex.Abstract.Classical
public import TauCeti.Topology.CWComplex.Abstract.ClosedEmbedding

/-!
# Attaching a relative CW complex along a map

Let `c : TopCat.RelativeCWComplex f` present `Y` as obtained from `X` by attaching cells along
`f : X ⟶ Y`, and let

```
X --f--> Y
|        |
a        b
v        v
Z --f'-> P
```

be a pushout square in `TopCat`, so that `P` is the adjunction space `Z ∪ₐ Y`, with the quotient
topology. Then `f'` is a relative CW complex attaching the same cells to `Z`
(`TopCat.RelativeCWComplex.ofIsPushout`), and its characteristic maps are those of
`c` followed by `b`. No cell structure on `Z` is needed. Consequently:

* `f' : Z ⟶ P` is a closed embedding (`TopCat.RelativeCWComplex.isClosedEmbedding_of_isPushout`);
* `P` is Hausdorff when `Z` is (`TopCat.RelativeCWComplex.t2Space_of_isPushout`);
* `P` carries a classical relative CW structure relative to the range of `f'`, namely
  `(c.ofIsPushout sq).toRelCWComplex`, whose `n`-cells, like those of `c.toRelCWComplex`, are the
  cells attached by `c` at stage `n`, and whose characteristic maps are those of
  `c.toRelCWComplex` followed by `b` (`TopCat.RelativeCWComplex.map_toRelCWComplex_ofIsPushout`).

The open cells of `P` are thus the images under `b` of the open cells of `Y`, and they are disjoint
from the image of `Z`.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 (attaching spaces) and the Appendix (the topology
  of cell complexes).
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology Set

namespace TopCat.RelativeCWComplex

variable {X Y Z P : TopCat.{u}} {f : X ⟶ Y} (c : RelativeCWComplex f) {a : X ⟶ Z} {b : Y ⟶ P}
  {f' : Z ⟶ P} (sq : IsPushout f a b f')

/-- **Attaching a relative CW complex along a map.** If `f'` is a pushout of a relative CW
complex `f` in `TopCat`, then `f'` is a relative CW complex attaching the cells of `f`. This is
`HomotopicalAlgebra.RelativeCellComplex.ofIsPushout`, typed as a `TopCat.RelativeCWComplex` so
that the API of relative CW complexes in `TopCat` applies to it. -/
noncomputable abbrev ofIsPushout : RelativeCWComplex f' :=
  HomotopicalAlgebra.RelativeCellComplex.ofIsPushout c sq

include c sq in
/-- **Attaching a relative CW complex along a map is a closed embedding.** If `f'` is a pushout of
a relative CW complex `f` in `TopCat`, then `f'` is a closed embedding. -/
theorem isClosedEmbedding_of_isPushout : IsClosedEmbedding f' :=
  (c.ofIsPushout sq).isClosedEmbedding

include c sq in
/-- **Attaching a relative CW complex to a Hausdorff space gives a Hausdorff space.** If `f'` is a
pushout of a relative CW complex `f` in `TopCat` and the source of `f'` is Hausdorff, then so is
its target. -/
theorem t2Space_of_isPushout [T2Space Z] : T2Space P :=
  (c.ofIsPushout sq).t2Space

/-- **The characteristic maps of a pushout.** The characteristic map of an `n`-cell of the
classical relative CW structure on the pushout of `c` along `a` is the characteristic map of the
corresponding cell of `c` followed by `b`. The cells of both structures are indexed by the cells
attached at stage `n` of `c`. -/
theorem map_toRelCWComplex_ofIsPushout (n : ℕ) (k : (c.attachCells n (not_isMax n)).ι)
    (x : Metric.closedBall (0 : Fin n → ℝ) 1) :
    (c.ofIsPushout sq).toRelCWComplex.map n
        (((c.ofIsPushout sq).toRelCWComplexCellEquiv n).symm k) x =
      b (c.toRelCWComplex.map n ((c.toRelCWComplexCellEquiv n).symm k) x) := by
  rw [toRelCWComplex_map_apply, toRelCWComplex_map_apply, Equiv.apply_symm_apply]
  -- The cells of `c.ofIsPushout sq` attached at stage `n` are those of `c` only up to unfolding,
  -- so the index is generalized before it is identified with `k`.
  generalize hk : ((c.ofIsPushout sq).toRelCWComplexCellEquiv n)
    (((c.ofIsPushout sq).toRelCWComplexCellEquiv n).symm k) = k'
  obtain rfl : k' = k := hk.symm.trans (Equiv.apply_symm_apply _ _)
  exact ConcreteCategory.congr_hom
    (HomotopicalAlgebra.RelativeCellComplex.Cells.ι_ofIsPushout_mk c sq n (not_isMax n) k') _

end TopCat.RelativeCWComplex
