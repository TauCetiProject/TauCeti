/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Compact
import TauCeti.Algebra.Category.ModuleCat.Finrank

/-!
# Euler characteristic of a compact manifold as a sum of Betti numbers

The Euler--Poincaré formula expresses the Euler characteristic of a space `M` of finite CW type
as the alternating sum of the dimensions of its singular homology over any division ring `k`. If
`M` is a compact Hausdorff space charted on a real normed space of dimension `n`, its homology
vanishes above degree `n`, so `eulerChar M = ∑ᵢ₌₀ⁿ (-1)ⁱ dim Hᵢ(M; k)`. If moreover `M` is a
connected surface then `H₀(M; k) = k`, and this reads `eulerChar M = 1 - b₁ + b₂`.

Finite CW type is an instance argument; for a compact smooth manifold it is supplied by
`TauCeti.FiniteCWType.of_isManifold`. These statements do not assert anything about the top
Betti number, which needs an orientation (see
`TauCeti.HomologicalOrientation.eulerChar_eq_two_sub_finrank_singularHomology_one`).

## Main results

* `TauCeti.eulerChar_eq_sum_range_finrank_singularHomology`: the Euler characteristic of a compact
  manifold is the alternating sum of its Betti numbers up to its dimension.
* `TauCeti.eulerChar_eq_one_sub_finrank_add_finrank`: a compact connected surface has
  `eulerChar M = 1 - b₁ + b₂`.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 2.44 and Proposition 3.29.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Module

universe u

namespace TauCeti

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (M : Type u) [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace E M]
  [FiniteCWType M] (k : Type u) [DivisionRing k]

/-- **The Euler characteristic of a compact manifold as an alternating sum of Betti numbers.**
For a compact Hausdorff space `M` of finite CW type charted on a real normed space of dimension
`n`, and any division ring `k`, `eulerChar M = ∑ᵢ₌₀ⁿ (-1)ⁱ dim Hᵢ(M; k)`. -/
theorem eulerChar_eq_sum_range_finrank_singularHomology :
    eulerChar M = ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i *
      finrank k (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (ModuleCat.of k k)).obj
        (TopCat.of M)) := by
  rw [eulerChar_eq_finsum_finrank_singularHomology M k,
    ModuleCat.finsum_neg_one_pow_finrank_eq_sum_range (N := finrank ℝ E + 1) fun i hi ↦
      isZero_singularHomology_of_compactSpace (M := M) (E := E) _ rfl (by omega)]

/-- **The Euler characteristic of a compact connected surface is `1 - b₁ + b₂`.** For a compact
connected Hausdorff space `M` of finite CW type charted on a real normed space of dimension `2`,
and any division ring `k`, `eulerChar M = 1 - dim H₁(M; k) + dim H₂(M; k)`. The zeroth Betti
number is `1` because `M` is path connected. -/
theorem eulerChar_eq_one_sub_finrank_add_finrank [ConnectedSpace M] (hE : finrank ℝ E = 2) :
    eulerChar M = 1 -
      (finrank k (((singularHomologyFunctor (ModuleCat.{u} k) 1).obj (ModuleCat.of k k)).obj
        (TopCat.of M)) : ℤ) +
      finrank k (((singularHomologyFunctor (ModuleCat.{u} k) 2).obj (ModuleCat.of k k)).obj
        (TopCat.of M)) := by
  have := ChartedSpace.locallyPathConnectedSpace E M
  have : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  have h₀ : finrank k
      (((singularHomologyFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)).obj
        (TopCat.of M)) = 1 := by
    rw [(asIso ((TopCat.of M).singularHomology₀ε (ModuleCat.of k k))).toLinearEquiv.finrank_eq]
    exact finrank_self k
  rw [eulerChar_eq_sum_range_finrank_singularHomology (E := E) M k, hE]
  simp [Finset.sum_range_succ, h₀]
  ring

end TauCeti
