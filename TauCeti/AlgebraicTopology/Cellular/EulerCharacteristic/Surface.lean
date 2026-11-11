/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass

/-!
# Euler characteristic of a closed oriented surface

A compact connected Hausdorff surface with a homological orientation has rational Betti numbers
`b₀ = b₂ = 1` and `bᵢ = 0` for `i > 2`. If it has finite CW type, the native Euler--Poincaré
formula therefore gives `χ = 2 - b₁`, and in particular `χ ≤ 2`.

The surface is a topological manifold charted on a real two-dimensional normed space, with no
boundary. Its orientation is the genuine native `TauCeti.HomologicalOrientation`, not an assumed
Betti-number computation. The top Betti number follows from the rational fundamental-class
isomorphism; the zeroth follows from connectedness and the local path connectedness of charts;
the higher homology vanishes by the compact-manifold local-homology theorem. Finite CW type is
an explicit hypothesis, and also ensures the first homology is finite-dimensional.

These statements do not assert evenness of `b₁` or construct a genus. Those require the
nondegenerate alternating cup pairing supplied by Poincaré duality. Conversion of a smooth
manifold orientation to a homological orientation and construction of a finite CW model are
separate inputs.

## References

* A. Hatcher, *Algebraic Topology*, Sections 2.2 and 3.3.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Module

namespace TauCeti.HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [FiniteCWType M] (o : HomologicalOrientation M E 2) (hn : finrank ℝ E = 2)

include o hn

/-- **The Euler characteristic of a closed oriented surface is `2 - b₁`.** The finite CW model
and the genuine homological orientation are explicit inputs; all required homology ranks and
vanishing are derived from the manifold hypotheses. -/
theorem eulerChar_eq_two_sub_finrank_singularHomology_one :
    eulerChar M = 2 - (finrank ℚ
      (((singularHomologyFunctor (ModuleCat.{0} ℚ) 1).obj (ModuleCat.of ℚ ℚ)).obj
        (TopCat.of M)) : ℤ) := by
  have := ChartedSpace.locallyPathConnectedSpace E M
  have : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  have h₀ : finrank ℚ
      (((singularHomologyFunctor (ModuleCat.{0} ℚ) 0).obj (ModuleCat.of ℚ ℚ)).obj
        (TopCat.of M)) = 1 := by
    rw [(asIso ((TopCat.of M).singularHomology₀ε (ModuleCat.of ℚ ℚ))).toLinearEquiv.finrank_eq]
    exact finrank_self ℚ
  have h₂ : finrank ℚ
      (((singularHomologyFunctor (ModuleCat.{0} ℚ) 2).obj (ModuleCat.of ℚ ℚ)).obj
        (TopCat.of M)) = 1 := by
    rw [(o.rationalFundamentalClassEquiv hn).symm.finrank_eq]
    exact finrank_self ℚ
  rw [eulerChar_eq_finsum_finrank_singularHomology M ℚ,
    ModuleCat.finsum_neg_one_pow_finrank_eq_sum_range (N := 3)
      (fun i hi ↦ isZero_singularHomology_of_compactSpace (M := M) (E := E)
        (ModuleCat.of ℚ ℚ) hn (by omega))]
  simp [Finset.sum_range_succ, h₀, h₂]
  ring

/-- A closed connected homologically oriented surface of finite CW type has Euler characteristic
at most two. -/
theorem eulerChar_le_two : eulerChar M ≤ 2 := by
  rw [o.eulerChar_eq_two_sub_finrank_singularHomology_one hn]
  exact sub_le_self _ (by positivity)

end TauCeti.HomologicalOrientation
