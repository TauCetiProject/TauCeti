/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Two
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.LocalIndex
-- Proof-only: the point-group index at the symbol `IV*`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Three
-- Proof-only: the point-group index at the symbol `IV`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.ResidueQuadratic
-- Proof-only: every point has nonsingular reduction at the symbol `II*`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.StarredReduction

/-!
# The point-group index reported by Tate's algorithm

Let `v` be a valuation on a field `F`, let `O` be its valuation ring with maximal ideal generated
by `ϖ`, and let `W` be an integral Weierstrass equation over `F`. The points with nonsingular
reduction form the subgroup `E₀(F)` of `W(F)`. When Tate's algorithm stops on the integral model,
its local index is supposed to equal `[W(F) : E₀(F)]`.

This file proves that equality for the six additive symbols outside the family `Iₙ*`. At `II` and
`II*`, every point has nonsingular reduction. At `III` and `III*`, the index is `2`. At `IV` and
`IV*`, both indices are `3` precisely when the relevant residue quadratic has a root and are `1`
otherwise. The comparison in the last two cases uses
`WeierstrassCurve.hasTateYRoot_iff_exists_residue_root` to identify the root test in the definition
of `WeierstrassCurve.tateLocalIndex` with the one used in the point-index theorems.

The remaining additive cases are the symbols `Iₙ*`; they require the corresponding point-group
index calculation for the residue cubic at `I₀*` and the alternating quadratics at `Iₙ*`, `n > 0`.

## Main result

* `WeierstrassCurve.Affine.index_nonsingularReduction_eq_tateLocalIndex_of_ne_I_of_ne_IStar`:
  at every additive symbol outside `Iₙ*`, the point-group index is the local index reported by
  Tate's algorithm.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

open IsLocalRing

namespace WeierstrassCurve

namespace Affine

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [IsIntegral v.valuationSubring W] [DecidableEq F]

/-- **At every additive symbol outside `Iₙ*`, Tate's local index is the point-group index.**
Suppose that `ϖ` generates the maximal ideal of the Henselian valuation ring, its residue field is
perfect, and Tate's algorithm stops on the integral model at a symbol other than `Iₙ` or `Iₙ*`.
Then the reported local index equals `[W(F) : E₀(F)]`.

The perfectness assumption is used at the symbol `III`, to lift the double tangent direction; the
other five symbols are already covered without it by their individual point-index theorems. -/
theorem index_nonsingularReduction_eq_tateLocalIndex_of_ne_I_of_ne_IStar
    [HenselianLocalRing v.valuationSubring] [PerfectField (ResidueField v.valuationSubring)]
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    {s : TauCeti.ReductionSymbol} (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ s)
    (hsI : ∀ n, s ≠ .I n) (hsIStar : ∀ n, s ≠ .IStar n) :
    (W.nonsingularReduction v).index =
      (integralModel v.valuationSubring W).tateLocalIndex ϖ s := by
  classical
  let Wo := integralModel v.valuationSubring W
  rcases s with (_ | n) | _ | _ | _ | (_ | n) | _ | _ | _
  · exact absurd rfl (hsI 0)
  · exact absurd rfl (hsI (n + 1))
  · obtain ⟨-, h₃, h₄, h₆, h₆'⟩ := isTateTerminal_II.1 h
    have hm (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
      rw [hϖ, Ideal.mem_span_singleton]
    have hm₂ (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ^ 2 ↔ ϖ ^ 2 ∣ z := by
      rw [hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rw [nonsingularReduction_eq_top_of_a₆_notMem v ((hm _).2 h₃) ((hm _).2 h₄)
      ((hm _).2 h₆) (fun ha₆ ↦ h₆' ((hm₂ _).1 ha₆)), AddSubgroup.index_top]
    exact tateLocalIndex_II.symm
  · rw [index_nonsingularReduction_eq_two_of_isTateTerminal_III v hϖ h]
    exact tateLocalIndex_III.symm
  · obtain ⟨-, ⟨A₃, h₃⟩, -, ⟨A₆, h₆⟩, -, -⟩ := isTateTerminal_IV.1 h
    have hϖ0 : ϖ ≠ 0 := h.ne_zero (by simp)
    have hroot := hasTateYRoot_iff_exists_residue_root (W := Wo) (m := 1) hϖ hϖ0
      (by simpa [Wo] using h₃) (by simpa [Wo] using h₆)
    by_cases hr : Wo.HasTateYRoot ϖ 1
    · obtain ⟨t, ht⟩ := hroot.mp hr
      rw [index_nonsingularReduction_eq_three_of_isTateTerminal_IV v hϖ h h₃ h₆ ht]
      exact (tateLocalIndex_IV_of_hasTateYRoot hr).symm
    · have hnroot (t : ResidueField v.valuationSubring) :
          t ^ 2 + residue _ A₃ * t - residue _ A₆ ≠ 0 := by
        intro ht
        exact hr (hroot.mpr ⟨t, ht⟩)
      rw [nonsingularReduction_eq_top_of_isTateTerminal_IV v hϖ h h₃ h₆ hnroot,
        AddSubgroup.index_top]
      exact (tateLocalIndex_IV_of_not_hasTateYRoot hr).symm
  · exact absurd rfl (hsIStar 0)
  · exact absurd rfl (hsIStar (n + 1))
  · obtain ⟨-, -, ⟨A₃, h₃⟩, -, ⟨A₆, h₆⟩, -⟩ := isTateTerminal_IVStar.1 h
    have hϖ0 : ϖ ≠ 0 := h.ne_zero (by simp)
    have hroot := hasTateYRoot_iff_exists_residue_root (W := Wo) (m := 2) hϖ hϖ0
      (by simpa [Wo] using h₃) (by norm_num [Wo]; exact h₆)
    by_cases hr : Wo.HasTateYRoot ϖ 2
    · rw [index_nonsingularReduction_eq_three_of_isTateTerminal_IVStar v hϖ h h₃ h₆
        (hroot.mp hr)]
      exact (tateLocalIndex_IVStar_of_hasTateYRoot hr).symm
    · have hnroot (t : ResidueField v.valuationSubring) :
          t ^ 2 + residue _ A₃ * t - residue _ A₆ ≠ 0 := by
        intro ht
        exact hr (hroot.mpr ⟨t, ht⟩)
      rw [nonsingularReduction_eq_top_of_isTateTerminal_IVStar v hϖ h h₃ h₆ hnroot,
        AddSubgroup.index_top]
      exact (tateLocalIndex_IVStar_of_not_hasTateYRoot hr).symm
  · rw [index_nonsingularReduction_eq_two_of_isTateTerminal_IIIStar v hϖ h]
    exact tateLocalIndex_IIIStar.symm
  · rw [nonsingularReduction_eq_top_of_isTateTerminal_IIStar v hϖ h,
      AddSubgroup.index_top]
    exact tateLocalIndex_IIStar.symm

end Affine

end WeierstrassCurve

end
