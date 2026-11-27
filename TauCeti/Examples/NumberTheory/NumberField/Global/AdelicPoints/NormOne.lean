/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Derived
public import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.NormOne

/-!
# Examples of the norm-one subgroup of adelic points

Two examples of the norm-one subgroup `G(𝔸_K)^1` (`TauCeti.AdelicPoints.normOne`).

* The special linear group `SL_n` has no nontrivial rational character, so its norm-one subgroup
  is all of `SL_n(𝔸_K)`.
* The norm-one subgroup is not cut out by a condition on archimedean components. For the
  multiplicative group over `ℚ`, the principal idele `2` has norm one, by the product formula,
  while its archimedean component has absolute value `2`: the factor `2` at the real place is
  compensated by the factor `1/2` at the place `2`. So `G(𝔸_ℚ)^1` is not the product of the
  norm-one archimedean points `G(ℝ)^1` with the finite adelic points.

## Main declarations

* `TauCeti.AdelicNormOne.normOne_specialLinear`: `SL_n(𝔸_K)^1 = SL_n(𝔸_K)`.
* `TauCeti.AdelicNormOne.diagonal_two_mem_normOne`,
  `TauCeti.AdelicNormOne.norm_diagonal_two_infinite`: the principal idele `2` of `ℚ` has norm one
  and archimedean absolute value `2`.

## References

* J. Arthur, *An introduction to the trace formula*, Clay Math. Proc. 4 (2005), §3, p. 16.
-/

public section

open NumberField
open scoped LaurentPolynomial

namespace TauCeti.AdelicNormOne

open AdelicPoints

/-- **`SL_n` has no rational characters,** so its norm-one adelic subgroup is everything. -/
theorem normOne_specialLinear (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    normOne K (SpecialLinear.coordinateHopfAlgebra K n) = ⊤ :=
  have : Subsingleton (GroupLike K (SpecialLinear.coordinateHopfAlgebra K n)) :=
    ⟨fun χ ψ ↦ (SpecialLinear.groupLike_eq_one K n χ).trans
      (SpecialLinear.groupLike_eq_one K n ψ).symm⟩
  normOne_eq_top _ _

/-- The principal idele `2` of `ℚ`, the image of the rational point `2` of `𝔾ₘ`, lies in the
norm-one subgroup of `𝔾ₘ(𝔸_ℚ)`. -/
theorem diagonal_two_mem_normOne :
    diagonal (𝓞 ℚ) ℚ ℚ[T;T⁻¹] (MultiplicativeGroup.pointsMulEquiv.symm (Units.mk0 2 two_ne_zero)) ∈
      normOne ℚ ℚ[T;T⁻¹] :=
  diagonal_mem_normOne _

/-- The principal idele `2` of `ℚ` has archimedean component of absolute value `2`, although it
has idele norm one. -/
theorem norm_diagonal_two_infinite (w : InfinitePlace ℚ) :
    ‖(diagonal (𝓞 ℚ) ℚ ℚ[T;T⁻¹]
      (MultiplicativeGroup.pointsMulEquiv.symm (Units.mk0 2 two_ne_zero))).ofConv
      (LaurentPolynomial.T 1) |>.1 w‖ = 2 := by
  -- The archimedean component of the diagonal `2` is `2 ∈ ℚ_w`, of absolute value `w 2`.
  simp only [diagonal_apply_apply, MultiplicativeGroup.pointsMulEquiv_symm_apply,
    laurentEval_T_one, Units.val_mk0, AdeleRing.algebraMap_fst_apply,
    AbsoluteValue.Completion.norm_coe]
  exact w.map_natCast 2

end TauCeti.AdelicNormOne
