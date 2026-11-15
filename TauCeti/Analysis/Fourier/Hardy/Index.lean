/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Toeplitz
public import TauCeti.Analysis.Fredholm.Adjoint
public import TauCeti.Analysis.Fredholm.Pow

/-!
# Fredholm indices of Toeplitz operators with monomial symbols

For `m ≥ 0`, the Toeplitz operator `T_{e_m}` of the Fourier monomial `e_m = exp (2πimt)` is
multiplication by `e_m`, an isometry of Hardy space, and it is the `m`th power of the forward shift
`S = T_{e_1}` (`TauCeti.toeplitz_fourierLp_natCast`).

The range of `S` is the orthogonal complement of the constant function `e₀`: a Hardy function `g`
with `ĝ(0) = 0` is `S (e_{-1} g)`. Since `S` is an isometry, it is an injective Fredholm operator
with one-dimensional cokernel, so its index is `-1`. Taking powers, and adjoints through
`T_{e_{-m}} = T_{e_m}†`, the Toeplitz operator of every Fourier monomial is Fredholm with

`index T_{e_k} = -k` for every `k : ℤ`.

These monomials are the models for the index theorem `index T_a = -wind(a, 0)` for continuous
nowhere-vanishing symbols `a`, and they fix its sign: a symbol of winding number `k` is homotopic,
through nowhere-vanishing symbols, to `e_k`.

## Main results

* `TauCeti.range_toeplitz_fourierLp_one`: the range of the forward shift is `(ℂ ∙ e₀)ᗮ`.
* `TauCeti.isFredholm_toeplitz_fourierLp`: `T_{e_k}` is a Fredholm operator for every `k : ℤ`.
* `TauCeti.index_toeplitz_fourierLp`: `index T_{e_k} = -k`.

## References

* J. B. Conway, *A Course in Functional Analysis*, second edition, for the forward shift on
  Hardy space.
* E. Park, *Toeplitz operators*, for the index of Toeplitz operators with continuous symbols.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped ENNReal InnerProductSpace

namespace TauCeti

/-- The range of the forward shift `S = T_{e_1}` is the orthogonal complement of the constant
function `e₀`: the Hardy functions with vanishing zeroth Fourier coefficient. -/
theorem range_toeplitz_fourierLp_one :
    LinearMap.range (toeplitz (fourierLp (T := 1) ∞ 1) : HardySpace →ₗ[ℂ] HardySpace) =
      (ℂ ∙ hardyBasis 0)ᗮ := by
  ext g
  rw [LinearMap.mem_range, Submodule.mem_orthogonal_singleton_iff_inner_right,
    ← HilbertBasis.repr_apply_apply, hardyBasis_repr, Nat.cast_zero]
  constructor
  · rintro ⟨f, rfl⟩
    rw [ContinuousLinearMap.coe_coe, coe_toeplitz_fourierLp_one_apply,
      fourierCoeff_fourierLp_smul]
    exact HardySpace.fourierCoeff_eq_zero f (by norm_num)
  · intro hg
    -- The preimage is `e_{-1} g`, which lies in Hardy space because `ĝ(0) = 0`.
    have hmem : (fourierLp (T := 1) ∞ (-1) • (g : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
        Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) ∈ hardySubmodule := by
      rw [mem_hardySubmodule_iff]
      intro n hn
      rw [fourierCoeff_fourierLp_smul]
      rcases (by omega : n - -1 < 0 ∨ n - -1 = 0) with h | h
      · exact HardySpace.fourierCoeff_eq_zero g h
      · rw [h, hg]
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    rw [ContinuousLinearMap.coe_coe, coe_toeplitz_fourierLp_one_apply,
      fourierLp_smul_fourierLp_smul, add_neg_cancel, fourierLp_zero_smul]

/-- The forward shift `S = T_{e_1}` on Hardy space is a Fredholm operator. -/
private theorem isFredholm_toeplitz_fourierLp_one :
    (toeplitz (fourierLp (T := 1) ∞ 1)).IsFredholm := by
  have hS := isometry_toeplitz_fourierLp_natCast 1
  rw [Nat.cast_one] at hS
  refine hS.isClosedEmbedding.isFredholm ?_
  rw [range_toeplitz_fourierLp_one]
  exact (Submodule.fg_span_singleton _).cofg_of_isCompl
    (Submodule.isCompl_orthogonal _)

/-- The forward shift `S = T_{e_1}` on Hardy space has Fredholm index `-1`: it is injective, and
its range has codimension one. -/
private theorem index_toeplitz_fourierLp_one :
    (toeplitz (fourierLp (T := 1) ∞ 1)).index = -1 := by
  have hS := isometry_toeplitz_fourierLp_natCast 1
  rw [Nat.cast_one] at hS
  rw [ContinuousLinearMap.index_of_injective _ hS.injective,
    range_toeplitz_fourierLp_one,
    (Submodule.quotientEquivOfIsCompl _ _
      (Submodule.isCompl_orthogonal _).symm).finrank_eq,
    finrank_span_singleton (hardyBasis.orthonormal.ne_zero 0)]
  norm_num

/-- The Toeplitz operator of every Fourier monomial `e_k`, `k : ℤ`, is a Fredholm operator. -/
theorem isFredholm_toeplitz_fourierLp (k : ℤ) :
    (toeplitz (fourierLp (T := 1) ∞ k)).IsFredholm := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [toeplitz_fourierLp_natCast]
    exact isFredholm_toeplitz_fourierLp_one.pow m
  · rw [toeplitz_fourierLp_neg, toeplitz_fourierLp_natCast]
    exact (isFredholm_toeplitz_fourierLp_one.pow m).adjoint

/-- **Index of monomial Toeplitz operators.** The Toeplitz operator of the Fourier monomial
`e_k = exp (2πikt)` has Fredholm index `-k`: for `k ≥ 0` it is the `k`th power of the forward
shift, and for `k < 0` it is the adjoint of the `(-k)`th power. -/
@[simp]
theorem index_toeplitz_fourierLp (k : ℤ) :
    (toeplitz (fourierLp (T := 1) ∞ k)).index = -k := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [toeplitz_fourierLp_natCast, ContinuousLinearMap.index_pow _
      isFredholm_toeplitz_fourierLp_one, index_toeplitz_fourierLp_one, mul_neg_one]
  · rw [toeplitz_fourierLp_neg, ContinuousLinearMap.index_adjoint _
      (isFredholm_toeplitz_fourierLp m), toeplitz_fourierLp_natCast,
      ContinuousLinearMap.index_pow _ isFredholm_toeplitz_fourierLp_one,
      index_toeplitz_fourierLp_one, mul_neg_one]

end TauCeti
