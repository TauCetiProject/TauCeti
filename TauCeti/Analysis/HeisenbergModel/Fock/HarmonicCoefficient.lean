/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.Fock.ComplexLinearPart
public import TauCeti.Analysis.HeisenbergModel.Fock.Fischer
import TauCeti.LinearAlgebra.Matrix.Block

/-!
# Matrix coefficients of the Fock model between harmonic polynomial vectors

Let `ω_ε` be the Weil representation of `U(ε)` on the Fock space `𝓕(ε)`, `v_P` the polynomial
vector of a complex polynomial `P`, and `⟨v_Q, ω_ε(u) v_P⟩` a matrix coefficient between
polynomial vectors. Let `d` be a labelling of the coordinates and `u ∈ U(ε)` block diagonal for
it: `u_{ij} = 0` whenever `d_i ≠ d_j`. Call a polynomial *harmonic* if it is killed by the mixed
second derivatives `∂_i ∂_j` with `d_i = d_j` and `ε_i ≠ ε_j`. The coefficients between harmonic
polynomial vectors are inner products after a linear substitution: with
`C(u) = P₊ u P₊ + P₋ conj(u) P₋` (`TauCeti.Fock.complexLinearPart`),
`⟨v_Q, ω_ε(u) v_P⟩ = det(u₋₋)⁻¹ ⟨v_{Q'}, v_P⟩`, where `Q'` is `Q` after the substitution
`X_b ↦ ∑ t, (C(u)⁻¹)_{tb} X_t`. This file proves the identities between coefficients from which
that formula follows by induction on the degree of `Q`.

* *Derivatives on the right.* If `∂_k Q = 0` for the `k` with the label of `i` and the other sign,
  then `⟨v_Q, ω_ε(u) v_{∂_i P}⟩ = ∑ k, conj (C(u)_{ki}) ⟨v_{X_k Q}, ω_ε(u) v_P⟩`.
* *Factors `X_j` on the left.* Inverting these relations, if `∂_i Q = 0` for the `i` with the
  label of `j` and the other sign, then
  `⟨v_{X_j Q}, ω_ε(u) v_P⟩ = ∑ i, conj ((C(u)⁻¹)_{ij}) ⟨v_Q, ω_ε(u) v_{∂_i P}⟩`.
* *The vacuum.* For such `Q`, `v_{X_j Q}` is orthogonal to `ω_ε(u) e` and `ω_ε(u) v_{X_j Q}` is
  orthogonal to `e`; the second fact is the inductive step for the coefficients
  `⟨e, ω_ε(u) v_P⟩`, which are computed at `P = 1` by `TauCeti.Fock.weilRep_vacuum_apply_zero`.

The first identity combines the commutation rules `TauCeti.Fock.innerSL_weilRep_raiseOp` and
`TauCeti.Fock.innerSL_weilRep_lowerOp`: of the terms they produce, those of the sign of `i` are the
terms of the sum, and those of the other sign vanish, by block diagonality of `u` when the labels
differ and by the hypothesis on `Q` when they agree. For the second, `C(u)` is invertible
(`TauCeti.Fock.isUnit_complexLinearPart`) and block diagonal for the pair of a label and a sign,
so its inverse is block diagonal too (`Matrix.inv_apply_eq_zero_of_ne`), and only the rows of the
first identity with the label and sign of `j` enter. The vacuum statements are the case `P = 1`
of the second identity, for `u` and, through the adjointness of `ω_ε(u⁻¹)` and `ω_ε(u)`, for
`u⁻¹`, which is block diagonal as well.

## Main results

* `TauCeti.Fock.innerSL_weilRep_pderiv`: a derivative `∂_i` on the right.
* `TauCeti.Fock.innerSL_X_mul_weilRep`: a factor `X_j` on the left.
* `TauCeti.Fock.innerSL_X_mul_weilRep_vacuum_eq_zero`,
  `TauCeti.Fock.innerSL_vacuum_weilRep_X_mul_eq_zero`: vanishing against the vacuum.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit 72fead1, Apache 2.0,
Copyright 2026 Anthropic, PBC), file `src/Lib/Weil/Fock/OscillatorPair.lean`
(`New.Fock.fockMatrixCoeff_pderiv`, `New.Fock.fockMatrixCoeff_X_mul`, and the inductive step of
`New.Fock.fockMatrixCoeff_one_left`).

## References

* M. Kashiwara, M. Vergne, *On the Segal–Shale–Weil representations and harmonic polynomials*,
  Invent. Math. 44 (1978), 1–48.
* R. Howe, *Transcending classical invariant theory*, J. Amer. Math. Soc. 2 (1989), 535–552.
-/

public noncomputable section

open Matrix MvPolynomial
open scoped ComplexConjugate

namespace TauCeti.Fock

open ReproducingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ} {κ : Type*} {d : ι → κ}
  (u : unitaryGroup ε)

/-- Let `u ∈ U(ε)` be block diagonal for the labels `d`, and let `∂_k Q = 0` for every `k` with
the label of `i` and the sign opposite to that of `i`. Then a derivative `∂_i` on the right of a
matrix coefficient of `ω_ε(u)` becomes a combination of factors `X_k` on the left:
`⟨v_Q, ω_ε(u) v_{∂_i P}⟩ = ∑ k, conj (C(u)_{ki}) ⟨v_{X_k Q}, ω_ε(u) v_P⟩`, where
`C(u) = P₊ u P₊ + P₋ conj(u) P₋` is the complex-linear part. -/
theorem innerSL_weilRep_pderiv
    (hd : ∀ i j, d i ≠ d j → ((u : GL ι ℂ) : Matrix ι ι ℂ) i j = 0)
    (P : MvPolynomial ι ℂ) {Q : MvPolynomial ι ℂ} {i : ι}
    (hQ : ∀ k, d k = d i → ε k ≠ ε i → pderiv k Q = 0) :
    innerSL (polyVector ε Q) (weilRep ε u (polyVector ε (pderiv i P))) =
      ∑ k, conj (complexLinearPart ε ((u : GL ι ℂ) : Matrix ι ι ℂ) k i) *
        innerSL (polyVector ε (X k * Q)) (weilRep ε u (polyVector ε P)) := by
  -- The commutation rules produce terms for every `k`; those of the sign opposite to that of `i`
  -- vanish, by block diagonality of `u` if the labels differ and by `hQ` if they agree.
  have h_other (k : ι) (hk : ε k ≠ ε i) :
      ((u : GL ι ℂ) : Matrix ι ι ℂ) k i = 0 ∨
        innerSL (polyVector ε (pderiv k Q)) (weilRep ε u (polyVector ε P)) = 0 := by
    by_cases h_label : d k = d i
    · simp [hQ k h_label hk]
    · exact .inl (hd k i h_label)
  rcases Int.units_eq_one_or (ε i) with hi | hi
  · -- For `ε i = 1`, `∂_i` is the lowering operator `B_i`, and `C(u)_{ki} = u_{ki}` for `ε k = 1`.
    rw [← lowerOp_apply_of_eq_one hi, innerSL_weilRep_lowerOp, hi]
    simp only [Units.val_one, Int.cast_one, one_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rcases Int.units_eq_one_or (ε k) with hk | hk
    · rw [raiseOp_apply_of_eq_one hk, complexLinearPart_apply_of_pos ε _ hk hi]
    · rw [complexLinearPart_apply_of_ne ε _ (by simp [hi, hk]), raiseOp_apply_of_eq_neg_one hk]
      rcases h_other k (by simp [hi, hk]) with h | h <;> simp [h]
  · -- For `ε i = -1`, `∂_i` is minus the raising operator `A_i`, and `C(u)_{ki} = conj (u_{ki})`
    -- for `ε k = -1`.
    rw [← neg_neg (pderiv i P), ← raiseOp_apply_of_eq_neg_one hi]
    simp only [map_neg]
    rw [innerSL_weilRep_raiseOp, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rcases Int.units_eq_one_or (ε k) with hk | hk
    · rw [complexLinearPart_apply_of_ne ε _ (by simp [hi, hk]), lowerOp_apply_of_eq_one hk]
      rcases h_other k (by simp [hi, hk]) with h | h <;> simp [h]
    · rw [lowerOp_apply_of_eq_neg_one hk, complexLinearPart_apply_of_neg ε _ hk hi,
        Complex.conj_conj, hk]
      push_cast
      ring

/-- Let `u ∈ U(ε)` be block diagonal for the labels `d`, and let `∂_i Q = 0` for every `i` with
the label of `j` and the sign opposite to that of `j`. Then a factor `X_j` on the left of a matrix
coefficient of `ω_ε(u)` becomes a combination of derivatives on the right:
`⟨v_{X_j Q}, ω_ε(u) v_P⟩ = ∑ i, conj ((C(u)⁻¹)_{ij}) ⟨v_Q, ω_ε(u) v_{∂_i P}⟩`, where
`C(u) = P₊ u P₊ + P₋ conj(u) P₋` is the complex-linear part. -/
theorem innerSL_X_mul_weilRep
    (hd : ∀ i j, d i ≠ d j → ((u : GL ι ℂ) : Matrix ι ι ℂ) i j = 0)
    (P : MvPolynomial ι ℂ) {Q : MvPolynomial ι ℂ} {j : ι}
    (hQ : ∀ i, d i = d j → ε i ≠ ε j → pderiv i Q = 0) :
    innerSL (polyVector ε (X j * Q)) (weilRep ε u (polyVector ε P)) =
      ∑ i, conj ((complexLinearPart ε ((u : GL ι ℂ) : Matrix ι ι ℂ))⁻¹ i j) *
        innerSL (polyVector ε Q) (weilRep ε u (polyVector ε (pderiv i P))) := by
  set C := complexLinearPart ε ((u : GL ι ℂ) : Matrix ι ι ℂ)
  let w (k : ι) : ℂ := innerSL (polyVector ε (X k * Q)) (weilRep ε u (polyVector ε P))
  -- `C` is block diagonal for the pair of a label and a sign, hence so is its inverse.
  have hC (k l : ι) (hkl : (d k, ε k) ≠ (d l, ε l)) : C k l = 0 := by
    by_cases h_label : d k = d l
    · exact complexLinearPart_apply_of_ne ε _ fun h_sign ↦ hkl (by rw [h_label, h_sign])
    · simp [C, complexLinearPart_apply, hd k l h_label]
  -- At the indices with the label and sign of `j`, `Cᴴ *ᵥ w` is the coefficient with `∂_i P`.
  have h_row (i : ι) (hi : (d i, ε i) = (d j, ε j)) :
      (Cᴴ *ᵥ w) i = innerSL (polyVector ε Q) (weilRep ε u (polyVector ε (pderiv i P))) := by
    obtain ⟨h_label, h_sign⟩ := Prod.ext_iff.1 hi
    rw [innerSL_weilRep_pderiv u hd P fun k hk_label hk_sign ↦
      hQ k (hk_label.trans h_label) (hk_sign.trans_eq h_sign)]
    simp only [mulVec_apply_eq_sum, conjTranspose_apply, RCLike.star_def, w, C]
  have h_unit : IsUnit Cᴴ.det := by
    rw [det_conjTranspose, isUnit_star, ← isUnit_iff_isUnit_det]
    exact isUnit_complexLinearPart ε u
  -- The entries of `Cᴴ⁻¹ = (C⁻¹)ᴴ` in row `j` are the `conj ((C⁻¹)_{ij})`.
  have h_inv (v : ι → ℂ) : (Cᴴ⁻¹ *ᵥ v) j = ∑ i, conj (C⁻¹ i j) * v i := by
    simp only [mulVec_apply_eq_sum, ← conjTranspose_nonsing_inv, conjTranspose_apply,
      RCLike.star_def]
  calc w j = (Cᴴ⁻¹ *ᵥ Cᴴ *ᵥ w) j := by rw [mulVec_mulVec, nonsing_inv_mul _ h_unit, one_mulVec]
    _ = ∑ i, conj (C⁻¹ i j) * (Cᴴ *ᵥ w) i := h_inv _
    _ = _ := Finset.sum_congr rfl fun i _ ↦ by
      by_cases hi : (d i, ε i) = (d j, ε j)
      · rw [h_row i hi]
      · rw [inv_apply_eq_zero_of_ne hC hi, map_zero, zero_mul, zero_mul]

/-- Let `u ∈ U(ε)` be block diagonal for the labels `d`, and let `∂_i Q = 0` for every `i` with the
label of `j` and the sign opposite to that of `j`. Then `v_{X_j Q}` is orthogonal to the image
`ω_ε(u) e` of the vacuum. -/
theorem innerSL_X_mul_weilRep_vacuum_eq_zero
    (hd : ∀ i j, d i ≠ d j → ((u : GL ι ℂ) : Matrix ι ι ℂ) i j = 0)
    {Q : MvPolynomial ι ℂ} {j : ι} (hQ : ∀ i, d i = d j → ε i ≠ ε j → pderiv i Q = 0) :
    innerSL (polyVector ε (X j * Q)) (weilRep ε u vacuum) = 0 := by
  -- The case `P = 1`: `v_1` is the vacuum, and the derivatives of `1` vanish.
  simpa [polyVector_one] using innerSL_X_mul_weilRep u hd 1 hQ

/-- Let `u ∈ U(ε)` be block diagonal for the labels `d`, and let `∂_i Q = 0` for every `i` with the
label of `j` and the sign opposite to that of `j`. Then `ω_ε(u) v_{X_j Q}` is orthogonal to the
vacuum: `⟨e, ω_ε(u) v_{X_j Q}⟩ = 0`. -/
theorem innerSL_vacuum_weilRep_X_mul_eq_zero
    (hd : ∀ i j, d i ≠ d j → ((u : GL ι ℂ) : Matrix ι ι ℂ) i j = 0)
    {Q : MvPolynomial ι ℂ} {j : ι} (hQ : ∀ i, d i = d j → ε i ≠ ε j → pderiv i Q = 0) :
    innerSL vacuum (weilRep ε u (polyVector ε (X j * Q))) = 0 := by
  -- The inverse matrix of `u` is block diagonal for `d` as well.
  have hd_inv (i k : ι) (hik : d i ≠ d k) : ((u⁻¹ : unitaryGroup ε) : GL ι ℂ) i k = 0 := by
    rw [Subgroup.coe_inv, coe_units_inv]
    exact inv_apply_eq_zero_of_ne hd hik
  rw [← innerSL_weilRep_inv, ← conj_innerSL,
    innerSL_X_mul_weilRep_vacuum_eq_zero u⁻¹ hd_inv hQ, map_zero]

end TauCeti.Fock
