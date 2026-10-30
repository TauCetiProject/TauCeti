/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.SesquilinearForm.Star
public import TauCeti.QuantumGroups.QuantumInteger.Binomial
public import TauCeti.QuantumGroups.UqSl2.LadderModule
public import TauCeti.QuantumGroups.UqSl2.Star

import Mathlib.Tactic

/-!
# The invariant inner product on the ladder modules of `U_q(sl₂)`

For a real parameter `q`, the compact real form of `UqSl2 q` is the star structure with
`K* = K`, `E* = K F` and `F* = E K⁻¹` (`TauCeti.UqSl2.instStarRing`). A sesquilinear form `⟪·,·⟫`
on a `UqSl2 q`-module, conjugate-linear in its first variable, is *invariant* when
`⟪a • x, y⟫ = ⟪x, a* • y⟫` for every `a : UqSl2 q`.

This file constructs such a form on every signed ladder module `L_m^ε`. It is the diagonal form
in the ladder basis `v₀, …, v_m` with

`⟪v_j, v_j⟫ = h_j = [m choose j]_q q^(j (j + 1 - m))`,

the solution of `h₀ = 1` and `h_j / h_(j-1) = [m - j + 1]_q / ([j]_q q^(m - 2j))`. The form is
Hermitian for real `q` and invariant for the compact real form.

For a positive parameter the weights `h_j` are positive, so the form is an inner product, and on
the positive modules `L_m^+` the generator `K` is a positive operator for it. At a generic real
parameter every invariant sesquilinear form on `L_m^ε` is a scalar multiple of this one.

These inner products make the positive ladder modules into unitary representations of the
compact real form. Through the orthonormal bases `v_j / √h_j` they are the input for comparing the
positive ladder modules with the unitary corepresentations of the compact quantum group `SU_q(2)`.

## Main definitions

* `TauCeti.UqSl2.LadderModule.invariantFormWeight q m j`: the weight
  `h_j = [m choose j]_q q^(j (j + 1 - m))`.
* `TauCeti.UqSl2.LadderModule.invariantForm q m ε`: the sesquilinear form on `L_m^ε` that is
  diagonal in the ladder basis with entries `h_j`.

## Main results

* `TauCeti.UqSl2.LadderModule.quantumInteger_mul_zpow_mul_invariantFormWeight_succ`: the
  recurrence `[j + 1]_q q^(m - 2(j + 1)) h_(j+1) = [m - j]_q h_j`.
* `TauCeti.UqSl2.LadderModule.invariantForm_smul_left`: invariance, `⟪a • x, y⟫ = ⟪x, a* • y⟫`.
* `TauCeti.UqSl2.LadderModule.isSymm_invariantForm`: the form is Hermitian for real `q`.
* `TauCeti.UqSl2.LadderModule.isPosSemidef_invariantForm` and `invariantForm_self_pos`: the form
  is positive definite for `0 < q`.
* `TauCeti.UqSl2.LadderModule.invariantForm_smul_k_self_pos`: `K` is a positive operator on
  `L_m^+` for `0 < q`.
* `TauCeti.UqSl2.LadderModule.eq_smul_invariantForm`: at a generic real parameter, every
  invariant sesquilinear form on `L_m^ε` is a scalar multiple of `invariantForm`.

## Implementation notes

The form is defined from its diagonal matrix in the ladder basis by `Matrix.toLinearMapₛₗ₂`, so
that Hermitian symmetry and positivity reduce to the diagonal matrix. Invariance is checked on
generators: under `K` and `K⁻¹` it holds because the form is diagonal and the eigenvalues
`ε q^(±(m - 2j))` are real, under `E` it is the recurrence of the weights, and under
`F = K⁻¹ E*` it follows from the other two because the form is Hermitian.

## References

* A. Klimyk and K. Schmüdgen, *Quantum Groups and Their Representations*, Springer, 1997,
  Chapter 3, for the unitarity of the finite-dimensional representations of the compact real
  form of `U_q(sl₂)`, there stated for a different coproduct convention.
* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Section VI.3, for the
  modules `L_m^ε`.
-/

public noncomputable section

open Module LinearMap Matrix
open scoped ComplexOrder

namespace TauCeti.UqSl2.LadderModule

/-! ### The weights -/

section Weight

variable (q : ℂ) (m : ℕ)

/-- The weight `h_j = [m choose j]_q q^(j (j + 1 - m))` of the ladder vector `v_j` of `L_m^ε`
under the invariant form: `⟪v_j, v_j⟫ = h_j`. It vanishes for `j > m`. -/
def invariantFormWeight (j : ℕ) : ℂ :=
  quantumBinomial q m j * q ^ ((j : ℤ) * (j + 1 - m))

/-- The weight of the highest vector is `h₀ = 1`. -/
@[simp]
theorem invariantFormWeight_zero : invariantFormWeight q m 0 = 1 := by
  simp [invariantFormWeight]

variable {q m}

/-- The weights vanish above the top index `m`. -/
@[simp]
theorem invariantFormWeight_eq_zero_of_lt {j : ℕ} (hj : m < j) : invariantFormWeight q m j = 0 := by
  simp [invariantFormWeight, quantumBinomial_eq_zero_of_lt q hj]

/-- The weights are real for a real parameter. -/
theorem star_invariantFormWeight (hq : IsSelfAdjoint q) (j : ℕ) :
    star (invariantFormWeight q m j) = invariantFormWeight q m j := by
  have h := map_quantumBinomial (starRingEnd ℂ) q m j
  simp only [starRingEnd_apply, hq.star_eq] at h
  simp [invariantFormWeight, h, star_zpow₀, hq.star_eq]

/-- The weights `h_0, …, h_m` are positive for a positive parameter. -/
theorem invariantFormWeight_pos (hq : 0 < q) {j : ℕ} (hj : j ≤ m) :
    0 < invariantFormWeight q m j :=
  mul_pos (quantumBinomial_pos hq hj) (zpow_pos hq _)

variable (q m) in
/-- The recurrence of the weights: `[j + 1]_q q^(m - 2(j + 1)) h_(j+1) = [m - j]_q h_j`. With
`h₀ = 1` it determines the weights whenever the quantum integers `[1]_q, …, [m]_q` are
nonzero. -/
theorem quantumInteger_mul_zpow_mul_invariantFormWeight_succ (j : ℕ) :
    quantumInteger q (j + 1) * q ^ ((m : ℤ) - 2 * (j + 1)) * invariantFormWeight q m (j + 1) =
      quantumInteger q (m - j) * invariantFormWeight q m j := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [quantumInteger_def]
  have habs := quantumBinomial_succ_right_eq q m j
  have hexp : (m : ℤ) - 2 * (j + 1) + (j + 1) * (j + 1 + 1 - m) = j * (j + 1 - m) := by ring
  simp only [invariantFormWeight, Nat.cast_add_one]
  rw [← hexp, zpow_add₀ hq]
  linear_combination (q ^ ((m : ℤ) - 2 * (j + 1)) * q ^ (((j : ℤ) + 1) * (j + 1 + 1 - m))) * habs

end Weight

/-! ### The form -/

variable (q : ℂ) (m : ℕ) (ε : ℤˣ)

/-- The invariant sesquilinear form on the ladder module `L_m^ε`, conjugate-linear in its first
variable: the form that is diagonal in the ladder basis with `⟪v_j, v_j⟫ = h_j`, the weight
`invariantFormWeight q m j`. It is invariant for the compact real form when `q` is real
(`invariantForm_smul_left`), and positive definite when `q` is positive. -/
def invariantForm : LadderModule q m ε →ₗ⋆[ℂ] LadderModule q m ε →ₗ[ℂ] ℂ :=
  Matrix.toLinearMapₛₗ₂ (starRingEnd ℂ) (basis q m ε) (basis q m ε)
    (diagonal fun i : Fin (m + 1) => invariantFormWeight q m i)

/-- The matrix of the invariant form in the ladder basis is the diagonal matrix of the weights. -/
theorem toMatrix₂_invariantForm :
    toMatrix₂ (basis q m ε) (basis q m ε) (invariantForm q m ε) =
      diagonal fun i : Fin (m + 1) => invariantFormWeight q m i := by
  rw [invariantForm, toMatrix₂_toLinearMapₛₗ₂]

variable {q m ε}

/-- The values of the invariant form on the ladder basis. -/
@[simp]
theorem invariantForm_basis_basis (i j : Fin (m + 1)) :
    invariantForm q m ε (basis q m ε i) (basis q m ε j) =
      if i = j then invariantFormWeight q m i else 0 := by
  rw [invariantForm, toLinearMapₛₗ₂_apply_basis, diagonal_apply]

/-- The values of the invariant form on the integer-indexed ladder vectors: `⟪v_i, v_j⟫` is the
weight `h_i` when `i = j` is a valid index and zero otherwise. -/
theorem invariantForm_vec_vec (i j : ℤ) :
    invariantForm q m ε (vec q m ε i) (vec q m ε j) =
      if i = j ∧ 0 ≤ i then invariantFormWeight q m i.toNat else 0 := by
  by_cases hi : 0 ≤ i ∧ i ≤ m
  · by_cases hj : 0 ≤ j ∧ j ≤ m
    · obtain ⟨a, rfl⟩ : ∃ a : Fin (m + 1), (a : ℤ) = i := ⟨⟨i.toNat, by omega⟩, by simp; omega⟩
      obtain ⟨b, rfl⟩ : ∃ b : Fin (m + 1), (b : ℤ) = j := ⟨⟨j.toNat, by omega⟩, by simp; omega⟩
      rw [vec_coe, vec_coe, invariantForm_basis_basis]
      simp [Fin.ext_iff]
    · rw [vec_eq_zero_iff.mpr (show j < 0 ∨ (m : ℤ) < j by omega), map_zero,
        ite_eq_right (by omega)]
  · rw [vec_eq_zero_iff.mpr (show i < 0 ∨ (m : ℤ) < i by omega), map_zero, LinearMap.zero_apply]
    split_ifs with h
    · rw [invariantFormWeight_eq_zero_of_lt (by omega)]
    · rfl

/-- The invariant form is Hermitian for a real parameter: `conj ⟪x, y⟫ = ⟪y, x⟫`. -/
theorem isSymm_invariantForm (hq : IsSelfAdjoint q) : (invariantForm q m ε).IsSymm := by
  rw [isSymm_iff_isHermitian_toMatrix (basis q m ε), toMatrix₂_invariantForm,
    isHermitian_diagonal_iff]
  exact fun i => star_invariantFormWeight hq i

/-- The invariant form is positive semidefinite for a positive parameter. -/
theorem isPosSemidef_invariantForm (hq : 0 < q) : (invariantForm q m ε).IsPosSemidef := by
  rw [isPosSemidef_iff_posSemidef_toMatrix (basis q m ε), toMatrix₂_invariantForm,
    posSemidef_diagonal_iff]
  exact fun i => (invariantFormWeight_pos hq (Nat.lt_succ_iff.mp i.isLt)).le

/-- The invariant form is positive definite for a positive parameter: `0 < ⟪x, x⟫` for `x ≠ 0`.
Thus it is an inner product on `L_m^ε`. -/
theorem invariantForm_self_pos (hq : 0 < q) {x : LadderModule q m ε} (hx : x ≠ 0) :
    0 < invariantForm q m ε x x := by
  have hpos : (diagonal fun i : Fin (m + 1) => invariantFormWeight q m i).PosDef :=
    posDef_diagonal_iff.mpr fun i => invariantFormWeight_pos hq (Nat.lt_succ_iff.mp i.isLt)
  rw [apply_eq_star_dotProduct_toMatrix₂_mulVec (basis q m ε), toMatrix₂_invariantForm]
  refine hpos.dotProduct_mulVec_pos fun h => hx ?_
  exact (basis q m ε).repr.injective (by rw [map_zero]; exact Finsupp.coe_eq_zero.mp h)

/-! ### Invariance -/

section Invariance

variable [Fact (IsSelfAdjoint q)]

/-- A real parameter is fixed by the star. -/
private theorem star_q : star q = q := (Fact.out : IsSelfAdjoint q).star_eq

/-- The quantum integers of a real parameter are real. -/
private theorem star_quantumInteger (r : ℤ) : star (quantumInteger q r) = quantumInteger q r := by
  rw [← starRingEnd_apply, map_quantumInteger, starRingEnd_apply, star_q]

/-- The signs `ε` are real. -/
private theorem star_units (u : ℤˣ) : star (u : ℂ) = u := by
  simp

variable [Fact (q ≠ 0)]

/-- Invariance of the form under `a` reduces to the ladder basis. -/
private theorem smul_left_of_basis {a : UqSl2 q}
    (h : ∀ i j : Fin (m + 1), invariantForm q m ε (a • vec q m ε i) (vec q m ε j) =
      invariantForm q m ε (vec q m ε i) (star a • vec q m ε j))
    (x y : LadderModule q m ε) :
    invariantForm q m ε (a • x) y = invariantForm q m ε x (star a • y) := by
  have hext : (invariantForm q m ε).comp (rep q m ε a) =
      (invariantForm q m ε).compl₂ (rep q m ε (star a)) :=
    ext_basis (basis q m ε) (basis q m ε) fun i j => by
      simpa only [LinearMap.comp_apply, compl₂_apply, smul_def, vec_coe] using h i j
  simpa only [LinearMap.comp_apply, compl₂_apply, smul_def] using congr($hext x y)

/-- A self-adjoint element acting diagonally on the ladder vectors with real eigenvalues
satisfies the invariance condition, since the form is diagonal. -/
private theorem smul_left_of_smul_vec {a : UqSl2 q} (ha : star a = a) {c : ℤ → ℂ}
    (hc : ∀ j, star (c j) = c j) (hac : ∀ j, a • vec q m ε j = c j • vec q m ε j)
    (x y : LadderModule q m ε) :
    invariantForm q m ε (a • x) y = invariantForm q m ε x (star a • y) := by
  refine smul_left_of_basis (fun i j => ?_) x y
  rw [ha, hac, hac, map_smulₛₗ₂, map_smul, invariantForm_vec_vec, smul_eq_mul, smul_eq_mul,
    starRingEnd_apply, hc]
  split_ifs with hij
  · rw [hij.1]
  · simp

/-- The invariance condition is closed under the star: by the Hermitian symmetry of the form,
invariance under `a` gives invariance under `a*`. -/
private theorem smul_left_star {a : UqSl2 q}
    (h : ∀ x y : LadderModule q m ε,
      invariantForm q m ε (a • x) y = invariantForm q m ε x (star a • y))
    (x y : LadderModule q m ε) :
    invariantForm q m ε (star a • x) y = invariantForm q m ε x (star (star a) • y) := by
  have hs := (isSymm_invariantForm (m := m) (ε := ε) (Fact.out : IsSelfAdjoint q)).eq
  rw [← hs, ← h y x, star_star, hs]

/-- The invariant form is invariant for the compact real form of `UqSl2 q`:
`⟪a • x, y⟫ = ⟪x, a* • y⟫` for every `a : UqSl2 q`. -/
theorem invariantForm_smul_left (a : UqSl2 q) (x y : LadderModule q m ε) :
    invariantForm q m ε (a • x) y = invariantForm q m ε x (star a • y) := by
  induction a using UqSl2.induction generalizing x y with
  | algebraMap c =>
    rw [algebraMap_smul, ← algebraMap_star_comm, algebraMap_smul, map_smulₛₗ₂, map_smul,
      starRingEnd_apply]
  | add a b ha hb => rw [add_smul, map_add₂, ha, hb, star_add, add_smul, map_add]
  | mul a b ha hb => rw [mul_smul, ha, hb, star_mul, mul_smul]
  | generator g =>
    have hK := smul_left_of_smul_vec (star_k q)
      (fun j => by rw [star_mul', star_units, star_zpow₀, star_q]) (k_smul_vec (m := m) (ε := ε))
    have hKInv := smul_left_of_smul_vec (star_kInv q)
      (fun j => by rw [star_mul', star_units, star_zpow₀, star_q])
      (kInv_smul_vec (m := m) (ε := ε))
    have hE : ∀ x y : LadderModule q m ε,
        invariantForm q m ε (e q • x) y = invariantForm q m ε x (star (e q) • y) := by
      refine smul_left_of_basis fun i j => ?_
      rw [star_e, mul_smul, f_smul_vec, smul_comm, k_smul_vec, e_smul_vec, map_smulₛₗ₂,
        map_smul, map_smul, invariantForm_vec_vec, invariantForm_vec_vec, starRingEnd_apply,
        star_mul', star_units, star_quantumInteger]
      simp only [smul_eq_mul]
      by_cases hij : (i : ℕ) = (j : ℕ) + 1
      · have hw := quantumInteger_mul_zpow_mul_invariantFormWeight_succ q m j
        rw [ite_eq_left (by omega), ite_eq_left (by omega), show ((i : ℤ) - 1).toNat = j by omega,
          show (i : ℤ).toNat = j + 1 by omega, show (m : ℤ) - i + 1 = m - j by omega,
          show (m : ℤ) - 2 * (j + 1) = m - 2 * ((j : ℤ) + 1) by ring]
        linear_combination -(ε : ℂ) * hw
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        simp
    -- `F = K⁻¹ E*`, and invariance passes to stars and products.
    have hF : ∀ x y : LadderModule q m ε,
        invariantForm q m ε (f q • x) y = invariantForm q m ε x (star (f q) • y) := by
      intro x y
      have hf : f q = kInv q * star (e q) := by rw [star_e, kInv_mul_k_mul]
      rw [hf, mul_smul, hKInv, smul_left_star hE, star_mul, mul_smul]
    cases g
    · exact hE x y
    · exact hF x y
    · exact hK x y
    · exact hKInv x y

/-- Invariance of the form, moving the action to the first variable:
`⟪x, a • y⟫ = ⟪a* • x, y⟫`. -/
theorem invariantForm_smul_right (a : UqSl2 q) (x y : LadderModule q m ε) :
    invariantForm q m ε x (a • y) = invariantForm q m ε (star a • x) y := by
  rw [invariantForm_smul_left, star_star]

end Invariance

/-! ### Positivity of `K` -/

/-- On the positive ladder module `L_m^+`, the generator `K` is a positive operator for the
invariant inner product when `0 < q`: `0 < ⟪x, K • x⟫` for `x ≠ 0`. -/
theorem invariantForm_smul_k_self_pos [Fact (q ≠ 0)] (hq : 0 < q) {x : LadderModule q m 1}
    (hx : x ≠ 0) : 0 < invariantForm q m 1 x (k q • x) := by
  set B := (invariantForm q m 1).compl₂ (rep q m 1 (k q))
  have hB : toMatrix₂ (basis q m 1) (basis q m 1) B =
      diagonal fun i : Fin (m + 1) => q ^ ((m : ℤ) - 2 * (i : ℕ)) * invariantFormWeight q m i := by
    ext i j
    rw [toMatrix₂_apply, compl₂_apply, ← smul_def, ← vec_coe, ← vec_coe, k_smul_vec, map_smul,
      invariantForm_vec_vec, diagonal_apply]
    simp only [Units.val_one, Int.cast_one, one_mul, smul_eq_mul, Fin.ext_iff, Nat.cast_inj,
      and_true, Nat.cast_nonneg, Int.toNat_natCast]
    split_ifs with hij
    · rw [hij]
    · rw [mul_zero]
  have hpos : (diagonal fun i : Fin (m + 1) =>
      q ^ ((m : ℤ) - 2 * (i : ℕ)) * invariantFormWeight q m i).PosDef :=
    posDef_diagonal_iff.mpr fun i =>
      mul_pos (zpow_pos hq _) (invariantFormWeight_pos hq (Nat.lt_succ_iff.mp i.isLt))
  have key : B x x = invariantForm q m 1 x (k q • x) := by rw [compl₂_apply, smul_def]
  rw [← key, apply_eq_star_dotProduct_toMatrix₂_mulVec (basis q m 1), hB]
  refine hpos.dotProduct_mulVec_pos fun h => hx ?_
  exact (basis q m 1).repr.injective (by rw [map_zero]; exact Finsupp.coe_eq_zero.mp h)

/-! ### Uniqueness -/

section Uniqueness

/-- A sequence obeying the recurrence of the weights is a multiple of the weights, provided the
leading coefficients `[j + 1]_q q^(m - 2(j + 1))` are nonzero. -/
private theorem eq_mul_invariantFormWeight (hq : IsGenericQuantumParameter q) {d : ℕ → ℂ}
    (hd : ∀ j : ℕ, quantumInteger q (j + 1) * q ^ ((m : ℤ) - 2 * (j + 1)) * d (j + 1) =
      quantumInteger q (m - j) * d j) (j : ℕ) :
    d j = d 0 * invariantFormWeight q m j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hne : quantumInteger q (j + 1) * q ^ ((m : ℤ) - 2 * (j + 1)) ≠ 0 :=
      mul_ne_zero (quantumInteger_ne_zero hq (by omega)) (zpow_ne_zero _ hq.ne_zero)
    have hw := quantumInteger_mul_zpow_mul_invariantFormWeight_succ q m j
    refine mul_left_cancel₀ hne ?_
    linear_combination hd j + quantumInteger q (m - j) * ih - d 0 * hw

variable [Fact (IsSelfAdjoint q)] [Fact (q ≠ 0)]

/-- At a generic real parameter the invariant form is unique up to a scalar: every sesquilinear
form on `L_m^ε` that is invariant for the compact real form is the multiple
`⟪v₀, v₀⟫' • invariantForm q m ε`. Invariance under `K` and `E` already forces this. -/
theorem eq_smul_invariantForm (hq : IsGenericQuantumParameter q)
    (B : LadderModule q m ε →ₗ⋆[ℂ] LadderModule q m ε →ₗ[ℂ] ℂ)
    (hB : ∀ (a : UqSl2 q) (x y : LadderModule q m ε), B (a • x) y = B x (star a • y)) :
    B = B (vec q m ε 0) (vec q m ε 0) • invariantForm q m ε := by
  -- Invariance under `K` makes `B` diagonal in the ladder basis.
  have hdiag : ∀ i j : ℤ, i ≠ j → B (vec q m ε i) (vec q m ε j) = 0 := by
    intro i j hij
    have h := hB (k q) (vec q m ε i) (vec q m ε j)
    rw [star_k, k_smul_vec, k_smul_vec, map_smulₛₗ₂, map_smul, starRingEnd_apply,
      star_mul', star_units, star_zpow₀, star_q, smul_eq_mul, smul_eq_mul] at h
    have hε : (ε : ℂ) ≠ 0 := by simp
    by_contra hne
    have h' : (ε * B (vec q m ε i) (vec q m ε j)) *
        (q ^ ((m : ℤ) - 2 * i) - q ^ ((m : ℤ) - 2 * j)) = 0 := by
      linear_combination h
    have hpow := sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left (mul_ne_zero hε hne))
    exact hij (by have := hq.zpow_injective hpow; omega)
  -- Invariance under `E` makes the diagonal entries obey the recurrence of the weights.
  set d : ℕ → ℂ := fun j => B (vec q m ε j) (vec q m ε j) with hd_def
  have hrec : ∀ j : ℕ, quantumInteger q (j + 1) * q ^ ((m : ℤ) - 2 * (j + 1)) * d (j + 1) =
      quantumInteger q (m - j) * d j := by
    intro j
    have h := hB (e q) (vec q m ε (j + 1)) (vec q m ε j)
    rw [star_e, mul_smul, f_smul_vec, smul_comm, k_smul_vec, e_smul_vec, map_smulₛₗ₂,
      map_smul, map_smul, starRingEnd_apply, star_mul', star_units,
      star_quantumInteger, smul_eq_mul, smul_eq_mul, smul_eq_mul, add_sub_cancel_right,
      show (m : ℤ) - (j + 1) + 1 = m - j by ring] at h
    have hε : (ε : ℂ) ≠ 0 := by simp
    simp only [hd_def, Nat.cast_add_one]
    refine mul_left_cancel₀ hε ?_
    linear_combination -h
  have hd := eq_mul_invariantFormWeight hq hrec
  refine ext_basis (basis q m ε) (basis q m ε) fun i j => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, invariantForm_basis_basis, ← vec_coe, ← vec_coe,
    smul_eq_mul]
  split_ifs with hij
  · subst hij
    have := hd i
    simp only [hd_def, Nat.cast_zero] at this
    exact this
  · rw [hdiag _ _ (by simpa [Fin.ext_iff] using hij), mul_zero]

end Uniqueness

end TauCeti.UqSl2.LadderModule
