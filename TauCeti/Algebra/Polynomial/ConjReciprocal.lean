/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.LinearAlgebra.Complex.Conjugation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Conjugate-reciprocal polynomials

A complex polynomial of degree at most `k` is *conjugate-reciprocal* when its coefficients satisfy
`aᵢ = conj aⱼ` whenever `i + j = k`. These polynomials form a real, not a complex, vector space,
of dimension `k + 1` for `k ≥ -1` and `0` for `k < 0`. Their coefficient vectors are the real
points of the conjugation `a ↦ conj ∘ a ∘ rev` of `Fin (k + 1) → ℂ`, so the dimension count is
`TauCeti.finrank_realPoints`.

For odd `k = 2 * m + 1` the coefficients pair off without a middle term, so a conjugate-reciprocal
polynomial is `∑_{j ≤ m} (aⱼ Xʲ + conj aⱼ X^(k-j))`, and its lower coefficients `a₀, …, aₘ`
identify these polynomials with `ℂ^(m+1)`. For even `k` the middle coefficient is real instead.

## Main definitions

* `TauCeti.conjReciprocalPolynomials k`: the real subspace of complex polynomials `p` with
  `p.coeff n = 0` for `n > k` and `p.coeff i = conj (p.coeff j)` whenever `i + j = k`.
* `TauCeti.conjReciprocalLowerCoeffEquiv m`: for `k = 2 * m + 1`, the real-linear isomorphism
  `p ↦ (p.coeff 0, …, p.coeff m)` onto `Fin (m + 1) → ℂ`.

## Main results

* `TauCeti.conjReciprocalPolynomials_eq_bot`: for `k < 0` the only conjugate-reciprocal
  polynomial is zero.
* `TauCeti.finiteDimensional_conjReciprocalPolynomials`: the conjugate-reciprocal polynomials of
  degree at most `k` form a finite-dimensional real vector space.
* `TauCeti.finrank_conjReciprocalPolynomials`: the conjugate-reciprocal polynomials of degree at
  most `k` form a real vector space of dimension `(k + 1).toNat`.
* `TauCeti.eq_sum_of_mem_conjReciprocalPolynomials`: for `k = 2 * m + 1`, the expansion
  `p = ∑_{j ≤ m} (aⱼ Xʲ + conj aⱼ X^(k-j))`.
-/

public section

namespace TauCeti

open Complex Module Polynomial
open scoped ComplexConjugate

/-- The *conjugate-reciprocal* complex polynomials of degree at most `k`: those whose
coefficients vanish above `k` and satisfy `aᵢ = conj aⱼ` whenever `i + j = k`. For `k < 0` only
the zero polynomial qualifies. They form a real, not a complex, vector space. -/
def conjReciprocalPolynomials (k : ℤ) : Submodule ℝ ℂ[X] where
  carrier := {p | (∀ n : ℕ, k < n → p.coeff n = 0) ∧
    ∀ i j : ℕ, (i + j : ℤ) = k → p.coeff i = conj (p.coeff j)}
  add_mem' := by
    rintro p q ⟨hp, hp'⟩ ⟨hq, hq'⟩
    exact ⟨fun n hn => by simp [hp n hn, hq n hn], fun i j h => by simp [hp' i j h, hq' i j h]⟩
  zero_mem' := by simp
  smul_mem' := by
    rintro c p ⟨hp, hp'⟩
    exact ⟨fun n hn => by simp [hp n hn], fun i j h => by simp [hp' i j h, real_smul]⟩

variable {k : ℤ} {p : ℂ[X]}

/-- Membership in `conjReciprocalPolynomials k`, unfolded. -/
@[simp]
theorem mem_conjReciprocalPolynomials_iff :
    p ∈ conjReciprocalPolynomials k ↔ (∀ n : ℕ, k < n → p.coeff n = 0) ∧
      ∀ i j : ℕ, (i + j : ℤ) = k → p.coeff i = conj (p.coeff j) :=
  Iff.rfl

/-- For `k < 0` the only conjugate-reciprocal polynomial of degree at most `k` is zero. -/
theorem conjReciprocalPolynomials_eq_bot (hk : k < 0) : conjReciprocalPolynomials k = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun p hp => ext fun n => by simpa using hp.1 n (by omega)

/-- The conjugation `a ↦ conj ∘ a ∘ rev` of `Fin N → ℂ`, whose real points are the coefficient
vectors of conjugate-reciprocal polynomials of degree less than `N`. -/
private def revConj (N : ℕ) : (Fin N → ℂ) →ₛₗ[starRingEnd ℂ] (Fin N → ℂ) :=
  (starLinearEquiv ℂ).toLinearMap.comp (LinearMap.funLeft ℂ ℂ Fin.rev)

private theorem revConj_apply (N : ℕ) (a : Fin N → ℂ) (j : Fin N) :
    revConj N a j = conj (a (Fin.rev j)) :=
  rfl

private theorem revConj_involutive (N : ℕ) : Function.Involutive (revConj N) := fun a =>
  funext fun j => by rw [revConj_apply, revConj_apply, Fin.rev_rev, conj_conj]

private theorem conjReciprocalPolynomials_eq_map :
    conjReciprocalPolynomials k =
      (realPoints (revConj (k + 1).toNat)).map ((ofFn (k + 1).toNat).restrictScalars ℝ) := by
  ext p
  simp only [mem_conjReciprocalPolynomials_iff, Submodule.mem_map, mem_realPoints,
    LinearMap.restrictScalars_apply, funext_iff, revConj_apply]
  constructor
  · rintro ⟨hp, hp'⟩
    refine ⟨fun j => p.coeff j, fun j => (hp' _ _ ?_).symm, ?_⟩
    · have := j.isLt
      simp only [Fin.val_rev]
      omega
    · ext n
      by_cases hn : n < (k + 1).toNat
      · rw [ofFn_coeff_eq_val_of_lt _ hn]
      · rw [ofFn_coeff_eq_zero_of_ge _ (not_lt.mp hn), hp n (by omega)]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨fun n hn => ofFn_coeff_eq_zero_of_ge _ (by omega), fun i j hij => ?_⟩
    have hi : i < (k + 1).toNat := by omega
    have hj : j < (k + 1).toNat := by omega
    rw [ofFn_coeff_eq_val_of_lt _ hi, ofFn_coeff_eq_val_of_lt _ hj, ← ha ⟨i, hi⟩]
    congr 2
    ext
    simp only [Fin.val_rev]
    omega

/-- The conjugate-reciprocal polynomials of degree at most `k` form a finite-dimensional real
vector space. -/
instance finiteDimensional_conjReciprocalPolynomials (k : ℤ) :
    FiniteDimensional ℝ (conjReciprocalPolynomials k) := by
  rw [conjReciprocalPolynomials_eq_map]
  infer_instance

/-- The conjugate-reciprocal polynomials of degree at most `k` form a real vector space of
dimension `k + 1` when `k ≥ -1`, and `0` when `k < 0`. -/
theorem finrank_conjReciprocalPolynomials (k : ℤ) :
    finrank ℝ (conjReciprocalPolynomials k) = (k + 1).toNat := by
  rw [conjReciprocalPolynomials_eq_map, ← (Submodule.equivMapOfInjective
    ((ofFn (k + 1).toNat).restrictScalars ℝ) (injective_ofFn (R := ℂ) _) _).finrank_eq,
    finrank_realPoints (revConj_involutive _), Module.finrank_fin_fun]

/-! ### Odd degree: the lower half of the coefficients -/

variable {m : ℕ}

/-- A conjugate-reciprocal polynomial of degree at most `2 * m + 1` is determined by its
coefficients `a₀, …, aₘ`: it is `∑_{j ≤ m} (aⱼ Xʲ + conj aⱼ X^(2m+1-j))`. -/
theorem eq_sum_of_mem_conjReciprocalPolynomials (hp : p ∈ conjReciprocalPolynomials (2 * m + 1)) :
    p = ∑ j ∈ Finset.range (m + 1),
      (C (p.coeff j) * X ^ j + C (conj (p.coeff j)) * X ^ (2 * m + 1 - j)) := by
  obtain ⟨hp, hp'⟩ := mem_conjReciprocalPolynomials_iff.mp hp
  ext n
  simp only [finsetSum_coeff, coeff_add, coeff_C_mul_X_pow, Finset.sum_add_distrib]
  -- The terms `j` with `n ≠ j` and `n ≠ 2 * m + 1 - j` vanish.
  have hzero (s : ℕ → ℕ) (f : ℕ → ℂ) (hs : ∀ j < m + 1, n ≠ s j) :
      ∑ j ∈ Finset.range (m + 1), (if n = s j then f j else 0) = 0 :=
    Finset.sum_eq_zero fun j hj => ite_eq_right (hs j (Finset.mem_range.mp hj))
  rcases le_or_gt n m with hn | hn
  · -- Low degree: only the term `aₙ Xⁿ` contributes.
    rw [hzero (2 * m + 1 - ·) _ fun j hj => by omega, add_zero, Finset.sum_ite_eq,
      ite_eq_left (Finset.mem_range.mpr (by omega))]
  rw [hzero (fun j => j) _ fun j hj => by omega, zero_add]
  rcases le_or_gt n (2 * m + 1) with hn' | hn'
  · -- High degree up to `2 * m + 1`: only the term `conj a_{2m+1-n} X^n` contributes.
    rw [Finset.sum_eq_single_of_mem (2 * m + 1 - n) (Finset.mem_range.mpr (by omega))
      fun j _ hjn => ite_eq_right (by omega), ite_eq_left (by omega),
      hp' n (2 * m + 1 - n) (by rw [Nat.cast_sub hn']; push_cast; ring)]
  · rw [hp n (by omega), hzero (2 * m + 1 - ·) _ fun j hj => by omega]

/-- A conjugate-reciprocal polynomial of degree at most `2 * m + 1` whose coefficients of degree
at most `m` vanish is zero. -/
theorem eq_zero_of_mem_conjReciprocalPolynomials_of_forall_coeff_eq_zero
    (hp : p ∈ conjReciprocalPolynomials (2 * m + 1)) (h : ∀ j ≤ m, p.coeff j = 0) : p = 0 := by
  rw [eq_sum_of_mem_conjReciprocalPolynomials hp]
  exact Finset.sum_eq_zero fun j hj => by
    simp [h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]

/-- The coefficients of degree at most `m`, as a real-linear map on the conjugate-reciprocal
polynomials of degree at most `2 * m + 1`. -/
private noncomputable def lowerCoeff (m : ℕ) :
    conjReciprocalPolynomials (2 * m + 1) →ₗ[ℝ] (Fin (m + 1) → ℂ) :=
  ((toFn (m + 1)).restrictScalars ℝ).comp (Submodule.subtype _)

private theorem lowerCoeff_injective (m : ℕ) : Function.Injective (lowerCoeff m) := by
  refine (injective_iff_map_eq_zero _).mpr fun p hp => Subtype.ext ?_
  refine eq_zero_of_mem_conjReciprocalPolynomials_of_forall_coeff_eq_zero p.2 fun j hj => ?_
  exact congrFun hp ⟨j, Nat.lt_succ_of_le hj⟩

/-- **The lower coefficients of an odd-degree conjugate-reciprocal polynomial.** For
`k = 2 * m + 1`, the coefficients `a₀, …, aₘ` identify the real vector space of
conjugate-reciprocal polynomials of degree at most `k` with `ℂ^(m+1)`; the remaining coefficients
are `a_{k-j} = conj aⱼ`. Both spaces have real dimension `2 * m + 2`. -/
noncomputable def conjReciprocalLowerCoeffEquiv (m : ℕ) :
    conjReciprocalPolynomials (2 * m + 1) ≃ₗ[ℝ] (Fin (m + 1) → ℂ) :=
  (lowerCoeff m).linearEquivOfInjective (lowerCoeff_injective m) <| by
    rw [finrank_conjReciprocalPolynomials, Module.finrank_pi_fintype]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    omega

@[simp]
theorem conjReciprocalLowerCoeffEquiv_apply (p : conjReciprocalPolynomials (2 * m + 1))
    (j : Fin (m + 1)) : conjReciprocalLowerCoeffEquiv m p j = (p : ℂ[X]).coeff j :=
  (rfl)

@[simp]
theorem coeff_conjReciprocalLowerCoeffEquiv_symm_apply (a : Fin (m + 1) → ℂ) (j : Fin (m + 1)) :
    ((conjReciprocalLowerCoeffEquiv m).symm a : ℂ[X]).coeff j = a j := by
  rw [← conjReciprocalLowerCoeffEquiv_apply, LinearEquiv.apply_symm_apply]

end TauCeti
