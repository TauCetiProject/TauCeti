/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.LinearAlgebra.Complex.Conjugation

/-!
# Conjugate-reciprocal polynomials

A complex polynomial of degree at most `k` is *conjugate-reciprocal* when its coefficients satisfy
`aᵢ = conj aⱼ` whenever `i + j = k`. These polynomials form a real, not a complex, vector space,
of dimension `k + 1` for `k ≥ -1` and `0` for `k < 0`. Their coefficient vectors are the real
points of the conjugation `a ↦ conj ∘ a ∘ rev` of `Fin (k + 1) → ℂ`, so the dimension count is
`TauCeti.finrank_realPoints`.

## Main definitions

* `TauCeti.conjReciprocalPolynomials k`: the real subspace of complex polynomials `p` with
  `p.coeff n = 0` for `n > k` and `p.coeff i = conj (p.coeff j)` whenever `i + j = k`.

## Main results

* `TauCeti.conjReciprocalPolynomials_eq_bot`: for `k < 0` the only conjugate-reciprocal
  polynomial is zero.
* `TauCeti.finiteDimensional_conjReciprocalPolynomials`: the conjugate-reciprocal polynomials of
  degree at most `k` form a finite-dimensional real vector space.
* `TauCeti.finrank_conjReciprocalPolynomials`: the conjugate-reciprocal polynomials of degree at
  most `k` form a real vector space of dimension `(k + 1).toNat`.
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

end TauCeti
