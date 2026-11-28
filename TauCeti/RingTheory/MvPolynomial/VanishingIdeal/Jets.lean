/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nullstellensatz

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Jet vanishing and Chinese remainder theorem for vanishing ideals

This file proves the jet-vanishing and Chinese remainder theorem ingredients used in the weighted
Combinatorial Nullstellensatz with multiplicity:

* TauCeti.coeff_translate_eq_zero_of_mem_vanishingIdeal_pow: if a multivariate polynomial p
  lies in anishingIdeal K {w} ^ d, then after translating w to the origin its coefficients of
  degree < d vanish.
* TauCeti.aeval_monomial_mem_vanishingIdeal_pow: if polynomials φ u vanish at w, then
  eval φ (monomial γ 1) lies in anishingIdeal K {w} ^ d whenever d ≤ γ.degree.
* TauCeti.exists_forall_coeff_translate_eq: Chinese remainder theorem for jets at finitely many
  distinct points z t.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, commit
72fead102f663d5c7a407964a13dc0cf9d977207), file src/Lib/General/Algebra/MultivariatePolynomials.lean
(New.coeff_translate_eq_zero_of_mem_vanishingIdeal_pow,
New.bind₁_monomial_mem_vanishingIdeal_pow, New.exists_forall_coeff_translate_eq).
-/

public section

open MvPolynomial Ideal Finsupp

namespace TauCeti

/-- If p vanishes to order d at the point w, then after translating w to the origin the
coefficients of p of degree below d are zero. -/
theorem coeff_translate_eq_zero_of_mem_vanishingIdeal_pow {K ι : Type*} [Field K]
    {w : ι → K} {d : ℕ} {p : MvPolynomial ι K} (hp : p ∈ vanishingIdeal K {w} ^ d)
    {γ : ι →₀ ℕ} (hγ : γ.degree < d) :
    (aeval (X + C ∘ w) p).coeff γ = 0 := by
  let T : MvPolynomial ι K →ₐ[K] MvPolynomial ι K := aeval (X + C ∘ w)
  have h_origin : vanishingIdeal K {w} ≤ (idealOfVars ι K).comap T := fun q hq ↦ by
    have h_const : constantCoeff (T q) = 0 := by simpa [T, map_aeval] using hq
    rw [Ideal.mem_comap, ← pow_one (idealOfVars ι K), mem_pow_idealOfVars_iff']
    simpa [degree_eq_zero_iff, ← constantCoeff_eq] using h_const
  have h_mem : T p ∈ idealOfVars ι K ^ d := le_comap_pow T d (pow_right_mono h_origin d hp)
  exact (mem_pow_idealOfVars_iff' d _).mp h_mem γ hγ

/-- If the polynomials φ u vanish at the point w, then eval φ (monomial γ 1) vanishes at w
to every order d ≤ γ.degree. -/
theorem aeval_monomial_mem_vanishingIdeal_pow {K ι : Type*} [Field K] {w : ι → K}
    {φ : ι → MvPolynomial ι K} (hφ : ∀ u : ι, eval w (φ u) = 0) {d : ℕ} {γ : ι →₀ ℕ}
    (hγ : d ≤ γ.degree) :
    aeval (R := K) φ (monomial γ 1) ∈ vanishingIdeal K {w} ^ d := by
  classical
  have h_vars : idealOfVars ι K ≤ (vanishingIdeal K {w}).comap (aeval (R := K) φ) := by
    simp [Ideal.span_le, hφ, Set.range_subset_iff, aeval_X]
  have h_mem : monomial γ 1 ∈ idealOfVars ι K ^ d := (mem_pow_idealOfVars_iff d _).mpr (by simpa)
  exact le_comap_pow _ d (pow_right_mono h_vars d h_mem)

/-- Chinese remainder theorem for jets: at finitely many distinct points z t, the coefficients
of degree below d after translation to the origin can be prescribed arbitrarily. -/
theorem exists_forall_coeff_translate_eq {K ι S : Type*} [Field K] [Finite S]
    {z : S → ι → K} (hz_inj : z.Injective) {d : ℕ} {Γ : Finset (ι →₀ ℕ)}
    (hΓ : ∀ γ ∈ Γ, γ.degree < d) (y : S × Γ → K) :
    ∃ p : MvPolynomial ι K,
      ∀ (t : S) (γ : Γ), (aeval (X + C ∘ z t) p).coeff γ = y (t, γ) := by
  classical
  have := Fintype.ofFinite S
  have h_ideal_inj : Function.Injective fun w : ι → K ↦ vanishingIdeal K {w} := fun w w' h_eq ↦ by
    funext u
    simpa [sub_eq_zero] using h_eq.ge (show X u - C (w' u) ∈ vanishingIdeal K {w'} by simp)
  have h_coprime : Pairwise (Function.onFun IsCoprime fun t : S ↦ vanishingIdeal K {z t} ^ d) :=
    fun t t' h_ne ↦ .pow (isCoprime_of_isMaximal ((h_ideal_inj.comp hz_inj).ne h_ne))
  let q (t : S) : MvPolynomial ι K := aeval (X + C ∘ (-z t)) (∑ γ : Γ, monomial γ (y (t, γ)))
  obtain ⟨p, hp⟩ := exists_forall_sub_mem_ideal h_coprime q
  refine ⟨p, fun t γ ↦ ?_⟩
  have h_jet : (aeval (X + C ∘ z t) (p - q t)).coeff γ = 0 :=
    coeff_translate_eq_zero_of_mem_vanishingIdeal_pow (hp t) (hΓ γ γ.property)
  simpa [q, comp_aeval_apply, coeff_sum, sub_eq_zero, aeval_X, aeval_X_left] using h_jet

end TauCeti
