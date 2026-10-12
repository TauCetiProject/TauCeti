/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Lazard.Evaluation

/-!
# Coefficient transport of Lazard evaluation

An injective coefficient map preserves the first nonzero Taylor coefficient, hence both
the removed exponents and Lazard evaluation. In particular, mapping coefficients to constant
univariate polynomials lets a content factor be Lazard-evaluated in the base variables while
the distinguished variable is retained.
-/

public section

namespace MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

/-- An injective coefficient map preserves the exponents removed by Lazard evaluation.
Injectivity prevents a surviving Taylor coefficient from disappearing. -/
theorem lazardExponent_map (φ : R →+* S) (hφ : Function.Injective φ)
    (p : MvPolynomial (Fin n) R) (a : Fin n → R) :
    (map φ p).lazardExponent (φ ∘ a) = p.lazardExponent a := by
  by_cases hp : p = 0
  · simp [hp]
  have hp' : map φ p ≠ 0 := by
    simpa only [map_zero] using (map_injective φ hφ).ne hp
  apply (lazardExponent_eq_iff hp').2
  have ht : taylor (φ ∘ a) (map φ p) = map φ (taylor a p) := (map_taylor p a φ).symm
  rw [ht]
  constructor
  · rw [coeff_map, coeff_taylor_lazardExponent]
    exact fun h ↦ lazardEval_ne_zero hp a (hφ (by simpa using h))
  · intro u hu
    rw [coeff_map, coeff_taylor_eq_zero_of_lt_lazardExponent hu, map_zero]

/-- Lazard evaluation commutes with an injective coefficient map, including for zero inputs. -/
theorem lazardEval_map (φ : R →+* S) (hφ : Function.Injective φ)
    (p : MvPolynomial (Fin n) R) (a : Fin n → R) :
    (map φ p).lazardEval (φ ∘ a) = φ (p.lazardEval a) := by
  have ht : taylor (φ ∘ a) (map φ p) = map φ (taylor a p) := (map_taylor p a φ).symm
  rw [← coeff_taylor_lazardExponent, lazardExponent_map φ hφ, ht, coeff_map,
    coeff_taylor_lazardExponent]

end MvPolynomial
