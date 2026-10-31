/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Lazard.Evaluation

/-!
# Transport of Lazard evaluation

An injective coefficient map preserves the first nonzero Taylor coefficient, hence both
the removed exponents and Lazard evaluation. In particular, mapping coefficients to constant
univariate polynomials lets a content factor be Lazard-evaluated in the base variables while
the distinguished variable is retained.

A Taylor shift translates the point at which both invariants are computed. Renaming the
variables along a strictly monotone map of indices relabels the removed exponents and keeps the
Lazard evaluation: the variables are eliminated in the same relative order, and the new variables
do not occur.
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
  refine toLex.injective (WithTop.coe_injective ?_)
  rw [← lazardValuation_eq_lazardExponent hp', ← lazardValuation_eq_lazardExponent hp]
  exact lazardValuation_map hφ p a

/-- Lazard evaluation commutes with an injective coefficient map, including for zero inputs. -/
theorem lazardEval_map (φ : R →+* S) (hφ : Function.Injective φ)
    (p : MvPolynomial (Fin n) R) (a : Fin n → R) :
    (map φ p).lazardEval (φ ∘ a) = φ (p.lazardEval a) := by
  have ht : taylor (φ ∘ a) (map φ p) = map φ (taylor a p) := (map_taylor p a φ).symm
  rw [← coeff_taylor_lazardExponent, lazardExponent_map φ hφ, ht, coeff_map,
    coeff_taylor_lazardExponent]

/-- A Taylor shift translates the point at which Lazard evaluation removes its exponents. -/
@[simp]
theorem lazardExponent_taylor (p : MvPolynomial (Fin n) R) (a b : Fin n → R) :
    (taylor a p).lazardExponent b = p.lazardExponent (b + a) := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  refine toLex.injective (WithTop.coe_injective ?_)
  rw [← lazardValuation_eq_lazardExponent (taylor_eq_zero.not.2 hp),
    ← lazardValuation_eq_lazardExponent hp, lazardValuation_taylor]

/-- The Lazard evaluation of a Taylor shift is the Lazard evaluation at the translated point. -/
@[simp]
theorem lazardEval_taylor (p : MvPolynomial (Fin n) R) (a b : Fin n → R) :
    (taylor a p).lazardEval b = p.lazardEval (b + a) := by
  rw [← coeff_taylor_lazardExponent, lazardExponent_taylor, taylor_taylor,
    coeff_taylor_lazardExponent]

/-- Renaming the variables along a strictly monotone map relabels the exponents removed by Lazard
evaluation. -/
theorem lazardExponent_rename {m : ℕ} {f : Fin n → Fin m} (hf : StrictMono f)
    (p : MvPolynomial (Fin n) R) (b : Fin m → R) :
    (rename f p).lazardExponent b = Finsupp.mapDomain f (p.lazardExponent (b ∘ f)) := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  refine toLex.injective (WithTop.coe_injective ?_)
  rw [← lazardValuation_eq_lazardExponent
      ((rename_eq_zero_iff_of_injective p hf.injective).not.2 hp),
    lazardValuation_rename hf, lazardValuation_eq_lazardExponent hp, WithTop.map_coe, ofLex_toLex]

/-- Renaming the variables along a strictly monotone map does not change the Lazard evaluation,
at the pulled back point. -/
theorem lazardEval_rename {m : ℕ} {f : Fin n → Fin m} (hf : StrictMono f)
    (p : MvPolynomial (Fin n) R) (b : Fin m → R) :
    (rename f p).lazardEval b = p.lazardEval (b ∘ f) := by
  rw [← coeff_taylor_lazardExponent, lazardExponent_rename hf, taylor_rename,
    coeff_rename_mapDomain f hf.injective, coeff_taylor_lazardExponent]

end MvPolynomial
