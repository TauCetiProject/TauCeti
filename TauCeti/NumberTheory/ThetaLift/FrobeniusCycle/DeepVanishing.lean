/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nullstellensatz
public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Forms
import TauCeti.RingTheory.MvPolynomial.Ideal.Pow

/-!
# Vanishing to order on slices of Frobenius-cycle forms

A form whose translates are all deep vanishes with multiplicity wherever a translate of the
linear equations for the deep variables vanishes. One can first substitute for the shallow
variables, for example by making them coefficients of a polynomial in the deep variables alone.
This is the local multiplicity input to the weighted Combinatorial Nullstellensatz argument in
`New.FrobeniusCycle.exists_le_weight_of_mem_deepForms` in
`grh/src/New/UpperBound/ElementaryDivisors/Depth.lean` of [lsernau/grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207
-/

public section

open MvPolynomial Matrix

namespace TauCeti.FrobeniusCycle

variable {W : Type*} [CommRing W] [IsLocalRing W] {R : Type*} [CommRing R] {N k n : ℕ}

/-- If a translate of the deep variables lies in `I` after applying `f`, a depth-`d`
form maps into `I ^ d`. The images of the shallow variables are unrestricted. -/
theorem map_formToMvPolynomial_mem_pow_of_mem_deepForms (T : FrobeniusCycle W R N)
    {A : Type*} [CommSemiring A] [Algebra R A] (f : MvPolynomial (Fin k × ZMod N) R →ₐ[R] A)
    {I : Ideal A} {r d : ℕ} {F : Exponent N k n → R} (hF : F ∈ T.deepForms k n r d)
    (g : GL (Fin k) W) (hI : ∀ x, T.IsDeep r x → f (T.twistedAction g (X x)) ∈ I) :
    f (formToMvPolynomial F) ∈ I ^ d := by
  let φ := fun x ↦ f (T.twistedAction g (X x))
  have hφ : aeval φ = f.comp (T.twistedAction g) := by ext x; simp [φ]
  -- Expand the inverse translate: its deep factors become the equations defining the slice.
  have hdepth (β : Fin k × ZMod N →₀ ℕ)
      (hβ : β ∈ (formToMvPolynomial (T.letterRep n g⁻¹ *ᵥ F)).support) :
      d ≤ Finsupp.weight (fun x ↦ if T.IsDeep r x then 1 else 0) β := by
    have hnz := mem_support_iff.mp hβ
    by_cases h : ∀ s, ∑ b, β (b, s) = n
    · refine le_of_not_gt fun hlt ↦ hnz ((coeff_formToMvPolynomial _ ⟨β, h⟩).trans ?_)
      apply T.mem_deepForms_iff.mp hF g⁻¹ ⟨β, h⟩
      simpa [T.depth_apply, Finsupp.weight_apply, nsmul_eq_mul, mul_ite] using hlt
    · exact (hnz (coeff_formToMvPolynomial_eq_zero _ h)).elim
  have hm := aeval_mem_pow_of_le_weight (T.IsDeep r) hI hdepth
  rwa [hφ, AlgHom.comp_apply, ← T.twistedAction_formToMvPolynomial, ← AlgHom.mul_apply,
    ← map_mul, mul_inv_cancel, map_one, AlgHom.one_apply] at hm

/-- A polynomial substitution of a deep form vanishes to order at least `d` at a point if
there is one group element such that every translated deep variable vanishes there. -/
theorem map_formToMvPolynomial_mem_vanishingIdeal_pow (T : FrobeniusCycle W R N)
    {A σ : Type*} [Field A] [Algebra R A]
    (f : MvPolynomial (Fin k × ZMod N) R →ₐ[R] MvPolynomial σ A) (z : σ → A)
    {r d : ℕ} {F : Exponent N k n → R} (hF : F ∈ T.deepForms k n r d)
    (g : GL (Fin k) W) (hz : ∀ x, T.IsDeep r x → eval z (f (T.twistedAction g (X x))) = 0) :
    f (formToMvPolynomial F) ∈ vanishingIdeal A {z} ^ d :=
  T.map_formToMvPolynomial_mem_pow_of_mem_deepForms f hF g fun x hx ↦
    (mem_vanishingIdeal_singleton_iff z _).2 (by simpa only [aeval_eq_eval] using hz x hx)

end TauCeti.FrobeniusCycle
