/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Forms

import Mathlib.RingTheory.Ideal.Operations

/-!
# Shallow-variable specialization and ideal-power vanishing for deep forms

For a Frobenius cycle `T` and a split `r`, this file provides the ring homomorphism
`T.specializeShallow r x` that keeps the deep variables and evaluates the shallow variables and
constants through `x`, together with the ideal-power vanishing criterion for deep forms:

* `TauCeti.FrobeniusCycle.specializeShallow`: keeps the variables `v` with `T.IsDeep r v` and
  sends constants and shallow variables to their images under `x`.
* `TauCeti.FrobeniusCycle.specializeShallow_injective`: `T.specializeShallow r x` is injective
  whenever `x` is injective.
* `TauCeti.FrobeniusCycle.specializeShallow_formToMvPolynomial_ne_zero`: for injective `x` and
  nonzero `F`, `T.specializeShallow r x (formToMvPolynomial F) ≠ 0`.
* `TauCeti.FrobeniusCycle.map_formToMvPolynomial_mem_pow_of_mem_deepForms`: if
  `F ∈ T.deepForms k n r τ` and a ring map `ψ` sends the `g⁻¹`-translates of deep variables into
  an ideal `𝔪`, then `ψ (formToMvPolynomial F) ∈ 𝔪 ^ τ`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file
`src/New/UpperBound/ElementaryDivisors/Depth.lean` (`New.FrobeniusCycle.specializeShallow`,
`New.FrobeniusCycle.specializeShallow_injective`,
`New.FrobeniusCycle.specializeShallow_polyOfCoeffs_ne_zero`,
`New.FrobeniusCycle.map_polyOfCoeffs_mem_pow_of_mem_deepForms`).
-/

public section

open MvPolynomial Matrix

namespace TauCeti.FrobeniusCycle

variable {W : Type*} [CommRing W] [IsLocalRing W] {R : Type*} [CommRing R] {N k : ℕ}
  (T : FrobeniusCycle W R N)

/-- For a ring map `x : MvPolynomial (Fin k × ZMod N) R →+* L`, the ring map to
`MvPolynomial (Fin k × ZMod N) L` that keeps the variables deep for `r` and sends constants and
shallow variables to their images under `x`. -/
noncomputable def specializeShallow {L : Type*} [CommRing L] (r : ℕ)
    (x : MvPolynomial (Fin k × ZMod N) R →+* L) :
    MvPolynomial (Fin k × ZMod N) R →+* MvPolynomial (Fin k × ZMod N) L :=
  letI : DecidablePred (T.IsDeep (k := k) r) := Classical.decPred _
  eval₂Hom (C.comp (x.comp C)) fun v : Fin k × ZMod N ↦
    if T.IsDeep r v then X v else C (x (X v))

/-- If `x` is injective, then `T.specializeShallow r x` is injective. -/
theorem specializeShallow_injective {L : Type*} [CommRing L] (r : ℕ)
    {x : MvPolynomial (Fin k × ZMod N) R →+* L} (hx : Function.Injective x) :
    Function.Injective (T.specializeShallow r x) := by
  have h_factor : x = (eval (x ∘ X)).comp (T.specializeShallow r x) := by
    ext <;> simp [specializeShallow, apply_ite]
  rw [h_factor, RingHom.coe_comp] at hx
  exact hx.of_comp

/-- If `x` is injective, `T.specializeShallow r x` maps the polynomial of a nonzero form `F` to a
nonzero polynomial. -/
theorem specializeShallow_formToMvPolynomial_ne_zero {L : Type*} [CommRing L] {n : ℕ} (r : ℕ)
    {x : MvPolynomial (Fin k × ZMod N) R →+* L} (hx : Function.Injective x)
    {F : Exponent N k n → R} (hF_ne : F ≠ 0) :
    T.specializeShallow r x (formToMvPolynomial F) ≠ 0 := by
  obtain ⟨β, hβ⟩ : ∃ β : Exponent N k n, F β ≠ 0 := Function.ne_iff.mp hF_ne
  have h_poly : formToMvPolynomial F ≠ 0 := fun h ↦
    hβ (by simpa [coeff_formToMvPolynomial] using congrArg (·.coeff β.val) h)
  exact fun h ↦ h_poly (T.specializeShallow_injective r hx (by simpa [map_zero] using h))

/-- If `F ∈ T.deepForms k n r τ` and a ring map `ψ` sends the `g⁻¹`-translates of deep variables
into an ideal `𝔪`, then `ψ (formToMvPolynomial F) ∈ 𝔪 ^ τ`. -/
theorem map_formToMvPolynomial_mem_pow_of_mem_deepForms {n r τ : ℕ} {F : Exponent N k n → R}
    (hF : F ∈ T.deepForms k n r τ) {L : Type*} [CommRing L]
    (ψ : MvPolynomial (Fin k × ZMod N) R →+* L) (𝔪 : Ideal L) (g : GL (Fin k) W)
    (h_var : ∀ v : Fin k × ZMod N, T.IsDeep r v → ψ (T.twistedAction g⁻¹ (X v)) ∈ 𝔪) :
    ψ (formToMvPolynomial F) ∈ 𝔪 ^ τ := by
  classical
  have : NeZero N := T.neZero
  let G : Exponent N k n → R := T.letterRep n g *ᵥ F
  have hF_eq : F = T.letterRep n g⁻¹ *ᵥ G := by
    simp [G, Matrix.mulVec_mulVec, ← map_mul]
  have h_form : formToMvPolynomial F = T.twistedAction g⁻¹ (formToMvPolynomial G) := by
    rw [hF_eq, T.twistedAction_formToMvPolynomial]
  rw [h_form, (formToMvPolynomial G).as_sum, map_sum, map_sum]
  refine Ideal.sum_mem _ fun α hα ↦ ?_
  have hα_deg : ∀ s : ZMod N, ∑ b : Fin k, α (b, s) = n := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hα) (coeff_formToMvPolynomial_eq_zero G h)
  let β : Exponent N k n := ⟨α, hα_deg⟩
  have h_deep : τ ≤ T.depth r α := by
    by_contra h_lt
    have hG0 : G β = 0 :=
      Ideal.mem_bot.mp ((mem_deepForms_iff (T := T)).mp hF g β (Nat.lt_of_not_ge h_lt))
    exact (MvPolynomial.mem_support_iff.mp hα) (by rw [coeff_formToMvPolynomial G β, hG0])
  rw [monomial_eq, map_mul, map_mul, Finsupp.prod, map_prod, map_prod]
  refine Ideal.pow_le_pow_right h_deep (Ideal.mul_mem_left _ _ ?_)
  have h_pow : 𝔪 ^ T.depth r α =
      ∏ v ∈ α.support, (if T.IsDeep r v then 𝔪 else ⊤) ^ α v := by
    rw [depth_apply, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    split_ifs <;> simp [← Ideal.one_eq_top]
  rw [h_pow]
  refine Ideal.prod_mem_prod fun v _ ↦ ?_
  rw [map_pow, map_pow]
  split_ifs with hv
  · exact Ideal.pow_mem_pow (h_var v hv) _
  · exact Ideal.pow_mem_pow trivial _

end TauCeti.FrobeniusCycle
