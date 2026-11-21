/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Grossencharacter.FiniteCharacter

import TauCeti.Data.SignType.Basic

/-!
# The explicit formula for the archimedean value of a presentation

Let `χ` be a presentation at a modulus `𝔪` of an algebraic Hecke character of a number field `K`,
with algebraic infinity type `n`. In Neukirch's decomposition `χ((a)) = χ_f(a) χ_∞(a)⁻¹` of a
Größencharakter on principal ideals (VII §6, (6.1)), the idelic archimedean factor `χ_∞`
(`Grossencharacter.archimedeanValue`, defined in
`TauCeti.NumberTheory.LFunctions.Grossencharacter.FiniteCharacter`) equals the product of all
infinite components of `χ.toHeckeCharacter`.

By `HeckeCharacter.coe_prod_infiniteComponent_eq_embeddingCharacter_mul_sign` and
`Grossencharacter.realParity_eq`, on `Kˣ` this product equals the algebraic monomial
`∏_τ τ(x) ^ (n τ)` multiplied by the real sign twist `sgn(τ_w x) ^ (ε_w - n_w)` at each real
place `w ∈ 𝔪.infinitePart`, where `ε_w` is the real parity of `χ.toHeckeCharacter`
(`coe_archimedeanValue_eq`). On elements congruent to `1` modulo `𝔪`, positivity at
`𝔪.infinitePart` kills the sign twists, reducing to the algebraic monomial
(`coe_archimedeanValue_eq_of_isCongrOne`). For the presentation of a ray class character, only
the real sign twists remain (`coe_archimedeanValue_ofRayClassCharacter`).

## Main results

* `TauCeti.LFunctions.Grossencharacter.coe_archimedeanValue_eq`: explicit monomial-times-sign-twist
  formula for `χ.archimedeanValue` on `Kˣ`.
* `TauCeti.LFunctions.Grossencharacter.coe_archimedeanValue_eq_of_isCongrOne`: on elements
  congruent to `1` modulo `𝔪`, `χ.archimedeanValue` equals the algebraic monomial.
* `TauCeti.LFunctions.Grossencharacter.coe_archimedeanValue_ofRayClassCharacter`: explicit sign
  product for the presentation of a ray class character.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
* A. Weil, *Basic Number Theory*, Chapter VII, §3.
-/

public section
noncomputable section

open NumberField
open scoped NumberField

namespace TauCeti.LFunctions.Grossencharacter

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- **Explicit formula for the archimedean value.** On `x : Kˣ`, `χ.archimedeanValue x` equals
the algebraic monomial `∏_τ τ(x) ^ (n τ)` multiplied, at each real place `w ∈ 𝔪.infinitePart`,
by `sgn(τ_w x) ^ (ε_w - n_w)`, where `ε_w` is the real parity of `χ.toHeckeCharacter`. -/
theorem coe_archimedeanValue_eq (χ : Grossencharacter K 𝔪) (x : Kˣ) :
    (χ.archimedeanValue x : ℂ) =
      (∏ τ : K →+* ℂ, τ (x : K) ^ χ.infinityType τ) *
        ∏ w ∈ 𝔪.infinitePart,
          (SignType.sign (InfinitePlace.embedding_of_isReal w.property (x : K)) : ℂ) ^
            (χ.toHeckeCharacter.infinityType.realParity w -
              (χ.infinityType w.val.embedding : ZMod 2)).val := by
  rw [archimedeanValue_apply, Units.coe_prod,
    χ.toHeckeCharacter.coe_prod_infiniteComponent_eq_embeddingCharacter_mul_sign
      χ.infinityType χ.agreesOnIdentityComponent 𝔪.infinitePart
      (fun w hw ↦ not_imp_comm.mp (χ.realParity_eq w) hw) x,
    AlgebraicInfinityType.coe_embeddingCharacter_apply]
  simp [AlgebraicInfinityType.toContinuous_realParity]

/-- On elements congruent to `1` modulo `𝔪`, the archimedean value reduces to the algebraic
monomial because `x` is positive at every real place of `𝔪.infinitePart`. -/
theorem coe_archimedeanValue_eq_of_isCongrOne (χ : Grossencharacter K 𝔪) {x : Kˣ}
    (hx : IsCongrOne 𝔪 x) :
    (χ.archimedeanValue x : ℂ) = ∏ τ : K →+* ℂ, τ (x : K) ^ χ.infinityType τ := by
  rw [χ.archimedeanValue_eq_embeddingCharacter (fun w hw ↦ (isCongrOne_iff.mp hx).2 w hw),
    AlgebraicInfinityType.coe_embeddingCharacter_apply]

/-- For the presentation of a ray class character, the archimedean value is the product of the
real sign characters over `𝔪.infinitePart`. -/
theorem coe_archimedeanValue_ofRayClassCharacter (η : RayClassCharacter 𝔪) (x : Kˣ) :
    ((ofRayClassCharacter η).archimedeanValue x : ℂ) =
      ∏ w ∈ 𝔪.infinitePart,
        (SignType.sign (InfinitePlace.embedding_of_isReal w.property (x : K)) : ℂ) ^
          ((HeckeCharacter.ofRayClassCharacter 𝔪 η).infinityType.realParity w).val := by
  simp [coe_archimedeanValue_eq]

end TauCeti.LFunctions.Grossencharacter
