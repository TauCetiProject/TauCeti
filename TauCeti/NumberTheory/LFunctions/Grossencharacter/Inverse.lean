/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Basic
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Inverse presentations of algebraic Hecke characters

The functional equation of a Hecke L-function pairs a character with its inverse. For a
presentation `χ = χ_u N^σ`, the inverse has unitary weight `conj χ_u`, infinity type `-n`, and
ideal-side shift `-σ`. In particular, conjugating only the unitary weight would not invert a
nonunitary character.

`Grossencharacter.inverse` constructs this presentation at the same modulus, using inversion
of the underlying Hecke character. It is involutive and commutes with the presentation of a
ray class character. The characteristic projection lemmas allow the inverse presentation to be
used without unfolding its construction.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
-/

public section
noncomputable section

open NumberField
open scoped NumberField

namespace TauCeti.LFunctions.Grossencharacter

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- The inverse presentation at the same modulus: inverse Hecke character, conjugate unitary
weight, and negated algebraic infinity type. Its ideal-side shift is the negative of the
original shift (`idealShift_inverse`). -/
def inverse (χ : Grossencharacter K 𝔪) : Grossencharacter K 𝔪 where
  toHeckeCharacter := χ.toHeckeCharacter⁻¹
  unitaryWeight := χ.unitaryWeight.conj
  infinityType := -χ.infinityType
  eq_one_of_mem y hy hw := by
    rw [← zpow_neg_one, ContinuousMonoidHom.zpow_apply, χ.eq_one_of_mem y hy hw, one_zpow]
  agreesOnIdentityComponent := by
    obtain ⟨hr, hc, hk⟩ := (ContinuousInfinityType.agreesOnIdentityComponent_iff _ _).mp
      χ.agreesOnIdentityComponent
    simp only [HeckeCharacter.infinityType_inv, map_neg,
      ContinuousInfinityType.agreesOnIdentityComponent_iff,
      ContinuousInfinityType.neg_realExponent, ContinuousInfinityType.neg_complexExponent,
      ContinuousInfinityType.neg_complexAngularFrequency]
    exact ⟨congrArg Neg.neg hr, congrArg Neg.neg hc, congrArg Neg.neg hk⟩
  realParity_eq w hw := by
    simp [χ.realParity_eq w hw]
  unitaryWeight_eq_zero I hI := by
    simp [χ.unitaryWeight_eq_zero I hI]
  unitaryWeight_apply v hv u hu := by
    rw [UnitaryIdealWeight.val_conj, MultiplicativeIdealWeight.conj_apply,
      χ.unitaryWeight_apply v hv u hu, HeckeCharacter.unitaryPart_inv,
      HeckeCharacter.finiteComponent_inv, ← zpow_neg_one,
      ContinuousMonoidHom.zpow_apply, zpow_neg_one, Units.val_inv_eq_inv_val,
      HeckeCharacter.finiteComponent_apply]
    exact (Complex.inv_eq_conj (χ.toHeckeCharacter.norm_unitaryPart
      (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u))).symm

/-- The inverse presentation presents the inverse Hecke character. -/
@[simp]
theorem toHeckeCharacter_inverse (χ : Grossencharacter K 𝔪) :
    χ.inverse.toHeckeCharacter = χ.toHeckeCharacter⁻¹ := (rfl)

/-- Inversion conjugates the unitary ideal weight. -/
@[simp]
theorem unitaryWeight_inverse (χ : Grossencharacter K 𝔪) :
    χ.inverse.unitaryWeight = χ.unitaryWeight.conj := (rfl)

/-- Inversion negates the algebraic infinity type, including both embeddings at a complex
place. -/
@[simp]
theorem infinityType_inverse (χ : Grossencharacter K 𝔪) :
    χ.inverse.infinityType = -χ.infinityType := (rfl)

/-- Inversion negates the ideal-side shift: `χ_u N^σ` becomes `conj(χ_u) N^(-σ)`. -/
@[simp]
theorem idealShift_inverse (χ : Grossencharacter K 𝔪) :
    χ.inverse.idealShift = -χ.idealShift := by
  simp [idealShift_def]

/-- Inverting a presentation twice recovers the original presentation. -/
@[simp]
theorem inverse_inverse (χ : Grossencharacter K 𝔪) : χ.inverse.inverse = χ := by
  apply ext
  rw [toHeckeCharacter_inverse, toHeckeCharacter_inverse]
  exact inv_inv χ.toHeckeCharacter

/-- Inversion is an involution on the presentations at a fixed modulus. -/
theorem inverse_involutive :
    Function.Involutive (inverse : Grossencharacter K 𝔪 → Grossencharacter K 𝔪) :=
  inverse_inverse

/-- Inversion commutes with the presentation of a ray class character. -/
@[simp]
theorem inverse_ofRayClassCharacter (η : RayClassCharacter 𝔪) :
    (ofRayClassCharacter η).inverse = ofRayClassCharacter η⁻¹ := by
  apply ext
  rw [toHeckeCharacter_inverse, toHeckeCharacter_ofRayClassCharacter,
    toHeckeCharacter_ofRayClassCharacter]
  exact (map_inv (HeckeCharacter.ofRayClassCharacter 𝔪) η).symm

end TauCeti.LFunctions.Grossencharacter
