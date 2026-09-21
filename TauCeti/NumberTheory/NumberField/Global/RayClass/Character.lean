/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Exact
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Integral

/-!
# Ray class characters

A ray class character of a modulus `𝔪` is a multiplicative character of its finite ray class
group with values in the complex units.  Composing with `idealClass 𝔪` evaluates it on the
nonzero integral ideals prime to the finite part of `𝔪`; the coprimality proof remains in the
domain, so no value is assigned to an ideal at which the character is ramified.

When `𝔪 ∣ 𝔫`, pullback along the surjective transition `classMap : Cl_𝔫 → Cl_𝔪` induces a
character of the larger modulus.  These pullbacks are injective, compose along chains of moduli,
and agree with the inclusion of integral ideals prime to the larger modulus.  This is the finite
character API used in ray-class counting and in the factorization of cyclotomic Galois
characters.

## Main definitions

* `TauCeti.GlobalNumberFields.RayClassCharacter`: multiplicative complex-unit characters of a
  ray class group;
* `TauCeti.GlobalNumberFields.RayClassCharacter.onIdeals`: evaluation on integral ideals prime
  to the modulus;
* `TauCeti.GlobalNumberFields.RayClassCharacter.induced`: pullback of a character along a change
  of modulus.

## Main results

* `TauCeti.GlobalNumberFields.RayClassCharacter.ext_onIdeals`: a ray class character is
  determined by its values on integral ideals;
* `TauCeti.GlobalNumberFields.RayClassCharacter.induced_injective`: increasing the modulus does
  not identify distinct characters;
* `TauCeti.GlobalNumberFields.RayClassCharacter.onIdeals_induced`: change of modulus commutes
  with evaluation on ideals.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VII, §1.
-/

public section

open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- A **ray class character** of `𝔪`: a multiplicative character of `RayClassGroup 𝔪`
with values in the complex units. -/
abbrev RayClassCharacter (𝔪 : Modulus K) := RayClassGroup 𝔪 →* ℂˣ

namespace RayClassCharacter

variable {𝔪 𝔫 𝔬 : Modulus K}

/-- Evaluate a ray class character on nonzero integral ideals prime to its modulus.

The domain is `integralIdealsPrimeTo 𝔪`, rather than all integral ideals, because an ideal
meeting the finite part of the modulus has no ray class and hence no character value. -/
noncomputable def onIdeals (χ : RayClassCharacter 𝔪) : integralIdealsPrimeTo 𝔪 →* ℂˣ :=
  χ.comp (idealClass 𝔪)

/-- Evaluating a ray class character on an ideal is evaluation at the ideal's ray class. -/
@[simp]
theorem onIdeals_apply (χ : RayClassCharacter 𝔪) (I : integralIdealsPrimeTo 𝔪) :
    χ.onIdeals I = χ (idealClass 𝔪 I) :=
  by simp [onIdeals]

/-- A ray class character is determined by its values on integral ideals prime to the modulus. -/
@[ext]
theorem ext_onIdeals {χ ψ : RayClassCharacter 𝔪}
    (h : ∀ I : integralIdealsPrimeTo 𝔪, χ.onIdeals I = ψ.onIdeals I) : χ = ψ := by
  apply MonoidHom.ext
  intro c
  obtain ⟨I, rfl⟩ := idealClass_surjective 𝔪 c
  simpa only [onIdeals_apply] using h I

/-- Pull a ray class character back from a modulus `𝔪` to a multiple `𝔫` of that modulus. -/
noncomputable def induced (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪) : RayClassCharacter 𝔫 :=
  χ.comp (classMap h)

/-- A character induced to a larger modulus is evaluated through the transition map. -/
@[simp]
theorem induced_apply (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪) (c : RayClassGroup 𝔫) :
    χ.induced h c = χ (classMap h c) :=
  by simp [induced]

/-- Pullback along the identity change of modulus fixes every character. -/
@[simp]
theorem induced_refl (χ : RayClassCharacter 𝔪) : χ.induced (Modulus.dvd_refl 𝔪) = χ := by
  apply MonoidHom.ext
  intro c
  simp

/-- Pullback of ray class characters composes along a chain of moduli. -/
@[simp]
theorem induced_trans (h₁ : 𝔪 ∣ 𝔫) (h₂ : 𝔫 ∣ 𝔬) (χ : RayClassCharacter 𝔪) :
    (χ.induced h₁).induced h₂ = χ.induced (Modulus.dvd_trans h₁ h₂) := by
  apply MonoidHom.ext
  intro c
  simp

/-- Pullback of the trivial character is trivial. -/
@[simp]
theorem induced_one (h : 𝔪 ∣ 𝔫) : (1 : RayClassCharacter 𝔪).induced h = 1 := by
  apply MonoidHom.ext
  intro c
  simp

/-- Increasing the modulus does not identify distinct ray class characters. -/
theorem induced_injective (h : 𝔪 ∣ 𝔫) :
    Function.Injective (induced h : RayClassCharacter 𝔪 → RayClassCharacter 𝔫) := by
  intro χ ψ hχψ
  apply MonoidHom.ext
  intro c
  obtain ⟨d, hd⟩ := classMap_surjective h c
  rw [← hd]
  exact DFunLike.congr_fun hχψ d

/-- A character induced to a larger modulus is trivial exactly when the original character is
trivial. -/
@[simp]
theorem induced_eq_one_iff (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪) :
    χ.induced h = 1 ↔ χ = 1 := by
  constructor
  · intro hχ
    apply induced_injective h
    rw [hχ, induced_one]
  · rintro rfl
    exact induced_one h

/-- A nontrivial character remains nontrivial when induced to a larger modulus. -/
theorem induced_ne_one (h : 𝔪 ∣ 𝔫) {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1) :
    χ.induced h ≠ 1 := by
  exact fun h' ↦ hχ ((induced_eq_one_iff h χ).mp h')

/-- Change of modulus commutes with evaluation on integral ideals: the induced character at an
ideal prime to `𝔫` is the original character at the same ideal viewed as prime to `𝔪`. -/
@[simp]
theorem onIdeals_induced (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪)
    (I : integralIdealsPrimeTo 𝔫) :
    (χ.induced h).onIdeals I = χ.onIdeals (integralIdealsPrimeToInclusion h I) := by
  simp [onIdeals, induced]

end RayClassCharacter

end TauCeti.GlobalNumberFields
