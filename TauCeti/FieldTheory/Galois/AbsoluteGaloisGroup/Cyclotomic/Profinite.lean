/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character
import TauCeti.NumberTheory.Cyclotomic.ModularCharacter
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Units
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The profinite cyclotomic character

For a characteristic-zero field `K`, the actions on the roots of unity of all positive
orders assemble into one continuous character of its absolute Galois group with values
in `(Additive zHat)ˣ`. Reduction modulo `n` recovers Mathlib's finite cyclotomic character;
taking the `ℓ`-adic component recovers `localCyclotomicCharacter ℓ K`.

The normalization is the power equation `σ ζ = ζ ^ χ_n(σ)`, with no inverse on the exponent.
The construction uses the existing ring of profinite integers and its `zHat.unitsLift`
universal property, not a new inverse-limit carrier.

## References

* T. Szamuely, *Galois Groups and Fundamental Groups*, Example 4.7.4.
-/

public section

namespace TauCeti

variable (K : Type*) [Field K] [CharZero K]

/-- The continuous cyclotomic character on all roots of unity of a characteristic-zero field. -/
noncomputable def profiniteCyclotomicCharacter :
    Field.absoluteGaloisGroup K →ₜ* (Additive zHat)ˣ :=
  ⟨zHat.unitsLift
    (fun n : ℕ+ ↦ (modularCyclotomicCharacter (AlgebraicClosure K)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity _ n)).comp
        (MulSemiringAction.toRingAut Gal(AlgebraicClosure K/K) (AlgebraicClosure K)))
    (fun _ _ h σ ↦ modularCyclotomicCharacter.unitsMap h _ _ σ.toRingEquiv),
    zHat.continuous_unitsLift _ _ (fun _ ↦ modularCyclotomicCharacter.continuous _)⟩

/-- Reduction of the profinite cyclotomic character is the finite cyclotomic character. -/
@[simp]
theorem map_toZMod_profiniteCyclotomicCharacter (n : ℕ+)
    (σ : Field.absoluteGaloisGroup K) :
    Units.map (zHat.toZMod n) (profiniteCyclotomicCharacter K σ) =
      modularCyclotomicCharacter (AlgebraicClosure K)
        (HasEnoughRootsOfUnity.natCard_rootsOfUnity _ n) σ.toRingEquiv :=
  zHat.map_toZMod_unitsLift _ _ n σ

/-- The finite power equation fixes the normalization of the profinite cyclotomic character. -/
theorem profiniteCyclotomicCharacter_spec (n : ℕ+) (σ : Field.absoluteGaloisGroup K)
    (ζ : AlgebraicClosure K) (hζ : ζ ^ (n : ℕ) = 1) :
    σ.toRingEquiv ζ =
      ζ ^ (zHat.toZMod n (profiniteCyclotomicCharacter K σ : Additive zHat)).val := by
  have h := congrArg Units.val (map_toZMod_profiniteCyclotomicCharacter K n σ)
  simp only [Units.coe_map, MonoidHom.coe_ofClass] at h
  rw [h]
  exact modularCyclotomicCharacter.spec (AlgebraicClosure K)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity _ n) σ.toRingEquiv
    (rootsOfUnity.mkOfPowEq ζ hζ).property

/-- The `ℓ`-adic component of the profinite character is the usual `ℓ`-adic character. -/
@[simp]
theorem map_component_profiniteCyclotomicCharacter (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : Field.absoluteGaloisGroup K) :
    Units.map (zHat.component ℓ) (profiniteCyclotomicCharacter K σ) =
      localCyclotomicCharacter ℓ K σ := by
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro r
  rw [Units.coe_map, MonoidHom.coe_ofClass, zHat.toZModPow_component,
    localCyclotomicCharacter_apply, cyclotomicCharacter.toZModPow]
  exact congrArg Units.val (map_toZMod_profiniteCyclotomicCharacter K
    ⟨ℓ ^ r, pow_pos (Fact.out : ℓ.Prime).pos r⟩ σ)

/-- The finite reductions uniquely characterize the profinite cyclotomic character. -/
theorem profiniteCyclotomicCharacter_unique
    (χ : Field.absoluteGaloisGroup K →* (Additive zHat)ˣ)
    (hχ : ∀ (n : ℕ+) (σ : Field.absoluteGaloisGroup K),
      Units.map (zHat.toZMod n) (χ σ) =
        modularCyclotomicCharacter (AlgebraicClosure K)
          (HasEnoughRootsOfUnity.natCard_rootsOfUnity _ n) σ.toRingEquiv) :
    χ = (profiniteCyclotomicCharacter K).toMonoidHom :=
  zHat.unitsLift_unique _ _ χ hχ

end TauCeti
