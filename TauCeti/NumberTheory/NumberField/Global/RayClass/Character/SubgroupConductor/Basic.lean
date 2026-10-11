/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Conductor
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Finite

import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.NumberField.Global.RayClass.Lattice

/-!
# The conductor of a subgroup of a ray class group

For a subgroup `H` of the ray class group of a modulus `𝔪`, the **conductor** of `H` is the least
modulus `𝔣` such that every ray class character trivial on `H` has conductor dividing `𝔣`. For a
divisor `𝔫` of `𝔪`, the conductor of `H` divides `𝔫` exactly when the kernel of the transition map
`classMap : RayClassGroup 𝔪 →* RayClassGroup 𝔫` lies in `H`, that is, when the projection to
`RayClassGroup 𝔪 ⧸ H` factors through `RayClassGroup 𝔫`. So the conductor of `H` is the least
modulus through which `H` is defined, and it divides `𝔪`.

This is the conductor of an abelian extension in its ideal-theoretic form: if the Artin map of an
abelian extension factors through `RayClassGroup 𝔪`, the conductor of its kernel is the least
modulus through which the Artin map factors.

## Main definitions

* `Subgroup.rayClassConductor`: the conductor of a subgroup of a ray class
  group.

## Main results

* `Subgroup.rayClassConductor_dvd_iff_forall_conductor_dvd`: the conductor of
  `H` divides `𝔫` exactly when the conductor of every ray class character trivial on `H` does.
* `Subgroup.rayClassConductor_dvd_iff`: for `𝔫 ∣ 𝔪`, the conductor of `H`
  divides `𝔫` exactly when the kernel of `classMap` lies in `H`.
* `Subgroup.rayClassConductor_dvd`: the conductor of `H` divides `𝔪`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §6.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 𝔫 : Modulus K}

/-- **A transition map has kernel in `H` exactly when the characters trivial on `H` come from the
smaller modulus.** For `𝔫 ∣ 𝔪` and a subgroup `H` of `RayClassGroup 𝔪`, the kernel of
`classMap : RayClassGroup 𝔪 →* RayClassGroup 𝔫` lies in `H` exactly when every ray class
character of `𝔪` trivial on `H` has conductor dividing `𝔫`. -/
theorem ker_classMap_le_iff (h : 𝔫 ∣ 𝔪) (H : Subgroup (RayClassGroup 𝔪)) :
    (classMap h).ker ≤ H ↔
      ∀ η : RayClassCharacter 𝔪, H ≤ η.ker → η.conductor ∣ 𝔫 := by
  refine ⟨fun hH η hη ↦ (RayClassCharacter.conductor_dvd_iff h).mpr
    ⟨MonoidHom.liftOfSurjective (classMap h) (classMap_surjective h) ⟨η, hH.trans hη⟩,
      MonoidHom.ext fun c ↦ by
        rw [RayClassCharacter.induced_apply, MonoidHom.liftOfRightInverse_comp_apply]⟩,
    fun hη c hc ↦ by_contra fun hcH ↦ ?_⟩
  -- A character of the finite abelian group `RayClassGroup 𝔪 ⧸ H` detects `c ∉ H`.
  obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    (RayClassGroup 𝔪 ⧸ H) ℂ (a := QuotientGroup.mk c) (by rwa [Ne, QuotientGroup.eq_one_iff])
  obtain ⟨ψ, hψ⟩ := (RayClassCharacter.conductor_dvd_iff h).mp
    (hη (χ.comp (QuotientGroup.mk' H)) fun x hx ↦ by
      simp [MonoidHom.mem_ker, (QuotientGroup.eq_one_iff x).mpr hx])
  refine hχ ?_
  have hc' := congrArg (fun η : RayClassCharacter 𝔪 ↦ η c) hψ
  simp only [RayClassCharacter.induced_apply, MonoidHom.mem_ker.mp hc, map_one] at hc'
  simpa using hc'.symm

end TauCeti.GlobalNumberFields

namespace Subgroup

open TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 𝔫 : Modulus K}

/-- The moduli dividing the conductor of every ray class character of `𝔪` trivial on `H`. -/
private def conductorBounds (H : Subgroup (RayClassGroup 𝔪)) : Set (Modulus K) :=
  {𝔫 | ∀ η : RayClassCharacter 𝔪, H ≤ η.ker → η.conductor ∣ 𝔫}

private theorem mem_conductorBounds_self (H : Subgroup (RayClassGroup 𝔪)) :
    𝔪 ∈ conductorBounds H :=
  fun η _ ↦ η.conductor_dvd

/-- **The conductor of a subgroup of a ray class group**: the least modulus divisible by the
conductor of every ray class character trivial on the subgroup
(`rayClassConductor_dvd_iff_forall_conductor_dvd`). For `𝔫 ∣ 𝔪` it divides `𝔫` exactly when the
subgroup contains the kernel of `classMap : RayClassGroup 𝔪 →* RayClassGroup 𝔫`
(`rayClassConductor_dvd_iff`). -/
def rayClassConductor (H : Subgroup (RayClassGroup 𝔪)) : Modulus K :=
  Modulus.wellFounded_dvd_and_ne.min (conductorBounds H) ⟨𝔪, mem_conductorBounds_self H⟩

/-- **The conductor of a subgroup is the least common multiple of the conductors of the
characters trivial on it**: it divides `𝔫` exactly when the conductor of every ray class character
trivial on the subgroup divides `𝔫`. -/
theorem rayClassConductor_dvd_iff_forall_conductor_dvd (H : Subgroup (RayClassGroup 𝔪)) :
    rayClassConductor H ∣ 𝔫 ↔ ∀ η : RayClassCharacter 𝔪, H ≤ η.ker → η.conductor ∣ 𝔫 := by
  have hmem : rayClassConductor H ∈ conductorBounds H :=
    WellFounded.min_mem _ _ ⟨𝔪, mem_conductorBounds_self H⟩
  refine ⟨fun h η hη ↦ Modulus.dvd_trans (hmem η hη) h, fun h ↦ ?_⟩
  -- The greatest common divisor of the conductor and `𝔫` is again a bound, so by minimality it is
  -- the conductor.
  have hgcd : (rayClassConductor H).gcd 𝔫 ∈ conductorBounds H :=
    fun η hη ↦ Modulus.dvd_gcd (hmem η hη) (h η hη)
  have hmin := Modulus.wellFounded_dvd_and_ne.not_lt_min (conductorBounds H) hgcd
  have heq : (rayClassConductor H).gcd 𝔫 = rayClassConductor H :=
    not_not.mp fun hne ↦ hmin ⟨Modulus.gcd_dvd_left _ _, hne⟩
  exact heq ▸ Modulus.gcd_dvd_right _ _

/-- **The conductor of a subgroup is the least modulus through which it is defined**: for
`𝔫 ∣ 𝔪`, the conductor of `H` divides `𝔫` exactly when the kernel of
`classMap : RayClassGroup 𝔪 →* RayClassGroup 𝔫` lies in `H`. -/
theorem rayClassConductor_dvd_iff (h : 𝔫 ∣ 𝔪) (H : Subgroup (RayClassGroup 𝔪)) :
    rayClassConductor H ∣ 𝔫 ↔ (classMap h).ker ≤ H := by
  rw [rayClassConductor_dvd_iff_forall_conductor_dvd, ker_classMap_le_iff]

/-- The conductor of a subgroup of the ray class group of `𝔪` divides `𝔪`. -/
theorem rayClassConductor_dvd (H : Subgroup (RayClassGroup 𝔪)) : rayClassConductor H ∣ 𝔪 :=
  (rayClassConductor_dvd_iff_forall_conductor_dvd H).mpr fun η _ ↦ η.conductor_dvd

/-- The kernel of the transition map from `𝔪` to the conductor of `H` lies in `H`. -/
theorem ker_classMap_rayClassConductor_le (H : Subgroup (RayClassGroup 𝔪)) :
    (classMap (rayClassConductor_dvd H)).ker ≤ H :=
  (rayClassConductor_dvd_iff (rayClassConductor_dvd H) H).mp (Modulus.dvd_refl _)

/-- A larger subgroup has a smaller conductor. -/
theorem rayClassConductor_dvd_of_le {H H' : Subgroup (RayClassGroup 𝔪)} (hle : H ≤ H') :
    rayClassConductor H' ∣ rayClassConductor H :=
  (rayClassConductor_dvd_iff_forall_conductor_dvd H').mpr fun _ hη ↦
    (rayClassConductor_dvd_iff_forall_conductor_dvd H).mp (Modulus.dvd_refl _) _ (hle.trans hη)

end Subgroup

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- The conductor of a ray class character trivial on `H` divides the conductor of `H`. -/
theorem RayClassCharacter.conductor_dvd_rayClassConductor {H : Subgroup (RayClassGroup 𝔪)}
    {η : RayClassCharacter 𝔪} (hη : H ≤ η.ker) : η.conductor ∣ H.rayClassConductor :=
  (H.rayClassConductor_dvd_iff_forall_conductor_dvd).mp (Modulus.dvd_refl _) η hη

end TauCeti.GlobalNumberFields
