/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Conductor
public import TauCeti.NumberTheory.NumberField.Global.Ideles.IdentityComponent

import TauCeti.Analysis.Normed.Algebra.NoSmallSubgroups
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Hecke characters trivial on the identity component

A Hecke character has finite order exactly when it kills the identity component of the idele
class group. Thus the ray conductor is available for every character trivial on that component,
without an additional finite-order hypothesis.

The quotient by the identity component is profinite. A character on it has open kernel because
the complex units have no small subgroups; it therefore factors through a finite ray class group.
Conversely, the open kernel of a finite-order character contains the identity component.

The proof uses the profiniteness established in
`TauCeti.NumberTheory.NumberField.Global.Ideles.IdentityComponent` and the no-small-subgroups
theorem `ContinuousMonoidHom.exists_mem_nhds_one_forall_le_ker`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
* E. Artin and J. Tate, *Class Field Theory*, Chapter IX.
-/

public section

open IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti.GlobalNumberFields.HeckeCharacter

variable {K : Type*} [Field K] [NumberField K]

/-- A Hecke character has finite order exactly when its kernel contains the identity component
of the idele class group. In particular, triviality on the identity component suffices to use
`HeckeCharacter.conductor`. -/
theorem isFiniteOrder_iff_connectedComponentOfOne_le_ker (χ : HeckeCharacter K) :
    χ.IsFiniteOrder ↔
      Subgroup.connectedComponentOfOne (IdeleClassGroup (𝓞 K) K) ≤ χ.ker := by
  refine ⟨fun hχ ↦ Subgroup.connectedComponentOfOne_le_of_isOpen
    (isOpen_ker_of_isFiniteOrder hχ), fun hχ ↦ ?_⟩
  let D := Subgroup.connectedComponentOfOne (IdeleClassGroup (𝓞 K) K)
  let ψ := ContinuousMonoidHom.quotientLift D χ hχ
  have hψ : IsOpen (ψ.ker : Set (IdeleClassGroup (𝓞 K) K ⧸ D)) :=
    ψ.isOpen_ker_of_compactSpace_of_totallyDisconnectedSpace
  apply (isFiniteOrder_iff_isOpen_ker χ).mpr
  have hker : ψ.ker.comap (QuotientGroup.mk' D) = χ.ker := by
    simp only [ψ, ContinuousMonoidHom.coe_quotientLift, MonoidHom.comap_ker,
      QuotientGroup.lift_comp_mk', ContinuousMonoidHom.coe_toMonoidHom]
  rw [← ContinuousMonoidHom.coe_toMonoidHom χ, ← hker, Subgroup.coe_comap]
  exact hψ.preimage QuotientGroup.continuous_mk

/-- A Hecke character trivial on the identity component has a unique least ray conductor:
it comes from a ray class character of a modulus exactly when that conductor divides the
modulus. -/
theorem existsUnique_rayConductor_of_connectedComponentOfOne_le_ker (χ : HeckeCharacter K)
    (hχ : Subgroup.connectedComponentOfOne (IdeleClassGroup (𝓞 K) K) ≤ χ.ker) :
    ∃! 𝔣 : Modulus K, ∀ 𝔪 : Modulus K,
      𝔣 ∣ 𝔪 ↔ χ ∈ (ofRayClassCharacter 𝔪).range := by
  have hfin := (isFiniteOrder_iff_connectedComponentOfOne_le_ker χ).mpr hχ
  refine ⟨χ.conductor hfin, fun _ ↦ conductor_dvd_iff hfin, fun 𝔣 h𝔣 ↦ ?_⟩
  exact Modulus.dvd_antisymm
    ((h𝔣 _).mpr (mem_range_ofRayClassCharacter_conductor hfin))
    ((conductor_dvd_iff hfin).mpr ((h𝔣 𝔣).mp (Modulus.dvd_refl 𝔣)))

end TauCeti.GlobalNumberFields.HeckeCharacter
