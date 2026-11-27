/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Conductor.Basic
public import TauCeti.NumberTheory.LocalField.Herbrand.ArtinConductor

import Mathlib.GroupTheory.FiniteAbelian.Duality
import TauCeti.NumberTheory.ClassFieldTheory.Local.UnitFiltration

/-!
# Local conductor exponents and characters

For a finite Galois extension of nonarchimedean local fields, the norm conductor exponent is the
maximum of the Artin conductor exponents of its one-dimensional characters
(`conductorExponent_eq_iSup_artinConductorExponent`). The bound is characterized in
`conductorExponent_le_iff_forall_artinConductorExponent_le`. The comparison uses
`normResidue_map_unitFiltration` and Mathlib's separation of points of the abelianized Galois
group by characters (`CommGroup.forall_apply_eq_apply_iff`).

## References

* J.-P. Serre, *Local Fields*, Chapter XV, §2.
-/

public section

open TauCeti.LocalFieldsRamification

namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [IsGalois K L]

local instance : Module.Finite K L := finite_of_valuativeExtension K L

variable (A : Type*) [CommMonoid A]
  [HasEnoughRootsOfUnity A (Monoid.exponent (Group.Abelianization Gal(L/K)))]

variable {K L} in
/-- The norm conductor exponent of a finite Galois extension of local fields is at most `n`
exactly when all one-dimensional characters have Artin conductor exponent at most `n`.
The character target must have enough roots of unity for the abelianized Galois group.
See Serre, *Local Fields*, Chapter XV, §2. -/
theorem conductorExponent_le_iff_forall_artinConductorExponent_le {n : ℕ} :
    conductorExponent K L ≤ n ↔ ∀ χ : Gal(L/K) →* Aˣ, artinConductorExponent K L χ ≤ n := by
  have hnorm : conductorExponent K L ≤ n ↔
      (unitFiltration K n).map
        ((normResidue K L).toMonoidHom.comp (QuotientGroup.mk' (normGroup K L))) = ⊥ := by
    rw [conductorExponent_le_iff, Subgroup.map_eq_bot_iff]
    simp only [IsConcreteLE.le_iff, MonoidHom.mem_ker, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply, normResidue_mk_eq_one_iff]
  rw [hnorm, normResidue_map_unitFiltration, Subgroup.map_eq_bot_iff]
  simp_rw [artinConductorExponent_le_iff]
  constructor
  · rw [Group.Abelianization.ker_of]
    exact fun h χ ↦ h.trans (Group.Abelianization.commutator_le_ker χ)
  · intro h σ hσ
    apply MonoidHom.mem_ker.2
    exact (CommGroup.forall_apply_eq_apply_iff (Group.Abelianization Gal(L/K)) (M := A)).1 fun χ ↦
      (MonoidHom.mem_ker.1 (h (χ.comp Group.Abelianization.of) hσ)).trans (map_one χ).symm

/-- The norm conductor exponent of a finite Galois extension of local fields is the maximum Artin
conductor exponent of its one-dimensional characters. The character target must have enough
roots of unity for the abelianized Galois group. See Serre, *Local Fields*, Chapter XV, §2. -/
theorem conductorExponent_eq_iSup_artinConductorExponent :
    conductorExponent K L = ⨆ χ : Gal(L/K) →* Aˣ, artinConductorExponent K L χ := by
  have hb : BddAbove (Set.range fun χ : Gal(L/K) →* Aˣ ↦ artinConductorExponent K L χ) :=
    ⟨conductorExponent K L, Set.forall_mem_range.2
      ((conductorExponent_le_iff_forall_artinConductorExponent_le A).1 le_rfl)⟩
  exact eq_of_forall_ge_iff fun n ↦
    (conductorExponent_le_iff_forall_artinConductorExponent_le A).trans (ciSup_le_iff hb).symm

end TauCeti.ClassFieldTheory
