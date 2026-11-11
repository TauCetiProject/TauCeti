/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic

/-!
# Faithful quotient representations

Mathlib's `Representation.ofQuotient` descends a representation through a normal subgroup
acting trivially. The kernel always acts trivially, and quotienting by it gives a faithful
representation on the original module, with the caller's scalar and additive structures.
-/

public section

namespace Representation

variable {R G M : Type*} [Semiring R] [Group G] [AddCommMonoid M] [Module R M]
    (ρ : Representation R G M)

/-- Restriction to the kernel is a trivial representation. -/
instance isTrivial_comp_ker : IsTrivial (ρ.comp ρ.ker.subtype) where
  out g := MonoidHom.mem_ker.mp g.2

/-- Restricting a quotient representation along the quotient map recovers the original
representation, on the same module with the caller's scalar and additive structures. -/
@[simp]
theorem ofQuotient_comp_mk' (S : Subgroup G) [S.Normal]
    [IsTrivial (ρ.comp S.subtype)] :
    (ρ.ofQuotient S).comp (QuotientGroup.mk' S) = ρ :=
  MonoidHom.ext fun g ↦ LinearMap.ext fun v ↦ ρ.ofQuotient_coe_apply S g v

/-- A quotient representation is faithful exactly when the subgroup removed is the entire
kernel. -/
theorem injective_ofQuotient_iff (S : Subgroup G) [S.Normal]
    [IsTrivial (ρ.comp S.subtype)] :
    Function.Injective (ρ.ofQuotient S) ↔ S = ρ.ker := by
  have hS : S ≤ ρ.ker := fun g hg ↦
    MonoidHom.mem_ker.mpr (isTrivial_def (ρ.comp S.subtype) ⟨g, hg⟩)
  have h : ρ.ofQuotient S = QuotientGroup.lift S ρ hS := by
    ext q x
    simp
  rw [h, QuotientGroup.injective_lift_iff]

end Representation
