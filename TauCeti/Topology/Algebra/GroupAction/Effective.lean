/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Homeomorph.Quotient
public import TauCeti.GroupTheory.GroupAction.Effective

/-!
# The coarse space of the faithful quotient action

Dividing by the kernel of a permutation action preserves the actual orbit quotient with its
quotient topology. This needs no continuity assumption: the two orbit relations coincide.
If the original group acts by continuous maps, so does the quotient group.

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

public section

namespace TauCeti

open MulAction

variable (G X : Type*) [Group G] [MulAction G X] [TopologicalSpace X]

/-- A faithful quotient of an action by continuous maps still acts by continuous maps. -/
instance instContinuousConstSMulQuotientKerToPermHom [ContinuousConstSMul G X] :
    ContinuousConstSMul (G ⧸ (toPermHom G X).ker) X where
  continuous_const_smul q := QuotientGroup.induction_on q fun g ↦ by
    simpa only [quotientKerToPermHom_mk_smul] using (continuous_const_smul g : Continuous (g • ·))

/-- Effective reduction of a connected finite smooth action chart preserves its coarse topology.
More generally, every action has the same orbit topology as its faithful quotient. -/
def effectiveOrbitHomeomorph :
    orbitRel.Quotient G X ≃ₜ orbitRel.Quotient (G ⧸ (toPermHom G X).ker) X :=
  Homeomorph.Quotient.congrRight fun x y ↦ (orbitRel_quotientKerToPermHom_iff G X x y).symm

@[simp]
theorem effectiveOrbitHomeomorph_mk (x : X) :
    effectiveOrbitHomeomorph G X (Quotient.mk _ x) = Quotient.mk _ x := (rfl)

@[simp]
theorem effectiveOrbitHomeomorph_symm_mk (x : X) :
    (effectiveOrbitHomeomorph G X).symm (Quotient.mk _ x) = Quotient.mk _ x := (rfl)

@[simp]
theorem effectiveOrbitHomeomorph_toEquiv :
    (effectiveOrbitHomeomorph G X).toEquiv = effectiveOrbitEquiv G X := by
  apply Equiv.ext
  intro q
  induction q using Quotient.inductionOn with
  | h x => exact (effectiveOrbitEquiv_mk G X x).symm

end TauCeti
