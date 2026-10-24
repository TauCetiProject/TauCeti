/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Stabilizer

/-!
# The faithful quotient of a group action

The quotient of a group by the kernel of its permutation action acts faithfully on the same
space. The action and its faithful quotient have exactly the same orbits. This is the algebraic
part of effective reduction of a connected finite smooth action chart: in that setting the
kernel of the action is also its ineffective germ kernel. For arbitrary actions, faithfulness
need not imply effectiveness of every local germ.

The quotient action uses Mathlib's `QuotientGroup.kerLift` and `MulAction.compHom`.

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

public section

namespace TauCeti

open _root_.MulAction

variable (G X : Type*) [Group G] [MulAction G X]

/-- The quotient by the permutation-action kernel acts on the original space. -/
instance instMulActionQuotientKerToPermHom :
    MulAction (G ⧸ (toPermHom G X).ker) X :=
  MulAction.compHom X (QuotientGroup.kerLift (toPermHom G X))

/-- A coset represented by `g` acts in exactly the same way as `g`. -/
@[simp]
theorem quotientKerToPermHom_mk_smul (g : G) (x : X) :
    (QuotientGroup.mk g : G ⧸ (toPermHom G X).ker) • x = g • x := (rfl)

/-- Dividing by the full action kernel makes the action faithful. -/
instance instFaithfulSMulQuotientKerToPermHom :
    FaithfulSMul (G ⧸ (toPermHom G X).ker) X where
  eq_of_smul_eq_smul h :=
    QuotientGroup.kerLift_injective (toPermHom G X) (Equiv.ext h)

/-- Dividing out the action kernel does not change the orbit relation. -/
theorem orbitRel_quotientKerToPermHom_iff (x y : X) :
    orbitRel (G ⧸ (toPermHom G X).ker) X x y ↔ orbitRel G X x y := by
  simp only [orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨g, hq⟩
  · rintro ⟨g, hg⟩
    exact ⟨QuotientGroup.mk g, hg⟩

/-- The projection onto the faithful quotient restricts to a homomorphism of stabilizers. -/
def effectiveStabilizerMap (x : X) :
    stabilizer G x →* stabilizer (G ⧸ (toPermHom G X).ker) x :=
  stabilizerMap (QuotientGroup.mk' _) x (quotientKerToPermHom_mk_smul G X · x)

@[simp]
theorem effectiveStabilizerMap_apply (x : X) (g : stabilizer G x) :
    (effectiveStabilizerMap G X x g : G ⧸ (toPermHom G X).ker) = QuotientGroup.mk (g : G) :=
  stabilizerMap_apply (QuotientGroup.mk' _) x (quotientKerToPermHom_mk_smul G X · x) g

/-- Every stabilizer element of the faithful quotient lifts to an original stabilizer element. -/
theorem effectiveStabilizerMap_surjective (x : X) :
    Function.Surjective (effectiveStabilizerMap G X x) :=
  stabilizerMap_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) x
    (quotientKerToPermHom_mk_smul G X · x)

/-- The stabilizer projection kills exactly the elements in the original action kernel. -/
@[simp]
theorem ker_effectiveStabilizerMap (x : X) :
    (effectiveStabilizerMap G X x).ker = (toPermHom G X).ker.subgroupOf (stabilizer G x) := by
  rw [effectiveStabilizerMap, TauCeti.ker_stabilizerMap, QuotientGroup.ker_mk']

/-- Isotropy of the faithful quotient is the original stabilizer modulo the action kernel. -/
noncomputable def effectiveStabilizerEquiv (x : X) :
    stabilizer G x ⧸ (toPermHom G X).ker.subgroupOf (stabilizer G x) ≃*
      stabilizer (G ⧸ (toPermHom G X).ker) x :=
  QuotientGroup.liftEquiv _ (effectiveStabilizerMap_surjective G X x)
    (ker_effectiveStabilizerMap G X x).symm

@[simp]
theorem effectiveStabilizerEquiv_mk (x : X) (g : stabilizer G x) :
    effectiveStabilizerEquiv G X x (QuotientGroup.mk g) = effectiveStabilizerMap G X x g :=
  QuotientGroup.liftEquiv_mk _ _ _ g

/-- The orbit spaces of an action and its faithful quotient are canonically equivalent. -/
def effectiveOrbitEquiv :
    orbitRel.Quotient G X ≃ orbitRel.Quotient (G ⧸ (toPermHom G X).ker) X :=
  Quotient.congrRight fun x y ↦ (orbitRel_quotientKerToPermHom_iff G X x y).symm

@[simp]
theorem effectiveOrbitEquiv_mk (x : X) :
    effectiveOrbitEquiv G X (Quotient.mk _ x) = Quotient.mk _ x := (rfl)

@[simp]
theorem effectiveOrbitEquiv_symm_mk (x : X) :
    (effectiveOrbitEquiv G X).symm (Quotient.mk _ x) = Quotient.mk _ x := (rfl)

end TauCeti
