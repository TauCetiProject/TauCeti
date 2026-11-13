/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
public import TauCeti.GroupTheory.Coprod.Basic
public import TauCeti.GroupTheory.PresentedGroup

/-!
# Systems of equations without coefficients

A system of equations over a group `G` whose equations involve no coefficients is a set of
relators `R` in the free group on the variables. The group `G_S = G[X] ⧸ ncl(S)` of such a system
is the free product of `G` with the group presented by these relators. More precisely, if the
equations only involve the variables from a part `α` of `X = α ⊕ β`, then

`G_S ≃* G ∗ ⟨α | R⟩ ∗ F(β)`:

the variables that do not occur in the system are free generators of a free factor.

## Main definitions

* `TauCeti.GroupAlgGeom.SystemGroup.coprodPresentedGroupEquiv`: the isomorphism
  `G_S ≃* G ∗ ⟨X | R⟩` for a system `S` given by relators `R` in the variables.
* `TauCeti.GroupAlgGeom.SystemGroup.coprodPresentedGroupFreeGroupEquiv`: the isomorphism
  `G_S ≃* G ∗ (⟨α | R⟩ ∗ F(β))` for a system `S` given by relators `R` in the variables `α`.
-/

public section

namespace TauCeti.GroupAlgGeom.SystemGroup

open Monoid.Coprod Subgroup

variable {G X α β : Type*} [Group G]

section PresentedGroup

variable (R : Set (FreeGroup X))

variable (G) in
/-- The group of a system without coefficients: if `R` is a set of words in the variables, then
the group of the system `R` over `G` is the free product of `G` and the group presented by
`R`. -/
def coprodPresentedGroupEquiv :
    SystemGroup G ((inr : FreeGroup X →* GX G X) '' R) ≃* Monoid.Coprod G (PresentedGroup R) :=
  quotientNormalClosureInrEquiv R

@[simp]
theorem coprodPresentedGroupEquiv_mk (w : GX G X) :
    coprodPresentedGroupEquiv G R (w : SystemGroup G _) =
      map (.id G) (PresentedGroup.mk R) w :=
  quotientNormalClosureInrEquiv_mk R w

@[simp]
theorem coprodPresentedGroupEquiv_symm_inl (g : G) :
    (coprodPresentedGroupEquiv G R).symm (inl g) = ((inl g : GX G X) : SystemGroup G _) :=
  quotientNormalClosureInrEquiv_symm_inl R g

@[simp]
theorem coprodPresentedGroupEquiv_symm_inr_mk (w : FreeGroup X) :
    (coprodPresentedGroupEquiv G R).symm (inr (PresentedGroup.mk R w)) =
      ((inr w : GX G X) : SystemGroup G _) :=
  quotientNormalClosureInrEquiv_symm_inr_mk R w

@[simp]
theorem coprodPresentedGroupEquiv_symm_inr_of (x : X) :
    (coprodPresentedGroupEquiv G R).symm (inr (PresentedGroup.of x)) =
      ((inr (FreeGroup.of x) : GX G X) : SystemGroup G _) :=
  coprodPresentedGroupEquiv_symm_inr_mk R (FreeGroup.of x)

end PresentedGroup

section FreeGroup

variable (R : Set (FreeGroup α)) (e : α ⊕ β ≃ X)

variable (G) in
/-- A system without coefficients, in some of the variables: if the variables `X` split as
`α ⊕ β` and `R` is a set of words in the variables from `α`, then the group of the system `R`
over `G` is the free product of `G`, the group presented by `R` on `α`, and the free group on the
remaining variables `β`. -/
def coprodPresentedGroupFreeGroupEquiv :
    SystemGroup G ((inr : FreeGroup X →* GX G X) '' (FreeGroup.map (e ∘ Sum.inl) '' R)) ≃*
      Monoid.Coprod G (Monoid.Coprod (PresentedGroup R) (FreeGroup β)) :=
  (coprodPresentedGroupEquiv G _).trans
    (MulEquiv.coprodCongr (.refl G) (PresentedGroup.coprodFreeGroupEquiv R e))

@[simp]
theorem coprodPresentedGroupFreeGroupEquiv_mk_inl (g : G) :
    coprodPresentedGroupFreeGroupEquiv G R e ((inl g : GX G X) : SystemGroup G _) = inl g := by
  simp [coprodPresentedGroupFreeGroupEquiv]

@[simp]
theorem coprodPresentedGroupFreeGroupEquiv_mk_inr_of (x : X) :
    coprodPresentedGroupFreeGroupEquiv G R e ((inr (FreeGroup.of x) : GX G X) : SystemGroup G _) =
      inr (Sum.elim (fun a => inl (PresentedGroup.of a)) (fun b => inr (FreeGroup.of b))
        (e.symm x)) := by
  simp [coprodPresentedGroupFreeGroupEquiv]

theorem coprodPresentedGroupFreeGroupEquiv_mk_inr_of_inl (a : α) :
    coprodPresentedGroupFreeGroupEquiv G R e
        ((inr (FreeGroup.of (e (Sum.inl a))) : GX G X) : SystemGroup G _) =
      inr (inl (PresentedGroup.of a)) := by
  simp

theorem coprodPresentedGroupFreeGroupEquiv_mk_inr_of_inr (b : β) :
    coprodPresentedGroupFreeGroupEquiv G R e
        ((inr (FreeGroup.of (e (Sum.inr b))) : GX G X) : SystemGroup G _) =
      inr (inr (FreeGroup.of b)) := by
  simp

@[simp]
theorem coprodPresentedGroupFreeGroupEquiv_symm_inl (g : G) :
    (coprodPresentedGroupFreeGroupEquiv G R e).symm (inl g) =
      ((inl g : GX G X) : SystemGroup G _) := by
  simp [MulEquiv.symm_apply_eq]

@[simp]
theorem coprodPresentedGroupFreeGroupEquiv_symm_inr_inl_of (a : α) :
    (coprodPresentedGroupFreeGroupEquiv G R e).symm (inr (inl (PresentedGroup.of a))) =
      ((inr (FreeGroup.of (e (Sum.inl a))) : GX G X) : SystemGroup G _) := by
  simp [MulEquiv.symm_apply_eq]

@[simp]
theorem coprodPresentedGroupFreeGroupEquiv_symm_inr_inl_mk (u : FreeGroup α) :
    (coprodPresentedGroupFreeGroupEquiv G R e).symm (inr (inl (PresentedGroup.mk R u))) =
      ((inr (FreeGroup.map (e ∘ Sum.inl) u) : GX G X) : SystemGroup G _) := by
  simp [coprodPresentedGroupFreeGroupEquiv]

@[simp]
theorem coprodPresentedGroupFreeGroupEquiv_symm_inr_inr_of (b : β) :
    (coprodPresentedGroupFreeGroupEquiv G R e).symm (inr (inr (FreeGroup.of b))) =
      ((inr (FreeGroup.of (e (Sum.inr b))) : GX G X) : SystemGroup G _) := by
  simp [MulEquiv.symm_apply_eq]

end FreeGroup

end TauCeti.GroupAlgGeom.SystemGroup
