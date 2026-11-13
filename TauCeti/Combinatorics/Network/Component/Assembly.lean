/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Component.Basic

/-!
# Assembling bounded assignments from weak components

An arrow has both endpoints in the same weakly connected component. Thus arbitrary assignments
on the components assemble uniquely into an assignment on the whole arrow family. Restriction
preserves excess, so the assembly also preserves arrow bounds and exact or interval excess
constraints. The resulting equivalences identify each global feasible-assignment type with the
product of its component feasible-assignment types.

In particular, feasibility can be checked and witnesses constructed independently on each weak
component. This is stronger than the necessary componentwise balance conditions: all the arrow
and vertex constraints are retained in each component problem. Empty vertex types, isolated
vertices, loops, and parallel arrows require no exceptions.
-/

public section

namespace TauCeti

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

open _root_.Quiver

namespace Assignment

/-- Restriction to all weak components is a bijection on arrow assignments. Its inverse assigns
to an arrow the value supplied by the component containing its source and target. No finiteness
or algebraic structure on the values is needed. -/
def componentEquiv (Q : V → V → Type v) (K : Type w) :
    Assignment Q K ≃
      ((C : @WeaklyConnectedComponent V ⟨Q⟩) → Assignment (Quiver.ComponentHom Q C) K) where
  toFun f C := f.restrictComponent C
  invFun f x y e := f (@WeaklyConnectedComponent.mk V ⟨Q⟩ x)
    (x := ⟨x, rfl⟩) (y := ⟨y, (Quiver.weaklyConnectedComponent_mk_eq_of_hom e).symm⟩) e
  left_inv f := by
    funext x y e
    exact restrictComponent_apply (@WeaklyConnectedComponent.mk V ⟨Q⟩ x) f
      (x := ⟨x, rfl⟩) (y := ⟨y, (Quiver.weaklyConnectedComponent_mk_eq_of_hom e).symm⟩) e
  right_inv f := by
    funext C ⟨x, hx⟩ ⟨y, hy⟩ e
    subst C
    simp only [restrictComponent_apply]

/-- The forward equivalence is component restriction. -/
@[simp]
theorem componentEquiv_apply (f : Assignment Q K) :
    componentEquiv Q K f = fun C ↦ f.restrictComponent C :=
  (rfl)

/-- Assembly evaluates an arrow in the component of its source. -/
@[simp]
theorem componentEquiv_symm_apply
    (f : (C : @WeaklyConnectedComponent V ⟨Q⟩) → Assignment (Quiver.ComponentHom Q C) K)
    {x y : V} (e : Q x y) :
    (componentEquiv Q K).symm f e = f (@WeaklyConnectedComponent.mk V ⟨Q⟩ x)
      (x := ⟨x, rfl⟩) (y := ⟨y, (Quiver.weaklyConnectedComponent_mk_eq_of_hom e).symm⟩) e :=
  (rfl)

/-- Restricting an assembled assignment recovers the supplied component assignment. -/
@[simp]
theorem restrictComponent_componentEquiv_symm
    (f : (C : @WeaklyConnectedComponent V ⟨Q⟩) → Assignment (Quiver.ComponentHom Q C) K)
    (C : @WeaklyConnectedComponent V ⟨Q⟩) :
    ((componentEquiv Q K).symm f).restrictComponent C = f C := by
  have h := congrFun ((componentEquiv Q K).apply_symm_apply f) C
  rwa [componentEquiv_apply] at h

/-- Arrowwise bounds hold globally exactly when they hold on every component. -/
theorem mem_Icc_iff_forall_restrictComponent [Preorder K] (f lo hi : Assignment Q K) :
    f ∈ Set.Icc lo hi ↔ ∀ C, f.restrictComponent C ∈
      Set.Icc (lo.restrictComponent C) (hi.restrictComponent C) := by
  constructor
  · intro hf C
    exact ⟨fun x y e ↦ by simpa using hf.1 x.1 y.1 e,
      fun x y e ↦ by simpa using hf.2 x.1 y.1 e⟩
  · intro hf
    constructor <;> intro x y e
    · simpa using (hf (@WeaklyConnectedComponent.mk V ⟨Q⟩ x)).1
        ⟨x, rfl⟩ ⟨y, (Quiver.weaklyConnectedComponent_mk_eq_of_hom e).symm⟩ e
    · simpa using (hf (@WeaklyConnectedComponent.mk V ⟨Q⟩ x)).2
        ⟨x, rfl⟩ ⟨y, (Quiver.weaklyConnectedComponent_mk_eq_of_hom e).symm⟩ e

variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K]

/-- The excess of an assembled assignment is the excess computed in its vertex's component. -/
theorem excessAt_componentEquiv_symm
    (f : (C : @WeaklyConnectedComponent V ⟨Q⟩) → Assignment (Quiver.ComponentHom Q C) K)
    (x : V) :
    excessAt ((componentEquiv Q K).symm f) x =
      excessAt (f (@WeaklyConnectedComponent.mk V ⟨Q⟩ x)) ⟨x, rfl⟩ := by
  have h := excessAt_restrictComponent (@WeaklyConnectedComponent.mk V ⟨Q⟩ x)
    ((componentEquiv Q K).symm f) ⟨x, rfl⟩
  rw [restrictComponent_componentEquiv_symm] at h
  exact h.symm

end Assignment

section Bounded

variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K] [Preorder K]
variable (lo hi : Assignment Q K) (d a b : V → K)

namespace ExcessFlow

/-- A prescribed-excess assignment is exactly a choice of a prescribed-excess assignment on each
weak component, with inherited arrow bounds and prescribed excess. -/
def componentEquiv : ExcessFlow lo hi d ≃
    ((C : @WeaklyConnectedComponent V ⟨Q⟩) →
      ExcessFlow (lo.restrictComponent C) (hi.restrictComponent C) (fun x ↦ d x.1)) where
  toFun f C := f.restrictComponent C
  invFun f := ⟨(Assignment.componentEquiv Q K).symm (fun C ↦ (f C).val),
    ⟨(Assignment.mem_Icc_iff_forall_restrictComponent _ lo hi).2 (by
        intro C
        simpa using (f C).mem_Icc),
      funext fun x ↦ by
        rw [Assignment.excessAt_componentEquiv_symm]
        exact (f (@WeaklyConnectedComponent.mk V ⟨Q⟩ x)).excessAt_eq ⟨x, rfl⟩⟩⟩
  left_inv f := by
    apply Subtype.ext
    simpa only [restrictComponent_val, ← Assignment.componentEquiv_apply] using
      (Assignment.componentEquiv Q K).symm_apply_apply f.val
  right_inv f := by
    funext C
    apply Subtype.ext
    simpa only [restrictComponent_val, Assignment.componentEquiv_apply] using
      congrFun ((Assignment.componentEquiv Q K).apply_symm_apply (fun C ↦ (f C).val)) C

/-- The equivalence sends a feasible assignment to its component restrictions. -/
@[simp]
theorem componentEquiv_apply (f : ExcessFlow lo hi d) :
    componentEquiv lo hi d f = fun C ↦ f.restrictComponent C :=
  (rfl)

/-- The inverse equivalence assembles the component arrow assignments without changing values. -/
@[simp]
theorem componentEquiv_symm_val
    (f : (C : @WeaklyConnectedComponent V ⟨Q⟩) →
      ExcessFlow (lo.restrictComponent C) (hi.restrictComponent C) (fun x ↦ d x.1)) :
    ((componentEquiv lo hi d).symm f).val =
      (Assignment.componentEquiv Q K).symm (fun C ↦ (f C).val) :=
  (rfl)

/-- Prescribed-excess feasibility is equivalent to feasibility on every weak component. The
component conditions retain all bounds, not just the necessary balance of prescribed excess. -/
theorem nonempty_iff_forall_component :
    Nonempty (ExcessFlow lo hi d) ↔ ∀ C : @WeaklyConnectedComponent V ⟨Q⟩,
      Nonempty (ExcessFlow (lo.restrictComponent C) (hi.restrictComponent C) (fun x ↦ d x.1)) := by
  rw [(componentEquiv lo hi d).nonempty_congr]
  exact Classical.nonempty_pi

end ExcessFlow

namespace ExcessIntervalFlow

/-- An interval-excess assignment is exactly a choice of such an assignment on each weak
component, retaining both arrow bounds and both vertex-excess bounds. -/
def componentEquiv : ExcessIntervalFlow lo hi a b ≃
    ((C : @WeaklyConnectedComponent V ⟨Q⟩) →
      ExcessIntervalFlow (lo.restrictComponent C) (hi.restrictComponent C)
        (fun x ↦ a x.1) (fun x ↦ b x.1)) where
  toFun f C := f.restrictComponent C
  invFun f := ⟨(Assignment.componentEquiv Q K).symm (fun C ↦ (f C).val),
    ⟨(Assignment.mem_Icc_iff_forall_restrictComponent _ lo hi).2 (by
        intro C
        simpa using (f C).mem_Icc),
      ⟨fun x ↦ by
        rw [Assignment.excessAt_componentEquiv_symm]
        exact (f (@WeaklyConnectedComponent.mk V ⟨Q⟩ x)).excessAt_mem_Icc.1 ⟨x, rfl⟩,
      fun x ↦ by
        rw [Assignment.excessAt_componentEquiv_symm]
        exact (f (@WeaklyConnectedComponent.mk V ⟨Q⟩ x)).excessAt_mem_Icc.2 ⟨x, rfl⟩⟩⟩⟩
  left_inv f := by
    apply Subtype.ext
    simpa only [restrictComponent_val, ← Assignment.componentEquiv_apply] using
      (Assignment.componentEquiv Q K).symm_apply_apply f.val
  right_inv f := by
    funext C
    apply Subtype.ext
    simpa only [restrictComponent_val, Assignment.componentEquiv_apply] using
      congrFun ((Assignment.componentEquiv Q K).apply_symm_apply (fun C ↦ (f C).val)) C

/-- The equivalence sends an interval-excess assignment to its component restrictions. -/
@[simp]
theorem componentEquiv_apply (f : ExcessIntervalFlow lo hi a b) :
    componentEquiv lo hi a b f = fun C ↦ f.restrictComponent C :=
  (rfl)

/-- The inverse interval-excess equivalence assembles the underlying arrow assignments. -/
@[simp]
theorem componentEquiv_symm_val
    (f : (C : @WeaklyConnectedComponent V ⟨Q⟩) →
      ExcessIntervalFlow (lo.restrictComponent C) (hi.restrictComponent C)
        (fun x ↦ a x.1) (fun x ↦ b x.1)) :
    ((componentEquiv lo hi a b).symm f).val =
      (Assignment.componentEquiv Q K).symm (fun C ↦ (f C).val) :=
  (rfl)

/-- Interval-excess feasibility is equivalent to feasibility on every weak component, with no
assumption that either interval endpoint is itself a feasible excess. -/
theorem nonempty_iff_forall_component :
    Nonempty (ExcessIntervalFlow lo hi a b) ↔ ∀ C : @WeaklyConnectedComponent V ⟨Q⟩,
      Nonempty (ExcessIntervalFlow (lo.restrictComponent C) (hi.restrictComponent C)
        (fun x ↦ a x.1) (fun x ↦ b x.1)) := by
  rw [(componentEquiv lo hi a b).nonempty_congr]
  exact Classical.nonempty_pi

end ExcessIntervalFlow

end Bounded

end TauCeti
