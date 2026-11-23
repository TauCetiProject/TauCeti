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
theorem componentEquiv_apply (f : Assignment Q K) (C : @WeaklyConnectedComponent V ⟨Q⟩) :
    componentEquiv Q K f C = f.restrictComponent C :=
  (rfl)

/-- Restriction to all components preserves the zero assignment. -/
@[simp]
theorem componentEquiv_zero [Zero K] :
    componentEquiv Q K (0 : Assignment Q K) = 0 := by
  funext C
  exact restrictComponent_zero C

/-- Restriction to all components preserves pointwise addition. -/
@[simp]
theorem componentEquiv_add [Add K] (f g : Assignment Q K) :
    componentEquiv Q K (f + g) = componentEquiv Q K f + componentEquiv Q K g := by
  funext C
  exact restrictComponent_add C f g

/-- Restriction to all components preserves pointwise negation. -/
@[simp]
theorem componentEquiv_neg [Neg K] (f : Assignment Q K) :
    componentEquiv Q K (-f) = -componentEquiv Q K f := by
  funext C
  exact restrictComponent_neg C f

/-- Restriction to all components preserves pointwise subtraction. -/
@[simp]
theorem componentEquiv_sub [Sub K] (f g : Assignment Q K) :
    componentEquiv Q K (f - g) = componentEquiv Q K f - componentEquiv Q K g := by
  funext C
  exact restrictComponent_sub C f g

/-- Assembly evaluates an arrow in the component of its source. -/
@[simp]
theorem componentEquiv_symm_apply
    (f : (C : @WeaklyConnectedComponent V ⟨Q⟩) → Assignment (Quiver.ComponentHom Q C) K)
    {x y : V} (e : Q x y) :
    (componentEquiv Q K).symm f e = f (@WeaklyConnectedComponent.mk V ⟨Q⟩ x)
      (x := ⟨x, rfl⟩) (y := ⟨y, (Quiver.weaklyConnectedComponent_mk_eq_of_hom e).symm⟩) e :=
  (rfl)

/-- Assembling all restrictions recovers the original assignment. -/
@[simp]
theorem componentEquiv_symm_restrictComponent (f : Assignment Q K) :
    (componentEquiv Q K).symm (fun C ↦ f.restrictComponent C) = f :=
  (componentEquiv Q K).symm_apply_apply f

/-- Assembling zero assignments gives the zero assignment. -/
@[simp]
theorem componentEquiv_symm_zero [Zero K] :
    (componentEquiv Q K).symm 0 = (0 : Assignment Q K) := by
  funext x y e
  simp

/-- Assembly preserves pointwise addition. -/
@[simp]
theorem componentEquiv_symm_add [Add K]
    (f g : (C : @WeaklyConnectedComponent V ⟨Q⟩) → Assignment (Quiver.ComponentHom Q C) K) :
    (componentEquiv Q K).symm (f + g) =
      (componentEquiv Q K).symm f + (componentEquiv Q K).symm g :=
  (rfl)

/-- Assembly preserves pointwise negation. -/
@[simp]
theorem componentEquiv_symm_neg [Neg K]
    (f : (C : @WeaklyConnectedComponent V ⟨Q⟩) → Assignment (Quiver.ComponentHom Q C) K) :
    (componentEquiv Q K).symm (-f) = -(componentEquiv Q K).symm f :=
  (rfl)

/-- Assembly preserves pointwise subtraction. -/
@[simp]
theorem componentEquiv_symm_sub [Sub K]
    (f g : (C : @WeaklyConnectedComponent V ⟨Q⟩) → Assignment (Quiver.ComponentHom Q C) K) :
    (componentEquiv Q K).symm (f - g) =
      (componentEquiv Q K).symm f - (componentEquiv Q K).symm g :=
  (rfl)

/-- Restricting an assembled assignment recovers the supplied component assignment. -/
@[simp high]
theorem restrictComponent_componentEquiv_symm
    (f : (C : @WeaklyConnectedComponent V ⟨Q⟩) → Assignment (Quiver.ComponentHom Q C) K)
    (C : @WeaklyConnectedComponent V ⟨Q⟩) :
    ((componentEquiv Q K).symm f).restrictComponent C = f C := by
  simpa only [componentEquiv_apply] using
    congrFun ((componentEquiv Q K).apply_symm_apply f) C

/-- Assembly evaluates an arrow in any specified component containing both endpoints. -/
theorem componentEquiv_symm_apply_of_mk_eq
    (f : (C : @WeaklyConnectedComponent V ⟨Q⟩) → Assignment (Quiver.ComponentHom Q C) K)
    {C : @WeaklyConnectedComponent V ⟨Q⟩} {x y : V}
    (hx : @WeaklyConnectedComponent.mk V ⟨Q⟩ x = C)
    (hy : @WeaklyConnectedComponent.mk V ⟨Q⟩ y = C) (e : Q x y) :
    (componentEquiv Q K).symm f e = f C (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) e := by
  simpa only [restrictComponent_apply] using
    congrArg (fun g : Assignment (Quiver.ComponentHom Q C) K ↦
      g (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) e) (restrictComponent_componentEquiv_symm f C)

/-- Arrowwise inequalities hold globally exactly when they hold on every component. -/
theorem le_iff_forall_restrictComponent [LE K] (f g : Assignment Q K) :
    f ≤ g ↔ ∀ C, f.restrictComponent C ≤ g.restrictComponent C := by
  constructor
  · intro h C x y e
    simpa using h x.val y.val e
  · intro h x y e
    simpa using h (@WeaklyConnectedComponent.mk V ⟨Q⟩ x)
      ⟨x, rfl⟩ ⟨y, (Quiver.weaklyConnectedComponent_mk_eq_of_hom e).symm⟩ e

/-- Arrowwise bounds hold globally exactly when they hold on every component. -/
theorem mem_Icc_iff_forall_restrictComponent [Preorder K] (f lo hi : Assignment Q K) :
    f ∈ Set.Icc lo hi ↔ ∀ C, f.restrictComponent C ∈
      Set.Icc (lo.restrictComponent C) (hi.restrictComponent C) := by
  simp only [Set.mem_Icc]
  rw [le_iff_forall_restrictComponent lo f, le_iff_forall_restrictComponent f hi, ← forall_and]

/-- An assignment lies below an assembly exactly when each restriction lies below its part. -/
@[simp]
theorem le_componentEquiv_symm_iff [LE K] (g : Assignment Q K)
    (f : (C : @WeaklyConnectedComponent V ⟨Q⟩) → Assignment (Quiver.ComponentHom Q C) K) :
    g ≤ (componentEquiv Q K).symm f ↔ ∀ C, g.restrictComponent C ≤ f C := by
  rw [le_iff_forall_restrictComponent]
  simp only [restrictComponent_componentEquiv_symm]

/-- An assembly lies below an assignment exactly when each part lies below its restriction. -/
@[simp]
theorem componentEquiv_symm_le_iff [LE K]
    (f : (C : @WeaklyConnectedComponent V ⟨Q⟩) → Assignment (Quiver.ComponentHom Q C) K)
    (g : Assignment Q K) :
    (componentEquiv Q K).symm f ≤ g ↔ ∀ C, f C ≤ g.restrictComponent C := by
  rw [le_iff_forall_restrictComponent]
  simp only [restrictComponent_componentEquiv_symm]

/-- An assembly satisfies arrow bounds exactly when every supplied part satisfies them. -/
theorem componentEquiv_symm_mem_Icc_iff [Preorder K]
    (f : (C : @WeaklyConnectedComponent V ⟨Q⟩) → Assignment (Quiver.ComponentHom Q C) K)
    (lo hi : Assignment Q K) :
    (componentEquiv Q K).symm f ∈ Set.Icc lo hi ↔
      ∀ C, f C ∈ Set.Icc (lo.restrictComponent C) (hi.restrictComponent C) := by
  simp only [Set.mem_Icc, le_componentEquiv_symm_iff, componentEquiv_symm_le_iff, forall_and]

variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K]

/-- Assembly preserves excess at a vertex in any specified component containing it. -/
theorem excessAt_componentEquiv_symm_of_mk_eq
    (f : (C : @WeaklyConnectedComponent V ⟨Q⟩) → Assignment (Quiver.ComponentHom Q C) K)
    {C : @WeaklyConnectedComponent V ⟨Q⟩} {x : V}
    (hx : @WeaklyConnectedComponent.mk V ⟨Q⟩ x = C) :
    excessAt ((componentEquiv Q K).symm f) x = excessAt (f C) ⟨x, hx⟩ := by
  simpa only [restrictComponent_componentEquiv_symm] using
    (excessAt_restrictComponent C ((componentEquiv Q K).symm f) ⟨x, hx⟩).symm

/-- The excess of an assembled assignment is the excess computed in its vertex's component. -/
@[simp]
theorem excessAt_componentEquiv_symm
    (f : (C : @WeaklyConnectedComponent V ⟨Q⟩) → Assignment (Quiver.ComponentHom Q C) K)
    (x : V) :
    excessAt ((componentEquiv Q K).symm f) x =
      excessAt (f (@WeaklyConnectedComponent.mk V ⟨Q⟩ x)) ⟨x, rfl⟩ :=
  excessAt_componentEquiv_symm_of_mk_eq f rfl

/-- An assignment is a circulation exactly when each component restriction is a circulation. -/
theorem isCirculation_iff_forall_restrictComponent (f : Assignment Q K) :
    IsCirculation f ↔ ∀ C, IsCirculation (f.restrictComponent C) := by
  constructor
  · exact fun hf C ↦ hf.restrictComponent C
  · intro h
    rw [isCirculation_iff]
    intro x
    simpa using (isCirculation_iff _).1 (h (@WeaklyConnectedComponent.mk V ⟨Q⟩ x)) ⟨x, rfl⟩

/-- Assembly is a circulation exactly when every supplied component assignment is a circulation. -/
@[simp]
theorem isCirculation_componentEquiv_symm_iff
    (f : (C : @WeaklyConnectedComponent V ⟨Q⟩) → Assignment (Quiver.ComponentHom Q C) K) :
    IsCirculation ((componentEquiv Q K).symm f) ↔ ∀ C, IsCirculation (f C) := by
  rw [isCirculation_iff_forall_restrictComponent]
  simp only [restrictComponent_componentEquiv_symm]

end Assignment

section Bounded

variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K] [Preorder K]
variable (lo hi : Assignment Q K) (d a b : V → K)

namespace ExcessFlow

/-- A prescribed-excess assignment is exactly a choice of a prescribed-excess assignment on each
weak component, with inherited arrow bounds and prescribed excess. -/
def componentEquiv : ExcessFlow lo hi d ≃
    ((C : @WeaklyConnectedComponent V ⟨Q⟩) →
      ExcessFlow (lo.restrictComponent C) (hi.restrictComponent C) (fun x ↦ d x.val)) :=
  ((Assignment.componentEquiv Q K).subtypeEquiv (fun f ↦ by
    simp only [Assignment.componentEquiv_apply, forall_and]
    rw [Assignment.mem_Icc_iff_forall_restrictComponent]
    apply and_congr_right
    intro _
    simp only [funext_iff]
    constructor
    · intro h C x
      simpa only [Assignment.excessAt_restrictComponent] using h x.val
    · intro h x
      simpa only [Assignment.excessAt_restrictComponent] using
        h (@WeaklyConnectedComponent.mk V ⟨Q⟩ x) ⟨x, rfl⟩)).trans Equiv.subtypePiEquivPi

/-- The equivalence sends a feasible assignment to its component restrictions. -/
@[simp]
theorem componentEquiv_apply (f : ExcessFlow lo hi d)
    (C : @WeaklyConnectedComponent V ⟨Q⟩) :
    componentEquiv lo hi d f C = f.restrictComponent C := by
  apply Subtype.ext
  simp [componentEquiv, Equiv.subtypePiEquivPi, restrictComponent_val]

/-- The inverse equivalence assembles the component arrow assignments without changing values. -/
@[simp]
theorem componentEquiv_symm_apply_val
    (f : (C : @WeaklyConnectedComponent V ⟨Q⟩) →
      ExcessFlow (lo.restrictComponent C) (hi.restrictComponent C) (fun x ↦ d x.val)) :
    ((componentEquiv lo hi d).symm f).val =
      (Assignment.componentEquiv Q K).symm (fun C ↦ (f C).val) :=
  (rfl)

/-- Assembling all restrictions recovers the original prescribed-excess assignment. -/
@[simp]
theorem componentEquiv_symm_restrictComponent (f : ExcessFlow lo hi d) :
    (componentEquiv lo hi d).symm (fun C ↦ f.restrictComponent C) = f := by
  simpa only [← componentEquiv_apply] using (componentEquiv lo hi d).symm_apply_apply f

/-- Restricting an assembly recovers the supplied prescribed-excess component assignment. -/
@[simp]
theorem restrictComponent_componentEquiv_symm
    (f : (C : @WeaklyConnectedComponent V ⟨Q⟩) →
      ExcessFlow (lo.restrictComponent C) (hi.restrictComponent C) (fun x ↦ d x.val))
    (C : @WeaklyConnectedComponent V ⟨Q⟩) :
    ((componentEquiv lo hi d).symm f).restrictComponent C = f C := by
  simpa only [componentEquiv_apply] using
    congrFun ((componentEquiv lo hi d).apply_symm_apply f) C

/-- Prescribed-excess feasibility is equivalent to feasibility on every weak component. The
component conditions retain all bounds, not just the necessary balance of prescribed excess. -/
theorem nonempty_iff_forall_component :
    Nonempty (ExcessFlow lo hi d) ↔ ∀ C : @WeaklyConnectedComponent V ⟨Q⟩,
      Nonempty (ExcessFlow (lo.restrictComponent C) (hi.restrictComponent C) (fun x ↦ d x.val))
          := by
  rw [(componentEquiv lo hi d).nonempty_congr]
  exact Classical.nonempty_pi

end ExcessFlow

namespace ExcessIntervalFlow

/-- An interval-excess assignment is exactly a choice of such an assignment on each weak
component, retaining both arrow bounds and both vertex-excess bounds. -/
def componentEquiv : ExcessIntervalFlow lo hi a b ≃
    ((C : @WeaklyConnectedComponent V ⟨Q⟩) →
      ExcessIntervalFlow (lo.restrictComponent C) (hi.restrictComponent C)
        (fun x ↦ a x.val) (fun x ↦ b x.val)) :=
  ((Assignment.componentEquiv Q K).subtypeEquiv (fun f ↦ by
    simp only [Assignment.componentEquiv_apply, forall_and]
    rw [Assignment.mem_Icc_iff_forall_restrictComponent]
    apply and_congr_right
    intro _
    simp only [Set.mem_Icc, Pi.le_def, ← forall_and]
    constructor
    · intro h C x
      simpa only [Assignment.excessAt_restrictComponent] using h x.val
    · intro h x
      simpa only [Assignment.excessAt_restrictComponent] using
        h (@WeaklyConnectedComponent.mk V ⟨Q⟩ x) ⟨x, rfl⟩)).trans Equiv.subtypePiEquivPi

/-- The equivalence sends an interval-excess assignment to its component restrictions. -/
@[simp]
theorem componentEquiv_apply (f : ExcessIntervalFlow lo hi a b)
    (C : @WeaklyConnectedComponent V ⟨Q⟩) :
    componentEquiv lo hi a b f C = f.restrictComponent C := by
  apply Subtype.ext
  simp [componentEquiv, Equiv.subtypePiEquivPi, restrictComponent_val]

/-- The inverse interval-excess equivalence assembles the underlying arrow assignments. -/
@[simp]
theorem componentEquiv_symm_apply_val
    (f : (C : @WeaklyConnectedComponent V ⟨Q⟩) →
      ExcessIntervalFlow (lo.restrictComponent C) (hi.restrictComponent C)
        (fun x ↦ a x.val) (fun x ↦ b x.val)) :
    ((componentEquiv lo hi a b).symm f).val =
      (Assignment.componentEquiv Q K).symm (fun C ↦ (f C).val) :=
  (rfl)

/-- Assembling all restrictions recovers the original interval-excess assignment. -/
@[simp]
theorem componentEquiv_symm_restrictComponent (f : ExcessIntervalFlow lo hi a b) :
    (componentEquiv lo hi a b).symm (fun C ↦ f.restrictComponent C) = f := by
  simpa only [← componentEquiv_apply] using (componentEquiv lo hi a b).symm_apply_apply f

/-- Restricting an assembly recovers the supplied interval-excess component assignment. -/
@[simp]
theorem restrictComponent_componentEquiv_symm
    (f : (C : @WeaklyConnectedComponent V ⟨Q⟩) →
      ExcessIntervalFlow (lo.restrictComponent C) (hi.restrictComponent C)
        (fun x ↦ a x.val) (fun x ↦ b x.val))
    (C : @WeaklyConnectedComponent V ⟨Q⟩) :
    ((componentEquiv lo hi a b).symm f).restrictComponent C = f C := by
  simpa only [componentEquiv_apply] using
    congrFun ((componentEquiv lo hi a b).apply_symm_apply f) C

/-- Interval-excess feasibility is equivalent to feasibility on every weak component, with no
assumption that either interval endpoint is itself a feasible excess. -/
theorem nonempty_iff_forall_component :
    Nonempty (ExcessIntervalFlow lo hi a b) ↔ ∀ C : @WeaklyConnectedComponent V ⟨Q⟩,
      Nonempty (ExcessIntervalFlow (lo.restrictComponent C) (hi.restrictComponent C)
        (fun x ↦ a x.val) (fun x ↦ b x.val)) := by
  rw [(componentEquiv lo hi a b).nonempty_congr]
  exact Classical.nonempty_pi

end ExcessIntervalFlow

end Bounded

end TauCeti
