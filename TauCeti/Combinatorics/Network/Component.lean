/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Shift
public import TauCeti.Combinatorics.Quiver.Reachable

/-!
# Restricting bounded assignments to weak components

An arrow family restricts to any one of its weakly connected components by taking the vertices
whose component class is fixed and retaining the original arrows between them. Every original
arrow incident to such a vertex stays inside the component. Consequently, restricting an arrow
assignment preserves its excess at each retained vertex.

This gives component restrictions of prescribed- and interval-excess assignments, preserving all
arrow and vertex bounds. In particular, prescribed excess sums to zero on every weak component,
while interval endpoints have nonpositive and nonnegative sums there. These are the componentwise
balance conditions used when bounded assignment problems are solved component by component.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

namespace Assignment

variable (C : @_root_.Quiver.WeaklyConnectedComponent V ⟨Q⟩)

/-- Restrict an assignment to the arrows within a weakly connected component. -/
def restrictComponent (f : Assignment Q K) : Assignment (Quiver.ComponentHom Q C) K :=
  fun _ _ e ↦ f e

@[simp]
theorem restrictComponent_apply (f : Assignment Q K) {x y : Quiver.ComponentVertex Q C}
    (e : Q x.1 y.1) : f.restrictComponent C e = f e :=
  (rfl)

variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K]

/-- Restricting an assignment to a weakly connected component preserves excess at every vertex
of that component. -/
@[simp]
theorem excessAt_restrictComponent (f : Assignment Q K) (x : Quiver.ComponentVertex Q C) :
    excessAt (f.restrictComponent C) x = excessAt f x.1 := by
  classical
  have hin : (∑ y : Quiver.ComponentVertex Q C, ∑ e : Q y.1 x.1, f e) =
      ∑ y : V, ∑ e : Q y x.1, f e := by
    calc
      _ = ∑ a : Σ y : Quiver.ComponentVertex Q C, Q y.1 x.1, f a.2 :=
        (Fintype.sum_sigma' fun (y : Quiver.ComponentVertex Q C) (e : Q y.1 x.1) ↦
          f e).symm
      _ = ∑ a : Σ y : V, Q y x.1, f a.2 :=
        by
          have h (a : Σ y : Quiver.ComponentVertex Q C, Q y.1 x.1) :
              f (Quiver.componentIncomingEquiv C x a).2 = f a.2 := by
            rw [Quiver.componentIncomingEquiv_apply]
          simpa only [h] using
            (Quiver.componentIncomingEquiv C x).sum_comp fun a ↦ f a.2
      _ = _ := Fintype.sum_sigma' fun y e ↦ f (x := y) (y := x.1) e
  have hout : (∑ y : Quiver.ComponentVertex Q C, ∑ e : Q x.1 y.1, f e) =
      ∑ y : V, ∑ e : Q x.1 y, f e := by
    calc
      _ = ∑ a : Σ y : Quiver.ComponentVertex Q C, Q x.1 y.1, f a.2 :=
        (Fintype.sum_sigma' fun (y : Quiver.ComponentVertex Q C) (e : Q x.1 y.1) ↦
          f e).symm
      _ = ∑ a : Σ y : V, Q x.1 y, f a.2 :=
        by
          have h (a : Σ y : Quiver.ComponentVertex Q C, Q x.1 y.1) :
              f (Quiver.componentOutgoingEquiv C x a).2 = f a.2 := by
            rw [Quiver.componentOutgoingEquiv_apply]
          simpa only [h] using
            (Quiver.componentOutgoingEquiv C x).sum_comp fun a ↦ f a.2
      _ = _ := Fintype.sum_sigma' fun y e ↦ f (x := x.1) (y := y) e
  simp only [excessAt_def, restrictComponent_apply]
  rw [hin, hout]

end Assignment

section Bounded

variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K] [Preorder K]
variable {lo hi : Assignment Q K} {a b d : V → K}
variable (C : @_root_.Quiver.WeaklyConnectedComponent V ⟨Q⟩)

namespace ExcessFlow

/-- Restrict a prescribed-excess assignment to one weakly connected component. -/
def restrictComponent (f : ExcessFlow lo hi d) :
    ExcessFlow (lo.restrictComponent C) (hi.restrictComponent C)
      (fun x ↦ d x.1) :=
  ⟨f.val.restrictComponent C,
    ⟨⟨fun x y e ↦ f.mem_Icc.1 x.1 y.1 e, fun x y e ↦ f.mem_Icc.2 x.1 y.1 e⟩,
      funext fun x ↦ by simp [f.excessAt_eq]⟩⟩

@[simp]
theorem restrictComponent_apply (f : ExcessFlow lo hi d)
    {x y : Quiver.ComponentVertex Q C} (e : Q x.1 y.1) :
    (f.restrictComponent C).val e = f.val e :=
  (rfl)

end ExcessFlow

namespace ExcessIntervalFlow

/-- Restrict an interval-excess assignment to one weakly connected component. -/
def restrictComponent (f : ExcessIntervalFlow lo hi a b) :
    ExcessIntervalFlow (lo.restrictComponent C) (hi.restrictComponent C)
      (fun x ↦ a x.1) (fun x ↦ b x.1) :=
  ⟨f.val.restrictComponent C,
    ⟨⟨fun x y e ↦ f.mem_Icc.1 x.1 y.1 e, fun x y e ↦ f.mem_Icc.2 x.1 y.1 e⟩,
      ⟨fun x ↦ by simpa using f.excessAt_mem_Icc.1 x.1,
        fun x ↦ by simpa using f.excessAt_mem_Icc.2 x.1⟩⟩⟩

@[simp]
theorem restrictComponent_apply (f : ExcessIntervalFlow lo hi a b)
    {x y : Quiver.ComponentVertex Q C} (e : Q x.1 y.1) :
    (f.restrictComponent C).val e = f.val e :=
  (rfl)

@[simp]
theorem excessAt_restrictComponent (f : ExcessIntervalFlow lo hi a b)
    (x : Quiver.ComponentVertex Q C) :
    excessAt (f.restrictComponent C).val x = excessAt f.val x.1 :=
  Assignment.excessAt_restrictComponent C f.val x

end ExcessIntervalFlow

end Bounded

section Balance

variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K]
variable {lo hi : Assignment Q K} {a b d : V → K}
variable (C : @_root_.Quiver.WeaklyConnectedComponent V ⟨Q⟩)

namespace ExcessFlow

/-- Prescribed excess sums to zero on each weakly connected component. -/
theorem sum_component_eq_zero [Preorder K] (f : ExcessFlow lo hi d) :
    ∑ x : Quiver.ComponentVertex Q C, d x.1 = 0 :=
  (f.restrictComponent C).sum_eq_zero

end ExcessFlow

namespace ExcessIntervalFlow

/-- The lower excess bounds sum to a nonpositive value on each weakly connected component. -/
theorem sum_component_lower_le_zero [PartialOrder K] [IsOrderedAddMonoid K]
    (f : ExcessIntervalFlow lo hi a b) :
    ∑ x : Quiver.ComponentVertex Q C, a x.1 ≤ 0 :=
  (f.restrictComponent C).sum_le_zero

/-- The upper excess bounds sum to a nonnegative value on each weakly connected component. -/
theorem zero_le_sum_component_upper [PartialOrder K] [IsOrderedAddMonoid K]
    (f : ExcessIntervalFlow lo hi a b) :
    0 ≤ ∑ x : Quiver.ComponentVertex Q C, b x.1 :=
  (f.restrictComponent C).zero_le_sum

end ExcessIntervalFlow

end Balance


end TauCeti
