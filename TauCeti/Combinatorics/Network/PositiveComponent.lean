/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Walk
public import TauCeti.Combinatorics.Quiver.StronglyConnectedComponent

/-!
# Strongly connected components of the positive-capacity arrows

For capacities `c` on an arrow family `Q`, the arrows of positive capacity form a quiver
`TauCeti.PositiveHom c` on the same vertices, whose paths witness exactly positive reachability
`TauCeti.PositiveReachable c`. Its strongly connected components, Mathlib's
`Quiver.StronglyConnectedComponent` for this explicit quiver, are the classes of mutual positive
reachability, partially ordered by positive reachability.

Given vertices `s` and `t`, the components reachable from the component of `s` and those reaching
the component of `t` are disjoint as soon as `t` is not positively reachable from `s`. The
remaining components are the *free* components between `s` and `t`. For the residual capacities
of a maximum flow, they parametrize the minimum cuts: the minimum cuts correspond to the upper
sets of free components.

## Main definitions

* `TauCeti.PositiveHom c`: the arrows of positive capacity for `c`.
* `TauCeti.PositiveComponent c`: the strongly connected components of the arrows of positive
  capacity, partially ordered by positive reachability.
* `TauCeti.PositiveComponent.Free c s t`: the components neither reachable from the component of
  `s` nor reaching the component of `t`.

## Main results

* `TauCeti.nonempty_arrowWalk_positiveHom_iff`: walks along arrows of positive capacity witness
  positive reachability.
* `TauCeti.PositiveComponent.mk_le_mk` and `TauCeti.PositiveComponent.mk_eq_mk`: the order and the
  equality of components, by positive reachability.
* `TauCeti.PositiveComponent.not_le_mk_of_mk_le`: if `t` is not positively reachable from `s`, no
  component is both above the component of `s` and below the component of `t`.
* `TauCeti.PositiveComponent.isEmpty_free_iff`: there is no free component exactly when every
  vertex is positively reachable from `s` or positively reaches `t`.
-/

public section

namespace TauCeti

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w} [Zero K] [LT K]

/-- The arrows of positive capacity for the capacities `c`. -/
abbrev PositiveHom (c : Assignment Q K) (x y : V) : Type v :=
  {e : Q x y // 0 < c e}

variable {c : Assignment Q K}

/-- Walks along arrows of positive capacity witness exactly positive reachability. -/
theorem nonempty_arrowWalk_positiveHom_iff {s t : V} :
    Nonempty (ArrowWalk (PositiveHom c) s t) ↔ PositiveReachable c s t := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact .refl c s
    | cons _ e ih => exact ih.tail e.1 e.2
  · intro h
    rw [positiveReachable_iff_reflTransGen] at h
    induction h with
    | refl => exact ⟨.nil s⟩
    | tail _ he ih => exact ⟨ih.some.cons ⟨he.choose, he.choose_spec⟩⟩

variable (c) in
/-- The *positive components* for the capacities `c`: the strongly connected components of the
quiver of arrows of positive capacity, that is, the classes of mutual positive reachability. They
are partially ordered by positive reachability. -/
@[expose] def PositiveComponent : Type u :=
  @Quiver.StronglyConnectedComponent V ⟨PositiveHom c⟩

namespace PositiveComponent

variable (c) in
/-- The positive component of a vertex. -/
def mk (v : V) : PositiveComponent c :=
  @Quiver.StronglyConnectedComponent.mk V ⟨PositiveHom c⟩ v

/-- Positive components are ordered by positive reachability of their vertices. -/
instance : PartialOrder (PositiveComponent c) :=
  @Quiver.StronglyConnectedComponent.instPartialOrder V ⟨PositiveHom c⟩

instance [Finite V] : Finite (PositiveComponent c) :=
  @Quiver.StronglyConnectedComponent.instFinite V ⟨PositiveHom c⟩ _

theorem mk_surjective : Function.Surjective (mk c) :=
  @Quiver.StronglyConnectedComponent.mk_surjective V ⟨PositiveHom c⟩

/-- Induction on positive components: a property of positive components holds for all of them
when it holds for the positive component of every vertex. -/
@[elab_as_elim]
protected theorem ind {β : PositiveComponent c → Prop} (h : ∀ v, β (mk c v))
    (C : PositiveComponent c) : β C :=
  @Quiver.StronglyConnectedComponent.ind V ⟨PositiveHom c⟩ β h C

/-- The positive component of `v` lies below that of `w` exactly when `w` is positively reachable
from `v`. -/
@[simp]
theorem mk_le_mk {v w : V} : mk c v ≤ mk c w ↔ PositiveReachable c v w :=
  (@Quiver.StronglyConnectedComponent.mk_le_mk V ⟨PositiveHom c⟩ v w).trans
    nonempty_arrowWalk_positiveHom_iff

/-- Two vertices have the same positive component exactly when each is positively reachable from
the other. -/
@[simp]
theorem mk_eq_mk {v w : V} :
    mk c v = mk c w ↔ PositiveReachable c v w ∧ PositiveReachable c w v := by
  rw [le_antisymm_iff, mk_le_mk, mk_le_mk]

variable (c) in
/-- The *free* positive components between `s` and `t`: those not above the positive component of
`s` and not below the positive component of `t`. That is, their vertices are not positively
reachable from `s`, and `t` is not positively reachable from them. -/
abbrev Free (s t : V) : Type u :=
  {C : PositiveComponent c // ¬mk c s ≤ C ∧ ¬C ≤ mk c t}

/-- If `t` is not positively reachable from `s`, then no positive component lies both above the
positive component of `s` and below that of `t`. -/
theorem not_le_mk_of_mk_le {s t : V} (hst : ¬PositiveReachable c s t) {C : PositiveComponent c}
    (hs : mk c s ≤ C) : ¬C ≤ mk c t :=
  fun ht ↦ hst (mk_le_mk.1 (hs.trans ht))

/-- There is no free positive component between `s` and `t` exactly when every vertex is
positively reachable from `s` or positively reaches `t`. -/
theorem isEmpty_free_iff {s t : V} :
    IsEmpty (Free c s t) ↔ ∀ v, PositiveReachable c s v ∨ PositiveReachable c v t := by
  rw [isEmpty_subtype]
  refine ⟨fun h v ↦ ?_, fun h C ↦ ?_⟩
  · by_contra! hv
    exact h (mk c v) ⟨mt mk_le_mk.1 hv.1, mt mk_le_mk.1 hv.2⟩
  · induction C using PositiveComponent.ind with
    | h v => exact fun ⟨hs, ht⟩ ↦ (h v).elim (hs ∘ mk_le_mk.2) (ht ∘ mk_le_mk.2)

end PositiveComponent

end TauCeti
