/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.UnitInterval

/-!
# The unreduced suspension of a space

The unreduced suspension `SX` of a topological space `X` is the quotient of the cylinder `X × I`
collapsing the end `X × {0}` to one point and the end `X × {1}` to another. Geometrically it is
two cones on `X` glued along their bases, and for the unit sphere `Sⁿ` it is `Sⁿ⁺¹`
(`TauCeti.sphereUnreducedSuspensionHomeomorph`).

It differs from the reduced suspension `TauCeti.ReducedSuspension`, which also collapses the
segment through the base point. The unreduced suspension needs no base point, which is why it is
the target of the Hopf construction (`TauCeti.Join.hopfConstruction`): a map `X × Y → Z` gives
`[x, y, t] ↦ [μ (x, y), t]` from the join `X * Y` to `SZ`, with no condition relating `μ` to base
points.

Being a quotient of `X × I`, the unreduced suspension of the empty space is empty in this model,
whereas it is often taken to be the two-point space `S⁰`. The two agree whenever `X` is nonempty.

## Main declarations

* `TauCeti.UnreducedSuspension`: the unreduced suspension, with the quotient map
  `TauCeti.UnreducedSuspension.mk`, its fibres `TauCeti.UnreducedSuspension.mk_eq_mk_iff` and the
  presentation `TauCeti.UnreducedSuspension.isQuotientMap_mk`.
* `TauCeti.UnreducedSuspension.lift`: the universal property, for maps out of `X × I` that are
  constant on each of the two ends, with `TauCeti.UnreducedSuspension.hom_ext`.
* `TauCeti.UnreducedSuspension.map`: functoriality.
* The unreduced suspension of a compact space is compact.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, *Operations on Spaces*, the suspension `SX`.
-/

public section

noncomputable section

namespace TauCeti

open Topology unitInterval

universe u w

variable {X : Type u}

variable (X) in
/-- The normal form of a point of `X × I` for the unreduced suspension: the `X` coordinate is
forgotten at the two ends. Two points have the same normal form exactly when the unreduced
suspension identifies them, which is how the unreduced suspension is defined below. -/
private def unreducedSuspensionNormalize (p : X × I) : Option X × I :=
  (if p.2 = 0 ∨ p.2 = 1 then none else some p.1, p.2)

private lemma unreducedSuspensionNormalize_eq_iff {x x' : X} {s t : I} :
    unreducedSuspensionNormalize X (x, s) = unreducedSuspensionNormalize X (x', t) ↔
      s = t ∧ (s ≠ 0 → s ≠ 1 → x = x') := by
  simp only [unreducedSuspensionNormalize, Prod.mk.injEq]
  constructor
  · rintro ⟨hx, rfl⟩
    exact ⟨rfl, fun h₀ h₁ => by simpa [h₀, h₁] using hx⟩
  · rintro ⟨rfl, hx⟩
    refine ⟨?_, rfl⟩
    by_cases h : s = 0 ∨ s = 1
    · simp [h]
    · simp only [not_or] at h
      simp [h, hx h.1 h.2]

variable (X) in
/-- The **unreduced suspension** `SX` of a topological space: the quotient of `X × I`
identifying `(x, 0)` with `(x', 0)` and `(x, 1)` with `(x', 1)`, with the quotient topology.

The presentation as a quotient is private to this file and is not part of the public interface:
points of the suspension come from `TauCeti.UnreducedSuspension.mk`, which points it identifies
from `TauCeti.UnreducedSuspension.mk_eq_mk_iff`, maps out of it from
`TauCeti.UnreducedSuspension.lift`, equalities of such maps from
`TauCeti.UnreducedSuspension.hom_ext`, and statements about all of its points from
`TauCeti.UnreducedSuspension.induction`. -/
def UnreducedSuspension : Type u :=
  Quotient (Setoid.ker (unreducedSuspensionNormalize X))

namespace UnreducedSuspension

variable [TopologicalSpace X]

/-! The topology is transported from the private quotient; the instance is `@[no_expose]`, which
is what lets its body name the private constant. -/

@[no_expose] instance : TopologicalSpace (UnreducedSuspension X) :=
  inferInstanceAs (TopologicalSpace (Quotient (Setoid.ker (unreducedSuspensionNormalize X))))

variable (X) in
/-- The point `[x, t]` of the unreduced suspension represented by `(x, t) : X × I`. -/
def mk : C(X × I, UnreducedSuspension X) :=
  ⟨Quotient.mk _, continuous_quot_mk⟩

/-- Two points of `X × I` have the same image in the unreduced suspension exactly when they have
the same time `t`, and the same `X` coordinate unless `t` is an end of the interval. -/
@[simp]
theorem mk_eq_mk_iff {x x' : X} {s t : I} :
    mk X (x, s) = mk X (x', t) ↔ s = t ∧ (s ≠ 0 → s ≠ 1 → x = x') :=
  (Quotient.eq (r := Setoid.ker (unreducedSuspensionNormalize X))).trans
    unreducedSuspensionNormalize_eq_iff

/-- At time `0` the point `[x, 0]` does not depend on `x`. -/
theorem mk_zero_eq (x x' : X) : mk X (x, 0) = mk X (x', 0) := by
  simp

/-- At time `1` the point `[x, 1]` does not depend on `x`. -/
theorem mk_one_eq (x x' : X) : mk X (x, 1) = mk X (x', 1) := by
  simp

/-- **The unreduced suspension is a quotient of `X × I`.** -/
theorem isQuotientMap_mk : IsQuotientMap (mk X) :=
  isQuotientMap_quot_mk

theorem mk_surjective : Function.Surjective (mk X) :=
  isQuotientMap_mk.surjective

/-- Every point of the unreduced suspension is of the form `[x, t]`. -/
@[elab_as_elim]
protected theorem induction {motive : UnreducedSuspension X → Prop}
    (h : ∀ p : X × I, motive (mk X p)) (z : UnreducedSuspension X) : motive z :=
  Quotient.ind h z

/-- Two maps out of the unreduced suspension agree as soon as they agree on every point
`[x, t]`. -/
@[ext]
theorem hom_ext {W : Type w} [TopologicalSpace W] {f g : C(UnreducedSuspension X, W)}
    (h : ∀ p, f (mk X p) = g (mk X p)) : f = g :=
  ContinuousMap.ext (UnreducedSuspension.induction h)

instance [CompactSpace X] : CompactSpace (UnreducedSuspension X) :=
  mk_surjective.compactSpace (mk X).continuous

section Lift

variable {W : Type w} [TopologicalSpace W]

/-- **The universal property of the unreduced suspension.** A map out of `X × I` which is
constant on `X × {0}` and on `X × {1}` descends to the unreduced suspension. -/
def lift (g : C(X × I, W)) (h₀ : ∀ x x', g (x, 0) = g (x', 0))
    (h₁ : ∀ x x', g (x, 1) = g (x', 1)) : C(UnreducedSuspension X, W) :=
  ⟨Quotient.lift g fun ⟨x, s⟩ ⟨x', t⟩ hab => by
      obtain ⟨rfl, hx⟩ := unreducedSuspensionNormalize_eq_iff.1 hab
      by_cases hs₀ : s = 0
      · subst hs₀
        exact h₀ x x'
      by_cases hs₁ : s = 1
      · subst hs₁
        exact h₁ x x'
      rw [hx hs₀ hs₁],
    Continuous.quotient_lift g.continuous _⟩

@[simp]
theorem lift_mk (g : C(X × I, W)) (h₀ : ∀ x x', g (x, 0) = g (x', 0))
    (h₁ : ∀ x x', g (x, 1) = g (x', 1)) (p : X × I) :
    lift g h₀ h₁ (mk X p) = g p := (rfl)

@[simp]
theorem lift_comp_mk (g : C(X × I, W)) (h₀ : ∀ x x', g (x, 0) = g (x', 0))
    (h₁ : ∀ x x', g (x, 1) = g (x', 1)) :
    (lift g h₀ h₁).comp (mk X) = g := (rfl)

end Lift

section Map

variable {Y : Type*} [TopologicalSpace Y] {Z : Type*} [TopologicalSpace Z]

/-- The map of unreduced suspensions induced by a map of spaces, `[x, t] ↦ [f x, t]`. -/
def map (f : C(X, Y)) : C(UnreducedSuspension X, UnreducedSuspension Y) :=
  lift ((mk Y).comp (f.prodMap (ContinuousMap.id I)))
    (fun x x' => mk_zero_eq (f x) (f x')) (fun x x' => mk_one_eq (f x) (f x'))

@[simp]
theorem map_mk (f : C(X, Y)) (x : X) (t : I) :
    map f (mk X (x, t)) = mk Y (f x, t) := (rfl)

@[simp]
theorem map_id : map (ContinuousMap.id X) = ContinuousMap.id (UnreducedSuspension X) :=
  hom_ext fun _ => rfl

theorem map_comp (g : C(Y, Z)) (f : C(X, Y)) : map (g.comp f) = (map g).comp (map f) :=
  hom_ext fun _ => rfl

end Map

end UnreducedSuspension

end TauCeti
