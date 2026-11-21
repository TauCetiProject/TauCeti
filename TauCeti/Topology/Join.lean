/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.UnitInterval

/-!
# The topological join of two spaces

The join `X * Y` of two topological spaces is the quotient of `X × Y × I` in which, at time `0`,
the point `[x, y, 0]` depends only on `x`, and at time `1`, the point `[x, y, 1]` depends only on
`y`. Geometrically it is the union of the segments `t ↦ [x, y, t]` joining each point of `X` to
each point of `Y`, with `X` at time `0` and `Y` at time `1`.

Maps out of the join are built with its universal property `TauCeti.Join.lift`. For instance the
Hopf construction of a map `μ : X × Y → Z` is `[x, y, t] ↦ [μ (x, y), t]`, from the join to the
unreduced suspension of `Z`; since the join of two spheres is a sphere
(`TauCeti.sphereJoinHomeomorph`), it turns a map `Sⁿ × Sⁿ → Sⁿ` into a map `S²ⁿ⁺¹ → Sⁿ⁺¹`.

Being a quotient of `X × Y × I`, the join with an empty space is empty in this model, whereas the
join of `∅` and `Y` is often taken to be `Y`. The two agree whenever both factors are nonempty.

## Main declarations

* `TauCeti.Join`: the join of two topological spaces, with the quotient map `TauCeti.Join.mk`,
  its fibres `TauCeti.Join.mk_eq_mk_iff` and the presentation
  `TauCeti.Join.isQuotientMap_mk`.
* `TauCeti.Join.lift`: the universal property, for maps out of `X × Y × I` that ignore `y` at
  time `0` and `x` at time `1`, with `TauCeti.Join.hom_ext`.
* `TauCeti.Join.map`: functoriality in both factors.
* The join of compact spaces is compact.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, *Operations on Spaces*, the join `X * Y`.
-/

public section

noncomputable section

namespace TauCeti

open Topology unitInterval

universe u v w

variable {X : Type u} {Y : Type v}

variable (X Y) in
/-- The normal form of a point of `X × Y × I` for the join: the `X` coordinate is forgotten at
time `1` and the `Y` coordinate at time `0`. Two points have the same normal form exactly when
the join identifies them, which is how the join is defined below. -/
private def joinNormalize (p : X × Y × I) : Option X × Option Y × I :=
  (if p.2.2 = 1 then none else some p.1, if p.2.2 = 0 then none else some p.2.1, p.2.2)

private lemma joinNormalize_eq_iff {x x' : X} {y y' : Y} {s t : I} :
    joinNormalize X Y (x, y, s) = joinNormalize X Y (x', y', t) ↔
      s = t ∧ (s ≠ 1 → x = x') ∧ (s ≠ 0 → y = y') := by
  simp only [joinNormalize, Prod.mk.injEq]
  constructor
  · rintro ⟨hx, hy, rfl⟩
    exact ⟨rfl, fun hs => by simpa [hs] using hx, fun hs => by simpa [hs] using hy⟩
  · rintro ⟨rfl, hx, hy⟩
    refine ⟨?_, ?_, rfl⟩
    · by_cases hs : s = 1 <;> simp [hs, hx]
    · by_cases hs : s = 0 <;> simp [hs, hy]

variable (X Y) in
/-- The **join** `X * Y` of two topological spaces: the quotient of `X × Y × I` identifying
`(x, y, 0)` with `(x, y', 0)` and `(x, y, 1)` with `(x', y, 1)`, with the quotient topology.

The presentation as a quotient is private to this file and is not part of the public interface:
points of the join come from `TauCeti.Join.mk`, which points it identifies from
`TauCeti.Join.mk_eq_mk_iff`, maps out of it from `TauCeti.Join.lift`, equalities of such maps
from `TauCeti.Join.hom_ext`, and statements about all of its points from `TauCeti.Join.ind`. -/
def Join : Type max u v :=
  Quotient (Setoid.ker (joinNormalize X Y))

namespace Join

variable [TopologicalSpace X] [TopologicalSpace Y]

/-! The topology is transported from the private quotient; the instance is `@[no_expose]`, which
is what lets its body name the private constant. -/

@[no_expose] instance : TopologicalSpace (Join X Y) :=
  inferInstanceAs (TopologicalSpace (Quotient (Setoid.ker (joinNormalize X Y))))

variable (X Y) in
/-- The point `[x, y, t]` of the join represented by `(x, y, t) : X × Y × I`. -/
def mk : C(X × Y × I, Join X Y) :=
  ⟨Quotient.mk _, continuous_quot_mk⟩

/-- Two points of `X × Y × I` have the same image in the join exactly when they have the same
time `t`, the same `X` coordinate unless `t = 1`, and the same `Y` coordinate unless `t = 0`. -/
@[simp]
theorem mk_eq_mk_iff {x x' : X} {y y' : Y} {s t : I} :
    mk X Y (x, y, s) = mk X Y (x', y', t) ↔ s = t ∧ (s ≠ 1 → x = x') ∧ (s ≠ 0 → y = y') :=
  (Quotient.eq (r := Setoid.ker (joinNormalize X Y))).trans joinNormalize_eq_iff

/-- At time `0` a point of the join depends only on its `X` coordinate. -/
theorem mk_zero_eq (x : X) (y y' : Y) : mk X Y (x, y, 0) = mk X Y (x, y', 0) := by
  simp

/-- At time `1` a point of the join depends only on its `Y` coordinate. -/
theorem mk_one_eq (x x' : X) (y : Y) : mk X Y (x, y, 1) = mk X Y (x', y, 1) := by
  simp

/-- **The join is a quotient of `X × Y × I`.** -/
theorem isQuotientMap_mk : IsQuotientMap (mk X Y) :=
  isQuotientMap_quot_mk

theorem mk_surjective : Function.Surjective (mk X Y) :=
  isQuotientMap_mk.surjective

/-- Every point of the join is of the form `[x, y, t]`. -/
@[elab_as_elim]
theorem ind {p : Join X Y → Prop} (h : ∀ q : X × Y × I, p (mk X Y q)) (z : Join X Y) : p z :=
  Quotient.ind h z

/-- Two maps out of the join agree as soon as they agree on every point `[x, y, t]`. -/
@[ext]
theorem hom_ext {W : Type w} [TopologicalSpace W] {f g : C(Join X Y, W)}
    (h : ∀ q, f (mk X Y q) = g (mk X Y q)) : f = g :=
  ContinuousMap.ext (ind h)

instance [CompactSpace X] [CompactSpace Y] : CompactSpace (Join X Y) :=
  mk_surjective.compactSpace (mk X Y).continuous

section Lift

variable {W : Type w} [TopologicalSpace W]

/-- **The universal property of the join.** A map out of `X × Y × I` which ignores the `Y`
coordinate at time `0` and the `X` coordinate at time `1` descends to the join. -/
def lift (g : C(X × Y × I, W)) (h₀ : ∀ x y y', g (x, y, 0) = g (x, y', 0))
    (h₁ : ∀ x x' y, g (x, y, 1) = g (x', y, 1)) : C(Join X Y, W) :=
  ⟨Quotient.lift g fun ⟨x, y, s⟩ ⟨x', y', t⟩ hab => by
      obtain ⟨rfl, hx, hy⟩ := joinNormalize_eq_iff.1 hab
      by_cases hs₀ : s = 0
      · subst hs₀
        rw [hx zero_ne_one, h₀]
      by_cases hs₁ : s = 1
      · subst hs₁
        rw [hy one_ne_zero, h₁]
      rw [hx hs₁, hy hs₀],
    Continuous.quotient_lift g.continuous _⟩

@[simp]
theorem lift_mk (g : C(X × Y × I, W)) (h₀ : ∀ x y y', g (x, y, 0) = g (x, y', 0))
    (h₁ : ∀ x x' y, g (x, y, 1) = g (x', y, 1)) (q : X × Y × I) :
    lift g h₀ h₁ (mk X Y q) = g q := (rfl)

@[simp]
theorem lift_comp_mk (g : C(X × Y × I, W)) (h₀ : ∀ x y y', g (x, y, 0) = g (x, y', 0))
    (h₁ : ∀ x x' y, g (x, y, 1) = g (x', y, 1)) :
    (lift g h₀ h₁).comp (mk X Y) = g := (rfl)

end Lift

section Map

variable {X' : Type*} [TopologicalSpace X'] {Y' : Type*} [TopologicalSpace Y']
  {X'' : Type*} [TopologicalSpace X''] {Y'' : Type*} [TopologicalSpace Y'']

/-- The map of joins induced by maps of the two factors, `[x, y, t] ↦ [f x, g y, t]`. -/
def map (f : C(X, X')) (g : C(Y, Y')) : C(Join X Y, Join X' Y') :=
  lift ((mk X' Y').comp (f.prodMap (g.prodMap (ContinuousMap.id I))))
    (fun x y y' => mk_zero_eq (f x) (g y) (g y')) (fun x x' y => mk_one_eq (f x) (f x') (g y))

@[simp]
theorem map_mk (f : C(X, X')) (g : C(Y, Y')) (x : X) (y : Y) (t : I) :
    map f g (mk X Y (x, y, t)) = mk X' Y' (f x, g y, t) := (rfl)

@[simp]
theorem map_id : map (ContinuousMap.id X) (ContinuousMap.id Y) = ContinuousMap.id (Join X Y) :=
  hom_ext fun _ => rfl

theorem map_comp (f' : C(X', X'')) (g' : C(Y', Y'')) (f : C(X, X')) (g : C(Y, Y')) :
    map (f'.comp f) (g'.comp g) = (map f' g').comp (map f g) :=
  hom_ext fun _ => rfl

end Map

end Join

end TauCeti
