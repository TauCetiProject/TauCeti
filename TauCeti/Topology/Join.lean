/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.UnitInterval

/-!
# The join of two topological spaces

The join `X * Y` of two spaces is the space of formal segments from a point of `X` to a point of
`Y`: it is the quotient of `X × Y × I` in which the triple `(x, y, t)` is identified with
`(x, y', 0)` for every `y'` when `t = 0`, and with `(x', y, 1)` for every `x'` when `t = 1`.
So the end `t = 0` is a copy of `X`, the end `t = 1` is a copy of `Y`, and every point of `X` is
joined to every point of `Y` by a segment. It carries the quotient topology.

The join is the source of the Hopf construction: a map `μ : X × Y → Z` gives a map
`X * Y → ΣZ` to the unreduced suspension by `[x, y, t] ↦ [μ (x, y), t]`. For unit spheres the
join of `Sⁿ` and `Sᵐ` is `Sⁿ⁺ᵐ⁺¹` (`TauCeti.sphereJoinHomeomorph` in
`TauCeti.Geometry.Sphere.Join`).

This file gives the join the interface of a quotient: the points `TauCeti.Join.mk x y t`, the
characterization of when two of them are equal, the quotient map from `X × Y × I`, the descent of
continuous maps constant on the collapsed ends (`TauCeti.Join.lift`) with its uniqueness, and
compactness of the join of compact spaces.

## Main definitions

* `TauCeti.Join X Y`: the join of `X` and `Y`.
* `TauCeti.Join.mk x y t`: the point at time `t` of the segment from `x` to `y`.
* `TauCeti.Join.lift`: a continuous map out of `X × Y × I` that does not depend on the point of `Y`
  at `t = 0` nor on the point of `X` at `t = 1` descends to the join.

## Main results

* `TauCeti.Join.mk_eq_mk_iff`: `[x, y, t] = [x', y', t']` exactly when `t = t'`, `x = x'` unless
  `t = 1`, and `y = y'` unless `t = 0`.
* `TauCeti.Join.isQuotientMap_mk`: the join carries the quotient topology of `X × Y × I`.
* `TauCeti.Join.continuousMap_ext`: continuous maps out of the join agreeing on all points
  `[x, y, t]` are equal.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0, p. 9.
-/

public section

open unitInterval Topology

namespace TauCeti

variable (X Y : Type*)

/-- The equivalence relation on `X × Y × I` whose quotient is the join: two triples are related
when they have the same time `t`, the same point of `X` unless `t = 1`, and the same point of `Y`
unless `t = 0`. -/
def joinSetoid : Setoid (X × Y × I) where
  r p q := p.2.2 = q.2.2 ∧ (p.2.2 ≠ 1 → p.1 = q.1) ∧ (p.2.2 ≠ 0 → p.2.1 = q.2.1)
  iseqv :=
    { refl _ := ⟨rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩
      symm := fun ⟨h, hx, hy⟩ ↦
        ⟨h.symm, fun ht ↦ (hx (h ▸ ht)).symm, fun ht ↦ (hy (h ▸ ht)).symm⟩
      trans := fun ⟨h, hx, hy⟩ ⟨h', hx', hy'⟩ ↦
        ⟨h.trans h', fun ht ↦ (hx ht).trans (hx' (h ▸ ht)),
          fun ht ↦ (hy ht).trans (hy' (h ▸ ht))⟩ }

/-- The join `X * Y` of two spaces: the quotient of `X × Y × I` collapsing `X × Y × {0}` onto `X`
and `X × Y × {1}` onto `Y`, with the quotient topology. -/
def Join : Type _ :=
  Quotient (joinSetoid X Y)

namespace Join

variable {X Y}

instance [TopologicalSpace X] [TopologicalSpace Y] : TopologicalSpace (Join X Y) :=
  inferInstanceAs (TopologicalSpace (Quotient (joinSetoid X Y)))

/-- The point `[x, y, t]` of the join: the point at time `t` of the segment from `x` to `y`. -/
def mk (x : X) (y : Y) (t : I) : Join X Y :=
  Quotient.mk _ (x, y, t)

/-- Two points `[x, y, t]` and `[x', y', t']` of the join are equal exactly when `t = t'`,
`x = x'` unless `t = 1`, and `y = y'` unless `t = 0`. -/
theorem mk_eq_mk_iff {x x' : X} {y y' : Y} {t t' : I} :
    mk x y t = mk x' y' t' ↔ t = t' ∧ (t ≠ 1 → x = x') ∧ (t ≠ 0 → y = y') :=
  Quotient.eq

/-- At time `0` the point of the join does not depend on the point of `Y`. -/
theorem mk_zero (x : X) (y y' : Y) : mk x y 0 = mk x y' 0 :=
  mk_eq_mk_iff.2 ⟨rfl, fun _ ↦ rfl, fun h ↦ absurd rfl h⟩

/-- At time `1` the point of the join does not depend on the point of `X`. -/
theorem mk_one (x x' : X) (y : Y) : mk x y 1 = mk x' y 1 :=
  mk_eq_mk_iff.2 ⟨rfl, fun h ↦ absurd rfl h, fun _ ↦ rfl⟩

/-- Every point of the join is of the form `[x, y, t]`. -/
@[elab_as_elim]
theorem ind {motive : Join X Y → Prop} (h : ∀ x y t, motive (mk x y t)) (z : Join X Y) :
    motive z :=
  Quotient.ind (fun p ↦ h p.1 p.2.1 p.2.2) z

/-- Every point of the join is of the form `[x, y, t]`. -/
theorem exists_mk_eq (z : Join X Y) : ∃ x y t, mk x y t = z :=
  ind (fun x y t ↦ ⟨x, y, t, rfl⟩) z

variable [TopologicalSpace X] [TopologicalSpace Y]

/-- The join carries the quotient topology of `X × Y × I`. -/
theorem isQuotientMap_mk : IsQuotientMap fun p : X × Y × I ↦ mk p.1 p.2.1 p.2.2 :=
  isQuotientMap_quot_mk

/-- The map `(x, y, t) ↦ [x, y, t]` is continuous. -/
@[fun_prop]
theorem continuous_mk : Continuous fun p : X × Y × I ↦ mk p.1 p.2.1 p.2.2 :=
  continuous_quot_mk

/-- The join of compact spaces is compact. -/
instance [CompactSpace X] [CompactSpace Y] : CompactSpace (Join X Y) :=
  Quotient.compactSpace

variable {Z : Type*} [TopologicalSpace Z]

/-- A continuous map `f` out of `X × Y × I` descends to the join when `f (x, y, 0)` does not depend
on `y` and `f (x, y, 1)` does not depend on `x`. -/
def lift (f : C(X × Y × I, Z)) (h₀ : ∀ x y y', f (x, y, 0) = f (x, y', 0))
    (h₁ : ∀ x x' y, f (x, y, 1) = f (x', y, 1)) : C(Join X Y, Z) where
  toFun := Quotient.lift f fun p q ⟨ht, hx, hy⟩ ↦ by
    obtain ⟨x, y, t⟩ := p
    obtain ⟨x', y', t'⟩ := q
    dsimp only at ht hx hy
    subst ht
    by_cases h0 : t = 0
    · subst h0
      rw [hx zero_ne_one]
      exact h₀ x' y y'
    by_cases h1 : t = 1
    · subst h1
      rw [hy one_ne_zero]
      exact h₁ x x' y'
    rw [hx h1, hy h0]
  continuous_toFun := continuous_quot_lift _ f.continuous

/-- The descended map sends `[x, y, t]` to `f (x, y, t)`. -/
@[simp]
theorem lift_mk (f : C(X × Y × I, Z)) (h₀ : ∀ x y y', f (x, y, 0) = f (x, y', 0))
    (h₁ : ∀ x x' y, f (x, y, 1) = f (x', y, 1)) (x : X) (y : Y) (t : I) :
    lift f h₀ h₁ (mk x y t) = f (x, y, t) :=
  (rfl)

/-- Continuous maps out of the join that agree on every point `[x, y, t]` are equal. -/
theorem continuousMap_ext {g g' : C(Join X Y, Z)} (h : ∀ x y t, g (mk x y t) = g' (mk x y t)) :
    g = g' :=
  ContinuousMap.ext (ind h)

/-- The descended map is the only continuous map out of the join through which `f` factors. -/
theorem eq_lift_iff (f : C(X × Y × I, Z)) (h₀ : ∀ x y y', f (x, y, 0) = f (x, y', 0))
    (h₁ : ∀ x x' y, f (x, y, 1) = f (x', y, 1)) (g : C(Join X Y, Z)) :
    g = lift f h₀ h₁ ↔ ∀ x y t, g (mk x y t) = f (x, y, t) :=
  ⟨fun h x y t ↦ by rw [h, lift_mk], fun h ↦ continuousMap_ext fun x y t ↦ by rw [h, lift_mk]⟩

end Join

end TauCeti
