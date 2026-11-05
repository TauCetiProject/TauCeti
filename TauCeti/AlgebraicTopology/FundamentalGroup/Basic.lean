/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Basic results on fundamental groupoids and fundamental groups

This file records a basic connectedness result for fundamental groupoids, the general
transport facts about the basepoint-adjusted induced map `FundamentalGroup.mapOfEq`, and when a
map induced on fundamental groups is trivial: a characterization of trivial range loop by loop,
and the basic consequences of triviality of the *source* fundamental group.

`TauCeti.FundamentalGroup.map_range_eq_bot_iff` was extracted from the proof of
`semilocallySimplyConnectedAt_iff_range_eq_bot` in
`TauCeti/AlgebraicTopology/SemilocallySimplyConnected/On.lean`, which is adapted from the Mathlib
drafts [#31449](https://github.com/leanprover-community/mathlib4/pull/31449),
[#31576](https://github.com/leanprover-community/mathlib4/pull/31576), and
[#38292](https://github.com/leanprover-community/mathlib4/pull/38292) by Kim Morrison.

## Main declarations

* `FundamentalGroup.map_id`: the identity induces the identity homomorphism.
* `FundamentalGroup.map_comp`: induced maps preserve composition.
* `FundamentalGroup.fromPath_mk_out`: every element of the fundamental group is the class of a
  chosen representative loop.
* `FundamentalGroup.mapOfEq_comp`: the induced map of a composite is the composite of the
  induced maps.
* `FundamentalGroup.mapOfEq_rfl`: along the reflexivity proof, `mapOfEq` is `map`.
* `FundamentalGroup.mapOfEq_id`: the identity map induces the identity under `mapOfEq`.
* `FundamentalGroup.mapOfEq_congr`: `mapOfEq` depends only on the underlying continuous map.
* `FundamentalGroup.mapOfEq_fromPath_eq_one_iff`: the induced map kills the class of a loop
  exactly when the image of the loop is nullhomotopic.
* `FundamentalGroup.mapOfEq_mapOfEq_of_comp_eq_id`: the induced map of a map whose composite
  with `f` is the identity undoes the induced map of `f`.
* `FundamentalGroupoid.nonempty_hom`: the fundamental groupoid of a path-connected
  space is connected.
* `TauCeti.FundamentalGroup.map_range_eq_bot_iff`: the induced map has trivial range exactly
  when every loop at the basepoint becomes nullhomotopic in the target.
* `TauCeti.FundamentalGroup.map_range_eq_bot_of_subsingleton`: if the source fundamental group
  is subsingleton, the range of any induced map from it is trivial.
* `TauCeti.FundamentalGroup.map_range_le_of_subsingleton`: if the source fundamental group is
  subsingleton, any induced-map range lies in any target subgroup.
* `TauCeti.FundamentalGroup.map_range_le_of_simplyConnectedSpace`: a simply connected domain has
  induced-map range contained in any target subgroup.
* `TauCeti.FundamentalGroup.mapOfEq_range_eq_bot_of_subsingleton`: the same triviality for the
  basepoint-transported induced map `FundamentalGroup.mapOfEq`.
-/

public section

open CategoryTheory

namespace FundamentalGroupoid

/-- In the fundamental groupoid of a path-connected space every object receives a morphism from
every other one, so the groupoid is connected. -/
theorem nonempty_hom {Y : Type*} [TopologicalSpace Y]
    [PathConnectedSpace Y] (x y : FundamentalGroupoid Y) : Nonempty (x ⟶ y) :=
  ⟨Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x.as y.as)⟩

end FundamentalGroupoid

namespace FundamentalGroup

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {x : X} {y : Y} {z : Z}

/-- The identity map induces the identity homomorphism on fundamental groups. -/
@[simp]
theorem map_id {X : Type*} [TopologicalSpace X] (x : X) :
    map (ContinuousMap.id X) x = MonoidHom.id _ := by
  ext ⟨p⟩ : 1
  -- Mapping a representative path by the identity preserves the path and its endpoints.
  induction p using Path.Homotopic.Quotient.ind
  rfl

/-- The map on fundamental groups induced by a composite is the composite of the induced maps. -/
@[simp]
theorem map_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (g : C(Y, Z)) (f : C(X, Y)) (x : X) :
    map (g.comp f) x = (map g (f x)).comp (map f x) :=
  MonoidHom.ext fun p ↦ End.ext (FundamentalGroupoid.map_comp_map g f p.asHom)

/-- Every element of the fundamental group is the class of a chosen representative loop. -/
@[simp]
theorem fromPath_mk_out {X : Type*} [TopologicalSpace X] {x : X} (g : FundamentalGroup X x) :
    fromPath (Path.Homotopic.Quotient.mk (Quotient.out (toPath g))) = g :=
  congrArg End.of (Quotient.out_eq _)

/-- The maps induced on fundamental groups by two continuous maps compose to the map induced by
their composite: `mapOfEq g hg (mapOfEq f hf p) = mapOfEq (g.comp f) _ p`. -/
theorem mapOfEq_comp (g : C(Y, Z)) (f : C(X, Y)) (hf : f x = y) (hg : g y = z)
    (p : FundamentalGroup X x) :
    FundamentalGroup.mapOfEq g hg (FundamentalGroup.mapOfEq f hf p) =
      -- `mapOfEq` takes the basepoint equality as an explicit parameter, so the `show` must
      -- spell out the composite equality `(g.comp f) x = z`, which `hf` and `hg` state only
      -- after routing through the intermediate basepoint `y`.
      FundamentalGroup.mapOfEq (g.comp f)
        (show (g.comp f) x = z by rw [ContinuousMap.comp_apply, hf, hg]) p := by
  simp only [FundamentalGroup.mapOfEq_apply]
  rw [Path.Homotopic.Quotient.map_cast, Path.Homotopic.Quotient.cast_cast,
    ← Path.Homotopic.Quotient.map_comp]

/-- Transporting the target basepoint along the reflexivity proof does nothing: `mapOfEq f rfl`
is Mathlib's `FundamentalGroup.map f x`.

This is the comparison needed whenever a statement phrased with a general basepoint equation
`f x = y` is applied to a lifting criterion phrased at the basepoint `f x` itself. -/
@[simp]
theorem mapOfEq_rfl (f : C(X, Y)) :
    FundamentalGroup.mapOfEq f (rfl : f x = f x) = FundamentalGroup.map f x := by
  ext γ
  rw [FundamentalGroup.mapOfEq_apply]
  exact Path.Homotopic.Quotient.cast_rfl_rfl _

/-- The map induced on fundamental groups by the identity continuous map is the identity. -/
@[simp]
theorem mapOfEq_id (h : (ContinuousMap.id X) x = x) (p : FundamentalGroup X x) :
    FundamentalGroup.mapOfEq (ContinuousMap.id X) h p = p := by
  have h1 : FundamentalGroup.mapOfEq (ContinuousMap.id X) h p =
      FundamentalGroup.mapOfEq (ContinuousMap.id X)
        (rfl : (ContinuousMap.id X) x = (ContinuousMap.id X) x) p := by
    rfl
  have h2 : FundamentalGroup.mapOfEq (ContinuousMap.id X)
      (rfl : (ContinuousMap.id X) x = (ContinuousMap.id X) x) p = p := by
    rw [mapOfEq_rfl (f := ContinuousMap.id X), map_id]
    rfl
  exact h1.trans h2

/-- The induced map `mapOfEq` depends only on the underlying continuous map, not on the chosen
proof of the basepoint equation: two equal continuous maps induce the same map. -/
theorem mapOfEq_congr {f₁ f₂ : C(X, Y)} (hfe : f₁ = f₂) (h₁ : f₁ x = y) (h₂ : f₂ x = y)
    (p : FundamentalGroup X x) :
    FundamentalGroup.mapOfEq f₁ h₁ p = FundamentalGroup.mapOfEq f₂ h₂ p := by
  subst hfe
  rfl

/-- **A loop is killed exactly when its image is nullhomotopic.** The induced map `mapOfEq f h`
sends the class of a loop `q` to `1` if and only if the image of `q` under `f` is homotopic,
relative to its endpoints, to the constant path. -/
theorem mapOfEq_fromPath_eq_one_iff (f : C(X, Y)) (h : f x = y) (q : Path x x) :
    FundamentalGroup.mapOfEq f h
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)) = 1 ↔
      (q.map f.continuous).Homotopic (Path.refl (f x)) := by
  subst h
  rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl,
    FundamentalGroup.one_def, ← Path.Homotopic.Quotient.mk_map]
  exact ⟨fun h => Quotient.exact (congrArg CategoryTheory.End.asHom h),
    fun h => congrArg CategoryTheory.End.of (Quotient.sound h)⟩

/-- If `g ∘ f` is the identity, then the induced map of `g` undoes the induced map of `f`. -/
theorem mapOfEq_mapOfEq_of_comp_eq_id (g : C(Y, X)) (f : C(X, Y)) (hf : f x = y) (hg : g y = x)
    (hgf : g.comp f = ContinuousMap.id X) (p : FundamentalGroup X x) :
    FundamentalGroup.mapOfEq g hg (FundamentalGroup.mapOfEq f hf p) = p := by
  rw [mapOfEq_comp g f hf hg]
  exact (mapOfEq_congr hgf _ rfl p).trans (mapOfEq_id rfl p)


end FundamentalGroup

namespace TauCeti

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
variable {A : Type*} [TopologicalSpace A]

/-- Mapping a loop class represented by a path is represented by mapping that path. -/
theorem FundamentalGroup.map_fromPath {Y : Type*} [TopologicalSpace Y] (f : C(X, Y)) (base : X)
    (q : Path base base) :
    _root_.FundamentalGroup.map f base
        (_root_.FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)) =
      _root_.FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (q.map f.continuous)) := by
  simp only [← Path.Homotopic.Quotient.mk''_eq_mk]
  rfl

/-- **The induced map is trivial exactly loop by loop.** The map on fundamental groups induced by
`f` has trivial range if and only if every loop at the basepoint becomes nullhomotopic after
applying `f`. -/
theorem FundamentalGroup.map_range_eq_bot_iff {Y : Type*} [TopologicalSpace Y] (f : C(X, Y))
    (base : X) :
    (_root_.FundamentalGroup.map f base).range = ⊥ ↔
      ∀ γ : Path base base, (γ.map f.continuous).Homotopic (Path.refl (f base)) := by
  rw [MonoidHom.range_eq_bot_iff]
  constructor
  · intro h γ
    have h_map : _root_.FundamentalGroup.fromPath ⟦γ.map f.continuous⟧ =
        _root_.FundamentalGroup.fromPath ⟦Path.refl (f base)⟧ := by
      simp only [Path.Homotopic.Quotient.mk''_eq_mk]
      rw [← FundamentalGroup.map_fromPath f base γ, h]
      simp only [MonoidHom.one_apply, _root_.FundamentalGroup.one_def,
        Path.Homotopic.Quotient.mk_refl]
    exact (FundamentalGroupoid.fromPath_eq_iff_homotopic _ _).mp (congrArg End.asHom h_map)
  · intro h
    ext ⟨p⟩ : 1
    obtain ⟨γ, rfl⟩ := Quotient.exists_rep p
    have hnull : _root_.FundamentalGroup.fromPath ⟦γ.map f.continuous⟧ =
        _root_.FundamentalGroup.fromPath ⟦Path.refl (f base)⟧ :=
      congrArg End.of ((FundamentalGroupoid.fromPath_eq_iff_homotopic _ _).mpr (h γ))
    simp only [Path.Homotopic.Quotient.mk''_eq_mk] at hnull ⊢
    rw [FundamentalGroup.map_fromPath f base γ, hnull]
    simp only [MonoidHom.one_apply, _root_.FundamentalGroup.one_def,
      Path.Homotopic.Quotient.mk_refl]

/-- If the source fundamental group is subsingleton, the range of any induced map from it is
trivial. -/
@[simp]
theorem FundamentalGroup.map_range_eq_bot_of_subsingleton
    [Subsingleton (_root_.FundamentalGroup A a₀)] (f : C(A, X)) :
    (_root_.FundamentalGroup.map f a₀).range = ⊥ := by
  have : Subsingleton ((_root_.FundamentalGroup.map f a₀).range) :=
    (Set.subsingleton_coe _).mpr ((_root_.FundamentalGroup.map f a₀).subsingleton_coe_range)
  exact Subgroup.eq_bot_of_subsingleton _

/-- A simply connected domain has trivial induced fundamental-group range. -/
theorem FundamentalGroup.map_range_eq_bot_of_simplyConnectedSpace [SimplyConnectedSpace A]
    (f : C(A, X)) (a₀ : A) : (_root_.FundamentalGroup.map f a₀).range = ⊥ :=
  FundamentalGroup.map_range_eq_bot_of_subsingleton f

/-- If the source fundamental group is subsingleton, its induced-map range lies in any target
subgroup. -/
theorem FundamentalGroup.map_range_le_of_subsingleton
    [Subsingleton (_root_.FundamentalGroup A a₀)] (f : C(A, X))
    (H : Subgroup (_root_.FundamentalGroup X (f a₀))) :
    (_root_.FundamentalGroup.map f a₀).range ≤ H := by
  rw [FundamentalGroup.map_range_eq_bot_of_subsingleton f]
  exact bot_le

/-- If the source fundamental group is subsingleton, the range of the induced map transported to
a prescribed target basepoint is trivial. -/
@[simp]
theorem FundamentalGroup.mapOfEq_range_eq_bot_of_subsingleton
    [Subsingleton (_root_.FundamentalGroup A a₀)] (f : C(A, X)) {x : X} (h : f a₀ = x) :
    (_root_.FundamentalGroup.mapOfEq f h).range = ⊥ := by
  have : Subsingleton ((_root_.FundamentalGroup.mapOfEq f h).range) :=
    (Set.subsingleton_coe _).mpr ((_root_.FundamentalGroup.mapOfEq f h).subsingleton_coe_range)
  exact Subgroup.eq_bot_of_subsingleton _

/-- A simply connected domain has induced fundamental-group range contained in any target
subgroup. -/
theorem FundamentalGroup.map_range_le_of_simplyConnectedSpace [SimplyConnectedSpace A]
    (f : C(A, X)) (a₀ : A) (H : Subgroup (_root_.FundamentalGroup X (f a₀))) :
    (_root_.FundamentalGroup.map f a₀).range ≤ H :=
  FundamentalGroup.map_range_le_of_subsingleton f H

end TauCeti
