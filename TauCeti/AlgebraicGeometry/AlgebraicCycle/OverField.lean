/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicCycle.Basic
public import TauCeti.AlgebraicGeometry.Scheme.LocalDimension
import TauCeti.AlgebraicGeometry.ResidueDegree

/-!
# Pushforward of algebraic cycles over a field

Let `k` be a field and `f : X ⟶ Y` a quasi-compact morphism of schemes locally of finite type over
`k`, over `Spec k`. Mathlib's pushforward of algebraic cycles `AlgebraicCycle.map f height height`
sends the cycle `[V]` of an integral closed subscheme `V ⊆ X` to `[κ(V) : κ(f(V))] [f(V)]` when
`f(V)` has the dimension of `V`, and to `0` otherwise. Over a field the dimension condition is
automatic: when `κ(V)` is finite over `κ(f(V))`, both have the same transcendence degree over `k`
(`TauCeti.AlgebraicGeometry.height_apply_eq_height_of_residueDegree_ne_zero`), so the
multiplicity is just the residue degree. This makes the pushforward functorial and compatible with
degrees ([Stacks, Sections 42.12 and 42.41](https://stacks.math.columbia.edu/tag/02R3); Fulton,
*Intersection Theory*, §1.4).

* `AlgebraicCycle.mapCoeff_height_eq_residueDegree` and `AlgebraicCycle.map_height_apply`: the
  multiplicities of the pushforward with height weights are the residue degrees.
* `AlgebraicCycle.map_height_comp`: the pushforward with height weights is functorial.
* `AlgebraicCycle.degree_eq_map_height_apply` and `AlgebraicCycle.degree_map_height`: on
  quasi-compact schemes, Mathlib's degree along the structure morphism is the pushforward to
  `Spec k`, and it is preserved by pushforward.
-/

public section

open AlgebraicGeometry Order CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicCycle

open TauCeti.AlgebraicGeometry

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of k))] {R : Type*} [Semiring R]

/-- Over a field, the multiplicity of Mathlib's pushforward of cycles with height weights is the
residue degree: a point with finite residue extension has the dimension of its image. -/
lemma mapCoeff_height_eq_residueDegree (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (x : X) :
    mapCoeff f height height x = f.residueDegree x := by
  rw [mapCoeff]
  split_ifs with h
  · rfl
  · by_contra hx
    exact h (height_apply_eq_height_of_residueDegree_ne_zero k f (Ne.symm hx)).symm

/-- Over a field, Mathlib's pushforward of cycles with height weights has, at a point `y`, the sum
of the coefficients at the points `x` over `y`, weighted by the residue degrees `[κ(x) : κ(y)]`. -/
lemma map_height_apply (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [QuasiCompact f]
    (α : AlgebraicCycle X R) (y : Y) :
    map f height height α y = ∑ᶠ x ∈ f ⁻¹' {y}, α x * (f.residueDegree x : R) := by
  simp only [map, Function.locallyFinsupp.map_apply, mapCoeff_height_eq_residueDegree k]

/-- Over a field, Mathlib's pushforward of cycles with height weights is functorial:
`(g ∘ f)_* = g_* f_*`, by the tower law for residue degrees. -/
lemma map_height_comp (f : X ⟶ Y) (g : Y ⟶ Z) [f.IsOver (Spec (.of k))]
    [g.IsOver (Spec (.of k))] [QuasiCompact f] [QuasiCompact g] (α : AlgebraicCycle X R) :
    map (f ≫ g) height height α = map g height height (map f height height α) :=
  map_comp f height height g height α fun x ↦ by
    simp only [mapCoeff_height_eq_residueDegree k, Scheme.Hom.residueDegree_comp]

section Degree

variable [CompactSpace X]

/-- The degree of a cycle on a quasi-compact scheme over `k` is the coefficient of its
pushforward to `Spec k`. -/
lemma degree_eq_map_height_apply (α : AlgebraicCycle X R) :
    degree (X ↘ Spec (.of k)) α = map (X ↘ Spec (.of k)) height height α default :=
  degree_eq_map_of_unique _ _ _ _ fun _ _ hx ↦
    (height_apply_eq_height_of_residueDegree_ne_zero k (X ↘ Spec (.of k)) hx).symm

/-- Pushforward along a morphism over `k` of quasi-compact schemes preserves the degree of
cycles. -/
lemma degree_map_height [CompactSpace Y] (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [QuasiCompact f]
    (α : AlgebraicCycle X R) :
    degree (Y ↘ Spec (.of k)) (map f height height α) = degree (X ↘ Spec (.of k)) α := by
  rw [degree_eq_map_height_apply, degree_eq_map_height_apply, ← map_height_comp k]
  simp only [comp_over]

end Degree

end AlgebraicGeometry.AlgebraicCycle
