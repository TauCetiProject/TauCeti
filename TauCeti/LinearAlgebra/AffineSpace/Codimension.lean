/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Dimension bounds for intersections of affine subspaces

Affine subspaces with equal-dimensional but different directions have an
intersection of strictly smaller direction dimension. In particular, distinct
hyperplane directions give intersections of codimension at least two. The
statements include empty intersections and require no topology or ordering of
the scalar division ring. An affine subspace cannot contain the image of an
affine map whose linear image has larger dimension; only the subspace direction
needs to be finite-dimensional.

A nonzero functional vanishing on a codimension-one set has its affine
direction as kernel, by Mathlib's `Module.Dual.finrank_ker_add_one_of_ne_zero`.

## Main results

* `AffineSubspace.finrank_direction_inf_add_one_lt`: two codimension-one affine subspaces with
  different directions meet in codimension at least two.
* `AffineSubspace.finrank_direction_inf_lt_of_eq_of_ne`: intersecting equal-dimensional affine
  subspaces with different directions lowers the direction dimension.
* `AffineSubspace.comap_ne_top_of_finrank_lt`: an affine subspace of smaller dimension cannot
  contain the image of an affine map.
* `AffineMap.direction_affineSpan_eq_ker_linear`: a nonconstant affine functional vanishing on a
  codimension-one set has the direction of its affine span as linear kernel.

These supply the dimension count behind the singular support in the ScatteringDiagrams roadmap,
§1.2 (generic paths): intersections of walls whose affine spans have different directions have
codimension at least two.

## Attribution

Adapted from `Mei/Geometry/Affine/Codimension.lean` in Mei at commit
`68536122a97fed8e87bc6870b9427151971b9ab2`. Original copyright and author credit are retained.

Source: https://github.com/yuma-mizuno-lean/Mei/blob/68536122a97fed8e87bc6870b9427151971b9ab2/Mei/Geometry/Affine/Codimension.lean
-/

public section

namespace LinearMap

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- A nonzero functional vanishing on a codimension-one set has its direction as kernel. -/
theorem ker_eq_direction_affineSpan (f : V →ₗ[K] K) (hf : f ≠ 0) {P : Set V}
    (hP : ∀ x ∈ P, f x = 0)
    (hdim : Module.finrank K (affineSpan K P).direction + 1 = Module.finrank K V) :
    f.ker = (affineSpan K P).direction := by
  have hle : (affineSpan K P).direction ≤ f.ker := by
    have ha : affineSpan K P ≤ f.ker.toAffineSubspace :=
      affineSpan_le.mpr fun x hx => LinearMap.mem_ker.mpr (hP x hx)
    simpa using AffineSubspace.direction_le ha
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

end LinearMap

namespace AffineMap

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The linear part of a nonconstant affine functional cuts out the direction
of any codimension-one set on which the functional vanishes. -/
theorem direction_affineSpan_eq_ker_linear [FiniteDimensional K V]
    (g : V →ᵃ[K] K) (hg : g.linear ≠ 0) {P : Set V}
    (hP : ∀ x ∈ P, g x = 0)
    (hdim : Module.finrank K (affineSpan K P).direction + 1 = Module.finrank K V) :
    (affineSpan K P).direction = g.linear.ker := by
  have hle : (affineSpan K P).direction ≤ g.linear.ker := by
    rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
    rintro v ⟨a, ha, b, hb, rfl⟩
    exact LinearMap.mem_ker.mpr (by rw [g.linear_apply_vsub, hP a ha, hP b hb, vsub_self])
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hg
  exact Submodule.eq_of_le_of_finrank_eq hle (by omega)

/-- An affine zero section has strictly smaller affine span when the function
is nonzero somewhere on the original set. No convexity is needed. -/
theorem affineSpan_inter_zero_lt (g : V →ᵃ[K] K) {P : Set V}
    (hg : ∃ p ∈ P, g p ≠ 0) :
    affineSpan K {x ∈ P | g x = 0} < affineSpan K P := by
  refine lt_of_le_of_ne (affineSpan_mono K (fun _ hx => hx.1)) ?_
  intro heq
  obtain ⟨p, hp, hgp⟩ := hg
  have hz : Set.EqOn g (0 : V →ᵃ[K] K) {x ∈ P | g x = 0} := fun _ hx => hx.2
  have hp' : p ∈ affineSpan K {x ∈ P | g x = 0} := by
    rw [heq]
    exact subset_affineSpan K P hp
  exact hgp (AffineMap.eqOn_affineSpan hz hp')

/-- A nonempty affine zero section has strictly smaller direction dimension
when the defining function is nonzero somewhere on the original set. -/
theorem finrank_direction_inter_zero_lt [FiniteDimensional K V]
    (g : V →ᵃ[K] K) {P : Set V} (hne : {x ∈ P | g x = 0}.Nonempty)
    (hg : ∃ p ∈ P, g p ≠ 0) :
    Module.finrank K (affineSpan K {x ∈ P | g x = 0}).direction <
      Module.finrank K (affineSpan K P).direction :=
  Submodule.finrank_lt_finrank_of_lt
    (AffineSubspace.direction_lt_of_nonempty (g.affineSpan_inter_zero_lt hg)
      (hne.affineSpan K))

end AffineMap

namespace AffineSubspace

section Comap

variable {k V W P Q : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddTorsor V P] [AddTorsor W Q]

/-- An affine subspace of dimension smaller than the image of an affine map
cannot contain that image. -/
theorem comap_ne_top_of_finrank_lt (S : AffineSubspace k Q) [FiniteDimensional k S.direction]
    (f : P →ᵃ[k] Q)
    (hS : Module.finrank k S.direction < Module.finrank k (LinearMap.range f.linear)) :
    S.comap f ≠ ⊤ := by
  intro he
  have hle := direction_le (map_comap_le f S)
  rw [he, map_direction, direction_top, Submodule.map_top] at hle
  exact (not_le_of_gt hS) (Submodule.finrank_mono hle)

end Comap

section

open scoped Affine

variable {K V P : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [AffineSpace V P]

/-- An affine subspace whose direction has codimension one is proper. -/
theorem ne_top_of_finrank_direction_add_one_eq (A : AffineSubspace K P)
    (hdim : Module.finrank K A.direction + 1 = Module.finrank K V) : A ≠ ⊤ := by
  intro heq
  rw [heq, direction_top, finrank_top] at hdim
  omega

end

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Intersecting equal-dimensional affine subspaces with different directions
strictly lowers the direction dimension, including for an empty intersection. -/
theorem finrank_direction_inf_lt_of_eq_of_ne (A B : AffineSubspace K V)
    (hdim : Module.finrank K A.direction = Module.finrank K B.direction)
    (hne : A.direction ≠ B.direction) :
    Module.finrank K (A ⊓ B).direction < Module.finrank K A.direction := by
  have hlt : A.direction ⊓ B.direction < A.direction := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    have hle : A.direction ≤ B.direction := by rw [← heq]; exact inf_le_right
    exact hne (Submodule.eq_of_le_of_finrank_eq hle hdim)
  have hle : (A ⊓ B).direction ≤ A.direction ⊓ B.direction :=
    A.direction_inf B
  exact (Submodule.finrank_mono hle).trans_lt (Submodule.finrank_lt_finrank_of_lt hlt)

/-- The intersection of two codimension-one affine subspaces with different
directions has codimension at least two. No nonemptiness hypothesis is needed. -/
theorem finrank_direction_inf_add_one_lt (A B : AffineSubspace K V)
    (hA : Module.finrank K A.direction + 1 = Module.finrank K V)
    (hB : Module.finrank K B.direction + 1 = Module.finrank K V)
    (hne : A.direction ≠ B.direction) :
    Module.finrank K (A ⊓ B).direction + 1 < Module.finrank K V := by
  have heq : Module.finrank K A.direction = Module.finrank K B.direction :=
    Nat.add_right_cancel (hA.trans hB.symm)
  rw [← hA]
  exact Nat.add_lt_add_right (A.finrank_direction_inf_lt_of_eq_of_ne B heq hne) 1

end AffineSubspace
