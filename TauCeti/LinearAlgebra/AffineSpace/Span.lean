/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Directions of affine spans under preimages and products

Under an affine map, the direction of the affine span of an image is the linear image of the
original direction (Mathlib's `AffineMap.map_vectorSpan`). This file adds the corresponding
statements for preimages under linear surjections and for products.

For a linear surjection `A : V → V'` and a nonempty set `S ⊆ V'`, the differences of points of
`A⁻¹(S)` are exactly the preimage of the differences of points of `S`, so by Mathlib's
`Submodule.span_preimage_eq` the direction of the affine span of `A⁻¹(S)` is the preimage of the
direction of the affine span of `S`. Taking the product with a fixed nonempty set preserves and
reflects equality of affine spans, and for nonempty sets also equality of their directions.

A linear map whose kernel contains the direction of a set is constant on that set. If `f` is
constant on a nonempty set `W₁` whose affine span is a fiber of `ν`, then `ker ν ≤ ker f`.

## Main results

* `LinearMap.direction_affineSpan_preimage`: under a linear surjection, the direction of the affine
  span of the preimage of a nonempty set is the preimage of its direction.
* `TauCeti.affineSpan_prod_eq_iff`: for a nonempty `u`, `affineSpan (s ×ˢ u) = affineSpan (t ×ˢ u)`
  if and only if `affineSpan s = affineSpan t`.
* `TauCeti.direction_affineSpan_prod_eq_iff`: the same for directions, for nonempty `s`, `t`
  and `u`.
* `LinearMap.map_eq_zero_of_affineSpan_eq`: if `f` is constant on a set `W₁` containing a point
  `y`, and `affineSpan W₁ = affineSpan W₂` is a fiber of `ν`, then `ν q = 0` implies `f q = 0`.

## Attribution

Adapted from `Mei/Geometry/Affine/Span.lean` in Mei at commit
`68536122a97fed8e87bc6870b9427151971b9ab2`. Original copyright and author credit are retained.

Source: https://github.com/yuma-mizuno-lean/Mei/blob/68536122a97fed8e87bc6870b9427151971b9ab2/Mei/Geometry/Affine/Span.lean
-/

public section

namespace LinearMap

/-- A linear map whose kernel contains the direction of a set is constant on that set. -/
theorem apply_eq_of_direction_le_ker {K V W : Type*} [Ring K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) {P : Set V}
    (hf : (affineSpan K P).direction ≤ f.ker) {x y : V} (hx : x ∈ P) (hy : y ∈ P) :
    f x = f y := by
  have hd := hf (AffineSubspace.vsub_mem_direction (subset_affineSpan K P hx)
    (subset_affineSpan K P hy))
  rwa [LinearMap.mem_ker, vsub_eq_sub, map_sub, sub_eq_zero] at hd

/-- Let `f` be constant, with value `c`, on a set `W₁` containing the point `y`, and let the
affine span of `W₁` equal that of `W₂`, which is the fiber `ν = b`. Then every vector in the
kernel of `ν` is in the kernel of `f`. The point `y` makes `W₁` nonempty, which is needed: for
empty sets the fiber hypothesis can hold with `ν = 0`. -/
theorem map_eq_zero_of_affineSpan_eq {K V E F : Type*} [Ring K] [AddCommGroup V] [Module K V]
    [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
    {W₁ W₂ : Set V} (f : V →ₗ[K] E) (ν : V →ₗ[K] F) {c : E} {b : F}
    (hheight : ∀ x ∈ W₁, f x = c) (hspan : (affineSpan K W₂ : Set V) = {x | ν x = b})
    (heq : affineSpan K W₁ = affineSpan K W₂) {y q : V} (hy : y ∈ W₁) (hq : ν q = 0) :
    f q = 0 := by
  have hyν : ν y = b := (hspan.subset) (heq ▸ subset_affineSpan K _ hy)
  have hyq : y + q ∈ affineSpan K W₁ := by
    rw [heq]
    apply hspan.symm.subset
    simpa only [Set.mem_ofPred_eq, map_add, hq, add_zero] using hyν
  have hh := AffineMap.eqOn_affineSpan
    (f := f.toAffineMap) (g := AffineMap.const K V c) hheight hyq
  simpa only [LinearMap.coe_toAffineMap, AffineMap.const_apply, map_add,
    hheight _ hy, add_eq_left] using hh

/-- The supporting direction of a preimage of a nonempty set under a linear surjection is
the preimage of the original supporting direction. -/
theorem direction_affineSpan_preimage {K V V' : Type*} [Ring K] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (A : V →ₗ[K] V') (hA : Function.Surjective A)
    {S : Set V'} (hS : S.Nonempty) :
    (affineSpan K (A ⁻¹' S)).direction = (affineSpan K S).direction.comap A := by
  have hvsub : A ⁻¹' S -ᵥ A ⁻¹' S = A ⁻¹' (S -ᵥ S) := by
    ext z
    simp only [Set.mem_vsub, Set.mem_preimage, vsub_eq_sub]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨A x, hx, A y, hy, (map_sub A x y).symm⟩
    · rintro ⟨s₁, hs₁, s₂, hs₂, h⟩
      obtain ⟨y, rfl⟩ := hA s₂
      refine ⟨z + y, ?_, y, hs₂, add_sub_cancel_right z y⟩
      rwa [map_add, ← h, sub_add_cancel]
  rw [direction_affineSpan, direction_affineSpan, vectorSpan_def, vectorSpan_def, hvsub,
    Submodule.span_preimage_eq (hS.vsub hS) (by simp [LinearMap.range_eq_top.mpr hA])]

end LinearMap

namespace TauCeti

variable {k V E P Q : Type*} [Ring k]
  [AddCommGroup V] [Module k V] [AddTorsor V P]
  [AddCommGroup E] [Module k E] [AddTorsor E Q]

/-- Taking the product with a fixed nonempty set preserves and reflects equality of affine spans,
including for empty `s` and `t`. -/
theorem affineSpan_prod_eq_iff {s t : Set P} {u : Set Q} (hu : u.Nonempty) :
    affineSpan k (s ×ˢ u) = affineSpan k (t ×ˢ u) ↔ affineSpan k s = affineSpan k t := by
  rw [affineSpan_prod_eq, affineSpan_prod_eq, ← SetLike.coe_set_eq, AffineSubspace.coe_prod,
    AffineSubspace.coe_prod, Set.prod_eq_iff_eq (hu.mono (subset_affineSpan k u)),
    SetLike.coe_set_eq]

/-- Taking the product with a fixed nonempty set preserves and reflects equality of the
directions of affine spans of nonempty sets. -/
theorem direction_affineSpan_prod_eq_iff {s t : Set P} {u : Set Q}
    (hs : s.Nonempty) (ht : t.Nonempty) (hu : u.Nonempty) :
    (affineSpan k (s ×ˢ u)).direction = (affineSpan k (t ×ˢ u)).direction ↔
      (affineSpan k s).direction = (affineSpan k t).direction := by
  simp only [direction_affineSpan]
  rw [vectorSpan_prod_eq hs hu, vectorSpan_prod_eq ht hu]
  constructor
  · intro h
    simpa only [Submodule.prod_map_fst] using
      congrArg (Submodule.map (LinearMap.fst k V E)) h
  · exact fun h => congrArg (fun S : Submodule k V => S.prod (vectorSpan k u)) h

end TauCeti
