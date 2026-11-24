/-
Copyright (c) 2026 The Tau Ceti contributors and Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Affine maps and line maps

Affine-map uniqueness, computations and affine-subspace avoidance for `AffineMap.lineMap`.

## Main results

* `AffineMap.ext_of_ne`: affine maps from a division ring that agree at two distinct points are
  equal.
* `AffineMap.apply_eq_linear_add_apply_zero`: an affine map is its linear part plus its value at
  `0`.
* `AffineMap.apply_eq_add_mul_sub`: an affine function on the line is
  `s ↦ f 0 + s * (f 1 - f 0)`.
* `AffineMap.lineMap_vsub_lineMap_eq_vsub_add_smul_sub_smul`: the difference of points on two
  segments, at independent parameters, in terms of the endpoints.
* `AffineMap.exists_leftInvOn_of_injOn`: over a division ring, an affine map injective on an
  affine subspace has an affine left inverse there.

The affine-subspace avoidance lemmas are adapted from `Mei/Geometry/Affine/Generic.lean`
at commit `7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).
Source: https://github.com/yuma-mizuno-lean/Mei/blob/7f1e4c7714fb020473694755ad8748c8f15d0e7f/Mei/Geometry/Affine/Generic.lean
-/

public section

namespace AffineMap

/-- Affine maps from a division ring that agree at two distinct points are equal. -/
theorem ext_of_ne {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
    [AddTorsor V P] {f g : k →ᵃ[k] P} {a b : k} (hab : a ≠ b) (ha : f a = g a)
    (hb : f b = g b) : f = g := by
  ext c
  have hc : c = lineMap a b ((c - a) / (b - a)) := by
    rw [lineMap_apply_ring', div_mul_cancel₀ _ (sub_ne_zero.mpr hab.symm)]
    exact (sub_add_cancel c a).symm
  rw [hc, f.apply_lineMap, g.apply_lineMap, ha, hb]

/-- An affine map on a module is its linear part plus its value at `0`. -/
theorem apply_eq_linear_add_apply_zero {k V W : Type*} [Ring k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (f : V →ᵃ[k] W) (x : V) : f x = f.linear x + f 0 := by
  simpa using congrFun f.decomp x

/-- An affine function on the line is determined by its values at `0` and `1`. -/
theorem apply_eq_add_mul_sub {k : Type*} [CommRing k] (f : k →ᵃ[k] k) (s : k) :
    f s = f 0 + s * (f 1 - f 0) := by
  have h := f.apply_lineMap (0 : k) 1 s
  rw [lineMap_apply_ring', lineMap_apply_ring'] at h
  simp only [sub_zero, mul_one, add_zero] at h
  rw [h]
  ring

/-- The difference of a point at parameter `s` on the segment `p₀ p₁` and a point at parameter
`t` on the segment `q₀ q₁`. Unlike `AffineMap.lineMap_vsub_lineMap`, the two parameters may
differ. -/
theorem lineMap_vsub_lineMap_eq_vsub_add_smul_sub_smul {k V P : Type*} [Ring k] [AddCommGroup V]
    [Module k V] [AddTorsor V P] (p₀ p₁ q₀ q₁ : P) (s t : k) :
    lineMap p₀ p₁ s -ᵥ lineMap q₀ q₁ t = (p₀ -ᵥ q₀) + s • (p₁ -ᵥ p₀) - t • (q₁ -ᵥ q₀) := by
  rw [lineMap_apply, lineMap_apply, vadd_vsub_vadd_comm]
  abel

/-- Over a division ring, an affine map which is injective on an affine subspace `S` has an affine
left inverse on `S`. This is the affine counterpart of
`LinearMap.exists_leftInverse_of_injective`: the inverse of the linear part on the direction of
`S` extends to the whole target by `LinearMap.exists_extend`. No topology is involved; for a
continuous left inverse into a finite-dimensional normed target see
`AffineMap.exists_leftInvOn_affineSpan`. -/
theorem exists_leftInvOn_of_injOn {k V₁ P₁ V₂ P₂ : Type*} [DivisionRing k] [AddCommGroup V₁]
    [Module k V₁] [AddTorsor V₁ P₁] [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
    (f : P₁ →ᵃ[k] P₂) {S : AffineSubspace k P₁} (hf : Set.InjOn f S) :
    ∃ g : P₂ →ᵃ[k] P₁, Set.LeftInvOn g f S := by
  obtain hS | ⟨p₀, hp₀⟩ := (S : Set P₁).eq_empty_or_nonempty
  · obtain ⟨p⟩ := ‹AddTorsor V₁ P₁›.nonempty
    exact ⟨const k P₂ p, fun x hx => absurd (hS ▸ hx) (Set.notMem_empty x)⟩
  -- The linear part of `f` is injective on the direction of `S`.
  have hinj : Function.Injective (f.linear.domRestrict S.direction) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    rw [LinearMap.domRestrict_apply] at hv
    have hv' : f (v.val +ᵥ p₀) = f p₀ := by rw [map_vadd, hv, zero_vadd]
    have hv₀ := hf (S.vadd_mem_of_mem_direction v.property hp₀) hp₀ hv'
    exact Subtype.ext (by simpa using vadd_right_cancel p₀ (hv₀.trans (zero_vadd V₁ p₀).symm))
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    (S.direction.subtype ∘ₗ (LinearEquiv.ofInjective _ hinj).symm.toLinearMap)
  refine ⟨⟨fun y => g (y -ᵥ f p₀) +ᵥ p₀, g, fun y v => by
    rw [vadd_vsub_assoc, map_add, vadd_vadd]⟩, fun x hx => ?_⟩
  have hx : x -ᵥ p₀ ∈ S.direction := S.vsub_mem_direction hx hp₀
  have key : g (f x -ᵥ f p₀) = x -ᵥ p₀ := by
    have := LinearMap.congr_fun hg (LinearEquiv.ofInjective _ hinj ⟨_, hx⟩)
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearEquiv.ofInjective_apply,
      LinearMap.domRestrict_apply] at this
    rw [← linear_apply_vsub, this]
  simp [key]

end AffineMap

namespace AffineSubspace

open Set
open scoped Affine

variable {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- Outside the span of an affine obstacle and an endpoint, every nonzero
parameter on the line from that endpoint avoids the obstacle. The endpoint
itself need not avoid the obstacle. -/
theorem lineMap_not_mem_of_not_mem_affineSpan_insert_of_ne_zero (S : AffineSubspace k P)
    {x z : P} (hz : z ∉ affineSpan k (insert x (S : Set P)))
    {t : k} (ht : t ≠ 0) : AffineMap.lineMap x z t ∉ S := by
  intro htS
  apply hz
  have hxspan : x ∈ affineSpan k (insert x (S : Set P)) :=
    subset_affineSpan k _ (mem_insert x _)
  have htspan : AffineMap.lineMap x z t ∈ affineSpan k (insert x (S : Set P)) :=
    subset_affineSpan k _ (mem_insert_of_mem x htS)
  simpa only [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ ht,
    AffineMap.lineMap_apply_one] using AffineMap.lineMap_mem t⁻¹ hxspan htspan

/-- A vertex outside the affine span of an obstacle and an allowed endpoint
determines a full line avoiding the obstacle. -/
theorem lineMap_not_mem_of_not_mem_affineSpan_insert (S : AffineSubspace k P)
    {x z : P} (hx : x ∉ S) (hz : z ∉ affineSpan k (insert x (S : Set P)))
    (t : k) : AffineMap.lineMap x z t ∉ S := by
  by_cases ht : t = 0
  · simpa [ht] using hx
  · exact S.lineMap_not_mem_of_not_mem_affineSpan_insert_of_ne_zero hz ht

end AffineSubspace
