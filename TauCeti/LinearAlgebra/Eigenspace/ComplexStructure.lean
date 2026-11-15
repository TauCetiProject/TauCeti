/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.LinearCombination

/-!
# Eigenspaces of complex structures

This file records the eigenspace decomposition of an endomorphism `f` whose square is negative
one. When the scalars contain a square root `i` of `-1` and `2` is invertible, the module is the
direct sum of the `i`- and `-i`-eigenspaces of `f`. These are the two complementary pieces used in
complex-structure and Hodge decompositions, where the scalars are `ℂ` and `i = Complex.I`. The
projections onto the `i`- and `-i`-eigenspaces are explicitly `(1 - i f) / 2` and
`(1 + i f) / 2`, fixing the normalization used in complex tangent type decompositions.

## Main declarations

* `Module.End.isCompl_eigenspace_eigenspace_neg_of_comp_self_eq_neg_id`: the `i`- and
  `-i`-eigenspaces of an endomorphism squaring to `-1` are complementary.
* `Module.End.projection_eigenspace_eigenspace_neg_apply` and
  `Module.End.projection_eigenspace_neg_eigenspace_apply`: the explicit formulas for the native
  projections onto the two eigenspaces.
-/

public section

namespace Module.End

universe u v

variable {K : Type u} {W : Type v}

section CommRing

variable [CommRing K] [AddCommGroup W] [Module K W] {i : K}

/-- For `f ∘ f = -1` and `i * i = -1`, the vector `x - i f x` lies in the `i`-eigenspace of
`f`. -/
private theorem sub_smul_apply_mem_eigenspace (hi : i * i = -1) {f : Module.End K W}
    (hf : f.comp f = -LinearMap.id) (x : W) : x - i • f x ∈ eigenspace f i := by
  have hf_apply : f (f x) = -x := by
    simpa only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply] using
      LinearMap.congr_fun hf x
  rw [mem_eigenspace_iff, map_sub, map_smul, hf_apply]
  linear_combination (norm := module) hi • f x

/-- If `2` is a unit and `i` is a square root of `-1`, the `i`- and `-i`-eigenspaces of an
endomorphism squaring to `-1` are complementary. -/
theorem isCompl_eigenspace_eigenspace_neg_of_comp_self_eq_neg_id (h2 : IsUnit (2 : K))
    (hi : i * i = -1) (f : Module.End K W) (hf : f.comp f = -LinearMap.id) :
    IsCompl (eigenspace f i) (eigenspace f (-i)) := by
  have hi' : -i * -i = -1 := by rwa [neg_mul_neg]
  refine ⟨Submodule.disjoint_def.mpr fun x hx hx' ↦ h2.smul_eq_zero.mp ?_,
    codisjoint_iff.mpr <| eq_top_iff.mpr fun x _ ↦ Submodule.mem_sup.mpr
      ⟨_, (eigenspace f i).smul_mem (↑h2.unit⁻¹ : K) (sub_smul_apply_mem_eigenspace hi hf x),
        _, (eigenspace f (-i)).smul_mem (↑h2.unit⁻¹ : K) (sub_smul_apply_mem_eigenspace hi' hf x),
        ?_⟩⟩
  · rw [mem_eigenspace_iff] at hx hx'
    linear_combination (norm := module) i • hx - i • hx' + (2 : K) • hi • x
  · linear_combination (norm := module) h2.val_inv_mul • x

/-- The projection onto the `i`-eigenspace of a complex structure along its `-i`-eigenspace
is the explicit operator `(1 - i f) / 2`, with `1 / 2` the inverse of the unit `2`. -/
theorem projection_eigenspace_eigenspace_neg_apply (h2 : IsUnit (2 : K)) (hi : i * i = -1)
    (f : Module.End K W) (hf : f.comp f = -LinearMap.id) (x : W) :
    (eigenspace f i).projection (eigenspace f (-i))
        (f.isCompl_eigenspace_eigenspace_neg_of_comp_self_eq_neg_id h2 hi hf) x =
      (↑h2.unit⁻¹ : K) • (x - i • f x) := by
  have hi' : -i * -i = -1 := by rwa [neg_mul_neg]
  have hx : x = (↑h2.unit⁻¹ : K) • (x - i • f x) + (↑h2.unit⁻¹ : K) • (x - -i • f x) := by
    linear_combination (norm := module) -h2.val_inv_mul • x
  conv_lhs => rw [hx]
  rw [map_add, Submodule.projection_apply_of_mem_left _
      (Submodule.smul_mem _ _ (sub_smul_apply_mem_eigenspace hi hf x)),
    (Submodule.projection_apply_eq_zero_iff _).mpr
      (Submodule.smul_mem _ _ (sub_smul_apply_mem_eigenspace hi' hf x)), add_zero]

/-- The projection onto the `-i`-eigenspace of a complex structure along its `i`-eigenspace
is the explicit operator `(1 + i f) / 2`, with `1 / 2` the inverse of the unit `2`. -/
theorem projection_eigenspace_neg_eigenspace_apply (h2 : IsUnit (2 : K)) (hi : i * i = -1)
    (f : Module.End K W) (hf : f.comp f = -LinearMap.id) (x : W) :
    (eigenspace f (-i)).projection (eigenspace f i)
        (f.isCompl_eigenspace_eigenspace_neg_of_comp_self_eq_neg_id h2 hi hf).symm x =
      (↑h2.unit⁻¹ : K) • (x + i • f x) := by
  rw [Submodule.projection_eq_self_sub_projection
      (f.isCompl_eigenspace_eigenspace_neg_of_comp_self_eq_neg_id h2 hi hf),
    projection_eigenspace_eigenspace_neg_apply h2 hi f hf]
  linear_combination (norm := module) -h2.val_inv_mul • x

end CommRing

end Module.End
