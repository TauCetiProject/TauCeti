/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Projection

/-!
# Eigenspaces of complex structures

This file records the eigenspace decomposition of a complex-linear endomorphism whose square is
negative one. The decomposition produces the two complementary pieces used in complex-structure
and Hodge decompositions. The projections onto the `i`- and `-i`-eigenspaces are explicitly
`(1 - i f) / 2` and `(1 + i f) / 2`, fixing the normalization used in complex tangent type
decompositions.

## Main declarations

* `Module.End.isCompl_eigenspace_I_neg_I_of_sq_eq_neg_id`: the `i`- and `-i`-eigenspaces of an
  endomorphism squaring to `-1` are complementary.
* `TauCeti.projection_eigenspace_I_neg_I_apply` and
  `TauCeti.projection_eigenspace_neg_I_I_apply`: the explicit formulas for the native
  projections onto the two eigenspaces.
-/

public section

namespace Module.End

universe u

variable {W : Type u} [AddCommGroup W] [Module ℂ W]

/-- The `i`- and `-i`-eigenspaces of a complex-linear endomorphism squaring to `-1` are
complementary. -/
theorem isCompl_eigenspace_I_neg_I_of_sq_eq_neg_id (f : Module.End ℂ W)
    (hf : f.comp f = -LinearMap.id) :
    IsCompl (eigenspace f Complex.I) (eigenspace f (-Complex.I)) := by
  have hf_apply (x : W) : f (f x) = -x := by
    simpa using LinearMap.congr_fun hf x
  constructor
  · simpa only [eigenspace] using
      disjoint_genEigenspace f (neg_ne_self.mpr Complex.I_ne_zero).symm 1 1
  · rw [codisjoint_iff]
    apply top_unique
    intro x _
    let xplus : W := (2 : ℂ)⁻¹ • (x - Complex.I • f x)
    let xminus : W := (2 : ℂ)⁻¹ • (x + Complex.I • f x)
    have hxplus : xplus ∈ eigenspace f Complex.I := by
      rw [mem_eigenspace_iff]
      simp only [xplus, map_smul, map_sub, hf_apply, smul_neg, smul_smul]
      simp only [smul_sub, smul_neg, smul_smul]
      have hscalar : Complex.I * (2 : ℂ)⁻¹ * Complex.I = -(2 : ℂ)⁻¹ := by
        calc
          Complex.I * (2 : ℂ)⁻¹ * Complex.I =
              (2 : ℂ)⁻¹ * (Complex.I * Complex.I) := by ring
          _ = -(2 : ℂ)⁻¹ := by rw [Complex.I_mul_I]; ring
      rw [hscalar]
      module
    have hxminus : xminus ∈ eigenspace f (-Complex.I) := by
      rw [mem_eigenspace_iff]
      simp only [xminus, map_smul, map_add, hf_apply, smul_neg, smul_smul]
      simp only [smul_add, smul_neg, smul_smul]
      have hscalar : -Complex.I * (2 : ℂ)⁻¹ * Complex.I = (2 : ℂ)⁻¹ := by
        calc
          -Complex.I * (2 : ℂ)⁻¹ * Complex.I =
              -(2 : ℂ)⁻¹ * (Complex.I * Complex.I) := by ring
          _ = (2 : ℂ)⁻¹ := by rw [Complex.I_mul_I]; ring
      rw [hscalar]
      module
    have hdecomp : x = xplus + xminus := by
      simp [xplus, xminus]
      module
    rw [hdecomp]
    exact Submodule.add_mem_sup hxplus hxminus

end Module.End

namespace TauCeti

open Module.End

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The projection onto the `i`-eigenspace of a complex structure along its `-i`-eigenspace
is the explicit operator `(1 - i f) / 2`. -/
theorem projection_eigenspace_I_neg_I_apply (f : Module.End ℂ W)
    (hf : f.comp f = -LinearMap.id) (x : W) :
    (eigenspace f Complex.I).projection (eigenspace f (-Complex.I))
        (f.isCompl_eigenspace_I_neg_I_of_sq_eq_neg_id hf) x =
      (2 : ℂ)⁻¹ • (x - Complex.I • f x) := by
  let h := f.isCompl_eigenspace_I_neg_I_of_sq_eq_neg_id hf
  let p := (eigenspace f Complex.I).projection (eigenspace f (-Complex.I)) h
  let q := (eigenspace f (-Complex.I)).projection (eigenspace f Complex.I) h.symm
  have hsum : p x + q x = x := Submodule.projection_add_projection_eq_self h x
  have hp : f (p x) = Complex.I • p x :=
    mem_eigenspace_iff.mp (Submodule.projection_apply_mem h x)
  have hq : f (q x) = -Complex.I • q x :=
    mem_eigenspace_iff.mp (Submodule.projection_apply_mem h.symm x)
  have hfx : f x = Complex.I • p x + -Complex.I • q x := by
    calc
      f x = f (p x + q x) := congrArg f hsum.symm
      _ = Complex.I • p x + -Complex.I • q x := by rw [map_add, hp, hq]
  calc
    p x = (2 : ℂ)⁻¹ • ((p x + q x) -
        Complex.I • (Complex.I • p x + -Complex.I • q x)) := by
      simp only [smul_add, smul_smul, mul_neg, Complex.I_mul_I, neg_one_smul,
        neg_neg]
      module
    _ = (2 : ℂ)⁻¹ • (x - Complex.I • f x) := by rw [hsum, hfx]

/-- The projection onto the `-i`-eigenspace of a complex structure along its `i`-eigenspace
is the explicit operator `(1 + i f) / 2`. -/
theorem projection_eigenspace_neg_I_I_apply (f : Module.End ℂ W)
    (hf : f.comp f = -LinearMap.id) (x : W) :
    (eigenspace f (-Complex.I)).projection (eigenspace f Complex.I)
        (f.isCompl_eigenspace_I_neg_I_of_sq_eq_neg_id hf).symm x =
      (2 : ℂ)⁻¹ • (x + Complex.I • f x) := by
  rw [Submodule.projection_eq_self_sub_projection
    (f.isCompl_eigenspace_I_neg_I_of_sq_eq_neg_id hf),
    projection_eigenspace_I_neg_I_apply f hf]
  module

end TauCeti
