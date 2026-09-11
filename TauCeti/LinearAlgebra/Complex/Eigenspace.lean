/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenspaces of complex structures

This file records the eigenspace decomposition of a complex-linear endomorphism whose square is
negative one. The decomposition produces the two complementary pieces used in complex-structure
and Hodge decompositions.

## Main declarations

* `Module.End.isCompl_eigenspace_I_neg_I_of_sq_eq_neg_id`: the `i`- and `-i`-eigenspaces of an
  endomorphism squaring to `-1` are complementary.
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
