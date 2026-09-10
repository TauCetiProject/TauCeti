/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.LinearAlgebra.Complex.Conjugation

/-!
# Complexification of almost complex structures

An almost complex structure on a real vector space extends complex-linearly to its
complexification. Its square remains `-1`, and its `i`- and `-i`-eigenspaces are complementary.

## Main declarations

* `TauCeti.AlmostComplexStructure.baseChange_apply_apply`: the complexified endomorphism squares
  to `-1`.
* `TauCeti.AlmostComplexStructure.isCompl_eigenspace_baseChange_I_neg_I`: its `i`- and
  `-i`-eigenspaces are complementary.
-/

public section

namespace TauCeti.AlmostComplexStructure

open scoped TensorProduct

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- Applying the complexification of an almost complex structure twice gives the negative of the
original vector. -/
@[simp]
theorem baseChange_apply_apply (J : AlmostComplexStructure V) (x : ℂ ⊗[ℝ] V) :
    J.toLinearMap.baseChange ℂ (J.toLinearMap.baseChange ℂ x) = -x := by
  have h := congrArg (LinearMap.baseChange ℂ) J.square_neg
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_neg, LinearMap.baseChange_id] at h
  exact LinearMap.congr_fun h x

/-- The `i`- and `-i`-eigenspaces of the complexification of an almost complex structure are
complementary. -/
theorem isCompl_eigenspace_baseChange_I_neg_I (J : AlmostComplexStructure V) :
    IsCompl (Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I)
      (Module.End.eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I)) := by
  constructor
  · rw [disjoint_iff, Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff,
      Module.End.mem_eigenspace_iff] at hx
    have hscalar : Complex.I • x = -Complex.I • x := hx.1.symm.trans hx.2
    have hzero : (2 * Complex.I) • x = 0 := by
      calc
        (2 * Complex.I) • x = Complex.I • x + Complex.I • x := by module
        _ = Complex.I • x + (-Complex.I) • x := congrArg (Complex.I • x + ·) hscalar
        _ = 0 := by rw [neg_smul, add_neg_cancel]
    exact (smul_eq_zero.mp hzero).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  · rw [codisjoint_iff]
    apply top_unique
    intro x _
    let xplus : ℂ ⊗[ℝ] V :=
      (2 : ℂ)⁻¹ • (x - Complex.I • J.toLinearMap.baseChange ℂ x)
    let xminus : ℂ ⊗[ℝ] V :=
      (2 : ℂ)⁻¹ • (x + Complex.I • J.toLinearMap.baseChange ℂ x)
    have hxplus : xplus ∈ Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I := by
      rw [Module.End.mem_eigenspace_iff]
      simp only [xplus, map_smul, map_sub, map_smul, baseChange_apply_apply, smul_neg,
        smul_smul]
      simp only [smul_sub, smul_neg, smul_smul]
      have hscalar : Complex.I * (2 : ℂ)⁻¹ * Complex.I = -(2 : ℂ)⁻¹ := by
        calc
          Complex.I * (2 : ℂ)⁻¹ * Complex.I = (2 : ℂ)⁻¹ * (Complex.I * Complex.I) := by ring
          _ = -(2 : ℂ)⁻¹ := by rw [Complex.I_mul_I]; ring
      rw [hscalar]
      module
    have hxminus : xminus ∈ Module.End.eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I) := by
      rw [Module.End.mem_eigenspace_iff]
      simp only [xminus, map_smul, map_add, map_smul, baseChange_apply_apply, smul_neg,
        smul_smul]
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

end TauCeti.AlmostComplexStructure
