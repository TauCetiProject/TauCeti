/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.LinearAlgebra.Complex.Eigenspace

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
  apply Module.End.isCompl_eigenspace_I_neg_I_of_sq_eq_neg_id
  have h := congrArg (LinearMap.baseChange ℂ) J.square_neg
  simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_neg,
    LinearMap.baseChange_id] using h

end TauCeti.AlmostComplexStructure
