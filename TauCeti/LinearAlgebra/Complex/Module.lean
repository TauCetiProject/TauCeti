/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module

/-!
# Scalar multiplication in complex modules

The action of a complex scalar decomposes into its real and imaginary parts. The formula uses
any real module structure compatible with the complex action, so it also applies when a real
module is equipped with a chosen complex structure.
-/

public section

namespace Complex

/-- Decompose a complex scalar action into its real and imaginary parts. -/
@[simp]
lemma re_smul_add_im_smul {V : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V]
    [IsScalarTower ℝ ℂ V] (z : ℂ) (v : V) :
    z.re • v + z.im • (I • v) = z • v := by
  simpa only [add_smul, mul_smul, ← coe_algebraMap, IsScalarTower.algebraMap_smul]
    using congrArg (fun c : ℂ => c • v) z.re_add_im

end Complex
