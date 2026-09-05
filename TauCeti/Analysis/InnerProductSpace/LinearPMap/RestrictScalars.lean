/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.LinearPMap
public import Mathlib.Topology.Instances.Complex

/-!
# Restriction of complex partial linear maps to real scalars
-/

public section

noncomputable section

namespace LinearPMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℂ E] [NormedSpace ℂ F]

/-- A complex partial linear map regarded as a real partial linear map, with the same domain and
values. -/
@[expose] def restrictScalarsReal (A : E →ₗ.[ℂ] F) : E →ₗ.[ℝ] F where
  domain := A.domain.restrictScalars ℝ
  toFun := A.toFun.restrictScalars ℝ

@[simp]
theorem restrictScalarsReal_domain (A : E →ₗ.[ℂ] F) :
    A.restrictScalarsReal.domain = A.domain.restrictScalars ℝ :=
  rfl

@[simp]
theorem restrictScalarsReal_apply (A : E →ₗ.[ℂ] F) (x : A.domain) :
    A.restrictScalarsReal x = A x :=
  rfl

/-- Real restriction commutes with negation. -/
@[simp]
theorem restrictScalarsReal_neg (A : E →ₗ.[ℂ] F) :
    (-A).restrictScalarsReal = -A.restrictScalarsReal :=
  LinearPMap.ext rfl fun _ _ _ => rfl

/-- The real restrictions of `-i • A` and `i • A` are negatives of one another. -/
theorem restrictScalarsReal_neg_I_smul (A : E →ₗ.[ℂ] F) :
    (-Complex.I • A).restrictScalarsReal = -(Complex.I • A).restrictScalarsReal := by
  rw [← restrictScalarsReal_neg]
  congr 1
  exact LinearPMap.ext rfl fun x hx _ => neg_smul Complex.I (A ⟨x, hx⟩)

end LinearPMap

end
