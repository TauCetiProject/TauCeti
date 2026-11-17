/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smoothness of the normalization map

On a real inner product space the norm is smooth away from the origin, and so is the
normalization `NormedSpace.normalize x = ‖x‖⁻¹ • x`, which sends a nonzero vector to the unit
vector in its direction. Composing a smooth function on the unit sphere with it gives the functions
that are positively homogeneous of degree zero, such as the angular cutoffs of microlocal analysis.

## Main results

* `NormedSpace.contDiffAt_normalize`: `normalize` is smooth at every nonzero vector.
* `NormedSpace.contDiffOn_normalize`: `normalize` is smooth on the complement of the origin.
* `NormedSpace.continuousOn_normalize`: on any real normed space, `normalize` is continuous on the
  complement of the origin.
* `NormedSpace.isClosed_setOf_eq_zero_or_normalize_mem`: the cone `{0} ∪ {x ≠ 0 | x / ‖x‖ ∈ S}`
  over a closed set `S` of directions is closed.
-/

public section

open scoped ContDiff

namespace NormedSpace

/-- The normalization `x ↦ ‖x‖⁻¹ • x` is continuous on the complement of the origin of a real
normed space. -/
theorem continuousOn_normalize {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ContinuousOn (normalize : F → F) {x | x ≠ 0} :=
  (continuous_norm.continuousOn.inv₀ fun _ hx ↦ norm_ne_zero_iff.2 hx).smul continuousOn_id

/-- The cone over a closed set `S` of directions, the set of vectors that are zero or whose
normalization lies in `S`, is closed. -/
theorem isClosed_setOf_eq_zero_or_normalize_mem {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {S : Set F} (hS : IsClosed S) :
    IsClosed {x : F | x = 0 ∨ normalize x ∈ S} := by
  have : {x : F | x = 0 ∨ normalize x ∈ S}ᶜ = {x | x ≠ 0} ∩ normalize ⁻¹' Sᶜ := by
    ext x
    simp [not_or]
  rw [← isOpen_compl_iff, this]
  exact continuousOn_normalize.isOpen_inter_preimage isOpen_ne hS.isOpen_compl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : WithTop ℕ∞}

/-- The normalization `x ↦ ‖x‖⁻¹ • x` is smooth at every nonzero vector of a real inner product
space. -/
theorem contDiffAt_normalize {x : E} (hx : x ≠ 0) : ContDiffAt ℝ n normalize x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.2 hx)).smul contDiffAt_id

/-- The normalization `x ↦ ‖x‖⁻¹ • x` is smooth on the complement of the origin of a real inner
product space. -/
theorem contDiffOn_normalize : ContDiffOn ℝ n (normalize : E → E) {x | x ≠ 0} :=
  fun _ hx ↦ (contDiffAt_normalize hx).contDiffWithinAt

end NormedSpace
