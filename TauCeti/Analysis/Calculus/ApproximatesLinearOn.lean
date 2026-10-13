/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-!
# A priori estimates for maps approximating linear maps

An estimate controlling a vector by its image under a continuous linear map and an auxiliary
additive map persists under a nonlinear approximation, with a loss proportional to the
approximation constant. `ApproximatesLinearOn.one_sub_mul_norm_sub_le` records this absorption
estimate. Taking the auxiliary map to be a projection onto the kernel gives the nonlinear form
of the Peetre estimate used in local properness arguments.
-/

public section

open Set
open scoped NNReal

namespace ApproximatesLinearOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- An a priori estimate for a linear map persists under a nonlinear approximation, with its
left side scaled by `1 - C * ε`. For `C * ε < 1`, this gives control of `‖x - y‖` by the images
under `f` and an auxiliary additive map `P`.

Taking `P` to be a projection onto the kernel recovers the nonlinear Peetre estimate; see
Wendl, *Fredholm operators*, Lemma 5.2, for the linear estimate. -/
theorem one_sub_mul_norm_sub_le {f : E → F} {f' : E →L[𝕜] F} {s : Set E} {ε : ℝ≥0}
    (hf : ApproximatesLinearOn f f' s ε) {G : Type*} [SeminormedAddGroup G]
    {P : E →+ G} {C : ℝ} (hC : 0 ≤ C) (hest : ∀ z, ‖z‖ ≤ C * ‖f' z‖ + ‖P z‖)
    {x : E} (hx : x ∈ s) {y : E} (hy : y ∈ s) :
    (1 - C * (ε : ℝ)) * ‖x - y‖ ≤ C * ‖f x - f y‖ + ‖P x - P y‖ := by
  have h1 := hest (x - y)
  have h2 := hf x hx y hy
  have h3 : ‖f' (x - y)‖ ≤ ‖f x - f y‖ + (ε : ℝ) * ‖x - y‖ := by
    exact (norm_le_norm_add_norm_sub (f x - f y) _).trans (add_le_add le_rfl h2)
  have h4 : C * ‖f' (x - y)‖ ≤ C * (‖f x - f y‖ + (ε : ℝ) * ‖x - y‖) :=
    mul_le_mul_of_nonneg_left h3 hC
  rw [map_sub P x y] at h1
  nlinarith

end ApproximatesLinearOn
