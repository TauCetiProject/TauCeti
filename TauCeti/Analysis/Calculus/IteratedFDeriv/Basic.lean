/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Iterated derivatives of iterated derivatives

The `i`-th iterated derivative of the `m`-th iterated derivative of a function has the same norm
as its `(i + m)`-th iterated derivative. This extends Mathlib's `norm_iteratedFDeriv_fderiv`, the
case `m = 1`, and lets bounds on all iterated derivatives of a function transfer to its iterated
derivative fields.
-/

public section

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The `i`-th iterated derivative of the `m`-th iterated derivative of `f` has the same norm as
the `(i + m)`-th iterated derivative of `f`. -/
theorem norm_iteratedFDeriv_iteratedFDeriv (f : E → F) (i m : ℕ) (x : E) :
    ‖iteratedFDeriv 𝕜 i (iteratedFDeriv 𝕜 m f) x‖ = ‖iteratedFDeriv 𝕜 (i + m) f x‖ := by
  induction m generalizing i with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      Nat.add_zero]
  | succ m ih =>
    -- Peel off the first derivative: `D^(m+1) f = e ∘ D (D^m f)` for a currying isometry `e`.
    have h : iteratedFDeriv 𝕜 (m + 1) f =
        (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (m + 1) => E) F).symm ∘
          fderiv 𝕜 (iteratedFDeriv 𝕜 m f) :=
      iteratedFDeriv_succ_eq_comp_left
    -- The spaces are given explicitly: unifying them against the instances carried by `e`
    -- otherwise fails.
    have he := LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := 𝕜) (E := E)
      (F := E →L[𝕜] E [×m]→L[𝕜] F) (G := E [×m + 1]→L[𝕜] F)
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (m + 1) => E) F).symm
      (fderiv 𝕜 (iteratedFDeriv 𝕜 m f)) x i
    rw [← h] at he
    rw [he, norm_iteratedFDeriv_fderiv, ih, Nat.add_right_comm, Nat.add_assoc]

end TauCeti
