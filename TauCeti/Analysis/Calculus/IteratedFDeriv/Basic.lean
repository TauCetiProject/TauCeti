/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Iterated derivatives of iterated derivatives

The `i`-th iterated derivative of the `m`-th iterated derivative of a function has the same norm
as its `(i + m)`-th iterated derivative. This extends Mathlib's `norm_iteratedFDeriv_fderiv`, the
case `m = 1`, and lets bounds on all iterated derivatives of a function transfer to its iterated
derivative fields. The file also supplies the two-variable currying isometry used to identify
continuous multilinear second derivatives with curried bilinear maps, and the corresponding
exact comparison for differences of second derivatives, which transfers Hölder bounds between
the two forms of the second derivative.
-/

public section

open scoped NNReal

namespace TauCeti

section CurryFin2

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The currying linear isometry from continuous multilinear maps on `Fin 2` to
continuous bilinear maps in curried form. -/
noncomputable def continuousMultilinearCurryFin2 :
    (E [×2]→L[𝕜] F) ≃ₗᵢ[𝕜] E →L[𝕜] E →L[𝕜] F :=
  (continuousMultilinearCurryRightEquiv' 𝕜 1 E F).trans
    (continuousMultilinearCurryFin1 𝕜 E (E →L[𝕜] F))

/-- The currying isometry evaluates a multilinear map on its two arguments in order. -/
@[simp]
theorem continuousMultilinearCurryFin2_apply (f : E [×2]→L[𝕜] F) (x y : E) :
    continuousMultilinearCurryFin2 𝕜 E F f x y = f ![x, y] := by
  simp [continuousMultilinearCurryFin2]

/-- The inverse currying isometry evaluates its arguments in their original order. -/
@[simp]
theorem continuousMultilinearCurryFin2_symm_apply
    (g : E →L[𝕜] E →L[𝕜] F) (m : Fin 2 → E) :
    (continuousMultilinearCurryFin2 𝕜 E F).symm g m = g (m 0) (m 1) := by
  simp [continuousMultilinearCurryFin2, Fin.init]

end CurryFin2

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Currying the second iterated derivative gives the Fréchet derivative of the first
Fréchet derivative, including at points where these derivatives are junk-valued. -/
theorem continuousMultilinearCurryFin2_iteratedFDeriv_two (f : E → F) (x : E) :
    continuousMultilinearCurryFin2 𝕜 E F (iteratedFDeriv 𝕜 2 f x) =
      fderiv 𝕜 (fderiv 𝕜 f) x := by
  ext v w
  simp only [continuousMultilinearCurryFin2_apply, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

/-- Differences of curried second derivatives and multilinear second derivatives have
exactly the same norm, without differentiability assumptions. -/
theorem norm_fderiv_fderiv_sub (f : E → F) (x y : E) :
    ‖fderiv 𝕜 (fderiv 𝕜 f) x - fderiv 𝕜 (fderiv 𝕜 f) y‖ =
      ‖iteratedFDeriv 𝕜 2 f x - iteratedFDeriv 𝕜 2 f y‖ := by
  rw [← continuousMultilinearCurryFin2_iteratedFDeriv_two f x,
    ← continuousMultilinearCurryFin2_iteratedFDeriv_two f y, ← LinearIsometryEquiv.map_sub,
    LinearIsometryEquiv.norm_map]

/-- The curried second Fréchet derivative is `r`-Hölder with constant `C` on a set exactly when
the second iterated derivative is, without differentiability assumptions: the two differ by the
currying isometry. -/
theorem holderOnWith_fderiv_fderiv_iff_iteratedFDeriv_two {C r : ℝ≥0} {s : Set E} (f : E → F) :
    HolderOnWith C r (fderiv 𝕜 (fderiv 𝕜 f)) s ↔ HolderOnWith C r (iteratedFDeriv 𝕜 2 f) s := by
  simp only [HolderOnWith, ← continuousMultilinearCurryFin2_iteratedFDeriv_two,
    LinearIsometryEquiv.edist_map]

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
