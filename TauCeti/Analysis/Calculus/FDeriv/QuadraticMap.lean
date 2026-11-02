/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.LinearAlgebra.QuadraticForm.Basis
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Analysis.Calculus.Bilinear

/-!
# Fréchet derivatives of quadratic maps

A quadratic map `Q` on a finite-dimensional normed space over a complete field is strictly
differentiable, and its derivative at `x` is the linear map `h ↦ polar Q x h`
(`QuadraticMap.hasStrictFDerivAt`). This upgrades Mathlib's line derivative of a quadratic map
(`QuadraticMap.hasLineDerivAt`), which requires no topology on the domain, to a Fréchet
derivative.

The proof writes `Q` as `x ↦ B x x` for a bilinear map `B`, which is possible because the
space is free (`LinearMap.BilinMap.toQuadraticMap_surjective`); no assumption on the
characteristic of the field is needed.

The file also builds a smooth function with prescribed value, derivative and constant symmetric
second derivative at a point (`TauCeti.exists_contDiff_apply_eq_fderiv_eq_fderiv_fderiv_eq`).
-/

public section

namespace QuadraticMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A quadratic map on a finite-dimensional space is strictly differentiable, with derivative
`h ↦ polar Q x h` at `x`. -/
theorem hasStrictFDerivAt (Q : QuadraticMap 𝕜 E F) (x : E) :
    HasStrictFDerivAt Q (LinearMap.toContinuousLinearMap (polarBilin Q x)) x := by
  obtain ⟨B, rfl⟩ := LinearMap.BilinMap.toQuadraticMap_surjective Q
  have hd : LinearMap.toContinuousLinearMap (polarBilin B.toQuadraticMap x) =
      B.toContinuousBilinearMap.precompR E x (.id 𝕜 E) +
        B.toContinuousBilinearMap.precompL E (.id 𝕜 E) x := by
    ext h
    simp [LinearMap.BilinMap.polar_toQuadraticMap]
  rw [hd]
  exact B.toContinuousBilinearMap.hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id x)
    (hasStrictFDerivAt_id x)

/-- A quadratic map on a finite-dimensional space has derivative `h ↦ polar Q x h` at `x`. -/
theorem hasFDerivAt (Q : QuadraticMap 𝕜 E F) (x : E) :
    HasFDerivAt Q (LinearMap.toContinuousLinearMap (polarBilin Q x)) x :=
  (Q.hasStrictFDerivAt x).hasFDerivAt

/-- A quadratic map on a finite-dimensional space is differentiable. -/
theorem differentiable (Q : QuadraticMap 𝕜 E F) : Differentiable 𝕜 Q :=
  fun x ↦ (Q.hasFDerivAt x).differentiableAt

/-- The derivative of a quadratic map on a finite-dimensional space at `x` is
`h ↦ polar Q x h`. -/
theorem fderiv_apply (Q : QuadraticMap 𝕜 E F) (x h : E) : fderiv 𝕜 Q x h = polar Q x h := by
  rw [(Q.hasFDerivAt x).fderiv]
  simp

end QuadraticMap

namespace TauCeti

open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A smooth function with prescribed value, derivative and symmetric second derivative at a
point, the latter constant: `z ↦ c + α (z - y) + (1 / 2) • B (z - y) (z - y)`. -/
theorem exists_contDiff_apply_eq_fderiv_eq_fderiv_fderiv_eq (y : E) (c : F) (α : E →L[ℝ] F)
    (B : E →L[ℝ] E →L[ℝ] F) (hB : ∀ u v, B u v = B v u) :
    ∃ φ : E → F, ContDiff ℝ ∞ φ ∧ φ y = c ∧ fderiv ℝ φ y = α ∧
      ∀ z, fderiv ℝ (fderiv ℝ φ) z = B := by
  have hsub (z : E) : HasFDerivAt (fun z : E ↦ z - y) (ContinuousLinearMap.id ℝ E) z :=
    (hasFDerivAt_id z).sub_const y
  have hφ (z : E) : HasFDerivAt (fun z ↦ c + α (z - y) + (1 / 2 : ℝ) • B (z - y) (z - y))
      (α + B (z - y)) z := by
    have h := ((hasFDerivAt_const c z).add (α.hasFDerivAt.comp z (hsub z))).add
      (((B.hasFDerivAt_apply_self (z - y)).comp z (hsub z)).const_smul (1 / 2 : ℝ))
    refine h.congr_fderiv (ContinuousLinearMap.ext fun h ↦ ?_)
    simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply, zero_add]
    rw [hB h (z - y), ← two_smul ℝ (B (z - y) h), smul_smul]
    norm_num
  have hD : fderiv ℝ (fun z ↦ c + α (z - y) + (1 / 2 : ℝ) • B (z - y) (z - y)) =
      fun z ↦ α + B (z - y) :=
    funext fun z ↦ (hφ z).fderiv
  refine ⟨fun z ↦ c + α (z - y) + (1 / 2 : ℝ) • B (z - y) (z - y), ?_, by simp,
    by rw [hD]; simp, fun z ↦ ?_⟩
  · exact (contDiff_const.add (α.contDiff.comp (contDiff_id.sub contDiff_const))).add
      ((B.contDiff_apply_self.comp (contDiff_id.sub contDiff_const)).const_smul _)
  · rw [hD]
    exact ((B.hasFDerivAt.comp z (hsub z)).const_add α).fderiv

end TauCeti
