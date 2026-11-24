/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
import TauCeti.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.InnerProductSpace.LinearMap
import TauCeti.Analysis.Normed.Operator.Bilinear
import TauCeti.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# The metric trace of continuous bilinear maps

On a finite-dimensional real inner product space `E`, the metric trace
`LinearMap.BilinMap.metricTrace` of a continuous bilinear map `H : E →L E →L F` is bounded by
`dim E * ‖H‖`, so it is a continuous linear map `TauCeti.traceL` on the space of continuous
bilinear maps. In an orthonormal basis `eᵢ` it is `H ↦ ∑ᵢ H eᵢ eᵢ`. The Laplacian is the trace of
the second Fréchet derivative (`TauCeti.laplacian_eq_traceL`).

## Main declarations

* `TauCeti.traceL`: the trace `H ↦ ∑ᵢ H eᵢ eᵢ` of a continuous bilinear map, as a continuous
  linear map.
* `ContinuousLinearMap.traceL_apply_eq_metricTrace`: it is the metric trace
  `LinearMap.BilinMap.metricTrace` of the underlying bilinear map.
* `ContinuousLinearMap.traceL_apply`: in the standard orthonormal basis it is the sum of the
  diagonal values.
* `ContinuousLinearMap.norm_traceL_apply_le`: `‖traceL H‖ ≤ dim E * ‖H‖`.
* `ContinuousLinearMap.traceL_flip`, `ContinuousLinearMap.traceL_bilinearComp_linearIsometryEquiv`,
  `TauCeti.traceL_innerSL`: the trace is invariant under transposition and pullback along a linear
  isometric equivalence, and the trace of the inner product is the dimension.
* `ContinuousLinearMap.traceL_smulRight`: the trace of the rank-one map `f.smulRight A` is `A`
  evaluated at the Riesz representative of `f`.
-/

public section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℝ F]

/-- The metric trace of a continuous bilinear map is bounded by the dimension times its norm. This
is the bound making `TauCeti.traceL` continuous; use `ContinuousLinearMap.norm_traceL_apply_le`. -/
private theorem norm_metricTrace_toLinearMap₁₂_le (H : E →L[ℝ] E →L[ℝ] F) :
    ‖LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ H)‖ ≤
      Module.finrank ℝ E * ‖H‖ := by
  have h := H.norm_sum_apply_apply_le Finset.univ
    (stdOrthonormalBasis ℝ E) (stdOrthonormalBasis ℝ E)
  rw [mul_comm] at h
  simpa [LinearMap.BilinMap.metricTrace_eq_sum _ (stdOrthonormalBasis ℝ E)] using h

/-- The metric trace `H ↦ ∑ᵢ H eᵢ eᵢ` of a continuous bilinear map, as a continuous linear map:
`LinearMap.BilinMap.metricTrace` of the underlying bilinear map, which is bounded by the dimension
of `E` times the norm of `H`. The Laplacian is the trace of the second Fréchet derivative
(`TauCeti.laplacian_eq_traceL`). -/
noncomputable def traceL : (E →L[ℝ] E →L[ℝ] F) →L[ℝ] F :=
  (LinearMap.BilinMap.metricTrace ∘ₗ ContinuousLinearMap.toLinearMap₁₂).mkContinuous
    (Module.finrank ℝ E) fun H : E →L[ℝ] E →L[ℝ] F ↦ norm_metricTrace_toLinearMap₁₂_le H

/-- The continuous trace of a bilinear map is the metric trace of the underlying bilinear map. -/
theorem _root_.ContinuousLinearMap.traceL_apply_eq_metricTrace (H : E →L[ℝ] E →L[ℝ] F) :
    traceL H = LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ H) := by
  rw [traceL, LinearMap.mkContinuous_apply, LinearMap.comp_apply]

/-- The trace of a bilinear map is the sum of its diagonal values on the standard orthonormal
basis. -/
theorem _root_.ContinuousLinearMap.traceL_apply (H : E →L[ℝ] E →L[ℝ] F) :
    traceL H = ∑ i, H (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) := by
  rw [H.traceL_apply_eq_metricTrace,
    LinearMap.BilinMap.metricTrace_eq_sum _ (stdOrthonormalBasis ℝ E)]
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]

/-- The trace of a continuous bilinear map is bounded by the dimension of `E` times its norm:
`‖traceL H‖ ≤ dim E * ‖H‖`. -/
theorem _root_.ContinuousLinearMap.norm_traceL_apply_le (H : E →L[ℝ] E →L[ℝ] F) :
    ‖traceL H‖ ≤ Module.finrank ℝ E * ‖H‖ := by
  rw [H.traceL_apply_eq_metricTrace]
  exact norm_metricTrace_toLinearMap₁₂_le H

/-- Transposing the arguments of a bilinear map preserves its trace. -/
@[simp] theorem _root_.ContinuousLinearMap.traceL_flip (B : E →L[ℝ] E →L[ℝ] F) :
    traceL B.flip = traceL B := by
  rw [B.flip.traceL_apply_eq_metricTrace, B.traceL_apply_eq_metricTrace,
    ContinuousLinearMap.toLinearMap₁₂_flip, LinearMap.BilinMap.metricTrace_flip]

/-- The trace of a continuous bilinear map is invariant under pulling back along a linear
isometric equivalence `e : E ≃ₗᵢ[ℝ] E'`. -/
@[simp] theorem _root_.ContinuousLinearMap.traceL_bilinearComp_linearIsometryEquiv
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    (H : E' →L[ℝ] E' →L[ℝ] F) (e : E ≃ₗᵢ[ℝ] E') :
    traceL (H.bilinearComp (e : E →L[ℝ] E') (e : E →L[ℝ] E')) = traceL H := by
  have he : ((e : E →L[ℝ] E') : E →ₗ[ℝ] E') = e.toLinearEquiv.toLinearMap :=
    LinearMap.ext fun _ ↦ by
      simp only [ContinuousLinearMap.coe_coe, LinearIsometryEquiv.coe_coe'', LinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toLinearEquiv]
  rw [ContinuousLinearMap.traceL_apply_eq_metricTrace,
    ContinuousLinearMap.traceL_apply_eq_metricTrace,
    ContinuousLinearMap.toLinearMap₁₂_bilinearComp, he, ← LinearMap.compl₁₂]
  exact LinearMap.BilinMap.metricTrace_compl₁₂_linearIsometryEquiv H.toLinearMap₁₂ e

/-- The trace of the real inner product is the dimension of the space. -/
@[simp] theorem traceL_innerSL :
    traceL (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) = (Module.finrank ℝ E : ℝ) := by
  rw [ContinuousLinearMap.traceL_apply_eq_metricTrace, ContinuousLinearMap.toLinearMap₁₂_innerSL,
    ← innerₗ, LinearMap.BilinMap.metricTrace_inner]

/-- The trace of the rank-one bilinear map `(v, w) ↦ f v • A w` is `A` evaluated at the Riesz
representative of `f`. -/
@[simp] theorem _root_.ContinuousLinearMap.traceL_smulRight (f : E →L[ℝ] ℝ) (A : E →L[ℝ] F) :
    traceL (f.smulRight A) = A ((InnerProductSpace.toDual ℝ E).symm f) := by
  -- The functional `f` is the inner product with its Riesz representative.
  have hf : innerₗ E ((InnerProductSpace.toDual ℝ E).symm f) = (f : E →ₗ[ℝ] ℝ) :=
    (LinearMap.congr_fun ContinuousLinearMap.toLinearMap₁₂_innerSL _).symm.trans
      (congrArg ContinuousLinearMap.toLinearMap (InnerProductSpace.innerSL_toDual_symm f))
  rw [ContinuousLinearMap.traceL_apply_eq_metricTrace, ContinuousLinearMap.toLinearMap₁₂_smulRight,
    ← hf, LinearMap.BilinMap.metricTrace_innerₗ_smulRight, ContinuousLinearMap.coe_coe]

end TauCeti
