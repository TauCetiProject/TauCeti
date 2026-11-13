/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
public import Mathlib.Analysis.InnerProductSpace.TwoDim

/-!
# Orientation-preserving maps and volume-form positivity

An orientation-preserving map between oriented Riemannian manifolds preserves positivity of
the Riemannian volume form on families of tangent vectors under its derivative, and conversely.

Let `M` be an oriented Riemannian manifold and `F` an oriented real inner product space of the
same dimension, with its constant orientation. If `f : M → F` preserves orientations at `x`,
its derivative `mvfderiv I f x` sends a family of tangent vectors at `x` on which the Riemannian
volume form is positive to a family on which the volume form of `F` is positive, and conversely
(`TauCeti.Manifold.Orientation.IsOrientationPreservingAt.volumeForm_mvfderiv_comp_pos_iff`).

For an oriented Riemannian surface and a map `φ` into `ℂ` with its constant standard orientation
`Complex.orientation`, the volume form of `ℂ` is the area form `(w, z) ↦ Im (conj w * z)`.
If `φ` preserves orientations at `x`, a pair of tangent vectors has positive area form exactly
when its image `(w, z)` under `mvfderiv I φ x` satisfies `0 < Im (conj w * z)`
(`TauCeti.Manifold.Orientation.IsOrientationPreservingAt.im_conj_mvfderiv_mul_pos_iff`).
-/

public section

noncomputable section

open Bundle
open scoped Manifold ComplexConjugate

namespace TauCeti.Manifold.Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The derivative of an orientation-preserving map between oriented Riemannian manifolds
sends a family of tangent vectors to one with positive Riemannian volume form exactly when
the original family has positive Riemannian volume form. -/
theorem IsOrientationPreservingAt.riemannianVolumeForm_mfderiv_comp_pos_iff
    {n : ℕ} {E' H' M' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']
    [RiemannianBundle (fun y : M' ↦ TangentSpace I' y)]
    {o : Manifold.Orientation I M (Fin n)} {o' : Manifold.Orientation I' M' (Fin n)}
    {f : M → M'} {x : M} (hf : IsOrientationPreservingAt o o' f x)
    (v : Fin n → TangentSpace I x) :
    0 < riemannianVolumeForm o' (f x) (mfderiv I I' f x ∘ v) ↔
      0 < riemannianVolumeForm o x v := by
  let := o.fact_finrank_tangentSpace x
  let := o'.fact_finrank_tangentSpace (f x)
  obtain ⟨e, he, hmap⟩ := (isOrientationPreservingAt_iff _ _ _ _).mp hf
  rw [riemannianVolumeForm_apply, riemannianVolumeForm_apply, ← he, ← hmap]
  exact _root_.Orientation.volumeForm_map_comp_pos_iff _ e.toLinearEquiv v

/-- If `f` maps an oriented Riemannian manifold into `F` with its constant orientation `oF`
and preserves orientations at `x`, then `oF.volumeForm (mvfderiv I f x ∘ v)` is positive exactly
when the Riemannian volume form is positive on the family of tangent vectors `v`. -/
theorem IsOrientationPreservingAt.volumeForm_mvfderiv_comp_pos_iff {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Fact (Module.finrank ℝ F = n)] {o : Manifold.Orientation I M (Fin n)}
    {oF : _root_.Orientation ℝ F (Fin n)} {hn : Fintype.card (Fin n) = Module.finrank ℝ F}
    {f : M → F} {x : M} (hf : IsOrientationPreservingAt o (model (I := 𝓘(ℝ, F)) oF hn) f x)
    (v : Fin n → TangentSpace I x) :
    0 < oF.volumeForm (mvfderiv I f x ∘ v) ↔ 0 < riemannianVolumeForm o x v := by
  let o' := model (I := 𝓘(ℝ, F)) oF hn
  let := o'.fact_finrank_tangentSpace (f x)
  have h := hf.riemannianVolumeForm_mfderiv_comp_pos_iff v
  have ht := _root_.Orientation.volumeForm_map_comp_pos_iff (o'.orientationAt (f x))
    (NormedSpace.fromTangentSpace (f x)).toLinearEquiv (mfderiv I 𝓘(ℝ, F) f x ∘ v)
  rw [map_orientationAt_model] at ht
  rw [riemannianVolumeForm_apply] at h
  -- `mvfderiv` composes `mfderiv` with the target's `fromTangentSpace` identification.
  refine Iff.trans ?_ h
  simpa only [mvfderiv, Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.coe_coe] using ht

/-- If `φ` maps an oriented Riemannian surface into `ℂ` with its constant standard orientation
`Complex.orientation` and preserves orientations at `x`, then
`0 < Im (conj (mvfderiv I φ x X) * mvfderiv I φ x Y)` exactly when the area form is positive on
the pair of tangent vectors `(X, Y)`. -/
theorem IsOrientationPreservingAt.im_conj_mvfderiv_mul_pos_iff
    {o : Manifold.Orientation I M (Fin 2)}
    {hn : Fintype.card (Fin 2) = Module.finrank ℝ ℂ} {φ : M → ℂ} {x : M}
    (hφ : IsOrientationPreservingAt o (model (I := 𝓘(ℝ, ℂ)) Complex.orientation hn) φ x)
    (X Y : TangentSpace I x) :
    0 < (conj (mvfderiv I φ x X) * mvfderiv I φ x Y).im ↔
      0 < (letI := o.fact_finrank_tangentSpace x; (o.orientationAt x).areaForm X Y) := by
  let := o.fact_finrank_tangentSpace x
  have : Fact (Module.finrank ℝ ℂ = 2) := Complex.finrank_real_complex_fact
  have h := hφ.volumeForm_mvfderiv_comp_pos_iff ![X, Y]
  rw [riemannianVolumeForm_apply, ← Orientation.areaForm_to_volumeForm] at h
  rw [← h, ← Complex.areaForm, Orientation.areaForm_to_volumeForm]
  congr! 2
  ext i
  fin_cases i <;> rfl

end TauCeti.Manifold.Orientation
