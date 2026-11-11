/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.Orientation

/-!
# Orientation-preserving maps into an oriented vector space

Let `M` be an oriented Riemannian manifold and `F` an oriented real inner product space of the
same dimension, with its constant orientation. A map `f : M → F` preserving orientations at `x`
sends a family of tangent vectors at `x` on which the Riemannian volume form is positive to a
family on which the volume form of `F` is positive, and conversely
(`TauCeti.Manifold.Orientation.IsOrientationPreservingAt.volumeForm_mvfderiv_comp_pos_iff`).

For an oriented Riemannian surface and a map `φ` into `ℂ`, a complex chart for instance, the
volume form of `ℂ` is the area form `(w, z) ↦ Im (conj w * z)`. So `φ` preserves orientations at
`x` only if the pairs of tangent vectors on which the area form is positive are those whose
images `(w, z)` satisfy `0 < Im (conj w * z)`
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

/-- A map `f` from an oriented Riemannian manifold to an oriented inner product space `F`, with
its constant orientation, that preserves orientations at `x` carries families of tangent vectors
on which the Riemannian volume form is positive exactly to families on which the volume form of
`F` is positive. -/
theorem IsOrientationPreservingAt.volumeForm_mvfderiv_comp_pos_iff {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Fact (Module.finrank ℝ F = n)] {o : Manifold.Orientation I M (Fin n)}
    {oF : _root_.Orientation ℝ F (Fin n)} {hn : Fintype.card (Fin n) = Module.finrank ℝ F}
    {f : M → F} {x : M} (hf : IsOrientationPreservingAt o (model (I := 𝓘(ℝ, F)) oF hn) f x)
    (v : Fin n → TangentSpace I x) :
    0 < oF.volumeForm (mvfderiv I f x ∘ v) ↔ 0 < riemannianVolumeForm o x v := by
  let := o.fact_finrank_tangentSpace x
  obtain ⟨e, he, hmap⟩ := (isOrientationPreservingAt_iff _ _ _ _).mp hf
  let e' : TangentSpace I x ≃ₗ[ℝ] F := e.toLinearEquiv
  have hmap' : _root_.Orientation.map (Fin n) e' (o.orientationAt x) = oF :=
    hmap.trans (orientationAt_model _ _ _)
  have hv : mvfderiv I f x ∘ v = e' ∘ v := by
    ext i
    rw [Function.comp_apply, mvfderiv_apply_eq_mfderiv_apply, ← he]
    -- `e'` is `e` viewed as a linear equivalence, so both sides evaluate `e` at `v i`.
    rfl
  rw [riemannianVolumeForm_apply, hv, ← hmap', _root_.Orientation.volumeForm_map_comp_pos_iff]

/-- A map `φ` from an oriented Riemannian surface to `ℂ` that preserves orientations at `x`
carries a pair of tangent vectors on which the area form is positive to a pair `(w, z)` with
`0 < Im (conj w * z)`, and conversely. -/
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
