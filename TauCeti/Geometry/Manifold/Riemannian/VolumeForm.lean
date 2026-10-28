/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Orientation
public import TauCeti.Geometry.Manifold.DifferentialForm.Basic
public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Basic
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram

/-!
# Riemannian volume forms

An orientation and a Riemannian metric determine a top-degree alternating form on every tangent
space.  This file packages Mathlib's oriented inner-product-space volume form fibrewise, giving the
pointwise object for the manifold divergence and Stokes identities.

The construction is total, as are the rough forms in the differential-form API.  Its defining
characterization is that it evaluates to `1` on every positively oriented orthonormal basis.

For a `C^n` metric on a `C^(n+1)` manifold the volume form is a `C^n` form
(`TauCeti.isSmoothForm_riemannianVolumeForm`): in the frame of a tangent trivialization its value
is `±√(det g)`, the chart volume density `TauCeti.chartVolumeDensity`, with a sign that is
locally constant because the orientation is.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Proposition 15.29.  The normalization on positively oriented orthonormal bases is the
  characterization stated in that proposition.
-/

public section

noncomputable section

open Bundle
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {m : ℕ}

/-- The Riemannian volume form determined by an orientation, defined fibrewise on tangent spaces. -/
noncomputable def riemannianVolumeForm (o : Manifold.Orientation I M (Fin m)) :
    RoughForm I M ℝ m := fun x ↦
  let := o.fact_finrank_tangentSpace x
  (Manifold.Orientation.orientationAt o x).volumeFormL

/-- Unfolding the Riemannian volume form at a point exposes its oriented fibre form. -/
theorem riemannianVolumeForm_def
    (o : Manifold.Orientation I M (Fin m)) (x : M) :
    riemannianVolumeForm o x =
      (letI := o.fact_finrank_tangentSpace x
       (Manifold.Orientation.orientationAt o x).volumeFormL) := by
  simp only [riemannianVolumeForm]

/-- Evaluation of the Riemannian volume form is Mathlib's oriented volume form. -/
@[simp]
theorem riemannianVolumeForm_apply
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (v : Fin m → TangentSpace I x) :
    riemannianVolumeForm o x v =
      (letI := o.fact_finrank_tangentSpace x
       (Manifold.Orientation.orientationAt o x).volumeForm v) := by
  let := o.fact_finrank_tangentSpace x
  simp [riemannianVolumeForm]

/-- The volume form takes value `1` on a positively oriented orthonormal tangent basis. -/
theorem riemannianVolumeForm_apply_orthonormal
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (b : OrthonormalBasis (Fin m) ℝ (TangentSpace I x))
    (hb : b.toBasis.orientation = Manifold.Orientation.orientationAt o x) :
    riemannianVolumeForm o x b = 1 := by
  let := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_def]
  exact Orientation.volumeFormL_apply_orthonormal _ b hb

/-- The Riemannian volume form has absolute value one on every orthonormal basis. -/
theorem abs_riemannianVolumeForm_apply_orthonormal
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (b : OrthonormalBasis (Fin m) ℝ (TangentSpace I x)) :
    |riemannianVolumeForm o x b| = 1 := by
  let := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_def]
  rw [Orientation.volumeFormL_apply]
  exact (Manifold.Orientation.orientationAt o x).abs_volumeForm_apply_of_orthonormal b

/-- The Riemannian volume form is negative on an oppositely oriented orthonormal basis. -/
theorem riemannianVolumeForm_apply_orthonormal_of_opposite
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (b : OrthonormalBasis (Fin m) ℝ (TangentSpace I x))
    (hb : b.toBasis.orientation ≠ Manifold.Orientation.orientationAt o x) :
    riemannianVolumeForm o x b = -1 := by
  let := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_def]
  rw [Orientation.volumeFormL_apply]
  rw [(Manifold.Orientation.orientationAt o x).volumeForm_robust_neg b hb, neg_apply]
  simpa only [OrthonormalBasis.coe_toBasis] using congrArg Neg.neg b.toBasis.det_self

/-- A top form taking value one on an oriented orthonormal basis is the Riemannian volume form. -/
theorem eq_riemannianVolumeForm_of_apply_orthonormal
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (ω : TangentSpace I x [⋀^Fin m]→L[ℝ] ℝ)
    (b : OrthonormalBasis (Fin m) ℝ (TangentSpace I x))
    (hb : b.toBasis.orientation = Manifold.Orientation.orientationAt o x)
    (hω : ω b = 1) :
    ω = riemannianVolumeForm o x := by
  let := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_def]
  exact Orientation.eq_volumeFormL_of_apply_orthonormal _ ω b hb hω

section Smooth

open Filter Module
open scoped Topology

open scoped Classical in
/-- The volume of the frame of a tangent trivialization: at a point `y` of the base set of the
trivialization `e` at `x`, the volume form on the basis `e.basisAt b` of the tangent space, for `b`
a reindexing of the standard basis of the model space, is `±√(det G)`, the chart volume density
up to sign, with sign `+` exactly when the frame is positively oriented. -/
private theorem riemannianVolumeForm_basisAt (o : Manifold.Orientation I M (Fin m))
    (σ : Fin (finrank ℝ E) ≃ Fin m) {x y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    riemannianVolumeForm o y
      ((trivializationAt E (TangentSpace I) x).basisAt ((Module.finBasis ℝ E).reindex σ) hy) =
      if ((Module.finBasis ℝ E).reindex σ).orientation =
          (trivializationAt E (TangentSpace I) x).mapOrientation (Fin m) hy (o.orientationAt y)
        then chartVolumeDensity (I := I) x y
        else -chartVolumeDensity (I := I) x y := by
  set e := trivializationAt E (TangentSpace I) x
  set b := (Module.finBasis ℝ E).reindex σ
  let := o.fact_finrank_tangentSpace y
  have hdet : (Matrix.gram ℝ (e.basisAt b hy)).det =
      (Riemannian.Tensor.chartGramMatrix (I := I) x y).det := by
    rw [Riemannian.Tensor.gram_basisAt_finBasis_reindex, Matrix.det_submatrix_equiv_self]
  have hor : (e.basisAt b hy).orientation = o.orientationAt y ↔
      b.orientation = e.mapOrientation (Fin m) hy (o.orientationAt y) := by
    rw [Trivialization.basisAt, Module.Basis.orientation_map, Trivialization.mapOrientation_apply,
      ← Orientation.map_symm, Equiv.symm_apply_eq]
  rw [riemannianVolumeForm_apply, chartVolumeDensity_def, ← hdet]
  split_ifs with h
  · exact (o.orientationAt y).volumeForm_apply_eq_sqrt_det_gram _ (hor.2 h)
  · exact (o.orientationAt y).volumeForm_apply_eq_neg_sqrt_det_gram _ (mt hor.1 h)

variable {n : WithTop ℕ∞} [IsManifold I (n + 1) M]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]

/-- **The Riemannian volume form is smooth**: for a `C^n` metric on a `C^(n+1)` manifold, the
volume form of an orientation is a `C^n` top form. -/
theorem isSmoothForm_riemannianVolumeForm (o : Manifold.Orientation I M (Fin m)) :
    IsSmoothForm I n (riemannianVolumeForm o) := by
  classical
  rw [isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply]
  intro x v
  set e := trivializationAt E (TangentSpace I) x
  have hm : finrank ℝ E = m := by simpa using o.card_eq.symm
  let σ : Fin (finrank ℝ E) ≃ Fin m := finCongr hm
  let b : Basis (Fin m) ℝ E := (Module.finBasis ℝ E).reindex σ
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hbase : e.baseSet ∈ 𝓝 x := e.open_baseSet.mem_nhds hx
  -- On the base set, the value on `e.symmL y ∘ v` is the volume of the frame `e.basisAt b`
  -- times `b.det v`.
  have hval (y : M) (hy : y ∈ e.baseSet) : riemannianVolumeForm o y (e.symmL ℝ y ∘ v) =
      riemannianVolumeForm o y (e.basisAt b hy) * b.det v := by
    have h := ContinuousAlternatingMap.apply_eq_det_mul
      ((riemannianVolumeForm o y).compContinuousLinearMap (e.symmL ℝ y)) b v
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply] at h
    rw [h, mul_comm]
    congr 2
    funext i
    rw [Function.comp_apply, TauCeti.Manifold.basisAt_apply]
  -- Near `x`, that volume is `±chartVolumeDensity` with a constant sign, since the orientation is
  -- locally constant in the trivialization, and the chart volume density is `C^n`.
  have hρ : ContMDiffAt I 𝓘(ℝ) n (chartVolumeDensity (I := I) x) x :=
    (contMDiffOn_chartVolumeDensity (I := I) x).contMDiffAt hbase
  have hconst := o.toVectorBundleOrientation.eventually_mapOrientation_eq (by simp [hm]) e hx
  simp only [Manifold.Orientation.toVectorBundleOrientation_apply] at hconst
  by_cases hP : b.orientation = e.mapOrientation (Fin m) hx (o.orientationAt x)
  · refine (hρ.mul (contMDiffAt_const (c := b.det v))).congr_of_eventuallyEq ?_
    filter_upwards [hconst, hbase] with y hy hyb
    rw [Pi.mul_apply, hval y hyb, riemannianVolumeForm_basisAt o σ hyb, hy hyb, ite_eq_left hP]
  · refine (hρ.neg.mul (contMDiffAt_const (c := b.det v))).congr_of_eventuallyEq ?_
    filter_upwards [hconst, hbase] with y hy hyb
    rw [Pi.mul_apply, hval y hyb, riemannianVolumeForm_basisAt o σ hyb, hy hyb, ite_eq_right hP]

end Smooth

end TauCeti
