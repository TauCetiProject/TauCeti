/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Stokes
public import TauCeti.Geometry.Manifold.Riemannian.Boundary
public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Divergence
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Divergence
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.LinearAlgebra.Alternating.Uncurry.Fin
import TauCeti.MeasureTheory.Integral.DivergenceTheorem.HalfSpace
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# Single-chart boundary divergence theorem and boundary volume-form contraction

This module develops the local chart-level ingredients for the Riemannian divergence theorem on a
manifold with boundary modeled on `EuclideanHalfSpace (n + 1)` (`𝓡∂ (n + 1)`), in every dimension
`n ≥ 0` and without global orientability assumptions.

## Main results

* `TauCeti.volumeForm_cons_mfderiv_subtypeVal_boundary`: at a boundary point, evaluating an
  oriented ambient volume form on `u` followed by boundary tangent vectors gives `inner ℝ u N`
  times the outward-first boundary volume form.
* `TauCeti.boundaryRestriction_interior_riemannianVolumeForm`: on an oriented Riemannian manifold
  with boundary, `ι^* (ι_X dV) = ⟪X, N⟫ dS`.
* `TauCeti.Manifold.integral_divergence_eq_boundaryFlux_of_tsupport_subset_chart`: the single-chart
  Riemannian divergence theorem on a half-space chart centered at the boundary or disjoint from the
  boundary.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Proposition
  15.33 and Theorem 16.32.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2.
-/

public section

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Riemannian.Tensor Set
open scoped ContDiff Manifold Matrix Topology

namespace TauCeti

/-! ### Normal contraction of oriented volume forms at the boundary -/

section VolumeFormContraction

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M) :=
  isManifold_boundary M one_ne_zero

/-- **Normal contraction of the volume form at a boundary point.** For any orientation `o` of the
ambient tangent space at a boundary point `x`, evaluating `o.volumeForm` on a vector `u` followed by
the images of boundary tangent vectors `v₀, …, vₙ₋₁` gives `inner ℝ u N` times the volume form of
the outward-first boundary orientation `Orientation.halfSpaceBoundaryOrientation o`, in every
dimension `n ≥ 0`. -/
theorem volumeForm_cons_mfderiv_subtypeVal_boundary
    (x : (𝓡∂ (n + 1)).boundary M)
    [Fact (Module.finrank ℝ (TangentSpace (𝓡∂ (n + 1)) (x : M)) = n + 1)]
    [Fact (Module.finrank ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) = n)]
    (o : Orientation ℝ (TangentSpace (𝓡∂ (n + 1)) (x : M)) (Fin (n + 1)))
    (u : TangentSpace (𝓡∂ (n + 1)) (x : M))
    (v : Fin n → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    o.volumeForm (Fin.cons u fun i ↦
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x (v i)) =
      inner ℝ u (halfSpaceOutwardUnitNormal x) *
        Orientation.volumeForm (E := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)
          (Orientation.halfSpaceBoundaryOrientation o) v := by
  set dι := mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
    (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x
  set N := halfSpaceOutwardUnitNormal x
  set o_b : Orientation ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) (Fin n) :=
    Orientation.halfSpaceBoundaryOrientation o
  let b : OrthonormalBasis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
    (stdOrthonormalBasis ℝ _).reindex (finCongr (by rw [TauCeti.finrank_tangentSpace]; simp))
  have hf_orth : Orthonormal ℝ (Fin.cons N fun i ↦ dι (b i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    refine Fin.cases ?_ (fun i ↦ ?_) i <;> refine Fin.cases ?_ (fun j ↦ ?_) j
    · simp [N, norm_halfSpaceOutwardUnitNormal]
    · simp [N, dι, inner_halfSpaceOutwardUnitNormal_mfderiv_subtypeVal, (Fin.succ_ne_zero j).symm]
    · simp [N, dι, inner_mfderiv_subtypeVal_halfSpaceOutwardUnitNormal]
    · simp only [Fin.cons_succ, Fin.succ_inj]
      rw [← inner_tangentSpace_boundary]
      exact orthonormal_iff_ite.1 b.orthonormal i j
  let b' : OrthonormalBasis (Fin (n + 1)) ℝ (TangentSpace (𝓡∂ (n + 1)) (x : M)) :=
    (basisOfLinearIndependentOfCardEqFinrank hf_orth.linearIndependent
      (by rw [TauCeti.finrank_tangentSpace]; simp)).toOrthonormalBasis
      (by rwa [coe_basisOfLinearIndependentOfCardEqFinrank])
  have hb'_coe : ⇑b'.toBasis = Fin.cons N fun i ↦ dι (b i) := by
    rw [Module.Basis.toBasis_toOrthonormalBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  let η : AlternatingMap ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) ℝ (Fin n) :=
    (o.volumeForm.curryLeft u).compLinearMap dι.toLinearMap
  have hη_apply (w : Fin n → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
      η w = o.volumeForm (Fin.cons u fun i ↦ dι (w i)) := by
    rw [AlternatingMap.compLinearMap_apply, AlternatingMap.curryLeft_apply_apply]; rfl
  have hη_det : η v = η b.toBasis * b.toBasis.det v := by
    simpa only [smul_apply, smul_eq_mul] using
      congrArg (fun L ↦ L v) (η.eq_smul_basis_det b.toBasis)
  have hη_basis : η b.toBasis = inner ℝ u N * o.volumeForm b'.toBasis := by
    have hcons : (Fin.cons u fun i ↦ dι (b.toBasis i)) =
        Matrix.vecCons u ((0 : Fin (n + 1)).removeNth b'.toBasis) := by
      have hrem : (0 : Fin (n + 1)).removeNth b'.toBasis = fun i ↦ dι (b i) := by
        ext i; simp [Fin.removeNth, hb'_coe]
      rw [hrem]; rfl
    have hrepr : b'.toBasis.repr u 0 = inner ℝ u N := by
      rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
        real_inner_comm]
      have hb'0 : b' 0 = N := by
        simpa only [OrthonormalBasis.coe_toBasis, Fin.cons_zero] using congrFun hb'_coe 0
      rw [hb'0]
    rw [hη_apply, hcons, o.volumeForm.map_vecCons_removeNth_basis b'.toBasis u 0, hrepr]; simp
  have hN_neg : (fun w : EuclideanSpace ℝ (Fin (n + 1)) ↦ w 0) N < 0 := by
    have h := (isOutwardPointing_halfSpaceOutwardUnitNormal x).coordinate_deriv_neg
    rwa [mfderiv_extChartAt_self] at h
  have horient : b.toBasis.orientation = o_b ↔ b'.toBasis.orientation = o := by
    refine Orientation.halfSpaceBoundaryOrientation_spec o hN_neg b.toBasis b'.toBasis ?_
    funext k
    refine Fin.cases (congrFun hb'_coe 0) (fun i ↦ ?_) k
    have hi := congrFun hb'_coe i.succ
    simp only [Fin.cons_succ, dι, mfderiv_subtypeVal_boundary, OrthonormalBasis.coe_toBasis] at hi ⊢
    exact hi
  rw [← hη_apply, hη_det, hη_basis]
  by_cases hb : b.toBasis.orientation = o_b
  · rw [o.volumeForm_robust b' (horient.1 hb), b'.toBasis.det_self,
      Orientation.volumeForm_robust (E := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) o_b b hb,
      mul_one]
  · rw [o.volumeForm_robust_neg b' (mt horient.2 hb), neg_apply, b'.toBasis.det_self,
      Orientation.volumeForm_robust_neg
        (E := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) o_b b hb, neg_apply]
    ring

/-- **Pullback of the interior product of the Riemannian volume form to the boundary.** On an
oriented Riemannian manifold with boundary, restricting `ι_X dV` to the boundary gives
`inner ℝ (X x) (N x)` times the Riemannian volume form of the induced boundary orientation, in every
dimension `n ≥ 0`. -/
theorem boundaryRestriction_interior_riemannianVolumeForm
    (o : Manifold.Orientation (𝓡∂ (n + 1)) M (Fin (n + 1)))
    (X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x) (x : (𝓡∂ (n + 1)).boundary M) :
    boundaryRestriction ((riemannianVolumeForm o).interior X) x =
      inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x) •
        riemannianVolumeForm (boundaryOrientation o) x := by
  let _ := o.fact_finrank_tangentSpace (x : M)
  let _ := (boundaryOrientation o).fact_finrank_tangentSpace x
  ext v
  rw [boundaryRestriction_apply, RoughForm.interior_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, riemannianVolumeForm_apply, riemannianVolumeForm_apply,
    orientationAt_boundaryOrientation]
  exact volumeForm_cons_mfderiv_subtypeVal_boundary x (o.orientationAt (x : M)) (X (x : M)) v

end VolumeFormContraction

end TauCeti

namespace TauCeti.Manifold

/-! ### Standard-basis chart volume density and coordinate divergence -/

section StdChartDensity

variable {m : ℕ} {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I 1 N]

private abbrev stdBasis (m : ℕ) : Module.Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)) :=
  (EuclideanSpace.basisFun (Fin m) ℝ).toBasis

private def finBasisReindex (m : ℕ) : Module.Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)) :=
  (Module.finBasis ℝ (EuclideanSpace ℝ (Fin m))).reindex (finCongr finrank_euclideanSpace_fin)

private def stdBasisDet (m : ℕ) : ℝ :=
  |(stdBasis m).det (finBasisReindex m)|

private theorem stdBasisDet_pos (m : ℕ) : 0 < stdBasisDet m :=
  abs_pos.2 ((stdBasis m).isUnit_det (finBasisReindex m)).ne_zero

/-- The Riemannian volume density in the chart frame induced by `EuclideanSpace.basisFun`. -/
private def stdChartVolumeDensity [RiemannianBundle (fun x : N ↦ TangentSpace I x)]
    (α y : N) : ℝ :=
  (stdBasisDet m)⁻¹ * chartVolumeDensity (I := I) α y

private theorem stdChartVolumeDensity_eq_sqrt_det_gram
    [RiemannianBundle (fun x : N ↦ TangentSpace I x)] (α : N) {y : N}
    (hy : y ∈ (trivializationAt (EuclideanSpace ℝ (Fin m)) (TangentSpace I) α).baseSet) :
    stdChartVolumeDensity (I := I) α y =
      √(Matrix.gram ℝ ((trivializationAt (EuclideanSpace ℝ (Fin m)) (TangentSpace I) α).basisAt
        (stdBasis m) hy)).det := by
  set e := trivializationAt (EuclideanSpace ℝ (Fin m)) (TangentSpace I) α
  set σ : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin m))) ≃ Fin m :=
    finCongr finrank_euclideanSpace_fin
  set B_std := e.basisAt (stdBasis m) hy
  set B_fin := e.basisAt (finBasisReindex m) hy
  have hmat : B_std.toMatrix B_fin = (stdBasis m).toMatrix (finBasisReindex m) := by
    ext i j
    simp [Module.Basis.toMatrix_apply, B_std, B_fin, Trivialization.basisAt, e.apply_mk_symm hy]
  have hgram_std : LinearMap.BilinForm.toMatrix B_std (innerₗ (TangentSpace I y)) =
      Matrix.gram ℝ B_std := by
    ext i j; simp [LinearMap.BilinForm.toMatrix_apply, Matrix.gram_apply]
  have hgram_fin : (LinearMap.BilinForm.toMatrix B_fin (innerₗ (TangentSpace I y))).det =
      (chartGramMatrix (I := I) α y).det := by
    have hsub : LinearMap.BilinForm.toMatrix B_fin (innerₗ (TangentSpace I y)) =
        (chartGramMatrix (I := I) α y).submatrix σ.symm σ.symm := by
      rw [← gram_basisAt_finBasis_reindex σ α hy]
      ext i j; simp [LinearMap.BilinForm.toMatrix_apply, Matrix.gram_apply, B_fin,
        finBasisReindex, σ, e]
    rw [hsub, Matrix.det_submatrix_equiv_self]
  have hdet : (chartGramMatrix (I := I) α y).det =
      (stdBasisDet m) ^ 2 * (Matrix.gram ℝ B_std).det := by
    rw [← hgram_fin, ← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix B_std B_fin
        (innerₗ (TangentSpace I y)),
      hgram_std, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hmat,
      ← Module.Basis.det_apply]
    simp only [stdBasisDet, sq_abs]; ring
  rw [stdChartVolumeDensity, chartVolumeDensity_def, hdet, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (stdBasisDet_pos m).le, inv_mul_cancel_left₀ (stdBasisDet_pos m).ne']

@[reducible]
private noncomputable def basisAddHaarOf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    [ms : MeasurableSpace E] [BorelSpace E] : @Measure E ms :=
  b.addHaar

private theorem integral_restrict_basisAddHaarOf_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (ms₁ ms₂ : MeasurableSpace E) (hb₁ : @BorelSpace E _ ms₁) (hb₂ : @BorelSpace E _ ms₂)
    (S : Set E) (g : E → ℝ) :
    ∫ z in S, g z ∂(@basisAddHaarOf E _ _ ι _ b ms₁ hb₁) =
      ∫ z in S, g z ∂(@basisAddHaarOf E _ _ ι _ b ms₂ hb₂) := by
  have heq : ms₁ = ms₂ := hb₁.measurable_eq.trans hb₂.measurable_eq.symm
  subst heq; rfl

private theorem setIntegral_riemannianVolume_std_of_subset
    [MeasurableSpace N] [BorelSpace N] [LindelofSpace N]
    [RiemannianBundle (fun x : N ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin m)) (fun x : N ↦ TangentSpace I x)]
    {α : N} {s : Set N} (hs : s ⊆ (chartAt H α).source) (hs' : MeasurableSet s) (φ : N → ℝ) :
    ∫ x in s, φ x ∂riemannianVolume I N =
      ∫ z in (extChartAt I α) '' s,
        stdChartVolumeDensity (I := I) α ((extChartAt I α).symm z) *
          φ ((extChartAt I α).symm z) ∂volume := by
  have hhaar : (Module.finBasis ℝ (EuclideanSpace ℝ (Fin m))).addHaar =
      ENNReal.ofReal (stdBasisDet m)⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin m))) := by
    rw [← Module.Basis.addHaar_reindex _ (finCongr finrank_euclideanSpace_fin)]
    change (finBasisReindex m).addHaar = _
    rw [Module.Basis.addHaar_eq_smul_of_basis (stdBasis m), stdBasis,
      OrthonormalBasis.addHaar_eq_volume, abs_inv]; rfl
  rw [setIntegral_riemannianVolume_of_subset hs hs' φ]
  simp_rw [smul_eq_mul]
  rw [integral_restrict_basisAddHaarOf_eq (Module.finBasis ℝ (EuclideanSpace ℝ (Fin m)))
      (@extChartAtMeasurableSpaceE (EuclideanSpace ℝ (Fin m)) _) inferInstance
      (@extChartAtBorelSpaceE (EuclideanSpace ℝ (Fin m)) _) inferInstance,
    basisAddHaarOf, hhaar, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.2 (stdBasisDet_pos m).le)]
  simp_rw [smul_eq_mul, ← integral_const_mul, ← mul_assoc, stdChartVolumeDensity]

private theorem mvfderiv_localFrame_eq_fderivWithin {α : N} {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ (extChartAt I α).target) {g : N → ℝ}
    (hg : MDifferentiableAt I 𝓘(ℝ) g ((extChartAt I α).symm z)) (i : Fin m) :
    mvfderiv I g ((extChartAt I α).symm z)
        ((trivializationAt (EuclideanSpace ℝ (Fin m)) (TangentSpace I) α).localFrame
          (stdBasis m) i ((extChartAt I α).symm z)) =
      fderivWithin ℝ (g ∘ (extChartAt I α).symm) (range I) z (stdBasis m i) := by
  have hy : (extChartAt I α).symm z ∈ (chartAt H α).source := by
    rw [← extChartAt_source (I := I)]; exact (extChartAt I α).map_target hz
  have hcomp := mfderiv_comp_mfderivWithin z hg (mdifferentiableWithinAt_extChartAt_symm hz)
    (I.uniqueDiffOn z (extChartAt_target_subset_range α hz)).uniqueMDiffWithinAt
  rw [mfderivWithin_eq_fderivWithin] at hcomp
  rw [← symmL_basis_eq_localFrame _ (by simpa using hy), TangentBundle.symmL_trivializationAt hy,
    (extChartAt I α).right_inv hz, mvfderiv_apply_eq_mfderiv_apply]
  exact (congrArg (fun L ↦ L (stdBasis m i)) hcomp).symm

private theorem stdChartVolumeDensity_mul_divergence [IsManifold I 2 N]
    [RiemannianBundle (fun x : N ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 (EuclideanSpace ℝ (Fin m)) (fun x : N ↦ TangentSpace I x)]
    (α : N) {y : N}
    (hy : y ∈ (trivializationAt (EuclideanSpace ℝ (Fin m)) (TangentSpace I) α).baseSet)
    {X : (x : N) → TangentSpace I x} (hX : MDiffAt (T% X) y) :
    stdChartVolumeDensity (I := I) α y * divergence I X y =
      ∑ i : Fin m, mvfderiv I (fun z ↦ stdChartVolumeDensity (I := I) α z *
        (trivializationAt (EuclideanSpace ℝ (Fin m)) (TangentSpace I) α).localFrameCoeff
          I (stdBasis m) i z (X z)) y
        ((trivializationAt (EuclideanSpace ℝ (Fin m)) (TangentSpace I) α).localFrame
          (stdBasis m) i y) := by
  have : IsManifold I (1 + 1) N := by norm_num; infer_instance
  let _ : ContMDiffVectorBundle 1 (EuclideanSpace ℝ (Fin m)) (TangentSpace I : N → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  set e := trivializationAt (EuclideanSpace ℝ (Fin m)) (TangentSpace I) α
  set b_fin := Module.finBasis ℝ (EuclideanSpace ℝ (Fin m))
  set σ : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin m))) ≃ Fin m :=
    finCongr finrank_euclideanSpace_fin
  let A : Fin m → Fin m → ℝ := fun i j ↦ (stdBasis m).repr (finBasisReindex m j) i
  have hρ : MDiffAt (chartVolumeDensity (I := I) α) y :=
    ((contMDiffOn_chartVolumeDensity (n := 1) α).contMDiffAt
      (e.open_baseSet.mem_nhds hy)).mdifferentiableAt one_ne_zero
  have hfk (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)))) :
      MDiffAt (fun z ↦ chartVolumeDensity (I := I) α z *
        e.localFrameCoeff I b_fin k z (X z)) y :=
    hρ.mul (mdifferentiableAt_localFrameCoeff b_fin hy hX k)
  have hframe (j : Fin m) :
      chartLocalFrame (I := I) α (σ.symm j) y =
        ∑ i : Fin m, A i j • e.localFrame (stdBasis m) i y := by
    rw [chartLocalFrame_eq_symmL, show b_fin (σ.symm j) = finBasisReindex m j by
      simp [b_fin, finBasisReindex, σ]]
    conv_lhs => rw [← (stdBasis m).sum_repr (finBasisReindex m j)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, symmL_basis_eq_localFrame _ hy]
  have hev (i : Fin m) :
      (fun z ↦ stdChartVolumeDensity (I := I) α z *
          e.localFrameCoeff I (stdBasis m) i z (X z)) =ᶠ[𝓝 y]
        fun z ↦ ∑ j : Fin m, ((stdBasisDet m)⁻¹ * A i j) •
          (chartVolumeDensity (I := I) α z *
            e.localFrameCoeff I b_fin (σ.symm j) z (X z)) := by
    filter_upwards [e.open_baseSet.mem_nhds hy] with z hz
    rw [e.localFrameCoeff_apply_of_mem_baseSet (stdBasis m) hz]
    have hw : (e.basisAt (stdBasis m) hz).repr (X z) i =
        ∑ j : Fin m, A i j * (e.basisAt b_fin hz).repr (X z) (σ.symm j) := by
      rw [← Finsupp.lapply_apply (R := ℝ) i]
      conv_lhs => rw [← (e.basisAt (finBasisReindex m) hz).sum_repr (X z)]
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp [A, Trivialization.basisAt, e.apply_mk_symm hz, b_fin, finBasisReindex, σ, mul_comm]
    rw [hw, stdChartVolumeDensity, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← e.localFrameCoeff_apply_of_mem_baseSet (I := I) b_fin hz X (σ.symm j), smul_eq_mul]
    ring
  calc stdChartVolumeDensity (I := I) α y * divergence I X y
      = (stdBasisDet m)⁻¹ * ∑ j : Fin m, mvfderiv I (fun z ↦ chartVolumeDensity (I := I) α z *
          e.localFrameCoeff I b_fin (σ.symm j) z (X z)) y
            (chartLocalFrame (I := I) α (σ.symm j) y) := by
          rw [stdChartVolumeDensity, mul_assoc, chartVolumeDensity_mul_divergence α hy hX]
          congr 1
          exact (Equiv.sum_comp σ.symm fun k ↦ mvfderiv I (fun z ↦ chartVolumeDensity (I := I) α z *
            e.localFrameCoeff I b_fin k z (X z)) y (chartLocalFrame (I := I) α k y)).symm
    _ = ∑ i : Fin m, ∑ j : Fin m, ((stdBasisDet m)⁻¹ * A i j) *
          mvfderiv I (fun z ↦ chartVolumeDensity (I := I) α z *
            e.localFrameCoeff I b_fin (σ.symm j) z (X z)) y (e.localFrame (stdBasis m) i y) := by
          rw [Finset.mul_sum, Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [hframe j, map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_mul]; ring
    _ = _ := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          symm
          rw [(hev i).mvfderiv_eq,
            TauCeti.mvfderiv_fun_sum
              (f := fun j z ↦ ((stdBasisDet m)⁻¹ * A i j) •
                (chartVolumeDensity (I := I) α z *
                  e.localFrameCoeff I b_fin (σ.symm j) z (X z)))
              (fun j _ ↦ (hfk (σ.symm j)).const_smul _),
            sum_apply]
          refine Finset.sum_congr rfl fun j _ ↦ by
            rw [TauCeti.mvfderiv_const_smul (hfk (σ.symm j)), smul_apply, smul_eq_mul]

end StdChartDensity

/-! ### Single-chart divergence theorem on a half-space chart -/

section HalfSpaceChart

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

local instance : IsManifold (𝓡∂ (n + 1)) 1 M :=
  IsManifold.of_le (n := 2) (by norm_num)

local instance : IsManifold (𝓡∂ (n + 1)) (1 + 1) M := by
  rw [one_add_one_eq_two]; infer_instance

local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M) :=
  isManifold_boundary M one_ne_zero

/-- In a boundary-centered chart at `α`, the zeroth standard-frame flux coefficient `ρ X⁰` at a
boundary point `q` equals `-ρ_∂ * inner ℝ (X q) (N q)`, where `ρ_∂` is the standard-frame boundary
chart density. This holds for all `n ≥ 0`. -/
private theorem stdChartVolumeDensity_mul_localFrameCoeff_zero_boundary
    (α q : (𝓡∂ (n + 1)).boundary M)
    (hq : q ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α).source)
    (u : TangentSpace (𝓡∂ (n + 1)) (q : M)) :
    stdChartVolumeDensity (I := 𝓡∂ (n + 1)) (α : M) (q : M) *
      (trivializationAt (EuclideanSpace ℝ (Fin (n + 1))) (TangentSpace (𝓡∂ (n + 1)))
        (α : M)).localFrameCoeff (𝓡∂ (n + 1)) (stdBasis (n + 1)) 0 (q : M) u =
      -(stdChartVolumeDensity (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) α q *
        inner ℝ u (halfSpaceOutwardUnitNormal q)) := by
  let _ : ContMDiffVectorBundle 1 (EuclideanSpace ℝ (Fin (n + 1)))
      (TangentSpace (𝓡∂ (n + 1)) : M → Type _) (𝓡∂ (n + 1)) :=
    TangentBundle.contMDiffVectorBundle
  have _ : Fact (Module.finrank ℝ (TangentSpace (𝓡∂ (n + 1)) (q : M)) = n + 1) :=
    ⟨by rw [TauCeti.finrank_tangentSpace]; simp⟩
  have _ : Fact (Module.finrank ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) = n) :=
    ⟨by rw [TauCeti.finrank_tangentSpace]; simp⟩
  set e' := trivializationAt (EuclideanSpace ℝ (Fin (n + 1))) (TangentSpace (𝓡∂ (n + 1))) (α : M)
  set e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    α
  have hq_chart : q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) α).source := by
    rwa [← extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))]
  have hq'_chart : (q : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) (α : M)).source := by
    simpa only [boundaryChartedSpace_chartAt_source, mem_preimage] using hq_chart
  have hq_base : q ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using hq_chart
  have hq'_base : (q : M) ∈ e'.baseSet := by
    simpa only [e', TangentBundle.trivializationAt_baseSet] using hq'_chart
  set B := e.basisAt (stdBasis n) hq_base
  set B' := e'.basisAt (stdBasis (n + 1)) hq'_base
  set dι := mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
    (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q
  have hdι_B (i : Fin n) : dι (B i) = B' i.succ := by
    have hparam : euclideanHalfSpaceBoundaryParam n (stdBasis n i) = stdBasis (n + 1) i.succ := by
      ext k; refine Fin.cases ?_ (fun j ↦ ?_) k <;>
        simp [stdBasis, euclideanHalfSpaceBoundaryParam_apply_zero,
          euclideanHalfSpaceBoundaryParam_apply_succ, Fin.succ_inj]
    have htcc := congrArg (fun L ↦ L (stdBasis n i))
      (tangentCoordChange_boundaryParam hq (mem_extChartAt_source q))
    simp only [ContinuousLinearMap.comp_apply, hparam] at htcc
    rw [show B i = e.symmL ℝ q (stdBasis n i) from basisAt_apply _ hq_base i,
      show B' i.succ = e'.symmL ℝ (q : M) (stdBasis (n + 1) i.succ) from
        basisAt_apply _ hq'_base i.succ,
      TangentBundle.symmL_trivializationAt_eq_core hq_chart,
      TangentBundle.symmL_trivializationAt_eq_core hq'_chart]
    simp only [tangentBundleCore_coordChange_achart, dι, mfderiv_subtypeVal_boundary]
    exact htcc.symm
  set o_q : _root_.Orientation ℝ (TangentSpace (𝓡∂ (n + 1)) (q : M)) (Fin (n + 1)) :=
    B'.orientation
  set o_b : _root_.Orientation ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) (Fin n) :=
    _root_.Orientation.halfSpaceBoundaryOrientation o_q
  have hlhs : o_q.volumeForm (Fin.cons u fun i ↦ dι (B i)) =
      stdChartVolumeDensity (I := 𝓡∂ (n + 1)) (α : M) (q : M) *
        e'.localFrameCoeff (𝓡∂ (n + 1)) (stdBasis (n + 1)) 0 (q : M) u := by
    have hcons : (Fin.cons u fun i ↦ dι (B i)) =
        Matrix.vecCons u ((0 : Fin (n + 1)).removeNth B') := by
      ext k; refine Fin.cases rfl (fun i ↦ by simp [hdι_B, Fin.tail]) k
    have hcoeff : e'.localFrameCoeff (𝓡∂ (n + 1)) (stdBasis (n + 1)) 0 (q : M) u = B'.repr u 0 :=
      e'.localFrameCoeff_apply_of_mem_baseSet (stdBasis (n + 1)) hq'_base (fun _ ↦ u) 0
    rw [hcons, o_q.volumeForm.map_vecCons_removeNth_basis B' u 0,
      o_q.volumeForm_apply_eq_sqrt_det_gram B' rfl,
      ← stdChartVolumeDensity_eq_sqrt_det_gram (α : M) hq'_base, hcoeff]
    simp [mul_comm]
  have hrhs_vol :
      _root_.Orientation.volumeForm (E := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q)
        o_b B = -stdChartVolumeDensity (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) α q := by
    let w : Fin (n + 1) → ℝˣ := Fin.cons (-1) fun _ ↦ 1
    let B_neg := B'.unitsSMul w
    have hB_neg0 : (fun v : EuclideanSpace ℝ (Fin (n + 1)) ↦ v 0) (B_neg 0) < 0 := by
      have hB0 : B_neg 0 = e'.symmL ℝ (q : M) (-EuclideanSpace.single 0 1) := by
        simp only [B_neg, w, Module.Basis.unitsSMul_apply, Fin.cons_zero, Units.smul_def,
          Units.val_neg, Units.val_one, neg_one_smul, map_neg]
        congr 1
        rw [← show stdBasis (n + 1) 0 = EuclideanSpace.single 0 1 by
          simp [stdBasis, EuclideanSpace.basisFun_apply]]
        exact basisAt_apply (stdBasis (n + 1)) hq'_base 0
      have h := (hB0 ▸ isOutwardPointing_trivializationAt_symmL_neg_single_zero
        hq'_base).coordinate_deriv_neg
      rwa [mfderiv_extChartAt_self] at h
    have hB_neg_orient : B_neg.orientation = -o_q := by
      dsimp only [o_q]
      rw [← B'.orientation_ne_iff_eq_neg, ne_comm, B_neg.orientation_ne_iff_eq_neg,
        B'.orientation_eq_neg_iff_det_neg B_neg, Module.Basis.det_apply]
      have hdiag : B'.toMatrix B_neg = Matrix.diagonal fun k ↦ (w k : ℝ) := by
        ext i j
        rw [Module.Basis.toMatrix_apply, Matrix.diagonal_apply]
        simp only [B_neg, Module.Basis.unitsSMul_apply, Units.smul_def, map_smul,
          Module.Basis.repr_self]
        by_cases hij : i = j <;> simp [hij]
      rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_succ]; simp [w]
    have hB_orient : B.orientation = -o_b := by
      have hspec := _root_.Orientation.halfSpaceBoundaryOrientation_spec (-o_q) hB_neg0 B B_neg (by
        funext k; refine Fin.cases rfl (fun i ↦ ?_) k
        have h1 : B_neg i.succ = B' i.succ := by simp [B_neg, w, Module.Basis.unitsSMul_apply]
        have h2 := (hdι_B i).symm
        simp only [dι, mfderiv_subtypeVal_boundary] at h2
        exact h1.trans h2)
      exact (hspec.2 hB_neg_orient).trans (_root_.Orientation.halfSpaceBoundaryOrientation_neg o_q)
    rw [_root_.Orientation.volumeForm_apply_eq_neg_sqrt_det_gram
        (E := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) o_b B
        (hB_orient ▸ (Module.Ray.ne_neg_self o_b).symm),
      stdChartVolumeDensity_eq_sqrt_det_gram α hq_base]
  have hmain := volumeForm_cons_mfderiv_subtypeVal_boundary q o_q u B
  rw [hlhs, hrhs_vol] at hmain
  linarith

/-- The `i`-th standard-frame flux of `X` in the extended chart at `α`, extended by zero off the
chart target. -/
private def stdChartFluxE (α : M) (X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x)
    (i : Fin (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
  (extChartAt (𝓡∂ (n + 1)) α).target.indicator fun z ↦
    stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α ((extChartAt (𝓡∂ (n + 1)) α).symm z) *
      (trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
        (TangentSpace (𝓡∂ (n + 1))) α).localFrameCoeff
        (𝓡∂ (n + 1)) (stdBasis (n + 1)) i ((extChartAt (𝓡∂ (n + 1)) α).symm z)
        (X ((extChartAt (𝓡∂ (n + 1)) α).symm z))

private theorem stdChartFluxE_eq_zero {α : M} {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (i : Fin (n + 1)) {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : z ∉ extChartAt (𝓡∂ (n + 1)) α '' tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) X) :
    stdChartFluxE α X i z = 0 := by
  by_cases ht : z ∈ (extChartAt (𝓡∂ (n + 1)) α).target
  · have hX0 : X ((extChartAt (𝓡∂ (n + 1)) α).symm z) = 0 :=
      image_eq_zero_of_notMem_tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) fun h ↦
        hz ⟨_, h, (extChartAt (𝓡∂ (n + 1)) α).right_inv ht⟩
    simp only [stdChartFluxE, indicator_of_mem ht, hX0, map_zero, mul_zero]
  · exact indicator_of_notMem ht _

private theorem stdChartFluxE_eventuallyEq_zero {α : M}
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hKc : IsCompact
      (extChartAt (𝓡∂ (n + 1)) α '' tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) X))
    (i : Fin (n + 1)) {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : z ∉ extChartAt (𝓡∂ (n + 1)) α '' tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) X) :
    stdChartFluxE α X i =ᶠ[𝓝 z] 0 :=
  Filter.eventually_of_mem (hKc.isClosed.isOpen_compl.mem_nhds hz) fun _ h ↦
    stdChartFluxE_eq_zero i h

variable [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
  (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

private theorem contMDiffOn_stdChartVolumeDensity_mul_localFrameCoeff {α : M}
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X)) (i : Fin (n + 1)) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) 1 (fun y ↦ stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α y *
      (trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
        (TangentSpace (𝓡∂ (n + 1))) α).localFrameCoeff
        (𝓡∂ (n + 1)) (stdBasis (n + 1)) i y (X y))
      (chartAt (EuclideanHalfSpace (n + 1)) α).source := by
  have hs : (trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
      (TangentSpace (𝓡∂ (n + 1))) α).baseSet =
      (chartAt (EuclideanHalfSpace (n + 1)) α).source := by simp
  rw [← hs]
  exact (contMDiffOn_const.mul (contMDiffOn_chartVolumeDensity (I := 𝓡∂ (n + 1)) (n := 1) α)).mul
    (contMDiffOn_baseSet_localFrameCoeff (I := 𝓡∂ (n + 1))
      (e := trivializationAt (EuclideanSpace ℝ (Fin (n + 1))) (TangentSpace (𝓡∂ (n + 1))) α)
      (stdBasis (n + 1)) (k := 1) hX.contMDiffOn i)

private theorem contDiffOn_stdChartFluxE {α : M} {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hKc : IsCompact
      (extChartAt (𝓡∂ (n + 1)) α '' tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) X))
    (himage : extChartAt (𝓡∂ (n + 1)) α ''
      tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) X ⊆ (extChartAt (𝓡∂ (n + 1)) α).target)
    (i : Fin (n + 1)) :
    ContDiffOn ℝ 1 (stdChartFluxE α X i) (range (𝓡∂ (n + 1))) := by
  intro z _
  by_cases hz : z ∈ (extChartAt (𝓡∂ (n + 1)) α).target
  · have hy : (extChartAt (𝓡∂ (n + 1)) α).symm z ∈
        (chartAt (EuclideanHalfSpace (n + 1)) α).source := by
      rw [← extChartAt_source (I := 𝓡∂ (n + 1))]; exact (extChartAt (𝓡∂ (n + 1)) α).map_target hz
    have hg : ContDiffWithinAt ℝ 1 _ (range (𝓡∂ (n + 1))) z :=
      contMDiffWithinAt_iff_contDiffWithinAt.1
        (((contMDiffOn_stdChartVolumeDensity_mul_localFrameCoeff hX i).contMDiffAt
          ((chartAt _ α).open_source.mem_nhds hy)).comp_contMDiffWithinAt z
            (contMDiffWithinAt_extChartAt_symm_range (n := 1) α hz))
    exact hg.congr_of_eventuallyEq
      (Filter.eventually_of_mem (extChartAt_target_mem_nhdsWithin_of_mem hz) fun _ h ↦
        indicator_of_mem h _) (indicator_of_mem hz _)
  · exact (contDiffAt_const.congr_of_eventuallyEq
      (stdChartFluxE_eventuallyEq_zero hKc i fun h ↦ hz (himage h))).contDiffWithinAt

open scoped Classical in
private theorem sum_fderivWithin_stdChartFluxE {α : M}
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hKc : IsCompact
      (extChartAt (𝓡∂ (n + 1)) α '' tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) X))
    (himage : extChartAt (𝓡∂ (n + 1)) α ''
      tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) X ⊆ (extChartAt (𝓡∂ (n + 1)) α).target)
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz_range : z ∈ range (𝓡∂ (n + 1))) :
    ∑ i : Fin (n + 1), fderivWithin ℝ (stdChartFluxE α X i) (range (𝓡∂ (n + 1))) z
        (stdBasis (n + 1) i) =
      if z ∈ (extChartAt (𝓡∂ (n + 1)) α).target then
        stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α ((extChartAt (𝓡∂ (n + 1)) α).symm z) *
          divergence (𝓡∂ (n + 1)) X ((extChartAt (𝓡∂ (n + 1)) α).symm z)
      else 0 := by
  by_cases hz : z ∈ (extChartAt (𝓡∂ (n + 1)) α).target
  · simp only [hz, ↓reduceIte]
    have hy : (extChartAt (𝓡∂ (n + 1)) α).symm z ∈
        (chartAt (EuclideanHalfSpace (n + 1)) α).source := by
      rw [← extChartAt_source (I := 𝓡∂ (n + 1))]; exact (extChartAt (𝓡∂ (n + 1)) α).map_target hz
    rw [stdChartVolumeDensity_mul_divergence α (by simpa using hy)
      ((hX _).mdifferentiableAt one_ne_zero)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hg : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) _ ((extChartAt (𝓡∂ (n + 1)) α).symm z) :=
      ((contMDiffOn_stdChartVolumeDensity_mul_localFrameCoeff hX i).contMDiffAt
        ((chartAt _ α).open_source.mem_nhds hy)).mdifferentiableAt one_ne_zero
    rw [mvfderiv_localFrame_eq_fderivWithin hz hg i]
    congr 1
    exact Filter.EventuallyEq.fderivWithin_eq
      (Filter.eventually_of_mem (extChartAt_target_mem_nhdsWithin_of_mem hz) fun _ h ↦
        indicator_of_mem h _) (indicator_of_mem hz _)
  · simp only [hz, ↓reduceIte]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have h0 : HasFDerivWithinAt (stdChartFluxE α X i)
        (0 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) (range (𝓡∂ (n + 1))) z :=
      ((hasFDerivAt_const (0 : ℝ) z).congr_of_eventuallyEq
        (stdChartFluxE_eventuallyEq_zero hKc i fun h ↦ hz (himage h))).hasFDerivWithinAt
    simp [h0.fderivWithin ((𝓡∂ (n + 1)).uniqueDiffOn z hz_range)]

variable [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- **Single-chart divergence theorem on a manifold with boundary.** For a compactly supported `C¹`
vector field `X` supported in `(chartAt _ α).source`, where either `α` lies on the boundary or the
support of `X` is disjoint from the boundary, `∫ div X dV = ∫_{∂M} ⟪X, N⟫ dS`. -/
theorem integral_divergence_eq_boundaryFlux_of_tsupport_subset_chart {α : M}
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hK : IsCompact (tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) X))
    (hKs : tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) X ⊆
      (chartAt (EuclideanHalfSpace (n + 1)) α).source)
    (hcase : α ∈ (𝓡∂ (n + 1)).boundary M ∨
      Disjoint (tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) X) ((𝓡∂ (n + 1)).boundary M)) :
    (∫ x, divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      ∫ x : (𝓡∂ (n + 1)).boundary M, inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x)
        ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  classical
  let L := (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
  let B := (EuclideanSpace.equiv (Fin n) ℝ).symm
  let H_set : Set (Fin (n + 1) → ℝ) := {x | 0 ≤ x 0}
  let T_set : Set (EuclideanSpace ℝ (Fin (n + 1))) := range (𝓡∂ (n + 1))
  have hKs' : tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) X ⊆
      (extChartAt (𝓡∂ (n + 1)) α).source := by rwa [extChartAt_source]
  have hKc := hK.image_of_continuousOn ((continuousOn_extChartAt α).mono hKs')
  have himage := ((extChartAt (𝓡∂ (n + 1)) α).mapsTo.mono_left hKs').image_subset
  let f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := fun x i ↦ stdChartFluxE α X i (L x)
  have hL_maps : MapsTo L H_set T_set := fun x hx ↦ by
    simpa [L, H_set, T_set, range_modelWithCornersEuclideanHalfSpace] using hx
  have hf_diff : ContDiffOn ℝ 1 f H_set :=
    contDiffOn_pi.2 fun i ↦ (contDiffOn_stdChartFluxE hX hKc himage i).comp
      L.contDiff.contDiffOn hL_maps
  have hf_supp : HasCompactSupport f := HasCompactSupport.intro (hKc.image L.symm.continuous)
    fun x hx ↦ funext fun i ↦ stdChartFluxE_eq_zero i fun h ↦ hx ⟨L x, h, L.symm_apply_apply x⟩
  obtain ⟨-, -, hdiv_coord⟩ := hf_diff.integral_divergence_coordinate_halfSpace hf_supp
  have hTm : MeasurableSet T_set := by
    dsimp only [T_set]; rw [range_modelWithCornersEuclideanHalfSpace]
    exact (isClosed_le continuous_const (EuclideanSpace.proj 0).continuous).measurableSet
  have hHm : MeasurableSet H_set :=
    (isClosed_le continuous_const (continuous_apply 0)).measurableSet
  have hp := (PiLp.volume_preserving_toLp (Fin (n + 1))).restrict_preimage hTm
  rw [show WithLp.toLp 2 ⁻¹' T_set = H_set by
    ext x; simp [T_set, H_set, range_modelWithCornersEuclideanHalfSpace]] at hp
  have hfderiv_eq (x : Fin (n + 1) → ℝ) (hx : x ∈ H_set) :
      (∑ i : Fin (n + 1), fderivWithin ℝ f H_set x (Pi.single i 1) i) =
        if L x ∈ (extChartAt (𝓡∂ (n + 1)) α).target then
          stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α ((extChartAt (𝓡∂ (n + 1)) α).symm (L x)) *
            divergence (𝓡∂ (n + 1)) X ((extChartAt (𝓡∂ (n + 1)) α).symm (L x))
        else 0 := by
    have huniqH := TauCeti.uniqueDiffOn_pi_halfSpace 0 0 x hx
    rw [← sum_fderivWithin_stdChartFluxE hX hKc himage (hL_maps hx)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hfi := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ)
      i).hasFDerivAt.comp_hasFDerivWithinAt x
        (hf_diff.differentiableOn one_ne_zero x hx).hasFDerivWithinAt).fderivWithin huniqH
    have hL_eq := (((contDiffOn_stdChartFluxE hX hKc himage i).differentiableOn one_ne_zero
      (L x) (hL_maps hx)).hasFDerivWithinAt.comp x
        L.hasFDerivAt.hasFDerivWithinAt hL_maps).fderivWithin huniqH
    have hval := congrArg (fun M_clm ↦ M_clm (Pi.single i 1)) (hfi.symm.trans hL_eq)
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at hval
    have hsingle : L (Pi.single i 1) = stdBasis (n + 1) i := by
      ext j; simp [L, stdBasis, EuclideanSpace.basisFun_apply]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hsingle] using hval
  have hlhs_eq : (∫ x, divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      ∫ x in H_set, ∑ i : Fin (n + 1), fderivWithin ℝ f H_set x (Pi.single i 1) i := by
    let dE : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
      (extChartAt (𝓡∂ (n + 1)) α).target.indicator fun z ↦
        stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α ((extChartAt (𝓡∂ (n + 1)) α).symm z) *
          divergence (𝓡∂ (n + 1)) X ((extChartAt (𝓡∂ (n + 1)) α).symm z)
    have htarget_meas : MeasurableSet (extChartAt (𝓡∂ (n + 1)) α).target := by
      rw [← (extChartAt (𝓡∂ (n + 1)) α).image_source_eq_target]
      exact (isOpen_extChartAt_source α).measurableSet.image_extChartAt α subset_rfl
    calc (∫ x, divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M)
        = ∫ x in (chartAt (EuclideanHalfSpace (n + 1)) α).source,
            divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M :=
            (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
              divergence_eq_zero_of_notMem_tsupport (𝓡∂ (n + 1)) fun h ↦ hx (hKs h)).symm
      _ = ∫ z in (extChartAt (𝓡∂ (n + 1)) α).target,
            stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α ((extChartAt (𝓡∂ (n + 1)) α).symm z) *
              divergence (𝓡∂ (n + 1)) X ((extChartAt (𝓡∂ (n + 1)) α).symm z) ∂volume := by
            rw [setIntegral_riemannianVolume_std_of_subset subset_rfl
              (chartAt _ α).open_source.measurableSet,
              ← extChartAt_source (I := 𝓡∂ (n + 1)),
              (extChartAt (𝓡∂ (n + 1)) α).image_source_eq_target]
      _ = ∫ z in T_set, dE z ∂volume := by
            rw [setIntegral_indicator htarget_meas,
              inter_eq_right.2 (extChartAt_target_subset_range α)]
      _ = ∫ x in H_set, dE (L x) :=
            (hp.integral_comp L.toHomeomorph.measurableEmbedding dE).symm
      _ = _ := setIntegral_congr_fun hHm fun x hx ↦ by
            rw [hfderiv_eq x hx]; exact Set.indicator_apply ..
  have hcons_param (y : Fin n → ℝ) :
      L (Fin.cons 0 y) = euclideanHalfSpaceBoundaryParam n (B y) := by
    ext k; refine Fin.cases ?_ (fun j ↦ ?_) k <;>
      simp [L, B, euclideanHalfSpaceBoundaryParam_apply_zero,
        euclideanHalfSpaceBoundaryParam_apply_succ]
  rw [hlhs_eq, hdiv_coord]
  rcases hcase with hα_bdry | hdisj
  · let _ : LindelofSpace ((𝓡∂ (n + 1)).boundary M) :=
      ((𝓡∂ (n + 1)).isClosed_boundary one_ne_zero).isClosedEmbedding_subtypeVal.LindelofSpace
    let α₀ : (𝓡∂ (n + 1)).boundary M := ⟨α, hα_bdry⟩
    let bE : EuclideanSpace ℝ (Fin n) → ℝ := fun w ↦
      if w ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α₀).target then
        stdChartVolumeDensity (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) α₀
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α₀).symm w) *
          inner ℝ
            (X (((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α₀).symm w :
              (𝓡∂ (n + 1)).boundary M) : M))
            (halfSpaceOutwardUnitNormal
              ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α₀).symm w))
      else 0
    have htrace (y : Fin n → ℝ) : f (Fin.cons 0 y) 0 = -bE (B y) := by
      dsimp only [f, bE]; rw [hcons_param y]
      by_cases hw : B y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α₀).target
      · have hw' : euclideanHalfSpaceBoundaryParam n (B y) ∈
            (extChartAt (𝓡∂ (n + 1)) α).target :=
          (boundaryParam_mem_extChartAt_target_iff α₀ (B y)).2 hw
        set q := (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α₀).symm (B y)
        have hq_src : q ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α₀).source :=
          (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α₀).map_target hw
        have hq'_src : (q : M) ∈ (extChartAt (𝓡∂ (n + 1)) α).source := by
          simpa only [extChartAt_source, boundaryChartedSpace_chartAt_source, mem_preimage]
            using hq_src
        have hsymm_eq : (extChartAt (𝓡∂ (n + 1)) α).symm
            (euclideanHalfSpaceBoundaryParam n (B y)) = (q : M) := by
          rw [← (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α₀).right_inv hw,
            boundaryParam_extChartAt hq_src, (extChartAt (𝓡∂ (n + 1)) α).left_inv hq'_src]
        simp only [hw, ↓reduceIte, stdChartFluxE, indicator_of_mem hw']
        rw [hsymm_eq]
        exact stdChartVolumeDensity_mul_localFrameCoeff_zero_boundary α₀ q hq_src (X (q : M))
      · have hw' : euclideanHalfSpaceBoundaryParam n (B y) ∉
            (extChartAt (𝓡∂ (n + 1)) α).target :=
          mt (boundaryParam_mem_extChartAt_target_iff α₀ (B y)).1 hw
        simp only [hw, ↓reduceIte, stdChartFluxE, indicator_of_notMem hw', neg_zero]
    simp_rw [htrace, integral_neg, neg_neg]
    trans (∫ w, bE w ∂volume)
    · exact (PiLp.volume_preserving_toLp (Fin n)).integral_comp
        B.toHomeomorph.measurableEmbedding bE
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α₀).target)
        (fun w hw ↦ by simp only [bE, hw, ↓reduceIte]),
      halfSpaceBoundaryVolume_eq_riemannianVolume,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := (chartAt (EuclideanSpace ℝ (Fin n)) α₀).source) fun q hq ↦ by
          have hq' : (q : M) ∉ (chartAt (EuclideanHalfSpace (n + 1)) α).source := by
            simpa only [boundaryChartedSpace_chartAt_source, mem_preimage] using hq
          have hX0 : X (q : M) = 0 :=
            image_eq_zero_of_notMem_tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) fun h ↦
              hq' (hKs h)
          simp [hX0],
      setIntegral_riemannianVolume_std_of_subset subset_rfl
        (chartAt (EuclideanSpace ℝ (Fin n)) α₀).open_source.measurableSet,
      ← extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))),
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α₀).image_source_eq_target]
    exact setIntegral_congr_fun (isOpen_extChartAt_target α₀).measurableSet fun w hw ↦ by
      simp only [bE, hw, ↓reduceIte]
  · have htrace_zero (y : Fin n → ℝ) : f (Fin.cons 0 y) 0 = 0 := by
      dsimp only [f]; rw [hcons_param y]
      by_cases hw' : euclideanHalfSpaceBoundaryParam n (B y) ∈
          (extChartAt (𝓡∂ (n + 1)) α).target
      · set p := (extChartAt (𝓡∂ (n + 1)) α).symm (euclideanHalfSpaceBoundaryParam n (B y))
        have hp_src : p ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source := by
          rw [← extChartAt_source (I := 𝓡∂ (n + 1))]
          exact (extChartAt (𝓡∂ (n + 1)) α).map_target hw'
        have hp_bdry : p ∈ (𝓡∂ (n + 1)).boundary M := by
          rw [ModelWithCorners.mem_boundary_euclideanHalfSpace_iff_of_mem_atlas
            (by simp : (2 : ℕ∞ω) ≠ 0) (chart_mem_atlas _ α) hp_src]
          simpa [p, extChartAt, modelWithCornersEuclideanHalfSpace_toFun,
            euclideanHalfSpaceBoundaryParam_apply_zero] using
            congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) ↦ v 0)
              ((extChartAt (𝓡∂ (n + 1)) α).right_inv hw')
        have hX0 : X p = 0 := image_eq_zero_of_notMem_tsupport
          (α := EuclideanSpace ℝ (Fin (n + 1))) (disjoint_right.1 hdisj hp_bdry)
        simp only [stdChartFluxE, indicator_of_mem hw', p, hX0, map_zero, mul_zero]
      · exact indicator_of_notMem hw' _
    have hbdry_zero (q : (𝓡∂ (n + 1)).boundary M) :
        inner ℝ (X (q : M)) (halfSpaceOutwardUnitNormal q) = 0 := by
      have hX0 : X (q : M) = 0 := image_eq_zero_of_notMem_tsupport
        (α := EuclideanSpace ℝ (Fin (n + 1))) (disjoint_right.1 hdisj q.property)
      simp [hX0]
    simp [htrace_zero, hbdry_zero]

end HalfSpaceChart

end TauCeti.Manifold
