/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Stokes
public import TauCeti.Geometry.Manifold.Riemannian.Boundary
public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Divergence
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Divergence
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.LinearAlgebra.Alternating.Uncurry.Fin
import TauCeti.MeasureTheory.Integral.DivergenceTheorem.HalfSpace
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# The divergence theorem on a Riemannian manifold with boundary

On a smooth manifold `M` with boundary modeled on `EuclideanHalfSpace (n + 1)` (`𝓡∂ (n + 1)`),
carrying a `C¹` Riemannian metric, the divergence of a compactly supported `C¹` vector field `X`
integrates to its outward normal flux across the boundary:

`∫ x, div X x ∂V = ∫ x : ∂M, inner ℝ (X x) (N x) ∂S`,

where `V = TauCeti.riemannianVolume (𝓡∂ (n + 1)) M` is the ambient Riemannian volume measure,
`S = TauCeti.halfSpaceBoundaryVolume` is the Riemannian volume measure of the induced boundary
metric `TauCeti.halfSpaceBoundaryMetric`, and `N = TauCeti.halfSpaceOutwardUnitNormal` is the
unique outward-pointing unit normal along the boundary. No orientability assumption is imposed on
`M`, and every dimension `n ≥ 0` is included: when `n = 0`, `S` is counting measure on the
zero-dimensional boundary.

Substituting `f X` and `f grad g` yields the boundary integration-by-parts formula for the
divergence and Green's first and second identities for the Laplace–Beltrami operator `Δ`:

* `∫ f div X dV = -∫ df(X) dV + ∫_{∂M} f ⟪X, N⟫ dS`,
* `∫ f Δg dV = -∫ ⟪grad f, grad g⟫ dV + ∫_{∂M} f ⟪grad g, N⟫ dS`,
* `∫ (f Δg - (Δf) g) dV = ∫_{∂M} (f ⟪grad g, N⟫ - g ⟪grad f, N⟫) dS`.

When `M` carries an orientation `o`, contracting `X` into the Riemannian volume form `dV_o` and
restricting to `∂M` gives `⟪X, N⟫ dS_{∂o}`
(`TauCeti.boundaryRestriction_interior_riemannianVolumeForm`), identifying the divergence theorem
on oriented manifolds with Stokes' theorem applied to `ι_X dV_o`.

## Main results

* `TauCeti.volumeForm_cons_mfderiv_subtypeVal_boundary`: at a boundary point, evaluating an
  oriented ambient volume form on `u` followed by boundary tangent vectors gives `inner ℝ u N`
  times the outward-first boundary volume form.
* `TauCeti.boundaryRestriction_interior_riemannianVolumeForm`: on an oriented Riemannian manifold
  with boundary, `ι^* (ι_X dV) = ⟪X, N⟫ dS`.
* `TauCeti.Manifold.integrable_boundaryFlux`: the outward normal flux `x ↦ inner ℝ (X x) (N x)` of
  a compactly supported `C¹` vector field is integrable against `halfSpaceBoundaryVolume`.
* `TauCeti.Manifold.integral_divergence_eq_boundaryFlux`: the Riemannian divergence theorem on a
  manifold with boundary without orientability assumptions.
* `TauCeti.Manifold.integral_mul_divergence_eq_boundaryFlux`,
  `TauCeti.Manifold.integral_mul_divergence_eq_boundaryFlux_of_hasCompactSupport_right`:
  integration by parts for the divergence with boundary term.
* `TauCeti.Manifold.integral_laplaceBeltrami_eq_boundaryFlux`,
  `TauCeti.Manifold.integral_mul_laplaceBeltrami_eq_boundaryFlux`,
  `TauCeti.Manifold.integral_mul_laplaceBeltrami_eq_boundaryFlux_of_hasCompactSupport_right`,
  `TauCeti.Manifold.integral_mul_laplaceBeltrami_sub_eq_boundaryFlux`: Green's identities with
  boundary.
* `TauCeti.integralTopForm_mextDeriv_interior_riemannianVolumeForm`: consistency of Stokes' theorem
  for `ι_X dV` with the Riemannian divergence theorem on oriented manifolds.
* `TauCeti.Manifold.integral_divergence_eq_zero_of_isEmpty_boundary`,
  `TauCeti.Manifold.integral_divergence_eq_tsum_boundaryFlux`,
  `TauCeti.Manifold.integral_divergence_eq_sum_boundaryFlux`: empty-boundary and one-dimensional
  (`n = 0`, counting measure) specializations.
* `TauCeti.integrable_divergence_and_boundaryFlux` and
  `TauCeti.integral_divergence_eq_boundaryFlux`: convenience formulations accepting either
  compactness of `M` or compact support of `X`, and any vector field `N` along `∂M` satisfying the
  outward unit normal characterization.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Proposition
  15.33, Theorem 16.32, and Proposition 16.34.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (the Riemannian density and divergence on manifolds with boundary).
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
    (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)).reindex
      (finCongr (by rw [TauCeti.finrank_tangentSpace]; simp))
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
  let b'_bas : Module.Basis (Fin (n + 1)) ℝ (TangentSpace (𝓡∂ (n + 1)) (x : M)) :=
    basisOfLinearIndependentOfCardEqFinrank hf_orth.linearIndependent
      (by rw [TauCeti.finrank_tangentSpace]; simp)
  let b' : OrthonormalBasis (Fin (n + 1)) ℝ (TangentSpace (𝓡∂ (n + 1)) (x : M)) :=
    b'_bas.toOrthonormalBasis (by rwa [coe_basisOfLinearIndependentOfCardEqFinrank])
  have hb'_coe : ⇑b'.toBasis = Fin.cons N fun i ↦ dι (b i) := by
    rw [Module.Basis.toBasis_toOrthonormalBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hremove : (0 : Fin (n + 1)).removeNth b'.toBasis = fun i ↦ dι (b i) := by
    ext i
    simp [Fin.removeNth, hb'_coe]
  let η : AlternatingMap ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) ℝ (Fin n) :=
    (o.volumeForm.curryLeft u).compLinearMap dι.toLinearMap
  have hη_apply (w : Fin n → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
      η w = o.volumeForm (Fin.cons u fun i ↦ dι (w i)) := by
    rw [AlternatingMap.compLinearMap_apply, AlternatingMap.curryLeft_apply_apply]
    rfl
  have hη_det : η v = η b.toBasis * b.toBasis.det v := by
    simpa only [smul_apply, smul_eq_mul] using
      congrArg (fun L ↦ L v) (η.eq_smul_basis_det b.toBasis)
  have hη_basis : η b.toBasis = inner ℝ u N * o.volumeForm b'.toBasis := by
    have hcons : (Fin.cons u fun i ↦ dι (b.toBasis i)) =
        Matrix.vecCons u ((0 : Fin (n + 1)).removeNth b'.toBasis) := by
      rw [hremove]
      rfl
    have hrepr : b'.toBasis.repr u 0 = inner ℝ u N := by
      rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
        real_inner_comm]
      have hb'0 : b' 0 = N := by
        simpa only [OrthonormalBasis.coe_toBasis, Fin.cons_zero] using congrFun hb'_coe 0
      rw [hb'0]
    rw [hη_apply, hcons, o.volumeForm.map_vecCons_removeNth_basis b'.toBasis u 0, hrepr]
    simp
  have hN_neg : (fun w : EuclideanSpace ℝ (Fin (n + 1)) ↦ w 0) N < 0 := by
    have h := (isOutwardPointing_halfSpaceOutwardUnitNormal x).coordinate_deriv_neg
    rwa [mfderiv_extChartAt_self] at h
  have horient : b.toBasis.orientation = o_b ↔ b'.toBasis.orientation = o := by
    refine Orientation.halfSpaceBoundaryOrientation_spec o hN_neg b.toBasis b'.toBasis ?_
    funext k
    refine Fin.cases (congrFun hb'_coe 0) (fun i ↦ ?_) k
    · have hi := congrFun hb'_coe i.succ
      simp only [Fin.cons_succ, dι, mfderiv_subtypeVal_boundary, OrthonormalBasis.coe_toBasis]
        at hi ⊢
      exact hi
  rw [← hη_apply, hη_det, hη_basis]
  by_cases hb : b.toBasis.orientation = o_b
  · have hb' : b'.toBasis.orientation = o := horient.1 hb
    rw [o.volumeForm_robust b' hb', b'.toBasis.det_self,
      Orientation.volumeForm_robust (E := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) o_b b hb,
      mul_one]
  · have hb' : b'.toBasis.orientation ≠ o := mt horient.2 hb
    rw [o.volumeForm_robust_neg b' hb', neg_apply, b'.toBasis.det_self,
      Orientation.volumeForm_robust_neg
        (E := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) o_b b hb,
      neg_apply]
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

/-- The Riemannian boundary volume measure is locally finite: every boundary point has a
neighbourhood in the boundary of finite boundary measure. -/
instance isLocallyFiniteMeasure_halfSpaceBoundaryVolume {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)] :
    IsLocallyFiniteMeasure (halfSpaceBoundaryVolume (n := n) (M := M)) := by
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M) :=
    isManifold_boundary M one_ne_zero
  let _ : LindelofSpace ((𝓡∂ (n + 1)).boundary M) :=
    ((𝓡∂ (n + 1)).isClosed_boundary one_ne_zero).isClosedEmbedding_subtypeVal.LindelofSpace
  rw [halfSpaceBoundaryVolume_eq_riemannianVolume]
  infer_instance

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
  (Module.finBasis ℝ (EuclideanSpace ℝ (Fin m))).reindex (finCongr (finrank_euclideanSpace_fin))

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
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, Matrix.gram_apply]
  have hgram_fin : (LinearMap.BilinForm.toMatrix B_fin (innerₗ (TangentSpace I y))).det =
      (chartGramMatrix (I := I) α y).det := by
    have hsub : LinearMap.BilinForm.toMatrix B_fin (innerₗ (TangentSpace I y)) =
        (chartGramMatrix (I := I) α y).submatrix σ.symm σ.symm := by
      rw [← gram_basisAt_finBasis_reindex σ α hy]
      ext i j
      simp [LinearMap.BilinForm.toMatrix_apply, Matrix.gram_apply, B_fin, finBasisReindex, σ, e]
    rw [hsub, Matrix.det_submatrix_equiv_self]
  have hdet : (chartGramMatrix (I := I) α y).det =
      (stdBasisDet m) ^ 2 * (Matrix.gram ℝ B_std).det := by
    calc (chartGramMatrix (I := I) α y).det
        = (LinearMap.BilinForm.toMatrix B_fin (innerₗ (TangentSpace I y))).det := hgram_fin.symm
      _ = ((stdBasis m).det (finBasisReindex m)) ^ 2 * (Matrix.gram ℝ B_std).det := by
            rw [← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix B_std B_fin
                (innerₗ (TangentSpace I y)),
              hgram_std, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hmat,
              ← Module.Basis.det_apply]
            ring
      _ = (stdBasisDet m) ^ 2 * (Matrix.gram ℝ B_std).det := by
            simp [stdBasisDet, sq_abs]
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
  subst heq
  rfl

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
    have hre : (Module.finBasis ℝ (EuclideanSpace ℝ (Fin m))).addHaar =
        (finBasisReindex m).addHaar := (Module.Basis.addHaar_reindex _ _).symm
    rw [hre, Module.Basis.addHaar_eq_smul_of_basis (stdBasis m), stdBasis,
      OrthonormalBasis.addHaar_eq_volume, abs_inv]
    rfl
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
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I α).map_target hz
  have hy_base : (extChartAt I α).symm z ∈
      (trivializationAt (EuclideanSpace ℝ (Fin m)) (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hy
  have hsymm : MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I
      (extChartAt I α).symm (range I) z :=
    mdifferentiableWithinAt_extChartAt_symm hz
  have huniq : UniqueDiffWithinAt ℝ (range I) z :=
    I.uniqueDiffOn z (extChartAt_target_subset_range α hz)
  have hcomp := mfderiv_comp_mfderivWithin z hg hsymm huniq.uniqueMDiffWithinAt
  rw [mfderivWithin_eq_fderivWithin] at hcomp
  rw [← symmL_basis_eq_localFrame _ hy_base, TangentBundle.symmL_trivializationAt hy,
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
    rw [chartLocalFrame_eq_symmL]
    have hbj : b_fin (σ.symm j) = finBasisReindex m j := by
      simp [b_fin, finBasisReindex, σ]
    rw [hbj]
    conv_lhs => rw [← (stdBasis m).sum_repr (finBasisReindex m j)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, symmL_basis_eq_localFrame _ hy]
  have hev (i : Fin m) :
      (fun z ↦ stdChartVolumeDensity (I := I) α z *
          e.localFrameCoeff I (stdBasis m) i z (X z)) =ᶠ[𝓝 y]
        fun z ↦ ∑ j : Fin m, ((stdBasisDet m)⁻¹ * A i j) •
          (chartVolumeDensity (I := I) α z *
            e.localFrameCoeff I b_fin (σ.symm j) z (X z)) := by
    filter_upwards [e.open_baseSet.mem_nhds hy] with z hz
    rw [e.localFrameCoeff_apply_of_mem_baseSet (stdBasis m) hz]
    have hw : (e.basisAt (stdBasis m) hz).repr (X z) i =
        ∑ j : Fin m, A i j * (e.basisAt (finBasisReindex m) hz).repr (X z) j := by
      rw [← Finsupp.lapply_apply (R := ℝ) i]
      conv_lhs => rw [← (e.basisAt (finBasisReindex m) hz).sum_repr (X z)]
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp [A, Trivialization.basisAt, e.apply_mk_symm hz, mul_comm]
    rw [hw, stdChartVolumeDensity, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hrepr_j : (e.basisAt (finBasisReindex m) hz).repr (X z) j =
        (e.basisAt b_fin hz).repr (X z) (σ.symm j) := by
      simp [Trivialization.basisAt, b_fin, finBasisReindex, σ]
    rw [hrepr_j, ← e.localFrameCoeff_apply_of_mem_baseSet (I := I) b_fin hz X (σ.symm j),
      smul_eq_mul]
    ring
  calc stdChartVolumeDensity (I := I) α y * divergence I X y
      = (stdBasisDet m)⁻¹ * (chartVolumeDensity (I := I) α y * divergence I X y) := by
          rw [stdChartVolumeDensity, mul_assoc]
    _ = (stdBasisDet m)⁻¹ * ∑ j : Fin m, mvfderiv I (fun z ↦ chartVolumeDensity (I := I) α z *
          e.localFrameCoeff I b_fin (σ.symm j) z (X z)) y
            (chartLocalFrame (I := I) α (σ.symm j) y) := by
          rw [chartVolumeDensity_mul_divergence α hy hX]
          congr 1
          exact (Equiv.sum_comp σ.symm fun k ↦ mvfderiv I (fun z ↦ chartVolumeDensity (I := I) α z *
            e.localFrameCoeff I b_fin k z (X z)) y (chartLocalFrame (I := I) α k y)).symm
    _ = ∑ j : Fin m, ∑ i : Fin m, ((stdBasisDet m)⁻¹ * A i j) *
          mvfderiv I (fun z ↦ chartVolumeDensity (I := I) α z *
            e.localFrameCoeff I b_fin (σ.symm j) z (X z)) y (e.localFrame (stdBasis m) i y) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [hframe j, map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [map_smul, smul_eq_mul]
          ring
    _ = ∑ i : Fin m, ∑ j : Fin m, ((stdBasisDet m)⁻¹ * A i j) *
          mvfderiv I (fun z ↦ chartVolumeDensity (I := I) α z *
            e.localFrameCoeff I b_fin (σ.symm j) z (X z)) y (e.localFrame (stdBasis m) i y) :=
          Finset.sum_comm
    _ = _ := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          symm
          rw [(hev i).mvfderiv_eq,
            TauCeti.mvfderiv_fun_sum
              (f := fun j z ↦ ((stdBasisDet m)⁻¹ * A i j) •
                (chartVolumeDensity (I := I) α z *
                  e.localFrameCoeff I b_fin (σ.symm j) z (X z)))
              (fun j _ ↦ (hfk (σ.symm j)).const_smul ((stdBasisDet m)⁻¹ * A i j)),
            sum_apply]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [TauCeti.mvfderiv_const_smul (hfk (σ.symm j)) ((stdBasisDet m)⁻¹ * A i j),
            smul_apply, smul_eq_mul]

end StdChartDensity

/-! ### Integrability of the boundary flux and single-chart divergence theorem -/

section BoundaryFluxIntegrable

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- The outward normal flux `x ↦ inner ℝ (X x) (N x)` of a compactly supported vector field has
compact support on the boundary. -/
theorem hasCompactSupport_boundaryFlux {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hc : HasCompactSupport (β := EuclideanSpace ℝ (Fin (n + 1))) X) :
    HasCompactSupport (fun x : (𝓡∂ (n + 1)).boundary M ↦
      inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x)) := by
  have hclosed :=
    ((𝓡∂ (n + 1)).isClosed_boundary (M := M) one_ne_zero).isClosedEmbedding_subtypeVal
  refine HasCompactSupport.intro' (hclosed.isCompact_preimage hc)
    ((isClosed_tsupport _).preimage continuous_subtype_val) fun x hx ↦ ?_
  have hX0 : X (x : M) = 0 :=
    image_eq_zero_of_notMem_tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) hx
  simp [hX0]

variable [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
  (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- The outward normal flux `x ↦ inner ℝ (X x) (N x)` of a continuous vector field `X` is
continuous on the boundary. -/
theorem continuous_boundaryFlux {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : Continuous (T% X)) :
    Continuous (fun x : (𝓡∂ (n + 1)).boundary M ↦
      inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x)) := by
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M) :=
    isManifold_boundary M one_ne_zero
  have _ : IsManifold (𝓡∂ (n + 1)) (0 + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡∂ (n + 1)) 1 M)
  have h0 : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 0 (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  have hX_bdry : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)).tangent 0
      (fun x : (𝓡∂ (n + 1)).boundary M ↦
        (⟨(x : M), X (x : M)⟩ : TangentBundle (𝓡∂ (n + 1)) M)) :=
    contMDiff_zero_iff.2 (hX.comp continuous_subtype_val)
  have hN_bdry : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)).tangent 0
      (fun x : (𝓡∂ (n + 1)).boundary M ↦
        (⟨(x : M), halfSpaceOutwardUnitNormal x⟩ : TangentBundle (𝓡∂ (n + 1)) M)) :=
    contMDiff_zero_iff.2 continuous_halfSpaceOutwardUnitNormal
  exact (ContMDiff.inner_bundle (h := h0) hX_bdry hN_bdry).continuous

variable [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]

/-- **Integrability of the boundary flux.** The outward normal flux `x ↦ inner ℝ (X x) (N x)` of a
compactly supported continuous vector field is integrable against `halfSpaceBoundaryVolume`. -/
theorem integrable_boundaryFlux_of_continuous {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : Continuous (T% X))
    (hc : HasCompactSupport (β := EuclideanSpace ℝ (Fin (n + 1))) X) :
    Integrable (fun x : (𝓡∂ (n + 1)).boundary M ↦
      inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x))
      (halfSpaceBoundaryVolume (n := n) (M := M)) :=
  (continuous_boundaryFlux hX).integrable_of_hasCompactSupport (hasCompactSupport_boundaryFlux hc)

/-- **Integrability of the boundary flux** for a compactly supported `C¹` vector field. -/
theorem integrable_boundaryFlux {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hc : HasCompactSupport (β := EuclideanSpace ℝ (Fin (n + 1))) X) :
    Integrable (fun x : (𝓡∂ (n + 1)).boundary M ↦
      inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x))
      (halfSpaceBoundaryVolume (n := n) (M := M)) :=
  integrable_boundaryFlux_of_continuous hX.continuous hc

end BoundaryFluxIntegrable

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
      ext k
      refine Fin.cases ?_ (fun j ↦ ?_) k
      · simp [stdBasis, euclideanHalfSpaceBoundaryParam_apply_zero]
      · simp [stdBasis, euclideanHalfSpaceBoundaryParam_apply_succ, Fin.succ_inj]
    have hqq : q ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q).source :=
      mem_extChartAt_source q
    have htcc := congrArg (fun L ↦ L (stdBasis n i)) (tangentCoordChange_boundaryParam hq hqq)
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
      ext k
      refine Fin.cases rfl (fun i ↦ ?_) k
      simp [hdι_B, Fin.tail]
    have hcoeff : e'.localFrameCoeff (𝓡∂ (n + 1)) (stdBasis (n + 1)) 0 (q : M) u = B'.repr u 0 := by
      conv_lhs => rw [← B'.sum_repr u]
      rw [map_sum, Finset.sum_eq_single 0]
      · dsimp only [B']
        simp only [map_smul, localFrameCoeff_basisAt (stdBasis (n + 1)) hq'_base,
          ↓reduceIte, smul_eq_mul, mul_one]
      · intro k _ hk0
        dsimp only [B']
        rw [map_smul, localFrameCoeff_basisAt (stdBasis (n + 1)) hq'_base]
        simp [hk0.symm]
      · simp
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
        have hstd0 : stdBasis (n + 1) 0 = EuclideanSpace.single 0 1 := by
          simp [stdBasis, EuclideanSpace.basisFun_apply]
        rw [← hstd0]
        exact basisAt_apply (stdBasis (n + 1)) hq'_base 0
      have hout : IsOutwardPointing (q : M) (B_neg 0) := by
        have hq'_ext : (q : M) ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).source := by
          rwa [extChartAt_source]
        rw [hB0, isOutwardPointing_iff_tangentCoordChange q.property hq'_ext]
        have hWs : (e'.symmL ℝ (q : M) (-EuclideanSpace.single 0 1) :
            EuclideanSpace ℝ (Fin (n + 1))) =
            tangentCoordChange (𝓡∂ (n + 1)) (α : M) (q : M) (q : M)
              (-EuclideanSpace.single 0 1) :=
          congrArg (fun L ↦ L (-EuclideanSpace.single 0 1))
            (TangentBundle.symmL_trivializationAt_eq_core (I := 𝓡∂ (n + 1)) hq'_chart)
        rw [hWs, tangentCoordChange_comp ⟨⟨hq'_ext, mem_extChartAt_source (q : M)⟩, hq'_ext⟩,
          tangentCoordChange_self hq'_ext]
        simp
      have h := hout.coordinate_deriv_neg
      rwa [mfderiv_extChartAt_self] at h
    have hB_neg_orient : B_neg.orientation = -o_q := by
      dsimp only [o_q]
      rw [← B'.orientation_ne_iff_eq_neg, ne_comm, B_neg.orientation_ne_iff_eq_neg,
        B'.orientation_eq_neg_iff_det_neg B_neg]
      have hdet : B'.det B_neg = ∏ k : Fin (n + 1), (w k : ℝ) := by
        rw [Module.Basis.det_apply]
        have hdiag : B'.toMatrix B_neg = Matrix.diagonal fun k ↦ (w k : ℝ) := by
          ext i j
          rw [Module.Basis.toMatrix_apply, Matrix.diagonal_apply]
          dsimp only [B_neg]
          rw [Module.Basis.unitsSMul_apply, Units.smul_def, map_smul, Module.Basis.repr_self]
          by_cases hij : i = j <;> simp [hij]
        rw [hdiag, Matrix.det_diagonal]
      rw [hdet, Fin.prod_univ_succ]
      simp [w]
    have hB_orient : B.orientation = -o_b := by
      have hspec := _root_.Orientation.halfSpaceBoundaryOrientation_spec (-o_q) hB_neg0 B B_neg (by
        funext k
        refine Fin.cases rfl (fun i ↦ ?_) k
        have h1 : B_neg i.succ = B' i.succ := by simp [B_neg, w, Module.Basis.unitsSMul_apply]
        have h2 := (hdι_B i).symm
        simp only [dι, mfderiv_subtypeVal_boundary] at h2
        exact h1.trans h2)
      have hneg : _root_.Orientation.halfSpaceBoundaryOrientation (-o_q) = -o_b :=
        _root_.Orientation.halfSpaceBoundaryOrientation_neg o_q
      rw [hneg] at hspec
      exact hspec.2 hB_neg_orient
    have hB_ne : B.orientation ≠ o_b := by
      rw [hB_orient]
      exact (Module.Ray.ne_neg_self o_b).symm
    rw [_root_.Orientation.volumeForm_apply_eq_neg_sqrt_det_gram
        (E := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) o_b B hB_ne,
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
  have : IsManifold (𝓡∂ (n + 1)) (1 + 1) M := by norm_num; infer_instance
  have hs : (trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
      (TangentSpace (𝓡∂ (n + 1))) α).baseSet =
      (chartAt (EuclideanHalfSpace (n + 1)) α).source := by simp
  have h1 : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) 1 (stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α)
      (trivializationAt (EuclideanSpace ℝ (Fin (n + 1))) (TangentSpace (𝓡∂ (n + 1))) α).baseSet :=
    contMDiffOn_const.mul (contMDiffOn_chartVolumeDensity (I := 𝓡∂ (n + 1)) (n := 1) α)
  have h2 := contMDiffOn_baseSet_localFrameCoeff (I := 𝓡∂ (n + 1))
    (e := trivializationAt (EuclideanSpace ℝ (Fin (n + 1))) (TangentSpace (𝓡∂ (n + 1))) α)
    (stdBasis (n + 1)) (k := 1) hX.contMDiffOn i
  rw [hs] at h1 h2
  exact h1.mul h2

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
      rw [← extChartAt_source (I := 𝓡∂ (n + 1))]
      exact (extChartAt (𝓡∂ (n + 1)) α).map_target hz
    have hg := ((contMDiffOn_stdChartVolumeDensity_mul_localFrameCoeff hX i).contMDiffAt
      ((chartAt _ α).open_source.mem_nhds hy)).comp_contMDiffWithinAt z
      (contMDiffWithinAt_extChartAt_symm_range (n := 1) α hz)
    have hg' : ContDiffWithinAt ℝ 1 _ (range (𝓡∂ (n + 1))) z :=
      contMDiffWithinAt_iff_contDiffWithinAt.1 hg
    have hev : stdChartFluxE α X i =ᶠ[𝓝[range (𝓡∂ (n + 1))] z] _ :=
      Filter.eventually_of_mem (extChartAt_target_mem_nhdsWithin_of_mem hz) fun z' hz' ↦
        indicator_of_mem hz' _
    exact hg'.congr_of_eventuallyEq hev (indicator_of_mem hz _)
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
      rw [← extChartAt_source (I := 𝓡∂ (n + 1))]
      exact (extChartAt (𝓡∂ (n + 1)) α).map_target hz
    rw [stdChartVolumeDensity_mul_divergence α (by simpa using hy)
      ((hX _).mdifferentiableAt one_ne_zero)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hg : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) _ ((extChartAt (𝓡∂ (n + 1)) α).symm z) :=
      ((contMDiffOn_stdChartVolumeDensity_mul_localFrameCoeff hX i).contMDiffAt
        ((chartAt _ α).open_source.mem_nhds hy)).mdifferentiableAt one_ne_zero
    rw [mvfderiv_localFrame_eq_fderivWithin hz hg i]
    have hev : stdChartFluxE α X i =ᶠ[𝓝[range (𝓡∂ (n + 1))] z] _ :=
      Filter.eventually_of_mem (extChartAt_target_mem_nhdsWithin_of_mem hz) fun z' hz' ↦
        indicator_of_mem hz' _
    rw [hev.fderivWithin_eq (indicator_of_mem hz _), Function.comp_def]
  · simp only [hz, ↓reduceIte]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hev := stdChartFluxE_eventuallyEq_zero hKc i fun h ↦ hz (himage h)
    have hfderiv : fderivWithin ℝ (stdChartFluxE α X i) (range (𝓡∂ (n + 1))) z = 0 := by
      have h0 : HasFDerivWithinAt (stdChartFluxE α X i)
          (0 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) (range (𝓡∂ (n + 1))) z :=
        ((hasFDerivAt_const (0 : ℝ) z).congr_of_eventuallyEq hev).hasFDerivWithinAt
      exact h0.fderivWithin ((𝓡∂ (n + 1)).uniqueDiffOn z hz_range)
    simp [hfderiv]

variable [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- Single-chart divergence theorem on a manifold with boundary: for a compactly supported `C¹`
field `X` supported in `(chartAt _ α).source`, where either `α` lies on the boundary or the support
of `X` is disjoint from the boundary, `∫ div X dV = ∫_{∂M} ⟪X, N⟫ dS`. -/
private theorem integral_divergence_eq_boundaryFlux_of_tsupport_subset_chart {α : M}
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
      (extChartAt (𝓡∂ (n + 1)) α).source := by
    rwa [extChartAt_source]
  have hKc := hK.image_of_continuousOn ((continuousOn_extChartAt α).mono hKs')
  have himage := ((extChartAt (𝓡∂ (n + 1)) α).mapsTo.mono_left hKs').image_subset
  let f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := fun x i ↦ stdChartFluxE α X i (L x)
  have hL_maps : MapsTo L H_set T_set := fun x hx ↦ by
    simpa [L, H_set, T_set, range_modelWithCornersEuclideanHalfSpace] using hx
  have hf_diff : ContDiffOn ℝ 1 f H_set :=
    contDiffOn_pi.2 fun i ↦ (contDiffOn_stdChartFluxE hX hKc himage i).comp
      L.contDiff.contDiffOn hL_maps
  have hf_supp : HasCompactSupport f := by
    refine HasCompactSupport.intro (hKc.image L.symm.continuous) fun x hx ↦ ?_
    ext i
    exact stdChartFluxE_eq_zero i fun h ↦ hx ⟨L x, h, L.symm_apply_apply x⟩
  obtain ⟨-, -, hdiv_coord⟩ := hf_diff.integral_divergence_coordinate_halfSpace hf_supp
  have hTm : MeasurableSet T_set := by
    dsimp only [T_set]
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact (isClosed_le continuous_const (EuclideanSpace.proj 0).continuous).measurableSet
  have hHm : MeasurableSet H_set :=
    (isClosed_le continuous_const (continuous_apply 0)).measurableSet
  have hp := (PiLp.volume_preserving_toLp (Fin (n + 1))).restrict_preimage hTm
  have hpre : WithLp.toLp 2 ⁻¹' T_set = H_set := by
    ext x
    simp [T_set, H_set, range_modelWithCornersEuclideanHalfSpace]
  rw [hpre] at hp
  have hfderiv_eq (x : Fin (n + 1) → ℝ) (hx : x ∈ H_set) :
      (∑ i : Fin (n + 1), fderivWithin ℝ f H_set x (Pi.single i 1) i) =
        if L x ∈ (extChartAt (𝓡∂ (n + 1)) α).target then
          stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α ((extChartAt (𝓡∂ (n + 1)) α).symm (L x)) *
            divergence (𝓡∂ (n + 1)) X ((extChartAt (𝓡∂ (n + 1)) α).symm (L x))
        else 0 := by
    have huniqH : UniqueDiffWithinAt ℝ H_set x := TauCeti.uniqueDiffOn_pi_halfSpace 0 0 x hx
    rw [← sum_fderivWithin_stdChartFluxE hX hKc himage (hL_maps hx)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hf_at := (hf_diff.differentiableOn one_ne_zero x hx).hasFDerivWithinAt
    have hproj :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ) i).hasFDerivAt.comp_hasFDerivWithinAt
        x hf_at
    have hfi : fderivWithin ℝ (fun y ↦ stdChartFluxE α X i (L y)) H_set x =
        (ContinuousLinearMap.proj i).comp (fderivWithin ℝ f H_set x) :=
      hproj.fderivWithin huniqH
    have hflux_at := ((contDiffOn_stdChartFluxE hX hKc himage i).differentiableOn one_ne_zero
      (L x) (hL_maps hx)).hasFDerivWithinAt
    have hL_comp := hflux_at.comp x L.hasFDerivAt.hasFDerivWithinAt hL_maps
    have hL_eq := hL_comp.fderivWithin huniqH
    have hsingle : L (Pi.single i 1) = stdBasis (n + 1) i := by
      ext j
      simp [L, stdBasis, EuclideanSpace.basisFun_apply]
    have hval := congrArg (fun M_clm ↦ M_clm (Pi.single i 1)) (hfi.symm.trans hL_eq)
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at hval
    change fderivWithin ℝ f H_set x (Pi.single i 1) i =
      fderivWithin ℝ (stdChartFluxE α X i) T_set (L x) (L (Pi.single i 1)) at hval
    rwa [hsingle] at hval
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
            divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M := by
            symm
            exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
              divergence_eq_zero_of_notMem_tsupport (𝓡∂ (n + 1)) fun h ↦ hx (hKs h)
      _ = ∫ z in (extChartAt (𝓡∂ (n + 1)) α).target,
            stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α ((extChartAt (𝓡∂ (n + 1)) α).symm z) *
              divergence (𝓡∂ (n + 1)) X ((extChartAt (𝓡∂ (n + 1)) α).symm z) ∂volume := by
            rw [setIntegral_riemannianVolume_std_of_subset subset_rfl
              (chartAt _ α).open_source.measurableSet,
              ← extChartAt_source (I := 𝓡∂ (n + 1)),
              (extChartAt (𝓡∂ (n + 1)) α).image_source_eq_target]
      _ = ∫ z in T_set, dE z ∂volume := by
            symm
            rw [setIntegral_indicator htarget_meas,
              inter_eq_right.2 (extChartAt_target_subset_range α)]
      _ = ∫ x in H_set, dE (L x) :=
            (hp.integral_comp L.toHomeomorph.measurableEmbedding dE).symm
      _ = _ := setIntegral_congr_fun hHm fun x hx ↦ by
            rw [hfderiv_eq x hx]
            by_cases h : L x ∈ (extChartAt (𝓡∂ (n + 1)) α).target
            · simp only [dE, indicator_of_mem h, h, ↓reduceIte]
            · simp only [dE, indicator_of_notMem h, h, ↓reduceIte]
  have hcons_param (y : Fin n → ℝ) :
      L (Fin.cons 0 y) = euclideanHalfSpaceBoundaryParam n (B y) := by
    ext k
    refine Fin.cases ?_ (fun j ↦ ?_) k
    · simp [L, euclideanHalfSpaceBoundaryParam_apply_zero]
    · simp [L, B, euclideanHalfSpaceBoundaryParam_apply_succ]
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
      dsimp only [f, bE]
      rw [hcons_param y]
      by_cases hw : B y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α₀).target
      · have hw' : euclideanHalfSpaceBoundaryParam n (B y) ∈
            (extChartAt (𝓡∂ (n + 1)) α).target :=
          (boundaryParam_mem_extChartAt_target_iff α₀ (B y)).2 hw
        set q : (𝓡∂ (n + 1)).boundary M :=
          (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α₀).symm (B y)
        have hq_src : q ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α₀).source :=
          (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α₀).map_target hw
        have hq'_src : (q : M) ∈ (extChartAt (𝓡∂ (n + 1)) α).source := by
          simpa only [extChartAt_source, boundaryChartedSpace_chartAt_source, mem_preimage]
            using hq_src
        have hsymm_eq : (extChartAt (𝓡∂ (n + 1)) α).symm
            (euclideanHalfSpaceBoundaryParam n (B y)) = (q : M) := by
          have hparam_q : euclideanHalfSpaceBoundaryParam n (B y) =
              extChartAt (𝓡∂ (n + 1)) α (q : M) := by
            rw [← (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α₀).right_inv hw]
            exact boundaryParam_extChartAt hq_src
          rw [hparam_q, (extChartAt (𝓡∂ (n + 1)) α).left_inv hq'_src]
        simp only [hw, ↓reduceIte, stdChartFluxE, indicator_of_mem hw']
        rw [hsymm_eq]
        exact stdChartVolumeDensity_mul_localFrameCoeff_zero_boundary α₀ q hq_src (X (q : M))
      · have hw' : euclideanHalfSpaceBoundaryParam n (B y) ∉
            (extChartAt (𝓡∂ (n + 1)) α).target :=
          mt (boundaryParam_mem_extChartAt_target_iff α₀ (B y)).1 hw
        simp only [hw, ↓reduceIte, stdChartFluxE, indicator_of_notMem hw', neg_zero]
    have hpb := PiLp.volume_preserving_toLp (Fin n)
    have htarget_bdry : MeasurableSet (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α₀).target :=
      (isOpen_extChartAt_target α₀).measurableSet
    simp_rw [htrace, integral_neg, neg_neg]
    trans (∫ w, bE w ∂volume)
    · exact hpb.integral_comp B.toHomeomorph.measurableEmbedding bE
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
    exact setIntegral_congr_fun htarget_bdry fun w hw ↦ by simp only [bE, hw, ↓reduceIte]
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

/-! ### Global divergence theorem and Green's identities with boundary -/

section Global

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- **The Riemannian divergence theorem** on a manifold with boundary: for a compactly supported
`C¹` vector field `X` on a smooth manifold `M` modeled on `𝓡∂ (n + 1)` with a `C¹` Riemannian
metric, the integral of `div X` against the Riemannian volume equals the integral of the outward
normal flux `inner ℝ (X x) (N x)` against the induced boundary Riemannian volume, with no
orientability assumption and in every dimension `n ≥ 0`. -/
theorem integral_divergence_eq_boundaryFlux {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hc : HasCompactSupport (β := EuclideanSpace ℝ (Fin (n + 1))) X) :
    (∫ x, divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      ∫ x : (𝓡∂ (n + 1)).boundary M, inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x)
        ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  classical
  let U : M → Set M := fun i ↦ (chartAt (EuclideanHalfSpace (n + 1)) i).source ∩
    if i ∈ (𝓡∂ (n + 1)).boundary M then univ else ((𝓡∂ (n + 1)).boundary M)ᶜ
  have hclosed_bdry : IsClosed ((𝓡∂ (n + 1)).boundary M) :=
    (𝓡∂ (n + 1)).isClosed_boundary (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hU_open (i : M) : IsOpen (U i) := by
    dsimp only [U]; split_ifs
    · exact (chartAt _ i).open_source.inter isOpen_univ
    · exact (chartAt _ i).open_source.inter hclosed_bdry.isOpen_compl
  have hcover : univ ⊆ ⋃ i, U i := fun x _ ↦ mem_iUnion.2 ⟨x, mem_chart_source _ x, by
    split_ifs with hx <;> simp [hx]⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡∂ (n + 1)) isClosed_univ U
    hU_open hcover
  have hfin := ρ.toPartitionOfUnity.locallyFinite_tsupport.finite_nonempty_inter_compact hc
  set s := hfin.toFinset
  have hmem (i x : M) (hρx : ρ i x ≠ 0) (hXx : X x ≠ 0) : i ∈ s :=
    hfin.mem_toFinset.2 ⟨x, subset_tsupport (ρ i) hρx,
      subset_tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) X hXx⟩
  have hsum (x : M) : X x = ∑ i ∈ s, ρ i x • X x := by
    by_cases hx : X x = 0
    · simp [hx]
    · rw [← Finset.sum_smul, ρ.sum_finsupport' x (mem_univ x) fun i hi ↦ hmem i x
        (by simpa only [SmoothPartitionOfUnity.mem_finsupport, Function.mem_support] using hi) hx,
        one_smul]
  have hY (i : M) : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% (fun x ↦ ρ i x • X x)) :=
    ((ρ i).contMDiff.of_le (by simp)).smul_section hX
  have hK (i : M) : IsCompact
      (tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) (fun x ↦ ρ i x • X x)) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_right _ _)
  have hdiv (x : M) : divergence (𝓡∂ (n + 1)) X x =
      ∑ i ∈ s, divergence (𝓡∂ (n + 1)) (fun x ↦ ρ i x • X x) x := by
    rw [← divergence_finsetSum (𝓡∂ (n + 1)) s _ x fun i _ ↦ (hY i x).mdifferentiableAt one_ne_zero]
    exact congrArg (divergence (𝓡∂ (n + 1)) · x) (funext hsum)
  have hflux (x : (𝓡∂ (n + 1)).boundary M) :
      inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x) =
        ∑ i ∈ s, inner ℝ (ρ i (x : M) • X (x : M)) (halfSpaceOutwardUnitNormal x) := by
    conv_lhs => rw [hsum (x : M)]
    rw [sum_inner]
  rw [integral_congr_ae (Filter.Eventually.of_forall hdiv),
    integral_finsetSum _ fun i _ ↦ integrable_divergence (hY i) (hK i),
    integral_congr_ae (Filter.Eventually.of_forall hflux),
    integral_finsetSum _ fun i _ ↦ integrable_boundaryFlux (hY i) (hK i)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hsub_i : tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) (fun x ↦ ρ i x • X x) ⊆ U i :=
    (tsupport_smul_subset_left _ _).trans (hρ i)
  refine integral_divergence_eq_boundaryFlux_of_tsupport_subset_chart (hY i) (hK i)
    (fun x hx ↦ (hsub_i hx).1) ?_
  by_cases hi : i ∈ (𝓡∂ (n + 1)).boundary M
  · exact Or.inl hi
  · refine Or.inr (disjoint_left.2 fun x hx hxb ↦ ?_)
    have hh := (hsub_i hx).2; simp only [hi, ↓reduceIte] at hh; exact hh hxb

/-- When the boundary of `M` is empty, `TauCeti.Manifold.integral_divergence_eq_boundaryFlux`
recovers vanishing of the integral of the divergence. -/
theorem integral_divergence_eq_zero_of_isEmpty_boundary [IsEmpty ((𝓡∂ (n + 1)).boundary M)]
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hc : HasCompactSupport (β := EuclideanSpace ℝ (Fin (n + 1))) X) :
    ∫ x, divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M = 0 := by
  rw [integral_divergence_eq_boundaryFlux hX hc, integral_of_isEmpty]

private theorem integral_mul_divergence_eq_boundaryFlux_of_integrable {f : M → ℝ}
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 1 f)
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hfXc : HasCompactSupport (β := EuclideanSpace ℝ (Fin (n + 1))) (fun x ↦ f x • X x))
    (hint : Integrable (fun x ↦ f x * divergence (𝓡∂ (n + 1)) X x)
      (riemannianVolume (𝓡∂ (n + 1)) M)) :
    (∫ x, f x * divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      -(∫ x, mvfderiv (𝓡∂ (n + 1)) f x (X x) ∂riemannianVolume (𝓡∂ (n + 1)) M) +
        ∫ x : (𝓡∂ (n + 1)).boundary M,
          f (x : M) * inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x)
          ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  have hfX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% (fun x ↦ f x • X x)) :=
    hf.smul_section hX
  have hpt (x : M) : divergence (𝓡∂ (n + 1)) (fun x ↦ f x • X x) x =
      f x * divergence (𝓡∂ (n + 1)) X x + mvfderiv (𝓡∂ (n + 1)) f x (X x) :=
    divergence_smul_function (𝓡∂ (n + 1)) f X x ((hf x).mdifferentiableAt one_ne_zero)
      ((hX x).mdifferentiableAt one_ne_zero)
  have hint' : Integrable (fun x ↦ mvfderiv (𝓡∂ (n + 1)) f x (X x))
      (riemannianVolume (𝓡∂ (n + 1)) M) :=
    ((integrable_divergence hfX hfXc).sub hint).congr
      (Filter.Eventually.of_forall fun x ↦ by simp only [Pi.sub_apply, hpt]; ring)
  have h := integral_divergence_eq_boundaryFlux hfX hfXc
  simp_rw [real_inner_smul_left] at h
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hint hint'] at h
  linarith

/-- **Integration by parts for the divergence** on a manifold with boundary, when `f` has compact
support: `∫ f div X dV = -∫ df(X) dV + ∫_{∂M} f ⟪X, N⟫ dS`. -/
theorem integral_mul_divergence_eq_boundaryFlux {f : M → ℝ}
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 1 f) (hfc : HasCompactSupport f)
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X)) :
    (∫ x, f x * divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      -(∫ x, mvfderiv (𝓡∂ (n + 1)) f x (X x) ∂riemannianVolume (𝓡∂ (n + 1)) M) +
        ∫ x : (𝓡∂ (n + 1)).boundary M,
          f (x : M) * inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x)
          ∂halfSpaceBoundaryVolume (n := n) (M := M) :=
  integral_mul_divergence_eq_boundaryFlux_of_integrable hf hX
    (hfc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left _ _))
    ((hf.continuous.mul (contMDiff_divergence (n := 0) (m := 2) (k := 1) (by norm_num)
      (by norm_num) (by simpa using hX)).continuous).integrable_of_hasCompactSupport hfc.mul_right)

/-- **Integration by parts for the divergence** on a manifold with boundary, when `X` has compact
support: `∫ f div X dV = -∫ df(X) dV + ∫_{∂M} f ⟪X, N⟫ dS`. -/
theorem integral_mul_divergence_eq_boundaryFlux_of_hasCompactSupport_right {f : M → ℝ}
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 1 f)
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hXc : HasCompactSupport (β := EuclideanSpace ℝ (Fin (n + 1))) X) :
    (∫ x, f x * divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      -(∫ x, mvfderiv (𝓡∂ (n + 1)) f x (X x) ∂riemannianVolume (𝓡∂ (n + 1)) M) +
        ∫ x : (𝓡∂ (n + 1)).boundary M,
          f (x : M) * inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x)
          ∂halfSpaceBoundaryVolume (n := n) (M := M) :=
  integral_mul_divergence_eq_boundaryFlux_of_integrable hf hX
    (hXc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_right _ _))
    ((hf.continuous.mul (contMDiff_divergence (n := 0) (m := 2) (k := 1) (by norm_num)
      (by norm_num) (by simpa using hX)).continuous).integrable_of_hasCompactSupport
      (hXc.divergence (𝓡∂ (n + 1))).mul_left)

/-- For a compactly supported `C²` function `f` on a manifold with boundary, the integral of its
Laplace–Beltrami operator `Δf` equals the boundary integral of its outward normal derivative
`inner ℝ (grad f) N`. -/
theorem integral_laplaceBeltrami_eq_boundaryFlux {f : M → ℝ}
    (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 2 f) (hfc : HasCompactSupport f) :
    (∫ x, laplaceBeltrami (𝓡∂ (n + 1)) f x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      ∫ x : (𝓡∂ (n + 1)).boundary M,
        inner ℝ (mgradient (𝓡∂ (n + 1)) f (x : M)) (halfSpaceOutwardUnitNormal x)
        ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  have : IsManifold (𝓡∂ (n + 1)) (1 + 1) M := by rw [one_add_one_eq_two]; infer_instance
  simp only [laplaceBeltrami_def]
  exact integral_divergence_eq_boundaryFlux
    (contMDiff_mgradient (n := 1) (by rwa [one_add_one_eq_two])) (hfc.mgradient (𝓡∂ (n + 1)))

/-- **Green's first identity** on a manifold with boundary, when `f` has compact support: for a
compactly supported `C¹` function `f` and a `C²` function `g`,
`∫ f Δg dV = -∫ ⟪grad f, grad g⟫ dV + ∫_{∂M} f ⟪grad g, N⟫ dS`. -/
theorem integral_mul_laplaceBeltrami_eq_boundaryFlux {f g : M → ℝ}
    (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 1 f) (hfc : HasCompactSupport f)
    (hg : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 2 g) :
    (∫ x, f x * laplaceBeltrami (𝓡∂ (n + 1)) g x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      -(∫ x, inner ℝ (mgradient (𝓡∂ (n + 1)) f x) (mgradient (𝓡∂ (n + 1)) g x)
          ∂riemannianVolume (𝓡∂ (n + 1)) M) +
        ∫ x : (𝓡∂ (n + 1)).boundary M,
          f (x : M) * inner ℝ (mgradient (𝓡∂ (n + 1)) g (x : M)) (halfSpaceOutwardUnitNormal x)
          ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  have : IsManifold (𝓡∂ (n + 1)) (1 + 1) M := by rw [one_add_one_eq_two]; infer_instance
  simp_rw [laplaceBeltrami_def]
  rw [integral_mul_divergence_eq_boundaryFlux hf hfc
    (contMDiff_mgradient (n := 1) (by rwa [one_add_one_eq_two]))]
  congr 2
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun x ↦
      (inner_mgradient (I := 𝓡∂ (n + 1)) (f := f) (x := x) _).symm)

/-- **Green's first identity** on a manifold with boundary, when `g` has compact support: for a
`C¹` function `f` and a compactly supported `C²` function `g`,
`∫ f Δg dV = -∫ ⟪grad f, grad g⟫ dV + ∫_{∂M} f ⟪grad g, N⟫ dS`. -/
theorem integral_mul_laplaceBeltrami_eq_boundaryFlux_of_hasCompactSupport_right {f g : M → ℝ}
    (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 1 f)
    (hg : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 2 g) (hgc : HasCompactSupport g) :
    (∫ x, f x * laplaceBeltrami (𝓡∂ (n + 1)) g x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      -(∫ x, inner ℝ (mgradient (𝓡∂ (n + 1)) f x) (mgradient (𝓡∂ (n + 1)) g x)
          ∂riemannianVolume (𝓡∂ (n + 1)) M) +
        ∫ x : (𝓡∂ (n + 1)).boundary M,
          f (x : M) * inner ℝ (mgradient (𝓡∂ (n + 1)) g (x : M)) (halfSpaceOutwardUnitNormal x)
          ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  have : IsManifold (𝓡∂ (n + 1)) (1 + 1) M := by rw [one_add_one_eq_two]; infer_instance
  simp_rw [laplaceBeltrami_def]
  rw [integral_mul_divergence_eq_boundaryFlux_of_hasCompactSupport_right hf
    (contMDiff_mgradient (n := 1) (by rwa [one_add_one_eq_two])) (hgc.mgradient (𝓡∂ (n + 1)))]
  congr 2
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun x ↦
      (inner_mgradient (I := 𝓡∂ (n + 1)) (f := f) (x := x) _).symm)

/-- **Green's second identity** on a manifold with boundary [Lee, Proposition 16.34(b)]: for a
compactly supported `C²` function `f` and a `C²` function `g`,
`∫ (f Δg - (Δf) g) dV = ∫_{∂M} (f ⟪grad g, N⟫ - g ⟪grad f, N⟫) dS`. -/
theorem integral_mul_laplaceBeltrami_sub_eq_boundaryFlux {f g : M → ℝ}
    (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 2 f) (hfc : HasCompactSupport f)
    (hg : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 2 g) :
    (∫ x, (f x * laplaceBeltrami (𝓡∂ (n + 1)) g x - laplaceBeltrami (𝓡∂ (n + 1)) f x * g x)
        ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      ∫ x : (𝓡∂ (n + 1)).boundary M,
        (f (x : M) * inner ℝ (mgradient (𝓡∂ (n + 1)) g (x : M)) (halfSpaceOutwardUnitNormal x) -
          g (x : M) * inner ℝ (mgradient (𝓡∂ (n + 1)) f (x : M)) (halfSpaceOutwardUnitNormal x))
        ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  have : IsManifold (𝓡∂ (n + 1)) (1 + 1) M := by rw [one_add_one_eq_two]; infer_instance
  have hf1 : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 1 f := hf.of_le (by norm_num)
  have hg1 : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 1 g := hg.of_le (by norm_num)
  have hgradf : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% (mgradient (𝓡∂ (n + 1)) f)) :=
    contMDiff_mgradient (n := 1) (by rwa [one_add_one_eq_two])
  have hgradg : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% (mgradient (𝓡∂ (n + 1)) g)) :=
    contMDiff_mgradient (n := 1) (by rwa [one_add_one_eq_two])
  have hint_fΔg : Integrable (fun x ↦ f x * laplaceBeltrami (𝓡∂ (n + 1)) g x)
      (riemannianVolume (𝓡∂ (n + 1)) M) := by
    simp only [laplaceBeltrami_def]
    exact (hf1.continuous.mul (contMDiff_divergence (n := 0) (m := 2) (k := 1) (by norm_num)
      (by norm_num) (by simpa using hgradg)).continuous).integrable_of_hasCompactSupport
      hfc.mul_right
  have hint_Δfg : Integrable (fun x ↦ laplaceBeltrami (𝓡∂ (n + 1)) f x * g x)
      (riemannianVolume (𝓡∂ (n + 1)) M) := by
    simp only [laplaceBeltrami_def]
    have h : Integrable (fun x ↦ g x * divergence (𝓡∂ (n + 1)) (mgradient (𝓡∂ (n + 1)) f) x)
        (riemannianVolume (𝓡∂ (n + 1)) M) :=
      (hg1.continuous.mul (contMDiff_divergence (n := 0) (m := 2) (k := 1) (by norm_num)
        (by norm_num) (by simpa using hgradf)).continuous).integrable_of_hasCompactSupport
        ((hfc.mgradient (𝓡∂ (n + 1))).divergence (𝓡∂ (n + 1))).mul_left
    exact h.congr (Filter.Eventually.of_forall fun x ↦ mul_comm _ _)
  have hbdry_f : Integrable (fun x : (𝓡∂ (n + 1)).boundary M ↦
      f (x : M) * inner ℝ (mgradient (𝓡∂ (n + 1)) g (x : M)) (halfSpaceOutwardUnitNormal x))
      (halfSpaceBoundaryVolume (n := n) (M := M)) := by
    have hsmul := integrable_boundaryFlux (X := fun x ↦ f x • mgradient (𝓡∂ (n + 1)) g x)
      (hf1.smul_section hgradg)
      (hfc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left _ _))
    simpa only [real_inner_smul_left] using hsmul
  have hbdry_g : Integrable (fun x : (𝓡∂ (n + 1)).boundary M ↦
      g (x : M) * inner ℝ (mgradient (𝓡∂ (n + 1)) f (x : M)) (halfSpaceOutwardUnitNormal x))
      (halfSpaceBoundaryVolume (n := n) (M := M)) := by
    have hsmul := integrable_boundaryFlux (X := fun x ↦ g x • mgradient (𝓡∂ (n + 1)) f x)
      (hg1.smul_section hgradf)
      ((hfc.mgradient (𝓡∂ (n + 1))).of_isClosed_subset (isClosed_tsupport _)
        (tsupport_smul_subset_right _ _))
    simpa only [real_inner_smul_left] using hsmul
  have h1 := integral_mul_laplaceBeltrami_eq_boundaryFlux hf1 hfc hg
  have h2 := integral_mul_laplaceBeltrami_eq_boundaryFlux_of_hasCompactSupport_right hg1 hf hfc
  have hcomm : (∫ x, inner ℝ (mgradient (𝓡∂ (n + 1)) g x) (mgradient (𝓡∂ (n + 1)) f x)
        ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      ∫ x, inner ℝ (mgradient (𝓡∂ (n + 1)) f x) (mgradient (𝓡∂ (n + 1)) g x)
        ∂riemannianVolume (𝓡∂ (n + 1)) M :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ real_inner_comm _ _)
  have hmul : (∫ x, laplaceBeltrami (𝓡∂ (n + 1)) f x * g x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      ∫ x, g x * laplaceBeltrami (𝓡∂ (n + 1)) f x ∂riemannianVolume (𝓡∂ (n + 1)) M :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ mul_comm _ _)
  rw [integral_sub hint_fΔg hint_Δfg, integral_sub hbdry_f hbdry_g, hmul, h1, h2, hcomm]
  ring

end Global

/-! ### One-dimensional specialization (`n = 0`) -/

section OneDim

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace 1) M]
  [IsManifold (𝓡∂ 1) ∞ M] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ 1) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ 1) 1 (EuclideanSpace ℝ (Fin 1))
    (fun x : M ↦ TangentSpace (𝓡∂ 1) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 1))
    (fun x : M ↦ TangentSpace (𝓡∂ 1) x)]

/-- On a one-dimensional Riemannian manifold with boundary (`n = 0`), the integral of `div X` is
the series of outward normal fluxes `inner ℝ (X x) (N x)` over all boundary points, because
`halfSpaceBoundaryVolume` is counting measure. -/
theorem integral_divergence_eq_tsum_boundaryFlux {X : (x : M) → TangentSpace (𝓡∂ 1) x}
    (hX : ContMDiff (𝓡∂ 1) (𝓡∂ 1).tangent 1 (T% X))
    (hc : HasCompactSupport (β := EuclideanSpace ℝ (Fin 1)) X) :
    (∫ x, divergence (𝓡∂ 1) X x ∂riemannianVolume (𝓡∂ 1) M) =
      ∑' x : (𝓡∂ 1).boundary M, inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x) := by
  let _ : LindelofSpace ((𝓡∂ 1).boundary M) :=
    ((𝓡∂ 1).isClosed_boundary (by simp : (∞ : ℕ∞ω) ≠ 0)).isClosedEmbedding_subtypeVal.LindelofSpace
  have : DiscreteTopology ((𝓡∂ 1).boundary M) := discreteTopology_iff_isOpen_singleton.2 fun x ↦ by
    have hs : (chartAt (EuclideanSpace ℝ (Fin 0)) x).source = {x} := Set.ext fun y ↦
      ⟨fun hy ↦ (chartAt _ x).injOn hy (mem_chart_source _ x) (Subsingleton.elim _ _),
        fun hy ↦ hy.symm ▸ mem_chart_source _ x⟩
    exact hs ▸ (chartAt _ x).open_source
  have : Countable ((𝓡∂ 1).boundary M) := by
    obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover
      (fun x : (𝓡∂ 1).boundary M ↦ ({x} : Set ((𝓡∂ 1).boundary M)))
      fun x ↦ (isOpen_discrete {x}).mem_nhds rfl
    exact countable_univ_iff.1 (hcover ▸ ht.biUnion fun x _ ↦ countable_singleton x)
  have : MeasurableSingletonClass ((𝓡∂ 1).boundary M) :=
    ⟨fun x ↦ (isOpen_discrete {x}).measurableSet⟩
  have hint := integrable_boundaryFlux (n := 0) hX hc
  rw [integral_divergence_eq_boundaryFlux (n := 0) hX hc]
  rw [halfSpaceBoundaryVolume_zero_eq_count] at hint ⊢
  rw [integral_countable hint]
  refine tsum_congr fun x ↦ ?_
  rw [measureReal_def, Measure.count_singleton' (measurableSet_singleton x), ENNReal.toReal_one,
    one_smul]

/-- On a one-dimensional Riemannian manifold with finite boundary (`n = 0`), the integral of
`div X` is the finite sum of outward normal fluxes `inner ℝ (X x) (N x)` at the boundary
endpoints. -/
theorem integral_divergence_eq_sum_boundaryFlux [Fintype ((𝓡∂ 1).boundary M)]
    {X : (x : M) → TangentSpace (𝓡∂ 1) x}
    (hX : ContMDiff (𝓡∂ 1) (𝓡∂ 1).tangent 1 (T% X))
    (hc : HasCompactSupport (β := EuclideanSpace ℝ (Fin 1)) X) :
    (∫ x, divergence (𝓡∂ 1) X x ∂riemannianVolume (𝓡∂ 1) M) =
      ∑ x : (𝓡∂ 1).boundary M, inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x) := by
  rw [integral_divergence_eq_tsum_boundaryFlux hX hc, tsum_fintype]

end OneDim

end TauCeti.Manifold

namespace TauCeti

/-! ### Oriented consistency with Stokes' theorem and convenience API -/

section OrientedStokes

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M) :=
  isManifold_boundary M one_ne_zero

/-- **Stokes' theorem for `ι_X dV` agrees with the Riemannian divergence theorem.** On an oriented
smooth Riemannian manifold with boundary, the top-form integral of `d(ι_X dV)` equals
`∫ div X dV`, the boundary top-form integral of `ι^*(ι_X dV)` equals `∫_{∂M} ⟪X, N⟫ dS`, and both
are equal by Stokes' theorem. -/
theorem integralTopForm_mextDeriv_interior_riemannianVolumeForm
    (o : Manifold.Orientation (𝓡∂ (n + 1)) M (Fin (n + 1)))
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hc : HasCompactSupport (β := EuclideanSpace ℝ (Fin (n + 1))) X) :
    integralTopForm o (mextDeriv ((riemannianVolumeForm o).interior X)) =
        (∫ x, Manifold.divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M) ∧
      integralTopForm (boundaryOrientation o)
          (boundaryRestriction ((riemannianVolumeForm o).interior X)) =
        ∫ x : (𝓡∂ (n + 1)).boundary M, inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x)
          ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  let _ : LindelofSpace ((𝓡∂ (n + 1)).boundary M) :=
    ((𝓡∂ (n + 1)).isClosed_boundary one_ne_zero).isClosedEmbedding_subtypeVal.LindelofSpace
  refine ⟨?_, ?_⟩
  · rw [mextDeriv_interior_riemannianVolumeForm o (hX.mdifferentiable one_ne_zero)]
    exact integralTopForm_smul_riemannianVolumeForm o
      (Manifold.contMDiff_divergence (n := 0) (m := 2) (k := 1) (by norm_num) (by norm_num)
        (by simpa using hX)).continuous
      (hc.divergence (𝓡∂ (n + 1)))
  · have hbdry : boundaryRestriction ((riemannianVolumeForm o).interior X) =
        fun x : (𝓡∂ (n + 1)).boundary M ↦
          inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x) •
            riemannianVolumeForm (boundaryOrientation o) x :=
      funext (boundaryRestriction_interior_riemannianVolumeForm o X)
    rw [hbdry, halfSpaceBoundaryVolume_eq_riemannianVolume]
    exact integralTopForm_smul_riemannianVolumeForm (boundaryOrientation o)
      (Manifold.continuous_boundaryFlux hX.continuous)
      (Manifold.hasCompactSupport_boundaryFlux hc)

end OrientedStokes

section ConvenienceAPI

private theorem hasCompactSupport_of_isCompact_univ_or_exists_compact {n : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hSupport : IsCompact (univ : Set M) ∨ ∃ K : Set M, IsCompact K ∧ ∀ x ∉ K, X x = 0) :
    HasCompactSupport (β := EuclideanSpace ℝ (Fin (n + 1))) X := by
  rcases hSupport with huniv | ⟨K, hK, hzero⟩
  · have : CompactSpace M := ⟨huniv⟩
    exact HasCompactSupport.of_compactSpace _
  · exact HasCompactSupport.intro hK hzero

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M] [SigmaCompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- **Integrability of the divergence and outward boundary flux** under either compactness of `M`
or compact support of `X`, for any boundary vector field `N` satisfying the outward unit normal
characterization. -/
theorem integrable_divergence_and_boundaryFlux {k : ℕ∞ω} {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent k (T% X))
    (hSupport : IsCompact (univ : Set M) ∨ ∃ K : Set M, IsCompact K ∧ ∀ x ∉ K, X x = 0)
    {N : (x : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (x : M)}
    (hN : ∀ x, ‖N x‖ = 1 ∧ IsOutwardPointing (x : M) (N x) ∧
      ∀ w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x,
        inner ℝ (N x) (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) Subtype.val x w) = 0)
    (hk : 1 ≤ k := by simp) :
    Integrable (Manifold.divergence (𝓡∂ (n + 1)) X) (riemannianVolume (𝓡∂ (n + 1)) M) ∧
      Integrable (fun x : (𝓡∂ (n + 1)).boundary M ↦ inner ℝ (X (x : M)) (N x))
        (halfSpaceBoundaryVolume (n := n) (M := M)) := by
  have hX1 : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X) := hX.of_le hk
  have hc := hasCompactSupport_of_isCompact_univ_or_exists_compact hSupport
  have hNeq : N = halfSpaceOutwardUnitNormal :=
    funext fun x ↦ eq_halfSpaceOutwardUnitNormal_of_norm_eq_one (hN x).1 (hN x).2.1 (hN x).2.2
  subst hNeq
  exact ⟨Manifold.integrable_divergence hX1 hc, Manifold.integrable_boundaryFlux hX1 hc⟩

/-- **The Riemannian divergence theorem with boundary** [Lee, Theorem 16.32]: on a smooth
Hausdorff `σ`-compact manifold `M` modeled on `𝓡∂ (n + 1)` with a `C¹` Riemannian metric (and no
orientability assumption), `∫_M div X dV = ∫_{∂M} ⟪X, N⟫ dS` whenever `M` is compact or `X` is
compactly supported, for any field `N` along `∂M` of unit norm, pointing outward, and orthogonal
to the boundary tangent space. -/
theorem integral_divergence_eq_boundaryFlux {k : ℕ∞ω} {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent k (T% X))
    (hSupport : IsCompact (univ : Set M) ∨ ∃ K : Set M, IsCompact K ∧ ∀ x ∉ K, X x = 0)
    {N : (x : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (x : M)}
    (hN : ∀ x, ‖N x‖ = 1 ∧ IsOutwardPointing (x : M) (N x) ∧
      ∀ w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x,
        inner ℝ (N x) (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) Subtype.val x w) = 0)
    (hk : 1 ≤ k := by simp) :
    (∫ x, Manifold.divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      ∫ x : (𝓡∂ (n + 1)).boundary M, inner ℝ (X (x : M)) (N x)
        ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  have hX1 : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X) := hX.of_le hk
  have hc := hasCompactSupport_of_isCompact_univ_or_exists_compact hSupport
  have hNeq : N = halfSpaceOutwardUnitNormal :=
    funext fun x ↦ eq_halfSpaceOutwardUnitNormal_of_norm_eq_one (hN x).1 (hN x).2.1 (hN x).2.2
  subst hNeq
  exact Manifold.integral_divergence_eq_boundaryFlux hX1 hc

end ConvenienceAPI

end TauCeti
