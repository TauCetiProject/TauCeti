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
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Divergence
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.VectorField.CoordinateFrame
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

private abbrev bdryI (n : ℕ) := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

/-- At a boundary point `x`, an orthonormal basis `b` of `T_x (∂M)` extends by the outward unit
normal `N` to an orthonormal basis `b'` of `T_x M` whose orientation agrees with `o` iff `b`
agrees with `Orientation.halfSpaceBoundaryOrientation o`. -/
private theorem exists_orthonormalBasis_cons_halfSpaceOutwardUnitNormal
    (x : (𝓡∂ (n + 1)).boundary M)
    (o : Orientation ℝ (TangentSpace (𝓡∂ (n + 1)) (x : M)) (Fin (n + 1))) :
    ∃ (b : OrthonormalBasis (Fin n) ℝ (TangentSpace (bdryI n) x))
      (b' : OrthonormalBasis (Fin (n + 1)) ℝ (TangentSpace (𝓡∂ (n + 1)) (x : M))),
      ⇑b'.toBasis = Fin.cons (halfSpaceOutwardUnitNormal x) (fun i ↦
          mfderiv (bdryI n) (𝓡∂ (n + 1)) (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x (b i)) ∧
        (b.toBasis.orientation = Orientation.halfSpaceBoundaryOrientation o ↔
          b'.toBasis.orientation = o) := by
  set dι := mfderiv (bdryI n) (𝓡∂ (n + 1)) (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x
  set N := halfSpaceOutwardUnitNormal x
  let b : OrthonormalBasis (Fin n) ℝ (TangentSpace (bdryI n) x) :=
    (stdOrthonormalBasis ℝ _).reindex (finCongr (by rw [TauCeti.finrank_tangentSpace]; simp))
  have hf_orth : Orthonormal ℝ (Fin.cons N fun i ↦ dι (b i)) := by
    rw [orthonormal_iff_ite]; intro i j
    refine Fin.cases ?_ (fun i ↦ ?_) i <;> refine Fin.cases ?_ (fun j ↦ ?_) j
    · simp [N, norm_halfSpaceOutwardUnitNormal]
    · simp [N, dι, inner_halfSpaceOutwardUnitNormal_mfderiv_subtypeVal, (Fin.succ_ne_zero j).symm]
    · simp [N, dι, inner_mfderiv_subtypeVal_halfSpaceOutwardUnitNormal]
    · simp only [Fin.cons_succ, Fin.succ_inj]; rw [← inner_tangentSpace_boundary]
      exact orthonormal_iff_ite.1 b.orthonormal i j
  let b' : OrthonormalBasis (Fin (n + 1)) ℝ (TangentSpace (𝓡∂ (n + 1)) (x : M)) :=
    (basisOfLinearIndependentOfCardEqFinrank hf_orth.linearIndependent
      (by rw [TauCeti.finrank_tangentSpace]; simp)).toOrthonormalBasis
      (by rwa [coe_basisOfLinearIndependentOfCardEqFinrank])
  have hb'_coe : ⇑b'.toBasis = Fin.cons N fun i ↦ dι (b i) := by
    rw [Module.Basis.toBasis_toOrthonormalBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hN_neg : (fun w : EuclideanSpace ℝ (Fin (n + 1)) ↦ w 0) N < 0 := by
    have h := (isOutwardPointing_halfSpaceOutwardUnitNormal x).coordinate_deriv_neg
    rwa [mfderiv_extChartAt_self] at h
  refine ⟨b, b', hb'_coe, Orientation.halfSpaceBoundaryOrientation_spec o hN_neg b.toBasis
    b'.toBasis (funext fun k ↦ Fin.cases (congrFun hb'_coe 0) (fun i ↦ ?_) k)⟩
  have hi := congrFun hb'_coe i.succ
  simp only [Fin.cons_succ, dι, mfderiv_subtypeVal_boundary, OrthonormalBasis.coe_toBasis] at hi ⊢
  exact hi

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
  set dι := mfderiv (bdryI n) (𝓡∂ (n + 1)) (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x
  set N := halfSpaceOutwardUnitNormal x
  set o_b : Orientation ℝ (TangentSpace (bdryI n) x) (Fin n) :=
    Orientation.halfSpaceBoundaryOrientation o
  obtain ⟨b, b', hb'_coe, horient⟩ := exists_orthonormalBasis_cons_halfSpaceOutwardUnitNormal x o
  -- Reduce evaluation of the boundary `n`-form `η := ι_u (o.volumeForm) ∘ dι` to the basis `b`.
  let η : AlternatingMap ℝ (TangentSpace (bdryI n) x) ℝ (Fin n) :=
    (o.volumeForm.curryLeft u).compLinearMap dι.toLinearMap
  have hη_apply (w : Fin n → TangentSpace (bdryI n) x) :
      η w = o.volumeForm (Fin.cons u fun i ↦ dι (w i)) := by
    rw [AlternatingMap.compLinearMap_apply, AlternatingMap.curryLeft_apply_apply]; rfl
  have hη_det : η v = η b.toBasis * b.toBasis.det v := by
    simpa only [smul_apply, smul_eq_mul] using congrArg (· v) (η.eq_smul_basis_det b.toBasis)
  -- Evaluate `η b` by expanding `u` in the orthonormal basis `b' = (N, dι b₀, …, dι bₙ₋₁)`.
  have hη_basis : η b.toBasis = inner ℝ u N * o.volumeForm b'.toBasis := by
    have hcons : (Fin.cons u fun i ↦ dι (b.toBasis i)) =
        Matrix.vecCons u ((0 : Fin (n + 1)).removeNth b'.toBasis) := by
      have hrem : (0 : Fin (n + 1)).removeNth b'.toBasis = fun i ↦ dι (b i) := by
        ext i; simp [Fin.removeNth, hb'_coe, dι]
      rw [hrem]; rfl
    have hb'0 : b' 0 = N := by
      simpa only [OrthonormalBasis.coe_toBasis, Fin.cons_zero] using congrFun hb'_coe 0
    have hrepr : b'.toBasis.repr u 0 = inner ℝ u N := by
      rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
        real_inner_comm, hb'0]
    rw [hη_apply, hcons, o.volumeForm.map_vecCons_removeNth_basis b'.toBasis u 0, hrepr]; simp
  -- Match the orientation signs of `b` and `b'`.
  rw [← hη_apply, hη_det, hη_basis]
  by_cases hb : b.toBasis.orientation = o_b
  · rw [o.volumeForm_robust b' (horient.1 hb), b'.toBasis.det_self,
      Orientation.volumeForm_robust (E := TangentSpace (bdryI n) x) o_b b hb, mul_one]
  · rw [o.volumeForm_robust_neg b' (mt horient.2 hb), neg_apply, b'.toBasis.det_self,
      Orientation.volumeForm_robust_neg (E := TangentSpace (bdryI n) x) o_b b hb, neg_apply]
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

private abbrev finBasisReindex (m : ℕ) : Module.Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)) :=
  (Module.finBasis ℝ (EuclideanSpace ℝ (Fin m))).reindex (finCongr finrank_euclideanSpace_fin)

private abbrev trivAt (α : N) :=
  trivializationAt (EuclideanSpace ℝ (Fin m)) (TangentSpace I) α

private def stdBasisDet (m : ℕ) : ℝ := |(stdBasis m).det (finBasisReindex m)|

private theorem stdBasisDet_pos (m : ℕ) : 0 < stdBasisDet m :=
  abs_pos.2 ((stdBasis m).isUnit_det (finBasisReindex m)).ne_zero

/-- Express the `finBasis` chart local frame in the `EuclideanSpace.basisFun` chart frame. -/
private theorem chartLocalFrame_eq_sum_stdLocalFrame (α : N) {y : N}
    (hy : y ∈ (trivAt (I := I) α).baseSet) (j : Fin m) :
    chartLocalFrame (I := I) α ((finCongr finrank_euclideanSpace_fin).symm j) y =
      ∑ i : Fin m, (stdBasis m).repr (finBasisReindex m j) i •
        (trivAt (I := I) α).localFrame (stdBasis m) i y := by
  have hb_eq : Module.finBasis ℝ (EuclideanSpace ℝ (Fin m))
      ((finCongr finrank_euclideanSpace_fin).symm j) = finBasisReindex m j :=
    (Module.Basis.reindex_apply _ _ j).symm
  rw [chartLocalFrame_eq_symmL, hb_eq]
  conv_lhs => rw [← (stdBasis m).sum_repr (finBasisReindex m j)]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, symmL_basis_eq_localFrame _ hy]

variable [RiemannianBundle (fun x : N ↦ TangentSpace I x)]

/-- The Riemannian volume density in the chart frame induced by `EuclideanSpace.basisFun`. -/
private def stdChartVolumeDensity (α y : N) : ℝ :=
  (stdBasisDet m)⁻¹ * chartVolumeDensity (I := I) α y

private theorem stdChartVolumeDensity_eq_sqrt_det_gram (α : N) {y : N}
    (hy : y ∈ (trivAt (I := I) α).baseSet) :
    stdChartVolumeDensity (I := I) α y =
      √(Matrix.gram ℝ ((trivAt (I := I) α).basisAt (stdBasis m) hy)).det := by
  set e := trivAt (I := I) α; set σ := finCongr (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := m))
  set B_std := e.basisAt (stdBasis m) hy; set B_fin := e.basisAt (finBasisReindex m) hy
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
      ext i j; simp [LinearMap.BilinForm.toMatrix_apply, Matrix.gram_apply, B_fin, σ, e, trivAt]
    rw [hsub, Matrix.det_submatrix_equiv_self]
  have hdet : (chartGramMatrix (I := I) α y).det =
      (stdBasisDet m) ^ 2 * (Matrix.gram ℝ B_std).det := by
    rw [← hgram_fin, ← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix B_std B_fin
        (innerₗ (TangentSpace I y)), hgram_std, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, hmat, ← Module.Basis.det_apply]
    simp only [stdBasisDet, sq_abs]; ring
  rw [stdChartVolumeDensity, chartVolumeDensity_def, hdet, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (stdBasisDet_pos m).le, inv_mul_cancel_left₀ (stdBasisDet_pos m).ne']

@[reducible]
private noncomputable def basisAddHaarOf {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] (b : Module.Basis ι ℝ E) [ms : MeasurableSpace E] [BorelSpace E] : @Measure E ms :=
  b.addHaar

private theorem integral_restrict_basisAddHaarOf_eq {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Fintype ι] (b : Module.Basis ι ℝ E) (ms₁ ms₂ : MeasurableSpace E)
    (hb₁ : @BorelSpace E _ ms₁) (hb₂ : @BorelSpace E _ ms₂) (S : Set E) (g : E → ℝ) :
    ∫ z in S, g z ∂(@basisAddHaarOf E ι _ _ _ b ms₁ hb₁) =
      ∫ z in S, g z ∂(@basisAddHaarOf E ι _ _ _ b ms₂ hb₂) := by
  have heq : ms₁ = ms₂ := hb₁.measurable_eq.trans hb₂.measurable_eq.symm
  subst heq; rfl

private theorem setIntegral_riemannianVolume_std_of_subset
    [MeasurableSpace N] [BorelSpace N] [LindelofSpace N]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin m)) (fun x : N ↦ TangentSpace I x)]
    {α : N} {s : Set N} (hs : s ⊆ (chartAt H α).source) (hs' : MeasurableSet s) (φ : N → ℝ) :
    ∫ x in s, φ x ∂riemannianVolume I N =
      ∫ z in (extChartAt I α) '' s,
        stdChartVolumeDensity (I := I) α ((extChartAt I α).symm z) *
          φ ((extChartAt I α).symm z) ∂volume := by
  have hhaar : (Module.finBasis ℝ (EuclideanSpace ℝ (Fin m))).addHaar =
      ENNReal.ofReal (stdBasisDet m)⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin m))) := by
    rw [← Module.Basis.addHaar_reindex _ (finCongr finrank_euclideanSpace_fin),
      Module.Basis.addHaar_eq_smul_of_basis (stdBasis m), stdBasis,
      OrthonormalBasis.addHaar_eq_volume, abs_inv, stdBasisDet]
  rw [setIntegral_riemannianVolume_of_subset hs hs' φ]; simp_rw [smul_eq_mul]
  rw [integral_restrict_basisAddHaarOf_eq (Module.finBasis ℝ (EuclideanSpace ℝ (Fin m)))
      (@extChartAtMeasurableSpaceE (EuclideanSpace ℝ (Fin m)) _) inferInstance
      (@extChartAtBorelSpaceE (EuclideanSpace ℝ (Fin m)) _) inferInstance,
    basisAddHaarOf, hhaar, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.2 (stdBasisDet_pos m).le)]
  simp_rw [smul_eq_mul, ← integral_const_mul, ← mul_assoc, stdChartVolumeDensity]

/-- Near `y`, each standard-frame density-weighted flux coefficient is a constant linear
combination of the `finBasis` density-weighted flux coefficients. -/
private theorem stdChartVolumeDensity_mul_localFrameCoeff_eventuallyEq_sum [IsManifold I 2 N]
    (α : N) {y : N} (hy : y ∈ (trivAt (I := I) α).baseSet)
    (X : (x : N) → TangentSpace I x) (i : Fin m) :
    (fun z ↦ stdChartVolumeDensity (I := I) α z *
        (trivAt (I := I) α).localFrameCoeff I (stdBasis m) i z (X z)) =ᶠ[𝓝 y]
      fun z ↦ ∑ j : Fin m, ((stdBasisDet m)⁻¹ * (stdBasis m).repr (finBasisReindex m j) i) •
        (chartVolumeDensity (I := I) α z * (trivAt (I := I) α).localFrameCoeff I
          (Module.finBasis ℝ (EuclideanSpace ℝ (Fin m)))
          ((finCongr finrank_euclideanSpace_fin).symm j) z (X z)) := by
  set e := trivAt (I := I) α; set b_fin := Module.finBasis ℝ (EuclideanSpace ℝ (Fin m))
  set σ := finCongr (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := m))
  filter_upwards [e.open_baseSet.mem_nhds hy] with z hz
  rw [e.localFrameCoeff_apply_of_mem_baseSet (stdBasis m) hz]
  have hw : (e.basisAt (stdBasis m) hz).repr (X z) i = ∑ j : Fin m,
      (stdBasis m).repr (finBasisReindex m j) i * (e.basisAt b_fin hz).repr (X z) (σ.symm j) := by
    rw [← Finsupp.lapply_apply (R := ℝ) i]
    conv_lhs => rw [← (e.basisAt (finBasisReindex m) hz).sum_repr (X z)]
    rw [map_sum, map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by
      simp [Trivialization.basisAt, e.apply_mk_symm hz, b_fin, σ, mul_comm]
  rw [hw, stdChartVolumeDensity, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← e.localFrameCoeff_apply_of_mem_baseSet (I := I) b_fin hz X (σ.symm j), smul_eq_mul]; ring

/-- The chart divergence formula `ρ_std div X = ∑ᵢ ∂ᵢ (ρ_std Xⁱ)` in the `EuclideanSpace.basisFun`
coordinate frame, obtained by a constant linear frame change from `Module.finBasis`. -/
private theorem stdChartVolumeDensity_mul_divergence [IsManifold I 2 N]
    [IsContMDiffRiemannianBundle I 1 (EuclideanSpace ℝ (Fin m)) (fun x : N ↦ TangentSpace I x)]
    (α : N) {y : N} (hy : y ∈ (trivAt (I := I) α).baseSet)
    {X : (x : N) → TangentSpace I x} (hX : MDiffAt (T% X) y) :
    stdChartVolumeDensity (I := I) α y * divergence I X y =
      ∑ i : Fin m, mvfderiv I (fun z ↦ stdChartVolumeDensity (I := I) α z *
        (trivAt (I := I) α).localFrameCoeff I (stdBasis m) i z (X z)) y
        ((trivAt (I := I) α).localFrame (stdBasis m) i y) := by
  have : IsManifold I (1 + 1) N := by norm_num; infer_instance
  let _ : ContMDiffVectorBundle 1 (EuclideanSpace ℝ (Fin m)) (TangentSpace I : N → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  set e := trivAt (I := I) α; set b_fin := Module.finBasis ℝ (EuclideanSpace ℝ (Fin m))
  set σ := finCongr (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := m))
  let A (i j : Fin m) : ℝ := (stdBasis m).repr (finBasisReindex m j) i
  let g (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)))) (z : N) : ℝ :=
    chartVolumeDensity (I := I) α z * e.localFrameCoeff I b_fin k z (X z)
  have hρ : MDiffAt (chartVolumeDensity (I := I) α) y :=
    ((contMDiffOn_chartVolumeDensity (n := 1) α).contMDiffAt
      (e.open_baseSet.mem_nhds hy)).mdifferentiableAt one_ne_zero
  have hfk (k) : MDiffAt (g k) y := hρ.mul (mdifferentiableAt_localFrameCoeff b_fin hy hX k)
  -- Reindex the `finBasis` divergence formula, expand the frame in `stdBasis`, and recombine
  -- the differentiated `stdBasis` coefficients.
  calc stdChartVolumeDensity (I := I) α y * divergence I X y
      = (stdBasisDet m)⁻¹ * ∑ j : Fin m,
          mvfderiv I (g (σ.symm j)) y (chartLocalFrame (I := I) α (σ.symm j) y) := by
          rw [stdChartVolumeDensity, mul_assoc, chartVolumeDensity_mul_divergence α hy hX]
          congr 1; exact (Equiv.sum_comp σ.symm fun k ↦
            mvfderiv I (g k) y (chartLocalFrame (I := I) α k y)).symm
    _ = ∑ i : Fin m, ∑ j : Fin m, ((stdBasisDet m)⁻¹ * A i j) *
          mvfderiv I (g (σ.symm j)) y (e.localFrame (stdBasis m) i y) := by
          rw [Finset.mul_sum, Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [chartLocalFrame_eq_sum_stdLocalFrame α hy j, map_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_mul]; ring
    _ = _ := by
          refine Finset.sum_congr rfl fun i _ ↦ Eq.symm ?_
          rw [(stdChartVolumeDensity_mul_localFrameCoeff_eventuallyEq_sum α hy X i).mvfderiv_eq,
            TauCeti.mvfderiv_fun_sum (f := fun j z ↦ ((stdBasisDet m)⁻¹ * A i j) • g (σ.symm j) z)
              (fun j _ ↦ (hfk (σ.symm j)).const_smul _), sum_apply]
          exact Finset.sum_congr rfl fun j _ ↦ by
            rw [TauCeti.mvfderiv_const_smul (hfk (σ.symm j)), smul_apply, smul_eq_mul]

end StdChartDensity

/-! ### Single-chart divergence theorem on a half-space chart -/

private abbrev piToE (m : ℕ) := (EuclideanSpace.equiv (Fin m) ℝ).symm
private abbrev piHalfSpace (n : ℕ) : Set (Fin (n + 1) → ℝ) := {x | 0 ≤ x 0}

private theorem piToE_cons_zero (n : ℕ) (y : Fin n → ℝ) :
    piToE (n + 1) (Fin.cons 0 y) = euclideanHalfSpaceBoundaryParam n (piToE n y) := by
  ext k; refine Fin.cases ?_ (fun j ↦ ?_) k <;>
    simp [piToE, euclideanHalfSpaceBoundaryParam_apply_zero,
      euclideanHalfSpaceBoundaryParam_apply_succ]

section HalfSpaceChart

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 2 M]

local instance : IsManifold (𝓡∂ (n + 1)) 1 M := IsManifold.of_le (n := 2) (by norm_num)

local instance : IsManifold (𝓡∂ (n + 1)) (1 + 1) M := by rw [one_add_one_eq_two]; infer_instance

local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M) :=
  isManifold_boundary M one_ne_zero

private abbrev ambTriv (α : M) :=
  trivializationAt (EuclideanSpace ℝ (Fin (n + 1))) (TangentSpace (𝓡∂ (n + 1))) α
private abbrev bdryTriv (α : (𝓡∂ (n + 1)).boundary M) :=
  trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (bdryI n)) α
private abbrev ambTsupport (X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x) : Set M :=
  tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) X

/-- The derivative of the boundary inclusion sends the standard boundary chart frame at `α` to the
last `n` vectors of the ambient standard chart frame at `α`. -/
private theorem mfderiv_subtypeVal_boundary_basisAt_stdBasis
    (α q : (𝓡∂ (n + 1)).boundary M) (hq : q ∈ (extChartAt (bdryI n) α).source)
    (hq_base : q ∈ (bdryTriv α).baseSet) (hq'_base : (q : M) ∈ (ambTriv (α : M)).baseSet)
    (i : Fin n) :
    mfderiv (bdryI n) (𝓡∂ (n + 1)) (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q
        ((bdryTriv α).basisAt (stdBasis n) hq_base i) =
      (ambTriv (α : M)).basisAt (stdBasis (n + 1)) hq'_base i.succ := by
  have hq_chart : q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) α).source :=
    (extChartAt_source (I := bdryI n) α) ▸ hq
  have hq'_chart : (q : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) (α : M)).source := by
    simpa only [boundaryChartedSpace_chartAt_source, mem_preimage] using hq_chart
  have hparam : euclideanHalfSpaceBoundaryParam n (stdBasis n i) = stdBasis (n + 1) i.succ := by
    ext k; refine Fin.cases ?_ (fun j ↦ ?_) k <;>
      simp [stdBasis, euclideanHalfSpaceBoundaryParam_apply_zero,
        euclideanHalfSpaceBoundaryParam_apply_succ, Fin.succ_inj]
  have htcc := congrArg (· (stdBasis n i))
    (tangentCoordChange_boundaryParam hq (mem_extChartAt_source q))
  simp only [ContinuousLinearMap.comp_apply, hparam] at htcc
  rw [basisAt_apply, basisAt_apply, TangentBundle.symmL_trivializationAt_eq_core hq_chart,
    TangentBundle.symmL_trivializationAt_eq_core hq'_chart]
  simp only [tangentBundleCore_coordChange_achart, mfderiv_subtypeVal_boundary]
  exact htcc.symm

/-- Because the zeroth ambient chart frame vector points inward (`x₀ ≥ 0`), the standard boundary
chart basis carries the opposite of the outward-first boundary orientation induced by the ambient
standard chart basis. -/
private theorem orientation_boundary_basisAt_stdBasis_eq_neg
    (α q : (𝓡∂ (n + 1)).boundary M) (hq : q ∈ (extChartAt (bdryI n) α).source)
    (hq_base : q ∈ (bdryTriv α).baseSet) (hq'_base : (q : M) ∈ (ambTriv (α : M)).baseSet) :
    ((bdryTriv α).basisAt (stdBasis n) hq_base).orientation =
      -(_root_.Orientation.halfSpaceBoundaryOrientation
        ((ambTriv (α : M)).basisAt (stdBasis (n + 1)) hq'_base).orientation) := by
  set e' := ambTriv (n := n) (α : M); set B := (bdryTriv α).basisAt (stdBasis n) hq_base
  set B' := e'.basisAt (stdBasis (n + 1)) hq'_base
  -- Flip the inward zeroth basis vector to an outward vector, reversing the ambient orientation.
  let w : Fin (n + 1) → ℝˣ := Fin.cons (-1) fun _ ↦ 1
  let B_neg := B'.unitsSMul w
  have hB_neg0 : (fun v : EuclideanSpace ℝ (Fin (n + 1)) ↦ v 0) (B_neg 0) < 0 := by
    have hB0 : B_neg 0 = e'.symmL ℝ (q : M) (-EuclideanSpace.single 0 1) := by
      simp only [B_neg, w, Module.Basis.unitsSMul_apply, Fin.cons_zero, Units.smul_def,
        Units.val_neg, Units.val_one, neg_one_smul, map_neg, B', basisAt_apply, stdBasis,
        OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
    have h := (hB0 ▸ isOutwardPointing_trivializationAt_symmL_neg_single_zero
      hq'_base).coordinate_deriv_neg
    rwa [mfderiv_extChartAt_self] at h
  have hB_neg_orient : B_neg.orientation = -B'.orientation := by
    rw [← B'.orientation_ne_iff_eq_neg, ne_comm, B_neg.orientation_ne_iff_eq_neg,
      B'.orientation_eq_neg_iff_det_neg B_neg, Module.Basis.det_apply]
    have hdiag : B'.toMatrix B_neg = Matrix.diagonal fun k ↦ (w k : ℝ) := by
      ext i j; simp only [Module.Basis.toMatrix_apply, Matrix.diagonal_apply, B_neg,
        Module.Basis.unitsSMul_apply, Units.smul_def, map_smul, Module.Basis.repr_self]
      by_cases hij : i = j <;> simp [hij]
    rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_succ]; simp [w]
  have hspec := _root_.Orientation.halfSpaceBoundaryOrientation_spec
    (-B'.orientation) hB_neg0 B B_neg (funext fun k ↦ Fin.cases rfl (fun i ↦ by
      have h1 : B_neg i.succ = B' i.succ := by simp [B_neg, w, Module.Basis.unitsSMul_apply]
      have h2 := (mfderiv_subtypeVal_boundary_basisAt_stdBasis α q hq hq_base hq'_base i).symm
      rw [mfderiv_subtypeVal_boundary] at h2; exact h1.trans h2) k)
  exact (hspec.2 hB_neg_orient).trans (_root_.Orientation.halfSpaceBoundaryOrientation_neg _)

variable [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- In a boundary-centered chart at `α`, the zeroth standard-frame flux coefficient `ρ X⁰` at a
boundary point `q` equals `-ρ_∂ * inner ℝ (X q) (N q)`, where `ρ_∂` is the standard-frame boundary
chart density. This holds for all `n ≥ 0`. -/
private theorem stdChartVolumeDensity_mul_localFrameCoeff_zero_boundary
    (α q : (𝓡∂ (n + 1)).boundary M) (hq : q ∈ (extChartAt (bdryI n) α).source)
    (u : TangentSpace (𝓡∂ (n + 1)) (q : M)) :
    stdChartVolumeDensity (I := 𝓡∂ (n + 1)) (α : M) (q : M) *
      (ambTriv (α : M)).localFrameCoeff (𝓡∂ (n + 1)) (stdBasis (n + 1)) 0 (q : M) u =
      -(stdChartVolumeDensity (I := bdryI n) α q * inner ℝ u (halfSpaceOutwardUnitNormal q)) := by
  have _ : Fact (Module.finrank ℝ (TangentSpace (𝓡∂ (n + 1)) (q : M)) = n + 1) :=
    ⟨by rw [TauCeti.finrank_tangentSpace]; simp⟩
  have _ : Fact (Module.finrank ℝ (TangentSpace (bdryI n) q) = n) :=
    ⟨by rw [TauCeti.finrank_tangentSpace]; simp⟩
  set e' := ambTriv (n := n) (α : M); set e := bdryTriv α
  have hq_chart : q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) α).source :=
    (extChartAt_source (I := bdryI n) α) ▸ hq
  have hq_base : q ∈ e.baseSet := by simpa [e, bdryTriv] using hq_chart
  have hq'_base : (q : M) ∈ e'.baseSet := by
    simpa [e', ambTriv, boundaryChartedSpace_chartAt_source] using hq_chart
  set B := e.basisAt (stdBasis n) hq_base; set B' := e'.basisAt (stdBasis (n + 1)) hq'_base
  set dι := mfderiv (bdryI n) (𝓡∂ (n + 1)) (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q
  set o_q := B'.orientation; set o_b := _root_.Orientation.halfSpaceBoundaryOrientation o_q
  -- Evaluate both sides of `volumeForm_cons_mfderiv_subtypeVal_boundary` on `(u, dι B)`.
  have hlhs : o_q.volumeForm (Fin.cons u fun i ↦ dι (B i)) =
      stdChartVolumeDensity (I := 𝓡∂ (n + 1)) (α : M) (q : M) *
        e'.localFrameCoeff (𝓡∂ (n + 1)) (stdBasis (n + 1)) 0 (q : M) u := by
    have hcons : (Fin.cons u fun i ↦ dι (B i)) =
        Matrix.vecCons u ((0 : Fin (n + 1)).removeNth B') := by
      ext k; refine Fin.cases rfl (fun i ↦ ?_) k
      simpa [Fin.tail] using mfderiv_subtypeVal_boundary_basisAt_stdBasis α q hq hq_base hq'_base i
    rw [hcons, o_q.volumeForm.map_vecCons_removeNth_basis B' u 0,
      o_q.volumeForm_apply_eq_sqrt_det_gram B' rfl,
      ← stdChartVolumeDensity_eq_sqrt_det_gram (α : M) hq'_base,
      e'.localFrameCoeff_apply_of_mem_baseSet (stdBasis (n + 1)) hq'_base (fun _ ↦ u) 0]
    simp [B', mul_comm]
  have hrhs_vol : _root_.Orientation.volumeForm (E := TangentSpace (bdryI n) q) o_b B =
      -stdChartVolumeDensity (I := bdryI n) α q := by
    rw [_root_.Orientation.volumeForm_apply_eq_neg_sqrt_det_gram (E := TangentSpace (bdryI n) q)
        o_b B ((orientation_boundary_basisAt_stdBasis_eq_neg α q hq hq_base hq'_base) ▸
          (Module.Ray.ne_neg_self o_b).symm),
      stdChartVolumeDensity_eq_sqrt_det_gram α hq_base]
  have hmain := volumeForm_cons_mfderiv_subtypeVal_boundary q o_q u B
  rw [hlhs, hrhs_vol] at hmain; linarith

/-- The `i`-th standard-frame flux of `X` in the extended chart at `α`, extended by zero off the
chart target. -/
private abbrev stdChartFluxE (α : M) (X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x)
    (i : Fin (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
  TauCeti.chartFlux (stdBasis (n + 1)) (stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α) α X i

/-- Pointwise boundary-trace identification: in a boundary-centered chart at `α₀`, evaluating the
zeroth chart flux on `x₀ = 0` gives the negated boundary-chart outward normal flux density. -/
private theorem stdChartFluxE_zero_boundaryParam (α₀ : (𝓡∂ (n + 1)).boundary M)
    (X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x) (w : EuclideanSpace ℝ (Fin n)) :
    stdChartFluxE (α₀ : M) X 0 (euclideanHalfSpaceBoundaryParam n w) =
      -((extChartAt (bdryI n) α₀).target.indicator (fun w ↦
        stdChartVolumeDensity (I := bdryI n) α₀ ((extChartAt (bdryI n) α₀).symm w) *
        inner ℝ (X (((extChartAt (bdryI n) α₀).symm w : (𝓡∂ (n + 1)).boundary M) : M))
          (halfSpaceOutwardUnitNormal ((extChartAt (bdryI n) α₀).symm w))) w) := by
  set e₀ := extChartAt (bdryI n) α₀; set ec := extChartAt (𝓡∂ (n + 1)) (α₀ : M)
  by_cases hw : w ∈ e₀.target
  · have hw' : euclideanHalfSpaceBoundaryParam n w ∈ ec.target :=
      (boundaryParam_mem_extChartAt_target_iff α₀ w).2 hw
    set q := e₀.symm w; have hq_src : q ∈ e₀.source := e₀.map_target hw
    have hq'_src : (q : M) ∈ ec.source := by
      simpa only [e₀, ec, extChartAt_source, boundaryChartedSpace_chartAt_source, mem_preimage]
        using hq_src
    have hsymm_eq : ec.symm (euclideanHalfSpaceBoundaryParam n w) = (q : M) := by
      rw [← e₀.right_inv hw, boundaryParam_extChartAt hq_src, ec.left_inv hq'_src]
    rw [indicator_of_mem hw, stdChartFluxE, chartFlux_apply_of_mem _ _ 0 hw', hsymm_eq]
    exact stdChartVolumeDensity_mul_localFrameCoeff_zero_boundary α₀ q hq_src (X (q : M))
  · rw [indicator_of_notMem hw, neg_zero, stdChartFluxE, chartFlux_apply_of_notMem _ _ 0
      (mt (boundaryParam_mem_extChartAt_target_iff α₀ w).1 hw)]

section DiffFlux

variable [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
  (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

private theorem contMDiffOn_stdChartVolumeDensity (α : M) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) 1 (stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α)
      (chartAt (EuclideanHalfSpace (n + 1)) α).source :=
  contMDiffOn_const.mul <| by
    simpa only [TangentBundle.trivializationAt_baseSet] using
      contMDiffOn_chartVolumeDensity (I := 𝓡∂ (n + 1)) (n := 1) α

private theorem sum_fderivWithin_stdChartFluxE {α : M} {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hKc : IsCompact (extChartAt (𝓡∂ (n + 1)) α '' ambTsupport X))
    (himage : extChartAt (𝓡∂ (n + 1)) α '' ambTsupport X ⊆ (extChartAt (𝓡∂ (n + 1)) α).target)
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz_range : z ∈ range (𝓡∂ (n + 1))) :
    ∑ i : Fin (n + 1), fderivWithin ℝ (stdChartFluxE α X i) (range (𝓡∂ (n + 1))) z
        (stdBasis (n + 1) i) =
      (extChartAt (𝓡∂ (n + 1)) α).target.indicator (fun z ↦
        stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α ((extChartAt (𝓡∂ (n + 1)) α).symm z) *
          divergence (𝓡∂ (n + 1)) X ((extChartAt (𝓡∂ (n + 1)) α).symm z)) z := by
  set ec := extChartAt (𝓡∂ (n + 1)) α
  by_cases hz : z ∈ ec.target
  · rw [indicator_of_mem hz]
    have hy : ec.symm z ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source :=
      (extChartAt_source (I := 𝓡∂ (n + 1)) α) ▸ ec.map_target hz
    rw [stdChartVolumeDensity_mul_divergence α (by simpa using hy)
      ((hX _).mdifferentiableAt one_ne_zero)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mvfderiv_localFrame_trivializationAt_eq_fderivWithin (stdBasis (n + 1)) α hy _ i,
      ec.right_inv hz]
    congr 1
    exact Filter.EventuallyEq.fderivWithin_eq
      (Filter.eventually_of_mem (extChartAt_target_mem_nhdsWithin_of_mem hz) fun _ h ↦
        chartFlux_apply_of_mem _ _ i h) (chartFlux_apply_of_mem _ _ i hz)
  · rw [indicator_of_notMem hz]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have h0 : HasFDerivWithinAt (stdChartFluxE α X i)
        (0 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) (range (𝓡∂ (n + 1))) z :=
      ((hasFDerivAt_const (0 : ℝ) z).congr_of_eventuallyEq
        (chartFlux_eventuallyEq_zero _ _ hKc i fun h ↦ hz (himage h))).hasFDerivWithinAt
    simp [h0.fderivWithin ((𝓡∂ (n + 1)).uniqueDiffOn z hz_range)]

/-- Pull the chart divergence formula back along `piToE (n + 1)` to `piHalfSpace n`. -/
private theorem sum_fderivWithin_stdChartFlux_pi {α : M}
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hKc : IsCompact (extChartAt (𝓡∂ (n + 1)) α '' ambTsupport X))
    (himage : extChartAt (𝓡∂ (n + 1)) α '' ambTsupport X ⊆ (extChartAt (𝓡∂ (n + 1)) α).target)
    {x : Fin (n + 1) → ℝ} (hx : x ∈ piHalfSpace n) :
    (∑ i : Fin (n + 1), fderivWithin ℝ (fun y j ↦ stdChartFluxE α X j (piToE (n + 1) y))
        (piHalfSpace n) x (Pi.single i 1) i) =
      (extChartAt (𝓡∂ (n + 1)) α).target.indicator (fun z ↦
        stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α ((extChartAt (𝓡∂ (n + 1)) α).symm z) *
          divergence (𝓡∂ (n + 1)) X ((extChartAt (𝓡∂ (n + 1)) α).symm z)) (piToE (n + 1) x) := by
  have hL_maps : MapsTo (piToE (n + 1)) (piHalfSpace n) (range (𝓡∂ (n + 1))) := fun y hy ↦ by
    simpa [piToE, piHalfSpace, range_modelWithCornersEuclideanHalfSpace] using hy
  have hflux_diff (i) : ContDiffOn ℝ 1 (stdChartFluxE α X i) (range (𝓡∂ (n + 1))) :=
    contDiffOn_chartFlux (stdBasis (n + 1)) (contMDiffOn_stdChartVolumeDensity α)
      hX.contMDiffOn hKc himage i
  have hf_diff : ContDiffOn ℝ 1 (fun y i ↦ stdChartFluxE α X i (piToE (n + 1) y))
      (piHalfSpace n) :=
    contDiffOn_pi.2 fun i ↦ (hflux_diff i).comp (piToE (n + 1)).contDiff.contDiffOn hL_maps
  have huniqH := TauCeti.uniqueDiffOn_pi_halfSpace 0 0 x hx
  rw [← sum_fderivWithin_stdChartFluxE hX hKc himage (hL_maps hx)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hfi := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ)
    i).hasFDerivAt.comp_hasFDerivWithinAt x
      (hf_diff.differentiableOn one_ne_zero x hx).hasFDerivWithinAt).fderivWithin huniqH
  have hL_eq := (((hflux_diff i).differentiableOn one_ne_zero (piToE (n + 1) x)
    (hL_maps hx)).hasFDerivWithinAt.comp x (piToE (n + 1)).hasFDerivAt.hasFDerivWithinAt
      hL_maps).fderivWithin huniqH
  have hsingle : piToE (n + 1) (Pi.single i 1) = stdBasis (n + 1) i := by
    ext j; simp [piToE, stdBasis, EuclideanSpace.basisFun_apply]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearEquiv.coe_coe, hsingle] using
    congrArg (· (Pi.single i 1)) (hfi.symm.trans hL_eq)

end DiffFlux

variable [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- Boundary-trace integral transport in a boundary-centered chart: the negated `x₀ = 0` slice
integral of `stdChartFluxE` equals the boundary flux integral `∫_{∂M} ⟪X, N⟫ dS`. -/
private theorem neg_integral_stdChartFlux_zero_eq_boundaryFlux (α₀ : (𝓡∂ (n + 1)).boundary M)
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hKs : ambTsupport X ⊆ (chartAt (EuclideanHalfSpace (n + 1)) (α₀ : M)).source) :
    -(∫ y : Fin n → ℝ, stdChartFluxE (α₀ : M) X 0 (piToE (n + 1) (Fin.cons 0 y))) =
      ∫ x : (𝓡∂ (n + 1)).boundary M, inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x)
        ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  let _ : LindelofSpace ((𝓡∂ (n + 1)).boundary M) :=
    ((𝓡∂ (n + 1)).isClosed_boundary one_ne_zero).isClosedEmbedding_subtypeVal.LindelofSpace
  set e₀ := extChartAt (bdryI n) α₀
  let bE : EuclideanSpace ℝ (Fin n) → ℝ := e₀.target.indicator fun w ↦
    stdChartVolumeDensity (I := bdryI n) α₀ (e₀.symm w) *
      inner ℝ (X ((e₀.symm w : (𝓡∂ (n + 1)).boundary M) : M))
        (halfSpaceOutwardUnitNormal (e₀.symm w))
  have htrace (y : Fin n → ℝ) :
      stdChartFluxE (α₀ : M) X 0 (piToE (n + 1) (Fin.cons 0 y)) = -bE (piToE n y) :=
    piToE_cons_zero n y ▸ stdChartFluxE_zero_boundaryParam α₀ X (piToE n y)
  simp_rw [htrace, integral_neg, neg_neg]
  trans (∫ w, bE w ∂volume)
  · exact (PiLp.volume_preserving_toLp (Fin n)).integral_comp
      (piToE n).toHomeomorph.measurableEmbedding bE
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := e₀.target)
      (fun _ hw ↦ indicator_of_notMem hw _), halfSpaceBoundaryVolume_eq_riemannianVolume,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := (chartAt (EuclideanSpace ℝ (Fin n)) α₀).source) fun q hq ↦ by
        have hX0 : X (q : M) = 0 := image_eq_zero_of_notMem_tsupport
          (α := EuclideanSpace ℝ (Fin (n + 1))) fun h ↦
            hq (by simpa [boundaryChartedSpace_chartAt_source] using hKs h)
        simp [hX0],
    setIntegral_riemannianVolume_std_of_subset subset_rfl
      (chartAt (EuclideanSpace ℝ (Fin n)) α₀).open_source.measurableSet,
    ← extChartAt_source (I := bdryI n), e₀.image_source_eq_target]
  exact setIntegral_congr_fun (isOpen_extChartAt_target α₀).measurableSet fun _ hw ↦
    indicator_of_mem hw _

/-- Boundary-trace vanishing when the support of `X` is disjoint from `∂M`: both the `x₀ = 0`
slice integral of `stdChartFluxE` and the boundary flux integral vanish. -/
private theorem neg_integral_stdChartFlux_zero_eq_boundaryFlux_of_disjoint {α : M}
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hdisj : Disjoint (ambTsupport X) ((𝓡∂ (n + 1)).boundary M)) :
    -(∫ y : Fin n → ℝ, stdChartFluxE α X 0 (piToE (n + 1) (Fin.cons 0 y))) =
      ∫ x : (𝓡∂ (n + 1)).boundary M, inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x)
        ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  set ec := extChartAt (𝓡∂ (n + 1)) α
  have htrace_zero (y : Fin n → ℝ) : stdChartFluxE α X 0 (piToE (n + 1) (Fin.cons 0 y)) = 0 := by
    rw [piToE_cons_zero]
    set w := euclideanHalfSpaceBoundaryParam n (piToE n y)
    by_cases hw' : w ∈ ec.target
    · have hp_src : ec.symm w ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source :=
        (extChartAt_source (I := 𝓡∂ (n + 1)) α) ▸ ec.map_target hw'
      have hp_bdry : ec.symm w ∈ (𝓡∂ (n + 1)).boundary M := by
        rw [ModelWithCorners.mem_boundary_euclideanHalfSpace_iff_of_mem_atlas
          (by simp : (2 : ℕ∞ω) ≠ 0) (chart_mem_atlas _ α) hp_src]
        simpa [ec, w, extChartAt, modelWithCornersEuclideanHalfSpace_toFun,
          euclideanHalfSpaceBoundaryParam_apply_zero] using
          congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) ↦ v 0) (ec.right_inv hw')
      have hX0 : X (ec.symm w) = 0 := image_eq_zero_of_notMem_tsupport
        (α := EuclideanSpace ℝ (Fin (n + 1))) (disjoint_right.1 hdisj hp_bdry)
      rw [stdChartFluxE, chartFlux_apply_of_mem _ _ 0 hw', hX0, map_zero, mul_zero]
    · exact chartFlux_apply_of_notMem _ _ 0 hw'
  have hbdry_zero (q : (𝓡∂ (n + 1)).boundary M) :
      inner ℝ (X (q : M)) (halfSpaceOutwardUnitNormal q) = 0 := by
    have hX0 : X (q : M) = 0 := image_eq_zero_of_notMem_tsupport
      (α := EuclideanSpace ℝ (Fin (n + 1))) (disjoint_right.1 hdisj q.property)
    simp [hX0]
  simp_rw [htrace_zero, hbdry_zero]; simp

variable [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
  (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- Coordinate-integral transport: for a `C¹` vector field supported in the chart at `α`, the
Riemannian volume integral `∫ div X dV` equals the coordinate divergence integral over the
half-space `piHalfSpace n`. -/
private theorem integral_divergence_eq_setIntegral_pi_halfSpace {α : M}
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hKc : IsCompact (extChartAt (𝓡∂ (n + 1)) α '' ambTsupport X))
    (hKs : ambTsupport X ⊆ (chartAt (EuclideanHalfSpace (n + 1)) α).source)
    (himage : extChartAt (𝓡∂ (n + 1)) α '' ambTsupport X ⊆ (extChartAt (𝓡∂ (n + 1)) α).target) :
    (∫ x, divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      ∫ x in piHalfSpace n, ∑ i : Fin (n + 1),
        fderivWithin ℝ (fun y j ↦ stdChartFluxE α X j (piToE (n + 1) y))
          (piHalfSpace n) x (Pi.single i 1) i := by
  set ec := extChartAt (𝓡∂ (n + 1)) α
  let dE : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := ec.target.indicator fun z ↦
    stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α (ec.symm z) * divergence (𝓡∂ (n + 1)) X (ec.symm z)
  have hTm : MeasurableSet (range (𝓡∂ (n + 1))) := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact (isClosed_le continuous_const (EuclideanSpace.proj 0).continuous).measurableSet
  have hHm : MeasurableSet (piHalfSpace n) :=
    (isClosed_le continuous_const (continuous_apply 0)).measurableSet
  have hpre : WithLp.toLp 2 ⁻¹' range (𝓡∂ (n + 1)) = piHalfSpace n := by
    ext x; simp [piHalfSpace, range_modelWithCornersEuclideanHalfSpace]
  have hp := (PiLp.volume_preserving_toLp (Fin (n + 1))).restrict_preimage hTm
  rw [hpre] at hp
  have htarget_meas : MeasurableSet ec.target :=
    ec.image_source_eq_target ▸ (isOpen_extChartAt_source α).measurableSet.image_extChartAt
      α subset_rfl
  calc (∫ x, divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M)
      = ∫ x in (chartAt (EuclideanHalfSpace (n + 1)) α).source,
          divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
            divergence_eq_zero_of_notMem_tsupport (𝓡∂ (n + 1)) fun h ↦ hx (hKs h)).symm
    _ = ∫ z in ec.target, stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α (ec.symm z) *
          divergence (𝓡∂ (n + 1)) X (ec.symm z) ∂volume := by
          rw [setIntegral_riemannianVolume_std_of_subset subset_rfl
            (chartAt _ α).open_source.measurableSet, ← extChartAt_source (I := 𝓡∂ (n + 1)),
            ec.image_source_eq_target]
    _ = ∫ z in range (𝓡∂ (n + 1)), dE z ∂volume := by
          rw [setIntegral_indicator htarget_meas,
            inter_eq_right.2 (extChartAt_target_subset_range α)]
    _ = ∫ x in piHalfSpace n, dE (piToE (n + 1) x) :=
          (hp.integral_comp (piToE (n + 1)).toHomeomorph.measurableEmbedding dE).symm
    _ = _ := setIntegral_congr_fun hHm fun x hx ↦
          (sum_fderivWithin_stdChartFlux_pi hX hKc himage hx).symm

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
  have hKs' : ambTsupport X ⊆ (extChartAt (𝓡∂ (n + 1)) α).source := by rwa [extChartAt_source]
  have hKc := hK.image_of_continuousOn ((continuousOn_extChartAt α).mono hKs')
  have himage := ((extChartAt (𝓡∂ (n + 1)) α).mapsTo.mono_left hKs').image_subset
  -- Stage 1: apply the coordinate half-space divergence theorem to the chart fluxes `f`.
  let f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := fun x i ↦ stdChartFluxE α X i (piToE (n + 1) x)
  have hL_maps : MapsTo (piToE (n + 1)) (piHalfSpace n) (range (𝓡∂ (n + 1))) := fun x hx ↦ by
    simpa [piToE, piHalfSpace, range_modelWithCornersEuclideanHalfSpace] using hx
  have hf_diff : ContDiffOn ℝ 1 f (piHalfSpace n) := contDiffOn_pi.2 fun i ↦
    (contDiffOn_chartFlux (stdBasis (n + 1)) (contMDiffOn_stdChartVolumeDensity α)
      hX.contMDiffOn hKc himage i).comp (piToE (n + 1)).contDiff.contDiffOn hL_maps
  have hf_supp : HasCompactSupport f := HasCompactSupport.intro
    (hKc.image (piToE (n + 1)).symm.continuous) fun x hx ↦ funext fun i ↦
      chartFlux_eq_zero _ _ i fun h ↦ hx ⟨piToE (n + 1) x, h, (piToE (n + 1)).symm_apply_apply x⟩
  obtain ⟨-, -, hdiv_coord⟩ := hf_diff.integral_divergence_coordinate_halfSpace hf_supp
  -- Stage 2: transport `∫ div X dV` to the coordinate half-space divergence integral.
  rw [integral_divergence_eq_setIntegral_pi_halfSpace hX hKc hKs himage, hdiv_coord]
  -- Stage 3: identify the `x₀ = 0` trace integral with the Riemannian boundary flux.
  rcases hcase with hα_bdry | hdisj
  · exact neg_integral_stdChartFlux_zero_eq_boundaryFlux ⟨α, hα_bdry⟩ hKs
  · exact neg_integral_stdChartFlux_zero_eq_boundaryFlux_of_disjoint hdisj

end HalfSpaceChart

end TauCeti.Manifold
