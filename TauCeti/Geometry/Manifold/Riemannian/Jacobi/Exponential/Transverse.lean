/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.ParameterJets
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.NormDet
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Basic
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bianchi
public import TauCeti.Analysis.InnerProductSpace.Compression
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Radial and transverse exponential Jacobi operators

The radial direction splits from the native exponential Jacobi operator. Gauss's lemma makes
its orthogonal complement invariant, and fixed compression gives the transverse Jacobi
equation, nonsingularity and determinant identity independently of curvature comparison.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 11.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff InnerProductSpace Manifold Topology

namespace TauCeti.Manifold.IsNormalDomain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  {p : M} {U : Set (TangentSpace I p)}

/-- The Jacobi determinant is the actual exponential density multiplied by the radial power. -/
theorem normDet_radialJacobiPosition (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l < r) (hseg : ∀ s ∈ Icc l r, s • v ∈ U)
    (h0 : 0 ∈ Icc l r) {t : ℝ} (ht : t ∈ Icc l r) :
    (h.radialJacobiPosition b v hlr.le hseg t).toLinearMap.normDet =
      |t| ^ Module.finrank ℝ E *
        LinearMap.normDet (U := TangentSpace I p)
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v)).toLinearMap := by
  let P := h.radialFrameCoordinates b v hlr.le hseg t
  let L : TangentSpace I p →L[ℝ] TangentSpace I (riemannianExp I M p (t • v)) :=
    mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v)
  have hP : P.toLinearMap =
      (h.radialParallelIsometry b v hlr hseg h0 ht).symm.toLinearEquiv.toLinearMap := by
    ext x
    exact h.radialFrameCoordinates_eq_symm b v hlr hseg h0 ht x
  have hPn : P.toLinearMap.normDet = 1 := by
    rw [hP]
    exact (h.radialParallelIsometry b v hlr hseg h0 ht).symm.toLinearIsometry.normDet_eq_one
  have heq : (h.radialJacobiPosition b v hlr.le hseg t).toLinearMap =
      P.toLinearMap ∘ₗ (t • L.toLinearMap) := by
    ext x
    simp only [ContinuousLinearMap.coe_coe, radialJacobiPosition_apply,
      LinearMap.comp_apply, LinearMap.smul_apply]
    -- Use the canonical tangent-space identification of a vector space for the differential.
    change P (L (t • x)) = P (t • L x)
    exact congrArg P (L.map_smul t x)
  rw [heq, LinearMap.normDet_comp_of_finrank_eq _ _
    ((finrank_tangentSpace (I := I) p).trans (finrank_tangentSpace (I := I) _).symm),
    hPn, one_mul, LinearMap.normDet_smul, Real.norm_eq_abs, finrank_tangentSpace]

/-- The radial direction is the radial eigenvector of the exponential Jacobi operator. -/
theorem radialJacobiPosition_radial (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l < r) (hseg : ∀ s ∈ Icc l r, s • v ∈ U)
    (h0 : 0 ∈ Icc l r) {t : ℝ} (ht : t ∈ Icc l r) :
    h.radialJacobiPosition b v hlr.le hseg t v = t • v := by
  let L : TangentSpace I p →L[ℝ] TangentSpace I (riemannianExp I M p (t • v)) :=
    mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v)
  have hL : L v = curveVelocity I (fun s : ℝ ↦ riemannianExp I M p (s • v)) t :=
    (curveVelocity_riemannianExp_smul (h.subset_expDomain (hseg t ht))).symm
  rw [radialJacobiPosition_apply]
  -- Identify the tangent space of the vector space at `t • v` with the initial tangent space.
  change (h.radialFrameCoordinates b v hlr.le hseg t) (L (t • v)) = t • v
  rw [map_smul, hL, map_smul,
    ← h.radialParallelLinearMap_radial b v hlr hseg h0 ht,
    h.radialFrameCoordinates_eq_symm b v hlr hseg h0 ht,
    ← h.radialParallelIsometry_apply b v hlr hseg h0 ht]
  simp

/-- The actual radial curvature operator annihilates the radial initial vector. -/
theorem radialJacobiCurvature_radial (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l < r) (hseg : ∀ s ∈ Icc l r, s • v ∈ U)
    (h0 : 0 ∈ Icc l r) {t : ℝ} (ht : t ∈ Icc l r) :
    h.radialJacobiCurvature b v hlr.le hseg t v = 0 := by
  rw [radialJacobiCurvature_apply,
    h.radialParallelLinearMap_radial b v hlr hseg h0 ht,
    (leviCivitaConnection I M).curvatureTensor_self, LinearMap.zero_apply, map_zero]

/-- Metric curvature symmetries make the genuine transported radial curvature symmetric. -/
theorem isSymmetric_radialJacobiCurvature (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l < r) (hseg : ∀ s ∈ Icc l r, s • v ∈ U)
    (h0 : 0 ∈ Icc l r) {t : ℝ} (ht : t ∈ Icc l r) :
    LinearMap.IsSymmetric (h.radialJacobiCurvature b v hlr.le hseg t).toLinearMap := by
  let e := h.radialParallelIsometry b v hlr hseg h0 ht
  let T := curveVelocity I (fun s : ℝ ↦ riemannianExp I M p (s • v)) t
  let R := (leviCivitaConnection I M).curvatureTensor (riemannianExp I M p (t • v))
  have hinner (x y : TangentSpace I p) :
      ⟪h.radialJacobiCurvature b v hlr.le hseg t x, y⟫_ℝ = ⟪R (e x) T T, e y⟫_ℝ := by
    rw [radialJacobiCurvature_apply,
      h.radialFrameCoordinates_eq_symm b v hlr hseg h0 ht,
      ← h.radialParallelIsometry_apply b v hlr hseg h0 ht]
    exact e.symm.inner_map_eq_flip _ _
  intro x y
  rw [ContinuousLinearMap.coe_coe, hinner]
  have hs : ⟪R (e x) T T, e y⟫_ℝ = ⟪e x, R (e y) T T⟫_ℝ := by
    dsimp only [R]
    rw [(isMetricCompatible_leviCivitaConnection I).inner_curvatureTensor_swap_pairs
      (torsion_leviCivitaConnection_eq_zero I),
      (leviCivitaConnection I M).curvatureTensor_antisymm _ T (e y),
      LinearMap.neg_apply, inner_neg_left,
      (isMetricCompatible_leviCivitaConnection I).inner_curvatureTensor_eq_neg, neg_neg]
  rw [hs, real_inner_comm, ← hinner, real_inner_comm]

/-- Gauss's lemma makes the exponential Jacobi operator preserve the initial transverse space. -/
theorem radialJacobiPosition_mem_orthogonal (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l < r) (hseg : ∀ s ∈ Icc l r, s • v ∈ U)
    (h0 : 0 ∈ Icc l r) {t : ℝ} (ht : t ∈ Icc l r)
    {w : TangentSpace I p} (hw : w ∈ (ℝ ∙ v)ᗮ) :
    h.radialJacobiPosition b v hlr.le hseg t w ∈ (ℝ ∙ v)ᗮ := by
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  let e := h.radialParallelIsometry b v hlr hseg h0 ht
  rw [radialJacobiPosition_apply,
    h.radialFrameCoordinates_eq_symm b v hlr hseg h0 ht, ← e.inner_map_eq_flip]
  rw [radialParallelIsometry_apply,
    h.radialParallelLinearMap_radial b v hlr hseg h0 ht,
    curveVelocity_riemannianExp_smul (h.subset_expDomain (hseg t ht))]
  exact inner_mfderiv_riemannianExp_radial_angular (h.subset_expDomain (hseg t ht))
    (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw)

/-- The transverse compression has the genuine polar Jacobian, including its radial power. -/
theorem normDet_compression_radialJacobiPosition (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {r : ℝ} (hr : 0 < r) (hseg : ∀ s ∈ Icc 0 r, s • v ∈ U)
    {t : ℝ} (ht : t ∈ Ioc 0 r) :
    ((h.radialJacobiPosition b v hr.le hseg t).compression (ℝ ∙ v)ᗮ.subtypeL).toLinearMap.normDet =
      t ^ Module.finrank ℝ (ℝ ∙ v)ᗮ * LinearMap.normDet (U := TangentSpace I p)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v)).toLinearMap := by
  let W := (ℝ ∙ v)ᗮ
  let J := h.radialJacobiPosition b v hr.le hseg t
  have hpres (w : TangentSpace I p) (hw : w ∈ W) : J w ∈ W :=
    h.radialJacobiPosition_mem_orthogonal b v hr hseg ⟨le_rfl, hr.le⟩ ⟨ht.1.le, ht.2⟩ hw
  have hcompression : (J.compression W.subtypeL).toLinearMap =
      (J.toLinearMap ∘ₗ W.subtype).codRestrict W (fun w ↦ hpres w w.prop) := by
    ext w
    exact ContinuousLinearMap.coe_compression_subtypeL_apply J W w (hpres w w.prop)
  have hnorm : (J.compression W.subtypeL).toLinearMap.normDet =
      (J.toLinearMap ∘ₗ W.subtype).normDet := by
    rw [hcompression]
    exact LinearMap.normDet_codRestrict (f := J.toLinearMap ∘ₗ W.subtype)
      (fun w ↦ hpres w w.prop)
  rcases eq_or_ne v 0 with rfl | hv
  · have hdim : Module.finrank ℝ W = Module.finrank ℝ E := by
      have hW : W = ⊤ := by
        simp only [W, Submodule.span_zero_singleton, Submodule.bot_orthogonal_eq_top]
      exact ((LinearEquiv.ofEq W ⊤ hW).trans Submodule.topEquiv).finrank_eq.trans
        (finrank_tangentSpace (I := I) p)
    rw [hnorm, LinearMap.normDet_comp_of_finrank_eq _ _
      (hdim.trans (finrank_tangentSpace (I := I) p).symm),
      LinearMap.normDet_subtype, mul_one]
    rw [hdim]
    simpa only [J, abs_of_pos ht.1] using
      h.normDet_radialJacobiPosition b 0 hr hseg ⟨le_rfl, hr.le⟩ ⟨ht.1.le, ht.2⟩
  have hrad : J v = t • v :=
    h.radialJacobiPosition_radial b v hr hseg ⟨le_rfl, hr.le⟩ ⟨ht.1.le, ht.2⟩
  have horth (w : TangentSpace I p) (hw : w ∈ W) : ⟪J v, J w⟫_ℝ = 0 := by
    rw [hrad, real_inner_smul_left,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hpres w hw), mul_zero]
  have hfactor := J.toLinearMap.normDet_eq_div_mul_normDet_orthogonal hv horth
  have hratio : ‖J v‖ / ‖v‖ = t := by
    rw [hrad, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1,
      mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hv)]
  rw [ContinuousLinearMap.coe_coe, hratio, ← hnorm] at hfactor
  have hdim : Module.finrank ℝ E = Module.finrank ℝ W + 1 := by
    have hd := (ℝ ∙ v).finrank_add_finrank_orthogonal
    simpa only [finrank_span_singleton hv, finrank_tangentSpace, Nat.add_comm] using hd.symm
  have hfull := h.normDet_radialJacobiPosition b v hr hseg ⟨le_rfl, hr.le⟩ ⟨ht.1.le, ht.2⟩
  rw [abs_of_pos ht.1, hdim, pow_succ, hfactor] at hfull
  apply mul_left_cancel₀ ht.1.ne'
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hfull

/-- On a positive normal ray the actual transverse Jacobi operator is nonsingular. -/
theorem isInvertible_compression_radialJacobiPosition (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {r : ℝ} (hr : 0 < r) (hseg : ∀ s ∈ Icc 0 r, s • v ∈ U)
    {t : ℝ} (ht : t ∈ Ioc 0 r) :
    ((h.radialJacobiPosition b v hr.le hseg t).compression (ℝ ∙ v)ᗮ.subtypeL).IsInvertible := by
  have h0 : 0 ∈ Icc (0 : ℝ) r := ⟨le_rfl, hr.le⟩
  have ht' : t ∈ Icc (0 : ℝ) r := ⟨ht.1.le, ht.2⟩
  let W := (ℝ ∙ v)ᗮ
  let J := h.radialJacobiPosition b v hr.le hseg t
  have hpres (w : TangentSpace I p) (hw : w ∈ W) : J w ∈ W :=
    h.radialJacobiPosition_mem_orthogonal b v hr hseg h0 ht' hw
  have hJ : Function.Injective J := by
    intro x y hxy
    have heq := (h.radialParallelIsometry b v hr hseg
      h0 ht').symm.injective
      (by simpa only [J, radialJacobiPosition_apply,
        h.radialFrameCoordinates_eq_symm b v hr hseg h0 ht'] using hxy)
    exact smul_right_injective _ ht.1.ne'
      (h.injective_mfderiv_riemannianExp (hseg t ht') heq)
  apply (ContinuousLinearMap.isInvertible_iff_injective_of_finrank_eq rfl).mpr
  intro x y hxy
  apply Subtype.ext
  apply hJ
  have heq := congrArg Subtype.val hxy
  -- Read the compressed endomorphism in the same initial tangent-space coordinates.
  change (J.compression W.subtypeL x : TangentSpace I p) =
    (J.compression W.subtypeL y : TangentSpace I p) at heq
  simpa only [ContinuousLinearMap.coe_compression_subtypeL_apply J W x (hpres x x.prop),
    ContinuousLinearMap.coe_compression_subtypeL_apply J W y (hpres y y.prop)] using heq

/-- Transverse compression commutes with the first radial Jacobi equation. -/
theorem hasDerivAt_compression_radialJacobiPosition (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ s ∈ Icc l r, s • v ∈ U)
    {t : ℝ} (ht : t ∈ Icc l r) :
    HasDerivAt (fun s ↦ (h.radialJacobiPosition b v hlr hseg s).compression
        (ℝ ∙ v)ᗮ.subtypeL)
      ((h.radialJacobiVelocity b v hlr hseg t).compression (ℝ ∙ v)ᗮ.subtypeL) t := by
  exact (h.hasDerivAt_radialJacobiPosition b v hlr hseg ht).compression _

/-- Gauss's lemma makes the compressed operators satisfy the genuine transverse Jacobi
equation. -/
theorem hasDerivAt_compression_radialJacobiVelocity (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l < r) (hseg : ∀ s ∈ Icc l r, s • v ∈ U)
    (h0 : 0 ∈ Icc l r) {t : ℝ} (ht : t ∈ Icc l r) :
    HasDerivAt (fun s ↦ (h.radialJacobiVelocity b v hlr.le hseg s).compression
        (ℝ ∙ v)ᗮ.subtypeL)
      (-(((h.radialJacobiCurvature b v hlr.le hseg t).compression
          (ℝ ∙ v)ᗮ.subtypeL).comp
        ((h.radialJacobiPosition b v hlr.le hseg t).compression (ℝ ∙ v)ᗮ.subtypeL))) t := by
  have hd := (h.hasDerivAt_radialJacobiVelocity b v hlr hseg h0 ht).compression
    (ℝ ∙ v)ᗮ.subtypeL
  have hcomp := ContinuousLinearMap.compression_comp_of_invariant
    (h.radialJacobiPosition b v hlr.le hseg t)
    (h.radialJacobiCurvature b v hlr.le hseg t) (ℝ ∙ v)ᗮ
    (fun _ hw ↦ h.radialJacobiPosition_mem_orthogonal b v hlr hseg h0 ht hw)
  simpa only [ContinuousLinearMap.compression_neg, hcomp] using hd

end TauCeti.Manifold.IsNormalDomain
