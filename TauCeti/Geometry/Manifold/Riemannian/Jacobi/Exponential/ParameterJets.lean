/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Parallel
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.Basic
public import TauCeti.Analysis.ODE.SecondOrder.ParameterJets
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Exponential Jacobi fields in the radial parallel frame

Radial parallel transport identifies the tangent spaces along a normal radial geodesic with
its initial tangent space. The differential of the exponential map and its covariant velocity,
read in that frame, solve the ordinary Jacobi equation. The coefficient is the actual
Levi-Civita curvature tensor transported to the initial tangent space.

This gives the geometric equation used in normal-coordinate parameter estimates.
The quantitative hypotheses concern the transported curvature coefficient and the parameter
regularity of the constructed fields; conversion from covariant curvature bounds is separate.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Lemma 5.7.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff InnerProductSpace Manifold Topology

/-- The canonical normed group on operator spaces, cached during geometric differentiation. -/
private local instance operatorGroup {𝕜 F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    NormedAddCommGroup (F →L[𝕜] G) := ContinuousLinearMap.toNormedAddCommGroup

/-- The canonical scalar action on operator spaces, cached during geometric differentiation. -/
private local instance operatorSpace {𝕜 F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    NormedSpace 𝕜 (F →L[𝕜] G) := ContinuousLinearMap.toNormedSpace

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  {p : M} {U : Set (TangentSpace I p)}

namespace IsNormalDomain

/-- The Jacobi curvature endomorphism, pulled back by radial parallel transport. -/
def radialJacobiCurvature (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ s ∈ Icc l r, s • v ∈ U) (t : ℝ) :
    TangentSpace I p →L[ℝ] TangentSpace I p :=
  let γ := fun s : ℝ ↦ riemannianExp I M p (s • v)
  let A := (((leviCivitaConnection I M).curvatureTensor (γ t)).flip
    (curveVelocity I γ t)).flip (curveVelocity I γ t)
  (h.radialFrameCoordinates b v hlr hseg t).comp
    (A.toContinuousLinearMap.comp
      (h.radialParallelLinearMap b v hlr hseg t).toContinuousLinearMap)

/-- The pulled-back curvature applies the native curvature tensor to the transported vector. -/
theorem radialJacobiCurvature_apply (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ s ∈ Icc l r, s • v ∈ U) (t : ℝ)
    (x : TangentSpace I p) :
    h.radialJacobiCurvature b v hlr hseg t x =
      h.radialFrameCoordinates b v hlr hseg t
        ((leviCivitaConnection I M).curvatureTensor (riemannianExp I M p (t • v))
          (h.radialParallelLinearMap b v hlr hseg t x)
          (curveVelocity I (fun s : ℝ ↦ riemannianExp I M p (s • v)) t)
          (curveVelocity I (fun s : ℝ ↦ riemannianExp I M p (s • v)) t)) := by
  rfl

/-- The differential of the radial exponential variation, read in the parallel frame. -/
def radialJacobiPosition (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ s ∈ Icc l r, s • v ∈ U) (t : ℝ) :
    TangentSpace I p →L[ℝ] TangentSpace I p :=
  (h.radialFrameCoordinates b v hlr hseg t).comp
    ((mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v)).comp
      (t • ContinuousLinearMap.id ℝ (TangentSpace I p)))

/-- The position operator is the parallel-frame reading of the native exponential Jacobi field. -/
theorem radialJacobiPosition_apply (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ s ∈ Icc l r, s • v ∈ U)
    (t : ℝ) (w : TangentSpace I p) :
    h.radialJacobiPosition b v hlr hseg t w =
      h.radialFrameCoordinates b v hlr hseg t
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) (t • w)) := by
  rfl

/-- The covariant velocity of the exponential Jacobi operator in radial parallel coordinates. -/
def radialJacobiVelocity (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ s ∈ Icc l r, s • v ∈ U) (t : ℝ) :
    TangentSpace I p →L[ℝ] TangentSpace I p :=
  ∑ i, InnerProductSpace.rankOne ℝ
    (h.radialFrameCoordinates b v hlr hseg t
      (alongCurveWithin (leviCivitaConnection I M)
        (fun s : ℝ ↦ riemannianExp I M p (s • v))
        (fun s ↦ mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (s • v) (s • b i))
        (geodesicInterval I M p v) t)) (b i)

/-- Each velocity column is the native covariant derivative of its exponential Jacobi field. -/
theorem radialJacobiVelocity_apply_basis (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ s ∈ Icc l r, s • v ∈ U) (t : ℝ) (i : ι) :
    h.radialJacobiVelocity b v hlr hseg t (b i) =
      h.radialFrameCoordinates b v hlr hseg t
        (alongCurveWithin (leviCivitaConnection I M)
          (fun s : ℝ ↦ riemannianExp I M p (s • v))
          (fun s ↦ mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p)
            (s • v) (s • b i)) (geodesicInterval I M p v) t) := by
  simp [radialJacobiVelocity, InnerProductSpace.rankOne_apply,
    orthonormal_iff_ite.mp b.orthonormal]

/-- The exponential Jacobi operator starts at zero. -/
@[simp]
theorem radialJacobiPosition_zero (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ s ∈ Icc l r, s • v ∈ U) :
    h.radialJacobiPosition b v hlr hseg 0 = 0 := by
  simp only [radialJacobiPosition, zero_smul ℝ (ContinuousLinearMap.id ℝ (TangentSpace I p))]
  exact ContinuousLinearMap.comp_zero
    ((h.radialFrameCoordinates b v hlr hseg 0).comp
      (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (0 • v)))

/-- The initial covariant velocity of the exponential Jacobi operator is the identity. -/
@[simp]
theorem radialJacobiVelocity_zero (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ s ∈ Icc l r, s • v ∈ U) :
    h.radialJacobiVelocity b v hlr hseg 0 = ContinuousLinearMap.id ℝ (TangentSpace I p) := by
  apply ContinuousLinearMap.coe_injective
  apply b.toBasis.ext
  intro i
  -- Evaluating the coerced continuous linear map exposes the basis-vector identity.
  change h.radialJacobiVelocity b v hlr hseg 0 (b i) = b i
  rw [radialJacobiVelocity_apply_basis, radialFrameCoordinates_apply]
  have hbase : riemannianExp I M p ((0 : ℝ) • v) = p := by
    rw [zero_smul, riemannianExp_zero]
  have hinner (j : ι) := congrArg
    (fun q : M ↦ @inner ℝ (TangentSpace I q) _ (b j) (b i)) hbase
  simp only [radialParallelLinearMap_apply_zero,
    alongCurveWithin_mfderiv_riemannianExp_zero, hinner]
  exact b.sum_repr' (b i)

/-- The first ordinary equation for each column of the radial exponential Jacobi operator. -/
theorem hasDerivAt_radialJacobiPosition_apply_basis (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ s ∈ Icc l r, s • v ∈ U) {t : ℝ}
    (ht : t ∈ Icc l r) (i : ι) :
    HasDerivAt (fun s ↦ h.radialJacobiPosition b v hlr hseg s (b i))
      (h.radialJacobiVelocity b v hlr hseg t (b i)) t := by
  let γ := fun s : ℝ ↦ riemannianExp I M p (s • v)
  let J := fun s : ℝ ↦ mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p)
    (s • v) (s • b i)
  have hmem : t ∈ geodesicInterval I M p v :=
    mem_geodesicInterval_iff_smul_mem_expDomain.mpr (h.subset_expDomain (hseg t ht))
  have hJ := isJacobiFieldOn_mfderiv_riemannianExp p v (b i)
  have hcoord := differentiableAt_sectionCoord γ J
    ((hJ.contMDiffOn.contMDiffAt
      (isOpen_geodesicInterval.mem_nhds hmem)).mdifferentiableAt (by norm_num))
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hd := h.hasDerivAt_radialFrameCoordinates b v hlr hseg ht hcoord
  rw [radialJacobiVelocity_apply_basis,
    alongCurveWithin_of_mem_nhds _ _ _ (isOpen_geodesicInterval.mem_nhds hmem)]
  simpa only [radialJacobiPosition_apply] using hd

/-- The second ordinary Jacobi equation follows from the native curvature equation. -/
theorem hasDerivAt_radialJacobiVelocity_apply_basis (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l < r) (hseg : ∀ s ∈ Icc l r, s • v ∈ U)
    (h0 : 0 ∈ Icc l r) {t : ℝ} (ht : t ∈ Icc l r) (i : ι) :
    HasDerivAt (fun s ↦ h.radialJacobiVelocity b v hlr.le hseg s (b i))
      (-(h.radialJacobiCurvature b v hlr.le hseg t)
        (h.radialJacobiPosition b v hlr.le hseg t (b i))) t := by
  let γ := fun s : ℝ ↦ riemannianExp I M p (s • v)
  let J := fun s : ℝ ↦ mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p)
    (s • v) (s • b i)
  have hmem : t ∈ geodesicInterval I M p v :=
    mem_geodesicInterval_iff_smul_mem_expDomain.mpr (h.subset_expDomain (hseg t ht))
  have hJ := isJacobiFieldOn_mfderiv_riemannianExp p v (b i)
  have hcoord := differentiableAt_sectionCoord γ _
    ((hJ.contMDiffOn_alongCurveWithin.contMDiffAt
      (isOpen_geodesicInterval.mem_nhds hmem)).mdifferentiableAt (by norm_num))
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hd := h.hasDerivAt_radialFrameCoordinates b v hlr.le hseg ht hcoord
  have hDD := hJ.alongCurveWithin_alongCurveWithin_eq hmem
  rw [alongCurveWithin_of_mem_nhds _ _ _ (isOpen_geodesicInterval.mem_nhds hmem),
    curveVelocityWithin_of_mem_nhds (isOpen_geodesicInterval.mem_nhds hmem)] at hDD
  rw [hDD, map_neg] at hd
  have hR : h.radialJacobiCurvature b v hlr.le hseg t
      (h.radialJacobiPosition b v hlr.le hseg t (b i)) =
      h.radialFrameCoordinates b v hlr.le hseg t
        ((leviCivitaConnection I M).curvatureTensor (γ t) (J t)
          (curveVelocity I γ t) (curveVelocity I γ t)) := by
    rw [radialJacobiCurvature_apply, radialJacobiPosition_apply,
      h.radialParallelLinearMap_radialFrameCoordinates b v hlr hseg h0 ht]
  simpa only [radialJacobiVelocity_apply_basis, hR] using hd

/-- The exponential Jacobi position as a function of time and initial ray velocity.
Its value is zero outside the rays whose prescribed segment stays in the normal domain. -/
def radialJacobiPositionFamily (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {l r : ℝ} (hlr : l ≤ r)
    (z : ℝ × TangentSpace I p) : TangentSpace I p →L[ℝ] TangentSpace I p := by
  classical
  exact if hseg : ∀ s ∈ Icc l r, s • z.2 ∈ U then
    h.radialJacobiPosition b z.2 hlr hseg z.1 else 0

/-- The exponential Jacobi velocity as a function of time and initial ray velocity.
Its value is zero outside the prescribed normal-ray domain. -/
def radialJacobiVelocityFamily (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {l r : ℝ} (hlr : l ≤ r)
    (z : ℝ × TangentSpace I p) : TangentSpace I p →L[ℝ] TangentSpace I p := by
  classical
  exact if hseg : ∀ s ∈ Icc l r, s • z.2 ∈ U then
    h.radialJacobiVelocity b z.2 hlr hseg z.1 else 0

/-- Transported curvature as a function of time and initial ray velocity.
Its value is zero outside the prescribed normal-ray domain. -/
def radialJacobiCurvatureFamily (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {l r : ℝ} (hlr : l ≤ r)
    (z : ℝ × TangentSpace I p) : TangentSpace I p →L[ℝ] TangentSpace I p := by
  classical
  exact if hseg : ∀ s ∈ Icc l r, s • z.2 ∈ U then
    h.radialJacobiCurvature b z.2 hlr hseg z.1 else 0

/-- On a normal ray the position family is the geometric Jacobi position. -/
@[simp]
theorem radialJacobiPositionFamily_eq (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {l r : ℝ} (hlr : l ≤ r)
    {z : ℝ × TangentSpace I p} (hseg : ∀ s ∈ Icc l r, s • z.2 ∈ U) :
    h.radialJacobiPositionFamily b hlr z = h.radialJacobiPosition b z.2 hlr hseg z.1 := by
  simp only [radialJacobiPositionFamily, dite_eq_left hseg]

/-- The position family is zero when the prescribed segment leaves the normal domain. -/
@[simp]
theorem radialJacobiPositionFamily_eq_zero (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {l r : ℝ} (hlr : l ≤ r)
    {z : ℝ × TangentSpace I p} (hseg : ∃ s, l ≤ s ∧ s ≤ r ∧ s • z.2 ∉ U) :
    h.radialJacobiPositionFamily b hlr z = 0 := by
  have hnot : ¬ ∀ s ∈ Icc l r, s • z.2 ∈ U := by
    obtain ⟨s, hls, hsr, hs⟩ := hseg
    exact fun h ↦ hs (h s ⟨hls, hsr⟩)
  simp only [radialJacobiPositionFamily, dite_eq_right hnot]

/-- On a normal ray the velocity family is the geometric Jacobi velocity. -/
@[simp]
theorem radialJacobiVelocityFamily_eq (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {l r : ℝ} (hlr : l ≤ r)
    {z : ℝ × TangentSpace I p} (hseg : ∀ s ∈ Icc l r, s • z.2 ∈ U) :
    h.radialJacobiVelocityFamily b hlr z = h.radialJacobiVelocity b z.2 hlr hseg z.1 := by
  simp only [radialJacobiVelocityFamily, dite_eq_left hseg]

/-- The velocity family is zero when the prescribed segment leaves the normal domain. -/
@[simp]
theorem radialJacobiVelocityFamily_eq_zero (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {l r : ℝ} (hlr : l ≤ r)
    {z : ℝ × TangentSpace I p} (hseg : ∃ s, l ≤ s ∧ s ≤ r ∧ s • z.2 ∉ U) :
    h.radialJacobiVelocityFamily b hlr z = 0 := by
  have hnot : ¬ ∀ s ∈ Icc l r, s • z.2 ∈ U := by
    obtain ⟨s, hls, hsr, hs⟩ := hseg
    exact fun h ↦ hs (h s ⟨hls, hsr⟩)
  simp only [radialJacobiVelocityFamily, dite_eq_right hnot]

/-- On a normal ray the curvature family is the actual transported curvature tensor. -/
@[simp]
theorem radialJacobiCurvatureFamily_eq (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {l r : ℝ} (hlr : l ≤ r)
    {z : ℝ × TangentSpace I p} (hseg : ∀ s ∈ Icc l r, s • z.2 ∈ U) :
    h.radialJacobiCurvatureFamily b hlr z = h.radialJacobiCurvature b z.2 hlr hseg z.1 := by
  simp only [radialJacobiCurvatureFamily, dite_eq_left hseg]

/-- The curvature family is zero when the prescribed segment leaves the normal domain. -/
@[simp]
theorem radialJacobiCurvatureFamily_eq_zero (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {l r : ℝ} (hlr : l ≤ r)
    {z : ℝ × TangentSpace I p} (hseg : ∃ s, l ≤ s ∧ s ≤ r ∧ s • z.2 ∉ U) :
    h.radialJacobiCurvatureFamily b hlr z = 0 := by
  have hnot : ¬ ∀ s ∈ Icc l r, s • z.2 ∈ U := by
    obtain ⟨s, hls, hsr, hs⟩ := hseg
    exact fun h ↦ hs (h s ⟨hls, hsr⟩)
  simp only [radialJacobiCurvatureFamily, dite_eq_right hnot]

/-- The constructed radial exponential Jacobi family satisfies its ordinary operator equation.
Only differentiability of the concrete coefficient readings is assumed; the equation is derived
from the geometric Jacobi equation and radial parallel transport. -/
theorem radialJacobiFamily_timeFDeriv (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {l r : ℝ} (hlr : l < r)
    (h0 : 0 ∈ Icc l r) {z : ℝ × TangentSpace I p} (ht : z.1 ∈ Icc l r)
    (hseg : ∀ s ∈ Icc l r, s • z.2 ∈ U)
    (hJ : DifferentiableAt ℝ (h.radialJacobiPositionFamily b hlr.le) z)
    (hV : DifferentiableAt ℝ (h.radialJacobiVelocityFamily b hlr.le) z) :
    timeFDeriv (h.radialJacobiPositionFamily b hlr.le) z.1 z.2 =
        h.radialJacobiVelocityFamily b hlr.le z ∧
      timeFDeriv (h.radialJacobiVelocityFamily b hlr.le) z.1 z.2 =
        -(h.radialJacobiCurvatureFamily b hlr.le z).comp
          (h.radialJacobiPositionFamily b hlr.le z) := by
  constructor
  · apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro i
    have hd := (hasDerivAt_parameterCurve hJ).clm_apply (hasDerivAt_const z.1 (b i))
    simp only [map_zero, add_zero] at hd
    have heq : (fun s ↦ h.radialJacobiPositionFamily b hlr.le (s, z.2) (b i)) =
        fun s ↦ h.radialJacobiPosition b z.2 hlr.le hseg s (b i) := by
      funext s
      rw [h.radialJacobiPositionFamily_eq b hlr.le (z := (s, z.2)) hseg]
    rw [heq] at hd
    rw [h.radialJacobiVelocityFamily_eq b hlr.le (z := z) hseg]
    exact hd.unique (h.hasDerivAt_radialJacobiPosition_apply_basis b z.2 hlr.le hseg ht i)
  · apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro i
    have hd := (hasDerivAt_parameterCurve hV).clm_apply (hasDerivAt_const z.1 (b i))
    simp only [map_zero, add_zero] at hd
    have heq : (fun s ↦ h.radialJacobiVelocityFamily b hlr.le (s, z.2) (b i)) =
        fun s ↦ h.radialJacobiVelocity b z.2 hlr.le hseg s (b i) := by
      funext s
      rw [h.radialJacobiVelocityFamily_eq b hlr.le (z := (s, z.2)) hseg]
    rw [heq] at hd
    rw [h.radialJacobiCurvatureFamily_eq b hlr.le hseg,
      h.radialJacobiPositionFamily_eq b hlr.le hseg]
    exact hd.unique
      (h.hasDerivAt_radialJacobiVelocity_apply_basis b z.2 hlr hseg h0 ht i)

private theorem radialJacobiFamily_initialJet_le (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {l r : ℝ} (hlr : l ≤ r)
    {W : Set (ℝ × TangentSpace I p)} (hW : IsOpen W) {q : TangentSpace I p}
    (hq : (0, q) ∈ W)
    (hWseg : ∀ z ∈ W, ∀ s ∈ Icc l r, s • z.2 ∈ U) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun q ↦
      (h.radialJacobiPositionFamily b hlr (0, q),
        h.radialJacobiVelocityFamily b hlr (0, q))) q‖ ≤ 1 := by
  have heq : (fun q ↦ (h.radialJacobiPositionFamily b hlr (0, q),
        h.radialJacobiVelocityFamily b hlr (0, q))) =ᶠ[𝓝 q]
      fun _ ↦ ((0 : TangentSpace I p →L[ℝ] TangentSpace I p),
        ContinuousLinearMap.id ℝ (TangentSpace I p)) := by
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hW.mem_nhds hq)] with q' hq'
    -- The continuity API presents this as membership in the time-zero slice's preimage.
    change (0, q') ∈ W at hq'
    rw [h.radialJacobiPositionFamily_eq b hlr (z := (0, q')) (hWseg _ hq'),
      h.radialJacobiVelocityFamily_eq b hlr (hWseg _ hq'),
      radialJacobiPosition_zero, radialJacobiVelocity_zero]
  rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
  by_cases hj : j = 0
  · subst j
    simp only [norm_iteratedFDeriv_zero]
    rw [Prod.norm_def]
    exact max_le (by
      calc ‖(0 : TangentSpace I p →L[ℝ] TangentSpace I p)‖ = 0 :=
          ContinuousLinearMap.opNorm_zero
        _ ≤ 1 := zero_le_one) (ContinuousLinearMap.norm_id_le (𝕜 := ℝ))
  · simp only [iteratedFDeriv_const_of_ne hj, Pi.zero_apply, norm_zero]
    exact zero_le_one

/-- Parameter jets of the constructed exponential Jacobi operator and its covariant velocity
are controlled by the parameter jets of actual transported curvature. This is a geometric
application of the operator Jacobi estimate, with its ODE and constant initial data proved here. -/
theorem norm_iteratedFDeriv_radialJacobiFamily_le (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {l r : ℝ} (hlr : l < r)
    (n : ℕ) {W : Set (ℝ × TangentSpace I p)} (hW : IsOpen W)
    {q : TangentSpace I p} (hqW : ∀ s ∈ Icc (0 : ℝ) 1, (s, q) ∈ W)
    (hWtime : ∀ z ∈ W, z.1 ∈ Icc l r)
    (hWseg : ∀ z ∈ W, ∀ s ∈ Icc l r, s • z.2 ∈ U)
    (hR : ContDiffOn ℝ n (h.radialJacobiCurvatureFamily b hlr.le) W)
    (hJ : ContDiffOn ℝ (n + 1) (h.radialJacobiPositionFamily b hlr.le) W)
    (hV : ContDiffOn ℝ (n + 1) (h.radialJacobiVelocityFamily b hlr.le) W)
    {C : ℝ} (hbound : ∀ j ≤ n, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ j (fun q ↦ h.radialJacobiCurvatureFamily b hlr.le (s, q)) q‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun q ↦ (h.radialJacobiPositionFamily b hlr.le (1, q),
      h.radialJacobiVelocityFamily b hlr.le (1, q))) q‖ ≤
      Real.exp ((2 : ℝ) ^ n * max 1 C) := by
  have h0W := hqW 0 ⟨le_rfl, zero_le_one⟩
  have h0 := hWtime _ h0W
  have hode := fun z hz ↦ h.radialJacobiFamily_timeFDeriv b hlr h0
    (hWtime z hz) (hWseg z hz)
    ((hJ.contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp))
    ((hV.contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp))
  have hb := TauCeti.norm_iteratedFDeriv_le_exp_of_operatorJacobiODE n
    (a := 0) (b := 1) (t₀ := 0) (D := 1) ⟨le_rfl, zero_le_one⟩ hW hqW hR hJ hV
    (fun z hz ↦ (hode z hz).1) (fun z hz ↦ (hode z hz).2)
    (fun j _ ↦ h.radialJacobiFamily_initialJet_le b hlr.le hW h0W hWseg j) hbound
    ⟨zero_le_one, le_rfl⟩
  simpa only [one_mul, sub_zero, abs_one, mul_one] using hb

/-- The radial-coframe reading of the differential of the exponential map has exponentially
bounded parameter jets when the concrete Jacobi coefficient jets are controlled. -/
theorem norm_iteratedFDeriv_radialJacobiPositionFamily_le (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {l r : ℝ} (hlr : l < r)
    (n : ℕ) {W : Set (ℝ × TangentSpace I p)} (hW : IsOpen W)
    {q : TangentSpace I p} (hqW : ∀ s ∈ Icc (0 : ℝ) 1, (s, q) ∈ W)
    (hWtime : ∀ z ∈ W, z.1 ∈ Icc l r)
    (hWseg : ∀ z ∈ W, ∀ s ∈ Icc l r, s • z.2 ∈ U)
    (hR : ContDiffOn ℝ n (h.radialJacobiCurvatureFamily b hlr.le) W)
    (hJ : ContDiffOn ℝ (n + 1) (h.radialJacobiPositionFamily b hlr.le) W)
    (hV : ContDiffOn ℝ (n + 1) (h.radialJacobiVelocityFamily b hlr.le) W)
    {C : ℝ} (hbound : ∀ j ≤ n, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ j (fun q ↦ h.radialJacobiCurvatureFamily b hlr.le (s, q)) q‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun q ↦ h.radialJacobiPositionFamily b hlr.le (1, q)) q‖ ≤
      Real.exp ((2 : ℝ) ^ n * max 1 C) := by
  have h1W := hqW 1 ⟨zero_le_one, le_rfl⟩
  have hb := h.norm_iteratedFDeriv_radialJacobiFamily_le b hlr n hW hqW
    hWtime hWseg hR hJ hV hbound
  rw [iteratedFDeriv_prodMk (hJ.contDiffAt_timeSlice hW h1W)
    (hV.contDiffAt_timeSlice hW h1W) (by exact_mod_cast Nat.le_succ n),
    ContinuousMultilinearMap.opNorm_prod] at hb
  exact (le_max_left _ _).trans hb

end IsNormalDomain

end TauCeti.Manifold
