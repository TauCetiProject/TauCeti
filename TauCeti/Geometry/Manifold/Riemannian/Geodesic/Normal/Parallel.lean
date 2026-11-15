/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Frame.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Translate
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Pullback
public import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
public import TauCeti.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Analysis.ODE.DysonSeries
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric

/-!
# Parallel transport along normal radial geodesics

A normal orthonormal frame identifies the parallel-field equation with a linear operator ODE
on the initial tangent space. A smooth extension of the connection coefficients near
a prescribed closed radial segment allows the Dyson series to solve this equation.
Reconstruction in the moving frame gives tangent fields whose Levi-Civita derivative
vanishes. Metric compatibility proves inner-product preservation, and finite dimensionality
then gives linear isometry equivalences between the endpoint tangent spaces.

The coefficient extension is auxiliary: all statements on the radial segment use the original
geometric connection operator. On a prescribed segment containing `0` the construction is
geometric parallel transport from `p`, and so does not depend on the segment
(`radialParallelLinearMap_eq_of_mem`); outside the segment it carries no geometric meaning.
Neither a prescribed parallel frame nor a model scalar equation is assumed.

See J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 4.
-/

public noncomputable section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff InnerProductSpace Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  {p : M} {U : Set (TangentSpace I p)}

variable [I.Boundaryless] [T2Space M]

namespace IsNormalDomain

private theorem exists_radialConnectionExtension (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (_hlr : l ≤ r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U) :
    ∃ A : ℝ → TangentSpace I p →L[ℝ] TangentSpace I p,
      ContDiff ℝ ∞ A ∧ ∀ t ∈ Icc l r, A =ᶠ[𝓝 t]
        (fun s : ℝ ↦ -b.normalFrameConnectionOperator (U := U) v
          (riemannianExp I M p (s • v))) := by
  obtain ⟨A, hA, -, -, -, hEq⟩ :=
    (h.contDiffOn_normalFrameConnectionOperator_radial b v).neg
      |>.exists_contDiff_eventuallyEq_on_isCompact isCompact_Icc
        (h.isOpen.preimage (continuous_id.smul continuous_const)) hseg
  exact ⟨A, hA, hEq⟩

private def radialConnectionExtension (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U) :
    ℝ → TangentSpace I p →L[ℝ] TangentSpace I p :=
  Classical.choose (h.exists_radialConnectionExtension b v hlr hseg)

private theorem contDiff_radialConnectionExtension (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U) :
    ContDiff ℝ ∞ (h.radialConnectionExtension b v hlr hseg) :=
  (Classical.choose_spec (h.exists_radialConnectionExtension b v hlr hseg)).1

private theorem radialConnectionExtension_eventuallyEq (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U) :
    ∀ t ∈ Icc l r, h.radialConnectionExtension b v hlr hseg =ᶠ[𝓝 t]
      (fun s : ℝ ↦ -b.normalFrameConnectionOperator (U := U) v
        (riemannianExp I M p (s • v))) :=
  (Classical.choose_spec (h.exists_radialConnectionExtension b v hlr hseg)).2

/-- The Dyson solution for the normal-frame parallel equation near a closed radial segment.

It is built from an auxiliary smooth extension of the connection coefficients, so it solves the
geometric coefficient equation only at parameters of the prescribed segment `Icc l r`. When that
segment contains `0`, its frame reconstruction is geometric parallel transport from `p` along
the radial geodesic at every parameter of the segment, independently of the segment chosen
(`radialParallelCoefficients_eq_of_mem`). Outside the segment its values depend on the
auxiliary extension. -/
def radialParallelCoefficients (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U) (t : ℝ) :
    TangentSpace I p →L[ℝ] TangentSpace I p :=
  TauCeti.dysonSeriesLeft (h.radialConnectionExtension b v hlr hseg) t

/-- The coefficient propagator starts at the identity. -/
@[simp]
theorem radialParallelCoefficients_zero (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U) :
    h.radialParallelCoefficients b v hlr hseg 0 = 1 := by
  exact TauCeti.dysonSeriesLeft_zero _

/-- The coefficient propagator is smooth. -/
theorem contDiff_radialParallelCoefficients (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U) :
    ContDiff ℝ ∞ (h.radialParallelCoefficients b v hlr hseg) := by
  rw [contDiff_infty]
  intro n
  exact (TauCeti.contDiff_dysonSeriesLeft
    ((h.contDiff_radialConnectionExtension b v hlr hseg).of_le (m := (n : ℕ∞ω))
      (by simp))).of_le (by exact_mod_cast Nat.le_succ n)

/-- The frame reconstruction of the coefficient propagator at the radial parameter `t`.

When `t` and `0` both lie in the prescribed segment `Icc l r`, this is parallel transport from
`p` along the radial geodesic `s ↦ exp_p (s • v)` (see `alongCurve_radialParallel_eq_zero` and
`radialParallelLinearMap_eq_of_mem`). For other parameters it depends on the auxiliary
coefficient extension and carries no geometric meaning. -/
def radialParallelLinearMap (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (v : TangentSpace I p) {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U) (t : ℝ) :
    TangentSpace I p →ₗ[ℝ] TangentSpace I (riemannianExp I M p (t • v)) where
  toFun a := b.normalFrameExpansion (U := U) (riemannianExp I M p (t • v))
    (radialParallelCoefficients (U := U) h b v hlr hseg t a)
  map_add' a a' := by simp
  map_smul' c a := by simp

/-- The radial transport map reconstructs the Dyson solution in the moving orthonormal frame.
This is parallel transport only at parameters of a prescribed segment containing `0`. -/
theorem radialParallelLinearMap_apply (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (v : TangentSpace I p) {l r : ℝ} (hlr : l ≤ r)
    (hseg : ∀ t ∈ Icc l r, t • v ∈ U) (t : ℝ) (a : TangentSpace I p) :
    radialParallelLinearMap (U := U) h b v hlr hseg t a =
      b.normalFrameExpansion (U := U) (riemannianExp I M p (t • v))
        (radialParallelCoefficients (U := U) h b v hlr hseg t a) := by rfl

/-- Covariant differentiation of a reconstructed field is its coefficient derivative plus
connection. -/
theorem inner_alongCurve_normalFrameExpansion (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {y : ℝ → TangentSpace I p} {t : ℝ} {y' : TangentSpace I p}
    (hy : HasDerivAt y y' t) (ht : t • v ∈ U) (k : ι) :
    ⟪normalOrthonormalFrame I M p U b k (riemannianExp I M p (t • v)),
      alongCurve (leviCivitaConnection I M)
        (fun s : ℝ ↦ riemannianExp I M p (s • v))
        (fun s ↦ b.normalFrameExpansion (U := U) (riemannianExp I M p (s • v)) (y s)) t⟫_ℝ =
      ⟪b k, y' + b.normalFrameConnectionOperator (U := U) v
        (riemannianExp I M p (t • v)) (y t)⟫_ℝ := by
  set γ := fun s : ℝ ↦ riemannianExp I M p (s • v)
  let e := fun i s ↦ normalOrthonormalFrame I M p U b i (γ s)
  have hq : γ t ∈ riemannianExp I M p '' U := mem_image_of_mem _ ht
  have hlin : ContDiff ℝ ∞ (fun s : ℝ ↦ s • v) := contDiff_id.smul contDiff_const
  have hγ : MDiffAt γ t :=
    ((contMDiffAt_riemannianExp (h.subset_expDomain ht)).comp t
      hlin.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have he (i : ι) : MDiffAt (T% (normalOrthonormalFrame I M p U b i)) (γ t) :=
    ((h.contMDiffOn_normalOrthonormalFrame b i).contMDiffAt
      (h.isOpen_image.mem_nhds hq)).mdifferentiableAt (by simp)
  have hecoord (i : ι) : DifferentiableAt ℝ (sectionCoord (F := E) γ (e i) (γ t)) t :=
    differentiableAt_sectionCoord γ (e i) ((he i).comp t hγ)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hcoeff (i : ι) : HasDerivAt (fun s ↦ ⟪b i, y s⟫_ℝ) ⟪b i, y'⟫_ℝ t :=
    (innerSL ℝ (b i)).hasFDerivAt.comp_hasDerivAt t hy
  have hterm (i : ι) : DifferentiableAt ℝ
      (sectionCoord (F := E) γ (fun s ↦ ⟪b i, y s⟫_ℝ • e i s) (γ t)) t := by
    rw [sectionCoord_smul]
    exact (hcoeff i).differentiableAt.smul (hecoord i)
  have hframe (i : ι) : alongCurve (leviCivitaConnection I M) γ (e i) t =
      leviCivitaConnection I M (normalOrthonormalFrame I M p U b i) (γ t)
        (normalCoordinateField I M p U v (γ t)) := by
    rw [alongCurve_pullback (leviCivitaConnection I M) γ _
      (hasMFDerivAt_curveVelocity hγ) (he i),
      h.curveVelocity_riemannianExp_smul_eq_normalCoordinateField ht]
  have hexp : (fun s ↦ b.normalFrameExpansion (U := U) (γ s) (y s)) =
      (fun s ↦ ∑ i, ⟪b i, y s⟫_ℝ • e i s) := by
    funext s
    exact b.normalFrameExpansion_apply (γ s) (y s)
  rw [hexp, alongCurve_sum _ _ Finset.univ _ (fun i _ ↦ hterm i), inner_sum]
  simp only [alongCurve_smul _ _ _ _ (hcoeff _).differentiableAt (hecoord _),
    (hcoeff _).deriv, hframe, inner_add_right, real_inner_smul_right]
  rw [Finset.sum_add_distrib, OrthonormalBasis.inner_normalFrameConnectionOperator]
  have horth := orthonormal_iff_ite.mp (h.orthonormal_normalOrthonormalFrame b hq)
  have hfirst : ∑ i, ⟪b i, y'⟫_ℝ *
      ⟪normalOrthonormalFrame I M p U b k (γ t), e i t⟫_ℝ = ⟪b k, y'⟫_ℝ := by
    simp [e, horth]
  rw [hfirst]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [γ]
  rw [OrthonormalBasis.normalFrameConnectionCoefficient_apply, mul_comm]
  congr 1
  exact real_inner_comm _ _

/-- A differentiable coefficient path reconstructs a differentiable tangent field along a radial
curve. -/
theorem differentiableAt_sectionCoord_normalFrameExpansion (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {y : ℝ → TangentSpace I p} {t : ℝ} (hy : DifferentiableAt ℝ y t) (ht : t • v ∈ U) :
    DifferentiableAt ℝ (sectionCoord (F := E)
      (fun s : ℝ ↦ riemannianExp I M p (s • v))
      (fun s ↦ b.normalFrameExpansion (U := U) (riemannianExp I M p (s • v)) (y s))
      (riemannianExp I M p (t • v))) t := by
  set γ := fun s : ℝ ↦ riemannianExp I M p (s • v)
  have hq : γ t ∈ riemannianExp I M p '' U := mem_image_of_mem _ ht
  have hlin : ContDiff ℝ ∞ (fun s : ℝ ↦ s • v) := contDiff_id.smul contDiff_const
  have hγ : MDiffAt γ t :=
    ((contMDiffAt_riemannianExp (h.subset_expDomain ht)).comp t
      hlin.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have hecoord (i : ι) : DifferentiableAt ℝ (sectionCoord (F := E) γ
      (fun s ↦ normalOrthonormalFrame I M p U b i (γ s)) (γ t)) t :=
    differentiableAt_sectionCoord γ _
      ((((h.contMDiffOn_normalOrthonormalFrame b i).contMDiffAt
        (h.isOpen_image.mem_nhds hq)).mdifferentiableAt (by simp)).comp t hγ)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hexp : (fun s ↦ b.normalFrameExpansion (U := U) (γ s) (y s)) =
      (fun s ↦ ∑ i, ⟪b i, y s⟫_ℝ • normalOrthonormalFrame I M p U b i (γ s)) := by
    funext s
    exact b.normalFrameExpansion_apply (γ s) (y s)
  rw [hexp, sectionCoord_sum]
  apply DifferentiableAt.fun_sum
  intro i _
  rw [sectionCoord_smul]
  exact ((innerSL ℝ (b i)).differentiableAt.comp t hy).smul (hecoord i)

/-- Solving the geometric coefficient equation gives a parallel tangent field. -/
theorem alongCurve_normalFrameExpansion_eq_zero (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {y : ℝ → TangentSpace I p} {t : ℝ}
    (hy : HasDerivAt y (-b.normalFrameConnectionOperator (U := U) v
      (riemannianExp I M p (t • v)) (y t)) t) (ht : t • v ∈ U) :
    alongCurve (leviCivitaConnection I M)
      (fun s : ℝ ↦ riemannianExp I M p (s • v))
      (fun s ↦ b.normalFrameExpansion (U := U) (riemannianExp I M p (s • v)) (y s)) t = 0 := by
  let γ := fun s : ℝ ↦ riemannianExp I M p (s • v)
  have hq : γ t ∈ riemannianExp I M p '' U := mem_image_of_mem _ ht
  let bq : OrthonormalBasis ι ℝ (TangentSpace I (γ t)) :=
    OrthonormalBasis.mk (h.orthonormal_normalOrthonormalFrame b hq)
      ((h.isLocalFrameOn_normalOrthonormalFrame b).generating hq)
  have hzero (k : ι) :
      ⟪bq k, alongCurve (leviCivitaConnection I M) γ
        (fun s ↦ b.normalFrameExpansion (U := U) (γ s) (y s)) t⟫_ℝ = 0 := by
    have hh := h.inner_alongCurve_normalFrameExpansion b v hy ht k
    simpa only [neg_add_cancel, inner_zero_right, bq, OrthonormalBasis.coe_mk] using hh
  rw [← bq.sum_repr' (alongCurve (leviCivitaConnection I M) γ
    (fun s ↦ b.normalFrameExpansion (U := U) (γ s) (y s)) t)]
  simp only [hzero, zero_smul, Finset.sum_const_zero]

/-- On the radial segment, the propagator solves the normal-frame connection equation. -/
theorem hasDerivAt_radialParallelCoefficients_apply (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U)
    (a : TangentSpace I p) {t : ℝ} (ht : t ∈ Icc l r) :
    HasDerivAt (fun s ↦ radialParallelCoefficients (U := U) h b v hlr hseg s a)
      (-b.normalFrameConnectionOperator (U := U) v (riemannianExp I M p (t • v))
        (radialParallelCoefficients (U := U) h b v hlr hseg t a)) t := by
  have hd := TauCeti.hasDerivAt_dysonSeriesLeft_apply
    (h.contDiff_radialConnectionExtension b v hlr hseg).continuous a t
  have heq := (h.radialConnectionExtension_eventuallyEq b v hlr hseg t ht).eq_of_nhds
  simpa only [heq, radialParallelCoefficients, neg_apply] using hd

/-- The reconstructed Dyson field is parallel on the prescribed radial segment. -/
theorem alongCurve_radialParallel_eq_zero (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U)
    (a : TangentSpace I p) {t : ℝ} (ht : t ∈ Icc l r) :
    alongCurve (leviCivitaConnection I M)
      (fun s : ℝ ↦ riemannianExp I M p (s • v))
      (fun s ↦ b.normalFrameExpansion (U := U) (riemannianExp I M p (s • v))
        (radialParallelCoefficients (U := U) h b v hlr hseg s a)) t = 0 := by
  exact h.alongCurve_normalFrameExpansion_eq_zero b v
    (h.hasDerivAt_radialParallelCoefficients_apply b v hlr hseg a ht) (hseg t ht)

/-- Radial parallel transport preserves the inner product on a segment containing the initial
point. -/
theorem inner_radialParallel (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l < r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U) (h0 : 0 ∈ Icc l r)
    (a a' : TangentSpace I p) {t : ℝ} (ht : t ∈ Icc l r) :
    ⟪b.normalFrameExpansion (U := U) (riemannianExp I M p (t • v))
        (radialParallelCoefficients (U := U) h b v hlr.le hseg t a),
      b.normalFrameExpansion (U := U) (riemannianExp I M p (t • v))
        (radialParallelCoefficients (U := U) h b v hlr.le hseg t a')⟫_ℝ = ⟪a, a'⟫_ℝ := by
  let γ := fun s : ℝ ↦ riemannianExp I M p (s • v)
  let P := fun (z : TangentSpace I p) s ↦ b.normalFrameExpansion (U := U) (γ s)
    (radialParallelCoefficients (U := U) h b v hlr.le hseg s z)
  have hγ (s : ℝ) (hs : s ∈ Icc l r) : MDiffAt γ s := by
    have hlin : ContDiff ℝ ∞ (fun s : ℝ ↦ s • v) := contDiff_id.smul contDiff_const
    exact ((contMDiffAt_riemannianExp (h.subset_expDomain (hseg s hs))).comp s
      hlin.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have hcoord (z : TangentSpace I p) (s : ℝ) (hs : s ∈ Icc l r) :
      DifferentiableAt ℝ (sectionCoord (F := E) γ (P z) (γ s)) s :=
    h.differentiableAt_sectionCoord_normalFrameExpansion b v
      (h.hasDerivAt_radialParallelCoefficients_apply b v hlr.le hseg z hs).differentiableAt
      (hseg s hs)
  have hparallel (z : TangentSpace I p) (s : ℝ) (hs : s ∈ Icc l r) :
      alongCurve (leviCivitaConnection I M) γ (P z) s = 0 :=
    h.alongCurve_radialParallel_eq_zero b v hlr.le hseg z hs
  have hrestrict (z : TangentSpace I p) (s : ℝ) (hs : s ∈ Icc l r) :
      alongCurveWithin (leviCivitaConnection I M) γ (P z) (Icc l r) s = 0 := by
    rw [alongCurveWithin_subset _ γ (P z) (subset_univ _) (uniqueDiffOn_Icc hlr s hs)
      (hcoord z s hs).differentiableWithinAt
      ((mdifferentiableAt_extChartAt (I := I) (mem_chart_source H (γ s))).comp s
        (hγ s hs)).differentiableAt.differentiableWithinAt,
      alongCurveWithin_univ, hparallel z s hs]
  have hconst : ⟪P a t, P a' t⟫_ℝ = ⟪P a 0, P a' 0⟫_ℝ :=
    (isMetricCompatible_leviCivitaConnection I).inner_eq_of_alongCurveWithin_eq_zero
      isPreconnected_Icc (fun s hs ↦ (hγ s hs).mdifferentiableWithinAt)
      (fun s hs ↦ (hcoord a s hs).differentiableWithinAt)
      (fun s hs ↦ (hcoord a' s hs).differentiableWithinAt) (hrestrict a) (hrestrict a') ht h0
  rw [hconst]
  dsimp only [P]
  rw [radialParallelCoefficients_zero, one_apply_eq_self, one_apply_eq_self]
  exact h.inner_normalFrameExpansion_pair b (mem_image_of_mem _ (hseg 0 h0)) a a'

/-- The transported vector has the prescribed initial value, with its canonical tangent-space
type. -/
@[simp]
theorem radialParallelLinearMap_apply_zero (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U) (a : TangentSpace I p) :
    radialParallelLinearMap (U := U) h b v hlr hseg 0 a = a := by
  simp only [radialParallelLinearMap_apply, radialParallelCoefficients_zero, one_apply_eq_self]
  have hinit (q : M) (hq : q = p) : b.normalFrameExpansion (U := U) q a = a := by
    subst q
    exact h.normalFrameExpansion_self b a
  apply hinit
  rw [zero_smul, riemannianExp_zero]

/-- Radial parallel transport as a linear isometry equivalence of the tangent spaces. -/
def radialParallelIsometry (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l < r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U) (h0 : 0 ∈ Icc l r)
    {t : ℝ} (ht : t ∈ Icc l r) :
    TangentSpace I p ≃ₗᵢ[ℝ] TangentSpace I (riemannianExp I M p (t • v)) := by
  let P : TangentSpace I p →ₗᵢ[ℝ] TangentSpace I (riemannianExp I M p (t • v)) :=
    { toLinearMap := radialParallelLinearMap (U := U) h b v hlr.le hseg t
      norm_map' := fun a ↦ by
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        simpa only [radialParallelLinearMap_apply, real_inner_self_eq_norm_sq] using
          h.inner_radialParallel b v hlr hseg h0 a a ht }
  exact LinearIsometryEquiv.ofSurjective P
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := P.toLinearMap)
      ((TauCeti.finrank_tangentSpace (I := I) p).trans
        (TauCeti.finrank_tangentSpace (I := I) (riemannianExp I M p (t • v))).symm)).mp P.injective)

/-- The isometry equivalence acts by the constructed parallel transport map. -/
theorem radialParallelIsometry_apply (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l < r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U) (h0 : 0 ∈ Icc l r)
    {t : ℝ} (ht : t ∈ Icc l r) (a : TangentSpace I p) :
    h.radialParallelIsometry b v hlr hseg h0 ht a =
      radialParallelLinearMap (U := U) h b v hlr.le hseg t a := by rfl

/-- The reconstructed radial parallel field is smooth as a map into the tangent bundle. -/
theorem contMDiffAt_radialParallelLinearMap_apply (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l ≤ r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U)
    (a : TangentSpace I p) {t : ℝ} (ht : t • v ∈ U) :
    ContMDiffAt 𝓘(ℝ) (I.prod 𝓘(ℝ, E)) ∞
      (fun s : ℝ ↦ TotalSpace.mk' E (riemannianExp I M p (s • v))
        (h.radialParallelLinearMap b v hlr hseg s a)) t := by
  let γ := fun s : ℝ ↦ riemannianExp I M p (s • v)
  have hlin : ContDiff ℝ ∞ (fun s : ℝ ↦ s • v) := contDiff_id.smul contDiff_const
  have hγ : ContMDiffAt 𝓘(ℝ) I ∞ γ t :=
    (contMDiffAt_riemannianExp (h.subset_expDomain ht)).comp t hlin.contMDiff.contMDiffAt
  have hq : γ t ∈ riemannianExp I M p '' U := mem_image_of_mem _ ht
  have hc (i : ι) : ContDiff ℝ ∞ (fun s : ℝ ↦
      ⟪b i, h.radialParallelCoefficients b v hlr hseg s a⟫_ℝ) :=
    contDiff_const.inner ℝ ((h.contDiff_radialParallelCoefficients b v hlr hseg).clm_apply
      contDiff_const)
  simp only [radialParallelLinearMap_apply, OrthonormalBasis.normalFrameExpansion_apply]
  apply ContMDiffAt.sum_sectionAlong Finset.univ _ hγ
  intro i _
  exact (hc i).contMDiff.contMDiffAt.smul_totalSpace
    (((h.contMDiffOn_normalOrthonormalFrame b i).contMDiffAt
      (h.isOpen_image.mem_nhds hq)).comp t hγ)

/-- Radial parallel transport carries the initial radial vector to the geodesic velocity. -/
theorem radialParallelLinearMap_radial (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l < r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U) (h0 : 0 ∈ Icc l r)
    {t : ℝ} (ht : t ∈ Icc l r) :
    h.radialParallelLinearMap b v hlr.le hseg t v =
      curveVelocity I (fun s : ℝ ↦ riemannianExp I M p (s • v)) t := by
  let γ := fun s : ℝ ↦ riemannianExp I M p (s • v)
  let P := fun s : ℝ ↦ h.radialParallelLinearMap b v hlr.le hseg s v
  have hgeoeq : γ = maximalGeodesic I M p v := funext (riemannianExp_smul p v)
  have hgeo := (isGeodesicCurveOnFrom_maximalGeodesic (I := I) p v).isGeodesicCurveOn
  rw [← hgeoeq] at hgeo
  have hmem (s : ℝ) (hs : s ∈ Icc l r) : s ∈ geodesicInterval I M p v :=
    mem_geodesicInterval_iff_smul_mem_expDomain.mpr (h.subset_expDomain (hseg s hs))
  have hγ (s : ℝ) (hs : s ∈ Icc l r) : MDiffAt γ s :=
    (hgeo.contMDiffOn.contMDiffAt
      (isOpen_geodesicInterval.mem_nhds (hmem s hs))).mdifferentiableAt (by norm_num)
  have hPcoord (s : ℝ) (hs : s ∈ Icc l r) :
      DifferentiableAt ℝ (sectionCoord (F := E) γ P (γ s)) s :=
    differentiableAt_sectionCoord γ P
      ((h.contMDiffAt_radialParallelLinearMap_apply b v hlr.le hseg v
        (hseg s hs)).mdifferentiableAt (by simp))
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ s))
  have hVcoord (s : ℝ) (hs : s ∈ Icc l r) :
      DifferentiableAt ℝ (sectionCoord (F := E) γ (curveVelocity I γ) (γ s)) s :=
    differentiableAt_sectionCoord_curveVelocity (γ := γ) hgeo.contMDiffOn
      isOpen_geodesicInterval (hmem s hs)
  have hP (s : ℝ) (hs : s ∈ Icc l r) : alongCurve (leviCivitaConnection I M) γ P s = 0 := by
    have hexp : P = fun u ↦ b.normalFrameExpansion (U := U) (γ u)
        (h.radialParallelCoefficients b v hlr.le hseg u v) :=
      funext fun u ↦ h.radialParallelLinearMap_apply b v hlr.le hseg u v
    rw [hexp]
    exact h.alongCurve_radialParallel_eq_zero b v hlr.le hseg v hs
  have hV (s : ℝ) (hs : s ∈ Icc l r) :
      alongCurve (leviCivitaConnection I M) γ (curveVelocity I γ) s = 0 := by
    simpa only [acceleration_def] using
      ((isGeodesicCurveOn_iff_of_isOpen isOpen_geodesicInterval).mp hgeo).2 s (hmem s hs)
  apply (isMetricCompatible_leviCivitaConnection I).eq_of_alongCurve_eq_zero
    isPreconnected_Icc hγ hPcoord hVcoord hP hV h0 ht
  dsimp only [P, γ]
  rw [h.radialParallelLinearMap_apply_zero b v hlr.le hseg v]
  exact (curveVelocity_riemannianExp_smul_zero p v).symm

/-- Parallel transport preserves the component in the radial velocity direction. -/
theorem inner_radialParallelLinearMap_curveVelocity (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v a : TangentSpace I p)
    {l r : ℝ} (hlr : l < r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U) (h0 : 0 ∈ Icc l r)
    {t : ℝ} (ht : t ∈ Icc l r) :
    ⟪h.radialParallelLinearMap b v hlr.le hseg t a,
      curveVelocity I (fun s : ℝ ↦ riemannianExp I M p (s • v)) t⟫_ℝ = ⟪a, v⟫_ℝ := by
  rw [← h.radialParallelLinearMap_radial b v hlr hseg h0 ht]
  simpa only [radialParallelLinearMap_apply] using
    h.inner_radialParallel b v hlr hseg h0 a v ht

/-- Radial parallel transport restricts to an isometry between the transverse tangent spaces. -/
def radialTransverseIsometry (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p) {r t : ℝ}
    (hr : 0 < r) (hseg : ∀ u ∈ Icc 0 r, u • v ∈ U)
    (htseg : t ∈ Icc 0 r) :
    (ℝ ∙ v)ᗮ ≃ₗᵢ[ℝ] (ℝ ∙ curveVelocity I (fun u : ℝ ↦ riemannianExp I M p (u • v)) t)ᗮ := by
  let e := h.radialParallelIsometry b v hr hseg ⟨le_rfl, hr.le⟩ htseg
  have hev : e v = curveVelocity I (fun u : ℝ ↦ riemannianExp I M p (u • v)) t := by
    calc
      e v = h.radialParallelLinearMap b v hr.le hseg t v :=
        h.radialParallelIsometry_apply b v hr hseg ⟨le_rfl, hr.le⟩ htseg v
      _ = curveVelocity I (fun u : ℝ ↦ riemannianExp I M p (u • v)) t :=
        h.radialParallelLinearMap_radial b v hr hseg ⟨le_rfl, hr.le⟩ htseg
  have hmap : (ℝ ∙ v)ᗮ.map (e.toLinearEquiv : TangentSpace I p →ₗ[ℝ]
      TangentSpace I (riemannianExp I M p (t • v))) =
      (ℝ ∙ curveVelocity I (fun u : ℝ ↦ riemannianExp I M p (u • v)) t)ᗮ := by
    rw [Submodule.map_orthogonal_equiv, Submodule.map_span]
    simp only [Set.image_singleton, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      hev]
  exact (LinearIsometryEquiv.submoduleMap (ℝ ∙ v)ᗮ e).trans
    (LinearIsometryEquiv.ofEq _ _ hmap)

/-- The transverse isometry acts by the ambient radial parallel transport. -/
theorem radialTransverseIsometry_apply (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {r t : ℝ} (hr : 0 < r)
    (hseg : ∀ u ∈ Icc 0 r, u • v ∈ U) (htseg : t ∈ Icc 0 r)
    (a : (ℝ ∙ v)ᗮ) :
    (h.radialTransverseIsometry b v hr hseg htseg a :
      TangentSpace I (riemannianExp I M p (t • v))) =
        h.radialParallelLinearMap b v hr.le hseg t a := by
  simp only [radialTransverseIsometry, LinearIsometryEquiv.trans_apply]
  exact h.radialParallelIsometry_apply b v hr hseg ⟨le_rfl, hr.le⟩ htseg a

/-- Radial parallel transport does not depend on the prescribed segment: for two segments
containing `0`, the reconstructed transports agree at every common parameter. -/
theorem radialParallelLinearMap_eq_of_mem (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r l' r' : ℝ} (hlr : l ≤ r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U) (h0 : 0 ∈ Icc l r)
    (hlr' : l' ≤ r') (hseg' : ∀ t ∈ Icc l' r', t • v ∈ U) (h0' : 0 ∈ Icc l' r')
    {t : ℝ} (ht : t ∈ Icc l r) (ht' : t ∈ Icc l' r') (a : TangentSpace I p) :
    h.radialParallelLinearMap b v hlr hseg t a = h.radialParallelLinearMap b v hlr' hseg' t a := by
  let γ := fun s : ℝ ↦ riemannianExp I M p (s • v)
  let P := fun s : ℝ ↦ h.radialParallelLinearMap b v hlr hseg s a
  let Q := fun s : ℝ ↦ h.radialParallelLinearMap b v hlr' hseg' s a
  have hlin : ContDiff ℝ ∞ (fun s : ℝ ↦ s • v) := contDiff_id.smul contDiff_const
  have hγ (s : ℝ) (hs : s ∈ Icc l r ∩ Icc l' r') : MDiffAt γ s :=
    ((contMDiffAt_riemannianExp (h.subset_expDomain (hseg s hs.1))).comp s
      hlin.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have hPcoord (s : ℝ) (hs : s ∈ Icc l r ∩ Icc l' r') :
      DifferentiableAt ℝ (sectionCoord (F := E) γ P (γ s)) s :=
    differentiableAt_sectionCoord γ P
      ((h.contMDiffAt_radialParallelLinearMap_apply b v hlr hseg a
        (hseg s hs.1)).mdifferentiableAt (by simp))
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ s))
  have hQcoord (s : ℝ) (hs : s ∈ Icc l r ∩ Icc l' r') :
      DifferentiableAt ℝ (sectionCoord (F := E) γ Q (γ s)) s :=
    differentiableAt_sectionCoord γ Q
      ((h.contMDiffAt_radialParallelLinearMap_apply b v hlr' hseg' a
        (hseg s hs.1)).mdifferentiableAt (by simp))
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ s))
  have hP (s : ℝ) (hs : s ∈ Icc l r ∩ Icc l' r') :
      alongCurve (leviCivitaConnection I M) γ P s = 0 := by
    have hexp : P = fun u ↦ b.normalFrameExpansion (U := U) (γ u)
        (h.radialParallelCoefficients b v hlr hseg u a) :=
      funext fun u ↦ h.radialParallelLinearMap_apply b v hlr hseg u a
    rw [hexp]
    exact h.alongCurve_radialParallel_eq_zero b v hlr hseg a hs.1
  have hQ (s : ℝ) (hs : s ∈ Icc l r ∩ Icc l' r') :
      alongCurve (leviCivitaConnection I M) γ Q s = 0 := by
    have hexp : Q = fun u ↦ b.normalFrameExpansion (U := U) (γ u)
        (h.radialParallelCoefficients b v hlr' hseg' u a) :=
      funext fun u ↦ h.radialParallelLinearMap_apply b v hlr' hseg' u a
    rw [hexp]
    exact h.alongCurve_radialParallel_eq_zero b v hlr' hseg' a hs.2
  have hconn : IsPreconnected (Icc l r ∩ Icc l' r') := by
    rw [Icc_inter_Icc]
    exact isPreconnected_Icc
  apply (isMetricCompatible_leviCivitaConnection I).eq_of_alongCurve_eq_zero
    hconn hγ hPcoord hQcoord hP hQ ⟨h0, h0'⟩ ⟨ht, ht'⟩
  dsimp only [P, Q]
  rw [h.radialParallelLinearMap_apply_zero b v hlr hseg a,
    h.radialParallelLinearMap_apply_zero b v hlr' hseg' a]

/-- The coefficient propagators for two segments containing `0` agree at every common
parameter. -/
theorem radialParallelCoefficients_eq_of_mem (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r l' r' : ℝ} (hlr : l ≤ r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U) (h0 : 0 ∈ Icc l r)
    (hlr' : l' ≤ r') (hseg' : ∀ t ∈ Icc l' r', t • v ∈ U) (h0' : 0 ∈ Icc l' r')
    {t : ℝ} (ht : t ∈ Icc l r) (ht' : t ∈ Icc l' r') :
    h.radialParallelCoefficients b v hlr hseg t =
      h.radialParallelCoefficients b v hlr' hseg' t := by
  have hq : riemannianExp I M p (t • v) ∈ riemannianExp I M p '' U :=
    mem_image_of_mem _ (hseg t ht)
  ext a
  refine b.toBasis.ext_elem fun k ↦ ?_
  have hk := congrArg (fun x ↦ ⟪normalOrthonormalFrame I M p U b k _, x⟫_ℝ)
    (h.radialParallelLinearMap_eq_of_mem b v hlr hseg h0 hlr' hseg' h0' ht ht' a)
  simpa only [radialParallelLinearMap_apply, h.inner_normalFrameExpansion b hq,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply] using hk

/-- The radial parallel isometries for two segments containing `0` agree at every common
parameter. -/
theorem radialParallelIsometry_eq_of_mem (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r l' r' : ℝ} (hlr : l < r) (hseg : ∀ t ∈ Icc l r, t • v ∈ U) (h0 : 0 ∈ Icc l r)
    (hlr' : l' < r') (hseg' : ∀ t ∈ Icc l' r', t • v ∈ U) (h0' : 0 ∈ Icc l' r')
    {t : ℝ} (ht : t ∈ Icc l r) (ht' : t ∈ Icc l' r') :
    h.radialParallelIsometry b v hlr hseg h0 ht = h.radialParallelIsometry b v hlr' hseg' h0' ht' :=
  LinearIsometryEquiv.ext fun a ↦ by
    rw [radialParallelIsometry_apply, radialParallelIsometry_apply]
    exact h.radialParallelLinearMap_eq_of_mem b v hlr.le hseg h0 hlr'.le hseg' h0' ht ht' a

/-- The transverse isometries for two radial segments `Icc 0 r` and `Icc 0 r'` agree at every
common parameter. -/
theorem radialTransverseIsometry_eq_of_mem (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p) {r r' t : ℝ}
    (hr : 0 < r) (hseg : ∀ u ∈ Icc 0 r, u • v ∈ U) (htseg : t ∈ Icc 0 r)
    (hr' : 0 < r') (hseg' : ∀ u ∈ Icc 0 r', u • v ∈ U) (htseg' : t ∈ Icc 0 r') :
    h.radialTransverseIsometry b v hr hseg htseg =
      h.radialTransverseIsometry b v hr' hseg' htseg' :=
  LinearIsometryEquiv.ext fun a ↦ Subtype.ext <| by
    rw [radialTransverseIsometry_apply, radialTransverseIsometry_apply]
    exact h.radialParallelLinearMap_eq_of_mem b v hr.le hseg ⟨le_rfl, hr.le⟩ hr'.le hseg'
      ⟨le_rfl, hr'.le⟩ htseg htseg' a

end IsNormalDomain
end TauCeti.Manifold
