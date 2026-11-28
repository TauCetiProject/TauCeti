/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Parallel
import TauCeti.Analysis.ODE.DysonSeries.ContDiff
import Mathlib.Analysis.Convex.PathConnected
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity

/-!
# Smooth radial parallel transport

Parallel transport from the centre of a normal domain depends smoothly on the radial endpoint.
A common smooth connection coefficient extension is defined near each compact radial segment.
Its left Dyson solution agrees with the existing transport coefficients on every nearby unit
segment, by uniqueness of the radial equation.

The endpoint section is reconstructed in the normal orthonormal frame. Its coefficients come
from parallel transport; the normal orthonormal frame itself need not be parallel away from the
centre.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 4.
* Formalization references: https://github.com/frenzymath/lean-eval-submissions and
  https://github.com/frenzymath/PoincareConjecture.
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
  [I.Boundaryless] [T2Space M]

namespace IsNormalDomain

/-- Nearby rays admit one jointly smooth coefficient extension which agrees with the
geometric connection equation on their whole unit segment. -/
private theorem exists_contDiff_radialConnectionExtension_joint (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {v : TangentSpace I p} (hv : v ∈ U) :
    ∃ (A : TangentSpace I p × ℝ → TangentSpace I p →L[ℝ] TangentSpace I p)
      (N : Set (TangentSpace I p)),
      ContDiff ℝ ∞ A ∧ IsOpen N ∧ v ∈ N ∧ N ⊆ U ∧
      ∀ x ∈ N, ∀ t ∈ Icc (0 : ℝ) 1,
        A (x, t) = -b.normalFrameConnectionOperator (U := U) x
          (riemannianExp I M p (t • x)) := by
  let Ω : Set (TangentSpace I p × ℝ) := {q | q.2 • q.1 ∈ U}
  let K : Set (TangentSpace I p × ℝ) := {v} ×ˢ Icc (0 : ℝ) 1
  have hΩ : IsOpen Ω := h.isOpen.preimage (continuous_snd.smul continuous_fst)
  have hK : IsCompact K := isCompact_singleton.prod isCompact_Icc
  have hKΩ : K ⊆ Ω := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    rcases mem_singleton_iff.mp hx with rfl
    exact h.smul_mem_Icc hv t ht
  obtain ⟨A, hA, -, -, -, hEq⟩ :=
    (h.contDiffOn_normalFrameConnectionOperator_radial_joint b).neg
      |>.exists_contDiff_eventuallyEq_on_isCompact hK hΩ hKΩ
  have hevent : ∀ᶠ x in 𝓝 v, ∀ t ∈ Icc (0 : ℝ) 1,
      A (x, t) = -b.normalFrameConnectionOperator (U := U) x
        (riemannianExp I M p (t • x)) :=
    isCompact_Icc.eventually_forall_of_forall_eventually fun t ht ↦ hEq (v, t) ⟨rfl, ht⟩
  obtain ⟨N, hNsub, hNopen, hvN⟩ := mem_nhds_iff.mp (inter_mem hevent (h.isOpen.mem_nhds hv))
  exact ⟨A, N, hA, hNopen, hvN, fun x hx ↦ (hNsub hx).2,
    fun x hx ↦ (hNsub hx).1⟩

/-- Near any ray in a normal domain the existing unit-segment transport coefficients admit a
jointly smooth representative. Agreement is asserted on the prescribed unit segments only. -/
theorem exists_contDiff_radialParallelCoefficients_joint (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {v : TangentSpace I p} (hv : v ∈ U) :
    ∃ (F : TangentSpace I p × ℝ → TangentSpace I p →L[ℝ] TangentSpace I p)
      (N : Set (TangentSpace I p)),
      ContDiff ℝ ∞ F ∧ IsOpen N ∧ v ∈ N ∧ ∃ hNU : N ⊆ U,
      ∀ x (hx : x ∈ N), ∀ t ∈ Icc (0 : ℝ) 1,
          F (x, t) = h.radialParallelCoefficients b x zero_le_one
            (h.smul_mem_Icc (hNU hx)) t := by
  obtain ⟨A, N, hA, hN, hvN, hNU, hEq⟩ :=
    h.exists_contDiff_radialConnectionExtension_joint b hv
  refine ⟨fun q ↦ TauCeti.dysonSeriesLeft (fun t ↦ A (q.1, t)) q.2, N,
    TauCeti.contDiff_parametric_dysonSeriesLeft (p := fun x t ↦ A (x, t))
      (n := ⊤) hA, hN, hvN, hNU, ?_⟩
  intro x hx t ht
  let hseg := h.smul_mem_Icc (hNU hx)
  apply (h.radialParallelCoefficients_eq_of_hasDerivWithinAt b x hseg
    (left_mem_Icc.2 zero_le_one) (TauCeti.dysonSeriesLeft_zero _) ?_ ht).symm
  intro a s hs
  have hAc : Continuous (fun r : ℝ ↦ A (x, r)) :=
    hA.continuous.comp (continuous_const.prodMk continuous_id)
  simpa only [hEq x hx s hs, neg_apply] using
    (TauCeti.hasDerivAt_dysonSeriesLeft_apply hAc a s).hasDerivWithinAt

/-- Coefficients of parallel transport from the centre to the radial endpoint. They are set to
zero outside the normal domain. -/
def radialParallelEndpointCoefficients (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (x : TangentSpace I p) :
    TangentSpace I p →L[ℝ] TangentSpace I p := by
  classical
  exact if hx : x ∈ U then
    h.radialParallelCoefficients b x zero_le_one
      (h.smul_mem_Icc hx) 1
  else 0

/-- At a point of the normal domain the endpoint coefficients are the existing unit-segment
radial transport coefficients. -/
@[simp]
theorem radialParallelEndpointCoefficients_of_mem (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {x : TangentSpace I p} (hx : x ∈ U) :
    h.radialParallelEndpointCoefficients b x =
      h.radialParallelCoefficients b x zero_le_one
        (h.smul_mem_Icc hx) 1 := by
  simp [radialParallelEndpointCoefficients, hx]

/-- Outside the normal domain the totalized endpoint coefficients vanish. -/
@[simp]
theorem radialParallelEndpointCoefficients_of_notMem (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {x : TangentSpace I p} (hx : x ∉ U) :
    h.radialParallelEndpointCoefficients b x = 0 := by
  simp [radialParallelEndpointCoefficients, hx]

/-- The actual radial endpoint transport coefficients are smooth on the normal domain. -/
theorem contDiffOn_radialParallelEndpointCoefficients (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) :
    ContDiffOn ℝ ∞ (h.radialParallelEndpointCoefficients b) U := by
  intro x hx
  obtain ⟨F, N, hF, hN, hxN, hNU, hEq⟩ :=
    h.exists_contDiff_radialParallelCoefficients_joint b hx
  have hend : ContDiff ℝ ∞ (fun y : TangentSpace I p ↦ F (y, 1)) :=
    hF.comp (contDiff_id.prodMk contDiff_const)
  apply (hend.contDiffAt.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hN.mem_nhds hxN] with y hy
  rw [h.radialParallelEndpointCoefficients_of_mem b (hNU hy)]
  exact (hEq y hy 1 (right_mem_Icc.2 zero_le_one)).symm

/-- Parallel transport from the centre of a normal domain to a radial endpoint. The zero
extension outside the domain is auxiliary. -/
def radialParallelEndpoint (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (x : TangentSpace I p) :
    TangentSpace I p →ₗ[ℝ] TangentSpace I (riemannianExp I M p x) where
  toFun a := b.normalFrameExpansion (U := U) (riemannianExp I M p x)
    (h.radialParallelEndpointCoefficients b x a)
  map_add' a a' := by simp
  map_smul' c a := by simp

/-- The radial endpoint map is reconstructed from its transport coefficients. -/
theorem radialParallelEndpoint_apply (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (x a : TangentSpace I p) :
    h.radialParallelEndpoint b x a =
      b.normalFrameExpansion (U := U) (riemannianExp I M p x)
        (h.radialParallelEndpointCoefficients b x a) := by rfl

/-- Transporting a fixed initial tangent vector gives a smooth section along the exponential
map on the normal domain. -/
theorem contMDiffOn_radialParallelEndpoint_apply (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (a : TangentSpace I p) :
    ContMDiffOn 𝓘(ℝ, TangentSpace I p) (I.prod 𝓘(ℝ, E)) ∞
      (fun x ↦ TotalSpace.mk' E (riemannianExp I M p x)
        (h.radialParallelEndpoint b x a)) U := by
  intro x hx
  have hexp : ContMDiffAt 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p) x :=
    contMDiffAt_riemannianExp (h.subset_expDomain hx)
  have hcoeff := (h.contDiffOn_radialParallelEndpointCoefficients b).contDiffAt
    (h.isOpen.mem_nhds hx)
  have hc (i : ι) : ContDiffAt ℝ ∞
      (fun y ↦ ⟪b i, h.radialParallelEndpointCoefficients b y a⟫_ℝ) x :=
    contDiffAt_const.inner ℝ (hcoeff.clm_apply contDiffAt_const)
  apply ContMDiffAt.contMDiffWithinAt
  simp only [radialParallelEndpoint_apply, OrthonormalBasis.normalFrameExpansion_apply]
  apply ContMDiffAt.sum_sectionAlong Finset.univ _ hexp
  intro i _
  exact (hc i).contMDiffAt.smul_totalSpace
    (((h.contMDiffOn_normalOrthonormalFrame b i).contMDiffAt
      (h.isOpen_image.mem_nhds (mem_image_of_mem _ hx))).comp x hexp)

/-- Endpoint coefficients at a point of any prescribed radial segment agree with its
transport coefficients, including signed times and the segment endpoints. -/
theorem radialParallelEndpointCoefficients_smul (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (x : TangentSpace I p)
    {l r : ℝ} (hseg : ∀ s ∈ Icc l r, s • x ∈ U) (h0 : 0 ∈ Icc l r)
    {t : ℝ} (ht : t ∈ Icc l r) :
    h.radialParallelEndpointCoefficients b (t • x) =
      h.radialParallelCoefficients b x (h0.1.trans h0.2) hseg t := by
  have htx : t • x ∈ U := hseg t ht
  let segt := h.smul_mem_Icc htx
  rw [h.radialParallelEndpointCoefficients_of_mem b htx]
  let F : ℝ → TangentSpace I p →L[ℝ] TangentSpace I p := fun s ↦
    h.radialParallelCoefficients b x (h0.1.trans h0.2) hseg (t * s)
  have hF : ∀ a, ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun u ↦ F u a)
      (-b.normalFrameConnectionOperator (U := U) (t • x)
        (riemannianExp I M p (s • (t • x))) (F s a)) (Icc 0 1) s := by
    intro a s hs
    have hts : t * s ∈ Icc l r := by
      rw [mul_comm]
      exact (convex_Icc l r).smul_mem_of_zero_mem h0 ht hs
    have hd := (h.hasDerivAt_radialParallelCoefficients_apply b x (h0.1.trans h0.2)
      hseg a hts).scomp s ((hasDerivAt_id s).const_mul t)
    have hscale : s • (t • x) = (t * s) • x := by
      rw [smul_smul, mul_comm]
    have hscaled : HasDerivAt (fun u ↦ F u a)
        (-b.normalFrameConnectionOperator (U := U) (t • x)
          (riemannianExp I M p (s • (t • x))) (F s a)) s := by
      rw [hscale]
      simpa only [F, OrthonormalBasis.normalFrameConnectionOperator_smul,
        neg_apply, smul_apply, mul_one, smul_neg, Function.comp_def] using hd
    exact hscaled.hasDerivWithinAt
  simpa only [F, mul_one] using
    h.radialParallelCoefficients_eq_of_hasDerivWithinAt b (t • x) segt
      (left_mem_Icc.2 zero_le_one) (by simp [F]) hF (right_mem_Icc.2 zero_le_one)

/-- The endpoint coefficient operator is the identity at the centre. -/
@[simp]
theorem radialParallelEndpointCoefficients_zero (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) :
    h.radialParallelEndpointCoefficients b 0 = 1 := by
  simpa using h.radialParallelEndpointCoefficients_smul b 0
    (l := 0) (r := 1) (fun _ _ ↦ by simpa using h.zero_mem)
    (left_mem_Icc.2 zero_le_one) (t := 0) (left_mem_Icc.2 zero_le_one)

/-- At every point of a prescribed radial segment the endpoint section equals the original
native parallel transport at that parameter. -/
theorem radialParallelEndpoint_smul (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (x : TangentSpace I p)
    {l r : ℝ} (hseg : ∀ s ∈ Icc l r, s • x ∈ U) (h0 : 0 ∈ Icc l r)
    {t : ℝ} (ht : t ∈ Icc l r) (a : TangentSpace I p) :
    h.radialParallelEndpoint b (t • x) a =
      h.radialParallelLinearMap b x (h0.1.trans h0.2) hseg t a := by
  simp only [radialParallelEndpoint_apply, radialParallelLinearMap_apply,
    h.radialParallelEndpointCoefficients_smul b x hseg h0 ht]

/-- Radial endpoint transport is independent of the auxiliary orthonormal basis. -/
theorem radialParallelEndpoint_eq (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    {κ : Type*} [Fintype κ] [LinearOrder κ] [LocallyFiniteOrderBot κ]
    (b' : OrthonormalBasis κ ℝ (TangentSpace I p)) (x : TangentSpace I p) :
    h.radialParallelEndpoint b x = h.radialParallelEndpoint b' x := by
  by_cases hx : x ∈ U
  · ext a
    have heq := h.radialParallelLinearMap_eq_of_mem b b' x zero_le_one
      (h.smul_mem_Icc hx) (left_mem_Icc.2 zero_le_one)
      zero_le_one (h.smul_mem_Icc hx)
      (left_mem_Icc.2 zero_le_one)
      (right_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) a
    have hb := h.radialParallelEndpoint_smul b x
      (h.smul_mem_Icc hx) (left_mem_Icc.2 zero_le_one)
      (right_mem_Icc.2 zero_le_one) a
    have hb' := h.radialParallelEndpoint_smul b' x
      (h.smul_mem_Icc hx) (left_mem_Icc.2 zero_le_one)
      (right_mem_Icc.2 zero_le_one) a
    rw [one_smul] at hb hb'
    exact hb.trans (heq.trans hb'.symm)
  · ext a
    simp [radialParallelEndpoint_apply, hx]

omit [I.Boundaryless] [T2Space M] in
/-- A ray through a normal domain admits a prescribed segment containing the centre and a
neighbourhood of any parameter whose radial endpoint belongs to the domain. -/
private theorem exists_radial_segment_mem_nhds (h : IsNormalDomain I M p U)
    (x : TangentSpace I p) {t : ℝ} (ht : t • x ∈ U) :
    ∃ l r, 0 ∈ Icc l r ∧ Icc l r ∈ 𝓝 t ∧ ∀ s ∈ Icc l r, s • x ∈ U := by
  let V : Set ℝ := {s | s • x ∈ U}
  have hV : IsOpen V := h.isOpen.preimage (continuous_id.smul continuous_const)
  have hzero : (0 : ℝ) ∈ V := by simpa only [V, mem_ofPred_eq, zero_smul] using h.zero_mem
  have hstar : StarConvex ℝ (0 : ℝ) V := by
    rw [starConvex_zero_iff]
    intro s hs c hc0 hc1
    simpa only [V, mem_ofPred_eq, smul_eq_mul, mul_smul] using h.smul_mem hs hc0 hc1
  have hconn := (hstar.isPathConnected hzero).isConnected.isPreconnected
  obtain ⟨a, b, htab, hN, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds (hV.mem_nhds ht)
  have hab : a ≤ b := htab.1.trans htab.2
  have ha : a ∈ V := hsub ⟨le_rfl, hab⟩
  have hb : b ∈ V := hsub ⟨hab, le_rfl⟩
  have hl : min 0 a ∈ V := by rcases min_choice (0 : ℝ) a with heq | heq <;> simp_all
  have hr : max 0 b ∈ V := by rcases max_choice (0 : ℝ) b with heq | heq <;> simp_all
  refine ⟨min 0 a, max 0 b, ⟨min_le_left _ _, le_max_left _ _⟩,
    mem_of_superset hN (Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)), ?_⟩
  exact fun s hs ↦ hconn.Icc_subset hl hr hs

/-- The smooth endpoint section is parallel at every parameter whose radial endpoint lies in
the normal domain, including the centre, signed times and unit-segment endpoints. -/
theorem alongCurve_radialParallelEndpoint_eq_zero (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {x : TangentSpace I p}
    {t : ℝ} (ht : t • x ∈ U) (a : TangentSpace I p) :
    (leviCivitaConnection I M).alongCurve
      (fun s : ℝ ↦ riemannianExp I M p (s • x))
      (fun s ↦ h.radialParallelEndpoint b (s • x) a) t = 0 := by
  obtain ⟨l, r, h0, hN, hseg⟩ := h.exists_radial_segment_mem_nhds x ht
  have heq : ∀ᶠ s in 𝓝 t, h.radialParallelEndpoint b (s • x) a =
      b.normalFrameExpansion (U := U) (riemannianExp I M p (s • x))
        (h.radialParallelCoefficients b x (h0.1.trans h0.2) hseg s a) := by
    filter_upwards [hN] with s hs
    simpa only [radialParallelLinearMap_apply] using
      h.radialParallelEndpoint_smul b x hseg h0 hs a
  rw [(leviCivitaConnection I M).alongCurve_congr _ _ heq]
  exact h.alongCurve_radialParallel_eq_zero b x (h0.1.trans h0.2) hseg a (mem_of_mem_nhds hN)

/-- Parallel transport to a radial endpoint preserves the metric inner product. -/
@[simp]
theorem inner_radialParallelEndpoint (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {x : TangentSpace I p} (hx : x ∈ U)
    (a a' : TangentSpace I p) :
    ⟪h.radialParallelEndpoint b x a, h.radialParallelEndpoint b x a'⟫_ℝ = ⟪a, a'⟫_ℝ := by
  have heq := h.inner_radialParallel b x zero_lt_one
    (h.smul_mem_Icc hx) (left_mem_Icc.2 zero_le_one) a a'
    (t := (1 : ℝ)) (right_mem_Icc.2 zero_le_one)
  rw [one_smul] at heq
  simpa only [radialParallelEndpoint_apply, h.radialParallelEndpointCoefficients_of_mem b hx]
    using heq

/-- Parallel transport to a radial endpoint preserves tangent-vector norms. -/
@[simp]
theorem norm_radialParallelEndpoint (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {x : TangentSpace I p} (hx : x ∈ U)
    (a : TangentSpace I p) : ‖h.radialParallelEndpoint b x a‖ = ‖a‖ := by
  exact (LinearMap.norm_map_iff_inner_map_map (h.radialParallelEndpoint b x)).2
    (h.inner_radialParallelEndpoint b hx) a

/-- The endpoint section has the prescribed value at the centre. -/
@[simp]
theorem radialParallelEndpoint_zero (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (a : TangentSpace I p) :
    h.radialParallelEndpoint b 0 a = a := by
  have heq := h.radialParallelEndpoint_smul b 0 (l := 0) (r := 1)
    (fun _ _ ↦ by simpa using h.zero_mem) (left_mem_Icc.2 zero_le_one)
    (t := 0) (left_mem_Icc.2 zero_le_one) a
  rw [zero_smul] at heq
  exact heq.trans (h.radialParallelLinearMap_apply_zero b 0 zero_le_one _ a)

/-- The endpoint section along all scaled rays is jointly smooth wherever the scaled radial
endpoint lies in the normal domain. On each unit segment this is the actual native transport,
by `radialParallelEndpoint_smul`. -/
theorem contMDiffOn_radialParallelEndpoint_radial_joint (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (a : TangentSpace I p) :
    ContMDiffOn 𝓘(ℝ, TangentSpace I p × ℝ) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : TangentSpace I p × ℝ ↦ TotalSpace.mk' E
        (riemannianExp I M p (q.2 • q.1))
        (h.radialParallelEndpoint b (q.2 • q.1) a)) {q | q.2 • q.1 ∈ U} := by
  have hscale : ContDiff ℝ ∞ (fun q : TangentSpace I p × ℝ ↦ q.2 • q.1) :=
    contDiff_snd.smul contDiff_fst
  exact (h.contMDiffOn_radialParallelEndpoint_apply b a).comp
    hscale.contMDiff.contMDiffOn (fun _ hq ↦ hq)

end IsNormalDomain

end TauCeti.Manifold
