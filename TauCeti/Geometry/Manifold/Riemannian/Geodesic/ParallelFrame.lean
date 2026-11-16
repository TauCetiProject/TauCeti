/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Parallel
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Uniform
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Reparametrization
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Smoothness
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Trajectory
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric

/-!
# Parallel fields along geodesics

Along a geodesic `γ` defined on the whole line, every tangent vector at `γ a` is the initial
value of a smooth parallel field on `[a, b]`, and parallel transport of an orthonormal basis
gives a parallel orthonormal frame (parallel fields are unique and keep their inner products,
`CovariantDerivative.IsMetricCompatible.eq_of_alongCurve_eq_zero`), and the velocity of the
geodesic is the parallel field starting at `γ'(a)`.

The fields are built from Tau Ceti's radial parallel transport inside normal balls
(`TauCeti.Manifold.IsNormalDomain.radialParallelLinearMap`). The image of `[a, b]` is compact,
so the normal balls at its points have a common radius; restarting `γ` at a point `τ` writes it
as the radial geodesic `t ↦ exp_(γ τ) ((t - τ) • γ'(τ))`, and finitely many radial pieces of a
fixed length are glued along their overlaps by uniqueness.

## Main results

* `TauCeti.Manifold.IsGeodesicCurveOn.eq_riemannianExp_sub_smul`: a geodesic on the whole line is
  the radial geodesic from any of its points.
* `TauCeti.Manifold.IsNormalDomain.exists_parallel_sub_smul`: parallel fields along a translated
  radial geodesic of a normal ball.
* `TauCeti.Manifold.IsGeodesicCurve.exists_parallel`: existence of parallel fields.
* `TauCeti.Manifold.IsGeodesicCurve.exists_parallel_orthonormal`: a parallel orthonormal frame.
* `TauCeti.Manifold.IsGeodesicCurve.eq_curveVelocity_of_alongCurve_eq_zero`: the parallel field
  starting at the velocity is the velocity.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 4.
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology InnerProductSpace

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- A geodesic defined on the whole line is the radial geodesic from any of its points:
`γ t = exp_(γ τ) ((t - τ) • γ'(τ))`. -/
theorem IsGeodesicCurveOn.eq_riemannianExp_sub_smul {γ : ℝ → M}
    (hγ : IsGeodesicCurveOn I γ univ) (τ t : ℝ) :
    γ t = riemannianExp I M (γ τ) ((t - τ) • curveVelocity I γ τ) := by
  set R := |t - τ| + 1
  have hτ : τ ∈ Ioo (τ - R) (τ + R) := ⟨by linarith [abs_nonneg (t - τ)],
    by linarith [abs_nonneg (t - τ)]⟩
  have hfrom := (hγ.mono (uniqueDiffOn_Ioo (τ - R) (τ + R))
    (subset_univ _)).isGeodesicCurveOnFrom_comp_add_const hτ
  have heq := hfrom.eqOn_maximalGeodesic
  have hmem : t - τ ∈ Ioo (τ - R - τ) (τ + R - τ) := by
    constructor <;> [linarith [neg_abs_le (t - τ)]; linarith [le_abs_self (t - τ)]]
  have h := heq hmem
  simp only [Function.comp_apply, sub_add_cancel] at h
  rw [riemannianExp_smul, h]

omit [I.Boundaryless] [T2Space M] in
/-- Two fields along a differentiable curve which are smooth and parallel at every point of
`[l, r]` and agree at one point of `[l, r]` agree on `[l, r]`. -/
private theorem eq_of_parallel_Icc {γ : ℝ → M} (hγd : ∀ t, MDifferentiableAt 𝓘(ℝ) I γ t)
    {V W : ∀ t, TangentSpace I (γ t)} {l r : ℝ}
    (hV : ∀ t ∈ Icc l r, ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (V t)) t ∧
      alongCurve (leviCivitaConnection I M) γ V t = 0)
    (hW : ∀ t ∈ Icc l r, ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (W t)) t ∧
      alongCurve (leviCivitaConnection I M) γ W t = 0)
    {τ : ℝ} (hτ : τ ∈ Icc l r) (hVW : V τ = W τ) {t : ℝ} (ht : t ∈ Icc l r) : V t = W t :=
  (isMetricCompatible_leviCivitaConnection I).eq_of_alongCurve_eq_zero isPreconnected_Icc
    (fun u _ ↦ hγd u)
    (fun u hu ↦ differentiableAt_sectionCoord γ V ((hV u hu).1.mdifferentiableAt (by simp))
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ u)))
    (fun u hu ↦ differentiableAt_sectionCoord γ W ((hW u hu).1.mdifferentiableAt (by simp))
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ u)))
    (fun u hu ↦ (hV u hu).2) (fun u hu ↦ (hW u hu).2) hτ ht hVW

variable {p : M} {U : Set (TangentSpace I p)}

/-- Radial parallel transport along a translated radial geodesic `t ↦ exp_p ((t - τ) • v)`
gives a smooth parallel field with any prescribed value at `τ`. -/
theorem IsNormalDomain.exists_parallel_sub_smul (h : IsNormalDomain I M p U)
    (v : TangentSpace I p) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hseg : ∀ s ∈ Icc (-ρ) ρ, s • v ∈ U) (τ : ℝ) (z : TangentSpace I p) :
    ∃ P : ∀ t, TangentSpace I (riemannianExp I M p ((t - τ) • v)), P τ = z ∧
      ∀ t ∈ Icc (τ - ρ) (τ + ρ),
        ContMDiffAt 𝓘(ℝ) I.tangent ∞
          (fun t ↦ TotalSpace.mk' E (riemannianExp I M p ((t - τ) • v)) (P t)) t ∧
        alongCurve (leviCivitaConnection I M)
          (fun t ↦ riemannianExp I M p ((t - τ) • v)) P t = 0 := by
  have hlr : -ρ ≤ ρ := by linarith
  let b := stdOrthonormalBasis ℝ (TangentSpace I p)
  set c : ℝ → M := fun s ↦ riemannianExp I M p (s • v)
  let W : ∀ s, TangentSpace I (c s) := fun s ↦ h.radialParallelLinearMap b v hlr hseg s z
  have hW₀ (u : ℝ) (hu : u = 0) : W u = z := by
    subst hu
    exact radialParallelLinearMap_apply_zero h b v hlr hseg z
  refine ⟨fun t ↦ W (t - τ), hW₀ _ (sub_self τ), fun t ht ↦ ?_⟩
  have hs : t - τ ∈ Icc (-ρ) ρ := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hφ : ContDiff ℝ ∞ (fun t : ℝ ↦ t - τ) := contDiff_id.sub contDiff_const
  have hlift := h.contMDiffAt_radialParallelLinearMap_apply b v hlr hseg z (hseg _ hs)
  refine ⟨?_, ?_⟩
  · convert hlift.comp t hφ.contMDiff.contMDiffAt using 1
    rfl
  · have hc : MDifferentiableAt 𝓘(ℝ) I c (t - τ) := by
      have hlin : ContDiff ℝ ∞ (fun s : ℝ ↦ s • v) := contDiff_id.smul contDiff_const
      exact ((contMDiffAt_riemannianExp (h.subset_expDomain (hseg _ hs))).comp (t - τ)
        hlin.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
    have hcomp := alongCurve_comp (leviCivitaConnection I M) c W (fun t ↦ t - τ)
      (hφ.differentiable (by simp) t)
      ((mdifferentiableAt_extChartAt (I := I) (mem_chart_source H (c (t - τ)))).comp _
        hc).differentiableAt
      (differentiableAt_sectionCoord c W (hlift.mdifferentiableAt (by simp))
        (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (c (t - τ))))
    have hW : W = fun s ↦ b.normalFrameExpansion (U := U) (c s)
        (h.radialParallelCoefficients b v hlr hseg s z) :=
      funext fun s ↦ radialParallelLinearMap_apply h b v hlr hseg s z
    have hzero : alongCurve (leviCivitaConnection I M) c W (t - τ) = 0 := by
      rw [hW]
      exact h.alongCurve_radialParallel_eq_zero b v hlr hseg z hs
    rw [hzero, smul_zero] at hcomp
    exact hcomp

/-- The local parallel field, along any curve equal to a translated radial geodesic. -/
private theorem IsNormalDomain.exists_parallel_of_eq (h : IsNormalDomain I M p U)
    (v : TangentSpace I p) {ρ : ℝ} (hρ : 0 ≤ ρ) (hseg : ∀ s ∈ Icc (-ρ) ρ, s • v ∈ U)
    {γ : ℝ → M} {τ : ℝ}
    (hγ : ∀ t, γ t = riemannianExp I M p ((t - τ) • v)) (z : TangentSpace I p) :
    ∃ P : ∀ t, TangentSpace I (γ t), P τ = z ∧ ∀ t ∈ Icc (τ - ρ) (τ + ρ),
      ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (P t)) t ∧
      alongCurve (leviCivitaConnection I M) γ P t = 0 := by
  obtain rfl : γ = _ := funext hγ
  exact h.exists_parallel_sub_smul v hρ hseg τ z

omit [I.Boundaryless] [T2Space M] in
/-- Gluing a parallel field on `[l, τ]` and a parallel field on `[m, r]`, `l ≤ m < τ ≤ r`, which
agree at `τ`, gives a parallel field on `[l, r]` equal to the first one on `[l, τ]`. -/
private theorem exists_parallel_glue {γ : ℝ → M} (hγd : ∀ t, MDifferentiableAt 𝓘(ℝ) I γ t)
    {l m τ r : ℝ} (hlm : l ≤ m) (hmτ : m < τ) (hτr : τ ≤ r) {P L : ∀ t, TangentSpace I (γ t)}
    (hP : ∀ t ∈ Icc l τ, ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (P t)) t ∧
      alongCurve (leviCivitaConnection I M) γ P t = 0)
    (hL : ∀ t ∈ Icc m r, ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (L t)) t ∧
      alongCurve (leviCivitaConnection I M) γ L t = 0) (hPL : P τ = L τ) :
    ∃ G : ∀ t, TangentSpace I (γ t), EqOn G P (Icc l τ) ∧ ∀ t ∈ Icc l r,
      ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (G t)) t ∧
      alongCurve (leviCivitaConnection I M) γ G t = 0 := by
  have hagree (t : ℝ) (ht : t ∈ Icc m τ) : P t = L t :=
    eq_of_parallel_Icc hγd (fun u hu ↦ hP u ⟨hlm.trans hu.1, hu.2⟩)
      (fun u hu ↦ hL u ⟨hu.1, hu.2.trans hτr⟩) ⟨hmτ.le, le_rfl⟩ hPL ht
  let G : ∀ t, TangentSpace I (γ t) := fun t ↦ if t ≤ τ then P t else L t
  have hlocal (t : ℝ) (X : ∀ t, TangentSpace I (γ t)) (hGX : ∀ᶠ u in 𝓝 t, G u = X u)
      (hX : ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (X t)) t ∧
        alongCurve (leviCivitaConnection I M) γ X t = 0) :
      ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (G t)) t ∧
        alongCurve (leviCivitaConnection I M) γ G t = 0 := by
    refine ⟨hX.1.congr_of_eventuallyEq (hGX.mono fun u hu ↦ ?_), ?_⟩
    · change TotalSpace.mk' E (γ u) (G u) = TotalSpace.mk' E (γ u) (X u)
      rw [hu]
    · rw [alongCurve_congr (leviCivitaConnection I M) γ G hGX]
      exact hX.2
  refine ⟨G, fun t ht ↦ by simp only [G, ht.2, ↓reduceIte]; exact rfl, fun t ht ↦ ?_⟩
  rcases lt_trichotomy t τ with hlt | rfl | hgt
  · exact hlocal t P ((eventually_lt_nhds hlt).mono fun u hu ↦ by simp [G, hu.le])
      (hP t ⟨ht.1, hlt.le⟩)
  · refine hlocal t L ((eventually_gt_nhds hmτ).mono fun u hu ↦ ?_) (hL t ⟨hmτ.le, hτr⟩)
    by_cases hu' : u ≤ t
    · simp only [G, hu', ↓reduceIte]
      exact hagree u ⟨hu.le, hu'⟩
    · simp only [G, hu', ↓reduceIte]
  · exact hlocal t L ((eventually_gt_nhds hgt).mono fun u hu ↦ by
      simp [G, not_le.2 hu])
      (hL t ⟨by linarith, ht.2⟩)

/-- Along a geodesic on the whole line, there is a uniform length `ρ > 0` such that every tangent
vector at a point `γ τ`, `τ ∈ [a, b]`, is the value at `τ` of a smooth parallel field on
`[τ - ρ, τ + ρ]`. -/
private theorem IsGeodesicCurve.exists_pos_forall_exists_parallel {γ : ℝ → M}
    (hγ : IsGeodesicCurve I γ) (a b : ℝ) :
    ∃ ρ > 0, ∀ τ ∈ Icc a b, ∀ z : TangentSpace I (γ τ), ∃ L : ∀ t, TangentSpace I (γ t),
      L τ = z ∧ ∀ t ∈ Icc (τ - ρ) (τ + ρ),
        ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (L t)) t ∧
        alongCurve (leviCivitaConnection I M) γ L t = 0 := by
  have hγon : IsGeodesicCurveOn I γ univ := isGeodesicCurveOn_univ.mpr hγ
  have hsmooth : ContMDiff 𝓘(ℝ) I 2 γ := contMDiffOn_univ.mp hγon.contMDiffOn
  have hK : IsCompact (γ '' Icc a b) := isCompact_Icc.image hsmooth.continuous
  obtain ⟨r, hr, _, _, hKU, hnd⟩ :=
    hK.exists_pos_exists_isOpen_superset_forall_isNormalDomain_ball (I := I)
  set C := ‖curveVelocity I γ a‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  refine ⟨r / (2 * (C + 1)), by positivity, fun τ hτ z ↦ ?_⟩
  have hseg : ∀ s ∈ Icc (-(r / (2 * (C + 1)))) (r / (2 * (C + 1))),
      s • curveVelocity I γ τ ∈ Metric.ball (0 : TangentSpace I (γ τ)) r := by
    intro s hs
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, hγ.norm_curveVelocity_eq τ a, ← hC]
    calc |s| * C ≤ r / (2 * (C + 1)) * C :=
          mul_le_mul_of_nonneg_right (abs_le.mpr ⟨hs.1, hs.2⟩) hC0
      _ < r := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
  exact (hnd (γ τ) (hKU (mem_image_of_mem γ hτ))).exists_parallel_of_eq _ (by positivity) hseg
    (hγon.eq_riemannianExp_sub_smul τ) z

/-- **Parallel fields along a geodesic.** Along a geodesic defined on the whole line, every
tangent vector at `γ a` is the initial value of a smooth parallel field on `[a, b]`. -/
theorem IsGeodesicCurve.exists_parallel {γ : ℝ → M} (hγ : IsGeodesicCurve I γ) (a b : ℝ)
    (w : TangentSpace I (γ a)) :
    ∃ P : ∀ t, TangentSpace I (γ t), P a = w ∧ ∀ t ∈ Icc a b,
      ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (P t)) t ∧
      alongCurve (leviCivitaConnection I M) γ P t = 0 := by
  rcases lt_or_ge b a with hba | hab
  · exact ⟨fun _ ↦ w, rfl, fun t ht ↦ absurd (ht.1.trans ht.2) (not_le.mpr hba)⟩
  have hγd (t : ℝ) : MDifferentiableAt 𝓘(ℝ) I γ t :=
    ((contMDiffOn_univ.mp (isGeodesicCurveOn_univ.mpr hγ).contMDiffOn) t).mdifferentiableAt
      (by simp)
  obtain ⟨ρ, hρ, hloc⟩ := hγ.exists_pos_forall_exists_parallel a b
  have hstep (k : ℕ) : ∃ P : ∀ t, TangentSpace I (γ t), P a = w ∧
      ∀ t ∈ Icc (a - ρ / 2) (min (a + k * (ρ / 2)) b),
        ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (P t)) t ∧
        alongCurve (leviCivitaConnection I M) γ P t = 0 := by
    induction k with
    | zero =>
      obtain ⟨L, hLa, hL⟩ := hloc a ⟨le_rfl, hab⟩ w
      refine ⟨L, hLa, fun t ht ↦ hL t ⟨by linarith [ht.1], ?_⟩⟩
      have := ht.2
      simp only [CharP.cast_eq_zero, zero_mul, add_zero, min_eq_left hab] at this
      linarith
    | succ k ih =>
      obtain ⟨P, hPa, hP⟩ := ih
      set τ := min (a + k * (ρ / 2)) b
      have hτ : τ ∈ Icc a b := ⟨le_min (by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) hab,
        min_le_right _ _⟩
      obtain ⟨L, hLτ, hL⟩ := hloc τ hτ (P τ)
      obtain ⟨G, hGP, hG⟩ := exists_parallel_glue hγd (le_max_left (a - ρ / 2) (τ - ρ))
        (max_lt (by linarith [hτ.1]) (by linarith)) (by linarith) hP
        (fun t ht ↦ hL t ⟨le_trans (le_max_right _ _) ht.1, ht.2⟩) hLτ.symm
      refine ⟨G, (hGP ⟨by linarith, hτ.1⟩).trans hPa, fun t ht ↦ hG t ⟨ht.1, ?_⟩⟩
      have h2 : min (a + ↑(k + 1) * (ρ / 2)) b ≤ τ + ρ / 2 := by
        rw [← min_add_add_right]
        exact min_le_min (by push_cast; linarith) (by linarith)
      linarith [ht.2]
  obtain ⟨k, hk⟩ := exists_nat_gt ((b - a) / (ρ / 2))
  obtain ⟨P, hPa, hP⟩ := hstep k
  have hkb : min (a + k * (ρ / 2)) b = b :=
    min_eq_right (by linarith [(div_lt_iff₀ (by positivity : (0 : ℝ) < ρ / 2)).mp hk])
  exact ⟨P, hPa, fun t ht ↦ hP t ⟨by linarith [ht.1], by rw [hkb]; exact ht.2⟩⟩

omit [T2Space M] in
/-- The velocity of a geodesic on the whole line is a smooth parallel field. -/
theorem IsGeodesicCurve.contMDiffAt_curveVelocity_and_alongCurve {γ : ℝ → M}
    (hγ : IsGeodesicCurve I γ) (t : ℝ) :
    ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (curveVelocity I γ t)) t ∧
      alongCurve (leviCivitaConnection I M) γ (curveVelocity I γ) t = 0 := by
  have hγon : IsGeodesicCurveOn I γ univ := isGeodesicCurveOn_univ.mpr hγ
  have h1 := hγon.contMDiffOn_curveVelocityLiftWithin_infty
  have hlift : curveVelocityLiftWithin I γ univ =
      fun t ↦ TotalSpace.mk' E (γ t) (curveVelocity I γ t) := by
    funext u
    rw [curveVelocityLiftWithin_apply, curveVelocityWithin_univ]
  rw [hlift] at h1
  refine ⟨(contMDiffOn_univ.mp h1) t, ?_⟩
  have h2 := hγon.accelerationWithin_eq_zero t (mem_univ t)
  rwa [accelerationWithin_univ, acceleration_def] at h2

/-- **A parallel orthonormal frame along a geodesic.** Parallel transport of an orthonormal basis
of `T_(γ a) M` along a geodesic on the whole line gives smooth parallel fields on `[a, b]` which
stay orthonormal. -/
theorem IsGeodesicCurve.exists_parallel_orthonormal {γ : ℝ → M} (hγ : IsGeodesicCurve I γ)
    (a b : ℝ) {ι : Type*} (e : ι → TangentSpace I (γ a)) :
    ∃ P : ι → ∀ t, TangentSpace I (γ t), (∀ i, P i a = e i) ∧
      (∀ i, ∀ t ∈ Icc a b,
        ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (P i t)) t ∧
        alongCurve (leviCivitaConnection I M) γ (P i) t = 0) ∧
      ∀ t ∈ Icc a b, ∀ i j, ⟪P i t, P j t⟫_ℝ = ⟪e i, e j⟫_ℝ := by
  choose P hPa hP using fun i ↦ hγ.exists_parallel a b (e i)
  refine ⟨P, hPa, hP, fun t ht i j ↦ ?_⟩
  have hγd (u : ℝ) : MDifferentiableAt 𝓘(ℝ) I γ u :=
    ((contMDiffOn_univ.mp (isGeodesicCurveOn_univ.mpr hγ).contMDiffOn) u).mdifferentiableAt
      (by simp)
  have hcoord (k : ι) (u : ℝ) (hu : u ∈ Icc a b) :
      DifferentiableAt ℝ (sectionCoord (F := E) γ (P k) (γ u)) u :=
    differentiableAt_sectionCoord γ (P k) ((hP k u hu).1.mdifferentiableAt (by simp))
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ u))
  rw [(isMetricCompatible_leviCivitaConnection I).inner_eq_of_alongCurve_eq_zero
    isPreconnected_Icc (fun u _ ↦ hγd u) (hcoord i) (hcoord j) (fun u hu ↦ (hP i u hu).2)
    (fun u hu ↦ (hP j u hu).2) ht ⟨le_rfl, ht.1.trans ht.2⟩, hPa, hPa]

omit [T2Space M] in
/-- A parallel field along a geodesic which starts at the velocity is the velocity. -/
theorem IsGeodesicCurve.eq_curveVelocity_of_alongCurve_eq_zero {γ : ℝ → M}
    (hγ : IsGeodesicCurve I γ) {a b : ℝ} {P : ∀ t, TangentSpace I (γ t)}
    (hP : ∀ t ∈ Icc a b,
      ContMDiffAt 𝓘(ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (P t)) t ∧
      alongCurve (leviCivitaConnection I M) γ P t = 0)
    (hPa : P a = curveVelocity I γ a) {t : ℝ} (ht : t ∈ Icc a b) :
    P t = curveVelocity I γ t := by
  have hv := hγ.contMDiffAt_curveVelocity_and_alongCurve
  exact eq_of_parallel_Icc
    (fun u ↦ ((contMDiffOn_univ.mp (isGeodesicCurveOn_univ.mpr hγ).contMDiffOn) u
      ).mdifferentiableAt (by simp)) hP (fun u _ ↦ hv u) ⟨le_rfl, ht.1.trans ht.2⟩ hPa ht

end TauCeti.Manifold
