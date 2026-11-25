/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian.Family
public import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple.Parabolic
public import TauCeti.Topology.Connected.Positivity
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Family
import TauCeti.Geometry.Manifold.Riemannian.Laplacian.Metric
import TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.ExponentialBarrier
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Radial
import TauCeti.Geometry.Manifold.ExtChartAt.ClosedBall
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Strong positivity for heat supersolutions with evolving metrics

A nonnegative scalar heat supersolution on a preconnected Hausdorff manifold is strictly
positive everywhere at every later time once it has one positive seed. If it has a later zero,
all earlier slices vanish. The metric is supplied by native smooth Riemannian metrics with
jointly `C¹` pairings. Scalar slices are `C²` and time derivatives are needed only in the open
slab. No compactness or completeness of the manifold is assumed.

The local argument compares against an expanding glued exponential profile inside a compact
chart ball. The uniform decay constant comes from the actual evolving Laplacian and gradient
coefficients. Compact-domain heat comparison uses the native Laplacian sign at local extrema;
preconnectedness then propagates positivity through the manifold.

## Main results

* `TauCeti.Manifold.heat_supersolution_local_positive_transfer`: local transfer in positive time.
* `TauCeti.Manifold.heat_supersolution_positive_at_later_time`: strict positivity everywhere.
* `TauCeti.Manifold.heat_supersolution_eq_zero_of_zero_at_later_time`: backward zero rigidity.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Corollaries 4.14–4.15.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section
open Bundle CovariantDerivative Set Topology Filter Function Polynomial Metric
open scoped ContDiff Manifold



namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The native Laplacian of a moving smooth profile. -/
private theorem laplacian_moving_scalar_barrier
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] {U : Set M}
    {q : M → ℝ} (hU : IsOpen U)
    (hq : ContMDiffOn I 𝓘(ℝ, ℝ) 2 q U)
    (A b epsilon t : ℝ) {x : M} (hx : x ∈ U) :
    laplaceBeltrami I (fun y ↦ epsilon * Real.exp (-A * t) *
        expNegInvGlue (q y + b * t)) x =
      epsilon * Real.exp (-A * t) *
        (deriv expNegInvGlue (q x + b * t) * laplaceBeltrami I q x +
          deriv (deriv expNegInvGlue) (q x + b * t) * ‖mgradient I q x‖ ^ 2) := by
  let c : ℝ := epsilon * Real.exp (-A * t)
  let φ : ℝ → ℝ := fun s ↦ c * expNegInvGlue (s + b * t)
  have harg : ContDiff ℝ ∞ (fun s : ℝ ↦ s + b * t) :=
    contDiff_id.add contDiff_const
  have hφ : ContDiff ℝ ∞ φ := by
    exact contDiff_const.mul (expNegInvGlue.contDiff.comp harg)
  have h := laplaceBeltrami_comp_of_contMDiffAt (hφ.contDiffAt.of_le (by simp))
    ((hq.contMDiffAt (hU.mem_nhds hx)).of_le (by simp))
  have hfirst : deriv φ = fun r ↦ c * deriv expNegInvGlue (r + b * t) := by
    funext r
    simp only [φ, deriv_const_mul_field, deriv_comp_add_const]
  have hφ1 : deriv φ (q x) = c * deriv expNegInvGlue (q x + b * t) := by
    rw [hfirst]
  have hφ2 : deriv (deriv φ) (q x) =
      c * deriv (deriv expNegInvGlue) (q x + b * t) := by
    rw [hfirst, deriv_const_mul_field, deriv_comp_add_const]
  rw [hφ1, hφ2] at h
  dsimp only [φ, c, Function.comp_def] at h
  rw [h]
  ring


variable (g : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hg : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        p.2 ((g p.1).inner p.2)))

include hg in
/-- One decay rate makes every nonnegative-amplitude moving profile a heat subsolution. -/
private theorem exists_moving_scalar_barrier_decay_Icc
    {a b : ℝ} {U C : Set M} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    {q : M → ℝ} (hq : ContMDiffOn I 𝓘(ℝ) 2 q U) {speed : ℝ}
    (hcritical : ∀ t ∈ Icc a b, ∀ x ∈ C,
      q x + speed * (t - a) = 0 → mvfderiv I q x ≠ 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ epsilon : ℝ, 0 ≤ epsilon → ∀ t ∈ Icc a b, ∀ x ∈ C,
      let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g t).toRiemannianMetric⟩
      epsilon * Real.exp (-A * (t - a)) *
          (-A * expNegInvGlue (q x + speed * (t - a)) +
            speed * deriv expNegInvGlue (q x + speed * (t - a))) ≤
        laplaceBeltrami I (fun y ↦ epsilon * Real.exp (-A * (t - a)) *
          expNegInvGlue (q y + speed * (t - a))) x := by
  have hK : IsCompact (Icc a b ×ˢ C) := isCompact_Icc.prod hC
  have hqP : ContinuousOn (fun p : ℝ × M ↦ q p.2) (Icc a b ×ˢ C) :=
    hq.continuousOn.comp continuousOn_snd (fun _ hp ↦ hCU hp.2)
  have hQ : ContinuousOn (fun p : ℝ × M ↦ q p.2 + speed * (p.1 - a))
      (Icc a b ×ˢ C) := hqP.add
    (continuous_const.mul (continuous_fst.sub continuous_const)).continuousOn
  have hsubset : Icc a b ×ˢ C ⊆ univ ×ˢ U := prod_mono (subset_univ _) hCU
  have hL := (continuousOn_laplaceBeltrami_family g hg.contMDiffOn hU hq).mono hsubset
  have hG := (continuousOn_norm_sq_mgradient_family
    (fun r ↦ (g r).toContinuousRiemannianMetric) hg.continuous.continuousOn hU
    (hq.of_le (by norm_num))).mono
    hsubset
  -- `toRiemannianMetric` is defined through the continuous carrier, so both functions
  -- install exactly the same fibre norm and gradient, including their instance arguments.
  have hmetric : (fun p : ℝ × M ↦
      let : RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(g p.1).toContinuousRiemannianMetric.toRiemannianMetric⟩
      ‖mgradient I q p.2‖ ^ 2) = (fun p : ℝ × M ↦
      let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g p.1).toRiemannianMetric⟩
      ‖mgradient I q p.2‖ ^ 2) := rfl
  rw [hmetric] at hG
  have hGzero : ∀ p ∈ Icc a b ×ˢ C, q p.2 + speed * (p.1 - a) = 0 →
      let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g p.1).toRiemannianMetric⟩
      0 < ‖mgradient I q p.2‖ ^ 2 := by
    intro p hp hz
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g p.1).toRiemannianMetric⟩
    exact sq_pos_of_pos (norm_pos_iff.mpr fun hzero ↦
      hcritical p.1 hp.1 p.2 hp.2 hz (mgradient_eq_zero_iff.mp hzero))
  obtain ⟨A, hA, hbar⟩ := exists_exponential_barrier_decay hK hQ hL hG hGzero speed
  refine ⟨A, hA, ?_⟩
  intro epsilon hepsilon t ht x hx
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g t).toRiemannianMetric⟩
  have hc : 0 ≤ epsilon * Real.exp (-A * (t - a)) :=
    mul_nonneg hepsilon (Real.exp_pos _).le
  have hineq := hbar (t, x) ⟨ht, hx⟩
  have hmul := mul_le_mul_of_nonneg_left hineq hc
  dsimp only at hmul ⊢
  rw [laplacian_moving_scalar_barrier hU hq A speed epsilon (t - a) (hCU hx)]
  nlinarith [hmul]

end TauCeti.Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable (g : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hg : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        p.2 ((g p.1).inner p.2)))

include hg in
/-- A supersolution dominates the expanding smooth barrier on a compact spatial domain. -/
private theorem compactDomain_moving_barrier [I.Boundaryless] [T2Space M]
    {a b : ℝ} {U C : Set M}
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    {q : M → ℝ} (hq : ContMDiffOn I 𝓘(ℝ) 2 q U) {speed : ℝ}
    (hcritical : ∀ t ∈ Icc a b, ∀ x ∈ C,
      q x + speed * (t - a) = 0 → mvfderiv I q x ≠ 0)
    (f v : ℝ → M → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ C))
    (hderiv : ∀ t ∈ Ioo a b, ∀ x ∈ interior C,
      HasDerivAt (fun s ↦ f s x) (v t x) t)
    (hsmooth : ∀ t ∈ Ioo a b, ContMDiffOn I 𝓘(ℝ) 2 (f t) U)
    (hnonneg : ∀ t ∈ Icc a b, ∀ x ∈ C, 0 ≤ f t x)
    (hevol : ∀ t ∈ Ioo a b, ∀ x ∈ interior C,
      let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g t).toRiemannianMetric⟩
      laplaceBeltrami I (f t) x ≤ v t x)
    (hboundary : ∀ t ∈ Icc a b, ∀ x ∈ C \ interior C,
      q x + speed * (t - a) ≤ 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ epsilon : ℝ, 0 ≤ epsilon →
      (∀ x ∈ C, epsilon * expNegInvGlue (q x) ≤ f a x) →
      ∀ t ∈ Icc a b, ∀ x ∈ C,
        epsilon * Real.exp (-A * (t - a)) *
          expNegInvGlue (q x + speed * (t - a)) ≤ f t x := by
  obtain ⟨A, hA, hbar⟩ := exists_moving_scalar_barrier_decay_Icc g hg hU hC hCU hq hcritical
  refine ⟨A, hA, ?_⟩
  intro epsilon hepsilon hinit
  let B : ℝ → M → ℝ := fun t x ↦ epsilon * Real.exp (-A * (t - a)) *
    expNegInvGlue (q x + speed * (t - a))
  let Bd : ℝ → M → ℝ := fun t x ↦ epsilon * Real.exp (-A * (t - a)) *
    (-A * expNegInvGlue (q x + speed * (t - a)) +
      speed * deriv expNegInvGlue (q x + speed * (t - a)))
  have hqC : ContinuousOn (fun p : ℝ × M ↦ q p.2) (Icc a b ×ˢ C) :=
    hq.continuousOn.comp continuous_snd.continuousOn (fun _ hp ↦ hCU hp.2)
  have hBC : ContinuousOn (Function.uncurry B) (Icc a b ×ˢ C) :=
    (continuousOn_const.mul
      ((continuous_const.mul (continuous_fst.sub continuous_const)).rexp.continuousOn)).mul
      ((expNegInvGlue.contDiff (n := (⊤ : ℕ∞))).continuous.comp_continuousOn
        (hqC.add (continuous_const.mul (continuous_fst.sub continuous_const)).continuousOn))
  have hBs (t : ℝ) : ContMDiffOn I 𝓘(ℝ) 2 (B t) U :=
    contMDiffOn_const.mul
      (expNegInvGlue.contDiff.contMDiff.comp_contMDiffOn (hq.add contMDiffOn_const))
  have hBd (t : ℝ) (x : M) : HasDerivAt (fun s ↦ B s x) (Bd t x) t := by
    have h := (hasDerivAt_exp_mul_expNegInvGlue (q x) A speed epsilon (t - a)).comp t
      ((hasDerivAt_id t).sub_const a)
    simpa only [Function.comp_def, id_eq, mul_one] using h
  -- Weak comparison uses only C¹ slices; this conversion retains the installed metric.
  apply compactDomain_heat_comparison (fun t ↦ (g t).ofLE (m := 1) (by simp)) le_rfl
    hU hC hCU B Bd f v hBC hf
    (fun t _ x _ ↦ hBd t x) hderiv (fun t _ ↦ hBs t) hsmooth
  · intro x hx
    simpa only [B, sub_self, mul_zero, Real.exp_zero, mul_one, add_zero] using hinit x hx
  · intro t ht x hx
    have hz := expNegInvGlue.zero_of_nonpos (hboundary t ht x hx)
    simpa only [B, hz, mul_zero] using hnonneg t ht x hx.1
  · intro t ht x hx
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g t).toRiemannianMetric⟩
    have hmetric : RiemannianBundle.g =
        ((g t).ofLE (m := 1) (by simp)).toRiemannianMetric :=
      ((g t).toRiemannianMetric_ofLE (m := 1) (by simp)).symm
    -- Expose the outer metric let, then transport the whole dependent scalar operator.
    dsimp only
    rw [((g t).ofLE (m := 1) (by simp)).laplaceBeltrami_eq_of_metric_eq hmetric (B t) x,
      ((g t).ofLE (m := 1) (by simp)).laplaceBeltrami_eq_of_metric_eq hmetric (f t) x]
    have hb := hbar epsilon hepsilon t ⟨ht.1.le, ht.2.le⟩ x (interior_subset hx)
    have he := hevol t ht x hx
    have hb' : Bd t x ≤ laplaceBeltrami I (B t) x := by
      simpa only [B, Bd] using hb
    -- `ofLE` changes only the regularity proof, so these evaluate under the same metric.
    exact (sub_nonpos.mpr hb').trans (sub_nonneg.mpr he)

end TauCeti.Manifold



namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (g : ℝ → ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
  (hg : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
    (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ)
      p.2 ((g p.1).inner p.2)))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A positive continuous seed dominates a small radial exponential bump in its chart. -/
private theorem exists_chart_radial_seed (p y : M)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).source) {R : ℝ} (hR : 0 < R)
    {F : M → ℝ} (hF : Continuous F) (hnonneg : ∀ x, 0 ≤ F x) (hpositive : 0 < F y) :
    ∃ epsilon r : ℝ, 0 < epsilon ∧ 0 < r ∧ r < R / 2 ∧
      ∀ x ∈ (extChartAt 𝓘(ℝ, E) p).source,
        epsilon * expNegInvGlue (r ^ 2 -
          ‖extChartAt 𝓘(ℝ, E) p x - extChartAt 𝓘(ℝ, E) p y‖ ^ 2) ≤ F x := by
  let e := extChartAt 𝓘(ℝ, E) p
  let epsilon : ℝ := F y / 2
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hcont : ContinuousAt (fun w : E ↦ F (e.symm w)) (e y) :=
    hF.continuousAt.comp (continuousAt_extChartAt_symm' hy)
  have hseed : {w : E | epsilon < F (e.symm w)} ∈ 𝓝 (e y) := by
    have hpreimage : {w : E | epsilon < F (e.symm w)} =
        (fun w : E ↦ F (e.symm w)) ⁻¹' Ioi epsilon := rfl
    rw [hpreimage]
    apply hcont.preimage_mem_nhds
    apply Ioi_mem_nhds
    rw [e.left_inv hy]
    dsimp [epsilon]
    linarith
  obtain ⟨delta, hdelta, hseedBall⟩ := Metric.mem_nhds_iff.mp hseed
  let r : ℝ := min (R / 4) (delta / 2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrR : r < R / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrdelta : r < delta := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨epsilon, r, hepsilon, hr, hrR, ?_⟩
  intro x hx
  by_cases hqx : r ^ 2 - ‖e x - e y‖ ^ 2 ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hqx, mul_zero]
    exact hnonneg x
  · have hsq : ‖e x - e y‖ ^ 2 < r ^ 2 := by linarith
    have hnorm : ‖e x - e y‖ < r := (sq_lt_sq₀ (norm_nonneg _) hr.le).mp hsq
    have hseedx : epsilon ≤ F x := by
      have h : epsilon < F (e.symm (e x)) :=
        hseedBall (mem_ball_iff_norm.mpr (hnorm.trans hrdelta))
      rw [e.left_inv hx] at h
      exact h.le
    calc
      epsilon * expNegInvGlue (r ^ 2 - ‖e x - e y‖ ^ 2) ≤ epsilon * 1 :=
        mul_le_mul_of_nonneg_left (expNegInvGlue.lt_one _).le hepsilon.le
      _ = epsilon := mul_one _
      _ ≤ F x := hseedx

include hg in
/-- The expanding radial barrier transfers positivity across a fixed chart ball. -/
private theorem positive_transfer_on_chart_ball [T2Space M]
    {a b : ℝ} (f v : ℝ → M → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ univ))
    (hderiv : ∀ t ∈ Ioo a b, ∀ x : M,
      HasDerivAt (fun s ↦ f s x) (v t x) t)
    (hsmooth : ∀ t ∈ Ioo a b, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (f t))
    (hnonneg : ∀ t ∈ Icc a b, ∀ x : M, 0 ≤ f t x)
    (hevol : ∀ t ∈ Ioo a b, ∀ x : M,
      let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
        ⟨(g t).toRiemannianMetric⟩
      laplaceBeltrami 𝓘(ℝ, E) (f t) x ≤ v t x)
    (p y z : M) {R : ℝ} (hR : 0 < R)
    (hyS : y ∈ (extChartAt 𝓘(ℝ, E) p).source)
    (hzS : z ∈ (extChartAt 𝓘(ℝ, E) p).source)
    (hballY : closedBall (extChartAt 𝓘(ℝ, E) p y) R ⊆
      (extChartAt 𝓘(ℝ, E) p).target)
    (hzy : ‖extChartAt 𝓘(ℝ, E) p z - extChartAt 𝓘(ℝ, E) p y‖ < R / 2)
    {s t : ℝ} (has : a ≤ s) (hst : s < t) (htb : t ≤ b) (hpositive : 0 < f s y) :
    0 < f t z := by
  let e := extChartAt 𝓘(ℝ, E) p
  let C : Set M := e.symm '' closedBall (e y) R
  obtain ⟨hC, hCU, hmem, hinterior⟩ := chart_closedBall_properties p (e y) hballY
  have hzC : z ∈ C := (hmem z hzS).2 (by linarith)
  have hstI : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
  have hs : s ∈ Icc a b := hstI ⟨le_rfl, hst.le⟩
  have hfS : Continuous (f s) := by
    rw [← continuousOn_univ]
    exact hf.comp (continuousOn_const.prodMk continuousOn_id) (fun x _ ↦ ⟨hs, mem_univ x⟩)
  obtain ⟨epsilon, r, hepsilon, hr, hrR, hinit⟩ :=
    exists_chart_radial_seed p y hyS hR hfS (hnonneg s hs) hpositive
  have hrsq : r ^ 2 < (R / 2) ^ 2 := (sq_lt_sq₀ hr.le (by positivity)).2 hrR
  let q : M → ℝ := fun x ↦ r ^ 2 - ‖e x - e y‖ ^ 2
  let speed : ℝ := ((R / 2) ^ 2 - r ^ 2) / (t - s)
  have hspeed : 0 < speed := div_pos (sub_pos.mpr hrsq) (sub_pos.mpr hst)
  have hspeedEnd : speed * (t - s) = (R / 2) ^ 2 - r ^ 2 :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr hst.ne')
  have hq : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ q e.source :=
    contMDiffOn_chart_radial p (e y) r
  have hcritical : ∀ tau ∈ Icc s t, ∀ x ∈ C,
      q x + speed * (tau - s) = 0 → mvfderiv 𝓘(ℝ, E) q x ≠ 0 := by
    intro tau htau x hx hzero
    apply mvfderiv_chart_radial_ne_zero p (e y) r (hCU hx)
    intro heq
    have heq' : e x = e y := heq
    have hqx : q x = r ^ 2 := by simp [q, heq']
    rw [hqx] at hzero
    have hmul : 0 ≤ speed * (tau - s) := mul_nonneg hspeed.le (sub_nonneg.mpr htau.1)
    nlinarith [sq_pos_of_pos hr]
  have hboundary : ∀ tau ∈ Icc s t, ∀ x ∈ C \ interior C,
      q x + speed * (tau - s) ≤ 0 := by
    intro tau htau x hx
    have hnorm : ‖e x - e y‖ = R := le_antisymm ((hmem x (hCU hx.1)).mp hx.1)
      (le_of_not_gt (fun hlt ↦ hx.2 (hinterior x (hCU hx.1) hlt)))
    have hmul : speed * (tau - s) ≤ speed * (t - s) :=
      mul_le_mul_of_nonneg_left (by linarith [htau.2]) hspeed.le
    dsimp only [q]
    rw [hnorm]
    nlinarith [sq_nonneg R]
  obtain ⟨A, _, hbar⟩ := compactDomain_moving_barrier g hg
    (isOpen_extChartAt_source p) hC hCU (hq.of_le (by norm_num)) hcritical f v
    (hf.mono (prod_mono hstI (subset_univ C)))
    (fun tau htau x _ ↦ hderiv tau ⟨has.trans_lt htau.1, htau.2.trans_le htb⟩ x)
    (fun tau htau ↦ (hsmooth tau ⟨has.trans_lt htau.1, htau.2.trans_le htb⟩).contMDiffOn)
    (fun tau htau x _ ↦ hnonneg tau (hstI htau) x)
    (fun tau htau x _ ↦ hevol tau ⟨has.trans_lt htau.1, htau.2.trans_le htb⟩ x)
    hboundary
  have hcomparison := hbar epsilon hepsilon.le (fun x hx ↦ hinit x (hCU hx))
    t ⟨hst.le, le_rfl⟩ z hzC
  have hargument : 0 < q z + speed * (t - s) := by
    have hsq : ‖e z - e y‖ ^ 2 < (R / 2) ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) (by positivity)).2 hzy
    dsimp [q]
    linarith
  exact (mul_pos (mul_pos hepsilon (Real.exp_pos _))
    (expNegInvGlue.pos_of_pos hargument)).trans_le hcomparison

include hg in
/-- A nonnegative heat supersolution with spatially `C²` slices transfers
positivity locally in any positive time using compact chart barriers, without completeness. -/
theorem heat_supersolution_local_positive_transfer [T2Space M]
    {a b : ℝ} (f v : ℝ → M → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ univ))
    (hderiv : ∀ t ∈ Ioo a b, ∀ x : M,
      HasDerivAt (fun s ↦ f s x) (v t x) t)
    (hsmooth : ∀ t ∈ Ioo a b, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (f t))
    (hnonneg : ∀ t ∈ Icc a b, ∀ x : M, 0 ≤ f t x)
    (hevol : ∀ t ∈ Ioo a b, ∀ x : M,
      let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
        ⟨(g t).toRiemannianMetric⟩
      laplaceBeltrami 𝓘(ℝ, E) (f t) x ≤ v t x)
    (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∀ s t : ℝ, a ≤ s → s < t → t ≤ b → ∀ y ∈ U, ∀ z ∈ U,
        0 < f s y → 0 < f t z := by
  let e := extChartAt 𝓘(ℝ, E) p
  obtain ⟨rho, hrho, htarget⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds (mem_extChartAt_target p))
  let R : ℝ := rho / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have hball : closedBall (e p) (3 * R) ⊆ e.target :=
    (closedBall_subset_ball (by dsimp [R]; linarith)).trans htarget
  let U : Set M := e.source ∩ e ⁻¹' ball (e p) (R / 4)
  have hU : IsOpen U :=
    (continuousOn_extChartAt p).isOpen_inter_preimage
      (isOpen_extChartAt_source p) isOpen_ball
  refine ⟨U, hU, ⟨mem_extChartAt_source p, mem_ball_self (by positivity)⟩, ?_⟩
  intro s t has hst htb y hy z hz hpositive
  have hyS : y ∈ e.source := hy.1
  have hzS : z ∈ e.source := hz.1
  have hyR : dist (e y) (e p) < R / 4 := hy.2
  have hzR : dist (e z) (e p) < R / 4 := hz.2
  have hzy : ‖e z - e y‖ < R / 2 := by
    have h := dist_triangle (e z) (e p) (e y)
    rw [dist_comm (e p) (e y)] at h
    have hd : dist (e z) (e y) < R / 2 := by linarith
    simpa only [dist_eq_norm] using hd
  have hballY : closedBall (e y) R ⊆ e.target :=
    (closedBall_subset_closedBall' (by linarith : R + dist (e y) (e p) ≤ 3 * R)).trans hball
  exact positive_transfer_on_chart_ball g hg f v hf hderiv hsmooth hnonneg hevol
    p y z hR hyS hzS hballY hzy has hst htb hpositive

include hg in
/-- On a preconnected Hausdorff manifold, one positive seed of a nonnegative scalar flow
supersolution gives strict positivity everywhere at every later time; no compactness or
completeness is assumed. -/
theorem heat_supersolution_positive_at_later_time [T2Space M] [PreconnectedSpace M]
    {a b : ℝ} (hab : a < b) (f v : ℝ → M → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ univ))
    (hderiv : ∀ t ∈ Ioo a b, ∀ x : M,
      HasDerivAt (fun s ↦ f s x) (v t x) t)
    (hsmooth : ∀ t ∈ Ioo a b, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (f t))
    (hnonneg : ∀ t ∈ Icc a b, ∀ x : M, 0 ≤ f t x)
    (hevol : ∀ t ∈ Ioo a b, ∀ x : M,
      let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
        ⟨(g t).toRiemannianMetric⟩
      laplaceBeltrami 𝓘(ℝ, E) (f t) x ≤ v t x)
    (p : M) (hp : 0 < f a p) : ∀ x : M, 0 < f b x := by
  exact positive_everywhere_of_local_transfer hab f
    (heat_supersolution_local_positive_transfer g hg f v hf hderiv hsmooth hnonneg hevol) p hp


include hg in
/-- A later zero of a nonnegative heat supersolution forces every earlier slice to vanish. -/
theorem heat_supersolution_eq_zero_of_zero_at_later_time [T2Space M] [PreconnectedSpace M]
    {a b : ℝ} (f v : ℝ → M → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ univ))
    (hderiv : ∀ t ∈ Ioo a b, ∀ x : M,
      HasDerivAt (fun s ↦ f s x) (v t x) t)
    (hsmooth : ∀ t ∈ Ioo a b, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 (f t))
    (hnonneg : ∀ t ∈ Icc a b, ∀ x : M, 0 ≤ f t x)
    (hevol : ∀ t ∈ Ioo a b, ∀ x : M,
      let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
        ⟨(g t).toRiemannianMetric⟩
      laplaceBeltrami 𝓘(ℝ, E) (f t) x ≤ v t x)
    {p : M} (hp : f b p = 0) : ∀ s ∈ Ico a b, ∀ x : M, f s x = 0 := by
  intro s hs x
  have hsub : Icc s b ⊆ Icc a b := Icc_subset_Icc_left hs.1
  have hnonnegx := hnonneg s ⟨hs.1, hs.2.le⟩ x
  apply le_antisymm _ hnonnegx
  by_contra! hpos
  have hpositive := heat_supersolution_positive_at_later_time g hg hs.2 f v
    (hf.mono (prod_mono hsub subset_rfl))
    (fun t ht y ↦ hderiv t ⟨hs.1.trans_lt ht.1, ht.2⟩ y)
    (fun t ht ↦ hsmooth t ⟨hs.1.trans_lt ht.1, ht.2⟩) (fun t ht ↦ hnonneg t (hsub ht))
    (fun t ht ↦ hevol t ⟨hs.1.trans_lt ht.1, ht.2⟩) x hpos p
  rw [hp] at hpositive
  exact lt_irrefl _ hpositive

end TauCeti.Manifold
