/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# Dilated cutoffs with Laplacian bounds

In a finite-dimensional real inner product space, dilating a fixed smooth bump by `R` gives cutoffs
`χ_R`, equal to `1` on `ball 0 R` and to `0` off `closedBall 0 (2R)`, with
`‖Dχ_R‖ = O(1/R)` and `|Δχ_R| = O(1/R²)` uniformly in `R`
(`TauCeti.exists_forall_contDiff_cutoff_ball_norm_laplacian_le`). These are the truncations used
to localize solutions of the Poisson equation: the error `Δ(χ_R u) - χ_R Δu` lives on the annulus
`R ≤ ‖x‖ ≤ 2R` and is controlled by the decay of `u` and `Du` there.

In dimension two the bound `|Δχ_R| = O(1/R²)` makes `∫ |Δχ_R|` bounded uniformly in `R`, so
`∫ Δχ_R f → 0` for every `f` tending to `0` at infinity
(`TauCeti.tendsto_integral_laplacian_smul_of_tendsto_cocompact`). This lets identities tested
against `χ_R` pass to `R → ∞`. The same holds for the cutoffs `χ_R h` of a harmonic weight `h`
which, with its derivative, grows at most like `‖x‖ᵏ`, against every `f` with `‖x‖ᵏ⁺¹ f → 0`
(`TauCeti.tendsto_integral_laplacian_mul_smul_of_tendsto_cocompact`): then
`Δ(χ_R h) = h Δχ_R + 2 ⟪∇χ_R, ∇h⟫` is `O(Rᵏ⁻¹)` on the annulus `R ≤ ‖x‖ ≤ 2R`. This lets
identities tested against `χ_R h` pass to `R → ∞`, giving the moments of a distribution against
harmonic polynomials.
-/

public section

namespace TauCeti

open ContinuousLinearMap Filter Metric MeasureTheory Topology
open scoped ContDiff Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Dilated cutoffs with Laplacian bounds.** There is a constant `C` such that for every `R > 0`
some smooth compactly supported `χ` equals `1` near every point of `ball 0 R`, equals `0` near
every point outside `closedBall 0 (2R)`, and satisfies `0 ≤ χ ≤ 1`, `‖Dχ‖ ≤ C / R` and
`|Δχ| ≤ C / R²`. The cutoff is `x ↦ b (R⁻¹ • x)` for a fixed smooth bump `b` equal to `1` on
`closedBall 0 1` and supported in `closedBall 0 2`. -/
theorem exists_forall_contDiff_cutoff_ball_norm_laplacian_le :
    ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∃ χ : E → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (∀ x, ‖x‖ < R → χ =ᶠ[𝓝 x] fun _ => 1) ∧
        (∀ x, 2 * R < ‖x‖ → χ =ᶠ[𝓝 x] fun _ => 0) ∧ (∀ x, ‖fderiv ℝ χ x‖ ≤ C / R) ∧
          (∀ x, ‖Δ χ x‖ ≤ C / R ^ 2) ∧ ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1 := by
  let b : ContDiffBump (0 : E) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hb : ContDiff ℝ ∞ b := b.contDiff
  obtain ⟨C₁, hC₁⟩ := (hb.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (b.hasCompactSupport.fderiv (𝕜 := ℝ))
  obtain ⟨C₂, hC₂⟩ := (continuousOn_univ.1 ((hb.of_le (by simp)).contDiffOn.continuousOn_laplacian
    isOpen_univ)).bounded_above_of_compact_support
      (b.hasCompactSupport.mono' ((subset_tsupport _).trans (tsupport_laplacian_subset _)))
  refine ⟨max C₁ C₂, fun R hR => ⟨fun x => b (R⁻¹ • x), hb.comp (contDiff_id.const_smul R⁻¹),
    b.hasCompactSupport.comp_smul (inv_ne_zero hR.ne'), fun x hx => ?_, fun x hx => ?_,
    fun x => ?_, (fun x => ?_), fun _ => ⟨b.nonneg, b.le_one⟩⟩⟩
  · filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hx)] with y hy
    refine b.one_of_mem_closedBall (mem_closedBall_zero_iff.2 ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, inv_mul_le_iff₀ hR, mul_one]
    exact (mem_ball_zero_iff.1 hy).le
  · filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    refine b.zero_of_le_dist ?_
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR,
      le_inv_mul_iff₀ hR]
    linarith
  · have h : HasFDerivAt (fun x => b (R⁻¹ • x)) _ x :=
      ((hb.differentiable (by simp)) (R⁻¹ • x)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).const_smul R⁻¹)
    rw [h.fderiv]
    refine (opNorm_comp_le _ _).trans ?_
    rw [div_eq_mul_inv]
    refine mul_le_mul ((hC₁ _).trans (le_max_left _ _)) ?_ (norm_nonneg _)
      ((norm_nonneg _).trans ((hC₁ 0).trans (le_max_left _ _)))
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    exact mul_le_of_le_one_right (inv_nonneg.2 hR.le) (norm_id_le)
  · rw [laplacian_comp_smul_right, norm_smul, Real.norm_eq_abs, div_eq_mul_inv, ← inv_pow,
      abs_pow, abs_inv, abs_of_pos hR, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hC₂ _).trans (le_max_right _ _)) (by positivity)

section Limits

open InnerProductSpace

variable [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} {l : Filter ι} {χ : ι → E → ℝ} {R : ι → ℝ}

/-- In a two-dimensional space, a function bounded by `a / r²` and supported in
`closedBall 0 (2 * r)` has integral of norm at most `4 a μ(closedBall 0 1)`. -/
private theorem norm_integral_le_of_norm_le_indicator_closedBall (μ : Measure E)
    [μ.IsAddHaarMeasure] (hE : Module.finrank ℝ E = 2) {f : E → F} {r a : ℝ} (hr : 0 < r)
    (hf : ∀ x, ‖f x‖ ≤ (closedBall (0 : E) (2 * r)).indicator (fun _ ↦ a / r ^ 2) x) :
    ‖∫ x, f x ∂μ‖ ≤ 4 * a * μ.real (closedBall (0 : E) 1) := by
  have hg : Integrable ((closedBall (0 : E) (2 * r)).indicator fun _ ↦ a / r ^ 2) μ :=
    (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall
  refine (norm_integral_le_of_norm_le hg (.of_forall hf)).trans_eq ?_
  rw [integral_indicator_const _ measurableSet_closedBall,
    Measure.addHaar_real_closedBall' μ _ (by positivity), hE, smul_eq_mul]
  field_simp
  ring

/-- **Laplacians of planar cutoffs against decaying functions.** In a two-dimensional space, let
the cutoffs `χ i` equal `1` near `ball 0 (R i)` and `0` near the complement of
`closedBall 0 (2 * R i)`, with `|Δ χ i| ≤ C / (R i)²` and `R i → ∞`. Then `∫ Δ χ i • f → 0` for
every `f` tending to `0` at infinity, since `∫ |Δ χ i|` is bounded uniformly in `i`. -/
theorem tendsto_integral_laplacian_smul_of_tendsto_cocompact (μ : Measure E)
    [μ.IsAddHaarMeasure] (hE : Module.finrank ℝ E = 2) {C : ℝ} (hR : Tendsto R l atTop)
    (hχ1 : ∀ i x, ‖x‖ < R i → χ i =ᶠ[𝓝 x] fun _ => 1)
    (hχ0 : ∀ i x, 2 * R i < ‖x‖ → χ i =ᶠ[𝓝 x] fun _ => 0)
    (hχΔ : ∀ i x, ‖Δ (χ i) x‖ ≤ C / R i ^ 2) {f : E → F}
    (hf : Tendsto f (cocompact E) (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, Δ (χ i) x • f x ∂μ) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set C' := max C 0
  set V := μ.real (closedBall (0 : E) 1)
  have hV : 0 ≤ V := measureReal_nonneg
  set ε' := ε / (4 * V * C' + 1) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨R', -, hR'⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := E) ▸ Metric.tendsto_nhds.mp hf ε' hε'pos)
  filter_upwards [hR.eventually_gt_atTop (max R' 0)] with i hi
  have hRi : 0 < R i := (le_max_right _ _).trans_lt hi
  -- `Δ χ i • f` is supported in `closedBall 0 (2 * R i)`, where it is at most `C' ε' / R i ^ 2`.
  set g : E → ℝ := (closedBall (0 : E) (2 * R i)).indicator fun _ ↦ C' * ε' / R i ^ 2
  have hbound : ∀ x, ‖Δ (χ i) x • f x‖ ≤ g x := by
    intro x
    have hg₀ : 0 ≤ g x := Set.indicator_nonneg (fun _ _ ↦ by positivity) x
    by_cases h₁ : ‖x‖ < R i
    · rw [(laplacian_congr_nhds (hχ1 i x h₁)).eq_of_nhds, laplacian_const]
      simpa using hg₀
    by_cases h₂ : 2 * R i < ‖x‖
    · rw [(laplacian_congr_nhds (hχ0 i x h₂)).eq_of_nhds, laplacian_const]
      simpa using hg₀
    have hx : x ∈ closedBall (0 : E) (2 * R i) := mem_closedBall_zero_iff.mpr (not_lt.mp h₂)
    have hfx : ‖f x‖ ≤ ε' := by
      simpa using (hR' (((le_max_left _ _).trans_lt hi).le.trans (not_lt.mp h₁))).le
    have hgx : g x = C' * ε' / R i ^ 2 := Set.indicator_of_mem hx _
    rw [hgx, norm_smul, mul_div_right_comm]
    exact mul_le_mul ((hχΔ i x).trans (div_le_div_of_nonneg_right (le_max_left _ _)
      (by positivity))) hfx (norm_nonneg _) (by positivity)
  rw [dist_zero_right]
  calc ‖∫ x, Δ (χ i) x • f x ∂μ‖ ≤ 4 * (C' * ε') * V :=
        norm_integral_le_of_norm_le_indicator_closedBall μ hE hRi hbound
    _ = 4 * V * C' * ε' := by ring
    _ < ε := by
      rw [hε', mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hV) (le_max_right C 0)]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Off the annulus `r ≤ ‖x‖ ≤ 2r`, where the cutoff `χ` is locally constant, `Δ (χ h) = 0` for a
harmonic `h`. -/
private theorem laplacian_mul_eq_zero_of_lt_or_lt {χ h : E → ℝ} {x : E} {r : ℝ}
    (hχ1 : ‖x‖ < r → χ =ᶠ[𝓝 x] fun _ => 1) (hχ0 : 2 * r < ‖x‖ → χ =ᶠ[𝓝 x] fun _ => 0)
    (hΔ : Δ h = 0) (hx : ‖x‖ < r ∨ 2 * r < ‖x‖) : Δ (fun y ↦ χ y * h y) x = 0 := by
  rcases hx with hx | hx
  · have heq : (fun y ↦ χ y * h y) =ᶠ[𝓝 x] h := (hχ1 hx).mono fun y hy ↦ by simp only [hy, one_mul]
    rw [(laplacian_congr_nhds heq).eq_of_nhds, hΔ, Pi.zero_apply]
  · have heq : (fun y ↦ χ y * h y) =ᶠ[𝓝 x] fun _ ↦ 0 :=
      (hχ0 hx).mono fun y hy ↦ by simp only [hy, zero_mul]
    rw [(laplacian_congr_nhds heq).eq_of_nhds, laplacian_const, Pi.zero_apply]

omit [MeasurableSpace E] [BorelSpace E] in
open Gradient in
/-- The pointwise estimate behind
`TauCeti.tendsto_integral_laplacian_mul_smul_of_tendsto_cocompact`. Let `1 ≤ r ≤ ‖x‖`,
`‖Dχ x‖ ≤ C / r`, `|Δχ x| ≤ C / r²`, `|h x| ≤ c ‖x‖ᵏ`, `‖Dh x‖ ≤ c ‖x‖ᵏ`, `Δh x = 0` and
`‖x‖ᵏ⁺¹ ‖f x‖ ≤ ε`. Then `‖Δ (χ h) x • f x‖ ≤ 3 c C ε / r²`. -/
private theorem norm_laplacian_mul_smul_le {χ h : E → ℝ} {f : E → F} {x : E} {r c C ε : ℝ}
    {k : ℕ} (hχ : ContDiffAt ℝ 2 χ x) (hh : ContDiffAt ℝ 2 h x) (hΔ : Δ h x = 0) (hr : 1 ≤ r)
    (hxr : r ≤ ‖x‖) (hc : 0 ≤ c) (hC : 0 ≤ C) (hχD : ‖fderiv ℝ χ x‖ ≤ C / r)
    (hχΔ : |Δ χ x| ≤ C / r ^ 2) (hhx : |h x| ≤ c * ‖x‖ ^ k)
    (hdhx : ‖fderiv ℝ h x‖ ≤ c * ‖x‖ ^ k) (hfx : ‖x‖ ^ (k + 1) * ‖f x‖ ≤ ε) :
    ‖Δ (fun y ↦ χ y * h y) x • f x‖ ≤ 3 * c * C * ε / r ^ 2 := by
  have hr₀ : 0 < r := one_pos.trans_le hr
  -- `‖x‖ᵏ ‖f x‖ ≤ ε / r`, from `‖x‖ᵏ⁺¹ ‖f x‖ ≤ ε`.
  have hfx' : ‖x‖ ^ k * ‖f x‖ ≤ ε / r := by
    rw [le_div_iff₀ hr₀]
    calc ‖x‖ ^ k * ‖f x‖ * r ≤ ‖x‖ ^ k * ‖f x‖ * ‖x‖ := by gcongr
      _ = ‖x‖ ^ (k + 1) * ‖f x‖ := by ring
      _ ≤ ε := hfx
  have hgrad : |⟪∇ χ x, ∇ h x⟫_ℝ| ≤ C / r * (c * ‖x‖ ^ k) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [gradient, gradient, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
    exact mul_le_mul hχD hdhx (norm_nonneg _) (by positivity)
  have hr₂ : 1 / r ^ 2 ≤ 1 / r := one_div_le_one_div_of_le hr₀ (le_self_pow₀ hr two_ne_zero)
  -- The Leibniz rule, with `Δ h = 0`.
  rw [hχ.laplacian_fun_mul hh, hΔ, mul_zero, zero_add, norm_smul, Real.norm_eq_abs]
  calc |2 * ⟪∇ χ x, ∇ h x⟫_ℝ + h x * Δ χ x| * ‖f x‖
      ≤ (2 * (C / r * (c * ‖x‖ ^ k)) + c * ‖x‖ ^ k * (C / r ^ 2)) * ‖f x‖ := by
        gcongr
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_two]; gcongr
        · rw [abs_mul]; gcongr
    _ = c * C * (2 / r + 1 / r ^ 2) * (‖x‖ ^ k * ‖f x‖) := by ring
    _ ≤ c * C * (3 / r) * (ε / r) := by
        gcongr
        linarith [show 2 / r + 1 / r = 3 / r by ring]
    _ = 3 * c * C * ε / r ^ 2 := by ring

/-- **Laplacians of planar cutoffs of harmonic weights against decaying functions.** In a
two-dimensional space, let the `C²` cutoffs `χ i` equal `1` near `ball 0 (R i)` and `0` near the
complement of `closedBall 0 (2 * R i)`, with `‖Dχ i‖ ≤ C / R i`, `|Δ χ i| ≤ C / (R i)²` and
`R i → ∞`. Let `h` be a `C²` harmonic function such that `h` and `Dh` are `O(‖x‖ᵏ)` at infinity.
Then `∫ Δ (χ i h) • f → 0` for every `f` such that `‖x‖ᵏ⁺¹ f x → 0` at infinity. -/
theorem tendsto_integral_laplacian_mul_smul_of_tendsto_cocompact (μ : Measure E)
    [μ.IsAddHaarMeasure] (hE : Module.finrank ℝ E = 2) {C : ℝ} (hR : Tendsto R l atTop)
    (hχ : ∀ i, ContDiff ℝ 2 (χ i)) (hχ1 : ∀ i x, ‖x‖ < R i → χ i =ᶠ[𝓝 x] fun _ => 1)
    (hχ0 : ∀ i x, 2 * R i < ‖x‖ → χ i =ᶠ[𝓝 x] fun _ => 0)
    (hχD : ∀ i x, ‖fderiv ℝ (χ i) x‖ ≤ C / R i) (hχΔ : ∀ i x, ‖Δ (χ i) x‖ ≤ C / R i ^ 2)
    {h : E → ℝ} (hh : ContDiff ℝ 2 h) (hΔ : Δ h = 0) {k : ℕ}
    (hhk : h =O[cocompact E] fun x ↦ ‖x‖ ^ k)
    (hdhk : fderiv ℝ h =O[cocompact E] fun x ↦ ‖x‖ ^ k) {f : E → F}
    (hf : Tendsto (fun x ↦ ‖x‖ ^ (k + 1) • f x) (cocompact E) (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, Δ (fun y ↦ χ i y * h y) x • f x ∂μ) l (𝓝 0) := by
  -- Bounds `|h x| ≤ c ‖x‖ᵏ` and `‖Dh x‖ ≤ c ‖x‖ᵏ` outside the disc of radius `R₀`.
  obtain ⟨c₁, hc₁⟩ := hhk.bound
  obtain ⟨c₂, hc₂⟩ := hdhk.bound
  obtain ⟨R₀, -, hR₀⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := E) ▸ hc₁.and hc₂)
  set c := max (max c₁ c₂) 0
  set C' := max C 0
  rw [Metric.tendsto_nhds]
  intro ε hε
  set V := μ.real (closedBall (0 : E) 1)
  have hV : 0 ≤ V := measureReal_nonneg
  set ε' := ε / (12 * c * C' * V + 1) with hε'
  obtain ⟨R', -, hR'⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := E) ▸ Metric.tendsto_nhds.mp hf ε' (by positivity))
  filter_upwards [hR.eventually_gt_atTop (max (max R' R₀) 1)] with i hi
  set r := R i
  have hr₁ : 1 < r := (le_max_right _ _).trans_lt hi
  -- `Δ (χ h) • f` is supported in `closedBall 0 (2 r)`, where it is at most `3 c C' ε' / r²`.
  set g : E → ℝ := (closedBall (0 : E) (2 * r)).indicator fun _ ↦ 3 * c * C' * ε' / r ^ 2
  have hbound : ∀ x, ‖Δ (fun y ↦ χ i y * h y) x • f x‖ ≤ g x := by
    intro x
    have hg₀ : 0 ≤ g x := Set.indicator_nonneg (fun _ _ ↦ by positivity) x
    by_cases h₁ : ‖x‖ < r ∨ 2 * r < ‖x‖
    · rwa [laplacian_mul_eq_zero_of_lt_or_lt (hχ1 i x) (hχ0 i x) hΔ h₁, zero_smul, norm_zero]
    obtain ⟨h₁, h₂⟩ := not_or.mp h₁
    have hxr : r ≤ ‖x‖ := not_lt.mp h₁
    obtain ⟨hhx, hdhx⟩ := hR₀ ((le_max_right _ _ |>.trans (le_max_left _ _)).trans
      (hi.le.trans hxr))
    simp only [Real.norm_eq_abs, abs_pow, abs_norm] at hhx hdhx
    have hgx : g x = 3 * c * C' * ε' / r ^ 2 :=
      Set.indicator_of_mem (mem_closedBall_zero_iff.mpr (not_lt.mp h₂)) _
    rw [hgx]
    refine norm_laplacian_mul_smul_le (hχ i).contDiffAt hh.contDiffAt (congrFun hΔ x) hr₁.le hxr
      (le_max_right _ _) (le_max_right _ _) ((hχD i x).trans (by gcongr; exact le_max_left _ _))
      ((hχΔ i x).trans (by gcongr; exact le_max_left _ _))
      (hhx.trans (by gcongr; exact (le_max_left _ _).trans (le_max_left _ _)))
      (hdhx.trans (by gcongr; exact (le_max_right _ _).trans (le_max_left _ _))) ?_
    simpa [norm_smul, norm_pow] using
      (hR' ((le_max_left _ _ |>.trans (le_max_left _ _)).trans (hi.le.trans hxr))).le
  rw [dist_zero_right]
  calc ‖∫ x, Δ (fun y ↦ χ i y * h y) x • f x ∂μ‖ ≤ 4 * (3 * c * C' * ε') * V :=
        norm_integral_le_of_norm_le_indicator_closedBall μ hE (by positivity) hbound
    _ = 12 * c * C' * V * ε' := by ring
    _ < ε := by
      rw [hε', mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12)
        (le_max_right (max c₁ c₂) 0)) (le_max_right C 0)) hV]

end Limits

end TauCeti
