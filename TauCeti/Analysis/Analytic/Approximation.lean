/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.Calculus.Deriv.LocallyFinite
import TauCeti.Analysis.Complex.GaussianTransform
import TauCeti.Analysis.PDE.HeatKernel.ApproximateIdentity
import TauCeti.Geometry.Manifold.PartitionOfUnity.Real
import TauCeti.Topology.LocallyFinite.Basic

/-!
# `C¹` approximation by real analytic functions on the line

Every `C¹` function `f : ℝ → ℝ` can be approximated, together with its derivative, by a real
analytic function, within any positive continuous tolerance `ε`:
there is `h`, analytic on all of `ℝ`, with `|h x - f x| < ε x` and `|h' x - f' x| < ε x` for every
`x` (`ContDiff.exists_analyticOnNhd_abs_sub_lt`). This is the one-variable, first-order case of
Whitney's analytic approximation theorem. In Łojasiewicz's triangulation of semianalytic sets it
replaces a smooth positive function with prescribed strict bounds on its values and on its
derivative by an analytic one satisfying the same strict bounds.

The proof has three steps.

* A compactly supported `C¹` function `g` is approximated, with its derivative, by its heat
  kernel smoothings `K_t ⋆ g` (`TauCeti.tendstoUniformly_heatKernel_convolution`). The smoothing
  is the restriction of the entire function `z ↦ ∫ y, g y K_t(z - y)`, which is small in the strip
  `|im z| ≤ 1 / 2` away from the support of `g` once `t` is small.
* For a constant tolerance, cut `f` into compactly supported pieces by a partition of unity
  subordinate to the intervals `(k - 1, k + 1)`, `k ∈ ℤ`, and add up the entire approximations of
  the pieces. The bounds off the supports make the sum converge locally uniformly on the strip,
  so it is holomorphic there and its restriction to `ℝ` is real analytic.
* For a variable tolerance, build a positive `C¹` function `Ψ ≤ ε / 24` with `|Ψ'| ≤ 1`, approximate
  `-2 log Ψ` by an analytic `ψ` within `1`, and approximate `f exp ψ` within `1` by an analytic
  `k`. Then `h = k exp (-ψ)` is within `ε` of `f`, since the weight `exp (-ψ)` and its derivative
  are bounded by a multiple of `Ψ`.

The approximation theorem preserves strict inequalities on values and derivatives. So, given
pairwise disjoint compact sets `K i` forming a locally finite family, there is an analytic function
lying above any locally bounded function `L`, above prescribed constants `M i` on `K i`, and
with derivative of absolute value less than prescribed `ε i > 0` on `K i`
(`TauCeti.exists_analyticOnNhd_lt_and_abs_deriv_lt`). It approximates a smooth function above
`L + 1` which is constant near each `K i` (`Continuous.exists_contDiff_lt_eventuallyEq_const`).

The Gaussian transforms of the first step and their bounds are in
`TauCeti.Analysis.Complex.GaussianTransform`; the partition of unity of the second step and the
function `Ψ` of the third are in `TauCeti.Geometry.Manifold.PartitionOfUnity.Real`.

## Main declarations

* `ContDiff.exists_analyticOnNhd_abs_sub_lt`: the analytic `C¹` approximation theorem.
* `TauCeti.exists_analyticOnNhd_lt_and_abs_deriv_lt`: an analytic function with prescribed strict
  lower bounds, and derivatives prescribed small on a locally finite disjoint compact family.

## References

* H. Whitney, *Analytic extensions of differentiable functions defined in closed sets*, Trans.
  Amer. Math. Soc. 36 (1934), 63–89.
* R. Narasimhan, *Analysis on Real and Complex Manifolds*, North-Holland, 1968, §1.6 (Whitney's
  approximation theorem, proved by convolution with Gaussian kernels and partitions of unity).
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §2, Lemma 10.
-/

public section

open Complex MeasureTheory Set Filter Topology Real
open scoped Convolution

namespace TauCeti

/-! ### Approximating a compactly supported function by entire functions -/

/-- `(4πt)^(-1/2) exp (-3 / (16 t)) → 0` as `t → 0⁺`. -/
private theorem tendsto_rpow_mul_exp_nhdsGT_zero :
    Tendsto (fun t ↦ (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (-(4 * t)⁻¹ * (3 / 4)))
      (𝓝[>] 0) (𝓝 0) := by
  have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) (3 / 16)
    (by norm_num)).comp tendsto_inv_nhdsGT_zero).const_mul ((4 * π) ^ (-(1 : ℝ) / 2))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [Function.comp_apply, Real.mul_rpow (by positivity) ht.le, Real.inv_rpow ht.le, neg_div,
    Real.rpow_neg ht.le]
  ring_nf

/-- A `C¹` function `g` supported in `[a, b]` is approximated within `η`, with its derivative, by
the restriction to `ℝ` of an entire function `F`, which is bounded on the strip `|im z| ≤ 1 / 2`
and at most `δ` there at distance at least `1` from `[a, b]`. -/
private theorem exists_differentiable_approx {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {a b : ℝ}
    (hab : a ≤ b) (hgs : tsupport g ⊆ Icc a b) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ x : ℝ, |(F x).re - g x| < η ∧ |(deriv F x).re - deriv g x| < η) ∧
      (∃ C, ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖F z‖ ≤ C) ∧
      ∀ z : ℂ, |z.im| ≤ 1 / 2 → (∀ y ∈ Icc a b, 1 ≤ |z.re - y|) → ‖F z‖ ≤ δ := by
  have hcs : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs
  have hgc := hg.continuous
  have hdc := hg.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := hgc.bounded_above_of_compact_support hcs
  obtain ⟨M', hM'⟩ := hdc.bounded_above_of_compact_support hcs.deriv
  -- Choose the time `t` so that `K_t ⋆ g` and `K_t ⋆ g'` are `η`-close to `g` and `g'`, and the
  -- Gaussian bound off the support is at most `δ`.
  have h₁ := Metric.tendstoUniformly_iff.1 (tendstoUniformly_heatKernel_convolution
    (.ofNormedAddCommGroup g hgc M hM) (hcs.uniformContinuous_of_continuous hgc)) η hη
  have h₂ := Metric.tendstoUniformly_iff.1 (tendstoUniformly_heatKernel_convolution
    (.ofNormedAddCommGroup (deriv g) hdc M' hM')
    (hcs.deriv.uniformContinuous_of_continuous hdc)) η hη
  have h₃ := ((tendsto_rpow_mul_exp_nhdsGT_zero.mul_const (M * (b - a))).eventually
    (gt_mem_nhds (a := δ) (by simpa using hδ)))
  obtain ⟨t, ⟨⟨⟨ht₁, ht₂⟩, ht₃⟩, ht : 0 < t⟩⟩ := (((h₁.and h₂).and h₃).and
    self_mem_nhdsWithin).exists
  set A := (4 * π * t) ^ (-(1 : ℝ) / 2) with hA
  set c := (4 * t)⁻¹ with hc
  have hA0 : 0 < A := by positivity
  have hc0 : 0 ≤ c := by positivity
  let F : ℂ → ℂ := fun z ↦ ∫ y in a..b, ((A * g y : ℝ) : ℂ) * cexp (-(c : ℂ) * (z - y) ^ 2)
  have hF : Differentiable ℂ F :=
    differentiable_intervalIntegral_mul_cexp_neg_mul_sub_sq
      ((by fun_prop : Continuous fun y : ℝ ↦ ((A * g y : ℝ) : ℂ)).intervalIntegrable _ _) _
  have hFx (x : ℝ) : F x = (heatKernel t ⋆ g) x := by
    rw [heatKernel_convolution_eq_intervalIntegral ((subset_tsupport g).trans hgs) hab,
      ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun y _ ↦ ?_
    simp only [hA, hc]
    push_cast [Complex.ofReal_exp]
    ring_nf
  have hFre : (fun x : ℝ ↦ (F x).re) = heatKernel t ⋆ g := funext fun x ↦ by simp [hFx]
  have hbound (D : ℝ) (hD : 0 ≤ D) (z : ℂ) (hz : |z.im| ≤ 1 / 2)
      (hzD : ∀ y ∈ Icc a b, D ≤ |z.re - y|) :
      ‖F z‖ ≤ A * M * Real.exp (-c * (D ^ 2 - 1 / 4)) * (b - a) := by
    refine (norm_intervalIntegral_mul_cexp_neg_mul_sub_sq_le hab hc0 hD (M := A * M)
      (fun y _ ↦ ?_) hzD).trans ?_
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hA0]
      exact mul_le_mul_of_nonneg_left (hM y) hA0.le
    · have : z.im ^ 2 ≤ 1 / 4 := by
        rw [← sq_abs]; nlinarith [abs_nonneg z.im]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 ?_) (mul_nonneg hA0.le ((norm_nonneg _).trans (hM a))))
        (sub_nonneg.2 hab)
      nlinarith
  refine ⟨F, hF, fun x ↦ ⟨?_, ?_⟩, ⟨_, fun z hz ↦ hbound 0 le_rfl z hz fun y _ ↦ abs_nonneg _⟩,
    fun z hz hzD ↦ (hbound 1 zero_le_one z hz hzD).trans ?_⟩
  · rw [hFx, Complex.ofReal_re, abs_sub_comm]
    exact ht₁ x
  · have hd : HasDerivAt (heatKernel t ⋆ g) (deriv F x).re x := by
      rw [← hFre]
      exact (hF x).hasDerivAt.real_of_complex
    rw [hd.unique (hcs.hasDerivAt_convolution_right _
      (contDiff_heatKernel t (k := 0)).continuous.locallyIntegrable hg x), abs_sub_comm]
    exact ht₂ x
  · calc A * M * Real.exp (-c * (1 ^ 2 - 1 / 4)) * (b - a)
        = A * Real.exp (-c * (3 / 4)) * (M * (b - a)) := by ring_nf
      _ ≤ δ := ht₃.le

/-! ### Approximation within a constant tolerance -/

/-- The analytic `C¹` approximation theorem for a constant tolerance. -/
private theorem exists_analyticOnNhd_abs_sub_lt_of_pos {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ → ℝ, AnalyticOnNhd ℝ h univ ∧
      ∀ x, |h x - f x| < ε ∧ |deriv h x - deriv f x| < ε := by
  -- Split `f` into compactly supported pieces `g k = ρ k * f` with `tsupport (g k) ⊆ [k-1, k+1]`.
  obtain ⟨ρ, hρ⟩ := exists_smoothPartitionOfUnity_isSubordinate_Ioo_int
  set g : ℤ → ℝ → ℝ := fun k x ↦ ρ k x * f x with hg_def
  have hg (k : ℤ) : ContDiff ℝ 1 (g k) :=
    ((ρ k).contMDiff.contDiff.of_le (by exact_mod_cast le_top)).mul hf
  have hgs (k : ℤ) : tsupport (g k) ⊆ Icc ((k : ℝ) - 1) (k + 1) :=
    tsupport_mul_subset_left.trans ((hρ k).trans Ioo_subset_Icc_self)
  have hfg : f = fun y ↦ ∑ᶠ k, g k y := funext fun y ↦ by
    simp only [hg_def, ← finsum_mul, ρ.sum_eq_one (mem_univ y), one_mul]
  have hloc (x : ℝ) :
      HasSum (fun k ↦ g k x) (f x) ∧ HasSum (fun k ↦ deriv (g k) x) (deriv f x) := by
    have hlf : LocallyFinite fun k ↦ Function.support (g k) :=
      ρ.locallyFinite.subset fun k ↦ Function.support_mul_subset_left _ _
    have hfin : Function.HasFiniteSupport fun k ↦ g k x := hlf.point_finite x
    rw [hfg]
    refine ⟨?_, hlf.hasSum_deriv_finsum fun k ↦ (hg k).differentiable one_ne_zero x⟩
    simpa [tsum_eq_finsum hfin] using
      (summable_of_hasFiniteSupport (L := SummationFilter.unconditional ℤ) hfin).hasSum
  -- Summable positive tolerances `w k` with sum less than `ε`.
  obtain ⟨w, hw0, c, hwc, hcε⟩ := NNReal.exists_pos_sum_of_countable (ε := ε.toNNReal)
    (Real.toNNReal_pos.2 hε).ne' ℤ
  have hw : HasSum (fun k ↦ (w k : ℝ)) c := NNReal.hasSum_coe.2 hwc
  have hcε' : (c : ℝ) < ε := Real.lt_toNNReal_iff_coe_lt.1 hcε
  choose F hFd hFapprox hFC hFtail using fun k : ℤ ↦ exists_differentiable_approx (hg k)
    (by linarith) (hgs k) (hw0 k) (hw0 k)
  choose C hC using hFC
  -- On a neighbourhood of each real point in the strip `|im z| < 1 / 2`, the pieces are bounded by
  -- a summable sequence: all but finitely many of them are far away.
  set U : ℝ → Set ℂ := fun x₀ ↦ {z | |z.im| < 1 / 2 ∧ |z.re - x₀| < 1} with hU
  have hUo (x₀ : ℝ) : IsOpen (U x₀) :=
    (isOpen_lt (continuous_abs.comp continuous_im) continuous_const).inter
      (isOpen_lt (continuous_abs.comp (continuous_re.sub continuous_const)) continuous_const)
  have hUx (x₀ : ℝ) : (x₀ : ℂ) ∈ U x₀ := by simp [hU]
  have hdom (x₀ : ℝ) : ∃ u : ℤ → ℝ, Summable u ∧ ∀ k, ∀ z ∈ U x₀, ‖F k z‖ ≤ u k := by
    have hfinite : {k : ℤ | |(k : ℝ) - x₀| < 3}.Finite := by
      refine (Set.finite_Icc (⌊x₀⌋ - 3) (⌈x₀⌉ + 3)).subset fun k (hk : |(k : ℝ) - x₀| < 3) ↦ ?_
      have hk := abs_lt.1 hk
      have h₁ : ((⌊x₀⌋ - 3 : ℤ) : ℝ) ≤ k := by push_cast; linarith [Int.floor_le x₀]
      have h₂ : (k : ℝ) ≤ ((⌈x₀⌉ + 3 : ℤ) : ℝ) := by push_cast; linarith [Int.le_ceil x₀]
      exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩
    refine ⟨fun k ↦ if |(k : ℝ) - x₀| < 3 then C k else w k, ?_, fun k z hz ↦ ?_⟩
    · refine Summable.of_norm_bounded_eventually hw.summable ?_
      filter_upwards [hfinite.compl_mem_cofinite] with k hk
      have hk : ¬|(k : ℝ) - x₀| < 3 := hk
      simp [hk]
    · obtain ⟨hz₁, hz₂⟩ := hz
      dsimp only
      split_ifs with hk
      · exact hC k z hz₁.le
      · refine hFtail k z hz₁.le fun y hy ↦ ?_
        have h₁ : |(k : ℝ) - y| ≤ 1 := abs_le.2 ⟨by linarith [hy.2], by linarith [hy.1]⟩
        have h₂ := abs_sub_le (k : ℝ) y x₀
        have h₃ := abs_sub_le y z.re x₀
        rw [abs_sub_comm y z.re] at h₃
        push Not at hk
        linarith
  -- The sum `H` of the entire approximations is holomorphic on the strip.
  set H : ℂ → ℂ := fun z ↦ ∑' k, F k z with hH_def
  have hH (x₀ : ℝ) : DifferentiableOn ℂ H (U x₀) := by
    obtain ⟨u, hu, hFu⟩ := hdom x₀
    exact differentiableOn_tsum_of_summable_norm hu (fun k ↦ (hFd k).differentiableOn) (hUo x₀) hFu
  have hHsum (x : ℝ) : HasSum (fun k ↦ F k x) (H x) := by
    obtain ⟨u, hu, hFu⟩ := hdom x
    exact (Summable.of_norm_bounded hu fun k ↦ hFu k x (hUx x)).hasSum
  have hHderiv (x : ℝ) : HasSum (fun k ↦ deriv (F k) x) (deriv H x) := by
    obtain ⟨u, hu, hFu⟩ := hdom x
    exact hasSum_deriv_of_summable_norm hu (fun k ↦ (hFd k).differentiableOn) (hUo x) hFu (hUx x)
  have hHan (x : ℝ) : AnalyticAt ℂ H x := (hH x).analyticAt ((hUo x).mem_nhds (hUx x))
  refine ⟨fun x ↦ (H x).re, fun x _ ↦ ?_, fun x ↦ ⟨?_, ?_⟩⟩
  · exact (reCLM.analyticAt _).comp ((hHan x).restrictScalars.comp (ofRealCLM.analyticAt x))
  · exact ((((hHsum x).mapL reCLM).sub (hloc x).1).norm_le_of_bounded hw
      fun k ↦ (hFapprox k x).1.le).trans_lt hcε'
  · rw [((hHan x).differentiableAt.hasDerivAt.real_of_complex).deriv]
    exact ((((hHderiv x).mapL reCLM).sub (hloc x).2).norm_le_of_bounded hw
      fun k ↦ (hFapprox k x).2.le).trans_lt hcε'

/-! ### Approximation within a variable tolerance -/

/-- An analytic weight `exp (-ψ)` whose size and derivative are controlled by a positive
continuous function: `exp (-ψ x) * (1 + |ψ' x|) ≤ ε x / 2`. -/
private theorem exists_analyticOnNhd_exp_neg_mul_le {ε : ℝ → ℝ} (hε : Continuous ε)
    (hε0 : ∀ x, 0 < ε x) :
    ∃ ψ : ℝ → ℝ, AnalyticOnNhd ℝ ψ univ ∧
      ∀ x, Real.exp (-ψ x) * (1 + |deriv ψ x|) ≤ ε x / 2 := by
  -- A positive `Ψ ≤ min (ε / 24) 1` with `|Ψ'| ≤ 1`, and an analytic `ψ` within `1` of
  -- `φ = -2 log Ψ` in `C¹`. Then `exp (-ψ) ≤ exp (1 - φ) ≤ 3 Ψ²` and `|ψ'| ≤ 1 + 2 / Ψ`.
  obtain ⟨Ψ, hΨ, hΨx⟩ := (hε.const_mul 24⁻¹ |>.min continuous_const)
    |>.exists_contDiff_pos_le_abs_deriv_le_one
      fun x ↦ lt_min (mul_pos (by norm_num) (hε0 x)) one_pos
  have hφ : ContDiff ℝ 1 fun x ↦ -2 * Real.log (Ψ x) :=
    contDiff_const.mul (hΨ.log fun x ↦ (hΨx x).1.ne')
  obtain ⟨ψ, hψa, hψ⟩ := exists_analyticOnNhd_abs_sub_lt_of_pos hφ one_pos
  refine ⟨ψ, hψa, fun x ↦ ?_⟩
  obtain ⟨hΨ0x, hΨε, hΨ'⟩ := hΨx x
  have hΨ1 : Ψ x ≤ 1 := hΨε.trans (min_le_right _ _)
  have hΨε' : 24 * Ψ x ≤ ε x := by linarith [hΨε.trans (min_le_left _ _)]
  have he : Real.exp (-ψ x) ≤ 3 * Ψ x ^ 2 := by
    calc Real.exp (-ψ x) ≤ Real.exp (1 + Real.log (Ψ x) + Real.log (Ψ x)) :=
          Real.exp_le_exp.2 (by linarith [(abs_lt.1 (hψ x).1).1])
      _ = Real.exp 1 * Ψ x ^ 2 := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log hΨ0x]; ring
      _ ≤ 3 * Ψ x ^ 2 := by
          gcongr; exact Real.exp_one_lt_d9.le.trans (by norm_num)
  have hd : Ψ x * |deriv ψ x| ≤ Ψ x + 2 := by
    have hφ' : deriv (fun x ↦ -2 * Real.log (Ψ x)) x = -2 * (deriv Ψ x / Ψ x) :=
      (((hΨ.differentiable one_ne_zero x).hasDerivAt.log hΨ0x.ne').const_mul _).deriv
    have h1 : |deriv ψ x| ≤ 1 + 2 * |deriv Ψ x| / Ψ x := by
      have h2 : |-2 * (deriv Ψ x / Ψ x)| = 2 * |deriv Ψ x| / Ψ x := by
        rw [abs_mul, abs_div, abs_of_pos hΨ0x]; norm_num; ring
      have := (abs_sub_abs_le_abs_sub _ _).trans (hψ x).2.le
      rw [hφ', h2] at this
      linarith
    calc Ψ x * |deriv ψ x| ≤ Ψ x * (1 + 2 * |deriv Ψ x| / Ψ x) :=
          mul_le_mul_of_nonneg_left h1 hΨ0x.le
      _ = Ψ x + 2 * |deriv Ψ x| := by field_simp
      _ ≤ Ψ x + 2 := by linarith
  nlinarith [abs_nonneg (deriv ψ x), Real.exp_pos (-ψ x)]

end TauCeti

open TauCeti in
/-- **Analytic `C¹` approximation on the line.** A `C¹` function `f : ℝ → ℝ` can be approximated
by a real analytic function `h`, together with its derivative, within any positive continuous
tolerance `ε`: `|h x - f x| < ε x` and `|h' x - f' x| < ε x` for every `x`. -/
theorem ContDiff.exists_analyticOnNhd_abs_sub_lt {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {ε : ℝ → ℝ}
    (hε : Continuous ε) (hε0 : ∀ x, 0 < ε x) :
    ∃ h : ℝ → ℝ, AnalyticOnNhd ℝ h univ ∧
      ∀ x, |h x - f x| < ε x ∧ |deriv h x - deriv f x| < ε x := by
  -- With the weight `e = exp (-ψ)`, approximate `G = f / e` within `1` by an analytic `k` and put
  -- `h = k e`. Then `h - f = (k - G) e` and `h' - f' = (k' - G') e + (k - G) e'`.
  obtain ⟨ψ, hψa, hsmall⟩ := exists_analyticOnNhd_exp_neg_mul_le hε hε0
  have hψd : ContDiff ℝ 1 ψ := hψa.contDiff
  set e : ℝ → ℝ := fun x ↦ Real.exp (-ψ x) with he_def
  have he0 (x : ℝ) : 0 < e x := Real.exp_pos _
  have hderiv_e (x : ℝ) : HasDerivAt e (-deriv ψ x * e x) x := by
    simpa [he_def, mul_comm] using ((hψd.differentiable one_ne_zero x).hasDerivAt.neg).exp
  set G : ℝ → ℝ := fun x ↦ f x * Real.exp (ψ x) with hG_def
  have hG : ContDiff ℝ 1 G := hf.mul hψd.exp
  obtain ⟨k, hka, hk⟩ := exists_analyticOnNhd_abs_sub_lt_of_pos hG one_pos
  have hfGe : f = fun x ↦ G x * e x := funext fun x ↦ by
    rw [hG_def, he_def, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  refine ⟨fun x ↦ k x * e x, fun x _ ↦ (hka x (mem_univ x)).mul
    (hψa x (mem_univ x)).neg.rexp', fun x ↦ ⟨?_, ?_⟩⟩
  · have : |k x * e x - f x| = |k x - G x| * e x := by
      rw [hfGe, ← sub_mul, abs_mul, abs_of_pos (he0 x)]
    rw [this]
    nlinarith [mul_lt_mul_of_pos_right (hk x).1 (he0 x), hsmall x, hε0 x,
      abs_nonneg (deriv ψ x)]
  · rw [((hka.contDiff (n := 1)).differentiable one_ne_zero x).hasDerivAt.fun_mul (hderiv_e x)
      |>.deriv, hfGe, ((hG.differentiable one_ne_zero x).hasDerivAt.fun_mul (hderiv_e x)).deriv]
    have key : deriv k x * e x + k x * (-deriv ψ x * e x) -
        (deriv G x * e x + G x * (-deriv ψ x * e x)) =
        (deriv k x - deriv G x) * e x - (k x - G x) * (deriv ψ x * e x) := by ring
    rw [key]
    calc |(deriv k x - deriv G x) * e x - (k x - G x) * (deriv ψ x * e x)|
        ≤ |deriv k x - deriv G x| * e x + |k x - G x| * (|deriv ψ x| * e x) := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos (he0 x)]
      _ < 1 * e x + 1 * (|deriv ψ x| * e x) := by
          have := he0 x
          have : 0 ≤ |deriv ψ x| * e x := by positivity
          nlinarith [(hk x).1, (hk x).2]
      _ = e x * (1 + |deriv ψ x|) := by ring
      _ < ε x := by linarith [hsmall x, hε0 x]

namespace TauCeti

open Function

/-- **Analytic functions with prescribed strict bounds.** Let `K i` be pairwise disjoint compact
subsets of `ℝ` forming a locally finite family, and let `L : ℝ → ℝ` be locally bounded above.
For any constants `M i` and `ε i > 0` there is a real analytic `h` with `L < h` everywhere and,
on each `K i`, `M i < h` and `|h'| < ε i`. -/
theorem exists_analyticOnNhd_lt_and_abs_deriv_lt {ι : Type*} {K : ι → Set ℝ}
    (hK : ∀ i, IsCompact (K i)) (hdisj : Pairwise (Disjoint on K)) (hlf : LocallyFinite K)
    {L : ℝ → ℝ} (hL : ∀ x, ∃ C, ∀ᶠ y in 𝓝 x, L y ≤ C) (M : ι → ℝ) {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) :
    ∃ h : ℝ → ℝ, AnalyticOnNhd ℝ h univ ∧ (∀ x, L x < h x) ∧
      ∀ i, ∀ x ∈ K i, M i < h x ∧ |deriv h x| < ε i := by
  -- A smooth target `F > L + 1`, constant above `M i + 1` near each `K i`.
  obtain ⟨G, hG⟩ := exists_continuous_forall_mem_convex_of_local_const
    (t := fun x ↦ Ioi (L x + 1)) (fun _ ↦ convex_Ioi _) fun x ↦ by
      obtain ⟨C, hC⟩ := hL x
      exact ⟨C + 2, hC.mono fun y hy ↦ by simp only [mem_Ioi]; linarith⟩
  obtain ⟨F, hFd, hGF, hFc⟩ :=
    G.continuous.exists_contDiff_lt_eventuallyEq_const hK hdisj hlf fun i ↦ M i + 1
  choose c hMc hFc using hFc
  -- A tolerance at most `1`, and below `ε i` on `K i`, preserves these strict bounds.
  obtain ⟨e, he0, he⟩ := hlf.exists_continuous_pos_lt (fun i ↦ (hK i).isClosed)
    (ε := fun i _ ↦ ε i) (fun _ ↦ continuousOn_const) fun i _ _ ↦ hε i
  obtain ⟨h, hha, hh⟩ := (hFd.of_le (by norm_cast)).exists_analyticOnNhd_abs_sub_lt
    (ε := fun x ↦ min (e x) 1) (e.continuous.min continuous_const)
    fun x ↦ lt_min (he0 x) one_pos
  refine ⟨h, hha, fun x ↦ ?_, fun i x hx ↦ ?_⟩
  · linarith [abs_lt.1 (hh x).1, mem_Ioi.1 (hG x), hGF x, min_le_right (e x) 1]
  · have hFx : F =ᶠ[𝓝 x] fun _ ↦ c i := (hFc i).filter_mono (nhds_le_nhdsSet hx)
    have h1 := abs_lt.1 (hh x).1
    have h2 := (hh x).2
    rw [hFx.deriv_eq, deriv_const, sub_zero] at h2
    rw [hFx.eq_of_nhds] at h1
    exact ⟨by linarith [min_le_right (e x) 1, hMc i],
      h2.trans_le ((min_le_left _ _).trans (he i x hx).le)⟩

end TauCeti
