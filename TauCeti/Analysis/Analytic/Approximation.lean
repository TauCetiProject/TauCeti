/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Analysis.Complex.LaplaceTransform
public import TauCeti.Analysis.PDE.HeatKernel.ApproximateIdentity
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

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

## Main declarations

* `TauCeti.differentiable_intervalIntegral_mul_cexp_neg_mul_sub_sq`: Gaussian transforms
  `z ↦ ∫ y in a..b, g y exp (-c (z - y)²)` over a compact interval are entire.
* `TauCeti.norm_intervalIntegral_mul_cexp_neg_mul_sub_sq_le`: their Gaussian bound in terms of
  the distance from `re z` to `[a, b]` and of `im z`.
* `TauCeti.heatKernel_convolution_eq_intervalIntegral`: on `ℝ`, the heat kernel smoothing of a
  function supported in `[a, b]` is such a Gaussian transform.
* `LocallyFinite.hasSum_deriv_finsum`: a locally finite sum is differentiated termwise.
* `ContDiff.exists_analyticOnNhd_abs_sub_lt`: the analytic `C¹` approximation theorem.

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
open scoped Convolution Manifold

namespace TauCeti

/-! ### Gaussian transforms over a compact interval -/

/-- **Gaussian transforms over a compact interval are entire.** For `g` integrable on `[a, b]`,
the function `z ↦ ∫ y in a..b, g y * exp (-c (z - y)²)` is complex differentiable everywhere. -/
theorem differentiable_intervalIntegral_mul_cexp_neg_mul_sub_sq {g : ℝ → ℂ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (c : ℂ) :
    Differentiable ℂ fun z : ℂ ↦ ∫ y in a..b, g y * cexp (-c * (z - y) ^ 2) := by
  -- Expanding the square writes the transform as `exp (-c z²)` times a truncated Laplace
  -- transform evaluated at `-2 c z`.
  have hL := differentiable_intervalIntegral_mul_cexp_neg_mul
    (hg.mul_continuousOn
      (by fun_prop : Continuous fun y : ℝ ↦ cexp (-c * (y : ℂ) ^ 2)).continuousOn)
  have key : (fun z : ℂ ↦ ∫ y in a..b, g y * cexp (-c * (z - y) ^ 2)) =
      fun z ↦ cexp (-c * z ^ 2) *
        ∫ y in a..b, (g y * cexp (-c * (y : ℂ) ^ 2)) * cexp (-(-2 * c * z) * y) := by
    funext z
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext y
    rw [mul_comm (cexp _), mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    ring_nf
  rw [key]
  exact (by fun_prop : Differentiable ℂ fun z : ℂ ↦ cexp (-c * z ^ 2)).mul
    (hL.comp (by fun_prop))

/-- **Gaussian bound for Gaussian transforms.** If `‖g‖ ≤ M` on `[a, b]`, `c ≥ 0`, and `re z` has
distance at least `D ≥ 0` from every point of `[a, b]`, then
`‖∫ y in a..b, g y * exp (-c (z - y)²)‖ ≤ M exp (-c (D² - (im z)²)) (b - a)`. -/
theorem norm_intervalIntegral_mul_cexp_neg_mul_sub_sq_le {g : ℝ → ℂ} {a b c M D : ℝ}
    (hab : a ≤ b) (hc : 0 ≤ c) (hD : 0 ≤ D) (hM : ∀ y ∈ Icc a b, ‖g y‖ ≤ M) {z : ℂ}
    (hz : ∀ y ∈ Icc a b, D ≤ |z.re - y|) :
    ‖∫ y in a..b, g y * cexp (-c * (z - y) ^ 2)‖ ≤
      M * Real.exp (-c * (D ^ 2 - z.im ^ 2)) * (b - a) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun y : ℝ ↦ g y * cexp (-c * (z - y) ^ 2))
    (C := M * Real.exp (-c * (D ^ 2 - z.im ^ 2))) ?_
  · rwa [abs_of_nonneg (sub_nonneg.2 hab)] at this
  intro y hy
  have hy' : y ∈ Icc a b := Ioc_subset_Icc_self (by rwa [uIoc_of_le hab] at hy)
  have hre : (-(c : ℂ) * (z - y) ^ 2).re = -c * ((z.re - y) ^ 2 - z.im ^ 2) := by
    simp [sq, Complex.mul_re, Complex.sub_re, Complex.sub_im]
  rw [norm_mul, Complex.norm_exp, hre]
  refine mul_le_mul (hM y hy') (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    ((norm_nonneg _).trans (hM y hy'))
  have : D ^ 2 ≤ (z.re - y) ^ 2 := by
    rw [← sq_abs (z.re - y)]
    exact pow_le_pow_left₀ hD (hz y hy') 2
  nlinarith

/-- On `ℝ`, the heat kernel smoothing of a function supported in `[a, b]` is the Gaussian
transform `x ↦ ∫ y in a..b, (4πt)^(-1/2) g y exp (-(x - y)² / (4t))`. -/
theorem heatKernel_convolution_eq_intervalIntegral {t a b : ℝ} {g : ℝ → ℝ}
    (hgs : Function.support g ⊆ Icc a b) (hab : a ≤ b) (x : ℝ) :
    (heatKernel t ⋆ g) x =
      ∫ y in a..b, (4 * π * t) ^ (-(1 : ℝ) / 2) * g y * Real.exp (-(4 * t)⁻¹ * (x - y) ^ 2) := by
  rw [convolution_lsmul_swap, intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc, setIntegral_eq_integral_of_forall_compl_eq_zero]
  · congr 1
    funext y
    rw [heatKernel_apply, Module.finrank_self, Real.norm_eq_abs, sq_abs, smul_eq_mul,
      show -(x - y) ^ 2 / (4 * t) = -(4 * t)⁻¹ * (x - y) ^ 2 by ring, Nat.cast_one]
    ring
  · intro y hy
    rw [Function.notMem_support.1 fun h ↦ hy (hgs h), mul_zero, zero_mul]

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

/-! ### Locally finite sums -/

/-- **Termwise differentiation of a locally finite sum.** If the supports of the functions `φ k`
form a locally finite family and every `φ k` is differentiable at `x`, then the derivative of
`y ↦ ∑ᶠ k, φ k y` at `x` is the sum of the derivatives of the `φ k` at `x`. -/
theorem _root_.LocallyFinite.hasSum_deriv_finsum {ι 𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {φ : ι → 𝕜 → F}
    (hlf : LocallyFinite fun k ↦ Function.support (φ k)) {x : 𝕜}
    (hd : ∀ k, DifferentiableAt 𝕜 (φ k) x) :
    HasSum (fun k ↦ deriv (φ k) x) (deriv (fun y ↦ ∑ᶠ k, φ k y) x) := by
  obtain ⟨I, hI⟩ := hlf.exists_finset_support x
  have hsum : (fun y ↦ ∑ᶠ k, φ k y) =ᶠ[𝓝 x] fun y ↦ ∑ k ∈ I, φ k y :=
    hI.mono fun y hy ↦ finsum_eq_sum_of_support_subset _ hy
  rw [hsum.deriv_eq, deriv_fun_sum fun k _ ↦ hd k]
  refine hasSum_sum_of_ne_finset_zero fun k hk ↦ ?_
  have : φ k =ᶠ[𝓝 x] fun _ ↦ 0 := hI.mono fun y hy ↦ by_contra fun h ↦ hk (hy h)
  rw [this.deriv_eq, deriv_const]

/-- A smooth partition of unity of `ℝ` by functions supported in `(k - 1, k + 1)`, `k ∈ ℤ`. -/
private theorem exists_smoothPartitionOfUnity_int :
    ∃ ρ : SmoothPartitionOfUnity ℤ 𝓘(ℝ, ℝ) ℝ,
      ρ.IsSubordinate fun k : ℤ ↦ Ioo ((k : ℝ) - 1) (k + 1) :=
  SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℝ) isClosed_univ _ (fun _ ↦ isOpen_Ioo) fun x _ ↦
    mem_iUnion.2 ⟨⌊x⌋, by linarith [Int.floor_le x], by linarith [Int.lt_floor_add_one x]⟩

/-! ### Approximation within a constant tolerance -/

/-- The analytic `C¹` approximation theorem for a constant tolerance. -/
private theorem exists_analyticOnNhd_abs_sub_lt_of_pos {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ → ℝ, AnalyticOnNhd ℝ h univ ∧
      ∀ x, |h x - f x| < ε ∧ |deriv h x - deriv f x| < ε := by
  -- Split `f` into compactly supported pieces `g k = ρ k * f` with `tsupport (g k) ⊆ [k-1, k+1]`.
  obtain ⟨ρ, hρ⟩ := exists_smoothPartitionOfUnity_int
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

/-- Below a positive continuous function `δ` there is a positive `C¹` function `Ψ` with
`|Ψ'| ≤ 1`. -/
private theorem exists_pos_le_abs_deriv_le_one {δ : ℝ → ℝ} (hδ : Continuous δ)
    (hδ0 : ∀ x, 0 < δ x) :
    ∃ Ψ : ℝ → ℝ, ContDiff ℝ 1 Ψ ∧ ∀ x, 0 < Ψ x ∧ Ψ x ≤ δ x ∧ |deriv Ψ x| ≤ 1 := by
  have hval {φ : ℤ → ℝ → ℝ} (hlf : LocallyFinite fun k ↦ Function.support (φ k)) (x : ℝ) :
      HasSum (fun k ↦ φ k x) (∑ᶠ k, φ k x) := by
    have hfin : Function.HasFiniteSupport fun k ↦ φ k x := hlf.point_finite x
    simpa [tsum_eq_finsum hfin] using
      (summable_of_hasFiniteSupport (L := SummationFilter.unconditional ℤ) hfin).hasSum
  obtain ⟨ρ, hρ⟩ := exists_smoothPartitionOfUnity_int
  have hρd (k : ℤ) : ContDiff ℝ 1 (ρ k) := (ρ k).contMDiff.contDiff.of_le (by exact_mod_cast le_top)
  have hρs (k : ℤ) : HasCompactSupport (ρ k) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) ((hρ k).trans Ioo_subset_Icc_self)
  -- On `[k - 1, k + 1]`, `δ ≥ m k > 0` and `|ρ' k| ≤ B k`.
  have hm (k : ℤ) : ∃ m > 0, ∀ y ∈ Icc ((k : ℝ) - 1) (k + 1), m ≤ δ y := by
    obtain ⟨y₀, -, hy₀⟩ := (isCompact_Icc (a := (k : ℝ) - 1) (b := k + 1)).exists_isMinOn
      (nonempty_Icc.2 (by linarith)) hδ.continuousOn
    exact ⟨δ y₀, hδ0 y₀, hy₀⟩
  choose m hm0 hm using hm
  have hB (k : ℤ) := ((hρd k).continuous_deriv le_rfl).bounded_above_of_compact_support
    (hρs k).deriv
  choose B hB using hB
  obtain ⟨w, hw0, s, hws, hs1⟩ := NNReal.exists_pos_sum_of_countable one_ne_zero ℤ
  have hw : HasSum (fun k ↦ (w k : ℝ)) s := NNReal.hasSum_coe.2 hws
  have hw0' (k : ℤ) : (0 : ℝ) < w k := NNReal.coe_pos.2 (hw0 k)
  have hs1' : (s : ℝ) ≤ 1 := by exact_mod_cast hs1.le
  -- The coefficients `c k ≤ m k` are small enough that `|c k * ρ' k| ≤ w k`.
  set c : ℤ → ℝ := fun k ↦ min (m k) (w k / (|B k| + 1)) with hc
  have hc0 (k : ℤ) : 0 < c k := lt_min (hm0 k) (div_pos (hw0' k) (by positivity))
  have hcB (k : ℤ) (y : ℝ) : |c k * deriv (ρ k) y| ≤ w k := by
    rw [abs_mul, abs_of_pos (hc0 k)]
    calc c k * |deriv (ρ k) y| ≤ w k / (|B k| + 1) * (|B k| + 1) :=
          mul_le_mul (min_le_right _ _) (((hB k) y).trans ((le_abs_self _).trans
            (le_add_of_nonneg_right zero_le_one))) (abs_nonneg _)
            (div_pos (hw0' k) (by positivity)).le
      _ = w k := div_mul_cancel₀ _ (by positivity)
  have hlf : LocallyFinite fun k ↦ Function.support fun y ↦ c k * ρ k y :=
    ρ.locallyFinite.subset fun k ↦ Function.support_mul_subset_right _ _
  have hd (k : ℤ) : Differentiable ℝ fun y ↦ c k * ρ k y :=
    ((hρd k).differentiable one_ne_zero).const_mul _
  refine ⟨fun y ↦ ∑ᶠ k, c k * ρ k y, ?_, fun x ↦ ⟨?_, ?_, ?_⟩⟩
  · have := ρ.contMDiff_finsum_smul (n := 1) (g := fun k _ ↦ c k) fun k x _ ↦ contMDiffAt_const
    simp only [smul_eq_mul] at this
    simp_rw [mul_comm (c _)]
    exact this.contDiff
  · obtain ⟨k, hk⟩ := ρ.exists_pos_of_mem (mem_univ x)
    exact lt_of_lt_of_le (mul_pos (hc0 k) hk) (le_hasSum (hval hlf x) k
      fun j _ ↦ mul_nonneg (hc0 j).le (ρ.nonneg j x))
  · have hρx : HasSum (fun k ↦ δ x * ρ k x) (δ x) := by
      have := (hval ρ.locallyFinite x).mul_left (δ x)
      rwa [ρ.sum_eq_one (mem_univ x), mul_one] at this
    refine hasSum_le (fun k ↦ ?_) (hval hlf x) hρx
    by_cases hk : ρ k x = 0
    · simp [hk]
    · exact mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (hm k x
        (Ioo_subset_Icc_self ((hρ k) (subset_tsupport _ hk))))) (ρ.nonneg k x)
  · have := (hlf.hasSum_deriv_finsum fun k ↦ hd k x).norm_le_of_bounded hw fun k ↦ by
      rw [deriv_const_mul _ ((hρd k).differentiable one_ne_zero).differentiableAt]
      exact hcB k x
    exact this.trans hs1'

/-- An analytic weight `exp (-ψ)` whose size and derivative are controlled by a positive
continuous function: `exp (-ψ x) * (1 + |ψ' x|) ≤ ε x / 2`. -/
private theorem exists_analyticOnNhd_exp_neg_mul_le {ε : ℝ → ℝ} (hε : Continuous ε)
    (hε0 : ∀ x, 0 < ε x) :
    ∃ ψ : ℝ → ℝ, AnalyticOnNhd ℝ ψ univ ∧
      ∀ x, Real.exp (-ψ x) * (1 + |deriv ψ x|) ≤ ε x / 2 := by
  -- A positive `Ψ ≤ min (ε / 24) 1` with `|Ψ'| ≤ 1`, and an analytic `ψ` within `1` of
  -- `φ = -2 log Ψ` in `C¹`. Then `exp (-ψ) ≤ exp (1 - φ) ≤ 3 Ψ²` and `|ψ'| ≤ 1 + 2 / Ψ`.
  obtain ⟨Ψ, hΨ, hΨx⟩ := exists_pos_le_abs_deriv_le_one (hε.const_mul 24⁻¹ |>.min continuous_const)
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
