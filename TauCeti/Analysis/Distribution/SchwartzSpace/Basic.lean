/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Conjneg
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import Mathlib.Analysis.RCLike.Lemmas
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Weighted bounds and integrability of Schwartz functions

A Schwartz function is bounded and decays faster than any power. Pointwise, it absorbs any
polynomial weight `⟨c x⟩ ^ m = (1 + ‖c x‖²) ^ (m / 2)` and still decays like `(1 + ‖x‖) ^ (-k)`.
Consequently `‖x‖ ^ k ‖f x‖²` is
integrable against any measure of temperate growth. This is the integrability input for weighted
`L²` estimates such as the weighted Plancherel identity. Likewise the pointwise inner product of two
Schwartz functions is integrable, which justifies splitting `L²` pairings of Schwartz functions.

## Main declarations

* `SchwartzMap.one_add_norm_smul_sq_rpow_mul_norm_le`: `⟨c x⟩ ^ m ‖f x‖` is bounded by a finite
  supremum of Schwartz seminorms of `f` times `(1 + ‖x‖) ^ (-k)`.
* `SchwartzMap.norm_le_add_seminorm_mul_inv_one_add_norm_pow`: `‖f x‖` is bounded by the sum of its
  `(0, 0)` and `(k, 0)` seminorms times `(1 + ‖x‖ ^ k)⁻¹`.
* `SchwartzMap.integrable_norm_pow_mul_norm_sq`: `‖x‖ ^ k ‖f x‖²` is integrable.
* `SchwartzMap.integrable_inner`: `⟪f x, g x⟫` is integrable.
* `SchwartzMap.integrable_mul`: `f x * g x` is integrable for Schwartz functions with values in a
  normed ring.
* `SchwartzMap.integrable_norm_rpow_mul_norm`: `‖x‖ ^ s ‖f x‖` is integrable for real `s ≥ 0`.
* `SchwartzMap.integrable_one_add_norm_sq_rpow_mul_norm`: `(1 + ‖x‖ ^ 2) ^ r ‖f x‖` is integrable
  for every real `r`.
* `SchwartzMap.integrable_one_add_norm_smul_sq_rpow_mul_norm`: `⟨c x⟩ ^ m ‖f x‖` is integrable
  against any measure of temperate growth.
* `SchwartzMap.integrable_norm_iteratedFDeriv`: `‖D^k f x‖` is integrable.
* `SchwartzMap.integrable_smul_apply`: a Schwartz function times a homogeneous polynomial
  `A (x, …, x)` is integrable.
* `SchwartzMap.exists_integrable_norm_iteratedFDeriv_add_le`: `‖D^n f (z + h)‖` has an integrable
  envelope in `z`, uniformly for `‖h‖ ≤ 1`, so convolutions with `f` can be differentiated under
  the integral.
* `SchwartzMap.postcompCLM_re_add_I_smul_im`: a complex Schwartz function is its real part plus `I`
  times its imaginary part, so complex-linear maps out of `𝓢(E, ℂ)` are determined by real
  Schwartz functions.
* `SchwartzMap.integrable_iteratedFDeriv_comp_left`,
  `SchwartzMap.integral_norm_iteratedFDeriv_comp_left_le`: for a continuous linear map `L`, the
  derivatives of `L ∘ f` are integrable, with `∫ ‖D^k (L ∘ f)‖ ≤ ‖L‖ ∫ ‖D^k f‖`.
* `SchwartzMap.norm_toLp_sq`: the squared `L²` norm of `f` is `∫ ‖f x‖²`.
* `SchwartzMap.integral_inner_eq_inner_toLp`: `∫ ⟪f x, g x⟫` is the `L²` inner product of `f`
  with an `L²` function `g`.
* `SchwartzMap.conjnegCLM`: the continuous conjugate-linear reversed-conjugation involution,
  with exact reflected-support, compact-support and near-origin cutoff laws.
* `SchwartzMap.bilinLeftCLM_apply_eq_sum`: the pointwise product of Schwartz functions with
  `A x = ∑ i ∈ s, c i x • L i` is `∑ i ∈ s, L i (c i f)`.
* `SchwartzMap.bilinLeftCLM_eq_sum_smulLeftCLM`: the expansion of `x ↦ B (u x) (g x)` in a basis
  of `G` as a finite sum of scalar multiplications.
* `SchwartzMap.conjCLM`: pointwise conjugation of scalar Schwartz functions, a continuous
  conjugate-linear map.
* `SchwartzMap.integral_norm_sq_eq_zero_iff`: a Schwartz function vanishes exactly when the
  integral of its squared norm does, for a measure charging every nonempty open set.
* `SchwartzMap.eq_of_forall_integral_mul_eq`: two `𝕜`-valued Schwartz functions with the same
  integral pairing against every Schwartz function are equal.
* `IsOpen.eqOn_of_integral_clm_apply_eq`: two operator families continuous on an open set `U`
  agree there if they have the same integrals against compactly supported Schwartz functions
  supported in `U`.
* `TauCeti.eq_zero_of_forall_integral_apply_eq_zero`: a continuous operator-valued function that
  integrates to zero against every Schwartz function vanishes.
* `SchwartzMap.closure_range_toLp_eq`: the closure of the Schwartz functions in `Lᵖ` is the
  topological closure of the range of `SchwartzMap.toLpCLM`, a closed subspace.
* `HasCompactSupport.toSchwartzMap_toLp`: the `Lᵖ` class of a smooth compactly supported function
  is the same whether built through `HasCompactSupport.toSchwartzMap` or from `MemLp`.
-/

public section

open MeasureTheory

namespace SchwartzMap

open scoped SchwartzMap InnerProductSpace

section Weight

variable {𝕜 E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- Pointwise decay of a Schwartz function against `1 + ‖x‖ ^ k`, bounded by the sum of its
`(0, 0)` and `(k, 0)` seminorms. -/
theorem norm_le_add_seminorm_mul_inv_one_add_norm_pow (k : ℕ) (f : 𝓢(E, F)) (x : E) :
    ‖f x‖ ≤ (SchwartzMap.seminorm 𝕜 0 0 f + SchwartzMap.seminorm 𝕜 k 0 f) * (1 + ‖x‖ ^ k)⁻¹ := by
  rw [le_mul_inv_iff₀ (by positivity), mul_add, mul_one, mul_comm ‖f x‖]
  exact add_le_add (f.norm_le_seminorm 𝕜 x) (f.norm_pow_mul_le_seminorm 𝕜 k x)

/-- A Schwartz function absorbs the polynomial weight `⟨c x⟩ ^ m = (1 + ‖c x‖²) ^ (m / 2)` and
still decays like `(1 + ‖x‖) ^ (-k)`, with a constant given by a finite supremum of Schwartz
seminorms. -/
theorem one_add_norm_smul_sq_rpow_mul_norm_le (c m : ℝ) (k : ℕ) (f : 𝓢(E, F)) (x : E) :
    (1 + ‖c • x‖ ^ 2) ^ (m / 2) * ‖f x‖ ≤
      max 1 |c| ^ ⌈m⌉₊ * 2 ^ (⌈m⌉₊ + k) *
        (Finset.Iic (⌈m⌉₊ + k, 0)).sup (fun n ↦ SchwartzMap.seminorm 𝕜 n.1 n.2) f *
        (1 + ‖x‖) ^ (-(k : ℝ)) := by
  set K := ⌈m⌉₊
  set S := (Finset.Iic (K + k, 0)).sup (fun n ↦ SchwartzMap.seminorm 𝕜 n.1 n.2) f
  set t := ‖c • x‖
  have ht : t = |c| * ‖x‖ := by
    simp [t, norm_smul]
  have hx : 0 < 1 + ‖x‖ := by positivity
  -- The bracket of order `m` is dominated by a polynomial weight of degree `K = ⌈m⌉₊`.
  have hweight : (1 + t ^ 2) ^ (m / 2) ≤ max 1 |c| ^ K * (1 + ‖x‖) ^ K := by
    calc (1 + t ^ 2) ^ (m / 2) ≤ (1 + t ^ 2) ^ ((K : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by nlinarith)
            (by gcongr; exact Nat.le_ceil m)
      _ ≤ ((1 + t) ^ 2) ^ ((K : ℝ) / 2) := by
          gcongr
          nlinarith [norm_nonneg (c • x)]
      _ = (1 + t) ^ K := by
          rw [← Real.rpow_natCast (1 + t) 2, ← Real.rpow_mul (by positivity),
            show ((2 : ℕ) : ℝ) * ((K : ℝ) / 2) = (K : ℝ) by push_cast; ring, Real.rpow_natCast]
      _ ≤ (max 1 |c| * (1 + ‖x‖)) ^ K := by
          gcongr
          rw [ht]
          nlinarith [le_max_left 1 |c|, le_max_right 1 |c|, norm_nonneg x]
      _ = max 1 |c| ^ K * (1 + ‖x‖) ^ K := mul_pow _ _ _
  -- The Schwartz function decays like `(1 + ‖x‖) ^ (-(K + k))`.
  have hdecay : (1 + ‖x‖) ^ (K + k) * ‖f x‖ ≤ 2 ^ (K + k) * S := by
    simpa using f.one_add_le_sup_seminorm_apply (𝕜 := 𝕜) (m := (K + k, 0)) le_rfl le_rfl x
  have hsplit : (1 + ‖x‖) ^ K = (1 + ‖x‖) ^ (-(k : ℝ)) * (1 + ‖x‖) ^ (K + k) := by
    rw [Real.rpow_neg hx.le, Real.rpow_natCast, pow_add]
    field_simp
  calc (1 + t ^ 2) ^ (m / 2) * ‖f x‖ ≤ max 1 |c| ^ K * (1 + ‖x‖) ^ K * ‖f x‖ := by gcongr
    _ = max 1 |c| ^ K * (1 + ‖x‖) ^ (-(k : ℝ)) * ((1 + ‖x‖) ^ (K + k) * ‖f x‖) := by
        rw [hsplit]; ring
    _ ≤ max 1 |c| ^ K * (1 + ‖x‖) ^ (-(k : ℝ)) * (2 ^ (K + k) * S) := by gcongr
    _ = _ := by ring

end Weight

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.HasTemperateGrowth]

omit [SecondCountableTopology E] in
/-- For a Schwartz function `f`, the function `‖x‖ ^ k * ‖D^n f x‖` is integrable. Unlike
`SchwartzMap.integrable_pow_mul_iteratedFDeriv`, this needs no second countability of `E`: the
function is real-valued and continuous. -/
theorem integrable_pow_mul_norm_iteratedFDeriv (f : 𝓢(E, F)) (k n : ℕ) :
    Integrable (fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) μ := by
  refine ((Measure.integrable_pow_neg_integrablePower μ).const_mul
    (2 ^ μ.integrablePower * (SchwartzMap.seminorm ℝ 0 n f +
      SchwartzMap.seminorm ℝ (k + μ.integrablePower) n f))).mono'
    ((continuous_norm.pow k).mul
      ((f.smooth ⊤).continuous_iteratedFDeriv (mod_cast le_top)).norm).aestronglyMeasurable
    (.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_mul_le_of_le_of_pow_mul_le (norm_nonneg _) (norm_nonneg _)
    (norm_iteratedFDeriv_le_seminorm ℝ _ _ x) (le_seminorm ℝ _ _ _ x)

omit [SecondCountableTopology E] in
/-- For a Schwartz function `f`, the function `‖x‖ ^ k ‖f x‖²` is integrable. -/
theorem integrable_norm_pow_mul_norm_sq (f : 𝓢(E, F)) (k : ℕ) :
    Integrable (fun x ↦ ‖x‖ ^ k * ‖f x‖ ^ 2) μ := by
  refine ((f.integrable_pow_mul_norm_iteratedFDeriv (μ := μ) k 0).const_mul
    (SchwartzMap.seminorm ℝ 0 0 f)).mono' (by fun_prop) (.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity), sq, ← mul_assoc, mul_comm _ ‖f x‖,
    norm_iteratedFDeriv_zero]
  gcongr
  exact f.norm_le_seminorm ℝ x

omit [BorelSpace E] [SecondCountableTopology E] in
/-- The squared `L²` norm of a Schwartz function is the integral of its squared pointwise norm. -/
theorem norm_toLp_sq [OpensMeasurableSpace E] [SecondCountableTopologyEither E F] (f : 𝓢(E, F)) :
    ‖f.toLp 2 μ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ :=
  (f.memLp 2 μ).norm_toLp_sq

omit [BorelSpace E] [SecondCountableTopology E] in
/-- The integral of the pointwise inner product of a Schwartz function `f` with an `L²` function
`g` is the `L²` inner product of `f` with `g`. -/
theorem integral_inner_eq_inner_toLp {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [NormedSpace ℝ H] [OpensMeasurableSpace E]
    [SecondCountableTopologyEither E H] (f : 𝓢(E, H)) (g : Lp H 2 μ) :
    ∫ x, ⟪f x, g x⟫_𝕜 ∂μ = ⟪f.toLp 2 μ, g⟫_𝕜 := by
  rw [L2.inner_def]
  exact integral_congr_ae (by filter_upwards [f.coeFn_toLp 2 μ] with x hx; rw [hx])

omit [SecondCountableTopology E] in
/-- A Schwartz function vanishes if and only if the integral of its squared norm does, against a
measure of temperate growth that charges every nonempty open set. -/
theorem integral_norm_sq_eq_zero_iff [μ.IsOpenPosMeasure] {f : 𝓢(E, F)} :
    ∫ x, ‖f x‖ ^ 2 ∂μ = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have hint : Integrable (fun x => ‖f x‖ ^ 2) μ := by
    simpa using f.integrable_norm_pow_mul_norm_sq (μ := μ) 0
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖f x‖) hint).mp h
  have hcont : Continuous fun x => ‖f x‖ ^ 2 := by fun_prop
  have := (hcont.ae_eq_iff_eq μ continuous_zero).mp hae
  exact SchwartzMap.ext fun x => by simpa using congrFun this x

omit [SecondCountableTopology E] in
/-- For Schwartz functions `f` and `g` with values in a normed ring `A` (for instance `ℝ` or `ℂ`),
the pointwise product `f x * g x` is integrable. -/
theorem integrable_mul {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℝ A]
    [SecondCountableTopologyEither E A] (f g : 𝓢(E, A)) : Integrable (fun x ↦ f x * g x) μ :=
  -- `‖f x * g x‖ ≤ ‖f x‖ * sup ‖g‖`, and `f` is integrable since it lies in `L¹`.
  ((memLp_one_iff_integrable.1 (f.memLp 1 μ)).norm.mul_const (SchwartzMap.seminorm ℝ 0 0 g)).mono'
    (f.continuous.mul g.continuous).aestronglyMeasurable
    (.of_forall fun x ↦ (norm_mul_le _ _).trans (by gcongr; exact g.norm_le_seminorm ℝ x))

omit [SecondCountableTopology E] in
/-- Two `𝕜`-valued Schwartz functions that have the same integral pairing against every `𝕜`-valued
Schwartz function are equal, for a measure of temperate growth that charges every nonempty open
set. -/
theorem eq_of_forall_integral_mul_eq {𝕜 : Type*} [RCLike 𝕜] [μ.IsOpenPosMeasure] {f g : 𝓢(E, 𝕜)}
    (h : ∀ θ : 𝓢(E, 𝕜), ∫ x, f x * θ x ∂μ = ∫ x, g x * θ x ∂μ) : f = g := by
  set δ : 𝓢(E, 𝕜) := f - g
  set θ : 𝓢(E, 𝕜) := δ.postcompCLM (RCLike.conjCLE (K := 𝕜)).toContinuousLinearMap
  have hδ0 : ∫ x, δ x * θ x ∂μ = 0 := by
    have hsub : (fun x ↦ δ x * θ x) = fun x ↦ f x * θ x - g x * θ x :=
      funext fun x ↦ sub_mul (f x) (g x) (θ x)
    rw [hsub, integral_sub (f.integrable_mul θ) (g.integrable_mul θ), h θ, sub_self]
  have hnorm : ∫ x, ‖δ x‖ ^ 2 ∂μ = 0 := by
    have hcongr : (fun x ↦ δ x * θ x) = fun x ↦ ((‖δ x‖ ^ 2 : ℝ) : 𝕜) :=
      funext fun x ↦ by simp [θ, mul_comm (δ x), RCLike.conj_mul]
    rwa [hcongr, integral_ofReal, RCLike.ofReal_eq_zero] at hδ0
  exact sub_eq_zero.1 ((integral_norm_sq_eq_zero_iff (μ := μ)).1 hnorm)

omit [SecondCountableTopology E] in
/-- For Schwartz functions `f` and `g` with values in an inner product space over `𝕜`, the
pointwise inner product `⟪f x, g x⟫_𝕜` is integrable. -/
theorem integrable_inner {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [NormedSpace ℝ H] (f g : 𝓢(E, H)) : Integrable (fun x ↦ ⟪f x, g x⟫_𝕜) μ := by
  have hf := f.integrable_pow_mul_norm_iteratedFDeriv (μ := μ) 0 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hf
  refine (hf.const_mul (SchwartzMap.seminorm ℝ 0 0 g)).mono'
    (f.continuous.inner g.continuous).aestronglyMeasurable (.of_forall fun x ↦ ?_)
  rw [mul_comm]
  exact (norm_inner_le_norm _ _).trans (by gcongr; exact g.norm_le_seminorm ℝ x)

omit [SecondCountableTopology E] in
/-- For a Schwartz function `f` and real `c`, `m`, the function
`⟨c x⟩ ^ m ‖f x‖ = (1 + ‖c x‖ ^ 2) ^ (m / 2) ‖f x‖` is integrable. -/
theorem integrable_one_add_norm_smul_sq_rpow_mul_norm (c m : ℝ) (f : 𝓢(E, F)) :
    Integrable (fun x ↦ (1 + ‖c • x‖ ^ 2) ^ (m / 2) * ‖f x‖) μ :=
  ((Measure.integrable_pow_neg_integrablePower μ).const_mul _).mono'
    ((((continuous_const.add ((continuous_const_smul _).norm.pow 2)).rpow_const
      fun x ↦ Or.inl (by positivity : (1 : ℝ) + ‖c • x‖ ^ 2 ≠ 0)).mul
        f.continuous.norm).aestronglyMeasurable)
    (.of_forall fun x ↦ by
      rw [Real.norm_of_nonneg (by positivity)]
      exact f.one_add_norm_smul_sq_rpow_mul_norm_le (𝕜 := ℝ) c m μ.integrablePower x)

omit [SecondCountableTopology E] in
/-- For a Schwartz function `f` and every real `r`, the function `(1 + ‖x‖ ^ 2) ^ r ‖f x‖` is
integrable. With `r = s / 2` this is the Japanese bracket weight `⟨x⟩ ^ s ‖f x‖`. -/
theorem integrable_one_add_norm_sq_rpow_mul_norm (r : ℝ) (f : 𝓢(E, F)) :
    Integrable (fun x ↦ (1 + ‖x‖ ^ 2) ^ r * ‖f x‖) μ := by
  simpa only [one_smul, mul_div_cancel_left₀ r two_ne_zero] using
    f.integrable_one_add_norm_smul_sq_rpow_mul_norm (μ := μ) 1 (2 * r)

omit [SecondCountableTopology E] in
/-- For a Schwartz function `f` and real `s ≥ 0`, the moment weight `‖x‖ ^ s ‖f x‖` is
integrable. -/
theorem integrable_norm_rpow_mul_norm (f : 𝓢(E, F)) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun x ↦ ‖x‖ ^ s * ‖f x‖) μ :=
  (f.integrable_one_add_norm_smul_sq_rpow_mul_norm (μ := μ) 1 s).mono'
    ((continuous_norm.rpow_const fun _ ↦ Or.inr hs).mul f.continuous.norm).aestronglyMeasurable
    (.of_forall fun x ↦ by
      rw [one_smul, Real.norm_of_nonneg (by positivity)]
      gcongr
      calc ‖x‖ ^ s = (‖x‖ ^ 2) ^ (s / 2) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]
            ring_nf
        _ ≤ (1 + ‖x‖ ^ 2) ^ (s / 2) := by gcongr; linarith)

omit [SecondCountableTopology E] in
/-- The norms of the derivatives of a Schwartz function are integrable. -/
theorem integrable_norm_iteratedFDeriv (f : 𝓢(E, F)) (k : ℕ) :
    Integrable (fun x ↦ ‖iteratedFDeriv ℝ k f x‖) μ := by
  simpa only [pow_zero, one_mul] using f.integrable_pow_mul_norm_iteratedFDeriv (μ := μ) 0 k

omit [BorelSpace E] [SecondCountableTopology E] in
/-- The derivatives of a Schwartz function have integrable envelopes on unit translates: for every
order `n` there is an integrable `ψ` with `‖D^n f (z + h)‖ ≤ ψ z` whenever `‖h‖ ≤ 1`. This is the
domination hypothesis under which a convolution with `f` is differentiated under the integral
(`MeasureTheory.iteratedFDeriv_convolution_left_of_dominated`). -/
theorem exists_integrable_norm_iteratedFDeriv_add_le (f : 𝓢(E, F)) (n : ℕ) :
    ∃ ψ : E → ℝ, Integrable ψ μ ∧
      ∀ z h, ‖h‖ ≤ 1 → ‖iteratedFDeriv ℝ n f (z + h)‖ ≤ ψ z := by
  set p := μ.integrablePower
  set S := (Finset.Iic (p, n)).sup (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) f
  refine ⟨fun z ↦ 2 ^ p * (2 ^ p * S) * (1 + ‖z‖) ^ (-(p : ℝ)),
    (Measure.integrable_pow_neg_integrablePower μ).const_mul _, fun z h hh ↦ ?_⟩
  have hz : 0 < 1 + ‖z‖ := by positivity
  -- Decay at `z + h`, and `1 + ‖z‖ ≤ 2 (1 + ‖z + h‖)` since `‖h‖ ≤ 1`.
  have hdecay := f.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (p, n)) le_rfl le_rfl (z + h)
  have hcomp : 1 + ‖z‖ ≤ 2 * (1 + ‖z + h‖) := by
    linarith [norm_le_add_norm_add z h, norm_nonneg (z + h)]
  dsimp only
  rw [Real.rpow_neg hz.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ‖iteratedFDeriv ℝ n f (z + h)‖ * (1 + ‖z‖) ^ p
      ≤ ‖iteratedFDeriv ℝ n f (z + h)‖ * (2 * (1 + ‖z + h‖)) ^ p := by gcongr
    _ = 2 ^ p * ((1 + ‖z + h‖) ^ p * ‖iteratedFDeriv ℝ n f (z + h)‖) := by rw [mul_pow]; ring
    _ ≤ 2 ^ p * (2 ^ p * S) := by gcongr

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- For a Schwartz function `f` and a continuous linear map `L`, the derivatives of `L ∘ f` are
integrable. -/
theorem integrable_iteratedFDeriv_comp_left (L : F →L[ℝ] G) (f : 𝓢(E, F)) (k : ℕ) :
    Integrable (iteratedFDeriv ℝ k (⇑L ∘ ⇑f)) μ :=
  ((f.integrable_norm_iteratedFDeriv k).const_mul ‖L‖).mono'
    ((L.contDiff.comp (f.smooth ⊤)).continuous_iteratedFDeriv
      (mod_cast le_top)).aestronglyMeasurable
    (.of_forall fun _ ↦ L.norm_iteratedFDeriv_comp_left (f.smooth ⊤).contDiffAt (mod_cast le_top))

omit [SecondCountableTopology E] in
/-- For a Schwartz function `f` and a continuous linear map `L`,
`∫ ‖D^k (L ∘ f)‖ ≤ ‖L‖ ∫ ‖D^k f‖`. -/
theorem integral_norm_iteratedFDeriv_comp_left_le (L : F →L[ℝ] G) (f : 𝓢(E, F)) (k : ℕ) :
    ∫ x, ‖iteratedFDeriv ℝ k (⇑L ∘ ⇑f) x‖ ∂μ ≤ ‖L‖ * ∫ x, ‖iteratedFDeriv ℝ k f x‖ ∂μ := by
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _)
    ((f.integrable_norm_iteratedFDeriv k).const_mul ‖L‖)
    (.of_forall fun _ ↦ L.norm_iteratedFDeriv_comp_left (f.smooth ⊤).contDiffAt (mod_cast le_top))

section Postcomp

variable {𝕜 E F G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜 G]

/-- As a function, the postcomposition of a Schwartz function `f` with a continuous linear map
`L` is the composite `L ∘ f`. -/
@[simp]
theorem coe_postcompCLM (f : 𝓢(E, F)) (L : F →L[𝕜] G) : ⇑(f.postcompCLM L) = L ∘ f := by
  ext x
  rw [postcompCLM_apply, Function.comp_apply]

end Postcomp

open scoped ENNReal in
/-- The closure of the Schwartz functions in `Lᵖ` is the topological closure of the range of the
inclusion `SchwartzMap.toLpCLM`. In particular it is a closed subspace: sums and scalar multiples
of `Lᵖ` limits of Schwartz functions are again such limits. -/
theorem closure_range_toLp_eq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [SecondCountableTopologyEither E F] {μ : Measure E} [μ.HasTemperateGrowth] (p : ℝ≥0∞)
    [Fact (1 ≤ p)] :
    closure (Set.range fun f : 𝓢(E, F) ↦ f.toLp p μ) =
      ((LinearMap.range (toLpCLM ℝ F p μ).toLinearMap).topologicalClosure : Set (Lp F p μ)) := by
  have hcoe : ⇑(toLpCLM ℝ F p μ) = fun f ↦ f.toLp p μ := funext fun _ ↦ toLpCLM_apply
  rw [Submodule.topologicalClosure_coe, LinearMap.coe_range, ContinuousLinearMap.coe_coe, hcoe]

section RealImag

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A complex Schwartz function is its real part plus `I` times its imaginary part, both embedded
back into complex Schwartz space by `Complex.ofRealCLM`. -/
theorem postcompCLM_re_add_I_smul_im (φ : 𝓢(E, ℂ)) :
    (φ.postcompCLM Complex.reCLM).postcompCLM Complex.ofRealCLM +
      Complex.I • (φ.postcompCLM Complex.imCLM).postcompCLM Complex.ofRealCLM = φ := by
  ext x
  simpa [mul_comm] using Complex.re_add_im (φ x)

end RealImag

section BilinLeft

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- **The pointwise product with a decomposed function.** If `A x = ∑ i ∈ s, c i x • L i` for
scalar functions `c i` of temperate growth and operators `L i`, then multiplying a Schwartz
function by `A` is the sum over `i ∈ s` of multiplying it by `c i` and then applying `L i`. -/
theorem bilinLeftCLM_apply_eq_sum {ι : Type*} (s : Finset ι) {c : ι → E → ℂ}
    (hc : ∀ i ∈ s, (c i).HasTemperateGrowth) (L : ι → F →L[ℂ] G) {A : E → F →L[ℂ] G}
    (hA : A.HasTemperateGrowth) (hAs : ∀ x, A x = ∑ i ∈ s, c i x • L i) :
    bilinLeftCLM (ContinuousLinearMap.apply ℂ G) hA =
      ∑ i ∈ s, postcompCLM (L i) ∘L smulLeftCLM F (c i) := by
  ext u x
  simp only [bilinLeftCLM_apply, ContinuousLinearMap.apply_apply, hAs x, sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, postcompCLM_apply]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [smulLeftCLM_apply_apply (hc i hi), map_smul]

end BilinLeft

section Bilin

variable {𝕜 D F G K ι : Type*} [RCLike 𝕜] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜 G] [IsScalarTower ℝ 𝕜 G]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [NormedSpace 𝕜 K] [Fintype ι]

/-- **Expansion of a bilinear multiplier in a basis.** If `gₖ` are the coordinates of `g` in a
basis `bₖ` of `G`, then `B (u x) (g x) = ∑ₖ gₖ x • (B.flip bₖ) (u x)`: the operator
`u ↦ (x ↦ B (u x) (g x))` is a finite sum of scalar multiplications by the `gₖ` after the pointwise
maps `B.flip bₖ`. -/
theorem bilinLeftCLM_eq_sum_smulLeftCLM (b : Module.Basis ι 𝕜 G) (B : F →L[𝕜] G →L[𝕜] K)
    {g : D → G} (hg : g.HasTemperateGrowth) (u : 𝓢(D, F)) :
    bilinLeftCLM B hg u =
      ∑ k, smulLeftCLM K (fun x ↦ b.repr (g x) k) (u.postcompCLM (B.flip (b k))) := by
  ext x
  have hx : B (u x) (g x) = ∑ k, b.repr (g x) k • B (u x) (b k) := by
    conv_lhs => rw [← b.sum_repr (g x)]
    simp only [map_sum, map_smul]
  simp [smulLeftCLM_apply_apply (hg.basis_repr b _), hx]

end Bilin

section Conj

open ComplexConjugate

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pointwise complex conjugation of the values, as a conjugate-linear map on Schwartz space. -/
noncomputable def conjCLM : 𝓢(E, 𝕜) →L⋆[𝕜] 𝓢(E, 𝕜) where
  -- Conjugation is real-linear, and postcomposition with a real-linear map is continuous.
  toFun := postcompCLM (RCLike.conjCLE : 𝕜 ≃L[ℝ] 𝕜).toContinuousLinearMap
  map_add' := map_add _
  map_smul' c f := by
    ext x
    simp
  cont := (postcompCLM (RCLike.conjCLE : 𝕜 ≃L[ℝ] 𝕜).toContinuousLinearMap).continuous

@[simp]
theorem conjCLM_apply (f : 𝓢(E, 𝕜)) (x : E) : conjCLM f x = conj (f x) :=
  (rfl)

/-- Conjugation is antilinear: `conj (c • f) = conj c • conj f`. -/
theorem conjCLM_smul (c : 𝕜) (f : 𝓢(E, 𝕜)) : conjCLM (c • f) = conj c • conjCLM f :=
  map_smulₛₗ conjCLM c f

@[simp]
theorem conjCLM_conjCLM (f : 𝓢(E, 𝕜)) : conjCLM (conjCLM f) = f := by
  ext x
  simp

/-- Reversed conjugation on Schwartz functions, the involution of convolution kernels.
It is conjugate-linear and continuous for the original Schwartz topology. -/
noncomputable def conjnegCLM : 𝓢(E, 𝕜) →L⋆[𝕜] 𝓢(E, 𝕜) :=
  conjCLM.comp (compCLMOfContinuousLinearEquiv 𝕜
    (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv)

/-- Reversed conjugation evaluates to the conjugate at the opposite point. -/
@[simp]
theorem conjnegCLM_apply (f : 𝓢(E, 𝕜)) (x : E) : conjnegCLM f x = conj (f (-x)) := by
  simp [conjnegCLM, conjCLM_apply]

/-- Forgetting the Schwartz structure recovers Mathlib's function-level reversed conjugation. -/
theorem coe_conjnegCLM (f : 𝓢(E, 𝕜)) : ⇑(conjnegCLM f) = conjneg (f : E → 𝕜) := by
  funext x
  exact conjnegCLM_apply f x

/-- Reversed conjugation is an algebraic involution. -/
@[simp]
theorem conjnegCLM_conjnegCLM (f : 𝓢(E, 𝕜)) : conjnegCLM (conjnegCLM f) = f := by
  ext x
  simpa only [conjnegCLM_apply, conjneg_apply] using congrFun (conjneg_conjneg (f : E → 𝕜)) x

open scoped Pointwise in
/-- The support is the reflected support, by Mathlib's function-level support law. -/
theorem support_conjnegCLM (f : 𝓢(E, 𝕜)) :
    Function.support (conjnegCLM f) = -Function.support f := by
  rw [coe_conjnegCLM]
  exact support_conjneg f

/-- Reversal and conjugation preserve a support bound by a ball about zero. -/
theorem support_conjnegCLM_subset_ball {f : 𝓢(E, 𝕜)} {R : ℝ}
    (hf : Function.support f ⊆ Metric.ball 0 R) :
    Function.support (conjnegCLM f) ⊆ Metric.ball 0 R := by
  intro x hx
  have hh : f (-x) ≠ 0 := by
    intro hh
    exact hx (by simp only [conjnegCLM_apply, hh, map_zero])
  simpa only [Metric.mem_ball, dist_zero_right, norm_neg] using hf hh

/-- Reversed conjugation preserves compact support. -/
theorem hasCompactSupport_conjnegCLM {f : 𝓢(E, 𝕜)} (hf : HasCompactSupport f) :
    HasCompactSupport (conjnegCLM f) := by
  have h := (hf.comp_homeomorph (LinearIsometryEquiv.neg ℝ).toHomeomorph).comp_left
    (map_zero (starRingEnd 𝕜))
  convert h using 1
  funext x
  exact conjnegCLM_apply f x

open scoped Topology in
/-- Reversed conjugation preserves the normalization equal to one near the origin. -/
theorem conjnegCLM_eventually_one {f : 𝓢(E, 𝕜)} (hf : ⇑f =ᶠ[𝓝 0] 1) :
    ⇑(conjnegCLM f) =ᶠ[𝓝 0] 1 := by
  have ht : Filter.Tendsto (fun x : E ↦ -x) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using continuous_neg.tendsto (0 : E)
  filter_upwards [ht.eventually hf] with x hx
  simp only [conjnegCLM_apply, hx, Pi.one_apply, map_one]

end Conj

section Polynomial

variable {𝕜 : Type*} [NormedRing 𝕜] [NormedSpace ℝ 𝕜] [Module 𝕜 F] [IsBoundedSMul 𝕜 F]

/-- A scalar Schwartz function times a homogeneous polynomial, `y ↦ K y • A (y, …, y)` for a
continuous multilinear map `A`, is integrable. -/
theorem integrable_smul_apply (K : 𝓢(E, 𝕜)) {n : ℕ} (A : E [×n]→L[ℝ] F) :
    Integrable (fun y ↦ K y • A (fun _ ↦ y)) μ :=
  ((K.integrable_pow_mul μ n).const_mul ‖A‖).mono'
    (K.continuous.smul (A.coe_continuous.comp
      (continuous_pi fun _ ↦ continuous_id))).aestronglyMeasurable
    (.of_forall fun y ↦ (norm_smul_le _ _).trans <| by
      rw [mul_comm, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      simpa using A.le_opNorm (fun _ ↦ y))

end Polynomial

end SchwartzMap

namespace TauCeti

open scoped SchwartzMap

section Smul

open SchwartzMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]

/-- Multiplication by a function which is not of temperate growth is the zero map: Mathlib's
`SchwartzMap.smulLeftCLM` is defined to be `0` there. -/
@[simp]
theorem smulLeftCLM_of_not_hasTemperateGrowth {g : E → 𝕜} (hg : ¬g.HasTemperateGrowth) :
    smulLeftCLM F g = 0 := by
  simp [smulLeftCLM, hg]

/-- Multiplication by a function `g` of temperate growth is the multiplier `bilinLeftCLM` of the
flipped scalar multiplication `(a, c) ↦ c • a`, paired with `g`. -/
theorem smulLeftCLM_eq_bilinLeftCLM {g : E → 𝕜} (hg : g.HasTemperateGrowth) :
    smulLeftCLM F g = bilinLeftCLM (ContinuousLinearMap.lsmul 𝕜 𝕜).flip hg := by
  ext f x
  simp only [smulLeftCLM_apply_apply hg, bilinLeftCLM_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply]

end Smul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsLocallyFiniteMeasure μ]
  [μ.IsOpenPosMeasure]
  {𝕜 V W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace 𝕜 W] [CompleteSpace W]
  [LinearMap.CompatibleSMul V W ℝ 𝕜]

/-- **Operator families are determined by Schwartz test functions.** Two families `K₁`, `K₂`
continuous on an open set `U` agree on `U` if `∫ K₁(y) u(y) ∂μ = ∫ K₂(y) u(y) ∂μ` for every
compactly supported Schwartz function `u` with support in `U`, against a locally finite measure
charging every nonempty open set. -/
theorem _root_.IsOpen.eqOn_of_integral_clm_apply_eq {K₁ K₂ : E → V →L[𝕜] W} {U : Set E}
    (hU : IsOpen U) (hK₁ : ContinuousOn K₁ U) (hK₂ : ContinuousOn K₂ U)
    (h : ∀ u : 𝓢(E, V), HasCompactSupport u → tsupport u ⊆ U →
      ∫ y, K₁ y (u y) ∂μ = ∫ y, K₂ y (u y) ∂μ) :
    Set.EqOn K₁ K₂ U := by
  intro y hy
  ext v
  set f : E → W := fun z ↦ K₁ z v - K₂ z v
  have hf : ContinuousOn f U :=
    (hK₁.clm_apply continuousOn_const).sub (hK₂.clm_apply continuousOn_const)
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hf.locallyIntegrableOn (μ := μ) hU.measurableSet) fun g hg hgs hgU ↦ ?_
  · exact sub_eq_zero.1 (Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).2 hae)
      hU hf continuousOn_const hy)
  -- Test against `z ↦ g(z) • v`, a compactly supported Schwartz function with support in `U`.
  have hgcs : HasCompactSupport fun z ↦ g z • v := hgs.smul_right
  set u := hgcs.toSchwartzMap (hg.smul contDiff_const)
  have huU : tsupport u ⊆ U := (tsupport_smul_subset_left _ _).trans hgU
  have hpt (L : E → V →L[𝕜] W) (z : E) : g z • L z v = L z (u z) := by
    rw [HasCompactSupport.toSchwartzMap_toFun, ContinuousLinearMap.map_smul_of_tower]
  simp only [f, smul_sub, hpt K₁, hpt K₂]
  rw [integral_sub (u.continuous.integrable_clm_apply_of_continuousOn hgcs huU hK₁)
    (u.continuous.integrable_clm_apply_of_continuousOn hgcs huU hK₂), h u hgcs huU, sub_self]

/-- A continuous function `g : E → V →L[𝕜] W` such that `∫ g ζ (f ζ) ∂μ = 0` for every Schwartz
function `f`, against a locally finite measure charging every nonempty open set, vanishes. -/
theorem eq_zero_of_forall_integral_apply_eq_zero {g : E → V →L[𝕜] W} (hg : Continuous g)
    (h : ∀ f : 𝓢(E, V), ∫ ζ, g ζ (f ζ) ∂μ = 0) (ζ : E) : g ζ = 0 :=
  isOpen_univ.eqOn_of_integral_clm_apply_eq (μ := μ) (K₂ := 0) hg.continuousOn continuousOn_const
    (fun f _ _ ↦ by simp [h f]) (Set.mem_univ ζ)

end TauCeti

section CompactSupport

open scoped ENNReal ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [SecondCountableTopologyEither E F]
  {μ : Measure E} [μ.HasTemperateGrowth]

/-- The `Lᵖ` class of a smooth compactly supported function does not depend on whether it is
built through `HasCompactSupport.toSchwartzMap` or from any proof of `Lᵖ` membership. -/
theorem HasCompactSupport.toSchwartzMap_toLp {f : E → F} (hc : HasCompactSupport f)
    (hf : ContDiff ℝ ∞ f) {p : ℝ≥0∞} (h : MemLp f p μ) :
    (hc.toSchwartzMap hf).toLp p μ = h.toLp f :=
  Lp.ext (((hc.toSchwartzMap hf).coeFn_toLp p μ).trans h.coeFn_toLp.symm)

end CompactSupport
