/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.RealMethod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.Normed.Interpolation.Exponent
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Bilinear real interpolation

Let `(A₀, A₁)`, `(B₀, B₁)` and `(C₀, C₁)` be compatible couples, and let `T` be a bilinear map
from `A₀ ∩ A₁` and `B₀ ∩ B₁` to the sum space `C₀ + C₁` with the three endpoint bounds

`T : A₀ × B₀ → C₀`, `T : A₀ × B₁ → C₁`, `T : A₁ × B₀ → C₁`,

of norms `M₀`, `M₁`, `M₁`. No bound is assumed on `A₁ × B₁`. The bilinear real interpolation
theorem (Bergh–Löfström, Exercise 3.13.5(b)) says that for `θ₀, θ₁ > 0` with `θ₀ + θ₁ < 1` and
`1 / p + 1 / q ≥ 1`,

`‖T a b‖_{(C₀, C₁)_{θ₀ + θ₁, 1}} ≤ K ‖a‖_{(A₀, A₁)_{θ₀, p}} ‖b‖_{(B₀, B₁)_{θ₁, q}}`,

with `K` depending only on `θ₀`, `θ₁`, `q`, `M₀` and `M₁`. Keel and Tao use this theorem, with
weighted sequence spaces as the target couple, to sum the dyadic pieces of the bilinear form in
their proof of the endpoint Strichartz estimate.

## Main results

* `TauCeti.CompatibleCouple.kMethodENorm_apply_apply_le`: the estimate for Hölder conjugate `p`
  and `q`, with `K = 48 c_{θ,1} M₀ ^ (1 - θ) M₁ ^ θ (θ₀⁻¹ + θ₁⁻¹) / (log 2)²`, `θ = θ₀ + θ₁`,
  where `c_{θ,1}` is `TauCeti.CompatibleCouple.kMethodConst θ 1`, finite for `0 < θ < 1`.
* `TauCeti.CompatibleCouple.kMethodENorm_apply_apply_le_of_le`: the estimate for every `q` with
  `1 / p + 1 / q ≥ 1`, through the secondary-exponent embedding.

## The argument

Every `a ∈ A₀ ∩ A₁` has a dyadic decomposition `a = ∑ⱼ uⱼ`, `j ∈ ℤ`, in the intersection with
`‖uⱼ‖_{A₀} ≤ 4 K(2 ^ j, a)` and `2 ^ j ‖uⱼ‖_{A₁} ≤ 6 K(2 ^ j, a)`: take near-optimal
decompositions `a = a⁰ⱼ + a¹ⱼ` for `K(2 ^ j, a)`, which lie in the intersection
(`TauCeti.CompatibleCouple.exists_add_eq_and_norm_interFst_add_mul_norm_interSnd_lt`), and put
`uⱼ = a⁰ⱼ - a⁰ⱼ₋₁`. With `b = ∑ₖ vₖ` likewise, the endpoint bounds give

`K(t, T uⱼ vₖ) ≤ C K(s, a) K(r, b) min M₀ (t M₁ min s⁻¹ r⁻¹)`

for `s ∈ [2 ^ j, 2 ^ (j + 1))` and `r ∈ [2 ^ k, 2 ^ (k + 1))`. Integrating against
`t ^ (-θ) dt / t` and summing over the dyadic squares bounds `‖T a b‖_{θ,1}` by a multiple of

`∫∫ f(s) κ(s, r) g(r) ds / s dr / r`, `f(s) = s ^ (-θ₀) K(s, a)`, `g(r) = r ^ (-θ₁) K(r, b)`,

with the kernel `κ(s, r) = s ^ θ₀ r ^ θ₁ min s⁻¹ r⁻¹ ^ (θ₀ + θ₁)`. It depends only on `s / r`
and has integral `θ₀⁻¹ + θ₁⁻¹` in each variable, so Schur's test
(`TauCeti.eLpNorm_lintegral_mul_le`) and Hölder's inequality bound the double integral by
`(θ₀⁻¹ + θ₁⁻¹) ‖f‖_{L^p(ds / s)} ‖g‖_{L^q(dr / r)}`, which are the two `K`-method norms.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §3.13, Exercise 5(b).
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. **120** (1998), 955–980,
  the proof of Theorem 1.2 at the endpoint.
-/

public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace TauCeti

namespace CompatibleCouple

section Dyadic

variable {𝕜 X₀ X₁ V : Type*} [NormedField 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  (C : CompatibleCouple 𝕜 X₀ X₁ V)

/-- Near-optimal decompositions `x = x⁰ⱼ + x¹ⱼ` inside the intersection for `K(2 ^ j, x)` at every
dyadic scale, with `‖x⁰ⱼ‖_{X₀} ≤ 2 K(2 ^ j, x)` and `2 ^ j ‖x¹ⱼ‖_{X₁} ≤ 2 K(2 ^ j, x)`. -/
private theorem exists_dyadic_split (x : C.inter) :
    ∃ d : ℤ → C.inter × C.inter, (∀ j, (d j).1 + (d j).2 = x) ∧
      (∀ j : ℤ, ‖C.interFst (d j).1‖ ≤ 2 * C.kFunctional (2 ^ j) (C.fstToSum (C.interFst x))) ∧
      (∀ j : ℤ, (2 : ℝ) ^ j * ‖C.interSnd (d j).2‖ ≤
        2 * C.kFunctional (2 ^ j) (C.fstToSum (C.interFst x))) := by
  set K : ℝ → ℝ := fun t => C.kFunctional t (C.fstToSum (C.interFst x))
  have hpos (j : ℤ) : (0 : ℝ) < 2 ^ j := zpow_pos two_pos j
  have hK0 (j : ℤ) : 0 ≤ K (2 ^ j) := kFunctional_nonneg (hpos j).le
  have hd (j : ℤ) : ∃ d : C.inter × C.inter, d.1 + d.2 = x ∧
      ‖C.interFst d.1‖ + 2 ^ j * ‖C.interSnd d.2‖ ≤ 2 * K (2 ^ j) := by
    by_cases hx : x = 0
    · exact ⟨(0, 0), by simp [hx], by simpa using mul_nonneg zero_le_two (hK0 j)⟩
    -- `K(2 ^ j, x) > 0`, so a decomposition within a factor `2` of the infimum exists
    have hKpos : 0 < K (2 ^ j) := by
      refine (hK0 j).lt_of_ne fun h => hx ?_
      have h0 := (kFunctional_eq_zero_iff (hpos j)).1 h.symm
      exact C.interFst_injective (C.fstToSum_injective (by simpa using h0))
    obtain ⟨y, z, hyz, hlt⟩ := C.exists_add_eq_and_norm_interFst_add_mul_norm_interSnd_lt
      (hpos j).le x (r := 2 * K (2 ^ j)) (by linarith)
    exact ⟨(y, z), hyz, hlt.le⟩
  choose d hdsum hdle using hd
  refine ⟨d, hdsum, fun j => ?_, fun j => ?_⟩
  · linarith [hdle j, mul_nonneg (hpos j).le (norm_nonneg (C.interSnd (d j).2))]
  · linarith [hdle j, norm_nonneg (C.interFst (d j).1)]

/-- The telescoping sum of `f j - f (j - 1)` over `-N < j ≤ N`, indexed by `i < 2 N` through
`j = i + 1 - N`, is `f N - f (-N)`. -/
private theorem sum_range_sub_sub_one {G : Type*} [AddCommGroup G] (f : ℤ → G) (N : ℕ) :
    ∑ i ∈ Finset.range (2 * N), (f ((i : ℤ) + 1 - N) - f ((i : ℤ) + 1 - N - 1)) =
      f N - f (-N) := by
  have h := Finset.sum_range_sub (fun i : ℕ => f ((i : ℤ) - N)) (2 * N)
  convert h using 2 with i
  · push_cast
    ring_nf
  · push_cast
    ring_nf
  · push_cast
    ring_nf

omit [T1Space V] in
/-- The bounds on one dyadic piece `x⁰ⱼ - x⁰ⱼ₋₁ = x¹ⱼ₋₁ - x¹ⱼ`, from those on the near-optimal
decompositions at the scales `2 ^ j` and `2 ^ (j - 1)` and monotonicity of `K`. -/
private theorem norm_dyadic_piece_le {x : C.inter} {d : ℤ → C.inter × C.inter}
    (hdsum : ∀ j, (d j).1 + (d j).2 = x)
    (hd₁ : ∀ j : ℤ, ‖C.interFst (d j).1‖ ≤ 2 * C.kFunctional (2 ^ j) (C.fstToSum (C.interFst x)))
    (hd₂ : ∀ j : ℤ, (2 : ℝ) ^ j * ‖C.interSnd (d j).2‖ ≤
      2 * C.kFunctional (2 ^ j) (C.fstToSum (C.interFst x))) (j : ℤ) :
    ‖C.interFst ((d j).1 - (d (j - 1)).1)‖ ≤
        4 * C.kFunctional (2 ^ j) (C.fstToSum (C.interFst x)) ∧
      (2 : ℝ) ^ j * ‖C.interSnd ((d j).1 - (d (j - 1)).1)‖ ≤
        6 * C.kFunctional (2 ^ j) (C.fstToSum (C.interFst x)) := by
  have hmono := kFunctional_mono (zpow_pos two_pos (j - 1)).le
    (zpow_le_zpow_right₀ one_le_two (by omega : j - 1 ≤ j)) (C.fstToSum (C.interFst x))
  have hu' : (d j).1 - (d (j - 1)).1 = (d (j - 1)).2 - (d j).2 := by
    rw [sub_eq_sub_iff_add_eq_add, hdsum j, add_comm, hdsum (j - 1)]
  have h2 : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
    rw [← zpow_one_add₀ two_ne_zero]
    ring_nf
  refine ⟨?_, ?_⟩
  · rw [map_sub]
    linarith [norm_sub_le (C.interFst (d j).1) (C.interFst (d (j - 1)).1), hd₁ j, hd₁ (j - 1)]
  · calc (2 : ℝ) ^ j * ‖C.interSnd ((d j).1 - (d (j - 1)).1)‖ ≤
          2 ^ j * (‖C.interSnd (d (j - 1)).2‖ + ‖C.interSnd (d j).2‖) := by
          rw [hu', map_sub]
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (zpow_pos two_pos j).le
      _ = 2 * (2 ^ (j - 1) * ‖C.interSnd (d (j - 1)).2‖) + 2 ^ j * ‖C.interSnd (d j).2‖ := by
          rw [h2]
          ring
      _ ≤ _ := by linarith [hd₂ j, hd₂ (j - 1)]

/-- A dyadic decomposition of an element `x` of the intersection, controlled by its
`K`-functional: `x = ∑ⱼ uⱼ` with `‖uⱼ‖_{X₀} ≤ 4 K(2 ^ j, x)` and `2 ^ j ‖uⱼ‖_{X₁} ≤ 6 K(2 ^ j, x)`.
The partial sums over `-N < j ≤ N` differ from `x` by `y_N + z_N`, where `y_N` is small in `X₀`
and `z_N` is small in `X₁`. The pieces are `uⱼ = x⁰ⱼ - x⁰ⱼ₋₁`, where `x = x⁰ⱼ + x¹ⱼ` is a
near-optimal decomposition for `K(2 ^ j, x)` inside the intersection. -/
private theorem exists_dyadic_decomposition (x : C.inter) :
    ∃ (u : ℤ → C.inter) (y z : ℕ → C.inter),
      (∀ j : ℤ, ‖C.interFst (u j)‖ ≤ 4 * C.kFunctional (2 ^ j) (C.fstToSum (C.interFst x))) ∧
      (∀ j : ℤ, (2 : ℝ) ^ j * ‖C.interSnd (u j)‖ ≤
        6 * C.kFunctional (2 ^ j) (C.fstToSum (C.interFst x))) ∧
      (∀ N : ℕ, ∑ i ∈ Finset.range (2 * N), u ((i : ℤ) + 1 - N) + y N + z N = x) ∧
      (∀ N : ℕ, ‖C.interFst (∑ i ∈ Finset.range (2 * N), u ((i : ℤ) + 1 - N))‖ ≤
        4 * ‖C.interFst x‖) ∧
      (∀ N : ℕ, ‖C.interFst (y N)‖ ≤ 2 * 2⁻¹ ^ N * ‖C.interSnd x‖) ∧
      (∀ N : ℕ, ‖C.interSnd (z N)‖ ≤ 2 * 2⁻¹ ^ N * ‖C.interFst x‖) := by
  obtain ⟨d, hdsum, hd₁, hd₂⟩ := C.exists_dyadic_split x
  set K : ℝ → ℝ := fun t => C.kFunctional t (C.fstToSum (C.interFst x)) with hK_def
  have hKx₀ (j : ℤ) : K (2 ^ j) ≤ ‖C.interFst x‖ := C.kFunctional_fstToSum_le (by positivity) _
  have hKx₁ (j : ℤ) : K (2 ^ j) ≤ 2 ^ j * ‖C.interSnd x‖ := by
    simp only [hK_def, fstToSum_interFst]
    exact C.kFunctional_sndToSum_le (by positivity) _
  have htel (N : ℕ) : ∑ i ∈ Finset.range (2 * N), ((d ((i : ℤ) + 1 - N)).1 -
      (d ((i : ℤ) + 1 - N - 1)).1) = (d N).1 - (d (-N)).1 :=
    sum_range_sub_sub_one (fun j => (d j).1) N
  refine ⟨fun j => (d j).1 - (d (j - 1)).1, fun N => (d (-N)).1, fun N => (d N).2,
    fun j => (C.norm_dyadic_piece_le hdsum hd₁ hd₂ j).1,
    fun j => (C.norm_dyadic_piece_le hdsum hd₁ hd₂ j).2, fun N => ?_, fun N => ?_, fun N => ?_,
    fun N => ?_⟩
  · rw [htel, sub_add_cancel, hdsum]
  · rw [htel, map_sub]
    linarith [norm_sub_le (C.interFst (d N).1) (C.interFst (d (-N)).1), hd₁ N, hd₁ (-N),
      hKx₀ N, hKx₀ (-N)]
  · have h := hKx₁ (-N)
    have h1 := hd₁ (-N)
    rw [zpow_neg, zpow_natCast] at h h1
    calc ‖C.interFst (d (-N)).1‖ ≤ 2 * K ((2 ^ N)⁻¹) := h1
      _ ≤ 2 * ((2 ^ N)⁻¹ * ‖C.interSnd x‖) := by linarith
      _ = 2 * 2⁻¹ ^ N * ‖C.interSnd x‖ := by rw [inv_pow]; ring
  · have h := hd₂ N
    have hN : (0 : ℝ) < 2 ^ N := pow_pos two_pos N
    have h' := hKx₀ N
    rw [zpow_natCast] at h h'
    calc ‖C.interSnd (d N).2‖ ≤ 2 * ‖C.interFst x‖ / 2 ^ N := by
          rw [le_div_iff₀ hN]
          nlinarith
      _ = 2 * 2⁻¹ ^ N * ‖C.interFst x‖ := by rw [inv_pow]; ring

end Dyadic

/-- For `A, B > 0`, `∫ t ^ (-θ) min A (t B) dt / t = A ^ (1 - θ) B ^ θ c_{θ,1}`, by the dilation
`t ↦ (B / A) t`. -/
private theorem lintegral_rpow_neg_mul_min {θ A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∫⁻ t, ENNReal.ofReal (t ^ (-θ) * min A (t * B)) ∂multHaar =
      ENNReal.ofReal (A ^ (1 - θ) * B ^ θ) * kMethodConst θ 1 := by
  set c := B / A with hc_def
  have hc : 0 < c := div_pos hB hA
  have hmp : MeasurePreserving (c * ·) multHaar multHaar :=
    ⟨measurable_const_mul c, map_multHaar_mul_left hc⟩
  have hmeas : Measurable fun t : ℝ => ‖t ^ (-θ) * min 1 t‖ₑ := by fun_prop
  rw [kMethodConst_def, eLpNorm_one_eq_lintegral_enorm
    (by fun_prop : Measurable fun t : ℝ => t ^ (-θ) * min 1 t).aestronglyMeasurable,
    ← hmp.lintegral_comp hmeas,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_pos_multHaar] with t ht
  have hct : 0 < c * t := mul_pos hc ht
  rw [Real.enorm_of_nonneg (mul_nonneg (Real.rpow_nonneg hct.le _) (le_min zero_le_one hct.le)),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hα : 0 < A ^ θ := Real.rpow_pos_of_pos hA θ
  have hβ : 0 < B ^ θ := Real.rpow_pos_of_pos hB θ
  have h1 : A ^ (1 - θ) = A / A ^ θ := by rw [Real.rpow_sub hA, Real.rpow_one]
  have h2 : (c * t) ^ (-θ) = A ^ θ / B ^ θ * t ^ (-θ) := by
    rw [Real.mul_rpow hc.le ht.le, hc_def, Real.rpow_neg (div_pos hB hA).le,
      Real.div_rpow hB.le hA.le, inv_div]
  have h3 : A * min 1 (c * t) = min A (t * B) := by
    rw [mul_min_of_nonneg _ _ hA.le, mul_one, hc_def]
    field_simp
  rw [h1, h2, ← h3]
  field_simp

/-- `∫ u ^ α min 1 u⁻¹ ^ (α + β) du / u = α⁻¹ + β⁻¹` for `α, β > 0`: the integrand is `u ^ α` on
`(0, 1]` and `u ^ (-β)` on `[1, ∞)`. -/
private theorem lintegral_rpow_mul_min_inv_rpow {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫⁻ u, ENNReal.ofReal (u ^ α * min 1 u⁻¹ ^ (α + β)) ∂multHaar =
      ENNReal.ofReal (α⁻¹ + β⁻¹) := by
  have hmeas : Measurable fun u : ℝ => ENNReal.ofReal (u ^ α * min 1 u⁻¹ ^ (α + β)) := by
    fun_prop
  rw [← map_volume_exp, lintegral_map hmeas Real.measurable_exp,
    ← lintegral_add_compl _ (measurableSet_Iic (a := (0 : ℝ))), compl_Iic]
  have hIic : ∫⁻ x in Iic 0, ENNReal.ofReal (Real.exp x ^ α * min 1 (Real.exp x)⁻¹ ^ (α + β)) =
      ENNReal.ofReal α⁻¹ := by
    rw [setLIntegral_congr_fun measurableSet_Iic (g := fun x => ENNReal.ofReal (Real.exp (α * x)))
      fun x (hx : x ≤ 0) => ?_]
    · rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Iic hα 0)
        (ae_of_all _ fun _ => (Real.exp_pos _).le), integral_exp_mul_Iic hα, mul_zero,
        Real.exp_zero, one_div]
    · rw [min_eq_left (one_le_inv_iff₀.2 ⟨Real.exp_pos x, Real.exp_le_one_iff.2 hx⟩),
        Real.one_rpow, mul_one, ← Real.exp_mul, mul_comm]
  have hIoi : ∫⁻ x in Ioi 0, ENNReal.ofReal (Real.exp x ^ α * min 1 (Real.exp x)⁻¹ ^ (α + β)) =
      ENNReal.ofReal β⁻¹ := by
    rw [setLIntegral_congr_fun measurableSet_Ioi
      (g := fun x => ENNReal.ofReal (Real.exp (-β * x))) fun x (hx : 0 < x) => ?_]
    · rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi (neg_lt_zero.2 hβ) 0)
        (ae_of_all _ fun _ => (Real.exp_pos _).le), integral_exp_mul_Ioi (neg_lt_zero.2 hβ),
        mul_zero, Real.exp_zero, neg_div, div_neg, neg_neg, one_div]
    · rw [min_eq_right (inv_le_one_of_one_le₀ (Real.one_le_exp hx.le)), ← Real.exp_neg,
        ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
      congr 2
      ring
  rw [hIic, hIoi, ← ENNReal.ofReal_add (inv_nonneg.2 hα.le) (inv_nonneg.2 hβ.le)]


/-- The dyadic intervals `[2 ^ j, 2 ^ (j + 1))` tile `(0, ∞)²` in pairs: if `G j k ≤ F s r` whenever
`s` lies in the `j`-th and `r` in the `k`-th interval, then
`(log 2)² ∑ⱼ ∑ₖ G j k ≤ ∫∫ F(s, r) ds / s dr / r`. -/
private theorem ofReal_log_two_mul_tsum_tsum_le {G : ℤ → ℤ → ℝ≥0∞} {F : ℝ → ℝ → ℝ≥0∞}
    (h : ∀ j k : ℤ, ∀ s ∈ Ico ((2 : ℝ) ^ j) (2 ^ (j + 1)), ∀ r ∈ Ico ((2 : ℝ) ^ k) (2 ^ (k + 1)),
      G j k ≤ F s r) :
    ENNReal.ofReal (Real.log 2) * (ENNReal.ofReal (Real.log 2) * ∑' j, ∑' k, G j k) ≤
      ∫⁻ s, ∫⁻ r, F s r ∂multHaar ∂multHaar := by
  rw [← ENNReal.tsum_mul_left]
  exact ofReal_log_mul_tsum_le_lintegral_multHaar_zpow one_lt_two fun j s hs =>
    ofReal_log_mul_tsum_le_lintegral_multHaar_zpow one_lt_two fun k r hr => h j k s hs r hr

/-- The kernel `κ(s, r) = s ^ θ₀ r ^ θ₁ min s⁻¹ r⁻¹ ^ (θ₀ + θ₁)` has integral `θ₀⁻¹ + θ₁⁻¹` in `r`
for every `s > 0`: the substitution `r = s u` turns it into `u ^ θ₁ min 1 u⁻¹ ^ (θ₀ + θ₁)`. -/
private theorem lintegral_kernel_right {θ₀ θ₁ s : ℝ} (hθ₀ : 0 < θ₀) (hθ₁ : 0 < θ₁) (hs : 0 < s) :
    ∫⁻ r, ENNReal.ofReal (s ^ θ₀ * r ^ θ₁ * min s⁻¹ r⁻¹ ^ (θ₀ + θ₁)) ∂multHaar =
      ENNReal.ofReal (θ₀⁻¹ + θ₁⁻¹) := by
  have hmp : MeasurePreserving (s * ·) multHaar multHaar :=
    ⟨measurable_const_mul s, map_multHaar_mul_left hs⟩
  rw [← hmp.lintegral_comp (by fun_prop), add_comm θ₀⁻¹, ← lintegral_rpow_mul_min_inv_rpow hθ₁ hθ₀]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_pos_multHaar] with u hu
  congr 1
  have hm : min s⁻¹ (s * u)⁻¹ = s⁻¹ * min 1 u⁻¹ := by
    rw [mul_min_of_nonneg _ _ (inv_nonneg.2 hs.le), mul_one, mul_inv]
  rw [hm, Real.mul_rpow (inv_nonneg.2 hs.le) (le_min zero_le_one (inv_nonneg.2 hu.le)),
    Real.mul_rpow hs.le hu.le, Real.inv_rpow hs.le, add_comm θ₁ θ₀, Real.rpow_add hs]
  field_simp

/-- The kernel `κ(s, r) = s ^ θ₀ r ^ θ₁ min s⁻¹ r⁻¹ ^ (θ₀ + θ₁)` has integral `θ₀⁻¹ + θ₁⁻¹` in `s`
for every `r > 0`: the substitution `s = r u` turns it into `u ^ θ₀ min 1 u⁻¹ ^ (θ₀ + θ₁)`. -/
private theorem lintegral_kernel_left {θ₀ θ₁ r : ℝ} (hθ₀ : 0 < θ₀) (hθ₁ : 0 < θ₁) (hr : 0 < r) :
    ∫⁻ s, ENNReal.ofReal (s ^ θ₀ * r ^ θ₁ * min s⁻¹ r⁻¹ ^ (θ₀ + θ₁)) ∂multHaar =
      ENNReal.ofReal (θ₀⁻¹ + θ₁⁻¹) := by
  have hmp : MeasurePreserving (r * ·) multHaar multHaar :=
    ⟨measurable_const_mul r, map_multHaar_mul_left hr⟩
  rw [← hmp.lintegral_comp (by fun_prop), ← lintegral_rpow_mul_min_inv_rpow hθ₀ hθ₁]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_pos_multHaar] with u hu
  congr 1
  have hm : min (r * u)⁻¹ r⁻¹ = r⁻¹ * min 1 u⁻¹ := by
    rw [mul_min_of_nonneg _ _ (inv_nonneg.2 hr.le), mul_one, mul_inv]
    exact min_comm _ _
  rw [hm, Real.mul_rpow (inv_nonneg.2 hr.le) (le_min zero_le_one (inv_nonneg.2 hu.le)),
    Real.mul_rpow hr.le hu.le, Real.inv_rpow hr.le, Real.rpow_add hr]
  field_simp

/-- **Schur's test and Hölder's inequality** for the kernel
`κ(s, r) = s ^ θ₀ r ^ θ₁ min s⁻¹ r⁻¹ ^ (θ₀ + θ₁)` on `(0, ∞)²` with the measure `ds / s dr / r`:
`∫∫ f(s) κ(s, r) g(r) ≤ (θ₀⁻¹ + θ₁⁻¹) ‖f‖_p ‖g‖_{p'}` for Hölder conjugate `p` and `p'`. -/
private theorem lintegral_lintegral_mul_kernel_mul_le {θ₀ θ₁ : ℝ} (hθ₀ : 0 < θ₀) (hθ₁ : 0 < θ₁)
    {p p' : ℝ≥0∞} [hpp' : p.HolderConjugate p'] {f g : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) :
    ∫⁻ s, ∫⁻ r, f s * (ENNReal.ofReal (s ^ θ₀ * r ^ θ₁ * min s⁻¹ r⁻¹ ^ (θ₀ + θ₁)) * g r)
        ∂multHaar ∂multHaar ≤
      ENNReal.ofReal (θ₀⁻¹ + θ₁⁻¹) * eLpNorm f p multHaar * eLpNorm g p' multHaar := by
  set κ : ℝ → ℝ → ℝ≥0∞ := fun s r => ENNReal.ofReal (s ^ θ₀ * r ^ θ₁ * min s⁻¹ r⁻¹ ^ (θ₀ + θ₁))
  have hκ : Measurable (Function.uncurry κ) := by
    simp only [κ, Function.uncurry_def]
    fun_prop
  set c := ENNReal.ofReal (θ₀⁻¹ + θ₁⁻¹)
  have hc0 : c ≠ 0 := by
    simp only [c, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hrow : ∀ᵐ s ∂multHaar, ∫⁻ r, κ s r ∂multHaar ≤ c := by
    filter_upwards [ae_pos_multHaar] with s hs using (lintegral_kernel_right hθ₀ hθ₁ hs).le
  have hcol : ∀ᵐ r ∂multHaar, ∫⁻ s, κ s r ∂multHaar ≤ c := by
    filter_upwards [ae_pos_multHaar] with r hr using (lintegral_kernel_left hθ₀ hθ₁ hr).le
  have hschur := eLpNorm_lintegral_mul_le hκ.aemeasurable hg.aemeasurable
    (ENNReal.HolderConjugate.one_le (p := p') (q := p)) hrow hcol
  rw [← ENNReal.rpow_add _ _ hc0 ENNReal.ofReal_ne_top, sub_add_cancel, ENNReal.rpow_one] at hschur
  have hκg : Measurable (Function.uncurry fun s r => κ s r * g r) := hκ.mul (hg.comp measurable_snd)
  have hH : Measurable fun s => ∫⁻ r, κ s r * g r ∂multHaar := hκg.lintegral_prod_right'
  calc ∫⁻ s, ∫⁻ r, f s * (κ s r * g r) ∂multHaar ∂multHaar
      = ∫⁻ s, (f * fun s => ∫⁻ r, κ s r * g r ∂multHaar) s ∂multHaar := by
        refine lintegral_congr fun s => ?_
        have hs : Measurable fun r => κ s r * g r := hκg.comp measurable_prodMk_left
        rw [Pi.mul_apply, lintegral_const_mul _ hs]
    _ = eLpNorm (f * fun s => ∫⁻ r, κ s r * g r ∂multHaar) 1 multHaar := by
        rw [eLpNorm_one_eq_lintegral_enorm (hf.mul hH).aestronglyMeasurable]
        simp
    _ ≤ eLpNorm f p multHaar * eLpNorm (fun s => ∫⁻ r, κ s r * g r ∂multHaar) p' multHaar :=
        eLpNorm_le_eLpNorm_mul_eLpNorm_ennreal_of_pos one_pos
    _ ≤ eLpNorm f p multHaar * (c * eLpNorm g p' multHaar) := by gcongr
    _ = c * eLpNorm f p multHaar * eLpNorm g p' multHaar := by ring


section Weighted

variable {𝕜 X₀ X₁ V : Type*} [NormedField 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [ContinuousAdd V]
  {C : CompatibleCouple 𝕜 X₀ X₁ V}

/-- The weighted `K`-functional `s ↦ s ^ (-θ) K(max s 0, x)` is measurable, being a power times a
monotone function, and its `L^p(ds / s)` norm is the `K`-method norm of `x`. -/
private theorem measurable_and_eLpNorm_eq (θ : ℝ) (p : ℝ≥0∞) (x : C.SumSpace) :
    Measurable (fun s : ℝ => ENNReal.ofReal (s ^ (-θ) * C.kFunctional (max s 0) x)) ∧
      eLpNorm (fun s : ℝ => ENNReal.ofReal (s ^ (-θ) * C.kFunctional (max s 0) x)) p multHaar =
        C.kMethodENorm θ p x := by
  have hmono : Monotone fun s : ℝ => C.kFunctional (max s 0) x := fun s s' h =>
    kFunctional_mono (le_max_right _ _) (max_le_max h le_rfl) x
  have hm : Measurable fun s : ℝ => ENNReal.ofReal (s ^ (-θ) * C.kFunctional (max s 0) x) :=
    (((measurable_id (α := ℝ)).pow_const _).mul hmono.measurable).ennreal_ofReal
  refine ⟨hm, ?_⟩
  rw [kMethodENorm_def]
  refine eLpNorm_congr_enorm_ae hm.aestronglyMeasurable
    (aestronglyMeasurable_rpow_neg_mul_kFunctional θ x) ?_
  filter_upwards [ae_pos_multHaar] with s hs
  rw [max_eq_left hs.le, Real.enorm_of_nonneg
    (mul_nonneg (Real.rpow_nonneg hs.le _) (kFunctional_nonneg hs.le)), enorm_eq_self]

end Weighted

section Bilinear

variable {𝕜 X₀ X₁ V Y₀ Y₁ W Z₀ Z₁ U : Type*} [NormedField 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [ContinuousAdd V]
  [NormedAddCommGroup Y₀] [NormedSpace 𝕜 Y₀] [NormedAddCommGroup Y₁] [NormedSpace 𝕜 Y₁]
  [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] [ContinuousAdd W]
  [NormedAddCommGroup Z₀] [NormedSpace 𝕜 Z₀] [NormedAddCommGroup Z₁] [NormedSpace 𝕜 Z₁]
  [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U] [ContinuousAdd U]
  {A : CompatibleCouple 𝕜 X₀ X₁ V} {B : CompatibleCouple 𝕜 Y₀ Y₁ W}
  {C : CompatibleCouple 𝕜 Z₀ Z₁ U} (T : A.inter →ₗ[𝕜] B.inter →ₗ[𝕜] C.SumSpace) {M₀ M₁ : ℝ}

omit [ContinuousAdd V] [ContinuousAdd W] in
/-- The three endpoint bounds of `T`, read through the `K`-functional of `C`. -/
private theorem kFunctional_apply_le
    (h₀₀ : ∀ a b, ∃ z : Z₀, T a b = C.fstToSum z ∧ ‖z‖ ≤ M₀ * ‖A.interFst a‖ * ‖B.interFst b‖)
    (h₀₁ : ∀ a b, ∃ z : Z₁, T a b = C.sndToSum z ∧ ‖z‖ ≤ M₁ * ‖A.interFst a‖ * ‖B.interSnd b‖)
    (h₁₀ : ∀ a b, ∃ z : Z₁, T a b = C.sndToSum z ∧ ‖z‖ ≤ M₁ * ‖A.interSnd a‖ * ‖B.interFst b‖)
    {t : ℝ} (ht : 0 ≤ t) (a : A.inter) (b : B.inter) :
    C.kFunctional t (T a b) ≤ M₀ * ‖A.interFst a‖ * ‖B.interFst b‖ ∧
      C.kFunctional t (T a b) ≤ t * (M₁ * ‖A.interFst a‖ * ‖B.interSnd b‖) ∧
      C.kFunctional t (T a b) ≤ t * (M₁ * ‖A.interSnd a‖ * ‖B.interFst b‖) := by
  obtain ⟨z₀, hz₀, hz₀le⟩ := h₀₀ a b
  obtain ⟨z₁, hz₁, hz₁le⟩ := h₀₁ a b
  obtain ⟨z₂, hz₂, hz₂le⟩ := h₁₀ a b
  refine ⟨?_, ?_, ?_⟩
  · rw [hz₀]
    exact (C.kFunctional_fstToSum_le ht z₀).trans hz₀le
  · rw [hz₁]
    exact (C.kFunctional_sndToSum_le ht z₁).trans (mul_le_mul_of_nonneg_left hz₁le ht)
  · rw [hz₂]
    exact (C.kFunctional_sndToSum_le ht z₂).trans (mul_le_mul_of_nonneg_left hz₂le ht)

variable {T}

/-- A finite double sum over the reindexed blocks `(i + 1 - N, i' + 1 - N)`, `i, i' < 2 N`, is at
most the double series over `ℤ × ℤ`. -/
private theorem sum_sum_le_tsum_tsum (N : ℕ) (c : ℤ → ℤ → ℝ≥0∞) :
    ∑ i ∈ Finset.range (2 * N), ∑ i' ∈ Finset.range (2 * N), c ((i : ℤ) + 1 - N) ((i' : ℤ) + 1 - N)
      ≤ ∑' j, ∑' k, c j k := by
  let e : ℕ ↪ ℤ := ⟨fun i => (i : ℤ) + 1 - N, fun i i' h => by simpa using h⟩
  have h (f : ℤ → ℝ≥0∞) : ∑ i ∈ Finset.range (2 * N), f ((i : ℤ) + 1 - N) ≤ ∑' j, f j := by
    have := Finset.sum_map (Finset.range (2 * N)) e f
    exact this ▸ sum_le_tsum _
  exact (Finset.sum_le_sum fun (i : ℕ) _ => h (c ((i : ℤ) + 1 - N))).trans
    (h fun j => ∑' k, c j k)

omit [ContinuousAdd V] [ContinuousAdd W] in
/-- The remainder terms of the dyadic partial sums: if `‖S‖_{X₀} ≤ 4 ‖a‖_{X₀}`, `y, y'` are
`O(2 ^ (-N))` in the first spaces and `z, z'` in the second spaces, then the `K`-functional at `t`
of `T S y' + T S z' + T y b + T z b` is `O(2 ^ (-N))`. -/
private theorem kFunctional_remainder_le
    (hK : ∀ t, 0 ≤ t → ∀ (a : A.inter) (b : B.inter),
      C.kFunctional t (T a b) ≤ M₀ * ‖A.interFst a‖ * ‖B.interFst b‖ ∧
      C.kFunctional t (T a b) ≤ t * (M₁ * ‖A.interFst a‖ * ‖B.interSnd b‖) ∧
      C.kFunctional t (T a b) ≤ t * (M₁ * ‖A.interSnd a‖ * ‖B.interFst b‖))
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) {t : ℝ} (ht : 0 ≤ t) {N : ℕ} {a S y z : A.inter}
    {b y' z' : B.inter} (hS : ‖A.interFst S‖ ≤ 4 * ‖A.interFst a‖)
    (hy : ‖A.interFst y‖ ≤ 2 * 2⁻¹ ^ N * ‖A.interSnd a‖)
    (hz : ‖A.interSnd z‖ ≤ 2 * 2⁻¹ ^ N * ‖A.interFst a‖)
    (hy' : ‖B.interFst y'‖ ≤ 2 * 2⁻¹ ^ N * ‖B.interSnd b‖)
    (hz' : ‖B.interSnd z'‖ ≤ 2 * 2⁻¹ ^ N * ‖B.interFst b‖) :
    C.kFunctional t (T S y' + T S z' + T y b + T z b) ≤ 2⁻¹ ^ N *
      (8 * M₀ * ‖A.interFst a‖ * ‖B.interSnd b‖ + 10 * t * M₁ * ‖A.interFst a‖ * ‖B.interFst b‖ +
        2 * M₀ * ‖A.interSnd a‖ * ‖B.interFst b‖) := by
  have h2 : (0 : ℝ) ≤ 2⁻¹ ^ N := by positivity
  have e1 := (hK t ht S y').1
  have e2 := (hK t ht S z').2.1
  have e3 := (hK t ht y b).1
  have e4 := (hK t ht z b).2.2
  have f1 : M₀ * ‖A.interFst S‖ * ‖B.interFst y'‖ ≤
      M₀ * (4 * ‖A.interFst a‖) * (2 * 2⁻¹ ^ N * ‖B.interSnd b‖) := by gcongr
  have f2 : t * (M₁ * ‖A.interFst S‖ * ‖B.interSnd z'‖) ≤
      t * (M₁ * (4 * ‖A.interFst a‖) * (2 * 2⁻¹ ^ N * ‖B.interFst b‖)) := by gcongr
  have f3 : M₀ * ‖A.interFst y‖ * ‖B.interFst b‖ ≤
      M₀ * (2 * 2⁻¹ ^ N * ‖A.interSnd a‖) * ‖B.interFst b‖ := by gcongr
  have f4 : t * (M₁ * ‖A.interSnd z‖ * ‖B.interFst b‖) ≤
      t * (M₁ * (2 * 2⁻¹ ^ N * ‖A.interFst a‖) * ‖B.interFst b‖) := by gcongr
  calc _ ≤ C.kFunctional t (T S y') + C.kFunctional t (T S z') +
        C.kFunctional t (T y b) + C.kFunctional t (T z b) := by
        refine (kFunctional_add_le ht _ _).trans ?_
        gcongr
        refine (kFunctional_add_le ht _ _).trans ?_
        gcongr
        exact kFunctional_add_le ht _ _
    _ ≤ _ := by linarith

omit [ContinuousAdd V] [ContinuousAdd W] in
/-- The `K`-functional of `T a b` at `t` is at most the sum over the dyadic pieces of the partial
sums of `a` and `b` up to `N`, plus an `O(2 ^ (-N))` remainder. -/
private theorem kFunctional_le_sum_sum_add
    (hK : ∀ t, 0 ≤ t → ∀ (a : A.inter) (b : B.inter),
      C.kFunctional t (T a b) ≤ M₀ * ‖A.interFst a‖ * ‖B.interFst b‖ ∧
      C.kFunctional t (T a b) ≤ t * (M₁ * ‖A.interFst a‖ * ‖B.interSnd b‖) ∧
      C.kFunctional t (T a b) ≤ t * (M₁ * ‖A.interSnd a‖ * ‖B.interFst b‖))
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) {t : ℝ} (ht : 0 ≤ t) (N : ℕ) {a : A.inter} {b : B.inter}
    {u : ℤ → A.inter} {v : ℤ → B.inter} {y z : A.inter} {y' z' : B.inter}
    (hua : ∑ i ∈ Finset.range (2 * N), u ((i : ℤ) + 1 - N) + y + z = a)
    (hSa : ‖A.interFst (∑ i ∈ Finset.range (2 * N), u ((i : ℤ) + 1 - N))‖ ≤
      4 * ‖A.interFst a‖)
    (hy : ‖A.interFst y‖ ≤ 2 * 2⁻¹ ^ N * ‖A.interSnd a‖)
    (hz : ‖A.interSnd z‖ ≤ 2 * 2⁻¹ ^ N * ‖A.interFst a‖)
    (hvb : ∑ i ∈ Finset.range (2 * N), v ((i : ℤ) + 1 - N) + y' + z' = b)
    (hy' : ‖B.interFst y'‖ ≤ 2 * 2⁻¹ ^ N * ‖B.interSnd b‖)
    (hz' : ‖B.interSnd z'‖ ≤ 2 * 2⁻¹ ^ N * ‖B.interFst b‖) :
    C.kFunctional t (T a b) ≤ ∑ i ∈ Finset.range (2 * N), ∑ i' ∈ Finset.range (2 * N),
        C.kFunctional t (T (u ((i : ℤ) + 1 - N)) (v ((i' : ℤ) + 1 - N))) + 2⁻¹ ^ N *
      (8 * M₀ * ‖A.interFst a‖ * ‖B.interSnd b‖ + 10 * t * M₁ * ‖A.interFst a‖ * ‖B.interFst b‖ +
        2 * M₀ * ‖A.interSnd a‖ * ‖B.interFst b‖) := by
  set Sa := ∑ i ∈ Finset.range (2 * N), u ((i : ℤ) + 1 - N)
  have e1 : T a b = T Sa b + T y b + T z b := by
    conv_lhs => rw [← hua]
    simp only [Sa, map_add, LinearMap.add_apply]
  have e2 : T Sa b = ∑ i ∈ Finset.range (2 * N), ∑ i' ∈ Finset.range (2 * N),
      T (u ((i : ℤ) + 1 - N)) (v ((i' : ℤ) + 1 - N)) + T Sa y' + T Sa z' := by
    conv_lhs => rw [← hvb]
    simp only [Sa, map_add, map_sum, LinearMap.sum_apply]
    rw [Finset.sum_comm]
  have hsplit : T a b = ∑ i ∈ Finset.range (2 * N), ∑ i' ∈ Finset.range (2 * N),
      T (u ((i : ℤ) + 1 - N)) (v ((i' : ℤ) + 1 - N)) + (T Sa y' + T Sa z' + T y b + T z b) := by
    rw [e1, e2]
    abel
  rw [hsplit]
  refine (kFunctional_add_le ht _ _).trans (add_le_add ?_
    (kFunctional_remainder_le hK hM₀ hM₁ ht hSa hy hz hy' hz'))
  exact (kFunctional_sum_le ht _ _).trans (Finset.sum_le_sum fun i _ => kFunctional_sum_le ht _ _)

omit [ContinuousAdd V] [ContinuousAdd W] in
/-- The pointwise step of the bilinear estimate: at each `t > 0`, `t ^ (-θ) K(t, T a b)` is at
most the double series of `t ^ (-θ) K(t, T uⱼ vₖ)` over dyadic decompositions `a = ∑ⱼ uⱼ` and
`b = ∑ₖ vₖ`, since the remainders of the partial sums are `O(2 ^ (-N))`. -/
private theorem ofReal_rpow_mul_kFunctional_le_tsum_tsum (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hK : ∀ t, 0 ≤ t → ∀ (a : A.inter) (b : B.inter),
      C.kFunctional t (T a b) ≤ M₀ * ‖A.interFst a‖ * ‖B.interFst b‖ ∧
      C.kFunctional t (T a b) ≤ t * (M₁ * ‖A.interFst a‖ * ‖B.interSnd b‖) ∧
      C.kFunctional t (T a b) ≤ t * (M₁ * ‖A.interSnd a‖ * ‖B.interFst b‖))
    {θ t : ℝ} (ht : 0 < t) {a : A.inter} {b : B.inter} {u : ℤ → A.inter} {v : ℤ → B.inter}
    {ya za : ℕ → A.inter} {yb zb : ℕ → B.inter}
    (hua : ∀ N : ℕ, ∑ i ∈ Finset.range (2 * N), u ((i : ℤ) + 1 - N) + ya N + za N = a)
    (hSa : ∀ N : ℕ, ‖A.interFst (∑ i ∈ Finset.range (2 * N), u ((i : ℤ) + 1 - N))‖ ≤
      4 * ‖A.interFst a‖)
    (hya : ∀ N : ℕ, ‖A.interFst (ya N)‖ ≤ 2 * 2⁻¹ ^ N * ‖A.interSnd a‖)
    (hza : ∀ N : ℕ, ‖A.interSnd (za N)‖ ≤ 2 * 2⁻¹ ^ N * ‖A.interFst a‖)
    (hvb : ∀ N : ℕ, ∑ i ∈ Finset.range (2 * N), v ((i : ℤ) + 1 - N) + yb N + zb N = b)
    (hyb : ∀ N : ℕ, ‖B.interFst (yb N)‖ ≤ 2 * 2⁻¹ ^ N * ‖B.interSnd b‖)
    (hzb : ∀ N : ℕ, ‖B.interSnd (zb N)‖ ≤ 2 * 2⁻¹ ^ N * ‖B.interFst b‖) :
    ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T a b)) ≤
      ∑' j, ∑' k, ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T (u j) (v k))) := by
  set R := 8 * M₀ * ‖A.interFst a‖ * ‖B.interSnd b‖ +
    10 * t * M₁ * ‖A.interFst a‖ * ‖B.interFst b‖ + 2 * M₀ * ‖A.interSnd a‖ * ‖B.interFst b‖
  set Q := t ^ (-θ) * R
  have hQ : 0 ≤ Q := by positivity
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (div_pos (NNReal.coe_pos.2 hε) (by positivity : (0 : ℝ) < Q + 1)) (by norm_num : (2⁻¹ : ℝ) < 1)
  have hNε : 2⁻¹ ^ N * Q < (ε : ℝ) := by
    rw [lt_div_iff₀ (by positivity)] at hN
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) N]
  have hreal : t ^ (-θ) * C.kFunctional t (T a b) ≤
      ∑ i ∈ Finset.range (2 * N), ∑ i' ∈ Finset.range (2 * N),
        t ^ (-θ) * C.kFunctional t (T (u ((i : ℤ) + 1 - N)) (v ((i' : ℤ) + 1 - N))) +
        2⁻¹ ^ N * Q := by
    simp only [← Finset.mul_sum]
    rw [show 2⁻¹ ^ N * Q = t ^ (-θ) * (2⁻¹ ^ N * R) by ring, ← mul_add]
    exact mul_le_mul_of_nonneg_left (kFunctional_le_sum_sum_add hK hM₀ hM₁ ht.le N (hua N)
      (hSa N) (hya N) (hza N) (hvb N) (hyb N) (hzb N)) (Real.rpow_nonneg ht.le _)
  have hnn (j k : ℤ) : 0 ≤ t ^ (-θ) * C.kFunctional t (T (u j) (v k)) :=
    mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le)
  calc ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T a b))
      ≤ ∑ i ∈ Finset.range (2 * N), ∑ i' ∈ Finset.range (2 * N),
          ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T (u ((i : ℤ) + 1 - N))
            (v ((i' : ℤ) + 1 - N)))) + ENNReal.ofReal (2⁻¹ ^ N * Q) := by
        refine (ENNReal.ofReal_le_ofReal hreal).trans_eq ?_
        rw [ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun i' _ =>
          hnn _ _) (by positivity), ENNReal.ofReal_sum_of_nonneg fun i _ =>
          Finset.sum_nonneg fun i' _ => hnn _ _]
        congr 1
        exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_sum_of_nonneg fun i' _ => hnn _ _
    _ ≤ ∑' j, ∑' k, ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T (u j) (v k))) + ε := by
        gcongr
        · exact sum_sum_le_tsum_tsum N fun j k =>
            ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T (u j) (v k)))
        · rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top]
          exact hNε.le

omit [ContinuousAdd V] [ContinuousAdd W] in
/-- The contribution of one pair of dyadic pieces. If `‖u‖_{X₀} ≤ 4 α`, `s ‖u‖_{X₁} ≤ 12 α`,
`‖v‖_{Y₀} ≤ 4 β` and `r ‖v‖_{Y₁} ≤ 12 β`, then
`K(t, T u v) ≤ 48 α β min M₀ (t M₁ min s⁻¹ r⁻¹)`, and integrating against `t ^ (-θ) dt / t` gives
`48 α β M₀ ^ (1 - θ) (M₁ min s⁻¹ r⁻¹) ^ θ c_{θ,1}`. -/
private theorem lintegral_rpow_mul_kFunctional_le (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hK : ∀ t, 0 ≤ t → ∀ (a : A.inter) (b : B.inter),
      C.kFunctional t (T a b) ≤ M₀ * ‖A.interFst a‖ * ‖B.interFst b‖ ∧
      C.kFunctional t (T a b) ≤ t * (M₁ * ‖A.interFst a‖ * ‖B.interSnd b‖) ∧
      C.kFunctional t (T a b) ≤ t * (M₁ * ‖A.interSnd a‖ * ‖B.interFst b‖))
    (θ : ℝ) {u : A.inter} {v : B.inter} {α β s r : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : 0 < s)
    (hr : 0 < r) (hu₀ : ‖A.interFst u‖ ≤ 4 * α) (hu₁ : s * ‖A.interSnd u‖ ≤ 12 * α)
    (hv₀ : ‖B.interFst v‖ ≤ 4 * β) (hv₁ : r * ‖B.interSnd v‖ ≤ 12 * β) :
    ∫⁻ t, ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T u v)) ∂multHaar ≤
      ENNReal.ofReal (48 * α * β * (M₀ ^ (1 - θ) * (M₁ * min s⁻¹ r⁻¹) ^ θ)) *
        kMethodConst θ 1 := by
  set c := M₁ * min s⁻¹ r⁻¹ with hc_def
  have hc : 0 < c := mul_pos hM₁ (lt_min (inv_pos.2 hs) (inv_pos.2 hr))
  have h48 : 0 ≤ 48 * α * β := by positivity
  have hu₁' : ‖A.interSnd u‖ ≤ 12 * α * s⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hs]
    linarith
  have hv₁' : ‖B.interSnd v‖ ≤ 12 * β * r⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hr]
    linarith
  have hpt : ∀ t, 0 < t → C.kFunctional t (T u v) ≤ 48 * α * β * min M₀ (t * c) := by
    intro t ht
    obtain ⟨e₀, e₁, e₂⟩ := hK t ht.le u v
    rw [hc_def, ← mul_assoc, mul_min_of_nonneg _ _ (mul_nonneg ht.le hM₁.le),
      mul_min_of_nonneg _ _ h48, mul_min_of_nonneg _ _ h48]
    refine le_min ?_ (le_min ?_ ?_)
    · calc _ ≤ M₀ * (4 * α) * (4 * β) := e₀.trans (by gcongr)
        _ ≤ 48 * α * β * M₀ := by nlinarith [mul_nonneg (mul_nonneg hα hβ) hM₀.le]
    · calc _ ≤ t * (M₁ * (12 * α * s⁻¹) * (4 * β)) := e₂.trans (by gcongr)
        _ = 48 * α * β * (t * M₁ * s⁻¹) := by ring
    · calc _ ≤ t * (M₁ * (4 * α) * (12 * β * r⁻¹)) := e₁.trans (by gcongr)
        _ = 48 * α * β * (t * M₁ * r⁻¹) := by ring
  calc ∫⁻ t, ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T u v)) ∂multHaar
      ≤ ∫⁻ t, ENNReal.ofReal (48 * α * β) * ENNReal.ofReal (t ^ (-θ) * min M₀ (t * c))
          ∂multHaar := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_pos_multHaar] with t ht
        rw [← ENNReal.ofReal_mul h48]
        refine ENNReal.ofReal_le_ofReal ?_
        calc t ^ (-θ) * C.kFunctional t (T u v) ≤ t ^ (-θ) * (48 * α * β * min M₀ (t * c)) :=
              mul_le_mul_of_nonneg_left (hpt t ht) (Real.rpow_nonneg ht.le _)
          _ = 48 * α * β * (t ^ (-θ) * min M₀ (t * c)) := by ring
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_rpow_neg_mul_min hM₀ hc,
          ← mul_assoc, ← ENNReal.ofReal_mul h48]


omit [ContinuousAdd V] [ContinuousAdd W] in
/-- The `K`-method norm of exponent `1` of `T a b` is at most the double series over the dyadic
pieces of `a` and `b`. -/
private theorem kMethodENorm_le_tsum_tsum_lintegral (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hK : ∀ t, 0 ≤ t → ∀ (a : A.inter) (b : B.inter),
      C.kFunctional t (T a b) ≤ M₀ * ‖A.interFst a‖ * ‖B.interFst b‖ ∧
      C.kFunctional t (T a b) ≤ t * (M₁ * ‖A.interFst a‖ * ‖B.interSnd b‖) ∧
      C.kFunctional t (T a b) ≤ t * (M₁ * ‖A.interSnd a‖ * ‖B.interFst b‖))
    (θ : ℝ) {a : A.inter} {b : B.inter} {u : ℤ → A.inter} {v : ℤ → B.inter}
    {ya za : ℕ → A.inter} {yb zb : ℕ → B.inter}
    (hua : ∀ N : ℕ, ∑ i ∈ Finset.range (2 * N), u ((i : ℤ) + 1 - N) + ya N + za N = a)
    (hSa : ∀ N : ℕ, ‖A.interFst (∑ i ∈ Finset.range (2 * N), u ((i : ℤ) + 1 - N))‖ ≤
      4 * ‖A.interFst a‖)
    (hya : ∀ N : ℕ, ‖A.interFst (ya N)‖ ≤ 2 * 2⁻¹ ^ N * ‖A.interSnd a‖)
    (hza : ∀ N : ℕ, ‖A.interSnd (za N)‖ ≤ 2 * 2⁻¹ ^ N * ‖A.interFst a‖)
    (hvb : ∀ N : ℕ, ∑ i ∈ Finset.range (2 * N), v ((i : ℤ) + 1 - N) + yb N + zb N = b)
    (hyb : ∀ N : ℕ, ‖B.interFst (yb N)‖ ≤ 2 * 2⁻¹ ^ N * ‖B.interSnd b‖)
    (hzb : ∀ N : ℕ, ‖B.interSnd (zb N)‖ ≤ 2 * 2⁻¹ ^ N * ‖B.interFst b‖) :
    C.kMethodENorm θ 1 (T a b) ≤
      ∑' j, ∑' k, ∫⁻ t, ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T (u j) (v k))) ∂multHaar := by
  have hmeas (c : C.SumSpace) :
      AEMeasurable (fun t => ENNReal.ofReal (t ^ (-θ) * C.kFunctional t c)) multHaar :=
    (aestronglyMeasurable_rpow_neg_mul_kFunctional θ c).aemeasurable.ennreal_ofReal
  rw [kMethodENorm_def, eLpNorm_one_eq_lintegral_enorm
    (aestronglyMeasurable_rpow_neg_mul_kFunctional θ _)]
  calc ∫⁻ t, ‖t ^ (-θ) * C.kFunctional t (T a b)‖ₑ ∂multHaar
      ≤ ∫⁻ t, ∑' j, ∑' k, ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T (u j) (v k)))
          ∂multHaar := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_pos_multHaar] with t ht
        rw [Real.enorm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le))]
        exact ofReal_rpow_mul_kFunctional_le_tsum_tsum hM₀ hM₁ hK ht hua hSa hya hza hvb hyb hzb
    _ = _ := by
        rw [lintegral_tsum fun j => AEMeasurable.tsum fun k => hmeas _]
        exact tsum_congr fun j => lintegral_tsum fun k => hmeas _

/-- The contribution of the dyadic pieces `u` and `v` at scales `2 ^ j` and `2 ^ k` is controlled
by the integrand `f(s) κ(s, r) g(r)` of the final double integral at every point `(s, r)` of the
dyadic square `[2 ^ j, 2 ^ (j + 1)) × [2 ^ k, 2 ^ (k + 1))`. -/
private theorem lintegral_le_mul_kernel_of_mem_Ico (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hK : ∀ t, 0 ≤ t → ∀ (a : A.inter) (b : B.inter),
      C.kFunctional t (T a b) ≤ M₀ * ‖A.interFst a‖ * ‖B.interFst b‖ ∧
      C.kFunctional t (T a b) ≤ t * (M₁ * ‖A.interFst a‖ * ‖B.interSnd b‖) ∧
      C.kFunctional t (T a b) ≤ t * (M₁ * ‖A.interSnd a‖ * ‖B.interFst b‖))
    {θ₀ θ₁ : ℝ} {a' : A.SumSpace} {b' : B.SumSpace} {u : A.inter} {v : B.inter} {j k : ℤ}
    (hu₀ : ‖A.interFst u‖ ≤ 4 * A.kFunctional (2 ^ j) a')
    (hu₁ : (2 : ℝ) ^ j * ‖A.interSnd u‖ ≤ 6 * A.kFunctional (2 ^ j) a')
    (hv₀ : ‖B.interFst v‖ ≤ 4 * B.kFunctional (2 ^ k) b')
    (hv₁ : (2 : ℝ) ^ k * ‖B.interSnd v‖ ≤ 6 * B.kFunctional (2 ^ k) b') {s r : ℝ}
    (hs : s ∈ Ico ((2 : ℝ) ^ j) (2 ^ (j + 1))) (hr : r ∈ Ico ((2 : ℝ) ^ k) (2 ^ (k + 1))) :
    ∫⁻ t, ENNReal.ofReal (t ^ (-(θ₀ + θ₁)) * C.kFunctional t (T u v)) ∂multHaar ≤
      48 * kMethodConst (θ₀ + θ₁) 1 *
        ENNReal.ofReal (M₀ ^ (1 - (θ₀ + θ₁)) * M₁ ^ (θ₀ + θ₁)) *
        (ENNReal.ofReal (s ^ (-θ₀) * A.kFunctional (max s 0) a') *
          (ENNReal.ofReal (s ^ θ₀ * r ^ θ₁ * min s⁻¹ r⁻¹ ^ (θ₀ + θ₁)) *
            ENNReal.ofReal (r ^ (-θ₁) * B.kFunctional (max r 0) b'))) := by
  set θ := θ₀ + θ₁
  have hs0 : 0 < s := (zpow_pos two_pos j).trans_le hs.1
  have hr0 : 0 < r := (zpow_pos two_pos k).trans_le hr.1
  have hα := kFunctional_nonneg (C := A) (u := a') hs0.le
  have hβ := kFunctional_nonneg (C := B) (u := b') hr0.le
  have hKa := kFunctional_mono (zpow_pos two_pos j).le hs.1 a'
  have hKb := kFunctional_mono (zpow_pos two_pos k).le hr.1 b'
  have hs2 : s * ‖A.interSnd u‖ ≤ 2 * (2 ^ j * ‖A.interSnd u‖) := by
    rw [← mul_assoc, ← zpow_one_add₀ two_ne_zero, add_comm]
    exact mul_le_mul_of_nonneg_right hs.2.le (norm_nonneg _)
  have hr2 : r * ‖B.interSnd v‖ ≤ 2 * (2 ^ k * ‖B.interSnd v‖) := by
    rw [← mul_assoc, ← zpow_one_add₀ two_ne_zero, add_comm]
    exact mul_le_mul_of_nonneg_right hr.2.le (norm_nonneg _)
  refine (lintegral_rpow_mul_kFunctional_le hM₀ hM₁ hK θ hα hβ hs0 hr0 (hu₀.trans
    (by linarith)) (hs2.trans (by linarith [hu₁])) (hv₀.trans (by linarith))
    (hr2.trans (by linarith [hv₁]))).trans_eq ?_
  have hm0 : 0 ≤ min s⁻¹ r⁻¹ := le_min (inv_nonneg.2 hs0.le) (inv_nonneg.2 hr0.le)
  have e : 48 * A.kFunctional s a' * B.kFunctional r b' * (M₀ ^ (1 - θ) * (M₁ * min s⁻¹ r⁻¹) ^ θ)
      = 48 * (M₀ ^ (1 - θ) * M₁ ^ θ) * (s ^ (-θ₀) * A.kFunctional s a' *
        (s ^ θ₀ * r ^ θ₁ * min s⁻¹ r⁻¹ ^ θ * (r ^ (-θ₁) * B.kFunctional r b'))) := by
    rw [Real.mul_rpow hM₁.le hm0, Real.rpow_neg hs0.le, Real.rpow_neg hr0.le]
    have := (Real.rpow_pos_of_pos hs0 θ₀).ne'
    have := (Real.rpow_pos_of_pos hr0 θ₁).ne'
    field_simp
  simp only [max_eq_left hs0.le, max_eq_left hr0.le]
  have hP : 0 ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by positivity
  have hκ0 : 0 ≤ s ^ θ₀ * r ^ θ₁ * min s⁻¹ r⁻¹ ^ θ :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg hr0.le _))
      (Real.rpow_nonneg hm0 _)
  rw [e, ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 48) hP),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 48),
    ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hs0.le _) hα), ENNReal.ofReal_mul hκ0,
    ENNReal.ofReal_ofNat]
  ring

/-- **Bilinear real interpolation** (Bergh–Löfström, §3.13, Exercise 5(b)). Let `T`
be a bilinear map from the intersections `A₀ ∩ A₁` and `B₀ ∩ B₁` of two compatible couples to the
sum space of a third couple `(C₀, C₁)`, with the three endpoint bounds

* `‖T a b‖_{C₀} ≤ M₀ ‖a‖_{A₀} ‖b‖_{B₀}`,
* `‖T a b‖_{C₁} ≤ M₁ ‖a‖_{A₀} ‖b‖_{B₁}`,
* `‖T a b‖_{C₁} ≤ M₁ ‖a‖_{A₁} ‖b‖_{B₀}`.

Then for `θ₀, θ₁ > 0` and Hölder conjugate exponents `p` and `p'`,

`‖T a b‖_{(C₀, C₁)_{θ₀ + θ₁, 1}} ≤ K ‖a‖_{(A₀, A₁)_{θ₀, p}} ‖b‖_{(B₀, B₁)_{θ₁, p'}}`

with `K = 48 c_{θ,1} M₀ ^ (1 - θ) M₁ ^ θ (θ₀⁻¹ + θ₁⁻¹) / (log 2)²`, `θ = θ₀ + θ₁`, where
`c_{θ,1} = kMethodConst θ 1` is finite when `θ < 1` (`kMethodConst_lt_top`); for `θ ≥ 1` the
bound is vacuous. No bound on `A₁ × B₁` is assumed, and the target carries the smallest secondary
exponent `1`. This is the interpolation step of Keel and Tao's proof of the endpoint Strichartz
estimate.

The proof decomposes `a = ∑ⱼ uⱼ` and `b = ∑ₖ vₖ` dyadically in the intersections, with
`uⱼ` controlled by `K(2 ^ j, a)`, bounds `K(t, T uⱼ vₖ)` by the endpoint estimates, compares the
resulting double series with a double integral against `ds / s dr / r`, and concludes by Schur's
test and Hölder's inequality for the kernel `s ^ θ₀ r ^ θ₁ min s⁻¹ r⁻¹ ^ θ`, a convolution
kernel on the multiplicative group with integral `θ₀⁻¹ + θ₁⁻¹`. -/
theorem kMethodENorm_apply_apply_le [T1Space V] [T1Space W]
    (T : A.inter →ₗ[𝕜] B.inter →ₗ[𝕜] C.SumSpace) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀₀ : ∀ a b, ∃ z : Z₀, T a b = C.fstToSum z ∧ ‖z‖ ≤ M₀ * ‖A.interFst a‖ * ‖B.interFst b‖)
    (h₀₁ : ∀ a b, ∃ z : Z₁, T a b = C.sndToSum z ∧ ‖z‖ ≤ M₁ * ‖A.interFst a‖ * ‖B.interSnd b‖)
    (h₁₀ : ∀ a b, ∃ z : Z₁, T a b = C.sndToSum z ∧ ‖z‖ ≤ M₁ * ‖A.interSnd a‖ * ‖B.interFst b‖)
    {θ₀ θ₁ : ℝ} (hθ₀ : 0 < θ₀) (hθ₁ : 0 < θ₁) {p p' : ℝ≥0∞} [p.HolderConjugate p']
    (a : A.inter) (b : B.inter) :
    C.kMethodENorm (θ₀ + θ₁) 1 (T a b) ≤
      48 * kMethodConst (θ₀ + θ₁) 1 *
        ENNReal.ofReal (M₀ ^ (1 - (θ₀ + θ₁)) * M₁ ^ (θ₀ + θ₁) * (θ₀⁻¹ + θ₁⁻¹) / Real.log 2 ^ 2) *
        A.kMethodENorm θ₀ p (A.fstToSum (A.interFst a)) *
        B.kMethodENorm θ₁ p' (B.fstToSum (B.interFst b)) := by
  -- dyadic decompositions of `a` and `b`, and the integrands `f`, `κ`, `g` of the final bound
  obtain ⟨u, ya, za, hu₀, hu₁, hua, hSa, hya, hza⟩ := A.exists_dyadic_decomposition a
  obtain ⟨v, yb, zb, hv₀, hv₁, hvb, -, hyb, hzb⟩ := B.exists_dyadic_decomposition b
  have hK := fun t (ht : 0 ≤ t) => kFunctional_apply_le T h₀₀ h₀₁ h₁₀ ht
  set θ := θ₀ + θ₁
  set a' := A.fstToSum (A.interFst a)
  set b' := B.fstToSum (B.interFst b)
  set f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (-θ₀) * A.kFunctional (max s 0) a')
  set g : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (r ^ (-θ₁) * B.kFunctional (max r 0) b')
  set κ : ℝ → ℝ → ℝ≥0∞ := fun s r => ENNReal.ofReal (s ^ θ₀ * r ^ θ₁ * min s⁻¹ r⁻¹ ^ θ)
  obtain ⟨hf, hfn⟩ := measurable_and_eLpNorm_eq θ₀ p a'
  obtain ⟨hg, hgn⟩ := measurable_and_eLpNorm_eq θ₁ p' b'
  set Cst := 48 * kMethodConst θ 1 * ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ)
  set L := ENNReal.ofReal (Real.log 2)
  have hL : L ≠ 0 := by simp [L, Real.log_pos one_lt_two]
  -- the double series over dyadic pieces, the double integral, then Schur and Hölder
  have hmain : L * (L * C.kMethodENorm θ 1 (T a b)) ≤
      Cst * (ENNReal.ofReal (θ₀⁻¹ + θ₁⁻¹) * eLpNorm f p multHaar * eLpNorm g p' multHaar) := by
    have hκ : Measurable (Function.uncurry κ) := by
      simp only [κ, Function.uncurry_def]
      fun_prop
    have hF : Measurable (Function.uncurry fun s r => f s * (κ s r * g r)) :=
      (hf.comp measurable_fst).mul (hκ.mul (hg.comp measurable_snd))
    calc L * (L * C.kMethodENorm θ 1 (T a b))
        ≤ L * (L * ∑' j, ∑' k,
            ∫⁻ t, ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T (u j) (v k))) ∂multHaar) := by
          gcongr
          exact kMethodENorm_le_tsum_tsum_lintegral hM₀.le hM₁.le hK θ hua hSa hya hza hvb hyb hzb
      _ ≤ ∫⁻ s, ∫⁻ r, Cst * (f s * (κ s r * g r)) ∂multHaar ∂multHaar :=
          ofReal_log_two_mul_tsum_tsum_le fun j k s hs r hr =>
            lintegral_le_mul_kernel_of_mem_Ico hM₀ hM₁ hK (hu₀ j) (hu₁ j) (hv₀ k) (hv₁ k) hs hr
      _ = Cst * ∫⁻ s, ∫⁻ r, f s * (κ s r * g r) ∂multHaar ∂multHaar := by
          have hmeas : Measurable fun s => ∫⁻ r, f s * (κ s r * g r) ∂multHaar :=
            hF.lintegral_prod_right'
          rw [← lintegral_const_mul _ hmeas]
          exact lintegral_congr fun s => lintegral_const_mul _ (hF.comp measurable_prodMk_left)
      _ ≤ _ := by
          gcongr
          exact lintegral_lintegral_mul_kernel_mul_le hθ₀ hθ₁ hf hg
  -- divide by `(log 2)²` and identify the two `L^p(dt / t)` norms as `K`-method norms
  calc C.kMethodENorm θ 1 (T a b) = L⁻¹ * (L⁻¹ * (L * (L * C.kMethodENorm θ 1 (T a b)))) := by
        rw [← mul_assoc L⁻¹ L, ENNReal.inv_mul_cancel hL ENNReal.ofReal_ne_top, one_mul,
          ← mul_assoc, ENNReal.inv_mul_cancel hL ENNReal.ofReal_ne_top, one_mul]
    _ ≤ L⁻¹ * (L⁻¹ * (Cst *
          (ENNReal.ofReal (θ₀⁻¹ + θ₁⁻¹) * eLpNorm f p multHaar * eLpNorm g p' multHaar))) := by
        gcongr
    _ = _ := by
        have hlog := Real.log_pos one_lt_two
        rw [hfn, hgn, ENNReal.ofReal_div_of_pos (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hlog.le, div_eq_mul_inv,
          ENNReal.inv_pow]
        simp only [Cst, L]
        ring

/-- **Bilinear real interpolation** for secondary exponents with `1 / p + 1 / q ≥ 1`, that is
`q ≤ p'` for the exponent `p'` conjugate to `p`: under the hypotheses of
`kMethodENorm_apply_apply_le`,
`‖T a b‖_{(C₀, C₁)_{θ₀ + θ₁, 1}} ≤ K' ‖a‖_{(A₀, A₁)_{θ₀, p}} ‖b‖_{(B₀, B₁)_{θ₁, q}}`
with `K' = K max 1 c_{θ₁,q}⁻¹`.
This is the form stated by Bergh–Löfström and Keel–Tao; it follows from the conjugate case by the
secondary-exponent embedding `(B₀, B₁)_{θ₁, q} ⊆ (B₀, B₁)_{θ₁, p'}`. -/
theorem kMethodENorm_apply_apply_le_of_le [T1Space V] [T1Space W]
    (T : A.inter →ₗ[𝕜] B.inter →ₗ[𝕜] C.SumSpace) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀₀ : ∀ a b, ∃ z : Z₀, T a b = C.fstToSum z ∧ ‖z‖ ≤ M₀ * ‖A.interFst a‖ * ‖B.interFst b‖)
    (h₀₁ : ∀ a b, ∃ z : Z₁, T a b = C.sndToSum z ∧ ‖z‖ ≤ M₁ * ‖A.interFst a‖ * ‖B.interSnd b‖)
    (h₁₀ : ∀ a b, ∃ z : Z₁, T a b = C.sndToSum z ∧ ‖z‖ ≤ M₁ * ‖A.interSnd a‖ * ‖B.interFst b‖)
    {θ₀ θ₁ : ℝ} (hθ₀ : 0 < θ₀) (hθ₁ : 0 < θ₁) {p p' q : ℝ≥0∞} [p.HolderConjugate p']
    [Fact (1 ≤ q)] (hq : q ≤ p') (a : A.inter) (b : B.inter) :
    C.kMethodENorm (θ₀ + θ₁) 1 (T a b) ≤
      48 * kMethodConst (θ₀ + θ₁) 1 *
        ENNReal.ofReal (M₀ ^ (1 - (θ₀ + θ₁)) * M₁ ^ (θ₀ + θ₁) * (θ₀⁻¹ + θ₁⁻¹) / Real.log 2 ^ 2) *
        ENNReal.ofReal (max 1 (kMethodConst θ₁ q).toReal⁻¹) *
        A.kMethodENorm θ₀ p (A.fstToSum (A.interFst a)) *
        B.kMethodENorm θ₁ q (B.fstToSum (B.interFst b)) := by
  calc C.kMethodENorm (θ₀ + θ₁) 1 (T a b)
      ≤ 48 * kMethodConst (θ₀ + θ₁) 1 *
          ENNReal.ofReal (M₀ ^ (1 - (θ₀ + θ₁)) * M₁ ^ (θ₀ + θ₁) * (θ₀⁻¹ + θ₁⁻¹) / Real.log 2 ^ 2) *
          A.kMethodENorm θ₀ p (A.fstToSum (A.interFst a)) *
          B.kMethodENorm θ₁ p' (B.fstToSum (B.interFst b)) :=
        kMethodENorm_apply_apply_le T hM₀ hM₁ h₀₀ h₀₁ h₁₀ hθ₀ hθ₁ a b
    _ ≤ 48 * kMethodConst (θ₀ + θ₁) 1 *
          ENNReal.ofReal (M₀ ^ (1 - (θ₀ + θ₁)) * M₁ ^ (θ₀ + θ₁) * (θ₀⁻¹ + θ₁⁻¹) / Real.log 2 ^ 2) *
          A.kMethodENorm θ₀ p (A.fstToSum (A.interFst a)) *
          (ENNReal.ofReal (max 1 (kMethodConst θ₁ q).toReal⁻¹) *
            B.kMethodENorm θ₁ q (B.fstToSum (B.interFst b))) := by
        gcongr
        exact kMethodENorm_le_ofReal_mul_kMethodENorm hq _
    _ = _ := by ring

end Bilinear

end CompatibleCouple

end TauCeti
