/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Basic
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Localization of the Sobolev wave front set

A complex distribution `T` is microlocally `H^s` at `(x, ξ)` if *one* cutoff `φ` with `φ x ≠ 0`
makes the weighted localized Fourier transform `η ↦ ⟨η⟩ ^ s T (φ e_η)` square integrable on an
open cone around `ξ`, where `⟨η⟩ ^ s = (1 + ‖η‖ ^ 2) ^ (s / 2)`. This file shows that the choice
of cutoff does not matter near `x`: multiplying `φ` by a smooth function keeps square
integrability, at the price of shrinking the cone. This is the `L²` form of Hörmander's
Lemma 8.1.1, and it gives the `H^s` wave front set the same calculus as the wave front set: the
`H^s` wave front set of a sum lies in the union of the `H^s` wave front sets, multiplication by a
smooth function `g` does not enlarge it and leaves it unchanged where `g ≠ 0`, and restriction to
an open subset keeps exactly the part over that subset.

The proof starts from the discrete convolution formula
`T (φ g e_η) = ∑ m, a_m T (φ e_(η - m))` of `Distribution.exists_hasSum_localFourier_of_eq_mul`,
with coefficients `a_m` rapidly decreasing in `‖m‖`. On a cone `Γ'` whose conic neighbourhoods
`closedBall η (c ‖η‖)` lie in `Γ`, each translate is controlled pointwise:

* if `‖m‖ ≤ c ‖η‖`, then `η - m ∈ Γ`, and Peetre's inequality
  `⟨η⟩ ^ s ≤ 2 ^ (|s| / 2) ⟨m⟩ ^ |s| ⟨η - m⟩ ^ s` bounds the weighted translate by
  `⟨m⟩ ^ |s|` times the translate of the weighted transform on `Γ`, a fixed `L²` function;
* if `‖m‖ > c ‖η‖`, then `‖η‖` is at most a multiple of `‖m‖`, and the polynomial growth of the
  localized Fourier transform bounds the weighted translate by a power of `1 + ‖m‖` times the
  fixed square integrable function `(1 + ‖η‖) ^ (-r)`, `2 r > dim E`.

So each weighted translate lies in `L²` with norm at most a power of `1 + ‖m‖`, and the series
converges absolutely in `L²` (`TauCeti.memLp_one_add_norm_sq_rpow_smul_of_hasSum`).

## Main results

* `TauCeti.memLp_one_add_norm_sq_rpow_smul_of_hasSum`: square integrability with weight
  `⟨η⟩ ^ s` on `Γ'` of a superposition of translates of a function of polynomial growth, with
  rapidly decreasing coefficients, which is square integrable with that weight on `Γ`.
* `Distribution.memLp_one_add_norm_sq_rpow_smul_localFourier_of_eq_mul`: weighted square
  integrability of the localized Fourier transform on `Γ` survives multiplication of the cutoff
  by a smooth function, on `Γ'`.
* `Distribution.IsMicrolocallySobolevAt.exists_nhds_cone`: at a point where `T` is microlocally
  `H^s` there are a neighbourhood `U` of `x` and an open cone `Γ` around `ξ` such that every
  cutoff supported in `U` has weighted localized Fourier transform square integrable on `Γ`.
* `Distribution.IsMicrolocallySobolevAt.add`, `Distribution.sobolevWaveFrontSet_add_subset`,
  `Distribution.sobolevWaveFrontSet_sub_subset`, `Distribution.sobolevWaveFrontSet_sum_subset`:
  the `H^s` wave front set of a sum lies in the union of the `H^s` wave front sets.
* `Distribution.IsMicrolocallySobolevAt.smulLeftCLM`,
  `Distribution.isMicrolocallySobolevAt_smulLeftCLM_iff`,
  `Distribution.sobolevWaveFrontSet_smulLeftCLM_subset`,
  `Distribution.mem_sobolevWaveFrontSet_smulLeftCLM_iff`,
  `Distribution.sobolevWaveFrontSet_smulLeftCLM_of_ne_zero`: the `H^s` wave front set of a smooth
  multiple `g T` lies in that of `T` over `tsupport g`, with equality where `g ≠ 0`.
* `Distribution.isMicrolocallySobolevAt_restrictCLM_iff`,
  `Distribution.sobolevWaveFrontSet_restrictCLM`,
  `Distribution.sobolevWaveFrontSet_inter_eq_of_restrictCLM_eq`: for an open subset `Ω' ≤ Ω`,
  `WF_s(T|_{Ω'}) = WF_s(T) ∩ (Ω' × E)`, so the `H^s` wave front set over an open set depends only
  on the restriction to it.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Lemma 8.1.1 (the rapid decay version, whose splitting of the convolution is
  followed here).
* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997, §11.1
  (the `H^s` wave front set).
-/

public section

noncomputable section

open Complex Filter Function Metric MeasureTheory Module Set TopologicalSpace TestFunction
open scoped Distributions Topology ENNReal ContDiff

namespace TauCeti

section Pointwise

variable {E : Type*} [NormedAddCommGroup E]

/-- The pointwise bound for one weighted translate. On `Γ'`, the weighted translate
`⟨η⟩ ^ s F (η - v)` is at most `D (1 + ‖v‖) ^ (k + N + r)` times the sum of the translate by `v` of
`⟨ζ⟩ ^ s F ζ` cut off to `Γ` and of `(1 + ‖η‖) ^ (-r)`, with `D` independent of `v` and `η`. -/
private theorem norm_one_add_norm_sq_rpow_smul_le {F : E → ℂ} {C₀ : ℝ} {k : ℕ}
    (hF : ∀ ζ, ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k) {Γ Γ' : Set E} {c : ℝ} (hc : 0 < c)
    (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ) {s : ℝ} {N : ℕ} (hN : |s| ≤ N) (r : ℕ)
    {η : E} (hη : η ∈ Γ') (v : E) :
    ‖(1 + ‖η‖ ^ 2) ^ (s / 2) • F (η - v)‖ ≤
      max (2 ^ (|s| / 2)) (C₀ * (1 + c⁻¹) ^ (k + N + r)) * (1 + ‖v‖) ^ (k + N + r) *
        (‖Γ.indicator (fun ζ ↦ (1 + ‖ζ‖ ^ 2) ^ (s / 2) • F ζ) (η - v)‖ +
          ((1 + ‖η‖) ^ r)⁻¹) := by
  have hC₀ : 0 ≤ C₀ := (norm_nonneg (F 0)).trans (by simpa using hF 0)
  set D := max (2 ^ (|s| / 2)) (C₀ * (1 + c⁻¹) ^ (k + N + r))
  set A := ‖Γ.indicator (fun ζ ↦ (1 + ‖ζ‖ ^ 2) ^ (s / 2) • F ζ) (η - v)‖
  have hA : 0 ≤ A := norm_nonneg _
  have hR : 0 < ((1 + ‖η‖) ^ r)⁻¹ := by positivity
  have hv1 : 1 ≤ 1 + ‖v‖ := le_add_of_nonneg_right (norm_nonneg v)
  have _ : 0 ≤ D := le_max_of_le_left (by positivity)
  have hw : 0 ≤ (1 + ‖η‖ ^ 2) ^ (s / 2) := by positivity
  rw [norm_smul, Real.norm_of_nonneg hw]
  -- The weight `⟨y⟩ ^ s` is at most `⟨y⟩ ^ N ≤ (1 + ‖y‖) ^ N`.
  have hweight (y : E) : (1 + ‖y‖ ^ 2) ^ (s / 2) ≤ (1 + ‖y‖) ^ N := by
    refine le_trans (Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖y‖])
      (by linarith [le_abs_self s] : s / 2 ≤ (N : ℝ) / 2)) ?_
    exact one_add_norm_sq_rpow_le_one_add_norm_pow y N
  by_cases hv : ‖v‖ ≤ c * ‖η‖
  · -- Small shifts stay in `Γ`; Peetre's inequality moves the weight to `η - v`.
    have hmem : η - v ∈ Γ := by
      refine hΓ' η hη (mem_closedBall.2 ?_)
      rwa [dist_eq_norm, sub_sub_cancel_left, norm_neg]
    have hAeq : A = (1 + ‖η - v‖ ^ 2) ^ (s / 2) * ‖F (η - v)‖ := by
      simp only [A, indicator_of_mem hmem, norm_smul, Real.norm_of_nonneg (by positivity :
        (0 : ℝ) ≤ (1 + ‖η - v‖ ^ 2) ^ (s / 2))]
    have hpeetre := one_add_norm_sq_rpow_le_mul_sub s η (η - v)
    rw [sub_sub_cancel] at hpeetre
    have hvN : (1 + ‖v‖ ^ 2) ^ (|s| / 2) ≤ (1 + ‖v‖) ^ (k + N + r) := by
      refine le_trans (Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖v‖])
        (by linarith : |s| / 2 ≤ (N : ℝ) / 2)) ?_
      exact (one_add_norm_sq_rpow_le_one_add_norm_pow v N).trans
        (pow_le_pow_right₀ hv1 (by omega))
    calc (1 + ‖η‖ ^ 2) ^ (s / 2) * ‖F (η - v)‖
        ≤ 2 ^ (|s| / 2) * (1 + ‖v‖ ^ 2) ^ (|s| / 2) * (1 + ‖η - v‖ ^ 2) ^ (s / 2) *
            ‖F (η - v)‖ := by gcongr
      _ = 2 ^ (|s| / 2) * (1 + ‖v‖ ^ 2) ^ (|s| / 2) * A := by rw [hAeq]; ring
      _ ≤ D * (1 + ‖v‖) ^ (k + N + r) * (A + ((1 + ‖η‖) ^ r)⁻¹) := by
          gcongr
          · exact le_max_left _ _
          · linarith
  · -- Large shifts: `1 + ‖η‖` and `1 + ‖η - v‖` are at most `(1 + c⁻¹) (1 + ‖v‖)`.
    push Not at hv
    have hηc : ‖η‖ < c⁻¹ * ‖v‖ := by
      rw [lt_inv_mul_iff₀ hc]
      linarith
    have hη' : 1 + ‖η‖ ≤ (1 + c⁻¹) * (1 + ‖v‖) := by
      nlinarith [norm_nonneg v, inv_pos.2 hc]
    have hηv : 1 + ‖η - v‖ ≤ (1 + c⁻¹) * (1 + ‖v‖) := by
      nlinarith [norm_sub_le η v, norm_nonneg v, inv_pos.2 hc]
    have _ : (1 + ‖η‖) ^ r * ((1 + ‖η‖) ^ r)⁻¹ = 1 :=
      mul_inv_cancel₀ (by positivity)
    calc (1 + ‖η‖ ^ 2) ^ (s / 2) * ‖F (η - v)‖
        ≤ (1 + ‖η‖) ^ N * (C₀ * (1 + ‖η - v‖) ^ k) := by
          gcongr
          · exact hweight η
          · exact hF _
      _ = C₀ * (1 + ‖η - v‖) ^ k * (1 + ‖η‖) ^ (N + r) * ((1 + ‖η‖) ^ r)⁻¹ := by
          rw [pow_add]
          field_simp
      _ ≤ C₀ * ((1 + c⁻¹) * (1 + ‖v‖)) ^ k * ((1 + c⁻¹) * (1 + ‖v‖)) ^ (N + r) *
            ((1 + ‖η‖) ^ r)⁻¹ := by gcongr
      _ = C₀ * (1 + c⁻¹) ^ (k + N + r) * (1 + ‖v‖) ^ (k + N + r) * ((1 + ‖η‖) ^ r)⁻¹ := by
          simp only [mul_pow, pow_add]
          ring
      _ ≤ D * (1 + ‖v‖) ^ (k + N + r) * (A + ((1 + ‖η‖) ^ r)⁻¹) := by
          gcongr
          · exact le_max_right _ _
          · linarith

end Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The countable case of `TauCeti.memLp_one_add_norm_sq_rpow_smul_of_hasSum`, where the series
can be summed in `L²`. -/
private theorem memLp_one_add_norm_sq_rpow_smul_of_hasSum_of_countable {ι : Type*} [Countable ι]
    {v : ι → E} {a : ι → ℂ} (ha : ∀ j : ℕ, Summable fun i ↦ (1 + ‖v i‖) ^ j * ‖a i‖)
    {F : E → ℂ} (hFc : Continuous F) {C₀ : ℝ} {k : ℕ} (hF : ∀ ζ, ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k)
    {Γ Γ' : Set E} (hΓ : MeasurableSet Γ) (hΓ'm : MeasurableSet Γ') {c : ℝ} (hc : 0 < c)
    (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ) {s : ℝ}
    (hL : MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • F η) 2 (volume.restrict Γ))
    {G : E → ℂ} (hG : ∀ η, HasSum (fun i ↦ a i * F (η - v i)) (G η)) :
    MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • G η) 2 (volume.restrict Γ') := by
  set w : E → ℝ := fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2)
  have hwc : Continuous w :=
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow E (s / 2)).1.continuous
  set N := ⌈|s|⌉₊
  have hN : |s| ≤ N := Nat.le_ceil _
  set r := finrank ℝ E + 1
  set D := max (2 ^ (|s| / 2)) (C₀ * (1 + c⁻¹) ^ (k + N + r))
  have _ : 0 ≤ D := le_max_of_le_left (by positivity)
  -- The two fixed square integrable functions of the pointwise bound.
  set H : E → ℂ := Γ.indicator fun ζ ↦ w ζ • F ζ
  have hH : MemLp H 2 volume := (memLp_indicator_iff_restrict hΓ.nullMeasurableSet).2 hL
  set R : E → ℝ := fun η ↦ ((1 + ‖η‖) ^ r)⁻¹
  have hR : MemLp R 2 volume := by
    refine (memLp_two_one_add_norm_rpow_neg (V := E) volume (r := r)
      (by simp only [r]; push_cast; linarith)).congr_norm ?_ (.of_forall fun η ↦ ?_)
    · exact ((continuous_const.add (continuous_norm (E := E))).pow r).inv₀
        (fun η : E ↦ (pow_pos (by positivity : (0 : ℝ) < 1 + ‖η‖) r).ne') |>.aestronglyMeasurable
    · simp only [R, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖η‖), Real.rpow_natCast]
  set M := eLpNorm H 2 volume + eLpNorm R 2 volume
  have hM : M ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hH.eLpNorm_ne_top, hR.eLpNorm_ne_top⟩
  -- Each weighted translate lies in `L²(Γ')`, with norm at most
  -- `D (1 + ‖v i‖) ^ (k + N + r) ‖a i‖ M` by the pointwise bound.
  set g : ι → E → ℂ := fun i η ↦ w η • (a i * F (η - v i))
  have hgm (i : ι) : AEStronglyMeasurable (g i) (volume.restrict Γ') :=
    (hwc.smul (continuous_const.mul
      (hFc.comp (continuous_id.sub continuous_const)))).aestronglyMeasurable
  have hgle (i : ι) : eLpNorm (g i) 2 (volume.restrict Γ') ≤
      ENNReal.ofReal (D * ((1 + ‖v i‖) ^ (k + N + r) * ‖a i‖)) * M := by
    set K : E → ℝ := fun η ↦ ‖H (η - v i)‖ + R η
    have hHv := hH.comp_measurePreserving (measurePreserving_sub_right volume (v i))
    -- Translation does not change the `L²` norm of `H`.
    have hHv' : eLpNorm (fun η ↦ ‖H (η - v i)‖) 2 volume = eLpNorm H 2 volume := by
      rw [eLpNorm_norm (fun η ↦ H (η - v i)) hHv.aestronglyMeasurable]
      exact eLpNorm_comp_measurePreserving hH.aestronglyMeasurable
        (measurePreserving_sub_right volume (v i))
    have hKle : eLpNorm K 2 volume ≤ M :=
      (eLpNorm_add_le (by norm_num)).trans_eq (by rw [hHv'])
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := K)
      (c := D * ((1 + ‖v i‖) ^ (k + N + r) * ‖a i‖)) (hgm i) ?_ 2).trans ?_
    · refine (ae_restrict_iff' hΓ'm).2 (.of_forall fun η hη ↦ ?_)
      have hb := norm_one_add_norm_sq_rpow_smul_le hF hc hΓ' hN r hη (v i)
      have hK0 : 0 ≤ K η := add_nonneg (norm_nonneg _) (by positivity)
      rw [Real.norm_of_nonneg hK0]
      calc ‖g i η‖ = ‖a i‖ * ‖w η • F (η - v i)‖ := by
            simp only [g, ← mul_smul_comm, norm_mul]
        _ ≤ ‖a i‖ * (D * (1 + ‖v i‖) ^ (k + N + r) * K η) := by gcongr
        _ = D * ((1 + ‖v i‖) ^ (k + N + r) * ‖a i‖) * K η := by ring
    · gcongr
      exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hKle
  have hgL (i : ι) : MemLp (g i) 2 (volume.restrict Γ') :=
    (hgle i).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM.lt_top)
  -- The series of weighted translates converges absolutely in `L²(Γ')`, to `⟨η⟩ ^ s G η`.
  set f : ι → Lp ℂ 2 (volume.restrict Γ') := fun i ↦ (hgL i).toLp (g i)
  have hsum : ∑' i, ‖f i‖ₑ ≠ ⊤ := by
    have hs := (ha (k + N + r)).mul_left D
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal (∑' i, D * ((1 + ‖v i‖) ^ (k + N + r) *
      ‖a i‖)) * M) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun i ↦ by positivity) hs, ← ENNReal.tsum_mul_right]
    exact CompleteLattice.summable.tsum_le_tsum (fun i ↦ (Lp.eNorm_toLp (hgL i)).trans_le (hgle i))
      CompleteLattice.summable
  have h2 : ∀ᵐ η ∂(volume.restrict Γ'), ∀ i, f i η = g i η :=
    ae_all_iff.2 fun i ↦ (hgL i).coeFn_toLp
  refine (Lp.memLp (∑' i, f i)).ae_eq ?_
  filter_upwards [Lp.coeFn_tsum hsum, h2] with η h1η h2η
  rw [h1η]
  simp only [h2η, g]
  exact ((hG η).const_smul (w η)).tsum_eq

/-- **Square integrability of a discrete convolution on a smaller cone.** Let `F` be a continuous
function of polynomial growth, and `a i` coefficients rapidly decreasing in `‖v i‖`. Suppose
`⟨η⟩ ^ s F η` is square integrable on a measurable set `Γ`, where
`⟨η⟩ ^ s = (1 + ‖η‖ ^ 2) ^ (s / 2)`, and that for some `c > 0` the closed ball of radius `c ‖η‖`
about every point `η` of a measurable set `Γ'` lies in `Γ`. Then the superposition of translates
`G η = ∑ i, a i F (η - v i)` makes `⟨η⟩ ^ s G η` square integrable on `Γ'`. -/
theorem memLp_one_add_norm_sq_rpow_smul_of_hasSum {ι : Type*} {v : ι → E} {a : ι → ℂ}
    (ha : ∀ j : ℕ, Summable fun i ↦ (1 + ‖v i‖) ^ j * ‖a i‖) {F : E → ℂ} (hFc : Continuous F)
    {C₀ : ℝ} {k : ℕ} (hF : ∀ ζ, ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k) {Γ Γ' : Set E}
    (hΓ : MeasurableSet Γ) (hΓ'm : MeasurableSet Γ') {c : ℝ} (hc : 0 < c)
    (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ) {s : ℝ}
    (hL : MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • F η) 2 (volume.restrict Γ))
    {G : E → ℂ} (hG : ∀ η, HasSum (fun i ↦ a i * F (η - v i)) (G η)) :
    MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • G η) 2 (volume.restrict Γ') := by
  -- Only the countably many indices with `a i ≠ 0` contribute.
  have hS : (support a).Countable :=
    (ha 0).countable_support.mono fun i hi ↦ by simpa using hi
  have := hS.to_subtype
  exact memLp_one_add_norm_sq_rpow_smul_of_hasSum_of_countable (ι := support a)
    (fun j ↦ (ha j).subtype _) hFc hF hΓ hΓ'm hc hΓ' hL fun η ↦
      (hasSum_subtype_iff_of_support_subset (support_mul_subset_left _ _)).2 (hG η)

end TauCeti

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-- **Localization of weighted square integrability** (the `L²` form of Hörmander I,
Lemma 8.1.1). Suppose `⟨η⟩ ^ s` times the localized Fourier transform of `T` with cutoff `φ` is
square integrable on a measurable set `Γ`, and `Γ'` is a measurable set such that for some `c > 0`
the closed ball of radius `c ‖η‖` about every `η ∈ Γ'` lies in `Γ`. Then for every cutoff
`ψ = φ g` with `g` smooth on `Ω`, `⟨η⟩ ^ s` times the localized Fourier transform of `T` with
cutoff `ψ` is square integrable on `Γ'`. Each point `ξ` of an open cone `Γ` lies in an open cone
`Γ'` of this kind (`IsOpen.exists_cone_closedBall_subset`). -/
theorem memLp_one_add_norm_sq_rpow_smul_localFourier_of_eq_mul {T : 𝓓'(Ω, ℂ)}
    {φ ψ : 𝓓(Ω, ℂ)} {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g Ω) (hψ : ∀ x, ψ x = φ x * g x)
    {Γ Γ' : Set E} (hΓ : MeasurableSet Γ) (hΓ'm : MeasurableSet Γ') {c : ℝ} (hc : 0 < c)
    (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ) {s : ℝ}
    (hL : MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier φ η) 2 (volume.restrict Γ)) :
    MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier ψ η) 2 (volume.restrict Γ') := by
  obtain ⟨L, a, ha, hsum⟩ := exists_hasSum_localFourier_of_eq_mul T hg hψ
  obtain ⟨C₀, k, hF⟩ := exists_norm_localFourier_le T φ
  exact TauCeti.memLp_one_add_norm_sq_rpow_smul_of_hasSum (v := fun m : L ↦ (m : E)) ha
    (T.continuous_localFourier φ) hF hΓ hΓ'm hc hΓ' hL hsum

/-- **Independence of the cutoff.** If `T` is microlocally `H^s` at `(x, ξ)`, then there are a
neighbourhood `U` of `x` and an open cone `Γ` containing `ξ` such that for *every* test function
`ψ` supported in `U`, `⟨η⟩ ^ s` times the localized Fourier transform of `T` with cutoff `ψ` is
square integrable on `Γ`. -/
theorem IsMicrolocallySobolevAt.exists_nhds_cone {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (h : T.IsMicrolocallySobolevAt s x ξ) :
    ∃ U ∈ 𝓝 x, ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
        MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier ψ η) 2 (volume.restrict Γ) := by
  obtain ⟨φ, hφx, Γ, hΓ, hξ, hcone, hL⟩ := isMicrolocallySobolevAt_iff.1 h
  obtain ⟨Γ', hΓ'o, hξ', hcone', c, hc, hΓ'⟩ := hΓ.exists_cone_closedBall_subset hcone hξ
  -- Near `x` every cutoff is a smooth multiple of `φ`.
  obtain ⟨U, hU, hUφ⟩ := exists_mem_nhds_forall_exists_contDiff_eq_mul hφx
  refine ⟨U, hU, Γ', hΓ'o, hξ', hcone', fun ψ hψ ↦ ?_⟩
  obtain ⟨g, hg, hψg⟩ := hUφ ψ hψ
  exact memLp_one_add_norm_sq_rpow_smul_localFourier_of_eq_mul hg.contDiffOn hψg
    hΓ.measurableSet hΓ'o.measurableSet hc hΓ' hL

/-- The sum of two distributions microlocally `H^s` at `(x, ξ)` is microlocally `H^s` there. -/
theorem IsMicrolocallySobolevAt.add {s : ℝ} {S T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (hS : S.IsMicrolocallySobolevAt s x ξ) (hT : T.IsMicrolocallySobolevAt s x ξ) :
    (S + T).IsMicrolocallySobolevAt s x ξ := by
  have hx : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySobolevAt_iff.1 hS
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hLS⟩ := hS.exists_nhds_cone
  obtain ⟨V, hV, Γ', hΓ', hξ', hcone', hLT⟩ := hT.exists_nhds_cone
  -- A cutoff supported in `U ∩ V` serves for both distributions, on the cone `Γ ∩ Γ'`.
  obtain ⟨ψ, hψ, hψx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (inter_mem hU hV) (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
  refine isMicrolocallySobolevAt_iff.2 ⟨ψ, by simp [hψx], Γ ∩ Γ', hΓ.inter hΓ', ⟨hξ, hξ'⟩,
    fun t ht η hη ↦ ⟨hcone t ht η hη.1, hcone' t ht η hη.2⟩, ?_⟩
  have h₁ := (hLS ψ (hψ.trans (inter_subset_left.trans inter_subset_left))).mono_measure
    (Measure.restrict_mono_set volume (inter_subset_left (t := Γ')))
  have h₂ := (hLT ψ (hψ.trans (inter_subset_left.trans inter_subset_right))).mono_measure
    (Measure.restrict_mono_set volume (inter_subset_right (s := Γ)))
  convert h₁.add h₂ using 1
  ext η
  simp [smul_add]

/-- The `H^s` wave front set of a sum lies in the union of the `H^s` wave front sets. -/
theorem sobolevWaveFrontSet_add_subset (s : ℝ) (S T : 𝓓'(Ω, ℂ)) :
    (S + T).sobolevWaveFrontSet s ⊆ S.sobolevWaveFrontSet s ∪ T.sobolevWaveFrontSet s := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, h⟩ := mem_sobolevWaveFrontSet_iff.1 hp
  by_contra hST
  simp only [mem_union, mem_sobolevWaveFrontSet_iff, not_or, not_and, not_not] at hST
  exact h ((hST.1 hx hξ).add (hST.2 hx hξ))

/-- The `H^s` wave front set of a difference lies in the union of the `H^s` wave front sets. -/
theorem sobolevWaveFrontSet_sub_subset (s : ℝ) (S T : 𝓓'(Ω, ℂ)) :
    (S - T).sobolevWaveFrontSet s ⊆ S.sobolevWaveFrontSet s ∪ T.sobolevWaveFrontSet s := by
  simpa [sub_eq_add_neg, sobolevWaveFrontSet_neg] using sobolevWaveFrontSet_add_subset s S (-T)

/-- The `H^s` wave front set of a finite sum lies in the union of the `H^s` wave front sets. -/
theorem sobolevWaveFrontSet_sum_subset (s : ℝ) {ι : Type*} (t : Finset ι) (T : ι → 𝓓'(Ω, ℂ)) :
    (∑ i ∈ t, T i).sobolevWaveFrontSet s ⊆ ⋃ i ∈ t, (T i).sobolevWaveFrontSet s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.set_biUnion_insert]
    exact (sobolevWaveFrontSet_add_subset s _ _).trans (union_subset_union_right _ ih)

section SmulLeft

variable {g : E → ℝ}

/-- A smooth multiple `g T` of a distribution microlocally `H^s` at `(x, ξ)` is microlocally
`H^s` there. -/
theorem IsMicrolocallySobolevAt.smulLeftCLM {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (h : T.IsMicrolocallySobolevAt s x ξ) (hg : ContDiff ℝ ∞ g) :
    (smulLeftCLM hg T).IsMicrolocallySobolevAt s x ξ := by
  obtain ⟨φ, hφx, Γ, hΓ, hξ, hcone, hL⟩ := isMicrolocallySobolevAt_iff.1 h
  obtain ⟨Γ', hΓ'o, hξ', hcone', c, hc, hΓ'⟩ := hΓ.exists_cone_closedBall_subset hcone hξ
  -- The same cutoff `φ` works for `g T` on the smaller cone `Γ'`, since `g T` with cutoff `φ`
  -- is `T` with cutoff `g φ`.
  refine isMicrolocallySobolevAt_iff.2 ⟨φ, hφx, Γ', hΓ'o, hξ', hcone', ?_⟩
  simp only [localFourier_smulLeftCLM]
  exact memLp_one_add_norm_sq_rpow_smul_localFourier_of_eq_mul
    (ofRealCLM.contDiff.comp hg).contDiffOn (fun y ↦ by simp [mul_comm]) hΓ.measurableSet
    hΓ'o.measurableSet hc hΓ' hL

/-- Where `g` does not vanish, a smooth multiple `g T` is microlocally `H^s` exactly where `T`
is. -/
theorem isMicrolocallySobolevAt_smulLeftCLM_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (hg : ContDiff ℝ ∞ g) (hx : g x ≠ 0) :
    (smulLeftCLM hg T).IsMicrolocallySobolevAt s x ξ ↔ T.IsMicrolocallySobolevAt s x ξ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.smulLeftCLM hg⟩
  -- A cutoff `φ` for `g T` gives the cutoff `g φ` for `T`, which does not vanish at `x`.
  obtain ⟨φ, hφx, Γ, hΓ, hξ, hcone, hL⟩ := isMicrolocallySobolevAt_iff.1 h
  refine isMicrolocallySobolevAt_iff.2
    ⟨TestFunction.smulLeftCLM hg φ, by simp [hx, hφx], Γ, hΓ, hξ, hcone, ?_⟩
  simpa using hL

/-- **Smooth multiplication.** The `H^s` wave front set of a smooth multiple `g T` lies in the
`H^s` wave front set of `T`, over the support of `g`. -/
theorem sobolevWaveFrontSet_smulLeftCLM_subset (s : ℝ) (T : 𝓓'(Ω, ℂ)) (hg : ContDiff ℝ ∞ g) :
    (smulLeftCLM hg T).sobolevWaveFrontSet s ⊆
      T.sobolevWaveFrontSet s ∩ tsupport g ×ˢ univ := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, hT⟩ := mem_sobolevWaveFrontSet_iff.1 hp
  exact ⟨mem_sobolevWaveFrontSet_iff.2 ⟨hx, hξ, fun h ↦ hT (h.smulLeftCLM hg)⟩,
    (waveFrontSet_smulLeftCLM_subset T hg (sobolevWaveFrontSet_subset_waveFrontSet s _ hp)).2⟩

/-- Over the points where `g` does not vanish, a smooth multiple `g T` has the same `H^s` wave
front set as `T`. -/
theorem mem_sobolevWaveFrontSet_smulLeftCLM_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (hg : ContDiff ℝ ∞ g) (hx : g x ≠ 0) :
    (x, ξ) ∈ (smulLeftCLM hg T).sobolevWaveFrontSet s ↔ (x, ξ) ∈ T.sobolevWaveFrontSet s := by
  simp [isMicrolocallySobolevAt_smulLeftCLM_iff hg hx]

/-- Multiplying by a smooth function that vanishes nowhere on `Ω` does not change the `H^s` wave
front set. -/
theorem sobolevWaveFrontSet_smulLeftCLM_of_ne_zero (s : ℝ) (T : 𝓓'(Ω, ℂ))
    (hg : ContDiff ℝ ∞ g) (hg0 : ∀ x ∈ Ω, g x ≠ 0) :
    (smulLeftCLM hg T).sobolevWaveFrontSet s = T.sobolevWaveFrontSet s := by
  ext ⟨x, ξ⟩
  by_cases hx : x ∈ Ω
  · exact mem_sobolevWaveFrontSet_smulLeftCLM_iff hg (hg0 x hx)
  · simp [hx]

end SmulLeft

section Restriction

variable {Ω' : Opens E}

/-- At a point of an open subset `Ω' ≤ Ω`, the restriction `T|_{Ω'}` is microlocally `H^s`
exactly where `T` is. -/
theorem isMicrolocallySobolevAt_restrictCLM_iff (h : Ω' ≤ Ω) {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (hx : x ∈ Ω') :
    (restrictCLM T : 𝓓'(Ω', ℂ)).IsMicrolocallySobolevAt s x ξ ↔
      T.IsMicrolocallySobolevAt s x ξ := by
  constructor
  · -- A cutoff on `Ω'`, extended by zero, is a cutoff on `Ω`.
    intro hT
    obtain ⟨φ, hφx, Γ, hΓ, hξ, hcone, hL⟩ := isMicrolocallySobolevAt_iff.1 hT
    exact isMicrolocallySobolevAt_iff.2 ⟨TestFunction.monoCLM ℝ φ, by simpa [h] using hφx, Γ,
      hΓ, hξ, hcone, by simpa using hL⟩
  · -- Every cutoff supported near `x` works for `T`; take one supported in `Ω'`.
    intro hT
    obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hL⟩ := hT.exists_nhds_cone
    obtain ⟨φ, hφ, hφx⟩ := exists_tsupport_subset_apply_eq (Ω := Ω') (n := ⊤)
      (inter_mem hU (Ω'.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
    refine isMicrolocallySobolevAt_iff.2 ⟨φ, by simp [hφx], Γ, hΓ, hξ, hcone, ?_⟩
    simp only [localFourier_restrictCLM]
    exact hL _ (by simpa [h] using hφ.trans inter_subset_left)

/-- **Restriction** to an open subset `Ω' ≤ Ω` cuts the `H^s` wave front set down to the points
of `Ω'`. -/
theorem sobolevWaveFrontSet_restrictCLM (h : Ω' ≤ Ω) (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    (restrictCLM T : 𝓓'(Ω', ℂ)).sobolevWaveFrontSet s =
      T.sobolevWaveFrontSet s ∩ (Ω' : Set E) ×ˢ univ := by
  ext ⟨x, ξ⟩
  simp only [mem_inter_iff, mem_sobolevWaveFrontSet_iff, mem_prod, mem_univ, and_true]
  constructor
  · rintro ⟨hx, hξ, hT⟩
    exact ⟨⟨h hx, hξ, fun h' ↦ hT ((isMicrolocallySobolevAt_restrictCLM_iff h hx).2 h')⟩, hx⟩
  · rintro ⟨⟨-, hξ, hT⟩, hx⟩
    exact ⟨hx, hξ, fun h' ↦ hT ((isMicrolocallySobolevAt_restrictCLM_iff h hx).1 h')⟩

/-- The `H^s` wave front set is local: two distributions with the same restriction to an open set
`U ≤ Ω` have the same `H^s` wave front set over `U`. -/
theorem sobolevWaveFrontSet_inter_eq_of_restrictCLM_eq {s : ℝ} {S T : 𝓓'(Ω, ℂ)} {U : Opens E}
    (hU : U ≤ Ω) (h : (restrictCLM S : 𝓓'(U, ℂ)) = restrictCLM T) :
    S.sobolevWaveFrontSet s ∩ (U : Set E) ×ˢ univ =
      T.sobolevWaveFrontSet s ∩ (U : Set E) ×ˢ univ := by
  rw [← sobolevWaveFrontSet_restrictCLM hU, h, sobolevWaveFrontSet_restrictCLM hU]

end Restriction

end Distribution
