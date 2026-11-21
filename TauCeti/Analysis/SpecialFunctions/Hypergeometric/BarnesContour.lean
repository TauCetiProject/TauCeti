/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.MellinBarnes
import Mathlib.Analysis.Meromorphic.Complex
import TauCeti.Analysis.Contour.Residue.ChangeOfVariables
import TauCeti.Analysis.Contour.Residue.VerticalLineShift
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.Gamma.Residue
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Barnes's integral over a separating contour

Barnes's integral for the Gauss hypergeometric function
([DLMF 15.6.6](https://dlmf.nist.gov/15.6.E6)) is

`𝐅(a, b; c; z) = (2πi Γ(a) Γ(b))⁻¹ ∫ Γ(a + t) Γ(b + t) Γ(-t) Γ(c + t)⁻¹ (-z)^t dt`

over a contour from `-i∞` to `i∞` that separates the poles `t = -a - k`, `t = -b - k`
(`k : ℕ`) of `Γ(a + t) Γ(b + t)` from the poles `t = 0, 1, 2, …` of `Γ(-t)`. When `Re a` and
`Re b` are positive, a vertical line `Re t = σ` with `-min (Re a, Re b) < σ < 0` is such a
contour (`Complex.eulerIntegral_eq_mellinBarnes`). In general no vertical line separates the two
families, and the contour is the line `Re t = σ` for some `σ < 0` avoiding the poles, deformed
to pass to the right of the finitely many poles of `Γ(a + t) Γ(b + t)` with real part above `σ`.
By the residue theorem its integral is the line integral plus `2πi` times the residues at those
poles. This file defines that value and proves that it does not depend on the line.

## Main definitions

* `Complex.hypergeometricMellinBarnesIntegrand a b c z t`: the integrand
  `Γ(a + t) Γ(b + t) Γ(-t) Γ(c + t)⁻¹ (-z)^t` of DLMF 15.6.6.
* `Complex.gammaPolesRightOf a σ`: the poles `-a - k` of `t ↦ Γ(a + t)` with real part `> σ`.
* `Complex.hypergeometricMellinBarnes a b c z σ`: the integral `(2πi)⁻¹ ∫_C` over the separating
  contour `C`, written as `(2π)⁻¹ ∫ F(σ + i y) dy` plus the residues of `F` at the poles of
  `Γ(a + t) Γ(b + t)` to the right of `Re t = σ`.

## Main results

* `Complex.hypergeometricMellinBarnes_eq`: for `-z ∈ slitPlane`, the value does not depend on
  the line `Re t = σ`, among lines with `σ < 0` that avoid the poles of `Γ(a + t) Γ(b + t)`.
  This holds for all complex `a`, `b`, `c`.
* `Complex.eulerIntegral_eq_hypergeometricMellinBarnes`: for `0 < Re a`, `0 < Re b < Re c` and
  `-z ∈ slitPlane`, Euler's integral is `(Γ(a) Γ(b))⁻¹` times the contour integral, on every such
  line, including lines with poles of `Γ(a + t) Γ(b + t)` to their right.
* `Complex.residue_hypergeometricMellinBarnesIntegrand_neg_sub_natCast`: the residue at a simple
  pole `t = -a - k` that is not a pole of `Γ(b + t)` or of `Γ(-t)`, which is
  `(-1)^k / k! · Γ(b - a - k) Γ(a + k) Γ(c - a - k)⁻¹ (-z)^(-a - k)`.

## Implementation notes

The line shift is `TauCeti.Contour.integral_vertical_sub_eq_two_pi_mul_sum_residue`. Its
horizontal connectors vanish by Stirling's bounds on vertical strips
(`TauCeti.exists_norm_Gamma_add_vertical_strip_le`,
`TauCeti.exists_norm_inv_Gamma_add_vertical_strip_le`):
on `A ≤ Re t ≤ B`, `|Im t| = T`, the integrand is `O((1 + T)^K exp (-(π - |arg (-z)|) T))`.

## References

* NIST Digital Library of Mathematical Functions, §15.6,
  [15.6.6](https://dlmf.nist.gov/15.6.E6), and the paragraph following it on the contour.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §14.5.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Nat Real Topology

namespace Complex

/-! ### The integrand and its poles -/

/-- The integrand `Γ(a + t) Γ(b + t) Γ(-t) Γ(c + t)⁻¹ (-z)^t` of Barnes's integral for the Gauss
hypergeometric function (DLMF 15.6.6). -/
def hypergeometricMellinBarnesIntegrand (a b c z t : ℂ) : ℂ :=
  Gamma (a + t) * Gamma (b + t) * Gamma (-t) * (Gamma (c + t))⁻¹ * (-z) ^ t

theorem hypergeometricMellinBarnesIntegrand_def (a b c z t : ℂ) :
    hypergeometricMellinBarnesIntegrand a b c z t =
      Gamma (a + t) * Gamma (b + t) * Gamma (-t) * (Gamma (c + t))⁻¹ * (-z) ^ t := (rfl)

theorem hypergeometricMellinBarnesIntegrand_comm (a b c z : ℂ) :
    hypergeometricMellinBarnesIntegrand a b c z = hypergeometricMellinBarnesIntegrand b a c z := by
  ext t
  simp only [hypergeometricMellinBarnesIntegrand_def]
  ring

/-- The integrand of Barnes's integral is meromorphic in `t` everywhere. -/
theorem meromorphicAt_hypergeometricMellinBarnesIntegrand (a b c z t : ℂ) :
    MeromorphicAt (hypergeometricMellinBarnesIntegrand a b c z) t := by
  have hG (s : ℂ → ℂ) (hs : AnalyticAt ℂ s t) :
      MeromorphicAt (fun t ↦ Gamma (s t)) t :=
    (Meromorphic.Gamma (s t)).comp_analyticAt hs
  have hinv : MeromorphicAt (fun t ↦ (Gamma (c + t))⁻¹) t := (hG _ (by fun_prop)).inv
  have hpow : MeromorphicAt (fun t ↦ (-z) ^ t) t := by
    rcases eq_or_ne z 0 with rfl | hz
    · rcases eq_or_ne t 0 with rfl | ht
      · refine (MeromorphicAt.const (0 : ℂ) 0).congr ?_
        filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ 0)
        simp [zero_cpow hs]
      · refine (analyticAt_const (v := (0 : ℂ))).meromorphicAt.congr ?_
        filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds ht)] with s (hs : s ≠ 0)
        simp [zero_cpow hs]
    · exact ((differentiable_id.const_cpow (.inl (neg_ne_zero.mpr hz))).analyticAt t).meromorphicAt
  exact ((((hG _ (by fun_prop)).mul (hG _ (by fun_prop))).mul (hG _ (by fun_prop))).mul
    hinv).mul hpow

/-- The poles `t = -a - k` (`k : ℕ`) of `t ↦ Γ(a + t)` that lie to the right of the vertical line
`Re t = σ`. There are finitely many, since `Re (-a - k) = -Re a - k`. -/
def gammaPolesRightOf (a : ℂ) (σ : ℝ) : Finset ℂ :=
  (Finset.range ⌈-a.re - σ⌉₊).image fun k : ℕ ↦ -a - k

@[simp]
theorem mem_gammaPolesRightOf {a t : ℂ} {σ : ℝ} :
    t ∈ gammaPolesRightOf a σ ↔ σ < t.re ∧ ∃ k : ℕ, t = -a - k := by
  simp only [gammaPolesRightOf, Finset.mem_image, Finset.mem_range, Nat.lt_ceil]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨by simp; linarith, k, rfl⟩
  · rintro ⟨hσ, k, rfl⟩
    exact ⟨k, by simp at hσ; linarith, rfl⟩

@[simp]
theorem gammaPolesRightOf_eq_empty_iff {a : ℂ} {σ : ℝ} :
    gammaPolesRightOf a σ = ∅ ↔ -a.re ≤ σ := by
  simp [gammaPolesRightOf, Nat.ceil_eq_zero]

/-- The poles of `t ↦ Γ(a + t) Γ(b + t)` to the right of the line `Re t = σ`. -/
theorem mem_gammaPolesRightOf_union {a b t : ℂ} {σ : ℝ} :
    t ∈ gammaPolesRightOf a σ ∪ gammaPolesRightOf b σ ↔
      σ < t.re ∧ ∃ k : ℕ, t = -a - k ∨ t = -b - k := by
  simp only [Finset.mem_union, mem_gammaPolesRightOf]
  grind

/-! ### The integral over the separating contour -/

/-- Barnes's integral `(2πi)⁻¹ ∫_C Γ(a + t) Γ(b + t) Γ(-t) Γ(c + t)⁻¹ (-z)^t dt` (DLMF 15.6.6)
over the contour `C` that runs up the line `Re t = σ` and is deformed to pass to the right of the
poles of `Γ(a + t) Γ(b + t)` with real part `> σ`: the line integral `(2π)⁻¹ ∫ F(σ + i y) dy` plus
the residues of the integrand at those poles. For `σ < 0` avoiding the poles of
`Γ(a + t) Γ(b + t)` and `-z ∈ slitPlane`, it does not depend on `σ`
(`Complex.hypergeometricMellinBarnes_eq`), and when moreover `0 < Re a`, `0 < Re b < Re c` it is
`Γ(a) Γ(b)` times Euler's integral (`Complex.eulerIntegral_eq_hypergeometricMellinBarnes`). -/
def hypergeometricMellinBarnes (a b c z : ℂ) (σ : ℝ) : ℂ :=
  (2 * (π : ℂ))⁻¹ * (∫ y : ℝ, hypergeometricMellinBarnesIntegrand a b c z (σ + y * I)) +
    ∑ p ∈ gammaPolesRightOf a σ ∪ gammaPolesRightOf b σ,
      TauCeti.Contour.residue (hypergeometricMellinBarnesIntegrand a b c z) p

theorem hypergeometricMellinBarnes_def (a b c z : ℂ) (σ : ℝ) :
    hypergeometricMellinBarnes a b c z σ =
      (2 * (π : ℂ))⁻¹ * (∫ y : ℝ, hypergeometricMellinBarnesIntegrand a b c z (σ + y * I)) +
        ∑ p ∈ gammaPolesRightOf a σ ∪ gammaPolesRightOf b σ,
          TauCeti.Contour.residue (hypergeometricMellinBarnesIntegrand a b c z) p := (rfl)

theorem hypergeometricMellinBarnes_comm (a b c z : ℂ) (σ : ℝ) :
    hypergeometricMellinBarnes a b c z σ = hypergeometricMellinBarnes b a c z σ := by
  simp only [hypergeometricMellinBarnes_def, hypergeometricMellinBarnesIntegrand_comm a b,
    Finset.union_comm]

/-- When no pole of `Γ(a + t) Γ(b + t)` lies to the right of the line `Re t = σ`, the contour is
the line itself. -/
theorem hypergeometricMellinBarnes_eq_integral (a b c z : ℂ) {σ : ℝ} (ha : -a.re ≤ σ)
    (hb : -b.re ≤ σ) :
    hypergeometricMellinBarnes a b c z σ =
      (2 * (π : ℂ))⁻¹ * ∫ y : ℝ, hypergeometricMellinBarnesIntegrand a b c z (σ + y * I) := by
  rw [hypergeometricMellinBarnes_def, gammaPolesRightOf_eq_empty_iff.mpr ha,
    gammaPolesRightOf_eq_empty_iff.mpr hb]
  simp

/-! ### Stirling bounds on vertical strips -/

/-- Stirling's bound for the integrand of Barnes's integral on the part `|Im t| ≥ T₀` of the strip
`A ≤ Re t ≤ B`: it is `O((1 + |Im t|)^K exp (-(π - |arg (-z)|) |Im t|))`. -/
private theorem exists_norm_hypergeometricMellinBarnesIntegrand_strip_le (a b c : ℂ) {z : ℂ}
    (hz : z ≠ 0) (A B : ℝ) :
    ∃ C K T₀ : ℝ, ∀ x ∈ Icc A B, ∀ T : ℝ, T₀ ≤ |T| →
      ‖hypergeometricMellinBarnesIntegrand a b c z (x + T * I)‖ ≤
        C * ((1 + |T|) ^ K * Real.exp (-((π - |arg (-z)|) * |T|))) := by
  obtain ⟨Ca, hCa, Ka, Ta, ha⟩ := TauCeti.exists_norm_Gamma_add_vertical_strip_le a A B
  obtain ⟨Cb, hCb, Kb, Tb, hb⟩ := TauCeti.exists_norm_Gamma_add_vertical_strip_le b A B
  obtain ⟨Cs, hCs, Ks, Ts, hs⟩ := TauCeti.exists_norm_Gamma_add_vertical_strip_le 0 (-B) (-A)
  obtain ⟨Cc, hCc, Kc, hc⟩ := TauCeti.exists_norm_inv_Gamma_add_vertical_strip_le c A B
  obtain ⟨Cz, hzb⟩ := TauCeti.exists_norm_cpow_strip_le (neg_ne_zero.mpr hz) A B
  refine ⟨Ca * Cb * Cs * Cc * Cz, Ka + Kb + Ks + Kc, max (max Ta Tb) Ts, fun x hx T hT ↦ ?_⟩
  -- `Γ(-t)` is the case `w = 0` at the reflected point `-x - i T`.
  have h3 := hs (-x) ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩ (-T)
    (by rw [abs_neg]; exact le_trans (le_max_right _ _) hT)
  rw [show (0 : ℂ) + (((-x : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) = -((x : ℂ) + T * I) by push_cast; ring,
    abs_neg] at h3
  rw [hypergeometricMellinBarnesIntegrand_def, norm_mul, norm_mul, norm_mul, norm_mul]
  calc ‖Gamma (a + (x + T * I))‖ * ‖Gamma (b + (x + T * I))‖ * ‖Gamma (-(x + T * I))‖ *
        ‖(Gamma (c + (x + T * I)))⁻¹‖ * ‖(-z) ^ ((x : ℂ) + T * I)‖
      ≤ (Ca * (1 + |T|) ^ Ka * Real.exp (-(π * |T| / 2))) *
          (Cb * (1 + |T|) ^ Kb * Real.exp (-(π * |T| / 2))) *
          (Cs * (1 + |T|) ^ Ks * Real.exp (-(π * |T| / 2))) *
          (Cc * (1 + |T|) ^ Kc * Real.exp (π * |T| / 2)) *
          (Cz * Real.exp (|arg (-z)| * |T|)) := by
        gcongr
        · exact ha x hx T (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT)
        · exact hb x hx T (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT)
        · exact hc x hx T
        · exact hzb x hx T
    _ = Ca * Cb * Cs * Cc * Cz * (((1 + |T|) ^ Ka * (1 + |T|) ^ Kb * (1 + |T|) ^ Ks *
          (1 + |T|) ^ Kc) * (Real.exp (-(π * |T| / 2)) * Real.exp (-(π * |T| / 2)) *
          Real.exp (-(π * |T| / 2)) * Real.exp (π * |T| / 2) * Real.exp (|arg (-z)| * |T|))) := by
        ring
    _ = Ca * Cb * Cs * Cc * Cz * ((1 + |T|) ^ (Ka + Kb + Ks + Kc) *
          Real.exp (-((π - |arg (-z)|) * |T|))) := by
        rw [← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity),
          ← Real.rpow_add (by positivity), ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
          ← Real.exp_add]
        ring_nf

/-- On a vertical strip `A ≤ Re t ≤ B`, the integrand of Barnes's integral tends to `0` as
`|Im t| → ∞`, uniformly in `Re t`, when `-z ∈ slitPlane`. -/
private theorem tendsto_hypergeometricMellinBarnesIntegrand_strip (a b c : ℂ) {z : ℂ}
    (hz : -z ∈ slitPlane) (A B : ℝ) :
    Tendsto (fun q : ℝ × ℝ ↦ hypergeometricMellinBarnesIntegrand a b c z (q.2 + q.1 * I))
      (cocompact ℝ ×ˢ 𝓟 (Icc A B)) (𝓝 0) := by
  obtain ⟨C, K, T₀, hbound⟩ :=
    exists_norm_hypergeometricMellinBarnesIntegrand_strip_le a b c
      (by simpa using slitPlane_ne_zero hz) A B
  have hθ : |arg (-z)| < π :=
    abs_lt.mpr ⟨neg_pi_lt_arg _, (arg_le_pi _).lt_of_ne (slitPlane_arg_ne_pi hz)⟩
  have hT : ∀ᶠ T : ℝ in cocompact ℝ, T₀ ≤ |T| :=
    ((tendsto_norm_cocompact_atTop (E := ℝ)).eventually_ge_atTop T₀).mono
      fun T h ↦ by rwa [Real.norm_eq_abs] at h
  have hlim := ((TauCeti.tendsto_one_add_abs_rpow_mul_exp_neg_mul_abs K (sub_pos.mpr hθ)).comp
    (tendsto_fst (f := cocompact ℝ) (g := 𝓟 (Icc A B)))).const_mul C
  rw [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hT.prod_mk (mem_principal_self (Icc A B))] with ⟨T, x⟩ ⟨hT, hx⟩
  exact hbound x hx T hT

/-! ### Independence of the line -/

/-- The integrand of Barnes's integral is holomorphic wherever none of `a + t`, `b + t`, `-t` is a
nonpositive integer. -/
private theorem differentiableAt_hypergeometricMellinBarnesIntegrand {a b c z t : ℂ} (hz : z ≠ 0)
    (ha : ∀ m : ℕ, a + t ≠ -m) (hb : ∀ m : ℕ, b + t ≠ -m) (ht : ∀ m : ℕ, -t ≠ -m) :
    DifferentiableAt ℂ (hypergeometricMellinBarnesIntegrand a b c z) t := by
  have hGa := (differentiableAt_Gamma _ ha).comp t (differentiableAt_id.const_add a)
  have hGb := (differentiableAt_Gamma _ hb).comp t (differentiableAt_id.const_add b)
  have hGs := (differentiableAt_Gamma _ ht).comp t differentiableAt_id.neg
  have hGc := (differentiable_one_div_Gamma (c + t)).comp t (differentiableAt_id.const_add c)
  have hpow := differentiableAt_id.const_cpow (x := t) (.inl (neg_ne_zero.mpr hz))
  exact (((hGa.mul hGb).mul hGs).mul hGc).mul hpow

/-- On a line `Re t = σ` with `σ < 0` avoiding the poles of `Γ(a + t) Γ(b + t)`, the integrand of
Barnes's integral is integrable. -/
private theorem integrable_hypergeometricMellinBarnesIntegrand (a b c : ℂ) {z : ℂ}
    (hz : -z ∈ slitPlane) {σ : ℝ} (hσ : σ < 0) (ha : ∀ n : ℕ, a.re + σ ≠ -n)
    (hb : ∀ n : ℕ, b.re + σ ≠ -n) :
    Integrable fun y : ℝ ↦ hypergeometricMellinBarnesIntegrand a b c z (σ + y * I) := by
  simp only [hypergeometricMellinBarnesIntegrand_def]
  exact integrable_Gamma_mul_Gamma_mul_Gamma_mul_inv_Gamma_mul_neg_cpow c hz ha hb
    fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)]

/-- A pole of `Γ(a + t) Γ(b + t)` does not lie on a line `Re t = σ` that avoids the poles. -/
private theorem re_ne_of_pole {a b t : ℂ} {σ : ℝ} (ha : ∀ n : ℕ, a.re + σ ≠ -n)
    (hb : ∀ n : ℕ, b.re + σ ≠ -n) (ht : ∃ k : ℕ, t = -a - k ∨ t = -b - k) : t.re ≠ σ := by
  obtain ⟨k, rfl | rfl⟩ := ht
  · exact fun h ↦ ha k (by simp at h; linarith)
  · exact fun h ↦ hb k (by simp at h; linarith)

/-- For `σ₁ ≤ σ₂ < 0`, with the line `Re t = σ₁` avoiding the poles of `Γ(a + t) Γ(b + t)`, the
integrand of Barnes's integral is holomorphic on an open neighbourhood of the strip
`σ₁ ≤ Re t ≤ σ₂` except at the poles of `Γ(a + t) Γ(b + t)` with `σ₁ < Re t`, `Re t ≤ σ₂`. -/
private theorem exists_differentiableOn_hypergeometricMellinBarnesIntegrand (a b c : ℂ) {z : ℂ}
    (hz : z ≠ 0) {σ₁ σ₂ : ℝ} (hσ₂ : σ₂ < 0) (ha₁ : ∀ n : ℕ, a.re + σ₁ ≠ -n)
    (hb₁ : ∀ n : ℕ, b.re + σ₁ ≠ -n) :
    ∃ U : Set ℂ, IsOpen U ∧ {t : ℂ | σ₁ ≤ t.re ∧ t.re ≤ σ₂} ⊆ U ∧
      DifferentiableOn ℂ (hypergeometricMellinBarnesIntegrand a b c z) (U \
        ↑((gammaPolesRightOf a σ₁ ∪ gammaPolesRightOf b σ₁) \
          (gammaPolesRightOf a σ₂ ∪ gammaPolesRightOf b σ₂))) := by
  set P := (gammaPolesRightOf a σ₁ ∪ gammaPolesRightOf b σ₁) \
    (gammaPolesRightOf a σ₂ ∪ gammaPolesRightOf b σ₂)
  -- Remove the finitely many poles with `σ₁ - 1 < Re t` that are not in `P`.
  set Q := gammaPolesRightOf a (σ₁ - 1) ∪ gammaPolesRightOf b (σ₁ - 1)
  refine ⟨{t : ℂ | σ₁ - 1 < t.re ∧ t.re < 0} \ ↑(Q \ P),
    ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_re continuous_const)).sdiff (Finset.finite_toSet _).isClosed, ?_, ?_⟩
  · rintro t ⟨h₁, h₂⟩
    refine ⟨⟨by linarith, by linarith⟩, fun ht ↦ ?_⟩
    rw [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, Finset.mem_coe,
      mem_gammaPolesRightOf_union] at ht
    obtain ⟨⟨-, hk⟩, hnot⟩ := ht
    refine hnot (Finset.mem_sdiff.mpr ⟨mem_gammaPolesRightOf_union.mpr ⟨?_, hk⟩, fun h ↦ ?_⟩)
    · exact lt_of_le_of_ne h₁ (re_ne_of_pole ha₁ hb₁ hk).symm
    · exact absurd (mem_gammaPolesRightOf_union.mp h).1 (not_lt.mpr h₂)
  · rintro t ⟨⟨⟨h₁, h₂⟩, hU⟩, hP⟩
    have hpole {w : ℂ} (hw : ∀ m : ℕ, w + t = -m → t ∈ Q) : ∀ m : ℕ, w + t ≠ -m :=
      fun m hm ↦ hU (by rw [Finset.coe_sdiff]; exact ⟨Finset.mem_coe.mpr (hw m hm), hP⟩)
    refine (differentiableAt_hypergeometricMellinBarnesIntegrand hz
      (hpole fun m hm ↦ mem_gammaPolesRightOf_union.mpr ⟨h₁, m, .inl (by linear_combination hm)⟩)
      (hpole fun m hm ↦ mem_gammaPolesRightOf_union.mpr ⟨h₁, m, .inr (by linear_combination hm)⟩)
      fun m hm ↦ ?_).differentiableWithinAt
    have : t.re = m := by simpa using congrArg re (neg_injective hm)
    linarith [m.cast_nonneg' (α := ℝ)]

/-- The line shift for Barnes's integral, for `σ₁ ≤ σ₂`. -/
private theorem hypergeometricMellinBarnes_eq_of_le (a b c : ℂ) {z : ℂ} (hz : -z ∈ slitPlane)
    {σ₁ σ₂ : ℝ} (hle : σ₁ ≤ σ₂) (hσ₂ : σ₂ < 0) (ha₁ : ∀ n : ℕ, a.re + σ₁ ≠ -n)
    (hb₁ : ∀ n : ℕ, b.re + σ₁ ≠ -n) (ha₂ : ∀ n : ℕ, a.re + σ₂ ≠ -n)
    (hb₂ : ∀ n : ℕ, b.re + σ₂ ≠ -n) :
    hypergeometricMellinBarnes a b c z σ₁ = hypergeometricMellinBarnes a b c z σ₂ := by
  have hsub : gammaPolesRightOf a σ₂ ∪ gammaPolesRightOf b σ₂ ⊆
      gammaPolesRightOf a σ₁ ∪ gammaPolesRightOf b σ₁ := fun t ht ↦ by
    rw [mem_gammaPolesRightOf_union] at ht ⊢
    exact ⟨hle.trans_lt ht.1, ht.2⟩
  -- The poles strictly between the two lines.
  set P := (gammaPolesRightOf a σ₁ ∪ gammaPolesRightOf b σ₁) \
    (gammaPolesRightOf a σ₂ ∪ gammaPolesRightOf b σ₂)
  have hP : ∀ p ∈ P, σ₁ < p.re ∧ p.re < σ₂ := fun p hp ↦ by
    rw [Finset.mem_sdiff, mem_gammaPolesRightOf_union, mem_gammaPolesRightOf_union] at hp
    obtain ⟨⟨h₁, hk⟩, h₂⟩ := hp
    exact ⟨h₁, lt_of_le_of_ne (not_lt.mp fun h ↦ h₂ ⟨h, hk⟩) (re_ne_of_pole ha₂ hb₂ hk)⟩
  obtain ⟨U, hU, hstrip, hF⟩ := exists_differentiableOn_hypergeometricMellinBarnesIntegrand a b c
    (by simpa using slitPlane_ne_zero hz) hσ₂ ha₁ hb₁
  have hhor := (tendsto_hypergeometricMellinBarnesIntegrand_strip a b c hz σ₁ σ₂)
  rw [← uIcc_of_le hle] at hhor
  have hshift := TauCeti.Contour.integral_vertical_sub_eq_two_pi_mul_sum_residue _ hle hU hstrip
    P hP hF (fun p _ ↦ meromorphicAt_hypergeometricMellinBarnesIntegrand a b c z p)
    (integrable_hypergeometricMellinBarnesIntegrand a b c hz hσ₂ ha₂ hb₂)
    (integrable_hypergeometricMellinBarnesIntegrand a b c hz (hle.trans_lt hσ₂) ha₁ hb₁)
    (TauCeti.Contour.tendsto_intervalIntegral_horizontal
      (hhor.mono_left (prod_mono atTop_le_cocompact le_rfl)))
    (TauCeti.Contour.tendsto_intervalIntegral_horizontal
      (hhor.mono_left (prod_mono atBot_le_cocompact le_rfl)))
  set r := TauCeti.Contour.residue (hypergeometricMellinBarnesIntegrand a b c z)
  have h2π : (2 * π : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  rw [hypergeometricMellinBarnes_def, hypergeometricMellinBarnes_def, ← Finset.sum_sdiff hsub,
    show (∫ y : ℝ, hypergeometricMellinBarnesIntegrand a b c z (σ₁ + y * I)) =
      (∫ y : ℝ, hypergeometricMellinBarnesIntegrand a b c z (σ₂ + y * I)) - 2 * π * ∑ p ∈ P, r p by
    linear_combination -hshift, mul_sub, ← mul_assoc, inv_mul_cancel₀ h2π, one_mul]
  ring

/-- **Barnes's integral does not depend on the line.** For `-z ∈ slitPlane` and any two lines
`Re t = σ₁`, `Re t = σ₂` with `σ₁, σ₂ < 0` that avoid the poles of `Γ(a + t) Γ(b + t)`, the line
integral plus the residues at the poles of `Γ(a + t) Γ(b + t)` to the right of the line has the
same value. -/
theorem hypergeometricMellinBarnes_eq (a b c : ℂ) {z : ℂ} (hz : -z ∈ slitPlane) {σ₁ σ₂ : ℝ}
    (hσ₁ : σ₁ < 0) (hσ₂ : σ₂ < 0) (ha₁ : ∀ n : ℕ, a.re + σ₁ ≠ -n)
    (hb₁ : ∀ n : ℕ, b.re + σ₁ ≠ -n) (ha₂ : ∀ n : ℕ, a.re + σ₂ ≠ -n)
    (hb₂ : ∀ n : ℕ, b.re + σ₂ ≠ -n) :
    hypergeometricMellinBarnes a b c z σ₁ = hypergeometricMellinBarnes a b c z σ₂ := by
  rcases le_total σ₁ σ₂ with h | h
  · exact hypergeometricMellinBarnes_eq_of_le a b c hz h hσ₂ ha₁ hb₁ ha₂ hb₂
  · exact (hypergeometricMellinBarnes_eq_of_le a b c hz h hσ₁ ha₂ hb₂ ha₁ hb₁).symm

/-- **Barnes's integral for Euler's integral over a separating contour** (DLMF 15.6.6). For
`0 < Re a`, `0 < Re b < Re c` and `-z ∈ slitPlane`, Euler's integral is `(Γ(a) Γ(b))⁻¹` times
Barnes's integral over the line `Re t = σ` plus the residues at the poles of `Γ(a + t) Γ(b + t)`
to its right, for every `σ < 0` whose line avoids those poles. -/
theorem eulerIntegral_eq_hypergeometricMellinBarnes {a b c z : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hbc : b.re < c.re) (hz : -z ∈ slitPlane) {σ : ℝ} (hσ : σ < 0)
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) :
    eulerIntegral a b c z = (Gamma a * Gamma b)⁻¹ * hypergeometricMellinBarnes a b c z σ := by
  -- A line between `-min (Re a, Re b)` and `0`, with no poles to its right.
  set σ' := max (-a.re) (-b.re) / 2
  have ha' : -a.re < σ' := by have := le_max_left (-a.re) (-b.re); simp only [σ']; linarith
  have hb' : -b.re < σ' := by have := le_max_right (-a.re) (-b.re); simp only [σ']; linarith
  have hσ' : σ' < 0 := by simp only [σ']; linarith [max_lt (neg_neg_of_pos ha) (neg_neg_of_pos hb)]
  have hpa : ∀ n : ℕ, a.re + σ' ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  have hpb : ∀ n : ℕ, b.re + σ' ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  rw [hypergeometricMellinBarnes_eq a b c hz hσ hσ' haσ hbσ hpa hpb,
    hypergeometricMellinBarnes_eq_integral a b c z ha'.le hb'.le,
    eulerIntegral_eq_mellinBarnes a hbc hz hσ' ha' hb']
  simp only [hypergeometricMellinBarnesIntegrand_def, mul_inv]
  ring

/-! ### Residues -/

/-- The residue of Barnes's integrand at a pole `t = -a - k` of `Γ(a + t)` that is not a pole of
`Γ(b + t)` or of `Γ(-t)` (that is, neither `a + k` nor `b - a - k` is a nonpositive integer) is
`(-1)^k / k! · Γ(b - a - k) Γ(a + k) Γ(c - a - k)⁻¹ (-z)^(-a - k)`. -/
theorem residue_hypergeometricMellinBarnesIntegrand_neg_sub_natCast (c : ℂ) {a b z : ℂ} (k : ℕ)
    (ha : ∀ m : ℕ, a + k ≠ -m) (hab : ∀ m : ℕ, b - a - k ≠ -m) :
    TauCeti.Contour.residue (hypergeometricMellinBarnesIntegrand a b c z) (-a - k) =
      (-1) ^ k / k ! * (Gamma (b - a - k) * Gamma (a + k) * (Gamma (c - a - k))⁻¹ *
        (-z) ^ (-a - k)) := by
  set G : ℂ → ℂ := fun t ↦ Gamma (b + t) * Gamma (-t) * (Gamma (c + t))⁻¹ * (-z) ^ t
  have hF : hypergeometricMellinBarnesIntegrand a b c z =
      fun t ↦ (fun s ↦ Gamma s * G (s - a)) (t + a) := by
    ext t
    simp only [hypergeometricMellinBarnesIntegrand_def, G, add_comm t a, add_sub_cancel_left]
    ring
  have hG : AnalyticAt ℂ G (-a - k) := by
    have h1 : AnalyticAt ℂ (fun t ↦ Gamma (b + t)) (-a - k) :=
      (analyticAt_Gamma fun m hm ↦ hab m (by linear_combination hm)).comp (by fun_prop)
    -- `Γ(-t) (-z)^t` is analytic at `-a - k` also for `z = 0`, where `(-z)^t` vanishes near it.
    have h24 : AnalyticAt ℂ (fun t ↦ Gamma (-t) * (-z) ^ t) (-a - k) := by
      have := (analyticAt_Gamma_sub_mul_cpow (-z) (s₀ := a + k) (β := 0)
        fun m hm ↦ ha m (by linear_combination hm)).comp_of_eq
          (f := fun t : ℂ ↦ -t) (x := -a - k) (by fun_prop) (by ring)
      simpa [Function.comp_def] using this
    have h3 : AnalyticAt ℂ (fun t ↦ (Gamma (c + t))⁻¹) (-a - k) :=
      (differentiable_one_div_Gamma.analyticAt _).comp (by fun_prop)
    exact ((h1.mul h24).mul h3).congr
      (Eventually.of_forall fun t ↦ by simp only [G, Pi.mul_apply]; ring)
  have hw : AnalyticAt ℂ (fun s ↦ G (s - a)) (-(k : ℂ)) :=
    hG.comp_of_eq (g := G) (f := fun s ↦ s - a) (by fun_prop) (by ring)
  rw [hF, TauCeti.Contour.residue_comp_add_const (fun s ↦ Gamma s * G (s - a)),
    show -a - (k : ℂ) + a = -(k : ℂ) by ring, Complex.residue_Gamma_mul_neg_nat k hw]
  simp only [G]
  rw [show b + (-(k : ℂ) - a) = b - a - k by ring, show -(-(k : ℂ) - a) = a + k by ring,
    show c + (-(k : ℂ) - a) = c - a - k by ring, show -(k : ℂ) - a = -a - k by ring]

end Complex
