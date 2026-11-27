/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor
import TauCeti.Analysis.Distribution.TemperedDistribution.Bernstein
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.Support
import TauCeti.MeasureTheory.Function.Holder

/-!
# Uniqueness of distributional solutions of the Schrödinger equation in `L¹_t L^r_x`

On a finite-dimensional real inner product space `E`, a function `u` of time with values in the
tempered distributions `𝓢'(E, F)` solves the free Schrödinger equation `i ∂ₜu + Δu = 0` with
`u(0) = 0` in the sense of distributions in space on `[0, T]` when, for every Schwartz function
`φ` and every `t ∈ [0, T]`,

`u(t)(φ) = i ∫_{(0,t]} u(s)(Δφ) ds`,

the integrated form of `∂ₜu = iΔu` tested against `φ`. This file proves that such a solution
vanishes on `[0, T]` as soon as it is integrable in time against an `Lᵖ` norm of the test
function: `‖u(s)(φ)‖ ≤ m(s) ‖φ‖_p` on `(0, T]` with `m` integrable
(`TauCeti.eqOn_zero_of_forall_apply_eq_I_smul_setIntegral_apply_laplacian`). No continuity in time
is assumed.

For a function `u` of time with values in `L^r(E, F)`, `1 ≤ r ≤ ∞`, Hölder's inequality gives this
bound with `m(s) = ‖u(s)‖_r` and the conjugate exponent `p`, so a solution in `L¹((0, T); L^r)`
vanishes
(`TauCeti.eqOn_zero_of_forall_integral_smul_eq_I_smul_setIntegral_integral_laplacian_smul`).
On the bounded interval `(0, T)` this contains every Strichartz class `L^q((0, T); L^r)`, `q ≥ 1`.
Applied to the difference of two solutions of the inhomogeneous equation with the same initial
value and forcing, whose pairings with Schwartz functions are integrable in time, it gives
uniqueness for the Cauchy problem in these classes. The solutions need not take values in `L²`,
unlike in
`TauCeti.eqOn_zero_of_forall_inner_toLp_eq_I_mul_setIntegral_inner_toLp_laplacian`, where `u` is
continuous with values in `L²`.

## The argument

The weak formulation can be iterated: by induction on `k`,

`‖u(t)(φ)‖ ≤ ‖Δᵏ⁺¹ φ‖_p M tᵏ / k!`, `M = ∫_{(0,T]} |m|`,

since each step integrates the bound of the previous one against `ds` over `(0, t]`. If the Fourier
transform of `φ` vanishes outside a ball of radius `R`, Bernstein's inequality for the Laplacian
(`TauCeti.exists_norm_toLp_iterate_laplacian_le_of_isVanishingOn_fourier`) gives
`‖Δᵏ⁺¹ φ‖_p ≤ (C R²)ᵏ⁺¹ ‖φ‖_p`, and `(C R² t)ᵏ / k! → 0`. So `u(t)` vanishes on every Schwartz
function whose Fourier transform has compact support, and such functions determine a tempered
distribution (`TemperedDistribution.eq_zero_of_forall_hasCompactSupport_fourier`).

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3.
-/

public section

noncomputable section

open MeasureTheory Set Complex Filter Topology TemperedDistribution
open scoped FourierTransform Laplacian SchwartzMap ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **The iterated weak formulation.** A solution of `u(t)(φ) = i ∫_{(0,t]} u(s)(Δφ) ds` with
`‖u(s)(φ)‖ ≤ m(s) ‖φ‖_p` satisfies `‖u(t)(φ)‖ ≤ ‖Δᵏ⁺¹ φ‖_p M tᵏ / k!` on `[0, T]`, where
`M = ∫_{(0,T]} |m|`. -/
private theorem norm_apply_le_of_forall_apply_eq {u : ℝ → 𝓢'(E, F)} {T : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {m : ℝ → ℝ} (hm : IntegrableOn m (Ioc 0 T))
    (hbound : ∀ s ∈ Ioc 0 T, ∀ φ : 𝓢(E, ℂ), ‖u s φ‖ ≤ m s * ‖φ.toLp p‖)
    (h : ∀ φ : 𝓢(E, ℂ), ∀ t ∈ Icc 0 T, u t φ = I • ∫ s in Ioc 0 t, u s (Δ φ)) (k : ℕ) :
    ∀ (φ : 𝓢(E, ℂ)) {t : ℝ}, t ∈ Icc 0 T →
      ‖u t φ‖ ≤ ‖(Δ^[k + 1] φ : 𝓢(E, ℂ)).toLp p volume‖ * (∫ s in Ioc 0 T, |m s|) * t ^ k /
        k.factorial := by
  induction k with
  | zero =>
    intro φ t ht
    have hint : IntegrableOn (fun s ↦ |m s| * ‖(Δ φ : 𝓢(E, ℂ)).toLp p volume‖) (Ioc 0 t) :=
      IntegrableOn.mono_set (hm.abs.mul_const _) (Ioc_subset_Ioc_right ht.2)
    calc ‖u t φ‖ = ‖∫ s in Ioc 0 t, u s (Δ φ)‖ := by rw [h φ t ht, norm_smul, norm_I, one_mul]
      _ ≤ ∫ s in Ioc 0 t, |m s| * ‖(Δ φ : 𝓢(E, ℂ)).toLp p volume‖ :=
        norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem measurableSet_Ioc
          fun s hs ↦ (hbound s ⟨hs.1, hs.2.trans ht.2⟩ (Δ φ)).trans
            (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)))
      _ = ‖(Δ φ : 𝓢(E, ℂ)).toLp p volume‖ * ∫ s in Ioc 0 t, |m s| := by
        rw [integral_mul_const, mul_comm]
      _ ≤ ‖(Δ φ : 𝓢(E, ℂ)).toLp p volume‖ * ∫ s in Ioc 0 T, |m s| :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_set hm.abs
          (ae_of_all _ fun _ ↦ abs_nonneg _)
          (Eventually.of_forall fun _ hx ↦ Ioc_subset_Ioc_right ht.2 hx)) (norm_nonneg _)
      _ = _ := by simp
  | succ k ih =>
    intro φ t ht
    obtain ⟨c, hc⟩ : ∃ c : ℝ,
        c = ‖(Δ^[k + 1 + 1] φ : 𝓢(E, ℂ)).toLp p volume‖ * (∫ s in Ioc 0 T, |m s|) /
          k.factorial :=
      ⟨_, rfl⟩
    have hint : IntegrableOn (fun s ↦ c * s ^ k) (Ioc 0 t) :=
      ((continuous_const.mul (continuous_pow k)).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    -- Integrate the bound for `Δ φ` over `(0, t]`.
    calc ‖u t φ‖ = ‖∫ s in Ioc 0 t, u s (Δ φ)‖ := by rw [h φ t ht, norm_smul, norm_I, one_mul]
      _ ≤ ∫ s in Ioc 0 t, c * s ^ k :=
        norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem measurableSet_Ioc
          fun s hs ↦ by
            have hs' := ih (Δ φ) ⟨hs.1.le, hs.2.trans ht.2⟩
            rw [← Function.iterate_succ_apply] at hs'
            exact hs'.trans_eq (by rw [hc]; ring))
      _ = c * (t ^ (k + 1) / (k + 1)) := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le ht.1, integral_pow]
        simp
      _ = ‖(Δ^[k + 1 + 1] φ : 𝓢(E, ℂ)).toLp p volume‖ * (∫ s in Ioc 0 T, |m s|) *
            t ^ (k + 1) / (k + 1).factorial := by
        simp only [hc, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        field_simp

/-- **Uniqueness for the Schrödinger equation in the sense of distributions.** Let
`u : ℝ → 𝓢'(E, F)` solve the free Schrödinger equation `i ∂ₜu + Δu = 0` with `u(0) = 0` in the
sense of distributions in space on `[0, T]`: for every Schwartz function `φ` and every
`t ∈ [0, T]`,

`u(t)(φ) = i ∫_{(0,t]} u(s)(Δφ) ds`.

If for some `1 ≤ p ≤ ∞` and some `m` integrable on `(0, T]` the bound `‖u(s)(φ)‖ ≤ m(s) ‖φ‖_p`
holds for every `s ∈ (0, T]` and every Schwartz `φ`, then `u = 0` on `[0, T]`. -/
theorem eqOn_zero_of_forall_apply_eq_I_smul_setIntegral_apply_laplacian {u : ℝ → 𝓢'(E, F)}
    {T : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {m : ℝ → ℝ} (hm : IntegrableOn m (Ioc 0 T))
    (hbound : ∀ s ∈ Ioc 0 T, ∀ φ : 𝓢(E, ℂ), ‖u s φ‖ ≤ m s * ‖φ.toLp p‖)
    (h : ∀ φ : 𝓢(E, ℂ), ∀ t ∈ Icc 0 T, u t φ = I • ∫ s in Ioc 0 t, u s (Δ φ)) :
    EqOn u 0 (Icc 0 T) := by
  obtain ⟨C, -, hB⟩ :=
    exists_norm_toLp_iterate_laplacian_le_of_isVanishingOn_fourier (E := E) (F := ℂ)
  intro t ht
  refine eq_zero_of_forall_hasCompactSupport_fourier fun φ hφ ↦ ?_
  -- The Fourier transform of `φ` vanishes outside a closed ball.
  obtain ⟨R, hR, hφR⟩ := exists_pos_isVanishingOn_fourier_compl_closedBall_of_hasCompactSupport hφ
  -- Iterate the weak formulation and apply Bernstein's inequality to `Δᵏ⁺¹ φ`.
  set M := ∫ s in Ioc 0 T, |m s|
  have hle (k : ℕ) : ‖u t φ‖ ≤
      C * R ^ 2 * ‖φ.toLp p volume‖ * M * ((C * R ^ 2 * t) ^ k / k.factorial) := by
    have hA := norm_apply_le_of_forall_apply_eq hm hbound h k φ ht
    have hMt : 0 ≤ M * t ^ k / k.factorial := by
      have := pow_nonneg ht.1 k
      positivity
    have hBk := mul_le_mul_of_nonneg_right (hB (p := p) hR (k + 1) φ hφR) hMt
    calc ‖u t φ‖ ≤ ‖(Δ^[k + 1] φ : 𝓢(E, ℂ)).toLp p volume‖ * (M * t ^ k / k.factorial) := by
          simpa only [mul_div_assoc, mul_assoc] using hA
      _ ≤ (C * R ^ 2) ^ (k + 1) * ‖φ.toLp p volume‖ * (M * t ^ k / k.factorial) := hBk
      _ = C * R ^ 2 * ‖φ.toLp p volume‖ * M * ((C * R ^ 2 * t) ^ k / k.factorial) := by ring
  -- The bounds tend to zero, since `xᵏ / k! → 0`.
  have hlim := (FloorSemiring.tendsto_pow_div_factorial_atTop (C * R ^ 2 * t)).const_mul
    (C * R ^ 2 * ‖φ.toLp p volume‖ * M)
  rw [mul_zero] at hlim
  exact norm_le_zero_iff.1 (ge_of_tendsto' hlim hle)

/-- **Uniqueness for the Schrödinger equation in `L¹_t L^r_x`.** Let `1 ≤ r ≤ ∞` and let
`u : ℝ → L^r(E, F)` have `s ↦ ‖u(s)‖_r` integrable on `(0, T]`. If `u` solves the free Schrödinger
equation `i ∂ₜu + Δu = 0` with `u(0) = 0` in the sense of distributions in space on `[0, T]`: for
every Schwartz function `φ` and every `t ∈ [0, T]`,

`∫ φ u(t) = i ∫_{(0,t]} ∫ (Δφ) u(s) ds`,

then `u = 0` on `[0, T]`. This covers every Strichartz class `L^q((0, T); L^r)` with `q ≥ 1`; no
continuity in time is assumed. -/
theorem eqOn_zero_of_forall_integral_smul_eq_I_smul_setIntegral_integral_laplacian_smul
    [CompleteSpace F] {r : ℝ≥0∞} [Fact (1 ≤ r)] {T : ℝ} {u : ℝ → Lp F r (volume : Measure E)}
    (hu : IntegrableOn (fun s ↦ ‖u s‖) (Ioc 0 T))
    (h : ∀ φ : 𝓢(E, ℂ), ∀ t ∈ Icc 0 T, ∫ x, φ x • u t x =
      I • ∫ s in Ioc 0 t, ∫ x, (Δ φ) x • u s x) :
    EqOn u 0 (Icc 0 T) := by
  -- Pair with Schwartz functions in the conjugate exponent `r'`.
  set r' : ℝ≥0∞ := (1 - r⁻¹)⁻¹
  have hr' : r'.HolderConjugate r := (ENNReal.HolderConjugate.inv_one_sub_inv' Fact.out).symm
  have : Fact (1 ≤ r') := ⟨hr'.one_le⟩
  have h0 := eqOn_zero_of_forall_apply_eq_I_smul_setIntegral_apply_laplacian
    (u := fun t ↦ (u t : 𝓢'(E, F))) (p := r') hu (fun s _ φ ↦ ?_) fun φ t ht ↦ ?_
  · intro t ht
    exact Lp.toTemperedDistribution_injective (by simpa using h0 ht)
  · -- Hölder's inequality `‖∫ φ u(s)‖ ≤ ‖φ‖_{r'} ‖u(s)‖_r`.
    rw [Lp.toTemperedDistribution_apply, mul_comm, SchwartzMap.norm_toLp, Lp.norm_def,
      ← ENNReal.toReal_mul, ← toReal_eNorm]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (φ.memLp r' volume).eLpNorm_ne_top
      (Lp.memLp _).eLpNorm_ne_top) enorm_integral_smul_le
  · simpa only [Lp.toTemperedDistribution_apply] using h φ t ht

end TauCeti
