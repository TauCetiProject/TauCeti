/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Localization
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure

/-!
# The wave front set as the closure of the Sobolev wave front sets

A complex distribution `T` on an open set `Ω` that is microlocally smooth at `(x, ξ)` is
microlocally `H^s` there for every real `s`
(`Distribution.IsMicrolocallySmoothAt.isMicrolocallySobolevAt`). This file proves the converse,
which needs a neighbourhood independent of `s`: `T` is microlocally smooth at `(x, ξ)` exactly
when, for every `s`, it is microlocally `H^s` at every point of a neighbourhood of `(x, ξ)` that
does not depend on `s`
(`Distribution.isMicrolocallySmoothAt_iff_eventually_forall_isMicrolocallySobolevAt`).
Equivalently, the wave front set is the closure of the union of the `H^s` wave front sets inside
`Ω × (E \ {0})`:

`WF(T) = (Ω × (E \ {0})) ∩ closure (⋃ s, WF_s(T))`

(`Distribution.waveFrontSet_eq_inter_closure_iUnion_sobolevWaveFrontSet`). The closure is needed:
covectors at which `T` has singularities of ever higher Sobolev regularity can accumulate at a
covector `(x, ξ)` at which `T` is microlocally `H^s` for every `s`. In particular `T` has empty
wave front set exactly when every `H^s` wave front set is empty
(`Distribution.waveFrontSet_eq_empty_iff_forall_sobolevWaveFrontSet_eq_empty`).

This is how microlocal regularity on the Sobolev scale yields microlocal smoothness: combined with
a microlocal elliptic regularity estimate `WF_{s+m}(u) ⊆ WF_s(P u) ∪ Char(P)` valid for every `s`,
it gives `WF(u) ⊆ WF(P u) ∪ Char(P)`, since `WF(P u) ∪ Char(P)` is closed in `Ω × (E \ {0})`.

## The argument

Suppose `T` is microlocally `H^s` for every `s` on a neighbourhood of `(x, ξ)`, which contains
`closedBall x r ×ˢ closedBall ξ r` for some `r > 0`.

* **One cutoff and one cone for every order.** Fix `s`. The neighbourhoods and cones provided by
  `Distribution.IsMicrolocallySobolevAt.exists_nhds_cone` at the points of this compact set have
  finite subcovers, first in the frequency and then in the position. A partition of unity then
  shows that every cutoff supported in `ball x r` has weighted localized Fourier transform
  `⟨η⟩ ^ s T (ψ e_η)` square integrable on the open cone `Γ` over `ball ξ r`. Neither `ball x r`
  nor `Γ` depends on `s`
  (`Distribution.exists_nhds_cone_forall_memLp_of_eventually_forall_isMicrolocallySobolevAt`).
* **From square integrability of every order to rapid decay.** The localized Fourier transform
  `F = T (φ e_·)` is Lipschitz with a polynomially growing constant:
  `‖F η - F ζ‖ ≤ A (1 + ‖η‖) ^ k ‖η - ζ‖` for `‖η - ζ‖ ≤ 1`
  (`Distribution.exists_norm_localFourier_sub_le`), because `φ e_η - φ e_ζ` is `φ (1 - e_(ζ - η))`
  times `e_η`. On the closed ball of radius `δ = (1 + ‖η‖) ^ (-M)` about `η` the value `F η` is
  therefore within `A (1 + ‖η‖) ^ (k - M)` of `F`, and averaging `‖F‖ ^ 2` over that ball, which
  lies in `Γ` for `η` in a smaller cone, bounds `‖F η‖ ^ 2` by
  `δ ^ (-n) (1 + ‖η‖) ^ (-2 s)` times the weighted `L²` norm, plus `A² (1 + ‖η‖) ^ (2 (k - M))`.
  For `M` and then `s` large both terms are `O((1 + ‖η‖) ^ (-2 N))`
  (`TauCeti.exists_one_add_norm_pow_mul_norm_le_of_forall_memLp`).

## Main results

* `TauCeti.exists_one_add_norm_pow_mul_norm_le_of_forall_memLp`: a function that is Lipschitz with
  polynomially growing constant and whose weighted squares are integrable on `Γ` for every weight
  decays rapidly on every cone whose conic neighbourhoods lie in `Γ`.
* `Distribution.exists_nhds_cone_forall_memLp_of_eventually_forall_isMicrolocallySobolevAt`: one
  neighbourhood and one cone serve for every Sobolev order.
* `Distribution.isMicrolocallySmoothAt_iff_eventually_forall_isMicrolocallySobolevAt`,
  `Distribution.waveFrontSet_eq_inter_closure_iUnion_sobolevWaveFrontSet`,
  `Distribution.waveFrontSet_eq_empty_iff_forall_sobolevWaveFrontSet_eq_empty`: the wave front set
  from the Sobolev wave front sets.

## References

* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997,
  §11.1 (the `H^s` wave front set).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1.
-/

public section

noncomputable section

open Complex Filter Function Metric MeasureTheory Module Set TopologicalSpace TestFunction
open scoped Distributions Topology ContDiff RealInnerProductSpace

namespace TauCeti

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ G] in
/-- A function that is Lipschitz with a polynomially growing constant is continuous. -/
private theorem continuous_of_norm_sub_le {F : E → G} {A : ℝ} {k : ℕ}
    (hLip : ∀ η ζ, ‖η - ζ‖ ≤ 1 → ‖F η - F ζ‖ ≤ A * (1 + ‖η‖) ^ k * ‖η - ζ‖) :
    Continuous F := by
  refine continuous_iff_continuousAt.2 fun η ↦ Metric.continuousAt_iff.2 fun ε hε ↦ ?_
  set L := |A| * (1 + ‖η‖) ^ k + 1
  have hL : 0 < L := by positivity
  refine ⟨min 1 (ε / L), by positivity, fun {ζ} hζ ↦ ?_⟩
  have hd : ‖η - ζ‖ < min 1 (ε / L) := by rwa [← dist_eq_norm, dist_comm]
  have hAL : A * (1 + ‖η‖) ^ k ≤ L :=
    (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)).trans (le_add_of_nonneg_right
      zero_le_one)
  rw [dist_eq_norm, norm_sub_rev]
  calc ‖F η - F ζ‖ ≤ A * (1 + ‖η‖) ^ k * ‖η - ζ‖ := hLip η ζ (hd.le.trans (min_le_left _ _))
    _ ≤ L * ‖η - ζ‖ := mul_le_mul_of_nonneg_right hAL (norm_nonneg _)
    _ < L * (ε / L) := mul_lt_mul_of_pos_left (hd.trans_le (min_le_right _ _)) hL
    _ = ε := by field_simp

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ G] in
/-- The pointwise step: within distance `δ ≤ 1` of a frequency `η` with `‖η‖ ≥ 1`, the value
`F η` is within `b = |A| (1 + ‖η‖) ^ k δ` of `F ζ`, and the weight `(1 + ‖ζ‖ ^ 2) ^ σ` is at least
`((1 + ‖η‖) ^ 2 / 8) ^ σ`. -/
private theorem sq_norm_le_of_norm_sub_le {F : E → G} {A : ℝ} {k : ℕ}
    (hLip : ∀ η ζ, ‖η - ζ‖ ≤ 1 → ‖F η - F ζ‖ ≤ A * (1 + ‖η‖) ^ k * ‖η - ζ‖) {η ζ : E}
    (hη : 1 ≤ ‖η‖) {δ : ℝ} (hδ : δ ≤ 1) (hd : ‖η - ζ‖ ≤ δ) (σ : ℕ) :
    ‖F η‖ ^ 2 ≤ 2 / ((1 + ‖η‖) ^ 2 / 8) ^ (2 * σ) * (((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 * ‖F ζ‖ ^ 2) +
      2 * (|A| * (1 + ‖η‖) ^ k * δ) ^ 2 := by
  set b := |A| * (1 + ‖η‖) ^ k * δ
  have hFη : ‖F η‖ ≤ ‖F ζ‖ + b :=
    calc ‖F η‖ = ‖F ζ + (F η - F ζ)‖ := by rw [add_sub_cancel]
      _ ≤ ‖F ζ‖ + ‖F η - F ζ‖ := norm_add_le _ _
      _ ≤ ‖F ζ‖ + A * (1 + ‖η‖) ^ k * ‖η - ζ‖ := by gcongr; exact hLip η ζ (hd.trans hδ)
      _ ≤ ‖F ζ‖ + b := add_le_add le_rfl (by
        calc A * (1 + ‖η‖) ^ k * ‖η - ζ‖ ≤ |A| * (1 + ‖η‖) ^ k * ‖η - ζ‖ := by
              gcongr; exact le_abs_self A
          _ ≤ |A| * (1 + ‖η‖) ^ k * δ := by gcongr)
  -- `‖ζ‖ ≥ ‖η‖ - 1 ≥ 0`, so `1 + ‖ζ‖ ^ 2 ≥ (1 + ‖η‖) ^ 2 / 8`.
  have hw : (1 + ‖η‖) ^ 2 / 8 ≤ 1 + ‖ζ‖ ^ 2 := by
    have hζη : ‖η‖ - 1 ≤ ‖ζ‖ := by linarith [norm_sub_norm_le η ζ]
    nlinarith [mul_self_le_mul_self (sub_nonneg.2 hη) hζη, sq_nonneg (‖η‖ - 9 / 7)]
  have hw₀ : 0 < ((1 + ‖η‖) ^ 2 / 8) ^ (2 * σ) := by positivity
  have hW : ((1 + ‖η‖) ^ 2 / 8) ^ (2 * σ) ≤ ((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 := by
    rw [← pow_mul, mul_comm σ 2]
    exact pow_le_pow_left₀ (by positivity) hw _
  have hFζ : ‖F ζ‖ ^ 2 ≤
      ((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 * ‖F ζ‖ ^ 2 / ((1 + ‖η‖) ^ 2 / 8) ^ (2 * σ) := by
    rw [le_div_iff₀ hw₀, mul_comm]
    exact mul_le_mul_of_nonneg_right hW (sq_nonneg _)
  calc ‖F η‖ ^ 2 ≤ 2 * ‖F ζ‖ ^ 2 + 2 * b ^ 2 := by
        nlinarith [norm_nonneg (F η), norm_nonneg (F ζ), sq_nonneg (‖F ζ‖ - b)]
    _ ≤ 2 * (((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 * ‖F ζ‖ ^ 2 / ((1 + ‖η‖) ^ 2 / 8) ^ (2 * σ)) +
        2 * b ^ 2 := by gcongr
    _ = _ := by ring

omit [NormedSpace ℝ G] in
/-- The averaging step: a pointwise bound `a ≤ e g ζ + c` on a set `B ⊆ Γ` of finite measure,
with `g ≥ 0` integrable on `Γ` and `e ≥ 0`, gives `vol(B) a ≤ e ∫_Γ g + vol(B) c`. -/
private theorem measureReal_mul_le_mul_setIntegral_add {g : E → ℝ} {Γ B : Set E}
    (hB : MeasurableSet B) (hBfin : volume B ≠ ⊤) (hBΓ : B ⊆ Γ)
    (hg : Integrable g (volume.restrict Γ)) (hg0 : ∀ ζ, 0 ≤ g ζ) {a c e : ℝ} (he : 0 ≤ e)
    (h : ∀ ζ ∈ B, a ≤ e * g ζ + c) :
    volume.real B * a ≤ e * (∫ ζ in Γ, g ζ) + volume.real B * c := by
  have hgB : Integrable g (volume.restrict B) :=
    hg.mono_measure (Measure.restrict_mono_set volume hBΓ)
  have hle := setIntegral_ge_of_const_le hB hBfin h
    ((hgB.const_mul e).add (integrableOn_const hBfin))
  rw [integral_add (hgB.const_mul e) (integrableOn_const hBfin), integral_const_mul,
    setIntegral_const, smul_eq_mul, smul_eq_mul] at hle
  exact hle.trans (add_le_add (mul_le_mul_of_nonneg_left
    (setIntegral_mono_set hg (.of_forall hg0) (ae_of_all _ hBΓ)) he) le_rfl)

omit [NormedSpace ℝ G] in
/-- The estimate at a frequency `η` far from the origin: averaging the pointwise step over the
ball of radius `(1 + ‖η‖) ^ (-(N + k))` about `η`, which lies in `Γ`, bounds
`((1 + ‖η‖) ^ N ‖F η‖) ^ 2` by the weighted `L²` norm of order `4 σ` of `F` on `Γ`, where
`σ = d (N + k) + N` and `d` is the dimension. -/
private theorem sq_one_add_norm_pow_mul_norm_le {F : E → G} {A : ℝ} {k : ℕ}
    (hLip : ∀ η ζ, ‖η - ζ‖ ≤ 1 → ‖F η - F ζ‖ ≤ A * (1 + ‖η‖) ^ k * ‖η - ζ‖) {Γ : Set E}
    (N : ℕ) (hint : Integrable (fun ζ ↦ ((1 + ‖ζ‖ ^ 2) ^ (finrank ℝ E * (N + k) + N)) ^ 2 *
      ‖F ζ‖ ^ 2) (volume.restrict Γ)) {η : E} (hη : 1 ≤ ‖η‖) (hΓ : closedBall η 1 ⊆ Γ) :
    ((1 + ‖η‖) ^ N * ‖F η‖) ^ 2 ≤
      2 * (∫ ζ in Γ, ((1 + ‖ζ‖ ^ 2) ^ (finrank ℝ E * (N + k) + N)) ^ 2 * ‖F ζ‖ ^ 2) *
        8 ^ (2 * (finrank ℝ E * (N + k) + N)) / volume.real (ball (0 : E) 1) + 2 * A ^ 2 := by
  set d := finrank ℝ E
  set σ := d * (N + k) + N
  have ht1 : 1 ≤ 1 + ‖η‖ := by linarith [norm_nonneg η]
  have hδ0 : 0 < ((1 + ‖η‖) ^ (N + k))⁻¹ := by positivity
  have hδ1 : ((1 + ‖η‖) ^ (N + k))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ht1)
  have hle := measureReal_mul_le_mul_setIntegral_add measurableSet_closedBall
    measure_closedBall_lt_top.ne ((closedBall_subset_closedBall hδ1).trans hΓ) hint
    (fun ζ ↦ by positivity) (by positivity : (0 : ℝ) ≤ 2 / ((1 + ‖η‖) ^ 2 / 8) ^ (2 * σ))
    fun ζ hζ ↦
      sq_norm_le_of_norm_sub_le hLip hη hδ1 (by rw [← dist_eq_norm, dist_comm]; exact hζ) σ
  rw [Measure.addHaar_real_closedBall volume η hδ0.le] at hle
  -- Name the quantities of the estimate; `set` also abbreviates them in `hle`.
  set I := ∫ ζ in Γ, ((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 * ‖F ζ‖ ^ 2
  set v := volume.real (ball (0 : E) 1)
  have hv : 0 < v :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  set t := 1 + ‖η‖
  set δ := (t ^ (N + k))⁻¹
  set w₀ : ℝ := (t ^ 2 / 8) ^ (2 * σ)
  set b := |A| * t ^ k * δ
  have hmain : ‖F η‖ ^ 2 ≤ 2 / w₀ * I / (δ ^ d * v) + 2 * b ^ 2 := by
    rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    calc ‖F η‖ ^ 2 * (δ ^ d * v) = δ ^ d * v * ‖F η‖ ^ 2 := by ring
      _ ≤ 2 / w₀ * I + δ ^ d * v * (2 * b ^ 2) := hle
      _ = 2 / w₀ * I + 2 * b ^ 2 * (δ ^ d * v) := by ring
  -- The powers of `t` cancel, since `2 N + (N + k) d ≤ 4 σ` and `M = N + k`.
  have key₁ : t ^ (2 * N) ≤ 8 ^ (2 * σ) * (w₀ * δ ^ d) := by
    have h : 8 ^ (2 * σ) * (w₀ * δ ^ d) = t ^ (4 * σ) / t ^ ((N + k) * d) := by
      simp only [w₀, δ, div_pow, inv_pow, ← pow_mul]
      field_simp
      ring
    rw [h, le_div_iff₀ (by positivity), ← pow_add]
    exact pow_le_pow_right₀ ht1 (by
      simp only [σ]; nlinarith [Nat.zero_le (d * N), Nat.zero_le (d * k)])
  have key₂ : b ^ 2 * t ^ (2 * N) = A ^ 2 := by
    simp only [b, δ, mul_pow, sq_abs, inv_pow]
    field_simp
    ring
  calc (t ^ N * ‖F η‖) ^ 2 = t ^ (2 * N) * ‖F η‖ ^ 2 := by ring
    _ ≤ t ^ (2 * N) * (2 / w₀ * I / (δ ^ d * v) + 2 * b ^ 2) := by gcongr
    _ = 2 * I / v * (t ^ (2 * N) / (w₀ * δ ^ d)) + 2 * (b ^ 2 * t ^ (2 * N)) := by
      field_simp
    _ ≤ 2 * I / v * 8 ^ (2 * σ) + 2 * A ^ 2 := by
      rw [key₂]
      gcongr
      rw [div_le_iff₀ (by positivity)]
      exact key₁
    _ = 2 * I * 8 ^ (2 * σ) / v + 2 * A ^ 2 := by ring

/-- **Rapid decay from square integrability of every order.** Let `F` be Lipschitz with a
polynomially growing constant, `‖F η - F ζ‖ ≤ A (1 + ‖η‖) ^ k ‖η - ζ‖` for `‖η - ζ‖ ≤ 1`, and let
`⟨η⟩ ^ s F η` be square integrable on a set `Γ` for every real `s`, where
`⟨η⟩ ^ s = (1 + ‖η‖ ^ 2) ^ (s / 2)`. If for some `c > 0` the closed ball of radius `c ‖η‖` about
every point `η` of `Γ'` lies in `Γ`, then `F` decays rapidly on `Γ'`. -/
theorem exists_one_add_norm_pow_mul_norm_le_of_forall_memLp {F : E → G} {A : ℝ} {k : ℕ}
    (hLip : ∀ η ζ, ‖η - ζ‖ ≤ 1 → ‖F η - F ζ‖ ≤ A * (1 + ‖η‖) ^ k * ‖η - ζ‖)
    {Γ Γ' : Set E} {c : ℝ} (hc : 0 < c) (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ)
    (hL : ∀ s : ℝ, MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • F η) 2 (volume.restrict Γ))
    (N : ℕ) : ∃ C, ∀ η ∈ Γ', (1 + ‖η‖) ^ N * ‖F η‖ ≤ C := by
  set σ : ℕ := finrank ℝ E * (N + k) + N
  -- The weighted squares of order `4 σ` are integrable on `Γ`.
  have hint : Integrable (fun ζ ↦ ((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 * ‖F ζ‖ ^ 2) (volume.restrict Γ) := by
    refine ((hL (2 * σ)).integrable_norm_pow two_ne_zero).congr (.of_forall fun ζ ↦ ?_)
    have h2 : (2 * (σ : ℝ)) / 2 = σ := by ring
    simp only [h2, Real.rpow_natCast, norm_smul, mul_pow,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + ‖ζ‖ ^ 2) ^ σ)]
  -- Near the origin `F` is bounded; far from it, `closedBall η 1 ⊆ Γ` for `η ∈ Γ'`.
  set R₀ := max 1 c⁻¹
  obtain ⟨C₁, hC₁⟩ := (isCompact_closedBall (0 : E) R₀).exists_bound_of_continuousOn
    (continuous_of_norm_sub_le hLip).continuousOn
  refine ⟨max (Real.sqrt (2 * (∫ ζ in Γ, ((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 * ‖F ζ‖ ^ 2) * 8 ^ (2 * σ) /
    volume.real (ball (0 : E) 1) + 2 * A ^ 2)) ((1 + R₀) ^ N * C₁), fun η hη ↦ ?_⟩
  rcases lt_or_ge ‖η‖ R₀ with hsmall | hlarge
  · exact le_max_of_le_right (mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) N)
      (hC₁ η (by simpa using hsmall.le)) (norm_nonneg _) (by positivity))
  have hct : 1 ≤ c * ‖η‖ :=
    calc 1 = c * c⁻¹ := (mul_inv_cancel₀ hc.ne').symm
      _ ≤ c * ‖η‖ := by gcongr; exact (le_max_right _ _).trans hlarge
  exact le_max_of_le_left ((le_abs_self _).trans (Real.abs_le_sqrt
    (sq_one_add_norm_pow_mul_norm_le hLip N hint ((le_max_left _ _).trans hlarge)
      ((closedBall_subset_closedBall hct).trans (hΓ' η hη)))))

end TauCeti

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-- **One cutoff and one cone for every Sobolev order.** If `T` is microlocally `H^s` for every
`s` at every point of a neighbourhood of `(x, ξ)`, then there are a neighbourhood `U` of `x` and an
open cone `Γ` containing `ξ`, both independent of `s`, such that for every `s` and every cutoff `ψ`
supported in `U` the weighted localized Fourier transform `⟨η⟩ ^ s T (ψ e_η)` is square integrable
on `Γ`. -/
theorem exists_nhds_cone_forall_memLp_of_eventually_forall_isMicrolocallySobolevAt
    {T : 𝓓'(Ω, ℂ)} {x ξ : E} (h : ∀ᶠ p in 𝓝 (x, ξ), ∀ s, T.IsMicrolocallySobolevAt s p.1 p.2) :
    ∃ U ∈ 𝓝 x, ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∀ s : ℝ, ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
        MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier ψ η) 2 (volume.restrict Γ) := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 h
  set r := ρ / 2
  have hr : 0 < r := half_pos hρ
  have hreg : ∀ y ∈ closedBall x r, ∀ η ∈ closedBall ξ r, ∀ s,
      T.IsMicrolocallySobolevAt s y η := fun y hy η hη ↦ hball (show (y, η) ∈ ball (x, ξ) ρ by
    rw [mem_ball, Prod.dist_eq]
    exact max_lt (lt_of_le_of_lt hy (half_lt_self hρ)) (lt_of_le_of_lt hη (half_lt_self hρ)))
  -- `Γ` is the open cone over `ball ξ r`.
  set Γ : Set E := ⋃ t ∈ Ioi (0 : ℝ), (t • ·) ⁻¹' ball ξ r
  have hmem {η : E} : η ∈ Γ ↔ ∃ t : ℝ, 0 < t ∧ t • η ∈ ball ξ r := by simp [Γ]
  have hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ := fun t ht η hη ↦ by
    obtain ⟨u, hu, huη⟩ := hmem.1 hη
    exact hmem.2 ⟨u / t, div_pos hu ht, by rwa [smul_smul, div_mul_cancel₀ _ ht.ne']⟩
  refine ⟨ball x r, ball_mem_nhds x hr, Γ,
    isOpen_biUnion fun t _ ↦ isOpen_ball.preimage (continuous_const_smul t),
    hmem.2 ⟨1, one_pos, by simpa using hr⟩, hcone, fun s ↦ ?_⟩
  -- Over each point of `closedBall x r`: finitely many cones cover `closedBall ξ r`, hence `Γ`.
  have hinner : ∀ y ∈ closedBall x r, ∃ V ∈ 𝓝 y, ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ V →
      MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier ψ η) 2 (volume.restrict Γ) := by
    intro y hy
    choose U hU Γ' hΓ' hηΓ' hcone' hL using fun η : closedBall ξ r ↦
      (hreg y hy η η.2 s).exists_nhds_cone
    obtain ⟨t, ht⟩ := (isCompact_closedBall ξ r).elim_finite_subcover
      (fun η : closedBall ξ r ↦ Γ' η) hΓ' fun η hη ↦ mem_iUnion.2 ⟨⟨η, hη⟩, hηΓ' _⟩
    refine ⟨⋂ η ∈ t, U η, (biInter_finset_mem t).2 fun η _ ↦ hU η, fun ψ hψ ↦ ?_⟩
    refine MemLp.restrict_of_subset_iUnion (t := fun η : t ↦ Γ' η) (fun ζ hζ ↦ ?_)
      fun η ↦ hL η ψ (hψ.trans (biInter_subset_of_mem η.2))
    obtain ⟨u, hu, huζ⟩ := hmem.1 hζ
    obtain ⟨η, hηt, hη⟩ := mem_iUnion₂.1 (ht (ball_subset_closedBall huζ))
    refine mem_iUnion.2 ⟨⟨η, hηt⟩, ?_⟩
    simpa [smul_smul, inv_mul_cancel₀ hu.ne'] using hcone' η u⁻¹ (inv_pos.2 hu) _ hη
  choose! V hV hVL using hinner
  -- A partition of unity reduces a cutoff supported in `ball x r` to these neighbourhoods.
  intro ψ hψ
  have hcover : tsupport ψ ⊆ ⋃ y : closedBall x r, interior (V y) := fun z hz ↦
    have hz' : z ∈ closedBall x r := ball_subset_closedBall (hψ hz)
    mem_iUnion.2 ⟨⟨z, hz'⟩, mem_interior_iff_mem_nhds.2 (hV z hz')⟩
  obtain ⟨t, ψ', hψ'supp, hψ'sum, -⟩ :=
    ψ.exists_sum_subordinate _ (fun _ ↦ isOpen_interior) hcover
  have hsum : ∀ η, T.localFourier ψ η = ∑ i, T.localFourier (ψ' i) η := fun η ↦ by
    rw [← hψ'sum, localFourier_sum_cutoff]
  simp_rw [hsum, Finset.smul_sum]
  exact memLp_finsetSum _ fun i _ ↦ hVL _ i.1.2 _ ((hψ'supp i).trans interior_subset)

/-- **Microlocal smoothness from every Sobolev order.** If `T` is microlocally `H^s` for every
`s` at every point of a neighbourhood of `(x, ξ)`, then `T` is microlocally smooth at `(x, ξ)`. -/
theorem isMicrolocallySmoothAt_of_eventually_forall_isMicrolocallySobolevAt {T : 𝓓'(Ω, ℂ)}
    {x ξ : E} (h : ∀ᶠ p in 𝓝 (x, ξ), ∀ s, T.IsMicrolocallySobolevAt s p.1 p.2) :
    T.IsMicrolocallySmoothAt x ξ := by
  have hx : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySobolevAt_iff.1 (h.self_of_nhds 0)
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hL⟩ :=
    exists_nhds_cone_forall_memLp_of_eventually_forall_isMicrolocallySobolevAt h
  obtain ⟨Γ', hΓ'o, hξ', hcone', c, hc, hΓ'⟩ := hΓ.exists_cone_closedBall_subset hcone hξ
  obtain ⟨φ, hφ, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem hU (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
  obtain ⟨A, k, hLip⟩ := exists_norm_localFourier_sub_le T φ
  exact isMicrolocallySmoothAt_iff.2 ⟨φ, by simp [hφx], Γ', hΓ'o, hξ', hcone', fun N ↦
    TauCeti.exists_one_add_norm_pow_mul_norm_le_of_forall_memLp hLip hc hΓ'
      (fun s ↦ hL s φ (hφ.trans inter_subset_left)) N⟩

/-- A complex distribution is microlocally smooth at `(x, ξ)` exactly when, for every `s`, it is
microlocally `H^s` at every point of a neighbourhood of `(x, ξ)` that does not depend on `s`. -/
theorem isMicrolocallySmoothAt_iff_eventually_forall_isMicrolocallySobolevAt {T : 𝓓'(Ω, ℂ)}
    {x ξ : E} :
    T.IsMicrolocallySmoothAt x ξ ↔ ∀ᶠ p in 𝓝 (x, ξ), ∀ s, T.IsMicrolocallySobolevAt s p.1 p.2 :=
  ⟨fun h ↦ Filter.mem_of_superset
    (T.isOpen_setOf_isMicrolocallySmoothAt.mem_nhds (x := (x, ξ)) h) fun _ hp s ↦
      hp.isMicrolocallySobolevAt s,
    isMicrolocallySmoothAt_of_eventually_forall_isMicrolocallySobolevAt⟩

/-- **The wave front set is the closure of the union of the `H^s` wave front sets** inside
`Ω × (E \ {0})`. The closure is needed, because covectors at which `T` has singularities of ever
higher Sobolev regularity can accumulate. -/
theorem waveFrontSet_eq_inter_closure_iUnion_sobolevWaveFrontSet (T : 𝓓'(Ω, ℂ)) :
    T.waveFrontSet = ((Ω : Set E) ×ˢ {0}ᶜ) ∩ closure (⋃ s, T.sobolevWaveFrontSet s) := by
  ext ⟨x, ξ⟩
  rw [mem_waveFrontSet_iff, mem_inter_iff, mem_prod, mem_compl_singleton_iff]
  refine ⟨fun ⟨hx, hξ, hT⟩ ↦ ⟨⟨hx, hξ⟩, mem_closure_iff_nhds.2 fun W hW ↦ ?_⟩,
    fun ⟨⟨hx, hξ⟩, hcl⟩ ↦ ⟨hx, hξ, fun hT ↦ ?_⟩⟩
  · -- Otherwise `T` is microlocally `H^s` for every `s` on a neighbourhood of `(x, ξ)`.
    by_contra hW'
    refine hT (isMicrolocallySmoothAt_of_eventually_forall_isMicrolocallySobolevAt ?_)
    filter_upwards [hW, (Ω.isOpen.prod isOpen_compl_singleton).mem_nhds (mem_prod.2 ⟨hx, hξ⟩)]
      with ⟨y, η⟩ hpW hp s
    by_contra hs
    rw [mem_prod, mem_compl_singleton_iff] at hp
    exact hW' ⟨(y, η), hpW, mem_iUnion.2 ⟨s, mem_sobolevWaveFrontSet_iff.2 ⟨hp.1, hp.2, hs⟩⟩⟩
  · obtain ⟨p, hp, hpS⟩ := mem_closure_iff_nhds.1 hcl _
      (isMicrolocallySmoothAt_iff_eventually_forall_isMicrolocallySobolevAt.1 hT)
    obtain ⟨s, hs⟩ := mem_iUnion.1 hpS
    exact (mem_sobolevWaveFrontSet_iff.1 hs).2.2 (hp s)

/-- A complex distribution has empty wave front set exactly when all its `H^s` wave front sets are
empty. -/
theorem waveFrontSet_eq_empty_iff_forall_sobolevWaveFrontSet_eq_empty (T : 𝓓'(Ω, ℂ)) :
    T.waveFrontSet = ∅ ↔ ∀ s, T.sobolevWaveFrontSet s = ∅ := by
  refine ⟨fun h s ↦ subset_empty_iff.1 (h ▸ T.sobolevWaveFrontSet_subset_waveFrontSet s),
    fun h ↦ ?_⟩
  rw [waveFrontSet_eq_inter_closure_iUnion_sobolevWaveFrontSet]
  simp [h]

end Distribution
