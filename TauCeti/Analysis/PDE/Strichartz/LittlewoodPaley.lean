/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.LittlewoodPaley
import TauCeti.Analysis.SpecificLimits.DyadicSum
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Function.LpSeminorm.SquareSum

/-!
# Summing frequency-localized mixed-norm estimates over Littlewood–Paley blocks

Let `V` be a nontrivial finite-dimensional real inner product space, let `Pⱼ`, `j ∈ ℤ`, be the
`L²` Fourier multipliers with the homogeneous Littlewood–Paley cutoffs `ψⱼ`
(`ContDiffBump.littlewoodPaley`) as symbols, and let `T(b)`, `b ∈ β`, be a measurable family of
bounded operators on `L²(V, F)`. Strichartz estimates are first proved for frequency-localized
data, in the form

`‖T(·) Pₖ x‖_{L^q_b L^r_x} ≤ C 2^{kσ} ‖x‖₂` for every `k ∈ ℤ` and `x ∈ L²`,

with `C` independent of the scale `k`. This file sums such estimates over the blocks: they imply

`‖T(·) f‖_{L^q_b L^r_x} ≤ K C ∑ⱼ 2^{jσ} ‖Pⱼ f‖₂`

for every `f ∈ L²` (`ContDiffBump.exists_eLpNorm_eLpNorm_le_mul_tsum`), where `K` depends only on
the bump function and on `σ`, and `1 ≤ q, r`. The right-hand side is the norm of `f` in the
homogeneous Besov space `\dot B^σ_{2,1}`, written through the blocks of `f`. Since it is an `ℓ¹`
sum rather than a square function, no Littlewood–Paley inequality in `L^r` is needed, and the
exponent `r = ∞` is allowed.

For `2 ≤ q ≤ ∞`, `2 ≤ r < ∞` and operators `T(b)` commuting with the blocks, the `ℓ¹` sum improves
to the square sum:

`‖T(·) f‖_{L^q_b L^r_x} ≤ K C (∑ⱼ 2^{2jσ} ‖Pⱼ f‖₂²)^{1/2}`

(`ContDiffBump.exists_eLpNorm_eLpNorm_le_mul_tsum_sq_rpow`), where `K` now also depends on `r`. The
right-hand side is the Littlewood–Paley form of the norm of `f` in the homogeneous Sobolev space
`\dot H^σ`.

`ContDiffBump.exists_eLpNorm_eLpNorm_le_tsum_of_littlewoodPaley_le_of_one_le` and
`ContDiffBump.exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_littlewoodPaley_le` state both summations
for a single family `T(b)` whose frequency-localized estimates hold with some constant, absorbing
`K C` into one constant; this is the form used by the Strichartz estimates for the wave equation.

## The argument

The block `Pⱼ f` is reproduced by its neighbouring blocks, `Pⱼ f = ∑_{|k - j| < L} Pₖ Pⱼ f`
(`ContDiffBump.sum_fourierMultiplierCLM_fourierMultiplierCLM_littlewoodPaley`), so the
frequency-localized estimate applied to `x = Pⱼ f` bounds `‖T(·) Pⱼ f‖_{L^q L^r}` by
`K C 2^{jσ} ‖Pⱼ f‖₂`. The partial sums of the blocks converge to `f` in `L²`
(`ContDiffBump.tendsto_sum_fourierMultiplierCLM_littlewoodPaley`), and the `L^r` seminorm is lower
semicontinuous on `L²` (`TauCeti.lowerSemicontinuous_eLpNorm_Lp`), so at each `b`,
`‖T(b) f‖_r ≤ ∑ⱼ ‖T(b) Pⱼ f‖_r`. Minkowski's inequality for countable sums in `L^q`
(`eLpNorm_tsum_le`) finishes the proof.

For the square sum, the reverse Littlewood–Paley inequality
(`TauCeti.exists_eLpNorm_le_mul_eLpNorm_tsum_enorm_fourierMultiplierCLM_littlewoodPaley_sq_rpow`)
bounds `‖T(b) f‖_r` by the `L^r` norm of `(∑ⱼ |Pⱼ T(b) f|²)^{1/2} = (∑ⱼ |T(b) Pⱼ f|²)^{1/2}`. Since
`r ≥ 2` and `q ≥ 2`, Minkowski's inequality for square sums
(`MeasureTheory.eLpNorm_tsum_sq_rpow_le`), first in `L^r` and then in `L^q`, moves the square sum
outside both norms.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, proof of Theorem 2.6.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Springer, 2011, Section 2.2.
-/

public section

open Filter MeasureTheory Topology
open scoped ENNReal NNReal

namespace ContDiffBump

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V] (φ : ContDiffBump (0 : V))
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {β : Type*} {mβ : MeasurableSpace β} {ρ : Measure β}

omit [Nontrivial V] in
/-- The frequency-localized estimate applied to `x = Pⱼ f` bounds `‖T(·) Pⱼ f‖_{L^q L^r}` by
`K C 2^{jσ} ‖Pⱼ f‖₂`, since `Pⱼ f` is reproduced by its neighbouring blocks. -/
private theorem eLpNorm_eLpNorm_apply_fourierMultiplierCLM_le {σ : ℝ} {q r : ℝ≥0∞} (hq : 1 ≤ q)
    (hr : 1 ≤ r) {L : ℕ}
    (hL : ∀ j k : ℤ, j + L ≤ k → ∀ ξ : V, φ.littlewoodPaley j ξ * φ.littlewoodPaley k ξ = 0)
    {m : ℤ → Lp ℂ ∞ (volume : Measure V)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))
    {T : β → Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V)}
    (hT : ∀ x, AEStronglyMeasurable (fun b ↦ T b x) ρ) {C : ℝ≥0∞}
    (hC : ∀ (k : ℤ) (x : Lp F 2 (volume : Measure V)),
      eLpNorm (fun b ↦ eLpNorm (T b (Lp.fourierMultiplierCLM F (m k) x)) r volume) q ρ ≤
        C * ENNReal.ofReal (((2 : ℝ) ^ k) ^ σ) * ‖x‖ₑ)
    (j : ℤ) (f : Lp F 2 (volume : Measure V)) :
    eLpNorm (fun b ↦ eLpNorm (T b (Lp.fourierMultiplierCLM F (m j) f)) r volume) q ρ ≤
      (∑ d ∈ Finset.Ioo (-(L : ℤ)) L, (((2 : ℝ) ^ d) ^ σ).toNNReal : ℝ≥0) * C *
        (ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) * ‖Lp.fourierMultiplierCLM F (m j) f‖ₑ) := by
  set S := Finset.Ioo (-(L : ℤ)) L
  have hrep := φ.sum_fourierMultiplierCLM_fourierMultiplierCLM_littlewoodPaley hL hm j f
  rw [show Finset.Ioo (j - L) (j + L) = S.map (addRightEmbedding j) by
    rw [Finset.map_add_right_Ioo, neg_add_eq_sub, add_comm (L : ℤ)], Finset.sum_map] at hrep
  simp only [addRightEmbedding_apply] at hrep
  set g := Lp.fourierMultiplierCLM F (m j) f
  have hpt (b : β) : eLpNorm (T b g) r volume ≤
      ∑ d ∈ S, eLpNorm (T b (Lp.fourierMultiplierCLM F (m (d + j)) g)) r volume := by
    calc eLpNorm (T b g) r volume
        = eLpNorm (T b (∑ d ∈ S, Lp.fourierMultiplierCLM F (m (d + j)) g)) r volume := by
          rw [hrep]
      _ ≤ _ := by
          rw [map_sum, eLpNorm_congr_ae (Lp.coeFn_finsetSum _ _)]
          exact eLpNorm_sum_le hr
  calc eLpNorm (fun b ↦ eLpNorm (T b g) r volume) q ρ
      ≤ eLpNorm (∑ d ∈ S, fun b ↦
          eLpNorm (T b (Lp.fourierMultiplierCLM F (m (d + j)) g)) r volume) q ρ :=
        eLpNorm_mono_eNorm ((hT g).aemeasurable_eLpNorm_Lp .rfl r).aestronglyMeasurable
          fun b ↦ by
            rw [Finset.sum_apply]
            simpa only [eNorm_eq_self] using hpt b
    _ ≤ ∑ d ∈ S, eLpNorm (fun b ↦
          eLpNorm (T b (Lp.fourierMultiplierCLM F (m (d + j)) g)) r volume) q ρ :=
        eLpNorm_sum_le hq
    _ ≤ ∑ d ∈ S, C * ENNReal.ofReal (((2 : ℝ) ^ (d + j)) ^ σ) * ‖g‖ₑ :=
        Finset.sum_le_sum fun d _ ↦ hC (d + j) g
    _ = _ := by
        simp_rw [TauCeti.ofReal_zpow_add_rpow two_pos, ENNReal.ofNNReal_finsetSum,
          ENNReal.ofNNReal_toNNReal, Finset.sum_mul]
        refine Finset.sum_congr rfl fun d _ ↦ ?_
        ring

/-- **Littlewood–Paley summation of mixed-norm estimates.** On a nontrivial space, for every
`σ ∈ ℝ` and exponents `1 ≤ q, r ≤ ∞` there is `K` with the following property. Let `Pⱼ` be the
`L²` Fourier multiplier with the homogeneous Littlewood–Paley cutoff `ψⱼ` built from `φ` as
symbol, and let `T(b)`, `b ∈ β`, be bounded operators on `L²(V, F)` such that `b ↦ T(b) x` is
almost everywhere strongly measurable for every `x`. If

`‖T(·) Pₖ x‖_{L^q_b L^r_x} ≤ C 2^{kσ} ‖x‖₂` for every `k ∈ ℤ` and every `x ∈ L²`,

then for every `f ∈ L²`,

`‖T(·) f‖_{L^q_b L^r_x} ≤ K C ∑ⱼ 2^{jσ} ‖Pⱼ f‖₂`.

The constant `K` depends only on `φ` and `σ`. Each symbol enters as any element of `L^∞` almost
everywhere equal to `ψⱼ`. -/
theorem exists_eLpNorm_eLpNorm_le_mul_tsum (σ : ℝ) {q r : ℝ≥0∞} (hq : 1 ≤ q) (hr : 1 ≤ r) :
    ∃ K : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure V),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ T : β → Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V),
        (∀ x, AEStronglyMeasurable (fun b ↦ T b x) ρ) → ∀ C : ℝ≥0∞,
        (∀ (k : ℤ) (x : Lp F 2 (volume : Measure V)),
          eLpNorm (fun b ↦ eLpNorm (T b (Lp.fourierMultiplierCLM F (m k) x)) r volume) q ρ ≤
            C * ENNReal.ofReal (((2 : ℝ) ^ k) ^ σ) * ‖x‖ₑ) →
        ∀ f : Lp F 2 (volume : Measure V),
          eLpNorm (fun b ↦ eLpNorm (T b f) r volume) q ρ ≤
            K * C * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
              ‖Lp.fourierMultiplierCLM F (m j) f‖ₑ := by
  obtain ⟨L, hL⟩ := φ.exists_littlewoodPaley_mul_eq_zero φ
  refine ⟨∑ d ∈ Finset.Ioo (-(L : ℤ)) L, (((2 : ℝ) ^ d) ^ σ).toNNReal,
    fun m hm T hT C hC f ↦ ?_⟩
  have hmeas (x : Lp F 2 (volume : Measure V)) :
      AEMeasurable (fun b ↦ eLpNorm (T b x) r volume) ρ :=
    (hT x).aemeasurable_eLpNorm_Lp .rfl r
  -- Bound `‖T(b) f‖_r` by the sum over the blocks at each `b`, then apply Minkowski's inequality
  -- in `b` and the estimate for each block.
  calc eLpNorm (fun b ↦ eLpNorm (T b f) r volume) q ρ
      ≤ eLpNorm (fun b ↦ ∑' j, eLpNorm (T b (Lp.fourierMultiplierCLM F (m j) f)) r volume) q ρ :=
        eLpNorm_mono_eNorm (hmeas f).aestronglyMeasurable fun b ↦ by
          simpa only [eNorm_eq_self] using
            φ.eLpNorm_apply_le_tsum_eLpNorm_apply_fourierMultiplierCLM hm (T b) f hr
    _ ≤ ∑' j, eLpNorm (fun b ↦ eLpNorm (T b (Lp.fourierMultiplierCLM F (m j) f)) r volume) q ρ :=
        eLpNorm_tsum_le (fun j ↦ hmeas _) hq
    _ ≤ ∑' j, (∑ d ∈ Finset.Ioo (-(L : ℤ)) L, (((2 : ℝ) ^ d) ^ σ).toNNReal : ℝ≥0) * C *
          (ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) * ‖Lp.fourierMultiplierCLM F (m j) f‖ₑ) :=
        tsum_le_tsum fun j ↦ φ.eLpNorm_eLpNorm_apply_fourierMultiplierCLM_le hq hr hL hm hT hC j f
    _ = _ := ENNReal.tsum_mul_left

/-- `ContDiffBump.exists_eLpNorm_eLpNorm_le_mul_tsum` for a single family `T(b)` whose
frequency-localized estimates hold with some constant `C`, along exponents `1 ≤ q` and `1 ≤ r`:
there is `C'` such that for every `f ∈ L²`,

`‖T(·) f‖_{L^q_b L^r_x} ≤ C' ∑ⱼ 2^{jσ} ‖Pⱼ f‖₂`. -/
theorem exists_eLpNorm_eLpNorm_le_tsum_of_littlewoodPaley_le_of_one_le {q r : ℝ≥0∞}
    (hq : 1 ≤ q) (hr : 1 ≤ r) (σ : ℝ)
    (T : β → Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V))
    (hT : ∀ x, AEStronglyMeasurable (fun b ↦ T b x) ρ)
    (hloc : ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure V)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ x : Lp F 2 (volume : Measure V),
        eLpNorm (fun b ↦ eLpNorm (T b (Lp.fourierMultiplierCLM F m x)) r volume) q ρ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) * ‖x‖ₑ) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure V),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp F 2 (volume : Measure V),
        eLpNorm (fun b ↦ eLpNorm (T b f) r volume) q ρ ≤
          C * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
            ‖Lp.fourierMultiplierCLM F (m j) f‖ₑ := by
  obtain ⟨C, hC⟩ := hloc
  obtain ⟨K, hK⟩ := φ.exists_eLpNorm_eLpNorm_le_mul_tsum (F := F) (ρ := ρ) σ hq hr
  refine ⟨K * C, fun m hm f ↦ (hK m hm T hT C (fun k x ↦ hC k (m k) (hm k) x) f).trans_eq ?_⟩
  push_cast
  ring

/-- **Littlewood–Paley summation of mixed-norm estimates in square-sum form.** On a nontrivial
space, for every `σ ∈ ℝ` and exponents `2 ≤ q ≤ ∞` and `2 ≤ r < ∞` there is `K` with the following
property. Let `Pⱼ` be the `L²` Fourier multiplier with the homogeneous Littlewood–Paley cutoff `ψⱼ`
built from `φ` as symbol, and let `T(b)`, `b ∈ β`, be bounded operators on `L²(V, F)` commuting
with every `Pⱼ`, such that `b ↦ T(b) x` is almost everywhere strongly measurable for every `x`. If

`‖T(·) Pₖ x‖_{L^q_b L^r_x} ≤ C 2^{kσ} ‖x‖₂` for every `k ∈ ℤ` and every `x ∈ L²`,

then for every `f ∈ L²`,

`‖T(·) f‖_{L^q_b L^r_x} ≤ K C (∑ⱼ 2^{2jσ} ‖Pⱼ f‖₂²)^{1/2}`.

The right-hand side is the Littlewood–Paley form of the norm of `f` in the homogeneous Sobolev space
`\dot H^σ`; it is at most the `\dot B^σ_{2,1}` norm of
`ContDiffBump.exists_eLpNorm_eLpNorm_le_mul_tsum`. The constant `K` depends only on `φ`, `σ`, `r`
and `F`. Each symbol enters as any element of `L^∞` almost everywhere equal to `ψⱼ`. -/
theorem exists_eLpNorm_eLpNorm_le_mul_tsum_sq_rpow (σ : ℝ) {q r : ℝ≥0∞} (hq : 2 ≤ q)
    (hr : 2 ≤ r) (hr_top : r ≠ ∞) :
    ∃ K : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure V),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ T : β → Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V),
        (∀ x, AEStronglyMeasurable (fun b ↦ T b x) ρ) →
        (∀ b k x, T b (Lp.fourierMultiplierCLM F (m k) x) =
          Lp.fourierMultiplierCLM F (m k) (T b x)) → ∀ C : ℝ≥0∞,
        (∀ (k : ℤ) (x : Lp F 2 (volume : Measure V)),
          eLpNorm (fun b ↦ eLpNorm (T b (Lp.fourierMultiplierCLM F (m k) x)) r volume) q ρ ≤
            C * ENNReal.ofReal (((2 : ℝ) ^ k) ^ σ) * ‖x‖ₑ) →
        ∀ f : Lp F 2 (volume : Measure V),
          eLpNorm (fun b ↦ eLpNorm (T b f) r volume) q ρ ≤
            K * C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
              ‖Lp.fourierMultiplierCLM F (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) := by
  obtain ⟨A, hA⟩ :=
    TauCeti.exists_eLpNorm_le_mul_eLpNorm_tsum_enorm_fourierMultiplierCLM_littlewoodPaley_sq_rpow
      (F := F) φ (ENNReal.one_lt_two.trans_le hr) hr_top
  obtain ⟨L, hL⟩ := φ.exists_littlewoodPaley_mul_eq_zero φ
  set K₀ : ℝ≥0 := ∑ d ∈ Finset.Ioo (-(L : ℤ)) L, (((2 : ℝ) ^ d) ^ σ).toNNReal
  refine ⟨A * K₀, fun m hm T hT hcomm C hC f ↦ ?_⟩
  set a : ℤ → β → ℝ≥0∞ := fun j b ↦ eLpNorm (T b (Lp.fourierMultiplierCLM F (m j) f)) r volume
  have ha (j : ℤ) : AEMeasurable (a j) ρ := (hT _).aemeasurable_eLpNorm_Lp .rfl r
  -- At each `b`, the Littlewood–Paley inequality in `L^r` and Minkowski's inequality in
  -- `L^{r/2}` bound `‖T(b) f‖_r` by the square sum of the `‖T(b) Pⱼ f‖_r`.
  have hpt (b : β) : eLpNorm (T b f) r volume ≤ A * (∑' j, a j b ^ 2) ^ (2⁻¹ : ℝ) := by
    refine (hA m hm (T b f)).trans ?_
    gcongr
    simp_rw [← hcomm]
    refine (eLpNorm_tsum_sq_rpow_le (fun j ↦ (Lp.aestronglyMeasurable _).eNorm) hr).trans_eq ?_
    simp_rw [eLpNorm_eNorm _ (Lp.aestronglyMeasurable _), a]
  have hsq : AEMeasurable (fun b ↦ (∑' j, a j b ^ 2) ^ (2⁻¹ : ℝ)) ρ :=
    (AEMeasurable.tsum fun j ↦ (ha j).pow_const 2).pow_const _
  -- Minkowski's inequality in `L^{q/2}` and the estimate for each block.
  calc eLpNorm (fun b ↦ eLpNorm (T b f) r volume) q ρ
      ≤ eLpNorm (fun b ↦ (A : ℝ≥0∞) * (∑' j, a j b ^ 2) ^ (2⁻¹ : ℝ)) q ρ :=
        eLpNorm_mono_eNorm ((hT f).aemeasurable_eLpNorm_Lp .rfl r).aestronglyMeasurable fun b ↦ by
          simpa only [eNorm_eq_self] using hpt b
    _ = A * eLpNorm (fun b ↦ (∑' j, a j b ^ 2) ^ (2⁻¹ : ℝ)) q ρ :=
        eLpNorm_const_mul_ennreal hsq.aestronglyMeasurable
    _ ≤ A * (∑' j, eLpNorm (a j) q ρ ^ 2) ^ (2⁻¹ : ℝ) := by
        gcongr
        exact eLpNorm_tsum_sq_rpow_le ha hq
    _ ≤ A * (∑' j, (K₀ * C * (ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
          ‖Lp.fourierMultiplierCLM F (m j) f‖ₑ)) ^ 2) ^ (2⁻¹ : ℝ) := by
        gcongr with j
        exact φ.eLpNorm_eLpNorm_apply_fourierMultiplierCLM_le (one_le_two.trans hq)
          (one_le_two.trans hr) hL hm hT hC j f
    _ = _ := by
        have hsqrt (x : ℝ≥0∞) : (x ^ 2) ^ (2⁻¹ : ℝ) = x := by
          exact_mod_cast ENNReal.pow_rpow_inv_natCast two_ne_zero x
        simp_rw [mul_pow (_ * _ : ℝ≥0∞), ENNReal.tsum_mul_left]
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hsqrt, ENNReal.coe_mul]
        ring

/-- `ContDiffBump.exists_eLpNorm_eLpNorm_le_mul_tsum_sq_rpow` for a single family `T(b)` commuting
with the Fourier multipliers whose frequency-localized estimates hold with some constant `C`, along
exponents `2 ≤ q` and `2 ≤ r < ∞`: there is `C'` such that for every `f ∈ L²`,

`‖T(·) f‖_{L^q_b L^r_x} ≤ C' (∑ⱼ 2^{2jσ} ‖Pⱼ f‖₂²)^{1/2}`. -/
theorem exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_littlewoodPaley_le {q r : ℝ≥0∞}
    (hq : 2 ≤ q) (hr : 2 ≤ r) (hr_top : r ≠ ∞) (σ : ℝ)
    (T : β → Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V))
    (hT : ∀ x, AEStronglyMeasurable (fun b ↦ T b x) ρ)
    (hcomm : ∀ b (n : Lp ℂ ∞ (volume : Measure V)) x,
      T b (Lp.fourierMultiplierCLM F n x) = Lp.fourierMultiplierCLM F n (T b x))
    (hloc : ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure V)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ x : Lp F 2 (volume : Measure V),
        eLpNorm (fun b ↦ eLpNorm (T b (Lp.fourierMultiplierCLM F m x)) r volume) q ρ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) * ‖x‖ₑ) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure V),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp F 2 (volume : Measure V),
        eLpNorm (fun b ↦ eLpNorm (T b f) r volume) q ρ ≤
          C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
            ‖Lp.fourierMultiplierCLM F (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) := by
  obtain ⟨C, hC⟩ := hloc
  obtain ⟨K, hK⟩ := φ.exists_eLpNorm_eLpNorm_le_mul_tsum_sq_rpow (F := F) (ρ := ρ) σ hq hr hr_top
  refine ⟨K * C, fun m hm f ↦ (hK m hm T hT (fun b k x ↦ hcomm b (m k) x) C
    (fun k x ↦ hC k (m k) (hm k) x) f).trans_eq ?_⟩
  push_cast
  ring

end ContDiffBump
