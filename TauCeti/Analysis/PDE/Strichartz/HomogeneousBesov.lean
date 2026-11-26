/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Homogeneous.Basic
public import TauCeti.Analysis.PDE.Strichartz.LittlewoodPaley
import Mathlib.Order.Filter.AtTopBot.Interval
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.MeasureTheory.Function.Lp.MixedNorm.Series

/-!
# Evolution of data in the homogeneous Besov space `\dot B^σ_{2,1}` by dyadic series

Let `V` be a finite-dimensional real inner product space, let `Pⱼ`, `j ∈ ℤ`, be the homogeneous
Littlewood–Paley blocks built from a bump function `φ`, and let `T(b)`, `b ∈ β`, be a measurable
family of bounded operators on `L²(V, F)`, such as the propagators `T(t)` of a dispersive equation.
Strichartz estimates are first proved for frequency-localized data,

`‖T(·) Pₖ x‖_{L^q_b L^r_x} ≤ C 2^{kσ} ‖x‖₂` for every `k ∈ ℤ` and `x ∈ L²`.

This file treats data in the homogeneous Besov space `\dot B^σ_{2,1}`
(`TauCeti.HomogeneousBesovSpace`), a space of tempered distributions modulo those with spectrum at
the origin, on which `T(b)` has no meaning a priori. The blocks `Pⱼ u` of such a datum `u` are `L²`
functions, so each term of the dyadic series

`∑ⱼ T(b) Pⱼ u`

is defined. The file builds no evolution operator on `\dot B^σ_{2,1}`; it shows that this series
converges (`ContDiffBump.exists_tendsto_eLpNorm_eLpNorm_sub_sum_apply_block`): there is some
`U : β → L^r`, determined for almost every `b`, such that the partial sums converge to `U(b)` in
`L^r` for almost every `b`, and to `U` in the mixed norm `L^q_b L^r_x`, with the Strichartz estimate

`‖U‖_{L^q_b L^r_x} ≤ C ‖u‖_{\dot B^σ_{2,1}}`.

When the datum is an `L²` function `f`, any such limit `U` agrees with `T(b) f` for almost every
`b` (`ContDiffBump.ae_ae_eq_apply_of_tendsto_eLpNorm_sub_sum_apply_block`).

On `L²` functions the blocks `Pⱼ` of tempered distributions are the `L²` Fourier multipliers with
symbols `ψⱼ` (`TemperedDistribution.homogeneousLittlewoodPaleyBlock_toTemperedDistribution`), which
is how the two descriptions of the blocks are compared. Each block `Pⱼ u` is reproduced by its
neighbouring blocks, `Pⱼ u = ∑_{-L ≤ k - j < L} Pₖ Pⱼ u`
(`TauCeti.HomogeneousBesovSpace.exists_sum_fourierMultiplierCLM_block_eq`), so the
frequency-localized estimates bound the piece `T(·) Pⱼ u` by `K C 2^{jσ} ‖Pⱼ u‖₂`
(`TauCeti.eLpNorm_eLpNorm_apply_le_of_sum_fourierMultiplierCLM_eq`). These bounds sum to
`K C ‖u‖_{\dot B^σ_{2,1}}`, and a series with summable mixed norms converges
(`MeasureTheory.exists_tendsto_eLpNorm_eLpNorm_sub_sum_of_tsum_ne_top`).

## Main declarations

* `ContDiffBump.exists_tendsto_eLpNorm_eLpNorm_sub_sum_apply_block`: the dyadic series of the
  evolution of a datum in `\dot B^σ_{2,1}` converges, with the Strichartz estimate.
* `ContDiffBump.ae_ae_eq_apply_of_tendsto_eLpNorm_sub_sum_apply_block`: for `L²` data the sum is
  the evolution of `L²`.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Theorem 2.6 and its proof.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Springer, 2011, Section 2.4.
-/

public section

open Filter MeasureTheory Topology TemperedDistribution
open scoped ENNReal NNReal SchwartzMap

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] (φ : ContDiffBump (0 : V))

namespace ContDiffBump

variable {β : Type*} {mβ : MeasurableSpace β} {ρ : Measure β}

/-- **The dyadic series of the evolution of a datum in `\dot B^σ_{2,1}`.** Let `1 ≤ q`, `1 ≤ r`,
let `Pⱼ` be the homogeneous Littlewood–Paley blocks built from `φ`, and let `T(b)`, `b ∈ β`, be
bounded operators on `L²(V, F)` such that `b ↦ T(b) x` is almost everywhere strongly measurable for
every `x`, with the frequency-localized estimates

`‖T(·) Pₖ x‖_{L^q_b L^r_x} ≤ C 2^{kσ} ‖x‖₂` for every `k ∈ ℤ` and `x ∈ L²`.

Then there is `C'` such that for every `u ∈ \dot B^σ_{2,1}` the series `∑ⱼ T(·) Pⱼ u` converges:
there is `U : β → L^r` such that the partial sums `∑_{j ∈ s} T(b) Pⱼ u` converge to `U(b)` in
`L^r` for almost every `b`, and to `U` in `L^q_b L^r_x`, and
`‖U‖_{L^q_b L^r_x} ≤ C' ‖u‖_{\dot B^σ_{2,1}}`.
The constant `C'` depends only on `φ`, `σ` and the constant of the frequency-localized estimates. -/
theorem exists_tendsto_eLpNorm_eLpNorm_sub_sum_apply_block {q r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hq : 1 ≤ q) (σ : ℝ) (T : β → Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V))
    (hT : ∀ x, AEStronglyMeasurable (fun b ↦ T b x) ρ)
    (hloc : ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure V)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ x : Lp F 2 (volume : Measure V),
        eLpNorm (fun b ↦ eLpNorm (T b (Lp.fourierMultiplierCLM F m x)) r volume) q ρ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) * ‖x‖ₑ) :
    ∃ C : ℝ≥0, ∀ u : TauCeti.HomogeneousBesovSpace F φ σ 2 1,
      ∃ U : β → Lp F r (volume : Measure V),
        (∀ᵐ b ∂ρ, Tendsto (fun s : Finset ℤ ↦
          eLpNorm (⇑(U b) - ⇑(∑ j ∈ s, T b (u.block j))) r volume) atTop (𝓝 0)) ∧
        Tendsto (fun s : Finset ℤ ↦
          eLpNorm (fun b ↦ eLpNorm (⇑(U b) - ⇑(∑ j ∈ s, T b (u.block j))) r volume) q ρ) atTop
            (𝓝 0) ∧
        eLpNorm (fun b ↦ ‖U b‖ₑ) q ρ ≤ C * ‖u‖ₑ := by
  obtain ⟨C, hC⟩ := hloc
  set m : ℤ → Lp ℂ ∞ (volume : Measure V) := fun j ↦ (φ.memLp_ofReal_littlewoodPaley j ∞).toLp _
  have hm (j : ℤ) : m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ) :=
    (φ.memLp_ofReal_littlewoodPaley j ∞).coeFn_toLp
  obtain ⟨L, hL⟩ := TauCeti.HomogeneousBesovSpace.exists_sum_fourierMultiplierCLM_block_eq
    (G := F) (s := σ) (q := 1) φ
  set K : ℝ≥0 := ∑ d ∈ Finset.Ico (-(L : ℤ)) L, (((2 : ℝ) ^ d) ^ σ).toNNReal
  refine ⟨K * C, fun u ↦ ?_⟩
  -- Each piece `T(·) Pⱼ u` is bounded by `K C 2^{jσ} ‖Pⱼ u‖₂`.
  have hpiece (j : ℤ) : eLpNorm (fun b ↦ eLpNorm (T b (u.block j)) r volume) q ρ ≤
      K * C * ‖u.weightedBlocks j‖ₑ := by
    rw [← TauCeti.HomogeneousBesovSpace.ofReal_mul_eNorm_block]
    exact TauCeti.eLpNorm_eLpNorm_apply_le_of_sum_fourierMultiplierCLM_eq hq Fact.out hT
      (fun k x ↦ hC k (m k) (hm k) x) (hL hm u j)
  have hsum : ∑' j, eLpNorm (fun b ↦ eLpNorm (T b (u.block j)) r volume) q ρ ≤
      K * C * ‖u‖ₑ := by
    rw [← TauCeti.HomogeneousBesovSpace.tsum_eNorm_weightedBlocks, ← ENNReal.tsum_mul_left]
    exact tsum_le_tsum hpiece
  obtain ⟨U, hae, hmix, hle⟩ := exists_tendsto_eLpNorm_eLpNorm_sub_sum_of_tsum_ne_top hq
    (g := fun j b ↦ T b (u.block j)) (fun j ↦ hT _)
    (hsum.trans_lt (by simp [ENNReal.mul_lt_top])).ne
  exact ⟨U, hae, hmix, hle.trans hsum⟩

/-- **The dyadic series extends the evolution of `L²`.** If `u ∈ \dot B^σ_{2,q}` is an `L²` function
`f` and the dyadic series `∑ⱼ T(b) Pⱼ u` converges in `L^r` to `U(b)` for almost every `b`, then
`U(b) = T(b) f` for almost every `b`. -/
theorem ae_ae_eq_apply_of_tendsto_eLpNorm_sub_sum_apply_block [Nontrivial V] {σ : ℝ}
    {q r : ℝ≥0∞} [Fact (1 ≤ r)]
    (T : β → Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V))
    {u : TauCeti.HomogeneousBesovSpace F φ σ 2 q} {f : Lp F 2 (volume : Measure V)}
    (hf : u.toDistr = f) {U : β → Lp F r (volume : Measure V)}
    (hU : ∀ᵐ b ∂ρ, Tendsto (fun s : Finset ℤ ↦
      eLpNorm (⇑(U b) - ⇑(∑ j ∈ s, T b (u.block j))) r volume) atTop (𝓝 0)) :
    ∀ᵐ b ∂ρ, ⇑(U b) =ᵐ[volume] ⇑(T b f) := by
  set m : ℤ → Lp ℂ ∞ (volume : Measure V) := fun j ↦ (φ.memLp_ofReal_littlewoodPaley j ∞).toLp _
  have hm (j : ℤ) : m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ) :=
    (φ.memLp_ofReal_littlewoodPaley j ∞).coeFn_toLp
  -- The blocks of `u` are the `L²` blocks of `f`.
  have hblock (j : ℤ) : u.block j = Lp.fourierMultiplierCLM F (m j) f :=
    Lp.toTemperedDistribution_injective <| by
      dsimp only
      rw [TauCeti.HomogeneousBesovSpace.coe_block, hf,
        homogeneousLittlewoodPaleyBlock_toTemperedDistribution φ (hm j)]
  have hL2 := φ.tendsto_sum_fourierMultiplierCLM_littlewoodPaley hm f
  filter_upwards [hU] with b hb
  set S : ℕ → Lp F 2 (volume : Measure V) := fun N ↦
    ∑ j ∈ Finset.Ioc (-(N : ℤ)) N, T b (u.block j)
  -- Along the partial sums over `(-N, N]`, the series tends to `U(b)` in `L^r` and to `T(b) f` in
  -- `L²`; both limits are limits in measure, so they agree almost everywhere.
  have hr : TendstoInMeasure volume (fun N ↦ ⇑(S N)) atTop ⇑(U b) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ r)).ne' ?_
    refine (hb.comp (Finset.tendsto_Ioc_neg (R := ℤ))).congr fun N ↦ ?_
    rw [Function.comp_apply, eLpNorm_sub_comm]
  have h2 : TendstoInMeasure volume (fun N ↦ ⇑(S N)) atTop ⇑(T b f) := by
    refine tendstoInMeasure_of_tendsto_Lp (((T b).continuous.tendsto f).comp hL2 |>.congr ?_)
    intro N
    simp only [Function.comp_apply, map_sum, S, hblock]
  exact tendstoInMeasure_ae_unique hr h2

end ContDiffBump
