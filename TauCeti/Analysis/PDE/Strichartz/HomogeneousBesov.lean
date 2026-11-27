/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Homogeneous.Basic
public import TauCeti.Analysis.PDE.Strichartz.LittlewoodPaley
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.Order.Filter.AtTopBot.Interval
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.MeasureTheory.Function.Lp.InfiniteSum
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

When the frequency-localized estimates hold at every `b` of a topological space,
`‖T(b) Pₖ x‖_r ≤ C 2^{kσ} ‖x‖₂`, and each `b ↦ T(b) Pₖ x` is continuous for the `L^r` distance,
the series converges in `L^r` uniformly in `b`, to a continuous `U : β → L^r`
(`ContDiffBump.exists_continuous_tendsto_iSup_eLpNorm_sub_sum_apply_block`). For an evolution in
time this is the statement that the solution is continuous with values in `L^r`.

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
* `ContDiffBump.exists_continuous_tendsto_iSup_eLpNorm_sub_sum_apply_block`: under estimates at
  every `b`, it converges uniformly to a continuous limit.
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
  -- Along the partial sums over `(-N, N]`, the series tends to `U(b)` in `L^r` and to `T(b) f` in
  -- `L²`.
  refine ae_eq_of_tendsto_eLpNorm_sub_sum_of_tendsto_sum hb (Finset.tendsto_Ioc_neg (R := ℤ))
    (((T b).continuous.tendsto f).comp hL2 |>.congr fun N ↦ ?_)
  simp only [Function.comp_apply, map_sum, hblock]

/-- The frequency-localized estimates of a single operator `A` bound `A Pⱼ u` by
`K C 2^{jσ} ‖Pⱼ u‖₂`, with `K` depending only on `φ` and `σ`. This is the mixed-norm estimate
`TauCeti.eLpNorm_eLpNorm_apply_le_of_sum_fourierMultiplierCLM_eq` over a one-point measure space. -/
private theorem exists_forall_eLpNorm_apply_block_le {r : ℝ≥0∞} [Fact (1 ≤ r)] (σ : ℝ) :
    ∃ K : ℝ≥0, ∀ (A : Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V)) (C : ℝ≥0),
      (∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure V)),
        m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ x : Lp F 2 (volume : Measure V),
          eLpNorm (A (Lp.fourierMultiplierCLM F m x)) r volume ≤
            C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) * ‖x‖ₑ) →
      ∀ (u : TauCeti.HomogeneousBesovSpace F φ σ 2 1) (j : ℤ),
        eLpNorm (A (u.block j)) r volume ≤ K * C * ‖u.weightedBlocks j‖ₑ := by
  set m : ℤ → Lp ℂ ∞ (volume : Measure V) := fun j ↦ (φ.memLp_ofReal_littlewoodPaley j ∞).toLp _
  have hm (j : ℤ) : m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ) :=
    (φ.memLp_ofReal_littlewoodPaley j ∞).coeFn_toLp
  obtain ⟨L, hL⟩ := TauCeti.HomogeneousBesovSpace.exists_sum_fourierMultiplierCLM_block_eq
    (G := F) (s := σ) (q := 1) φ
  refine ⟨∑ d ∈ Finset.Ico (-(L : ℤ)) L, (((2 : ℝ) ^ d) ^ σ).toNNReal, fun A C hC u j ↦ ?_⟩
  have h := TauCeti.eLpNorm_eLpNorm_apply_le_of_sum_fourierMultiplierCLM_eq (σ := σ)
    (ρ := Measure.dirac ()) le_rfl Fact.out (T := fun _ : Unit ↦ A)
    (fun _ ↦ aestronglyMeasurable_const) (fun k y ↦ by simpa using hC k (m k) (hm k) y)
    (hL hm u j)
  rw [eLpNorm_dirac _ _ one_ne_zero, eNorm_eq_self] at h
  refine h.trans_eq ?_
  rw [← TauCeti.HomogeneousBesovSpace.ofReal_mul_eNorm_block, mul_assoc]

/-- If each `b ↦ T(b) Pₖ x` is continuous for the `L^r` distance, so is `b ↦ T(b) Pⱼ u` for every
`u ∈ \dot B^σ_{2,1}`, since the block `Pⱼ u` is reproduced by finitely many blocks. -/
private theorem tendsto_eLpNorm_apply_block_sub {r : ℝ≥0∞} [Fact (1 ≤ r)] {β : Type*}
    [TopologicalSpace β] {σ : ℝ}
    (T : β → Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V))
    (hcont : ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure V)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
        ∀ (x : Lp F 2 (volume : Measure V)) (b₀ : β),
          Tendsto (fun b ↦ eLpNorm (⇑(T b (Lp.fourierMultiplierCLM F m x)) -
            ⇑(T b₀ (Lp.fourierMultiplierCLM F m x))) r volume) (𝓝 b₀) (𝓝 0))
    (u : TauCeti.HomogeneousBesovSpace F φ σ 2 1) (j : ℤ) (b₀ : β) :
    Tendsto (fun b ↦ eLpNorm (⇑(T b (u.block j)) - ⇑(T b₀ (u.block j))) r volume) (𝓝 b₀)
      (𝓝 0) := by
  set m : ℤ → Lp ℂ ∞ (volume : Measure V) := fun j ↦ (φ.memLp_ofReal_littlewoodPaley j ∞).toLp _
  have hm (j : ℤ) : m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ) :=
    (φ.memLp_ofReal_littlewoodPaley j ∞).coeFn_toLp
  obtain ⟨L, hL⟩ := TauCeti.HomogeneousBesovSpace.exists_sum_fourierMultiplierCLM_block_eq
    (G := F) (s := σ) (q := 1) φ
  set S := Finset.Ico (-(L : ℤ)) L
  set P : ℤ → Lp F 2 (volume : Measure V) := fun d ↦
    Lp.fourierMultiplierCLM F (m (d + j)) (u.block j)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun b ↦ ∑ d ∈ S, eLpNorm (⇑(T b (P d)) - ⇑(T b₀ (P d))) r volume)
    (by simpa using tendsto_finsetSum S fun d _ ↦
      hcont (d + j) (m (d + j)) (hm _) (u.block j) b₀) (fun _ ↦ zero_le) fun b ↦ ?_
  calc eLpNorm (⇑(T b (u.block j)) - ⇑(T b₀ (u.block j))) r volume
      = eLpNorm (⇑(∑ d ∈ S, (T b (P d) - T b₀ (P d)))) r volume := by
        rw [Finset.sum_sub_distrib, ← map_sum, ← map_sum, hL hm u j]
        exact eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm
    _ ≤ ∑ d ∈ S, eLpNorm (⇑(T b (P d) - T b₀ (P d))) r volume := by
        rw [eLpNorm_congr_ae (Lp.coeFn_finsetSum _ _)]
        exact eLpNorm_sum_le Fact.out
    _ = _ := Finset.sum_congr rfl fun d _ ↦ eLpNorm_congr_ae (Lp.coeFn_sub _ _)

/-- **The dyadic series of an evolution continuous in time.** Let `1 ≤ r`, let `Pⱼ` be the
homogeneous Littlewood–Paley blocks built from `φ`, and let `T(b)`, `b ∈ β`, be bounded operators
on `L²(V, F)` indexed by a topological space, with the frequency-localized estimates at every
`b`,

`‖T(b) Pₖ x‖_r ≤ C 2^{kσ} ‖x‖₂` for every `k ∈ ℤ`, `b ∈ β` and `x ∈ L²`,

and such that each `b ↦ T(b) Pₖ x` is continuous for the `L^r` distance. Then there is `C'` such
that for every `u ∈ \dot B^σ_{2,1}` the series `∑ⱼ T(b) Pⱼ u` converges in `L^r` uniformly in `b`:
there is a continuous `U : β → L^r` such that `sup_b ‖U(b) - ∑_{j ∈ s} T(b) Pⱼ u‖_r` tends to `0`
along the finite sets `s` of scales, and `‖U(b)‖_r ≤ C' ‖u‖_{\dot B^σ_{2,1}}` for every `b`.
The constant `C'` depends only on `φ`, `σ` and the constant of the frequency-localized
estimates. -/
theorem exists_continuous_tendsto_iSup_eLpNorm_sub_sum_apply_block {r : ℝ≥0∞} [Fact (1 ≤ r)]
    {β : Type*} [TopologicalSpace β] (σ : ℝ)
    (T : β → Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V))
    (hloc : ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure V)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
        ∀ (b : β) (x : Lp F 2 (volume : Measure V)),
          eLpNorm (T b (Lp.fourierMultiplierCLM F m x)) r volume ≤
            C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) * ‖x‖ₑ)
    (hcont : ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure V)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
        ∀ (x : Lp F 2 (volume : Measure V)) (b₀ : β),
          Tendsto (fun b ↦ eLpNorm (⇑(T b (Lp.fourierMultiplierCLM F m x)) -
            ⇑(T b₀ (Lp.fourierMultiplierCLM F m x))) r volume) (𝓝 b₀) (𝓝 0)) :
    ∃ C : ℝ≥0, ∀ u : TauCeti.HomogeneousBesovSpace F φ σ 2 1,
      ∃ U : β → Lp F r (volume : Measure V), Continuous U ∧
        Tendsto (fun s : Finset ℤ ↦
          ⨆ b, eLpNorm (⇑(U b) - ⇑(∑ j ∈ s, T b (u.block j))) r volume) atTop (𝓝 0) ∧
        ∀ b, ‖U b‖ₑ ≤ C * ‖u‖ₑ := by
  obtain ⟨C, hC⟩ := hloc
  obtain ⟨K, hK⟩ := φ.exists_forall_eLpNorm_apply_block_le (F := F) (r := r) σ
  refine ⟨K * C, fun u ↦ ?_⟩
  -- The pieces `T(b) Pⱼ u` are bounded in `L^r` by the summable `w j = K C 2^{jσ} ‖Pⱼ u‖₂`.
  set w : ℤ → ℝ≥0∞ := fun j ↦ K * C * ‖u.weightedBlocks j‖ₑ
  have hpiece (b : β) (j : ℤ) : eLpNorm (T b (u.block j)) r volume ≤ w j :=
    hK (T b) C (fun j m hm x ↦ hC j m hm b x) u j
  have hw : ∑' j, w j = K * C * ‖u‖ₑ := by
    rw [ENNReal.tsum_mul_left, TauCeti.HomogeneousBesovSpace.tsum_eNorm_weightedBlocks]
  have hw_top : ∑' j, w j ≠ ∞ := by
    rw [hw]
    finiteness
  have hmem (b : β) (j : ℤ) : MemLp (T b (u.block j)) r volume :=
    (hpiece b j).trans_lt ((le_tsum w j).trans_lt hw_top.lt_top)
  set v : β → ℤ → Lp F r (volume : Measure V) := fun b j ↦ (hmem b j).toLp
  have hv (b : β) (j : ℤ) : ‖v b j‖ₑ ≤ w j := by
    rw [Lp.eNorm_def, eLpNorm_congr_ae (hmem b j).coeFn_toLp]
    exact hpiece b j
  have hvn (j : ℤ) (b : β) : ‖v b j‖ ≤ (w j).toReal := by
    rw [← toReal_eNorm]
    exact ENNReal.toReal_mono (ne_top_of_tsum_ne_top hw_top j) (hv b j)
  have hsum (b : β) : Summable (v b) :=
    Summable.of_norm_bounded (ENNReal.summable_toReal hw_top) fun j ↦ hvn j b
  -- The remainder after the scales in `s` is bounded by the tail of `∑ⱼ w j`, uniformly in `b`.
  have htail (b : β) (s : Finset ℤ) :
      eLpNorm (⇑(∑' j, v b j) - ⇑(∑ j ∈ s, T b (u.block j))) r volume ≤
        ∑' j : {j // j ∉ s}, w j := by
    have hcoe : ⇑(∑' j, v b j) - ⇑(∑ j ∈ s, T b (u.block j)) =ᵐ[volume]
        ⇑((∑' j, v b j) - ∑ j ∈ s, v b j) := by
      filter_upwards [Lp.coeFn_sub (∑' j, v b j) (∑ j ∈ s, v b j), Lp.coeFn_finsetSum s (v b),
        Lp.coeFn_finsetSum s fun j ↦ T b (u.block j),
        ae_all_iff.2 fun j ↦ (hmem b j).coeFn_toLp] with x h₁ h₂ h₃ h₄
      simp only [Pi.sub_apply, h₁, h₂, h₃, Finset.sum_apply, v, h₄]
    rw [eLpNorm_congr_ae hcoe, ← Lp.eNorm_def, ← (hsum b).sum_add_tsum_subtype_compl s,
      add_sub_cancel_left]
    exact eNorm_tsum_le_tsum_eNorm.trans (tsum_le_tsum fun j ↦ hv b j)
  -- Each piece is continuous in `b`, and the series of pieces is normally convergent.
  have hvcont (j : ℤ) : Continuous fun b ↦ v b j :=
    continuous_iff_continuousAt.2 fun b₀ ↦ (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).2 <|
      (φ.tendsto_eLpNorm_apply_block_sub T hcont u j b₀).congr fun b ↦ eLpNorm_congr_ae <| by
        filter_upwards [(hmem b j).coeFn_toLp, (hmem b₀ j).coeFn_toLp] with x h₁ h₂
        rw [Pi.sub_apply, Pi.sub_apply, h₁, h₂]
  refine ⟨fun b ↦ ∑' j, v b j, continuous_tsum hvcont (ENNReal.summable_toReal hw_top) hvn,
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_tsum_compl_atTop_zero hw_top) (fun _ ↦ zero_le)
      fun s ↦ iSup_le fun b ↦ htail b s, fun b ↦ ?_⟩
  calc ‖∑' j, v b j‖ₑ ≤ ∑' j, ‖v b j‖ₑ := eNorm_tsum_le_tsum_eNorm
    _ ≤ ∑' j, w j := tsum_le_tsum (hv b)
    _ = _ := by rw [hw, ENNReal.coe_mul]

end ContDiffBump
