/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.HomogeneousLittlewoodPaley
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Homogeneous.Basic
public import TauCeti.Analysis.PDE.Wave.DuhamelStrichartz
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.Order.Filter.AtTopBot.Interval
import TauCeti.Analysis.Fourier.LittlewoodPaley
import TauCeti.Analysis.SpecificLimits.DyadicSum
import TauCeti.MeasureTheory.Function.Lp.InfiniteSum
import TauCeti.MeasureTheory.Function.Lp.MixedNorm.Series

/-!
# The dyadic Duhamel series for the wave equation with Besov data and dyadic forcing

On a nontrivial real inner product space `E` of dimension `n`, let `D = √(-Δ)` and let `Pⱼ`,
`j ∈ ℤ`, be the homogeneous Littlewood–Paley blocks built from a bump function `φ`. For data
`f, g ∈ L²(E)` and a forcing `G : ℝ → L²(E)` integrable on `[0, T]`, the Cauchy problem

`∂ₜ²u - Δu = G`, `u(0) = f`, `∂ₜu(0) = g`

is solved by Duhamel's formula (`TauCeti.waveDuhamelSolution`)

`u(t) = cos(tD) f + D⁻¹ sin(tD) g + ∫₀ᵗ D⁻¹ sin((t - s)D) G(s) ds`,

which satisfies the Strichartz estimate on `[0, T]` with the dyadic `ℓ¹` norms of the data and of
the forcing on the right (`ContDiffBump.exists_eLpNorm_eLpNorm_waveDuhamelSolution_le_tsum`). This
file constructs the candidate solution, and proves its Strichartz estimate, when the data lie in the
homogeneous Besov spaces themselves, `f ∈ \dot B^γ_{2,1}` and `g ∈ \dot B^{γ - 1}_{2,1}`
(`TauCeti.HomogeneousBesovSpace`), and the forcing `F(s)` is a tempered distribution at every time
`s` of `[0, T]`, known only through its blocks `Gⱼ(s) = Pⱼ F(s)`, which are `L²` functions
integrable on `[0, T]` with

`∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Gⱼ‖_{L^{p₁}([0, T]; L^{r₁'}_x)} < ∞`.

Neither the data nor the forcing need be functions, so Duhamel's formula has no a priori meaning
for them, but it does for their blocks, and the candidate solution is the sum of the dyadic
Duhamel series

`∑ⱼ (cos(tD) Pⱼ f + D⁻¹ sin(tD) Pⱼ g + ∫₀ᵗ D⁻¹ sin((t - s)D) Gⱼ(s) ds)`,

whose terms are the solutions `waveDuhamelSolution ℂ (f.block j) (g.block j) (G j)` with the
blocks of the data and of the forcing. Let `(q, r)` and `(q₁, r₁)` be wave-admissible pairs as in
the Strichartz estimates on `[0, T]`, with Hölder conjugates `p₁` and `r₁'` of `q₁` and `r₁`. Then
the series converges: there is `U : ℝ → L^r`, determined for almost every `t ∈ [0, T]`, such that
the partial sums converge to `U(t)` in `L^r` for almost every `t ∈ [0, T]` and to `U` in
`L^q([0, T]; L^r_x)`, with

`‖U‖_{L^q([0, T]; L^r_x)} ≤ C (‖f‖_{\dot B^γ_{2,1}} + ‖g‖_{\dot B^{γ - 1}_{2,1}}`
`  + ∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Gⱼ‖_{L^{p₁}([0, T]; L^{r₁'}_x)})`

and `C` independent of `T`, of the data and of the forcing. This holds at the pairs `(q, r)` with
`2 ≤ q < ∞`, the time exponent `2` in dimension `n ≥ 4` only
(`ContDiffBump.exists_tendsto_eLpNorm_eLpNorm_sub_sum_waveDuhamelSolution_block`), and at the
pairs `(∞, r)`, `2 ≤ r ≤ ∞`, with `γ = n / 2 - n / r`
(`ContDiffBump.exists_tendsto_eLpNorm_top_eLpNorm_sub_sum_waveDuhamelSolution_block`); at `(∞, ∞)`
the sum `U` is bounded uniformly on `[0, T] × E`.

This file proves only the convergence of the series and the estimate of its sum `U`: that `U`
satisfies `∂ₜ²u - Δu = F` in a weak sense and attains the data `f` and `g` is not proved here.

When the data are `L²` functions `f₀`, `g₀` and the forcing is a function `G₀ : ℝ → L²(E)`
integrable on `[0, T]`, with blocks `Gⱼ(s) = Pⱼ G₀(s)`, any such sum agrees with Duhamel's formula
`waveDuhamelSolution ℂ f₀ g₀ G₀ t` for almost every `t ∈ [0, T]`
(`ContDiffBump.ae_ae_eq_waveDuhamelSolution_of_tendsto`), so the series extends Duhamel's formula
to these data and forcings.

## The argument

The blocks are almost orthogonal: there is `L` such that `Pₖ Pⱼ = 0` unless `|k - j| < L`, and
they are bounded on every `Lᵖ`, `1 ≤ p`, uniformly in the scale, also in mixed norms (in the
namespace `TemperedDistribution`,
`exists_eLpNorm_eLpNorm_fourierMultiplierCLM_of_eq_homogeneousLittlewoodPaleyBlock`).
So when the data and the forcing are the `j`-th blocks `Pⱼ f`, `Pⱼ g` and `Gⱼ`, the Strichartz
estimate on `[0, T]` for `L²` data and forcing has at most `2L - 1` nonzero terms in each of its
three sums, and it bounds the `j`-th term of the series by a constant times

`2^{jγ} ‖Pⱼ f‖₂ + 2^{j(γ - 1)} ‖Pⱼ g‖₂ + 2^{j(γ + γ₁ - 1)} ‖Gⱼ‖_{L^{p₁}([0, T]; L^{r₁'}_x)}`

(`TauCeti.tsum_ofReal_two_zpow_rpow_mul_le_of_eq_zero`). Summed over `j` these are the norms of the
data in the Besov spaces and the dyadic norm of the forcing, and a series with summable mixed
norms converges (`MeasureTheory.exists_tendsto_eLpNorm_eLpNorm_sub_sum_of_tsum_ne_top`).

For `L²` data and forcing, `Pⱼ` commutes with Duhamel's formula
(`TauCeti.fourierMultiplierCLM_waveDuhamelSolution`), so the partial sums of the series are the
partial sums `∑ⱼ Pⱼ u(t)` of the blocks of `u(t) = waveDuhamelSolution ℂ f₀ g₀ G₀ t`, which converge
to `u(t)` in `L²` (`ContDiffBump.tendsto_sum_fourierMultiplierCLM_littlewoodPaley`). Limits in `L²`
and in `L^r` are both limits in measure, so they agree almost everywhere
(`MeasureTheory.ae_eq_of_tendsto_eLpNorm_sub_sum_of_tendsto_sum`).

## Main declarations

* `ContDiffBump.exists_tendsto_eLpNorm_eLpNorm_sub_sum_waveDuhamelSolution_block`: convergence of
  the dyadic Duhamel series on `[0, T]` with Besov data and dyadic forcing, with the Strichartz
  estimate of its sum at the pairs with `2 ≤ q < ∞`.
* `ContDiffBump.exists_tendsto_eLpNorm_top_eLpNorm_sub_sum_waveDuhamelSolution_block`: the same at
  the pairs `(∞, r)`.
* `ContDiffBump.ae_ae_eq_waveDuhamelSolution_of_tendsto`: for `L²` data and forcing the series sums
  to Duhamel's formula.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Theorem 2.6 and its proof.
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980,
  Corollary 1.3.
-/

public section

noncomputable section

open Filter MeasureTheory Topology TauCeti TemperedDistribution
open scoped ENNReal NNReal FourierTransform SchwartzMap

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (φ : ContDiffBump (0 : E))

/-- **The Strichartz estimate on `[0, T]` for data and forcing made of `j`-th blocks.** If the
solutions of the forced wave equation with `L²` data and forcing satisfy

`‖u‖_{L^q([0, T]; L^r_x)} ≤ C (∑ₖ 2^{kγ} ‖Pₖ f‖₂ + ∑ₖ 2^{k(γ - 1)} ‖Pₖ g‖₂`
`  + ∑ₖ 2^{kσ} ‖Pₖ G‖_{L^{p₁}([0, T]; L^{r₁'}_x)})`,

then there is `C'` such that, when `x`, `y` and `G(s)` for `s ∈ [0, T]` are `j`-th blocks of
tempered distributions, the solution with data `x`, `y` and forcing `G` satisfies

`‖u‖_{L^q([0, T]; L^r_x)} ≤ C' (2^{jγ} ‖x‖₂ + 2^{j(γ - 1)} ‖y‖₂`
`  + 2^{jσ} ‖G‖_{L^{p₁}([0, T]; L^{r₁'}_x)})`,

with `C'` independent of `j` and `T`. -/
private theorem exists_eLpNorm_eLpNorm_waveDuhamelSolution_le_of_eq_block {q r p₁ r₁' : ℝ≥0∞}
    (hr₁' : 1 ≤ r₁') {γ σ : ℝ} {C : ℝ≥0}
    (hC : ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (f g : Lp ℂ 2 (volume : Measure E)) (G : ℝ → Lp ℂ 2 (volume : Measure E)) (T : ℝ),
        IntegrableOn G (Set.Icc 0 T) →
        eLpNorm (fun t ↦ eLpNorm (waveDuhamelSolution ℂ f g G t) r volume) q
            (volume.restrict (Set.Icc 0 T)) ≤
          C * (∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ γ) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ +
            ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ (γ - 1)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) g‖ₑ +
            ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
                eLpNorm (fun s ↦ eLpNorm (Lp.fourierMultiplierCLM ℂ (m j) (G s)) r₁' volume) p₁
                  (volume.restrict (Set.Icc 0 T)))) :
    ∃ C' : ℝ≥0, ∀ (j : ℤ) (x y : Lp ℂ 2 (volume : Measure E))
      (G : ℝ → Lp ℂ 2 (volume : Measure E)) (T : ℝ), IntegrableOn G (Set.Icc 0 T) →
      (∃ v : 𝓢'(E, ℂ), (x : 𝓢'(E, ℂ)) = homogeneousLittlewoodPaleyBlock ℂ φ j v) →
      (∃ v : 𝓢'(E, ℂ), (y : 𝓢'(E, ℂ)) = homogeneousLittlewoodPaleyBlock ℂ φ j v) →
      (∀ s ∈ Set.Icc 0 T,
        ∃ v : 𝓢'(E, ℂ), (G s : 𝓢'(E, ℂ)) = homogeneousLittlewoodPaleyBlock ℂ φ j v) →
        eLpNorm (fun t ↦ eLpNorm (waveDuhamelSolution ℂ x y G t) r volume) q
            (volume.restrict (Set.Icc 0 T)) ≤
          C' * (ENNReal.ofReal (((2 : ℝ) ^ j) ^ γ) * ‖x‖ₑ +
            ENNReal.ofReal (((2 : ℝ) ^ j) ^ (γ - 1)) * ‖y‖ₑ +
            ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
              eLpNorm (fun s ↦ eLpNorm (G s) r₁' volume) p₁ (volume.restrict (Set.Icc 0 T))) := by
  obtain ⟨L, K, hLK⟩ :=
    exists_eLpNorm_eLpNorm_fourierMultiplierCLM_of_eq_homogeneousLittlewoodPaleyBlock (G := ℂ) φ
  set m : ℤ → Lp ℂ ∞ (volume : Measure E) := fun j ↦ (φ.memLp_ofReal_littlewoodPaley j ∞).toLp _
  have hm (j : ℤ) : m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ) :=
    (φ.memLp_ofReal_littlewoodPaley j ∞).coeFn_toLp
  -- The constant of the window `-L < d < L` for the weight exponent `a`.
  set S : ℝ → ℝ≥0 := fun a ↦ ∑ d ∈ Finset.Ioo (-(L : ℤ)) L, (((2 : ℝ) ^ d) ^ a).toNNReal
  refine ⟨C * K * (S γ + S (γ - 1) + S σ), fun j x y G T hG hx hy hblock ↦ ?_⟩
  -- Only the blocks `Pₖ` with `|k - j| < L` see the data, as constant families over a point, and
  -- the forcing on `[0, T]`, and each costs at most the factor `K`.
  have hdata {z : Lp ℂ 2 (volume : Measure E)}
      (hz : ∃ v : 𝓢'(E, ℂ), (z : 𝓢'(E, ℂ)) = homogeneousLittlewoodPaleyBlock ℂ φ j v) (k : ℤ) :
      (k ∉ Finset.Ioo (j - L) (j + L) → ‖Lp.fourierMultiplierCLM ℂ (m k) z‖ₑ = 0) ∧
        ‖Lp.fourierMultiplierCLM ℂ (m k) z‖ₑ ≤ K * ‖z‖ₑ := by
    simpa only [eLpNorm_dirac _ _ one_ne_zero, eNorm_eq_self, ← Lp.eNorm_def] using
      hLK (ρ := Measure.dirac ()) (p := 1) one_le_two (x := fun _ ↦ z) aestronglyMeasurable_const
        (ae_of_all _ fun _ ↦ hz) (hm k)
  have hforcing (k : ℤ) := hLK (p := p₁) hr₁' hG.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Icc hblock) (hm k)
  refine (hC m hm x y G T hG).trans ?_
  grw [tsum_ofReal_two_zpow_rpow_mul_le_of_eq_zero γ (fun k hk ↦ (hdata hx k).1 hk)
      fun k _ ↦ (hdata hx k).2,
    tsum_ofReal_two_zpow_rpow_mul_le_of_eq_zero (γ - 1) (fun k hk ↦ (hdata hy k).1 hk)
      fun k _ ↦ (hdata hy k).2,
    tsum_ofReal_two_zpow_rpow_mul_le_of_eq_zero σ (fun k hk ↦ (hforcing k).1 hk)
      fun k _ ↦ (hforcing k).2]
  -- Each window constant is at most their sum.
  set S₀ := S γ + S (γ - 1) + S σ
  have hS₁ : (S γ : ℝ≥0∞) ≤ S₀ := by exact_mod_cast le_add_right le_self_add
  have hS₂ : (S (γ - 1) : ℝ≥0∞) ≤ S₀ := by exact_mod_cast le_add_right le_add_self
  have hS₃ : (S σ : ℝ≥0∞) ≤ S₀ := by exact_mod_cast le_add_self
  grw [hS₁, hS₂, hS₃]
  rw [ENNReal.coe_mul, ENNReal.coe_mul]
  exact le_of_eq (by ring)

/-- **Summation over the blocks.** If the solutions of the forced wave equation with `L²` data and
forcing satisfy the Strichartz estimate on `[0, T]` with the dyadic norms
`∑ₖ 2^{kγ} ‖Pₖ f‖₂`, `∑ₖ 2^{k(γ - 1)} ‖Pₖ g‖₂` and `∑ₖ 2^{kσ} ‖Pₖ G‖_{L^{p₁}([0, T]; L^{r₁'}_x)}`
on the right, then for data `f ∈ \dot B^γ_{2,1}`, `g ∈ \dot B^{γ - 1}_{2,1}` and a forcing with
blocks `Gⱼ`, the series of the solutions with the blocks of the data and of the forcing
converges, with the same estimate up to a constant. -/
private theorem exists_tendsto_of_eLpNorm_eLpNorm_waveDuhamelSolution_le {q r p₁ r₁' : ℝ≥0∞}
    [Fact (1 ≤ r)] (hq : 1 ≤ q) (hr₁' : 1 ≤ r₁') {γ σ : ℝ} {C : ℝ≥0}
    (hC : ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (f g : Lp ℂ 2 (volume : Measure E)) (G : ℝ → Lp ℂ 2 (volume : Measure E)) (T : ℝ),
        IntegrableOn G (Set.Icc 0 T) →
        eLpNorm (fun t ↦ eLpNorm (waveDuhamelSolution ℂ f g G t) r volume) q
            (volume.restrict (Set.Icc 0 T)) ≤
          C * (∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ γ) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ +
            ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ (γ - 1)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) g‖ₑ +
            ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
                eLpNorm (fun s ↦ eLpNorm (Lp.fourierMultiplierCLM ℂ (m j) (G s)) r₁' volume) p₁
                  (volume.restrict (Set.Icc 0 T)))) :
    ∃ C' : ℝ≥0, ∀ (T : ℝ) (f : HomogeneousBesovSpace ℂ φ γ 2 1)
      (g : HomogeneousBesovSpace ℂ φ (γ - 1) 2 1) (F : ℝ → 𝓢'(E, ℂ))
      (G : ℤ → ℝ → Lp ℂ 2 (volume : Measure E)),
      (∀ j, ∀ s ∈ Set.Icc 0 T,
        (G j s : 𝓢'(E, ℂ)) = homogeneousLittlewoodPaleyBlock ℂ φ j (F s)) →
      (∀ j, IntegrableOn (G j) (Set.Icc 0 T)) →
      ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
          eLpNorm (fun s ↦ eLpNorm (G j s) r₁' volume) p₁ (volume.restrict (Set.Icc 0 T)) ≠ ∞ →
      ∃ U : ℝ → Lp ℂ r (volume : Measure E),
        (∀ᵐ t ∂volume.restrict (Set.Icc 0 T), Tendsto (fun s : Finset ℤ ↦ eLpNorm (⇑(U t) -
          ⇑(∑ j ∈ s, waveDuhamelSolution ℂ (f.block j) (g.block j) (G j) t)) r volume) atTop
            (𝓝 0)) ∧
        Tendsto (fun s : Finset ℤ ↦ eLpNorm (fun t ↦ eLpNorm (⇑(U t) -
          ⇑(∑ j ∈ s, waveDuhamelSolution ℂ (f.block j) (g.block j) (G j) t)) r volume) q
            (volume.restrict (Set.Icc 0 T))) atTop (𝓝 0) ∧
        eLpNorm (fun t ↦ ‖U t‖ₑ) q (volume.restrict (Set.Icc 0 T)) ≤
          C' * (‖f‖ₑ + ‖g‖ₑ + ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
            eLpNorm (fun s ↦ eLpNorm (G j s) r₁' volume) p₁ (volume.restrict (Set.Icc 0 T))) := by
  obtain ⟨C', hC'⟩ := φ.exists_eLpNorm_eLpNorm_waveDuhamelSolution_le_of_eq_block hr₁' hC
  refine ⟨C', fun T f g F G hG hint hS ↦ ?_⟩
  set N : ℤ → ℝ≥0∞ := fun j ↦
    eLpNorm (fun s ↦ eLpNorm (G j s) r₁' volume) p₁ (volume.restrict (Set.Icc 0 T))
  -- The `j`-th term of the series is bounded by the `j`-th terms of the three dyadic norms.
  have hsum : ∑' j, eLpNorm (fun t ↦ eLpNorm (waveDuhamelSolution ℂ (f.block j) (g.block j)
      (G j) t) r volume) q (volume.restrict (Set.Icc 0 T)) ≤
        C' * (‖f‖ₑ + ‖g‖ₑ + ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) * N j) := by
    calc _ ≤ ∑' j : ℤ, C' * (ENNReal.ofReal (((2 : ℝ) ^ j) ^ γ) * ‖f.block j‖ₑ +
            ENNReal.ofReal (((2 : ℝ) ^ j) ^ (γ - 1)) * ‖g.block j‖ₑ +
            ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) * N j) :=
          tsum_le_tsum fun j ↦ hC' j (f.block j) (g.block j) (G j) T (hint j)
            ⟨f.toDistr, f.coe_block j⟩ ⟨g.toDistr, g.coe_block j⟩
            fun s hs ↦ ⟨F s, hG j s hs⟩
      _ = _ := by
          rw [ENNReal.tsum_mul_left, tsum_add, tsum_add]
          simp_rw [HomogeneousBesovSpace.ofReal_mul_eNorm_block,
            HomogeneousBesovSpace.tsum_eNorm_weightedBlocks]
  have hmeas (j : ℤ) : AEStronglyMeasurable
      (fun t ↦ waveDuhamelSolution ℂ (f.block j) (g.block j) (G j) t)
        (volume.restrict (Set.Icc 0 T)) :=
    aestronglyMeasurable_waveDuhamelSolution_restrict _ _ (hint j).aestronglyMeasurable
  have hfin : C' * (‖f‖ₑ + ‖g‖ₑ + ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) * N j) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨eNorm_ne_top, eNorm_ne_top⟩, hS⟩)
  obtain ⟨U, hae, hmix, hle⟩ :=
    exists_tendsto_eLpNorm_eLpNorm_sub_sum_of_tsum_ne_top hq hmeas (ne_top_of_le_ne_top hfin hsum)
  exact ⟨U, hae, hmix, hle.trans hsum⟩

variable [Nontrivial E]

/-- **Convergence of the dyadic Duhamel series on `[0, T]` with Besov data and dyadic forcing.**
Let `E` be nontrivial
of dimension `n`, let `Pⱼ` be the homogeneous Littlewood–Paley blocks built from `φ`, let `(q, r)`
be wave-admissible, `2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 ≤ q < ∞`, and let `(q₁, r₁)` be
wave-admissible with `2 ≤ q₁ ≤ ∞`, with Hölder conjugates `p₁` and `r₁'`, where `q = 2` and
`q₁ = 2` are allowed only in dimension `n ≥ 4`. Put `γ = n / 2 - n / r - 1 / q` and
`γ₁ = n / 2 - n / r₁ - 1 / q₁`. There is `C` such that the following holds for every `T`, all data
`f ∈ \dot B^γ_{2,1}` and `g ∈ \dot B^{γ - 1}_{2,1}`, and every family `F(s)` of tempered
distributions whose blocks `Gⱼ(s) = Pⱼ F(s)` at the times `s ∈ [0, T]` are `L²` functions,
integrable on `[0, T]`, with `∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Gⱼ‖_{L^{p₁}([0, T]; L^{r₁'}_x)} < ∞`: the
dyadic series

`∑ⱼ (cos(tD) Pⱼ f + D⁻¹ sin(tD) Pⱼ g + ∫₀ᵗ D⁻¹ sin((t - s)D) Gⱼ(s) ds)`

converges, to some `U : ℝ → L^r` in `L^r` for almost every `t ∈ [0, T]` and in
`L^q([0, T]; L^r_x)`, with

`‖U‖_{L^q([0, T]; L^r_x)} ≤ C (‖f‖_{\dot B^γ_{2,1}} + ‖g‖_{\dot B^{γ - 1}_{2,1}}`
`  + ∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Gⱼ‖_{L^{p₁}([0, T]; L^{r₁'}_x)})`. -/
theorem exists_tendsto_eLpNorm_eLpNorm_sub_sum_waveDuhamelSolution_block {q : ℝ≥0}
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hq : 2 ≤ q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq2 : q = 2 → 3 < Module.finrank ℝ E)
    {p₁ q₁ r₁ r₁' : ℝ≥0∞} [p₁.HolderConjugate q₁] [r₁'.HolderConjugate r₁] (hq₁ : 2 ≤ q₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq₁2 : q₁ = 2 → 3 < Module.finrank ℝ E) :
    ∃ C : ℝ≥0, ∀ (T : ℝ) (f : HomogeneousBesovSpace ℂ φ ((Module.finrank ℝ E : ℝ) / 2 -
        Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹) 2 1)
      (g : HomogeneousBesovSpace ℂ φ ((Module.finrank ℝ E : ℝ) / 2 -
        Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹ - 1) 2 1) (F : ℝ → 𝓢'(E, ℂ))
      (G : ℤ → ℝ → Lp ℂ 2 (volume : Measure E)),
      (∀ j, ∀ s ∈ Set.Icc 0 T,
        (G j s : 𝓢'(E, ℂ)) = homogeneousLittlewoodPaleyBlock ℂ φ j (F s)) →
      (∀ j, IntegrableOn (G j) (Set.Icc 0 T)) →
      ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹) + ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal) - 1)) *
          eLpNorm (fun s ↦ eLpNorm (G j s) r₁' volume) p₁ (volume.restrict (Set.Icc 0 T)) ≠ ∞ →
      ∃ U : ℝ → Lp ℂ r (volume : Measure E),
        (∀ᵐ t ∂volume.restrict (Set.Icc 0 T), Tendsto (fun s : Finset ℤ ↦ eLpNorm (⇑(U t) -
          ⇑(∑ j ∈ s, waveDuhamelSolution ℂ (f.block j) (g.block j) (G j) t)) r volume) atTop
            (𝓝 0)) ∧
        Tendsto (fun s : Finset ℤ ↦ eLpNorm (fun t ↦ eLpNorm (⇑(U t) -
          ⇑(∑ j ∈ s, waveDuhamelSolution ℂ (f.block j) (g.block j) (G j) t)) r volume) q
            (volume.restrict (Set.Icc 0 T))) atTop (𝓝 0) ∧
        eLpNorm (fun t ↦ ‖U t‖ₑ) q (volume.restrict (Set.Icc 0 T)) ≤
          C * (‖f‖ₑ + ‖g‖ₑ + ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^
            (((Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹) +
              ((Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r₁⁻¹).toReal -
                (q₁⁻¹).toReal) - 1)) *
            eLpNorm (fun s ↦ eLpNorm (G j s) r₁' volume) p₁ (volume.restrict (Set.Icc 0 T))) := by
  obtain ⟨C, hC⟩ := φ.exists_eLpNorm_eLpNorm_waveDuhamelSolution_le_tsum (p₁ := p₁) (r₁' := r₁')
    hq hqr hq2 hq₁ hqr₁ hq₁2
  exact φ.exists_tendsto_of_eLpNorm_eLpNorm_waveDuhamelSolution_le
    (by exact_mod_cast one_le_two.trans hq) (ENNReal.HolderConjugate.one_le r₁' r₁) hC

/-- **Convergence of the dyadic Duhamel series on `[0, T]` with Besov data and dyadic forcing, at
the pairs `(∞, r)`.** Let `E` be nontrivial of dimension `n`, let `Pⱼ` be the homogeneous
Littlewood–Paley blocks built from `φ`, let `2 ≤ r ≤ ∞` and `γ = n / 2 - n / r`. Let `(q₁, r₁)` be
wave-admissible with `2 ≤ q₁ ≤ ∞` and `2 ≤ r₁`, with Hölder conjugates `p₁` and `r₁'`, where
`q₁ = 2` only if `1 + (n - 1) / r₁ = (n - 1) / 2` in dimension `n ≥ 4`, and put
`γ₁ = n / 2 - n / r₁ - 1 / q₁`. There is `C` such that the following holds for every `T`, all
data `f ∈ \dot B^γ_{2,1}` and `g ∈ \dot B^{γ - 1}_{2,1}`, and every family `F(s)` of tempered
distributions whose blocks `Gⱼ(s) = Pⱼ F(s)` at the times `s ∈ [0, T]` are `L²` functions,
integrable on `[0, T]`, with `∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Gⱼ‖_{L^{p₁}([0, T]; L^{r₁'}_x)} < ∞`: the
dyadic series

`∑ⱼ (cos(tD) Pⱼ f + D⁻¹ sin(tD) Pⱼ g + ∫₀ᵗ D⁻¹ sin((t - s)D) Gⱼ(s) ds)`

converges, to some `U : ℝ → L^r` in `L^r` for almost every `t ∈ [0, T]` and in
`L^∞([0, T]; L^r_x)`, with

`‖U‖_{L^∞([0, T]; L^r_x)} ≤ C (‖f‖_{\dot B^γ_{2,1}} + ‖g‖_{\dot B^{γ - 1}_{2,1}}`
`  + ∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Gⱼ‖_{L^{p₁}([0, T]; L^{r₁'}_x)})`.

At `r = ∞` this bounds the sum `U` uniformly on `[0, T] × E`. -/
theorem exists_tendsto_eLpNorm_top_eLpNorm_sub_sum_waveDuhamelSolution_block {r : ℝ≥0∞}
    [Fact (1 ≤ r)] (hr : 2 ≤ r) {p₁ q₁ r₁ r₁' : ℝ≥0∞} [p₁.HolderConjugate q₁]
    [r₁'.HolderConjugate r₁] (hq₁ : 2 ≤ q₁) (hr₁ : 2 ≤ r₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq₁2 : q₁ = 2 → 3 < Module.finrank ℝ E ∧
      1 + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal = ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (T : ℝ) (f : HomogeneousBesovSpace ℂ φ ((Module.finrank ℝ E : ℝ) / 2 -
        Module.finrank ℝ E * (r⁻¹).toReal) 2 1)
      (g : HomogeneousBesovSpace ℂ φ ((Module.finrank ℝ E : ℝ) / 2 -
        Module.finrank ℝ E * (r⁻¹).toReal - 1) 2 1) (F : ℝ → 𝓢'(E, ℂ))
      (G : ℤ → ℝ → Lp ℂ 2 (volume : Measure E)),
      (∀ j, ∀ s ∈ Set.Icc 0 T,
        (G j s : 𝓢'(E, ℂ)) = homogeneousLittlewoodPaleyBlock ℂ φ j (F s)) →
      (∀ j, IntegrableOn (G j) (Set.Icc 0 T)) →
      ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal) + ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal) - 1)) *
          eLpNorm (fun s ↦ eLpNorm (G j s) r₁' volume) p₁ (volume.restrict (Set.Icc 0 T)) ≠ ∞ →
      ∃ U : ℝ → Lp ℂ r (volume : Measure E),
        (∀ᵐ t ∂volume.restrict (Set.Icc 0 T), Tendsto (fun s : Finset ℤ ↦ eLpNorm (⇑(U t) -
          ⇑(∑ j ∈ s, waveDuhamelSolution ℂ (f.block j) (g.block j) (G j) t)) r volume) atTop
            (𝓝 0)) ∧
        Tendsto (fun s : Finset ℤ ↦ eLpNorm (fun t ↦ eLpNorm (⇑(U t) -
          ⇑(∑ j ∈ s, waveDuhamelSolution ℂ (f.block j) (g.block j) (G j) t)) r volume) ∞
            (volume.restrict (Set.Icc 0 T))) atTop (𝓝 0) ∧
        eLpNorm (fun t ↦ ‖U t‖ₑ) ∞ (volume.restrict (Set.Icc 0 T)) ≤
          C * (‖f‖ₑ + ‖g‖ₑ + ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^
            (((Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r⁻¹).toReal) +
              ((Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r₁⁻¹).toReal -
                (q₁⁻¹).toReal) - 1)) *
            eLpNorm (fun s ↦ eLpNorm (G j s) r₁' volume) p₁ (volume.restrict (Set.Icc 0 T))) := by
  obtain ⟨C, hC⟩ := φ.exists_eLpNorm_top_eLpNorm_waveDuhamelSolution_le_tsum
    (p₁ := p₁) (r₁' := r₁') hr hq₁ hr₁ hqr₁ hq₁2
  exact φ.exists_tendsto_of_eLpNorm_eLpNorm_waveDuhamelSolution_le le_top
    (ENNReal.HolderConjugate.one_le r₁' r₁) hC

/-- **The dyadic series extends Duhamel's formula.** Let `f ∈ \dot B^γ_{2,b}` and
`g ∈ \dot B^{γ'}_{2,b'}` be `L²` functions `f₀` and `g₀`, and let `G₀ : ℝ → L²(E)` be integrable on
`[0, T]`. If the series `∑ⱼ (cos(tD) Pⱼ f + D⁻¹ sin(tD) Pⱼ g + ∫₀ᵗ D⁻¹ sin((t - s)D) Pⱼ G₀(s) ds)`
converges in `L^r` to `U(t)` for almost every `t ∈ [0, T]`, then `U(t)` is Duhamel's formula
`cos(tD) f₀ + D⁻¹ sin(tD) g₀ + ∫₀ᵗ D⁻¹ sin((t - s)D) G₀(s) ds` for almost every `t ∈ [0, T]`. -/
theorem ae_ae_eq_waveDuhamelSolution_of_tendsto {r : ℝ≥0∞} [Fact (1 ≤ r)] {γ γ' : ℝ}
    {b b' : ℝ≥0∞} {f : HomogeneousBesovSpace ℂ φ γ 2 b} {g : HomogeneousBesovSpace ℂ φ γ' 2 b'}
    {f₀ g₀ : Lp ℂ 2 (volume : Measure E)} (hf : f.toDistr = f₀) (hg : g.toDistr = g₀)
    {m : ℤ → Lp ℂ ∞ (volume : Measure E)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))
    {G₀ : ℝ → Lp ℂ 2 (volume : Measure E)} {T : ℝ} (hG₀ : IntegrableOn G₀ (Set.Icc 0 T))
    {U : ℝ → Lp ℂ r (volume : Measure E)}
    (hU : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), Tendsto (fun s : Finset ℤ ↦ eLpNorm (⇑(U t) -
      ⇑(∑ j ∈ s, waveDuhamelSolution ℂ (f.block j) (g.block j)
        (fun τ ↦ Lp.fourierMultiplierCLM ℂ (m j) (G₀ τ)) t)) r volume) atTop (𝓝 0)) :
    ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
      ⇑(U t) =ᵐ[volume] ⇑(waveDuhamelSolution ℂ f₀ g₀ G₀ t) := by
  filter_upwards [hU, ae_restrict_mem measurableSet_Icc] with t ht htT
  have hGt : IntervalIntegrable G₀ volume 0 t :=
    (hG₀.mono_set (by rw [Set.uIcc_of_le htT.1]; exact Set.Icc_subset_Icc le_rfl htT.2)
      ).intervalIntegrable
  -- Along the partial sums over `(-N, N]`, the series tends to `U(t)` in `L^r` and to the
  -- solution in `L²`, since its partial sums are the partial sums of the blocks of the solution.
  refine ae_eq_of_tendsto_eLpNorm_sub_sum_of_tendsto_sum ht (Finset.tendsto_Ioc_neg (R := ℤ))
    ((φ.tendsto_sum_fourierMultiplierCLM_littlewoodPaley hm _).congr fun N ↦ ?_)
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  -- The blocks of the Besov data are the `L²` blocks of `f₀` and `g₀`.
  rw [fourierMultiplierCLM_waveDuhamelSolution _ _ _ hGt,
    HomogeneousBesovSpace.block_eq_fourierMultiplierCLM hf (hm j),
    HomogeneousBesovSpace.block_eq_fourierMultiplierCLM hg (hm j)]

end ContDiffBump
