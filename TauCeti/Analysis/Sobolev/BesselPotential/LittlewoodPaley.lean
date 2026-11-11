/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace
import TauCeti.Analysis.Distribution.TemperedDistribution.BesselPotential
import TauCeti.Analysis.Fourier.L2Multiplier
import TauCeti.Analysis.InnerProductSpace.OrthogonalFamily
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The Littlewood–Paley characterization of `H^{s,2}`: `B^s_{2,2} = H^{s,2}`

For a real order `s` and a complex Hilbert space `F`, this file proves that the inhomogeneous
Besov space `B^s_{2,2}` built from a bump function `φ` (`TauCeti.BesovSpace`) and Mathlib's
Bessel-potential space `H^{s,2} = H^s` (`BesselPotentialSpace`) contain the same tempered
distributions, with equivalent norms:

`‖u‖_{H^s}² = ‖J^s u‖₂² ≍ ∑ⱼ 2^{2js} ‖Δⱼ u‖₂² = ‖u‖_{B^s_{2,2}}²`,

where `J^s = 𝓕⁻ (1 + ‖ξ‖²)^{s/2} 𝓕` is the Bessel potential and `Δⱼ` are the Littlewood–Paley
blocks of `φ`. The constants depend on `φ` and `s`. Thus at `p = q = 2` the Besov scale is the
Sobolev scale, which is how statements proved for Besov spaces (dyadic estimates, paraproducts)
specialize to `H^s`.

## Main declarations

* `TemperedDistribution.memBesov_two_two_iff_memSobolev`: `u ∈ B^s_{2,2}` if and only if
  `u ∈ H^{s,2}`.
* `TauCeti.BesovSpace.besselPotentialSpaceEquiv`: the identity on tempered distributions as an
  isomorphism of normed spaces `B^s_{2,2} ≃L[ℂ] H^{s,2}`.

## The argument

The order `0` case is Plancherel's theorem for the blocks. The blocks are `L²` Fourier
multipliers by the pieces `ψⱼ` of the Littlewood–Paley partition, which take values in `[-1, 1]`
and have disjoint supports when their indices differ by at least some `L`. Multipliers by real
symbols with disjoint supports have orthogonal ranges, so the blocks are almost orthogonal, and
`‖∑ⱼ gⱼ‖² ≤ L ∑ⱼ ‖gⱼ‖²` for almost orthogonal vectors
(`TauCeti.norm_sum_sq_le_mul_sum_norm_sq_of_inner_eq_zero`).

* If `f ∈ L²`, then `∑ ‖Δⱼ f‖² = Re ⟪f, ∑ Δⱼ Δⱼ f⟫ ≤ ‖f‖ (L ∑ ‖Δⱼ f‖²)^{1/2}`, so the blocks of
  `f` are square summable.
* Conversely, if the blocks `gⱼ = Δⱼ v` of a tempered distribution are `L²` functions with
  `∑ ‖gⱼ‖² < ∞`, then `gⱼ` is unchanged by the enlarged cutoff `Ψⱼ`, which equals `1` on the
  support of `ψⱼ` and vanishes on the support of `ψₖ` for `k` far from `j`. So the `gⱼ` are almost
  orthogonal, the series `∑ gⱼ` converges in `L²`, and its sum is `v` by Littlewood–Paley
  reconstruction in `𝓢'`.

General orders reduce to order `0`: `J^s` commutes with the blocks, and on the `j`-th block it is
the multiplier by the Schwartz symbol `(1 + ‖ξ‖²)^{s/2} Ψⱼ`, whose kernel has `L¹` norm `O(2^{js})`.
Young's inequality then gives `‖J^s Δⱼ u‖₂ ≤ C 2^{js} ‖Δⱼ u‖₂`
(`TemperedDistribution.exists_besselPotential_littlewoodPaleyBlock_eq_and_norm_le`), and the same
bound for `J^{-s}` gives the reverse.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Chapter 2 (the Littlewood–Paley decomposition and Besov spaces).
* H. Triebel, *Theory of Function Spaces*, Section 2.3.
-/

public section

noncomputable section

open MeasureTheory FourierTransform Filter Topology
open scoped ENNReal SchwartzMap InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace TemperedDistribution

section Multiplier

variable {u u₁ u₂ : E → ℝ} {m m₁ m₂ : Lp ℂ ∞ (volume : Measure E)}

/-- The `L²` multiplier by a smooth compactly supported real symbol agrees, as a tempered
distribution, with the multiplier on tempered distributions. -/
private theorem toTemperedDistribution_fourierMultiplierCLM (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hs : HasCompactSupport u) (hm : m =ᵐ[volume] fun ξ ↦ (u ξ : ℂ))
    (a : Lp F 2 (volume : Measure E)) :
    (Lp.fourierMultiplierCLM F m a : 𝓢'(E, F)) =
      fourierMultiplierCLM F (fun ξ ↦ (u ξ : ℂ)) (a : 𝓢'(E, F)) := by
  have hc : HasCompactSupport fun ξ ↦ (u ξ : ℂ) := hs.comp_left Complex.ofReal_zero
  have hd : ContDiff ℝ (⊤ : ℕ∞) fun ξ ↦ (u ξ : ℂ) := Complex.ofRealCLM.contDiff.comp hu
  have hg' := hd.continuous.memLp_top_of_hasCompactSupport hc (volume : Measure E)
  obtain rfl : m = hg'.toLp _ := Lp.ext (hm.trans hg'.coeFn_toLp.symm)
  exact (Lp.fourierMultiplierCLM_toTemperedDistribution_eq a (hc.hasTemperateGrowth hd) hg').symm

/-- A symbol that is almost everywhere real is self-adjoint in `L^∞`. -/
private theorem star_eq_self_of_ae_eq (hm : m =ᵐ[volume] fun ξ ↦ (u ξ : ℂ)) : star m = m :=
  Lp.ext <| by
    filter_upwards [Lp.coeFn_star m, hm] with ξ h₁ h₂
    rw [h₁, Pi.star_apply, h₂, Complex.star_def, Complex.conj_ofReal]

/-- The `L²` multiplier by a real symbol is self-adjoint. -/
private theorem inner_fourierMultiplierCLM_left (hm : m =ᵐ[volume] fun ξ ↦ (u ξ : ℂ))
    (a b : Lp F 2 (volume : Measure E)) :
    ⟪Lp.fourierMultiplierCLM F m a, b⟫_ℂ = ⟪a, Lp.fourierMultiplierCLM F m b⟫_ℂ :=
  (Lp.isSelfAdjoint_fourierMultiplierCLM (star_eq_self_of_ae_eq hm)).isSymmetric a b

/-- `L²` multipliers by real symbols with disjoint supports have orthogonal ranges. -/
private theorem inner_fourierMultiplierCLM_eq_zero (hm₁ : m₁ =ᵐ[volume] fun ξ ↦ (u₁ ξ : ℂ))
    (hm₂ : m₂ =ᵐ[volume] fun ξ ↦ (u₂ ξ : ℂ)) (h : ∀ ξ, u₁ ξ * u₂ ξ = 0)
    (a b : Lp F 2 (volume : Measure E)) :
    ⟪Lp.fourierMultiplierCLM F m₁ a, Lp.fourierMultiplierCLM F m₂ b⟫_ℂ = 0 := by
  refine Lp.inner_fourierMultiplierCLM_fourierMultiplierCLM_eq_zero ?_ a b
  rw [star_eq_self_of_ae_eq hm₁]
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_lpSMul (r := ∞) m₁ m₂, hm₁, hm₂,
    Lp.coeFn_zero ℂ ∞ (volume : Measure E)] with ξ h₁ h₂ h₃ h₄
  rw [h₁, Pi.smul_apply', h₂, h₃, h₄, smul_eq_mul, ← Complex.ofReal_mul, h, Complex.ofReal_zero,
    Pi.zero_apply]

end Multiplier

variable (φ : ContDiffBump (0 : E))

/-- Each piece `ψⱼ` of the Littlewood–Paley partition defines a symbol in `L^∞` of norm at most
`1`. -/
private theorem exists_ae_eq_inhomogeneousLittlewoodPaley_and_norm_le (j : ℕ) :
    ∃ m : Lp ℂ ∞ (volume : Measure E),
      m =ᵐ[volume] (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) ∧ ‖m‖ ≤ 1 := by
  have hc : HasCompactSupport fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) :=
    (φ.hasCompactSupport_inhomogeneousLittlewoodPaley j).comp_left Complex.ofReal_zero
  have hm := (Complex.continuous_ofReal.comp
    (φ.contDiff_inhomogeneousLittlewoodPaley j (n := 0)).continuous).memLp_top_of_hasCompactSupport
      hc (volume : Measure E)
  refine ⟨hm.toLp _, hm.coeFn_toLp, Lp.norm_top_le_of_ae_bound zero_le_one ?_⟩
  filter_upwards [hm.coeFn_toLp] with ξ hξ
  rw [hξ, Function.comp_apply, Complex.norm_real, Real.norm_eq_abs]
  exact φ.abs_inhomogeneousLittlewoodPaley_le_one j ξ

/-- **The Littlewood–Paley blocks of an `L²` function are square summable.** There is `C`,
depending only on `φ`, such that the blocks `Δⱼ f` of every `f ∈ L²` are `L²` functions with
`∑ⱼ ‖Δⱼ f‖² ≤ C ‖f‖²`. -/
private theorem exists_sum_norm_sq_littlewoodPaleyBlock_le :
    ∃ C : ℝ, ∀ f : Lp F 2 (volume : Measure E), ∃ g : ℕ → Lp F 2 (volume : Measure E),
      (∀ j, littlewoodPaleyBlock F φ j (f : 𝓢'(E, F)) = g j) ∧
        ∀ t : Finset ℕ, ∑ j ∈ t, ‖g j‖ ^ 2 ≤ C * ‖f‖ ^ 2 := by
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ
  choose m hm hm1 using exists_ae_eq_inhomogeneousLittlewoodPaley_and_norm_le φ
  set T : ℕ → Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
    fun j ↦ Lp.fourierMultiplierCLM F (m j)
  refine ⟨L, fun f ↦ ⟨fun j ↦ T j f, fun j ↦ ?_, fun t ↦ ?_⟩⟩
  · rw [littlewoodPaleyBlock_apply]
    exact (toTemperedDistribution_fourierMultiplierCLM (φ.contDiff_inhomogeneousLittlewoodPaley j)
      (φ.hasCompactSupport_inhomogeneousLittlewoodPaley j) (hm j) f).symm
  -- With `gⱼ = Δⱼ f`, `∑ ‖gⱼ‖² = Re ⟪f, ∑ Δⱼ gⱼ⟫`, and the vectors `Δⱼ gⱼ` are almost orthogonal.
  set A := ∑ j ∈ t, ‖T j f‖ ^ 2
  set S := ‖∑ j ∈ t, T j (T j f)‖
  have hA : A = RCLike.re ⟪f, ∑ j ∈ t, T j (T j f)⟫_ℂ := by
    rw [inner_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← inner_fourierMultiplierCLM_left (hm j), ← norm_sq_eq_re_inner (𝕜 := ℂ)]
  have hS : S ^ 2 ≤ L * A := by
    refine (TauCeti.norm_sum_sq_le_mul_sum_norm_sq_of_inner_eq_zero (fun i k hik ↦
      inner_fourierMultiplierCLM_eq_zero (hm i) (hm k) (hL i k hik) _ _) t).trans ?_
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦ ?_) (Nat.cast_nonneg L)
    exact pow_le_pow_left₀ (norm_nonneg _) ((Lp.norm_fourierMultiplierCLM_apply_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (hm1 j))) 2
  have hAS : A ≤ ‖f‖ * S := hA ▸ re_inner_le_norm _ _
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ ↦ by positivity
  -- `A² ≤ ‖f‖² S² ≤ ‖f‖² L A`, so `A ≤ L ‖f‖²`.
  have h : A * A ≤ (L * ‖f‖ ^ 2) * A := by
    calc A * A ≤ (‖f‖ * S) * (‖f‖ * S) := mul_self_le_mul_self hA0 hAS
      _ = ‖f‖ ^ 2 * S ^ 2 := by ring
      _ ≤ ‖f‖ ^ 2 * (L * A) := by gcongr
      _ = (L * ‖f‖ ^ 2) * A := by ring
  rcases hA0.eq_or_lt with h0 | h0
  · rw [← h0]
    positivity
  · exact le_of_mul_le_mul_right h h0

/-- **Almost orthogonality of `L²` blocks.** There is `L`, depending only on `φ`, such that if the
blocks `Δᵢ v` and `Δₖ v` of a tempered distribution `v` are `L²` functions `gᵢ` and `gₖ`, then
`⟪gᵢ, gₖ⟫ = 0` whenever `i + L ≤ k`. -/
private theorem exists_inner_eq_zero_of_littlewoodPaleyBlock_eq :
    ∃ L : ℕ, ∀ (v : 𝓢'(E, F)) (g : ℕ → Lp F 2 (volume : Measure E)),
      (∀ j, littlewoodPaleyBlock F φ j v = g j) → ∀ i k, i + L ≤ k → ⟪g i, g k⟫_ℂ = 0 := by
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ
  refine ⟨2 * L, fun v g hg ↦ ?_⟩
  have hinj : Function.Injective fun f : Lp F 2 (volume : Measure E) ↦ (f : 𝓢'(E, F)) :=
    LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot
  -- The enlarged cutoff `Ψᵢ` is `1` on the support of `ψᵢ` and vanishes on the support of `ψₖ`
  -- for `k ≥ i + 2L`.
  have hΨ : ∀ i k, i + 2 * L ≤ k → ∀ ξ,
      φ.enlargedLittlewoodPaley L i ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0 := by
    intro i k hik ξ
    rw [φ.enlargedLittlewoodPaley_apply, Finset.sum_mul]
    exact Finset.sum_eq_zero fun l hl ↦ hL l k (by rw [Finset.mem_Ico] at hl; omega) ξ
  have hc : ∀ i, HasCompactSupport fun ξ ↦ (φ.enlargedLittlewoodPaley L i ξ : ℂ) := fun i ↦
    (φ.hasCompactSupport_enlargedLittlewoodPaley L i).comp_left Complex.ofReal_zero
  have hM : ∀ i, ∃ M : Lp ℂ ∞ (volume : Measure E),
      M =ᵐ[volume] fun ξ ↦ (φ.enlargedLittlewoodPaley L i ξ : ℂ) := fun i ↦
    ⟨_, ((Complex.continuous_ofReal.comp (φ.contDiff_enlargedLittlewoodPaley L i
      (n := 0)).continuous).memLp_top_of_hasCompactSupport (hc i) volume).coeFn_toLp⟩
  choose M hM using hM
  set T : ℕ → Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
    fun i ↦ Lp.fourierMultiplierCLM F (M i)
  -- `Ψᵢ gₖ` is the multiplier by `ψₖ Ψᵢ` applied to `v`.
  have hT : ∀ i k, (T i (g k) : 𝓢'(E, F)) = fourierMultiplierCLM F (fun ξ ↦
      ((φ.inhomogeneousLittlewoodPaley k ξ * φ.enlargedLittlewoodPaley L i ξ : ℝ) : ℂ)) v := by
    intro i k
    rw [toTemperedDistribution_fourierMultiplierCLM (φ.contDiff_enlargedLittlewoodPaley L i)
      (φ.hasCompactSupport_enlargedLittlewoodPaley L i) (hM i), ← hg, littlewoodPaleyBlock_apply,
      fourierMultiplierCLM_fourierMultiplierCLM_apply
        (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley k)
        ((hc i).hasTemperateGrowth
          (Complex.ofRealCLM.contDiff.comp (φ.contDiff_enlargedLittlewoodPaley L i)))]
    congr 2
    funext ξ
    simp
  have hTg : ∀ i, T i (g i) = g i := fun i ↦ hinj <| by
    simp only [hT, ← hg, littlewoodPaleyBlock_apply]
    congr 2
    funext ξ
    rw [mul_comm, φ.enlargedLittlewoodPaley_mul_inhomogeneousLittlewoodPaley hL]
  have hT0 : ∀ i k, i + 2 * L ≤ k → T i (g k) = 0 := fun i k hik ↦ hinj <| by
    simp only [hT, mul_comm _ (φ.enlargedLittlewoodPaley L i _), hΨ i k hik, Complex.ofReal_zero,
      Lp.toTemperedDistribution_zero]
    simp [fourierMultiplierCLM_const]
  intro i k hik
  rw [← hTg i, inner_fourierMultiplierCLM_left (hM i), hT0 i k hik, inner_zero_right]

/-- **A tempered distribution with square-summable `L²` blocks is an `L²` function.** There is
`C`, depending only on `φ`, such that if every block `Δⱼ v` of `v ∈ 𝓢'` is an `L²` function `gⱼ`
with `∑ⱼ ‖gⱼ‖² < ∞`, then `v` is an `L²` function `f` with `‖f‖² ≤ C ∑ⱼ ‖gⱼ‖²`. -/
private theorem exists_eq_and_norm_sq_le_of_summable :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : 𝓢'(E, F)) (g : ℕ → Lp F 2 (volume : Measure E)),
      (∀ j, littlewoodPaleyBlock F φ j v = g j) → Summable (fun j ↦ ‖g j‖ ^ 2) →
        ∃ f : Lp F 2 (volume : Measure E), v = f ∧ ‖f‖ ^ 2 ≤ C * ∑' j, ‖g j‖ ^ 2 := by
  obtain ⟨L, hL⟩ := exists_inner_eq_zero_of_littlewoodPaleyBlock_eq (F := F) φ
  refine ⟨L, by positivity, fun v g hg hsq ↦ ?_⟩
  have hbound : ∀ t : Finset ℕ, ‖∑ j ∈ t, g j‖ ^ 2 ≤ L * ∑ j ∈ t, ‖g j‖ ^ 2 :=
    TauCeti.norm_sum_sq_le_mul_sum_norm_sq_of_inner_eq_zero (hL v g hg)
  -- The series `∑ gⱼ` converges in `L²` by the Cauchy criterion.
  have hsum : Summable g := summable_iff_vanishing_norm.2 fun ε hε ↦ by
    obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.1 hsq (ε ^ 2 / (L + 1)) (by positivity)
    refine ⟨s, fun t ht ↦ ?_⟩
    have h1 := hs t ht
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ ↦ by positivity)] at h1
    refine (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).1 ((hbound t).trans_lt ?_)
    calc (L : ℝ) * ∑ j ∈ t, ‖g j‖ ^ 2 ≤ (L + 1) * ∑ j ∈ t, ‖g j‖ ^ 2 := by
          gcongr
          linarith
      _ < (L + 1) * (ε ^ 2 / (L + 1)) := by gcongr
      _ = ε ^ 2 := by field_simp
  refine ⟨∑' j, g j, ?_, ?_⟩
  · -- In `𝓢'`, the partial sums `∑_{j < N} gⱼ` tend both to `v` and to `∑' j, gⱼ`.
    have h1 := tendsto_sum_littlewoodPaleyBlock φ v
    simp_rw [hg] at h1
    refine tendsto_nhds_unique h1 ?_
    have h2 := ((Lp.toTemperedDistributionCLM F (volume : Measure E) 2).continuous.tendsto _).comp
      hsum.hasSum.tendsto_sum_nat
    simpa [Function.comp_def, map_sum] using h2
  · refine le_of_tendsto' ((hsum.hasSum.tendsto_sum_nat.norm).pow 2) fun N ↦ (hbound _).trans ?_
    gcongr
    exact hsq.sum_le_tsum _ fun j _ ↦ by positivity

/-- `∑ⱼ (2^{sj} ‖fⱼ‖)²` controls `‖J^s u‖²` when the `fⱼ` are the blocks of `u`. -/
private theorem exists_besselPotential_eq_and_norm_sq_le (s : ℝ) :
    ∃ C : ℝ, ∀ (u : 𝓢'(E, F)) (f : ℕ → Lp F 2 (volume : Measure E)),
      (∀ j, littlewoodPaleyBlock F φ j u = f j) →
        Summable (fun j : ℕ ↦ (2 ^ (s * j) * ‖f j‖) ^ 2) →
          ∃ w : Lp F 2 (volume : Measure E), besselPotential E F s u = w ∧
            ‖w‖ ^ 2 ≤ C * ∑' j : ℕ, (2 ^ (s * j) * ‖f j‖) ^ 2 := by
  obtain ⟨C₁, -, hC₁⟩ := exists_besselPotential_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ s
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_eq_and_norm_sq_le_of_summable (F := F) φ
  refine ⟨C₂ * C₁ ^ 2, fun u f hf hsum ↦ ?_⟩
  choose g hg hgf using fun j ↦ hC₁ (p := 2) j u (f j) (hf j)
  have hgf' : ∀ j, ‖g j‖ ^ 2 ≤ C₁ ^ 2 * (2 ^ (s * j) * ‖f j‖) ^ 2 := fun j ↦ by
    rw [← mul_pow, ← mul_assoc]
    exact pow_le_pow_left₀ (norm_nonneg _) (hgf j) 2
  have hsum' : Summable fun j ↦ ‖g j‖ ^ 2 :=
    (hsum.mul_left (C₁ ^ 2)).of_nonneg_of_le (fun j ↦ by positivity) hgf'
  obtain ⟨w, hw, hwg⟩ :=
    hC₂ _ g (fun j ↦ (littlewoodPaleyBlock_besselPotential_comm φ s j u).trans (hg j)) hsum'
  refine ⟨w, hw, hwg.trans ?_⟩
  calc C₂ * ∑' j, ‖g j‖ ^ 2 ≤ C₂ * ∑' j : ℕ, C₁ ^ 2 * (2 ^ (s * j) * ‖f j‖) ^ 2 :=
        mul_le_mul_of_nonneg_left (hsum'.tsum_le_tsum hgf' (hsum.mul_left _)) hC₂0
    _ = C₂ * C₁ ^ 2 * ∑' j : ℕ, (2 ^ (s * j) * ‖f j‖) ^ 2 := by rw [tsum_mul_left, mul_assoc]

/-- `‖J^s u‖²` controls `∑ⱼ (2^{sj} ‖Δⱼ u‖)²`. -/
private theorem exists_littlewoodPaleyBlock_eq_and_sum_sq_le (s : ℝ) :
    ∃ C : ℝ, ∀ (u : 𝓢'(E, F)) (w : Lp F 2 (volume : Measure E)), besselPotential E F s u = w →
      ∃ f : ℕ → Lp F 2 (volume : Measure E), (∀ j, littlewoodPaleyBlock F φ j u = f j) ∧
        ∀ t : Finset ℕ, ∑ j ∈ t, (2 ^ (s * j) * ‖f j‖) ^ 2 ≤ C * ‖w‖ ^ 2 := by
  obtain ⟨C₁, -, hC₁⟩ :=
    exists_besselPotential_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ (-s)
  obtain ⟨C₂, hC₂⟩ := exists_sum_norm_sq_littlewoodPaleyBlock_le (F := F) φ
  refine ⟨C₁ ^ 2 * C₂, fun u w hw ↦ ?_⟩
  obtain ⟨g, hg, hgw⟩ := hC₂ w
  have hu : besselPotential E F (-s) (w : 𝓢'(E, F)) = u :=
    (besselPotential_neg_apply_eq_iff s _ _).2 hw
  choose f hf hfg using fun j ↦ hC₁ (p := 2) j w (g j) (hg j)
  refine ⟨f, fun j ↦ hu ▸ (littlewoodPaleyBlock_besselPotential_comm φ _ j _).trans (hf j),
    fun t ↦ ?_⟩
  have hfg' : ∀ j : ℕ, (2 ^ (s * j) * ‖f j‖) ^ 2 ≤ C₁ ^ 2 * ‖g j‖ ^ 2 := fun j ↦ by
    have h2 : (2 : ℝ) ^ (s * j) * 2 ^ (-s * j) = 1 := by
      rw [← Real.rpow_add two_pos, neg_mul, add_neg_cancel, Real.rpow_zero]
    calc (2 ^ (s * j) * ‖f j‖) ^ 2 ≤ (2 ^ (s * j) * (C₁ * 2 ^ (-s * j) * ‖g j‖)) ^ 2 := by
          gcongr
          exact hfg j
      _ = C₁ ^ 2 * ‖g j‖ ^ 2 := by
          rw [show (2 : ℝ) ^ (s * j) * (C₁ * 2 ^ (-s * j) * ‖g j‖) =
            C₁ * ((2 : ℝ) ^ (s * j) * 2 ^ (-s * j)) * ‖g j‖ by ring, h2]
          ring
  calc ∑ j ∈ t, (2 ^ (s * j) * ‖f j‖) ^ 2 ≤ ∑ j ∈ t, C₁ ^ 2 * ‖g j‖ ^ 2 :=
        Finset.sum_le_sum fun j _ ↦ hfg' j
    _ ≤ C₁ ^ 2 * C₂ * ‖w‖ ^ 2 := by
        rw [← Finset.mul_sum, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hgw t) (sq_nonneg C₁)

/-- **`B^s_{2,2} = H^{s,2}`.** A tempered distribution lies in the Besov space `B^s_{2,2}` built
from any bump function `φ` exactly when it lies in the Bessel-potential space `H^{s,2}`, that is,
when `J^s u = 𝓕⁻ ((1 + ‖ξ‖²)^{s/2} 𝓕 u)` is an `L²` function. -/
theorem memBesov_two_two_iff_memSobolev {s : ℝ} {u : 𝓢'(E, F)} :
    u.MemBesov φ s 2 2 ↔ u.MemSobolev s 2 := by
  have memℓp_two_iff_summable_sq : ∀ {a : ℕ → ℝ}, Memℓp a 2 ↔ Summable fun j ↦ a j ^ 2 := by
    intro a
    rw [memℓp_gen_iff (by simp)]
    simp
  constructor
  · intro hu
    obtain ⟨f, hf, hmem⟩ := memBesov_iff.1 hu
    obtain ⟨C, hC⟩ := exists_besselPotential_eq_and_norm_sq_le (F := F) φ s
    obtain ⟨w, hw, -⟩ := hC u f hf (memℓp_two_iff_summable_sq.1 hmem)
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    obtain ⟨C, hC⟩ := exists_littlewoodPaleyBlock_eq_and_sum_sq_le (F := F) φ s
    obtain ⟨f, hf, hfw⟩ := hC u w hw
    exact memBesov_iff.2 ⟨f, hf, memℓp_two_iff_summable_sq.2
      (summable_of_sum_le (fun j ↦ by positivity) hfw)⟩

end TemperedDistribution

namespace TauCeti.BesovSpace

open TemperedDistribution

variable {φ : ContDiffBump (0 : E)} {s : ℝ}

/-- The squared `B^s_{2,2}` norm is `∑ⱼ (2^{sj} ‖Δⱼ u‖)²`. -/
private theorem hasSum_sq (u : BesovSpace F φ s 2 2) :
    HasSum (fun j : ℕ ↦ (2 ^ (s * j) * ‖u.block j‖) ^ 2) (‖u‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by simp) u.weightedBlocks
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_weightedBlocks_apply,
    norm_weightedBlocks] at h
  exact h

variable (φ s) in
/-- The `H^{s,2}` norm is bounded by a multiple of the `B^s_{2,2}` norm. -/
private theorem exists_norm_le_of_toDistr_eq :
    ∃ C : ℝ, ∀ (u : BesovSpace F φ s 2 2) (v : BesselPotentialSpace E F s 2),
      v.toDistr = u.toDistr → ‖v‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC⟩ := exists_besselPotential_eq_and_norm_sq_le (F := F) φ s
  refine ⟨√C, fun u v huv ↦ ?_⟩
  obtain ⟨w, hw, hwu⟩ := hC u.toDistr u.block (fun j ↦ (u.coe_block j).symm) (hasSum_sq u).summable
  have hv : v.toLp = w := LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
    simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply,
      ← v.bessel_toDistr_eq_toLp, huv, hw]
  rw [← BesselPotentialSpace.norm_toLp_eq, hv, ← Real.sqrt_sq (norm_nonneg u),
    ← Real.sqrt_mul' _ (sq_nonneg _), ← (hasSum_sq u).tsum_eq]
  exact Real.le_sqrt_of_sq_le hwu

variable (φ s) in
/-- The `B^s_{2,2}` norm is bounded by a multiple of the `H^{s,2}` norm. -/
private theorem exists_norm_le_of_toDistr_eq' :
    ∃ C : ℝ, ∀ (v : BesselPotentialSpace E F s 2) (u : BesovSpace F φ s 2 2),
      u.toDistr = v.toDistr → ‖u‖ ≤ C * ‖v‖ := by
  obtain ⟨C, hC⟩ := exists_littlewoodPaleyBlock_eq_and_sum_sq_le (F := F) φ s
  refine ⟨√C, fun v u huv ↦ ?_⟩
  obtain ⟨f, hf, hfv⟩ := hC v.toDistr v.toLp v.bessel_toDistr_eq_toLp
  have hu : ∀ j, u.block j = f j := fun j ↦
    LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
      simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply, coe_block, huv,
        hf]
  rw [← BesselPotentialSpace.norm_toLp_eq, ← Real.sqrt_sq (norm_nonneg v.toLp),
    ← Real.sqrt_mul' _ (sq_nonneg _)]
  refine Real.le_sqrt_of_sq_le ?_
  rw [← (hasSum_sq u).tsum_eq]
  simp_rw [hu] at hfv ⊢
  exact Summable.tsum_le_of_sum_le ((hasSum_sq u).summable.congr fun j ↦ by rw [hu]) hfv

variable (F φ s) in
/-- **`B^s_{2,2} = H^{s,2}` with equivalent norms.** The identity on tempered distributions is an
isomorphism of normed spaces between the Besov space `B^s_{2,2}` built from `φ` and the
Bessel-potential space `H^{s,2}`. -/
def besselPotentialSpaceEquiv : BesovSpace F φ s 2 2 ≃L[ℂ] BesselPotentialSpace E F s 2 :=
  ContinuousLinearEquiv.equivOfInverse
    (LinearMap.mkContinuous
      { toFun u := ((memBesov_two_two_iff_memSobolev φ).1 u.memBesov_toDistr).toBesselPotentialSpace
        map_add' _ _ := BesselPotentialSpace.ext (by simp)
        map_smul' _ _ := BesselPotentialSpace.ext (by simp) }
      _ fun u ↦ (exists_norm_le_of_toDistr_eq (F := F) φ s).choose_spec u _ (by simp))
    (LinearMap.mkContinuous
      { toFun v := ((memBesov_two_two_iff_memSobolev φ).2 v.memSobolev_toDistr).toBesovSpace
        map_add' _ _ := BesovSpace.ext (by simp)
        map_smul' _ _ := BesovSpace.ext (by simp) }
      _ fun v ↦ (exists_norm_le_of_toDistr_eq' (F := F) φ s).choose_spec v _ (by simp))
    (fun _ ↦ BesovSpace.ext (by simp)) fun _ ↦ BesselPotentialSpace.ext (by simp)

@[simp]
theorem toDistr_besselPotentialSpaceEquiv (u : BesovSpace F φ s 2 2) :
    (besselPotentialSpaceEquiv F φ s u).toDistr = u.toDistr := by
  simp [besselPotentialSpaceEquiv]

@[simp]
theorem toDistr_besselPotentialSpaceEquiv_symm (v : BesselPotentialSpace E F s 2) :
    ((besselPotentialSpaceEquiv F φ s).symm v).toDistr = v.toDistr := by
  simp [besselPotentialSpaceEquiv]

end TauCeti.BesovSpace
