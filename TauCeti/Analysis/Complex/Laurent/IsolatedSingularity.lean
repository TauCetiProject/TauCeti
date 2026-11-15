/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import TauCeti.Analysis.Complex.Laurent.Series
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.Algebra.InfiniteSum.GroupCompletion
import TauCeti.Analysis.Complex.Laurent.Expansion
import TauCeti.Topology.MetricSpace.EBall

/-!
# Uniqueness of Laurent splittings and classification of isolated singularities

Let `E` be a complex normed space. Building on convergent Laurent series on concentric annuli from
`TauCeti.Analysis.Complex.Laurent.Series` and `TauCeti.Analysis.Complex.Laurent.Expansion`, this
file proves:

1. **Uniqueness of annular holomorphic splittings**
   (`TauCeti.eqOn_of_differentiableOn_eball_and_compl_closedBall_of_tendsto_cocompact` and
   `TauCeti.HasLaurentSeriesOnAnnulus.eqOn_laurentPosPart_and_laurentNegPart`): if two splittings
   `gPos + gNeg` and `hPos + hNeg` into a part holomorphic on `Metric.eball c R` and a part
   holomorphic on `(Metric.closedBall c r)ᶜ` vanishing at infinity agree on the overlap annulus
   `Metric.eball c R \ Metric.closedBall c r`, they agree separately on `Metric.eball c R` and
   `(Metric.closedBall c r)ᶜ`. Gluing `gPos - hPos` and `hNeg - gNeg` across the overlap gives an
   entire function vanishing along `Filter.cocompact ℂ`, to which Liouville's theorem applies
   without assuming completeness of `E`.
2. **Uniform tail convergence of `laurentNegPart` on exteriors of open disks**
   (`TauCeti.HasLaurentSeriesOnAnnulus.tendstoUniformlyOn_laurentNegPart`): for complete `E` and any
   `r < r'`, the finite partial sums over `Finset.range N` converge uniformly to
   `TauCeti.laurentNegPart a c` on `(Metric.ball c r')ᶜ`, even when `r'` exceeds the outer radius
   `R` of the original annulus.
3. **Casorati-Weierstrass / Laurent classification of isolated singularities**
   (`TauCeti.HasLaurentSeriesOnAnnulus.meromorphicOrderAt_eq_top_iff`,
   `TauCeti.HasLaurentSeriesOnAnnulus.meromorphicAt_and_meromorphicOrderAt_eq_iff`,
   `TauCeti.HasLaurentSeriesOnAnnulus.meromorphicAt_iff`, and
   `TauCeti.HasLaurentSeriesOnAnnulus.not_meromorphicAt_iff`): for a convergent Laurent series on a
   punctured disk `Metric.eball c R \ {c}`, meromorphy at `c` is equivalent to finiteness of the set
   of nonzero negative-degree coefficients, essential non-meromorphy to infinitude of that set, and
   integer meromorphic order `n : ℤ` to `a n ≠ 0` with `a m = 0` for all `m < n`.

## Main results

* `TauCeti.eqOn_of_differentiableOn_eball_and_compl_closedBall_of_tendsto_cocompact` and
  `TauCeti.HasLaurentSeriesOnAnnulus.eqOn_laurentPosPart_and_laurentNegPart`: uniqueness of annular
  holomorphic splittings vanishing at infinity.
* `TauCeti.laurentNegPart_eq_sum_range` and
  `TauCeti.HasLaurentSeriesOnAnnulus.tendstoUniformlyOn_laurentNegPart`: finite-pole evaluation and
  uniform exterior convergence of `laurentNegPart`.
* `TauCeti.HasLaurentSeriesOnAnnulus.comp_continuousLinearMap` and
  `TauCeti.HasLaurentSeriesOnAnnulus.sub_zpow_smul_self`: postcomposition with a continuous linear
  map and index shift under multiplication by `(w - c) ^ m`.
* `TauCeti.HasLaurentSeriesOnAnnulus.meromorphicOrderAt_eq_top_iff`,
  `TauCeti.HasLaurentSeriesOnAnnulus.meromorphicAt_and_meromorphicOrderAt_eq_iff`,
  `TauCeti.HasLaurentSeriesOnAnnulus.meromorphicAt_iff`, and
  `TauCeti.HasLaurentSeriesOnAnnulus.not_meromorphicAt_iff`: characterization of meromorphy,
  essential singularities, and meromorphic order via Laurent coefficients.

## References

* John B. Conway, *Functions of One Complex Variable I*, Graduate Texts in Mathematics 11,
  Springer, 2nd edition, 1978, Chapter V, §1.
* Lars V. Ahlfors, *Complex Analysis*, 3rd edition, McGraw-Hill, 1979, Chapter 5, §1.2.
* Armin Rainer, *Advanced Complex Analysis*, Corollary 7.5 and Theorem 7.6.
-/

public section

open Complex Filter Metric Set
open scoped ENNReal NNReal Real Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ### Uniqueness of annular holomorphic splittings -/

/-- **Uniqueness of annular holomorphic splittings.** Let `ENNReal.ofReal r < R`. Suppose
`gPos, hPos` are complex-differentiable on `Metric.eball c R` and `gNeg, hNeg` are
complex-differentiable on `(Metric.closedBall c r)ᶜ` and tend to `0` along `Filter.cocompact ℂ`.
If `gPos + gNeg` and `hPos + hNeg` agree on `Metric.eball c R \ Metric.closedBall c r`, then
`gPos = hPos` on `Metric.eball c R` and `gNeg = hNeg` on `(Metric.closedBall c r)ᶜ`. -/
theorem eqOn_of_differentiableOn_eball_and_compl_closedBall_of_tendsto_cocompact
    {gPos gNeg hPos hNeg : ℂ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞} (hrR : ENNReal.ofReal r < R)
    (hgPos : DifferentiableOn ℂ gPos (eball c R))
    (hgNeg : DifferentiableOn ℂ gNeg (closedBall c r)ᶜ)
    (hgNeg_lim : Tendsto gNeg (cocompact ℂ) (𝓝 0))
    (hhPos : DifferentiableOn ℂ hPos (eball c R))
    (hhNeg : DifferentiableOn ℂ hNeg (closedBall c r)ᶜ)
    (hhNeg_lim : Tendsto hNeg (cocompact ℂ) (𝓝 0))
    (heq : EqOn (gPos + gNeg) (hPos + hNeg) (eball c R \ closedBall c r)) :
    EqOn gPos hPos (eball c R) ∧ EqOn gNeg hNeg (closedBall c r)ᶜ := by
  classical
  let G : ℂ → E := fun z => if z ∈ eball c R then gPos z - hPos z else hNeg z - gNeg z
  have hG_pos : EqOn G (gPos - hPos) (eball c R) := fun z hz => ite_eq_left hz
  have hG_neg : EqOn G (hNeg - gNeg) (closedBall c r)ᶜ := fun z hz => by
    by_cases hzR : z ∈ eball c R
    · dsimp only [G, Pi.sub_apply]
      rw [ite_eq_left hzR, sub_eq_sub_iff_add_eq_add, add_comm (hNeg z)]
      exact heq ⟨hzR, hz⟩
    · exact ite_eq_right hzR
  have hG_diff : Differentiable ℂ G := fun z => by
    by_cases hzR : z ∈ eball c R
    · exact ((hgPos.sub hhPos).differentiableAt (isOpen_eball.mem_nhds hzR)).congr_of_eventuallyEq
        (hG_pos.eventuallyEq_of_mem (isOpen_eball.mem_nhds hzR))
    · have hzr : z ∈ (closedBall c r)ᶜ := fun hmem => hzR <| by
        rw [mem_eball, edist_dist]
        exact (ENNReal.ofReal_le_ofReal (mem_closedBall.mp hmem)).trans_lt hrR
      exact ((hhNeg.sub hgNeg).differentiableAt
        (isClosed_closedBall.isOpen_compl.mem_nhds hzr)).congr_of_eventuallyEq
        (hG_neg.eventuallyEq_of_mem (isClosed_closedBall.isOpen_compl.mem_nhds hzr))
  have hG_lim : Tendsto G (cocompact ℂ) (𝓝 0) := by
    have hlim : Tendsto (hNeg - gNeg) (cocompact ℂ) (𝓝 0) := by
      change Tendsto (fun z => hNeg z - gNeg z) (cocompact ℂ) (𝓝 0)
      simpa only [sub_zero] using hhNeg_lim.sub hgNeg_lim
    exact hlim.congr'
      (Filter.eventuallyEq_of_mem (isCompact_closedBall c r).compl_mem_cocompact fun z hz =>
        (hG_neg hz).symm)
  have hG_zero : ∀ z, G z = 0 := fun z => hG_diff.apply_eq_of_tendsto_cocompact z hG_lim
  exact ⟨fun z hz => sub_eq_zero.mp ((hG_pos hz).symm.trans (hG_zero z)),
    fun z hz => (sub_eq_zero.mp ((hG_neg hz).symm.trans (hG_zero z))).symm⟩

/-- When all negative-degree Laurent coefficients of index `-(k + 1)` with `m ≤ k` vanish,
`laurentNegPart a c w` reduces to the finite sum over `Finset.range m`. -/
theorem laurentNegPart_eq_sum_range {a : ℤ → E} {m : ℕ}
    (ha : ∀ k ≥ m, a (-((k : ℤ) + 1)) = 0) (c w : ℂ) :
    laurentNegPart a c w =
      ∑ k ∈ Finset.range m, (w - c) ^ (-((k : ℤ) + 1)) • a (-((k : ℤ) + 1)) := by
  rw [laurentNegPart_def, tsum_eq_sum]
  intro k hk
  rw [ha k (Nat.le_of_not_lt (Finset.mem_range.not.mp hk)), smul_zero]

namespace HasLaurentSeriesOnAnnulus

/-- Postcomposing a convergent Laurent series on an open annulus with a continuous complex-linear
map `L : E →L[ℂ] F` transforms its coefficients termwise by `L`. -/
theorem comp_continuousLinearMap {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) (L : E →L[ℂ] F) :
    HasLaurentSeriesOnAnnulus (L ∘ f) (L ∘ a) c r R where
  r_nonneg := h.r_nonneg
  r_lt := h.r_lt
  hasSum hw := ((h.hasSum hw).map L L.continuous).congr_fun fun n => by simp

/-- **Uniqueness of the Laurent decomposition.** If `f` has a convergent Laurent series with
coefficients `a` on `Metric.eball c R \ Metric.closedBall c r`, and `f = gPos + gNeg` on that
annulus where `gPos` is complex-differentiable on `Metric.eball c R` and `gNeg` is
complex-differentiable on `(Metric.closedBall c r)ᶜ` with `gNeg → 0` along `Filter.cocompact ℂ`,
then `gPos` agrees with `laurentPosPart a c` on `Metric.eball c R` and `gNeg` agrees with
`laurentNegPart a c` on `(Metric.closedBall c r)ᶜ`. -/
theorem eqOn_laurentPosPart_and_laurentNegPart
    {f gPos gNeg : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R)
    (hgPos : DifferentiableOn ℂ gPos (eball c R))
    (hgNeg : DifferentiableOn ℂ gNeg (closedBall c r)ᶜ)
    (hgNeg_lim : Tendsto gNeg (cocompact ℂ) (𝓝 0))
    (hfg : EqOn f (gPos + gNeg) (eball c R \ closedBall c r)) :
    EqOn gPos (laurentPosPart a c) (eball c R) ∧
      EqOn gNeg (laurentNegPart a c) (closedBall c r)ᶜ := by
  let L : E →L[ℂ] UniformSpace.Completion E := UniformSpace.Completion.toComplL
  have hc : HasLaurentSeriesOnAnnulus (L ∘ f) (L ∘ a) c r R := h.comp_continuousLinearMap L
  have hlim : Tendsto (L ∘ gNeg) (cocompact ℂ) (𝓝 0) := by
    simpa only [map_zero] using (L.continuous.tendsto 0).comp hgNeg_lim
  obtain ⟨heqPos, heqNeg⟩ :=
    eqOn_of_differentiableOn_eball_and_compl_closedBall_of_tendsto_cocompact h.r_lt
      (L.differentiable.comp_differentiableOn hgPos)
      (L.differentiable.comp_differentiableOn hgNeg) hlim
      hc.differentiableOn_laurentPosPart hc.differentiableOn_laurentNegPart
      hc.tendsto_laurentNegPart_cocompact fun w hw => by
        change L (gPos w) + L (gNeg w) = laurentPosPart (L ∘ a) c w + laurentNegPart (L ∘ a) c w
        rw [← map_add]
        change L ((gPos + gNeg) w) = _
        rw [← hfg hw]
        exact hc.eq_laurentPosPart_add_laurentNegPart hw
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · have hsum_c : HasSum (UniformSpace.Completion.toCompl ∘ fun n : ℕ => (w - c) ^ n • a n)
        (gPos w) := by
      have hp := hc.hasSum_laurentPosPart hw
      rw [← heqPos hw] at hp
      exact hp.congr_fun fun n => by simp [L]
    rw [laurentPosPart_def]
    exact ((hasSum_iff_hasSum_compl _ _).mp hsum_c).tsum_eq.symm
  · have hsum_c : HasSum (UniformSpace.Completion.toCompl ∘
        fun n : ℕ => (w - c) ^ (-((n : ℤ) + 1)) • a (-((n : ℤ) + 1))) (gNeg w) := by
      have hn := hc.hasSum_laurentNegPart hw
      rw [← heqNeg hw] at hn
      exact hn.congr_fun fun n => by simp [L]
    rw [laurentNegPart_def]
    exact ((hasSum_iff_hasSum_compl _ _).mp hsum_c).tsum_eq.symm

/-- For complete `E` and any `r < r'`, the finite partial sums over `Finset.range N` converge
uniformly on `(Metric.ball c r')ᶜ` to `laurentNegPart a c`. -/
theorem tendstoUniformlyOn_laurentNegPart [CompleteSpace E]
    {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r r' : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) (hrr' : r < r') :
    TendstoUniformlyOn
      (fun (N : ℕ) w => ∑ k ∈ Finset.range N, (w - c) ^ (-((k : ℤ) + 1)) • a (-((k : ℤ) + 1)))
      (laurentNegPart a c) atTop (ball c r')ᶜ := by
  obtain ⟨ρ₁, hrρ₁, hρ₁R⟩ := h.exists_radius
  let ρ : ℝ := min r' ρ₁
  have hrρ : r < ρ := lt_min hrr' hrρ₁
  have hρ_pos : 0 < ρ := h.r_nonneg.trans_lt hrρ
  have hρR : ENNReal.ofReal ρ < R := (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans_lt hρ₁R
  have htu := tendstoUniformlyOn_tsum_nat (s := (ball c r')ᶜ)
      (f := fun (k : ℕ) w => (w - c) ^ (-((k : ℤ) + 1)) • a (-((k : ℤ) + 1)))
      (h.summable_norm_mul_zpow_neg_add_one hrρ hρR) fun k w hw => by
    have hρw : ρ ≤ ‖w - c‖ :=
      (min_le_left _ _).trans
        (by simpa only [mem_compl_iff, mem_ball, dist_eq_norm, not_lt] using hw)
    rw [norm_smul, norm_zpow, mul_comm, ← Int.negSucc_eq, zpow_negSucc, zpow_negSucc]
    exact mul_le_mul_of_nonneg_left
      (inv_anti₀ (pow_pos hρ_pos (k + 1)) (pow_le_pow_left₀ hρ_pos.le hρw (k + 1))) (norm_nonneg _)
  simpa only [← laurentNegPart_def] using htu

/-! ### Index shift and isolated-singularity classification -/

/-- Multiplying a convergent Laurent series on `Metric.eball c R \ Metric.closedBall c r` by
`(w - c) ^ m` (`m : ℤ`) shifts its Laurent coefficients by `n ↦ a (n - m)`. -/
theorem sub_zpow_smul_self {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) (m : ℤ) :
    HasLaurentSeriesOnAnnulus (fun w => (w - c) ^ m • f w) (fun n => a (n - m)) c r R where
  r_nonneg := h.r_nonneg
  r_lt := h.r_lt
  hasSum {w} hw := by
    have hwc : w - c ≠ 0 :=
      sub_ne_zero.mpr (ne_of_mem_of_not_mem (mem_closedBall_self h.r_nonneg) hw.2).symm
    rw [← (Equiv.addRight m).hasSum_iff]
    refine ((h.hasSum hw).const_smul ((w - c) ^ m)).congr_fun fun n => ?_
    simp only [Function.comp_def, Equiv.coe_addRight, add_sub_cancel_right]
    rw [← mul_smul, ← zpow_add₀ hwc, add_comm]

/-- Completeness-free removable-singularity power-series extension on `Metric.eball c R`: since
`f` already converges in `E` on the punctured disk and `a 0` lies in `E`, the power series
`laurentPosPowerSeries a` converges to `Function.update f c (a 0)` in `E` without completeness. -/
private theorem hasFPowerSeriesOnBall_update_of_neg_eq_zero'
    {f : ℂ → E} {a : ℤ → E} {c : ℂ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c 0 R) (ha : ∀ k : ℕ, a (-((k : ℤ) + 1)) = 0) :
    HasFPowerSeriesOnBall (Function.update f c (a 0)) (laurentPosPowerSeries a) c R where
  r_le := h.le_radius_laurentPosPowerSeries
  r_pos := h.outerRadius_pos
  hasSum {y} hy := by
    let L : E →L[ℂ] UniformSpace.Completion E := UniformSpace.Completion.toComplL
    have hc := (h.comp_continuousLinearMap L).hasFPowerSeriesOnBall_update_of_neg_eq_zero
      fun k => by rw [Function.comp_apply, ha k, map_zero]
    have hsum_c : HasSum
        (UniformSpace.Completion.toCompl ∘ fun n : ℕ => laurentPosPowerSeries a n (fun _ => y))
        (Function.update f c (a 0) (c + y)) := by
      have hp := hc.hasSum hy
      have hupd : Function.update (L ∘ f) c ((L ∘ a) 0) (c + y) =
          L (Function.update f c (a 0) (c + y)) := by
        rcases eq_or_ne y 0 with rfl | hy0
        · simp
        · have hcy : c + y ≠ c := by simpa using hy0
          rw [Function.update_of_ne hcy, Function.update_of_ne hcy, Function.comp_apply]
      rw [hupd] at hp
      exact hp.congr_fun fun n => by simp [L, laurentPosPowerSeries_def]
    exact (hasSum_iff_hasSum_compl _ _).mp hsum_c

/-- Completeness-free negative-coefficient vanishing and constant-term extraction from local
analytic agreement near `c`. -/
private theorem coeff_neg_eq_zero_and_zero_eq_of_analyticAt
    {f g : ℂ → E} {a : ℤ → E} {c : ℂ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c 0 R) (hg : AnalyticAt ℂ g c) (hfg : f =ᶠ[𝓝[≠] c] g) :
    (∀ k : ℕ, a (-((k : ℤ) + 1)) = 0) ∧ a 0 = g c := by
  let L : E →L[ℂ] UniformSpace.Completion E := UniformSpace.Completion.toComplL
  have hc : HasLaurentSeriesOnAnnulus (L ∘ f) (L ∘ a) c 0 R := h.comp_continuousLinearMap L
  have hLg : AnalyticAt ℂ (L ∘ g) c := (L.analyticAt (g c)).comp hg
  have hLfg : L ∘ f =ᶠ[𝓝[≠] c] L ∘ g := hfg.fun_comp L
  have hinj : Function.Injective L := UniformSpace.Completion.toComplₗᵢ.injective
  refine ⟨fun k => hinj ?_, hinj (hc.coeff_zero_eq_of_analyticAt hLg hLfg)⟩
  simpa only [Function.comp_apply, map_zero] using
    hc.coeff_neg_add_one_eq_zero_of_analyticAt hLg hLfg k

/-- A function with a convergent Laurent series on `Metric.eball c R \ {c}` has infinite
meromorphic order (`⊤`) at `c` if and only if all of its Laurent coefficients vanish. -/
theorem meromorphicOrderAt_eq_top_iff {f : ℂ → E} {a : ℤ → E} {c : ℂ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c 0 R) :
    meromorphicOrderAt f c = ⊤ ↔ a = 0 := by
  rw [_root_.meromorphicOrderAt_eq_top_iff]
  refine ⟨fun hf0 => ?_, fun ha => ?_⟩
  · obtain ⟨ε, hε, hε0⟩ := EMetric.mem_nhdsWithin_iff.1 hf0
    let R₁ : ℝ≥0∞ := min R ε
    have hR₁ : ENNReal.ofReal 0 < R₁ := by simpa [R₁] using lt_min h.outerRadius_pos hε
    let L : E →L[ℂ] UniformSpace.Completion E := UniformSpace.Completion.toComplL
    have h₁ : HasLaurentSeriesOnAnnulus (fun _ => (0 : E)) a c 0 R₁ :=
      (h.mono le_rfl (min_le_left _ _) hR₁).congr fun w hw =>
        hε0 ⟨eball_subset_eball (min_le_right _ _) hw.1, by simpa using hw.2⟩
    have hcoeff := (h₁.comp_continuousLinearMap L).coeff_unique
      (HasLaurentSeriesOnAnnulus.zero c le_rfl hR₁)
    funext n
    exact UniformSpace.Completion.toComplₗᵢ.injective ((congrFun hcoeff n).trans (map_zero L).symm)
  · subst ha
    have hmem : eball c R \ closedBall c 0 ∈ 𝓝[≠] c := by
      rw [closedBall_zero]
      exact sdiff_mem_nhdsWithin_compl (isOpen_eball.mem_nhds (mem_eball_self h.outerRadius_pos)) _
    filter_upwards [hmem] with w hw
    exact (by simpa only [Pi.zero_apply, smul_zero] using h.hasSum hw :
      HasSum (fun _ : ℤ => (0 : E)) (f w)).unique hasSum_zero

/-- **Integer meromorphic order via Laurent coefficients.** For a convergent Laurent series on
`Metric.eball c R \ {c}` and any `n : ℤ` (covering poles when `n < 0`, regular nonzero values when
`n = 0`, and zeros when `0 < n`), `f` is meromorphic at `c` of order `n` if and only if `a n ≠ 0`
and `a m = 0` for all `m < n`. -/
theorem meromorphicAt_and_meromorphicOrderAt_eq_iff
    {f : ℂ → E} {a : ℤ → E} {c : ℂ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c 0 R) (n : ℤ) :
    MeromorphicAt f c ∧ meromorphicOrderAt f c = n ↔
      a n ≠ 0 ∧ ∀ m < n, a m = 0 := by
  have hshift : HasLaurentSeriesOnAnnulus (fun w => (w - c) ^ (-n) • f w)
      (fun k => a (k + n)) c 0 R := by
    simpa only [sub_neg_eq_add] using h.sub_zpow_smul_self (-n)
  refine ⟨fun ⟨hm, hord⟩ => ?_, fun ⟨han, hlt⟩ => ?_⟩
  · obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hm).mp hord
    have hFg : (fun w => (w - c) ^ (-n) • f w) =ᶠ[𝓝[≠] c] g := by
      filter_upwards [hfg, self_mem_nhdsWithin] with w hw hwc
      have hne : w - c ≠ 0 := sub_ne_zero.mpr hwc
      rw [hw, ← mul_smul, ← zpow_add₀ hne, neg_add_cancel, zpow_zero, one_smul]
    obtain ⟨hneg, hzero⟩ := hshift.coeff_neg_eq_zero_and_zero_eq_of_analyticAt hg hFg
    rw [zero_add] at hzero
    refine ⟨hzero ▸ hg0, fun m hm_lt => ?_⟩
    have hm_eq : -(((n - 1 - m).toNat : ℤ) + 1) + n = m := by omega
    simpa only [hm_eq] using hneg (n - 1 - m).toNat
  · have hneg : ∀ k : ℕ, a (-((k : ℤ) + 1) + n) = 0 := fun k => hlt _ (by omega)
    let g := Function.update (fun w => (w - c) ^ (-n) • f w) c (a (0 + n))
    have hg : AnalyticAt ℂ g c :=
      (hshift.hasFPowerSeriesOnBall_update_of_neg_eq_zero' hneg).analyticAt
    have hg0 : g c ≠ 0 := by simpa [g] using han
    have hf_eq : ∀ᶠ w in 𝓝[≠] c, f w = (w - c) ^ n • g w := by
      filter_upwards [self_mem_nhdsWithin] with w hwc
      have hne : w - c ≠ 0 := sub_ne_zero.mpr hwc
      simp only [g, Function.update_of_ne hwc, ← mul_smul, ← zpow_add₀ hne, add_neg_cancel,
        zpow_zero, one_smul]
    have hm : MeromorphicAt f c :=
      ((((MeromorphicAt.id c).sub (MeromorphicAt.const c c)).zpow n).smul hg.meromorphicAt).congr
        (EventuallyEq.symm hf_eq)
    exact ⟨hm, (meromorphicOrderAt_eq_int_iff hm).mpr ⟨g, hg, hg0, hf_eq⟩⟩

/-- **Characterization of meromorphy via Laurent coefficients.** A function with a convergent
Laurent series on `Metric.eball c R \ {c}` is meromorphic at `c` if and only if only finitely many
of its negative-degree coefficients are nonzero. -/
theorem meromorphicAt_iff {f : ℂ → E} {a : ℤ → E} {c : ℂ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c 0 R) :
    MeromorphicAt f c ↔ {k : ℕ | a (-((k : ℤ) + 1)) ≠ 0}.Finite := by
  refine ⟨fun ⟨N, hN⟩ => ?_, fun hfin => ?_⟩
  · have hshift : HasLaurentSeriesOnAnnulus (fun w => (w - c) ^ N • f w)
        (fun m => a (m - N)) c 0 R := by
      simpa only [zpow_natCast] using h.sub_zpow_smul_self (N : ℤ)
    obtain ⟨hneg, -⟩ := hshift.coeff_neg_eq_zero_and_zero_eq_of_analyticAt hN EventuallyEq.rfl
    refine (finite_Iio N).subset fun k hk => ?_
    rw [mem_Iio]
    refine not_le.mp fun hNk => hk ?_
    have hk_eq : -(((k - N : ℕ) : ℤ) + 1) - (N : ℤ) = -((k : ℤ) + 1) := by omega
    simpa only [hk_eq] using hneg (k - N)
  · obtain ⟨N, hN⟩ := hfin.bddAbove
    let M : ℕ := N + 1
    have hshift : HasLaurentSeriesOnAnnulus (fun w => (w - c) ^ M • f w)
        (fun m => a (m - M)) c 0 R := by
      simpa only [zpow_natCast] using h.sub_zpow_smul_self (M : ℤ)
    have hneg : ∀ j : ℕ, a (-((j : ℤ) + 1) - M) = 0 := fun j => by
      by_contra hne
      have hj_eq : -((j : ℤ) + 1) - (M : ℤ) = -(((j + M : ℕ) : ℤ) + 1) := by omega
      rw [hj_eq] at hne
      exact absurd (hN hne) (by dsimp [M]; omega)
    let g := Function.update (fun w => (w - c) ^ M • f w) c (a (0 - M))
    have hg : AnalyticAt ℂ g c :=
      (hshift.hasFPowerSeriesOnBall_update_of_neg_eq_zero' hneg).analyticAt
    have hf_eq : f =ᶠ[𝓝[≠] c] fun w => (w - c) ^ (-(M : ℤ)) • g w := by
      filter_upwards [self_mem_nhdsWithin] with w hwc
      have hne : w - c ≠ 0 := sub_ne_zero.mpr hwc
      simp only [g, Function.update_of_ne hwc, ← zpow_natCast, ← mul_smul,
        ← zpow_add₀ hne, neg_add_cancel, zpow_zero, one_smul]
    exact ((((MeromorphicAt.id c).sub (MeromorphicAt.const c c)).zpow (-(M : ℤ))).smul
      hg.meromorphicAt).congr hf_eq.symm

/-- **Characterization of essential singularities via Laurent coefficients.** A function with a
convergent Laurent series on `Metric.eball c R \ {c}` fails to be meromorphic at `c` (that is, has
an essential singularity at `c`) if and only if infinitely many of its negative-degree coefficients
are nonzero. -/
theorem not_meromorphicAt_iff {f : ℂ → E} {a : ℤ → E} {c : ℂ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c 0 R) :
    ¬ MeromorphicAt f c ↔ {k : ℕ | a (-((k : ℤ) + 1)) ≠ 0}.Infinite := by
  rw [h.meromorphicAt_iff, Set.Infinite]

end HasLaurentSeriesOnAnnulus

end TauCeti
