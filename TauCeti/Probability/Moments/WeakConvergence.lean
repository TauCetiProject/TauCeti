/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import TauCeti.Probability.Moments.Determinacy
import Mathlib.MeasureTheory.Measure.Prokhorov
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.PolynomialMemLp
import TauCeti.MeasureTheory.Measure.FiniteMeasure.UniformIntegrable
import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
import TauCeti.MeasureTheory.Measure.Tight.Moment

/-!
# Weak convergence from convergence of moments

The *method of moments* on the real line: if probability measures `μᵢ` on `ℝ` have eventually
finite moments of every order and `∫ xⁿ dμᵢ → ∫ xⁿ dμ` for every `n`, where the limit `μ` is
determined by its moments (`MeasureTheory.Measure.IsMomentDeterminate`), then `μᵢ → μ` weakly.
Finiteness is only assumed for the even moments, which control the others. The approximating
measures need not be compactly supported. This is how a limit theorem proved by computing moments,
such as the free central limit theorem, the moment convergence of a random-matrix ensemble or a
central limit theorem by cumulants, is turned into weak convergence of the corresponding laws.

Determinacy cannot be dropped: the log-normal law has the same moments as other probability
measures (`TauCeti.Probability.not_isMomentDeterminate_logNormalMeasure`), so moment convergence
to its moments does not identify a weak limit.

## Main results

* `TauCeti.abs_integral_eval_sub_le` — a polynomial within `δ` of a bounded continuous function
  almost everywhere has integral within `δ` of that of the function, against a probability measure.
* `MeasureTheory.FiniteMeasure.integrable_pow_two_mul_of_tendsto` and
  `MeasureTheory.FiniteMeasure.tendsto_integral_pow_of_tendsto` — along a weakly convergent
  family of finite measures with eventually finite and bounded moments of an even order `2k`, the
  limit has a finite moment of order `2k` when the filter is nontrivial, and the moments of every
  order `n < 2k` converge.
* `MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_integral_pow_of_isMomentDeterminate` — the
  method of moments for a moment-determinate limit.
* `MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_integral_pow_of_isMomentDeterminate` —
  when the even moments are eventually finite and eventually bounded, weak convergence to a
  moment-determinate law is convergence of all moments.
* `MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_integral_pow` — the special case of a
  compactly supported limit.
* `MeasureTheory.ProbabilityMeasure.exists_forall_mem_of_integral_pow_close_of_mem_nhds` — every
  weak neighbourhood of a moment-determinate law contains all laws whose moment of some even order
  `2N` is finite and whose moments up to order `2N` are close to its own.
* `MeasureTheory.ProbabilityMeasure.tendsto_measure_notMem_nhds_of_tendsto_measure_integral_pow`
  and `MeasureTheory.ProbabilityMeasure.ae_tendsto_of_ae_tendsto_integral_pow` — the versions for
  random probability measures, in measure on varying sample spaces (in probability when the
  sample measures are probability measures) and almost surely.
* `MeasureTheory.tendstoInDistribution_of_tendsto_integral_pow` — the version for real random
  variables and convergence in distribution.

## Implementation notes

The convergence `∫ p dμᵢ → ∫ p dμ` of the integral of a polynomial `p`, given the convergence of
the moments in its support and their integrability against `μ` and, eventually, against `μᵢ`, is
`TauCeti.tendsto_integral_eval_of_tendsto_integral_pow`
(`TauCeti.MeasureTheory.Function.PolynomialMemLp`).

The proof runs through Prokhorov's theorem. Convergent second moments are eventually bounded,
so the family restricted to an eventual set of indices is tight, and every cluster point `ν` is
its limit along some finer ultrafilter. A bound on the moment of order `2k` makes the moments of
order `n < 2k` converge along the family (`TauCeti.tendsto_integral_of_rpow_bound` with exponent
`2k / n > 1`), so `ν` has the limiting moments, and determinacy gives `ν = μ`. The random
versions use the neighbourhood form and a finite union bound
(`MeasureTheory.tendsto_measure_of_subset_biUnion_finset`).

## References

* P. Billingsley, *Probability and Measure*, 3rd ed., Wiley (1995), Theorems 30.1 and 30.2.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), Theorem 2.4.4 and its proof.
-/

public section

open MeasureTheory Filter Polynomial Set Finset
open scoped Topology ENNReal BoundedContinuousFunction

namespace TauCeti

/-- A finite moment of order `2k` that is at most `C` bounds the lower integral of `x²ᵏ` by
`ofReal C`. -/
private theorem lintegral_ofReal_pow_two_mul_le {ρ : Measure ℝ} {k : ℕ} {C : ℝ}
    (h : Integrable (fun x : ℝ ↦ x ^ (2 * k)) ρ) (hC : ∫ x, x ^ (2 * k) ∂ρ ≤ C) :
    ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂ρ ≤ ENNReal.ofReal C := by
  rw [← ofReal_integral_eq_lintegral_ofReal h (ae_of_all _ fun x ↦ (even_two_mul k).pow_nonneg x)]
  exact ENNReal.ofReal_le_ofReal hC

/-- If `|p - f| ≤ δ` almost everywhere for a probability measure `μ`, then
`|∫ p dμ - ∫ f dμ| ≤ δ`. -/
theorem abs_integral_eval_sub_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f : ℝ →ᵇ ℝ} {p : ℝ[X]} {δ : ℝ} (hp : ∀ᵐ x ∂μ, |p.eval x - f x| ≤ δ) :
    |∫ x, p.eval x ∂μ - ∫ x, f x ∂μ| ≤ δ := by
  have hb : ∀ᵐ x ∂μ, ‖p.eval x - f x‖ ≤ δ := hp.mono fun x hx => (Real.norm_eq_abs _).trans_le hx
  have hpf : Integrable (fun x => p.eval x - f x) μ :=
    .of_bound (p.continuous.sub f.continuous).aestronglyMeasurable δ hb
  rw [← integral_sub ((hpf.add (f.integrable μ)).congr (.of_forall fun x => sub_add_cancel _ _))
    (f.integrable μ)]
  have := norm_integral_le_of_norm_le_const hb
  rwa [Real.norm_eq_abs, probReal_univ, mul_one] at this

end TauCeti

namespace MeasureTheory.FiniteMeasure

open TauCeti

variable {ι : Type*} {l : Filter ι}

/-! ### Moments along weakly convergent families -/

/-- **Weak limits inherit bounded even moments.** If finite measures `μᵢ → μ` weakly along a
nontrivial filter and the moments of order `2k` are eventually finite and at most `C`, then the
moment of order `2k` of `μ` is finite. -/
theorem integrable_pow_two_mul_of_tendsto [l.NeBot] {μs : ι → FiniteMeasure ℝ}
    {μ : FiniteMeasure ℝ} (h : Tendsto μs l (𝓝 μ)) {k : ℕ} {C : ℝ}
    (hint : ∀ᶠ i in l, Integrable (fun x : ℝ ↦ x ^ (2 * k)) (μs i : Measure ℝ))
    (hC : ∀ᶠ i in l, ∫ x, x ^ (2 * k) ∂(μs i : Measure ℝ) ≤ C) :
    Integrable (fun x : ℝ ↦ x ^ (2 * k)) (μ : Measure ℝ) := by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x ↦ (even_two_mul k).pow_nonneg x)]
  exact (lintegral_le_of_tendsto_finiteMeasure
    (ENNReal.continuous_ofReal.comp (continuous_pow _)).lowerSemicontinuous h
    ((hint.and hC).mono fun i hi ↦ lintegral_ofReal_pow_two_mul_le hi.1 hi.2)).trans_lt
    ENNReal.ofReal_lt_top

/-- **Moments along weak convergence.** If finite measures `μᵢ → μ` weakly and the moments of an
even order `2k` are eventually finite and at most `C`, then every moment of lower order converges:
`∫ xⁿ dμᵢ → ∫ xⁿ dμ` for `n < 2k`. The moment of order `0` is the mass. -/
theorem tendsto_integral_pow_of_tendsto {μs : ι → FiniteMeasure ℝ}
    {μ : FiniteMeasure ℝ} (h : Tendsto μs l (𝓝 μ)) {k : ℕ} {C : ℝ}
    (hint : ∀ᶠ i in l, Integrable (fun x : ℝ ↦ x ^ (2 * k)) (μs i : Measure ℝ))
    (hC : ∀ᶠ i in l, ∫ x, x ^ (2 * k) ∂(μs i : Measure ℝ) ≤ C) {n : ℕ} (hn : n < 2 * k) :
    Tendsto (fun i ↦ ∫ x, x ^ n ∂(μs i : Measure ℝ)) l (𝓝 (∫ x, x ^ n ∂(μ : Measure ℝ))) := by
  rcases eq_or_ne n 0 with rfl | hn₀
  · simpa using tendsto_iff_forall_integral_tendsto.1 h 1
  -- The power `2k / n > 1` of `|xⁿ|` is `x²ᵏ`.
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn₀)
  have hp : (1 : ℝ) < ((2 * k : ℕ) : ℝ) / n := by
    rw [one_lt_div hn']
    exact_mod_cast hn
  refine tendsto_integral_of_rpow_bound (by fun_prop) h hp (C := C.toNNReal) ?_
  filter_upwards [hint, hC] with i hi hiC
  calc ∫⁻ x, ‖x ^ n‖ₑ ^ (((2 * k : ℕ) : ℝ) / n) ∂(μs i : Measure ℝ)
      = ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(μs i : Measure ℝ) := by
        refine lintegral_congr fun x ↦ ?_
        rw [Real.eNorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _)
          (by positivity), abs_pow, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x),
          mul_div_cancel₀ _ hn'.ne', Real.rpow_natCast, (even_two_mul k).pow_abs]
    _ ≤ ENNReal.ofReal C := lintegral_ofReal_pow_two_mul_le hi hiC

end MeasureTheory.FiniteMeasure

namespace MeasureTheory.ProbabilityMeasure

open TauCeti

variable {ι : Type*} {l : Filter ι}

/-! ### The method of moments -/

/-- **The method of moments for a moment-determinate limit.** Let `μᵢ` and `μ` be probability
measures on `ℝ` such that `μ` is determined by its moments, every even moment of `μᵢ` is
eventually finite, and `∫ xⁿ dμᵢ → ∫ xⁿ dμ` for every `n`. Then `μᵢ → μ` weakly. -/
theorem tendsto_of_tendsto_integral_pow_of_isMomentDeterminate {μs : ι → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ).IsMomentDeterminate)
    (hμs : ∀ n, ∀ᶠ i in l, Integrable (fun x : ℝ ↦ x ^ (2 * n)) (μs i : Measure ℝ))
    (h : ∀ n, Tendsto (fun i ↦ ∫ x, x ^ n ∂(μs i : Measure ℝ)) l
      (𝓝 (∫ x, x ^ n ∂(μ : Measure ℝ)))) :
    Tendsto μs l (𝓝 μ) := by
  -- Each even moment is eventually at most its limit plus one.
  have hbound (n : ℕ) : ∀ᶠ i in l, ∫ x, x ^ (2 * n) ∂(μs i : Measure ℝ) ≤
      ∫ x, x ^ (2 * n) ∂(μ : Measure ℝ) + 1 :=
    (h (2 * n)).eventually (eventually_le_nhds (lt_add_one _))
  -- The family restricted to the eventual set of indices where the second moment is finite and
  -- bounded is tight.
  set s := {i | Integrable (fun x : ℝ ↦ x ^ (2 * 1)) (μs i : Measure ℝ) ∧
    ∫ x, x ^ (2 * 1) ∂(μs i : Measure ℝ) ≤ ∫ x, x ^ (2 * 1) ∂(μ : Measure ℝ) + 1}
  have hs : s ∈ l := (hμs 1).and (hbound 1)
  have hcomp : IsCompact (closure (μs '' s)) := by
    refine isCompact_closure_of_isTightMeasureSet (isTightMeasureSet_of_lintegral_edist_rpow_le 0
      two_pos (C := ENNReal.ofReal (∫ x, x ^ (2 * 1) ∂(μ : Measure ℝ) + 1))
      ENNReal.ofReal_ne_top ?_)
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    refine (lintegral_congr fun x ↦ ?_).trans_le (lintegral_ofReal_pow_two_mul_le hi.1 hi.2)
    rw [edist_dist, dist_zero_right, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg x) zero_le_two,
      Real.rpow_two, Real.norm_eq_abs, sq_abs, mul_one]
  -- Every cluster point `ν` is a limit along some ultrafilter `U ≤ l`, so it has the limiting
  -- moments, hence is `μ`.
  refine hcomp.tendsto_nhds_of_unique_mapClusterPt
    (mem_of_superset hs fun i hi ↦ subset_closure (mem_image_of_mem μs hi)) fun ν _ hν ↦ ?_
  obtain ⟨U, hU, hνU⟩ := mapClusterPt_iff_ultrafilter.mp hν
  have hνU' := (tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds _).1 hνU
  have hνint (n : ℕ) : Integrable (fun x : ℝ ↦ x ^ n) (ν : Measure ℝ) :=
    integrable_pow_of_integrable_pow_two_mul (k := n) (by omega)
      (FiniteMeasure.integrable_pow_two_mul_of_tendsto hνU' ((hμs n).filter_mono hU)
        ((hbound n).filter_mono hU))
  have hνmom (n : ℕ) : ∫ x, x ^ n ∂(ν : Measure ℝ) = ∫ x, x ^ n ∂(μ : Measure ℝ) :=
    tendsto_nhds_unique (FiniteMeasure.tendsto_integral_pow_of_tendsto hνU'
      ((hμs (n + 1)).filter_mono hU) ((hbound (n + 1)).filter_mono hU) (by omega))
      ((h n).mono_left hU)
  exact toMeasure_injective (hμ.eq_of_forall_integral_pow_eq hνint hνmom)

/-- **Weak convergence and convergence of moments.** If every even moment of `μᵢ` is eventually
finite and eventually bounded, then `μᵢ` converges weakly to a moment-determinate law `μ` if and
only if `∫ xⁿ dμᵢ → ∫ xⁿ dμ` for every `n`. -/
theorem tendsto_iff_tendsto_integral_pow_of_isMomentDeterminate {μs : ι → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ).IsMomentDeterminate)
    (hμs : ∀ n, ∀ᶠ i in l, Integrable (fun x : ℝ ↦ x ^ (2 * n)) (μs i : Measure ℝ))
    (hbdd : ∀ n, ∃ C, ∀ᶠ i in l, ∫ x, x ^ (2 * n) ∂(μs i : Measure ℝ) ≤ C) :
    Tendsto μs l (𝓝 μ) ↔ ∀ n, Tendsto (fun i ↦ ∫ x, x ^ n ∂(μs i : Measure ℝ)) l
      (𝓝 (∫ x, x ^ n ∂(μ : Measure ℝ))) :=
  ⟨fun h n ↦ (hbdd (n + 1)).elim fun _ hC ↦ FiniteMeasure.tendsto_integral_pow_of_tendsto
      ((tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds l).1 h) (hμs (n + 1)) hC (by omega),
    tendsto_of_tendsto_integral_pow_of_isMomentDeterminate hμ hμs⟩

/-- **The method of moments for a compactly supported limit.** Let `μᵢ` and `μ` be probability
measures on `ℝ` such that `μ` is concentrated on a compact set, every even moment of `μᵢ` is
eventually finite, and `∫ xⁿ dμᵢ → ∫ xⁿ dμ` for every `n`. Then `μᵢ → μ` weakly. -/
theorem tendsto_of_tendsto_integral_pow {μs : ι → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} {K : Set ℝ} (hK : IsCompact K) (hμK : (μ : Measure ℝ) Kᶜ = 0)
    (hμs : ∀ n, ∀ᶠ i in l, Integrable (fun x : ℝ ↦ x ^ (2 * n)) (μs i : Measure ℝ))
    (h : ∀ n, Tendsto (fun i ↦ ∫ x, x ^ n ∂(μs i : Measure ℝ)) l
      (𝓝 (∫ x, x ^ n ∂(μ : Measure ℝ)))) :
    Tendsto μs l (𝓝 μ) :=
  tendsto_of_tendsto_integral_pow_of_isMomentDeterminate
    (.of_isCompact_of_measure_compl_eq_zero hK hμK) hμs h

/-- **Weak neighbourhoods of a moment-determinate law.** Every weak neighbourhood `U` of a
moment-determinate probability measure `μ` on `ℝ` contains, for some `N` and `δ > 0`, each
probability measure whose moment of order `2N` is finite and whose moments of order at most `2N`
are within `δ` of those of `μ`. The finiteness is part of the condition, since a measure with an
infinite moment has the junk value `0` as its Bochner integral. -/
theorem exists_forall_mem_of_integral_pow_close_of_mem_nhds {μ : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ).IsMomentDeterminate) {U : Set (ProbabilityMeasure ℝ)}
    (hU : U ∈ 𝓝 μ) :
    ∃ N : ℕ, ∃ δ > 0, ∀ ν : ProbabilityMeasure ℝ,
      Integrable (fun x : ℝ ↦ x ^ (2 * N)) (ν : Measure ℝ) →
      (∀ n ≤ 2 * N, |∫ x, x ^ n ∂(ν : Measure ℝ) - ∫ x, x ^ n ∂(μ : Measure ℝ)| < δ) →
        ν ∈ U := by
  -- Otherwise measures outside `U` with ever closer moments converge to `μ`.
  by_contra! hne
  choose ν hνint hν hνU using fun N : ℕ ↦ hne N (1 / (N + 1)) Nat.one_div_pos_of_nat
  have hlim : Tendsto ν atTop (𝓝 μ) := by
    refine tendsto_of_tendsto_integral_pow_of_isMomentDeterminate hμ
      (fun n ↦ (eventually_ge_atTop n).mono fun N hN ↦
        integrable_pow_of_integrable_pow_two_mul (by omega) (hνint N)) fun n ↦ ?_
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _)
      ((eventually_ge_atTop n).mono fun N hN ↦ (hν N n (by omega)).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  obtain ⟨N, hN⟩ := (hlim.eventually hU).exists
  exact hνU N hN

/-! ### Random probability measures -/

/-- **The method of moments in measure.** Let `μᵢ ω` be random probability measures on `ℝ`,
indexed by `ω` in spaces `Ωᵢ` with measures `Pᵢ` that may vary with `i`. Suppose that for every
`n` the outer measure of the event that the moment of order `2n` of `μᵢ` is infinite tends to
zero, and that every moment of `μᵢ` converges in measure to the corresponding moment of a
moment-determinate law `μ`. Then `μᵢ → μ` weakly in measure: `Pᵢ (μᵢ ∉ U) → 0` for every weak
neighbourhood `U` of `μ`. For probability measures `Pᵢ` this is convergence in probability. No
measurability of the random measures or of these events is needed, since only outer measures
appear. By `MeasureTheory.ProbabilityMeasure.tendsto_measure_notMem_nhds_iff_integral`, the
conclusion is convergence in measure of every bounded continuous test integral `∫ f dμᵢ` to
`∫ f dμ`. -/
theorem tendsto_measure_notMem_nhds_of_tendsto_measure_integral_pow
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (P : (i : ι) → Measure (Ω i)) (μs : (i : ι) → Ω i → ProbabilityMeasure ℝ)
    (l : Filter ι) {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ).IsMomentDeterminate)
    (hint : ∀ n, Tendsto (fun i ↦ P i {ω | ¬Integrable (fun x : ℝ ↦ x ^ (2 * n))
      (μs i ω : Measure ℝ)}) l (𝓝 0))
    (h : ∀ n, ∀ ε : ℝ, 0 < ε → Tendsto (fun i ↦ P i {ω |
      ε ≤ |∫ x, x ^ n ∂(μs i ω : Measure ℝ) - ∫ x, x ^ n ∂(μ : Measure ℝ)|}) l (𝓝 0))
    {U : Set (ProbabilityMeasure ℝ)} (hU : U ∈ 𝓝 μ) :
    Tendsto (fun i ↦ P i {ω | μs i ω ∉ U}) l (𝓝 0) := by
  obtain ⟨N, δ, hδ, hN⟩ := exists_forall_mem_of_integral_pow_close_of_mem_nhds hμ hU
  -- Outside `U`, the moment of order `2N` is infinite or some moment of order at most `2N` is
  -- `δ`-far from its limit.
  refine tendsto_measure_of_subset_biUnion_finset (range (2 * N + 1))
    (A := fun n i ↦ {ω | ¬Integrable (fun x : ℝ ↦ x ^ (2 * N)) (μs i ω : Measure ℝ)} ∪
      {ω | δ ≤ |∫ x, x ^ n ∂(μs i ω : Measure ℝ) - ∫ x, x ^ n ∂(μ : Measure ℝ)|})
    (fun n _ ↦ tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using (hint N).add (h n δ hδ)) (fun _ ↦ zero_le) fun _ ↦ measure_union_le _ _)
    fun i ω hω ↦ ?_
  by_contra hcon
  simp only [mem_iUnion, mem_union, mem_ofPred_eq, Finset.mem_range, not_exists, not_or,
    not_le, not_not] at hcon
  exact hω (hN _ (hcon 0 (by omega)).1 fun n hn ↦ (hcon n (by omega)).2)

/-- **The method of moments almost surely.** If almost surely every even moment of the random
probability measures `μᵢ ω` is eventually finite and every moment converges to the corresponding
moment of a moment-determinate law `μ`, then almost surely `μᵢ ω → μ` weakly. The exceptional null
sets may depend on the order of the moment. -/
theorem ae_tendsto_of_ae_tendsto_integral_pow {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {μs : ι → Ω → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ).IsMomentDeterminate)
    (hμs : ∀ n, ∀ᵐ ω ∂P, ∀ᶠ i in l, Integrable (fun x : ℝ ↦ x ^ (2 * n)) (μs i ω : Measure ℝ))
    (h : ∀ n, ∀ᵐ ω ∂P, Tendsto (fun i ↦ ∫ x, x ^ n ∂(μs i ω : Measure ℝ)) l
      (𝓝 (∫ x, x ^ n ∂(μ : Measure ℝ)))) :
    ∀ᵐ ω ∂P, Tendsto (fun i ↦ μs i ω) l (𝓝 μ) := by
  filter_upwards [ae_all_iff.2 hμs, ae_all_iff.2 h] with ω hω₁ hω₂
  exact tendsto_of_tendsto_integral_pow_of_isMomentDeterminate hμ hω₁ hω₂

end MeasureTheory.ProbabilityMeasure

namespace MeasureTheory

/-- **The method of moments for random variables.** Real random variables `Xᵢ` whose even moments
are eventually finite and whose moments converge to those of a random variable `Z`, whose law is
determined by its moments, converge to `Z` in distribution. -/
theorem tendstoInDistribution_of_tendsto_integral_pow {ι : Type*} {l : Filter ι}
    {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)} {P : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (P i)] {Ω' : Type*} {m' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X : (i : ι) → Ω i → ℝ} {Z : Ω' → ℝ}
    (hX : ∀ i, AEMeasurable (X i) (P i)) (hZ : AEMeasurable Z P')
    (hdet : (P'.map Z).IsMomentDeterminate)
    (hint : ∀ n, ∀ᶠ i in l, Integrable (fun ω ↦ X i ω ^ (2 * n)) (P i))
    (h : ∀ n, Tendsto (fun i ↦ ∫ ω, X i ω ^ n ∂P i) l (𝓝 (∫ ω, Z ω ^ n ∂P'))) :
    TendstoInDistribution X l Z P P' := by
  refine ⟨hX, hZ, ProbabilityMeasure.tendsto_of_tendsto_integral_pow_of_isMomentDeterminate
    hdet (fun n ↦ (hint n).mono fun i hi ↦ ?_) fun n ↦ ?_⟩
  · simpa only [ProbabilityMeasure.coe_mk] using
      (integrable_map_measure (g := fun x : ℝ ↦ x ^ (2 * n)) (by fun_prop) (hX i)).2 hi
  · simpa only [ProbabilityMeasure.coe_mk, integral_map (hX _) (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ ↦ x ^ n) _), integral_map hZ (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ ↦ x ^ n) _)] using h n

end MeasureTheory
