/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import TauCeti.Probability.Moments.Determinacy
import Mathlib.MeasureTheory.Measure.Prokhorov
import TauCeti.MeasureTheory.Function.PolynomialMemLp
import TauCeti.MeasureTheory.Measure.FiniteMeasure.UniformIntegrable
import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
import TauCeti.MeasureTheory.Measure.Tight.Moment

/-!
# Weak convergence from convergence of moments

The *method of moments* on the real line: if probability measures `μᵢ` on `ℝ` have eventually
finite moments of every order and `∫ xⁿ dμᵢ → ∫ xⁿ dμ` for every `n`, where the limit `μ` is
determined by its moments (`MeasureTheory.Measure.IsMomentDeterminate`), then `μᵢ → μ` weakly.
The approximating measures need not be compactly supported. This is how a limit theorem proved
by computing moments, such as the free central limit theorem, the moment convergence of a
random-matrix ensemble or a central limit theorem by cumulants, is turned into weak convergence
of the corresponding laws.

Determinacy cannot be dropped: the log-normal law has the same moments as other probability
measures (`TauCeti.Probability.not_isMomentDeterminate_logNormalMeasure`), so moment convergence
to its moments does not identify a weak limit.

## Main results

* `TauCeti.tendsto_integral_eval_of_tendsto_integral_pow` — convergence of all moments gives
  convergence of the integral of every real polynomial.
* `MeasureTheory.ProbabilityMeasure.integrable_pow_two_mul_of_tendsto` and
  `MeasureTheory.ProbabilityMeasure.tendsto_integral_pow_of_tendsto` — along a weakly convergent
  family with eventually bounded moments of an even order `2k`, the limit has a finite moment of
  order `2k` and the moments of every order `n < 2k` converge.
* `MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_integral_pow_of_isMomentDeterminate` — the
  method of moments for a moment-determinate limit.
* `MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_integral_pow_of_isMomentDeterminate` —
  under eventual bounds on every even moment, weak convergence to a moment-determinate law is
  convergence of all moments.
* `MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_integral_pow` — the special case of a
  compactly supported limit.
* `MeasureTheory.ProbabilityMeasure.exists_forall_integral_pow_mem_of_mem_nhds` — every weak
  neighbourhood of a moment-determinate law contains all laws whose moments up to some order are
  close to its own.
* `MeasureTheory.ProbabilityMeasure.tendsto_measure_notMem_nhds_of_tendsto_measure_integral_pow`
  and `MeasureTheory.ProbabilityMeasure.ae_tendsto_of_ae_tendsto_integral_pow` — the versions for
  random probability measures, in probability on varying sample spaces and almost surely.
* `MeasureTheory.tendstoInDistribution_of_tendsto_integral_pow` — the version for real random
  variables and convergence in distribution.

## Implementation notes

The proof runs through Prokhorov's theorem. Convergent second moments are eventually bounded,
so the family is tight, and every cluster point `ν` is its limit along some finer ultrafilter. A
bound on the moment of order `2k` makes the integrals of the positive and negative parts of `xⁿ`,
for `n < 2k`, converge along the family (`TauCeti.tendsto_lintegral_of_rpow_bound`), so `ν` has
the limiting moments, and determinacy gives `ν = μ`. The random versions use the
neighbourhood form and a finite union bound.

## References

* P. Billingsley, *Probability and Measure*, 3rd ed., Wiley (1995), Theorems 30.1 and 30.2.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), Theorem 2.4.4 and its proof.
-/

public section

open MeasureTheory Filter Polynomial Set Finset
open scoped Topology ENNReal

namespace TauCeti

variable {ι : Type*} {l : Filter ι}

/-- If every monomial is eventually integrable against `μᵢ`, then eventually all the monomials up
to the degree of a given polynomial are. -/
private theorem eventually_forall_le_natDegree_integrable {μs : ι → Measure ℝ}
    (hμs : ∀ n, ∀ᶠ i in l, Integrable (fun x : ℝ => x ^ n) (μs i)) (p : ℝ[X]) :
    ∀ᶠ i in l, ∀ k ≤ p.natDegree, Integrable (fun x : ℝ => x ^ k) (μs i) :=
  (eventually_all_finite (Set.finite_Iic p.natDegree)).2 fun n _ => hμs n

/-- If every moment `∫ xⁿ dμᵢ` converges to `∫ xⁿ dμ`, then so does the integral of every real
polynomial. The moments must be genuine: each monomial is assumed integrable against `μ` and,
eventually, against `μᵢ`. -/
theorem tendsto_integral_eval_of_tendsto_integral_pow {μs : ι → Measure ℝ} {μ : Measure ℝ}
    (hμs : ∀ n, ∀ᶠ i in l, Integrable (fun x : ℝ => x ^ n) (μs i))
    (hμ : ∀ n, Integrable (fun x : ℝ => x ^ n) μ)
    (h : ∀ n, Tendsto (fun i => ∫ x, x ^ n ∂μs i) l (𝓝 (∫ x, x ^ n ∂μ))) (p : ℝ[X]) :
    Tendsto (fun i => ∫ x, p.eval x ∂μs i) l (𝓝 (∫ x, p.eval x ∂μ)) := by
  rw [integral_eval_eq_sum_range fun n _ => hμ n]
  refine (tendsto_finsetSum _ fun n _ => (h n).const_mul (p.coeff n)).congr' ?_
  filter_upwards [eventually_forall_le_natDegree_integrable hμs p] with i hi
  exact (integral_eval_eq_sum_range hi).symm

end TauCeti

namespace MeasureTheory.ProbabilityMeasure

open TauCeti

variable {ι : Type*} {l : Filter ι}

/-! ### Moments along weakly convergent families -/

/-- The bound `∫ x²ᵏ dμᵢ ≤ C` passes to a weak limit, as a bound on its lower integral. -/
private theorem lintegral_ofReal_pow_two_mul_le_of_tendsto [l.NeBot]
    {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} (h : Tendsto μs l (𝓝 μ))
    {k : ℕ} {C : ℝ}
    (hint : ∀ᶠ i in l, Integrable (fun x : ℝ ↦ x ^ (2 * k)) (μs i : Measure ℝ))
    (hC : ∀ᶠ i in l, ∫ x, x ^ (2 * k) ∂(μs i : Measure ℝ) ≤ C) :
    ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(μ : Measure ℝ) ≤ ENNReal.ofReal C := by
  have hlsc : LowerSemicontinuous fun x : ℝ ↦ ENNReal.ofReal (x ^ (2 * k)) :=
    (ENNReal.continuous_ofReal.comp (continuous_pow _)).lowerSemicontinuous
  refine (le_liminf_lintegral_of_tendsto_probabilityMeasure hlsc h).trans
    (liminf_le_of_frequently_le' ((hint.and hC).mono fun i hi ↦ ?_).frequently)
  rw [← ofReal_integral_eq_lintegral_ofReal hi.1
    (ae_of_all _ fun x ↦ (even_two_mul k).pow_nonneg x)]
  exact ENNReal.ofReal_le_ofReal hi.2

/-- **Weak limits inherit bounded even moments.** If `μᵢ → μ` weakly and the moments of order
`2k` are eventually finite and at most `C`, then the moment of order `2k` of `μ` is finite. -/
theorem integrable_pow_two_mul_of_tendsto [l.NeBot] {μs : ι → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} (h : Tendsto μs l (𝓝 μ)) {k : ℕ} {C : ℝ}
    (hint : ∀ᶠ i in l, Integrable (fun x : ℝ ↦ x ^ (2 * k)) (μs i : Measure ℝ))
    (hC : ∀ᶠ i in l, ∫ x, x ^ (2 * k) ∂(μs i : Measure ℝ) ≤ C) :
    Integrable (fun x : ℝ ↦ x ^ (2 * k)) (μ : Measure ℝ) := by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x ↦ (even_two_mul k).pow_nonneg x)]
  exact (lintegral_ofReal_pow_two_mul_le_of_tendsto h hint hC).trans_lt ENNReal.ofReal_lt_top

/-- Along a weakly convergent family whose moments of order `2k` are eventually finite and at
most `C`, the integrals of `ofReal ∘ f` converge for every continuous `f` with `|f x| ≤ |x|ⁿ`,
where `0 < n < 2k`: the power `2k / n > 1` of the integrand is at most `x²ᵏ`, so
`TauCeti.tendsto_lintegral_of_rpow_bound` applies. -/
private theorem tendsto_lintegral_ofReal_of_abs_le_pow {μs : ι → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} (h : Tendsto μs l (𝓝 μ)) {k : ℕ} {C : ℝ}
    (hint : ∀ᶠ i in l, Integrable (fun x : ℝ ↦ x ^ (2 * k)) (μs i : Measure ℝ))
    (hC : ∀ᶠ i in l, ∫ x, x ^ (2 * k) ∂(μs i : Measure ℝ) ≤ C) {n : ℕ} (hn₀ : n ≠ 0)
    (hn : n < 2 * k) {f : ℝ → ℝ} (hf : Continuous f) (hfn : ∀ x, |f x| ≤ |x| ^ n) :
    Tendsto (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i : Measure ℝ)) l
      (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure ℝ))) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn₀)
  have hp : (1 : ℝ) < ((2 * k : ℕ) : ℝ) / n := by
    rw [one_lt_div hn']
    exact_mod_cast hn
  -- The power `2k / n` of the integrand is at most `x²ᵏ`.
  have hpow (x : ℝ) : ENNReal.ofReal (f x) ^ (((2 * k : ℕ) : ℝ) / n) ≤
      ENNReal.ofReal (x ^ (2 * k)) := by
    calc ENNReal.ofReal (f x) ^ (((2 * k : ℕ) : ℝ) / n)
        ≤ ENNReal.ofReal (|x| ^ n) ^ (((2 * k : ℕ) : ℝ) / n) :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hfn x)))
            (by positivity)
      _ = ENNReal.ofReal (x ^ (2 * k)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul (abs_nonneg x), mul_div_cancel₀ _ hn'.ne', Real.rpow_natCast,
            (even_two_mul k).pow_abs]
  simp_rw [← ENNReal.ofNNReal_toNNReal]
  refine tendsto_lintegral_of_rpow_bound (continuous_real_toNNReal.comp hf)
    ((tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds l).1 h) hp (C := C.toNNReal) ?_
  filter_upwards [hint, hC] with i hi hiC
  calc ∫⁻ x, ((f x).toNNReal : ℝ≥0∞) ^ (((2 * k : ℕ) : ℝ) / n) ∂(μs i : Measure ℝ)
      ≤ ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(μs i : Measure ℝ) :=
        lintegral_mono fun x ↦ by simpa only [ENNReal.ofNNReal_toNNReal] using hpow x
    _ = ENNReal.ofReal (∫ x, x ^ (2 * k) ∂(μs i : Measure ℝ)) :=
        (ofReal_integral_eq_lintegral_ofReal hi
          (ae_of_all _ fun x ↦ (even_two_mul k).pow_nonneg x)).symm
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hiC

/-- **Moments along weak convergence.** If `μᵢ → μ` weakly and the moments of an even order
`2k` are eventually finite and bounded, then every moment of lower order converges:
`∫ xⁿ dμᵢ → ∫ xⁿ dμ` for `n < 2k`. -/
theorem tendsto_integral_pow_of_tendsto {μs : ι → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} (h : Tendsto μs l (𝓝 μ)) {k : ℕ} {C : ℝ}
    (hint : ∀ᶠ i in l, Integrable (fun x : ℝ ↦ x ^ (2 * k)) (μs i : Measure ℝ))
    (hC : ∀ᶠ i in l, ∫ x, x ^ (2 * k) ∂(μs i : Measure ℝ) ≤ C) {n : ℕ} (hn : n < 2 * k) :
    Tendsto (fun i ↦ ∫ x, x ^ n ∂(μs i : Measure ℝ)) l (𝓝 (∫ x, x ^ n ∂(μ : Measure ℝ))) := by
  rcases l.eq_or_neBot with rfl | _
  · exact tendsto_bot
  rcases eq_or_ne n 0 with rfl | hn₀
  · simp
  -- A finite moment of order `2k` makes the moment of order `n` finite.
  have hlow {ρ : Measure ℝ} [IsFiniteMeasure ρ]
      (hρ : Integrable (fun x : ℝ ↦ x ^ (2 * k)) ρ) : Integrable (fun x : ℝ ↦ x ^ n) ρ :=
    (integrable_norm_iff (by fun_prop)).1 <| by
      simpa only [norm_pow, id] using integrable_norm_pow_of_le (f := id)
        aestronglyMeasurable_id hn.le
        (by simpa only [id, Real.norm_eq_abs, (even_two_mul k).pow_abs] using hρ)
  have hμ := hlow (integrable_pow_two_mul_of_tendsto h hint hC)
  have hpos := tendsto_lintegral_ofReal_of_abs_le_pow h hint hC hn₀ hn (f := fun x ↦ x ^ n)
    (by fun_prop) fun x ↦ (abs_pow x n).le
  have hneg := tendsto_lintegral_ofReal_of_abs_le_pow h hint hC hn₀ hn (f := fun x ↦ -x ^ n)
    (by fun_prop) fun x ↦ by rw [abs_neg, abs_pow]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hμ]
  refine (((ENNReal.tendsto_toReal hμ.lintegral_lt_top.ne).comp hpos).sub
    ((ENNReal.tendsto_toReal hμ.neg.lintegral_lt_top.ne).comp hneg)).congr' ?_
  filter_upwards [hint] with i hi
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hlow hi)).symm

/-! ### The method of moments -/

/-- **The method of moments for a moment-determinate limit.** Let `μᵢ` and `μ` be probability
measures on `ℝ` such that `μ` is determined by its moments, every moment of `μᵢ` is eventually
finite, and `∫ xⁿ dμᵢ → ∫ xⁿ dμ` for every `n`. Then `μᵢ → μ` weakly. -/
theorem tendsto_of_tendsto_integral_pow_of_isMomentDeterminate {μs : ι → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ).IsMomentDeterminate)
    (hμs : ∀ n, ∀ᶠ i in l, Integrable (fun x : ℝ ↦ x ^ n) (μs i : Measure ℝ))
    (h : ∀ n, Tendsto (fun i ↦ ∫ x, x ^ n ∂(μs i : Measure ℝ)) l
      (𝓝 (∫ x, x ^ n ∂(μ : Measure ℝ)))) :
    Tendsto μs l (𝓝 μ) := by
  -- Each even moment is eventually at most its limit plus one.
  have hbound (n : ℕ) : ∀ᶠ i in l, ∫ x, x ^ (2 * n) ∂(μs i : Measure ℝ) ≤
      ∫ x, x ^ (2 * n) ∂(μ : Measure ℝ) + 1 :=
    (h (2 * n)).eventually (eventually_le_nhds (lt_add_one _))
  -- On the eventual set where the second moment is finite and bounded, the family is tight.
  set s := {i | Integrable (fun x : ℝ ↦ x ^ (2 * 1)) (μs i : Measure ℝ) ∧
    ∫ x, x ^ (2 * 1) ∂(μs i : Measure ℝ) ≤ ∫ x, x ^ (2 * 1) ∂(μ : Measure ℝ) + 1}
  have hs : s ∈ l := (hμs (2 * 1)).and (hbound 1)
  have hcomp : IsCompact (closure (μs '' s)) := by
    refine isCompact_closure_of_isTightMeasureSet (isTightMeasureSet_of_lintegral_enorm_rpow_le
      two_pos (C := ENNReal.ofReal (∫ x, x ^ (2 * 1) ∂(μ : Measure ℝ) + 1))
      ENNReal.ofReal_ne_top ?_)
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    calc ∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂(μs i : Measure ℝ)
        = ∫⁻ x, ENNReal.ofReal (x ^ (2 * 1)) ∂(μs i : Measure ℝ) := by
          refine lintegral_congr fun x ↦ ?_
          rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg x) zero_le_two,
            Real.rpow_two, Real.norm_eq_abs, sq_abs, mul_one]
      _ = ENNReal.ofReal (∫ x, x ^ (2 * 1) ∂(μs i : Measure ℝ)) :=
          (ofReal_integral_eq_lintegral_ofReal hi.1
            (ae_of_all _ fun x ↦ (even_two_mul 1).pow_nonneg x)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hi.2
  -- Every cluster point `ν` is a limit along some ultrafilter `U ≤ l`, so it has the limiting
  -- moments, hence is `μ`.
  refine hcomp.tendsto_nhds_of_unique_mapClusterPt
    (mem_of_superset hs fun i hi ↦ subset_closure (mem_image_of_mem μs hi)) fun ν _ hν ↦ ?_
  obtain ⟨U, hU, hνU⟩ := mapClusterPt_iff_ultrafilter.mp hν
  have hνint (n : ℕ) : Integrable (fun x : ℝ ↦ x ^ n) (ν : Measure ℝ) := by
    have h2n := integrable_pow_two_mul_of_tendsto hνU ((hμs (2 * n)).filter_mono hU)
      ((hbound n).filter_mono hU)
    refine (integrable_norm_iff (by fun_prop)).1 ?_
    simpa only [norm_pow, id] using integrable_norm_pow_of_le (f := id) aestronglyMeasurable_id
      (by omega : n ≤ 2 * n)
      (by simpa only [id, Real.norm_eq_abs, (even_two_mul n).pow_abs] using h2n)
  have hνmom (n : ℕ) : ∫ x, x ^ n ∂(ν : Measure ℝ) = ∫ x, x ^ n ∂(μ : Measure ℝ) :=
    tendsto_nhds_unique (tendsto_integral_pow_of_tendsto hνU
      ((hμs (2 * (n + 1))).filter_mono hU) ((hbound (n + 1)).filter_mono hU) (by omega))
      ((h n).mono_left hU)
  exact toMeasure_injective (hμ.eq_of_forall_integral_pow_eq hνint hνmom)

/-- **Weak convergence and convergence of moments.** If every moment of `μᵢ` is eventually
finite and the moments of each even order are eventually bounded, then `μᵢ` converges weakly to a
moment-determinate law `μ` if and only if `∫ xⁿ dμᵢ → ∫ xⁿ dμ` for every `n`. -/
theorem tendsto_iff_tendsto_integral_pow_of_isMomentDeterminate {μs : ι → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ).IsMomentDeterminate)
    (hμs : ∀ n, ∀ᶠ i in l, Integrable (fun x : ℝ ↦ x ^ n) (μs i : Measure ℝ))
    (hbdd : ∀ n, ∃ C, ∀ᶠ i in l, ∫ x, x ^ (2 * n) ∂(μs i : Measure ℝ) ≤ C) :
    Tendsto μs l (𝓝 μ) ↔ ∀ n, Tendsto (fun i ↦ ∫ x, x ^ n ∂(μs i : Measure ℝ)) l
      (𝓝 (∫ x, x ^ n ∂(μ : Measure ℝ))) :=
  ⟨fun h n ↦ (hbdd (n + 1)).elim fun _ hC ↦
      tendsto_integral_pow_of_tendsto h (hμs (2 * (n + 1))) hC (by omega),
    tendsto_of_tendsto_integral_pow_of_isMomentDeterminate hμ hμs⟩

/-- **The method of moments for a compactly supported limit.** Let `μᵢ` and `μ` be probability
measures on `ℝ` such that `μ` is concentrated on a compact set, every moment of `μᵢ` is
eventually finite, and `∫ xⁿ dμᵢ → ∫ xⁿ dμ` for every `n`. Then `μᵢ → μ` weakly. -/
theorem tendsto_of_tendsto_integral_pow {μs : ι → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} {K : Set ℝ} (hK : IsCompact K) (hμK : (μ : Measure ℝ) Kᶜ = 0)
    (hμs : ∀ n, ∀ᶠ i in l, Integrable (fun x : ℝ ↦ x ^ n) (μs i : Measure ℝ))
    (h : ∀ n, Tendsto (fun i ↦ ∫ x, x ^ n ∂(μs i : Measure ℝ)) l
      (𝓝 (∫ x, x ^ n ∂(μ : Measure ℝ)))) :
    Tendsto μs l (𝓝 μ) :=
  tendsto_of_tendsto_integral_pow_of_isMomentDeterminate (.of_isCompact hK hμK) hμs h

/-- **Weak neighbourhoods of a moment-determinate law.** Every weak neighbourhood `U` of a
moment-determinate probability measure `μ` on `ℝ` contains each probability measure whose moments
up to some order `N` are finite and within some `δ > 0` of those of `μ`. -/
theorem exists_forall_integral_pow_mem_of_mem_nhds {μ : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ).IsMomentDeterminate) {U : Set (ProbabilityMeasure ℝ)}
    (hU : U ∈ 𝓝 μ) :
    ∃ N : ℕ, ∃ δ > 0, ∀ ν : ProbabilityMeasure ℝ, (∀ n ≤ N,
      Integrable (fun x : ℝ ↦ x ^ n) (ν : Measure ℝ) ∧
        |∫ x, x ^ n ∂(ν : Measure ℝ) - ∫ x, x ^ n ∂(μ : Measure ℝ)| < δ) → ν ∈ U := by
  -- Otherwise measures outside `U` with ever closer moments converge to `μ`.
  by_contra! hne
  choose ν hν hνU using fun N : ℕ ↦ hne N (1 / (N + 1)) Nat.one_div_pos_of_nat
  have hlim : Tendsto ν atTop (𝓝 μ) := by
    refine tendsto_of_tendsto_integral_pow_of_isMomentDeterminate hμ
      (fun n ↦ (eventually_ge_atTop n).mono fun N hN ↦ (hν N n hN).1) fun n ↦ ?_
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _)
      ((eventually_ge_atTop n).mono fun N hN ↦ (hν N n hN).2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  obtain ⟨N, hN⟩ := (hlim.eventually hU).exists
  exact hνU N hN

/-! ### Random probability measures -/

/-- **The method of moments in probability.** Let `μᵢ ω` be random probability measures on `ℝ`,
defined on sample spaces `(Ωᵢ, Pᵢ)` that may vary with `i`. If each moment of `μᵢ` is finite with
probability tending to one and converges in probability to the corresponding moment of a
moment-determinate law `μ`, then `μᵢ → μ` weakly in probability: `Pᵢ (μᵢ ∉ U) → 0` for every weak
neighbourhood `U` of `μ`. No measurability of the random measures is needed. By
`MeasureTheory.ProbabilityMeasure.tendsto_measure_notMem_nhds_iff_integral`, this is convergence
in probability of every bounded continuous test integral `∫ f dμᵢ` to `∫ f dμ`. -/
theorem tendsto_measure_notMem_nhds_of_tendsto_measure_integral_pow
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (P : (i : ι) → Measure (Ω i)) (μs : (i : ι) → Ω i → ProbabilityMeasure ℝ)
    (l : Filter ι) {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ).IsMomentDeterminate)
    (hint : ∀ n, Tendsto (fun i ↦ P i {ω | ¬Integrable (fun x : ℝ ↦ x ^ n)
      (μs i ω : Measure ℝ)}) l (𝓝 0))
    (h : ∀ n, ∀ ε : ℝ, 0 < ε → Tendsto (fun i ↦ P i {ω |
      ε ≤ |∫ x, x ^ n ∂(μs i ω : Measure ℝ) - ∫ x, x ^ n ∂(μ : Measure ℝ)|}) l (𝓝 0))
    {U : Set (ProbabilityMeasure ℝ)} (hU : U ∈ 𝓝 μ) :
    Tendsto (fun i ↦ P i {ω | μs i ω ∉ U}) l (𝓝 0) := by
  obtain ⟨N, δ, hδ, hN⟩ := exists_forall_integral_pow_mem_of_mem_nhds hμ hU
  -- Outside `U`, some moment of order at most `N` is infinite or `δ`-far from its limit.
  have hsub (i : ι) : {ω | μs i ω ∉ U} ⊆ ⋃ n ∈ range (N + 1),
      ({ω | ¬Integrable (fun x : ℝ ↦ x ^ n) (μs i ω : Measure ℝ)} ∪ {ω |
        δ ≤ |∫ x, x ^ n ∂(μs i ω : Measure ℝ) - ∫ x, x ^ n ∂(μ : Measure ℝ)|}) := by
    intro ω hω
    by_contra hcon
    simp only [mem_iUnion, mem_union, mem_ofPred_eq, Finset.mem_range, not_exists, not_or,
      not_le, not_not] at hcon
    exact hω (hN _ fun n hn ↦ hcon n (by omega))
  have hsum : Tendsto (fun i ↦ ∑ n ∈ range (N + 1),
      (P i {ω | ¬Integrable (fun x : ℝ ↦ x ^ n) (μs i ω : Measure ℝ)} + P i {ω |
        δ ≤ |∫ x, x ^ n ∂(μs i ω : Measure ℝ) - ∫ x, x ^ n ∂(μ : Measure ℝ)|})) l (𝓝 0) := by
    simpa using tendsto_finsetSum (range (N + 1)) fun n _ ↦ (hint n).add (h n δ hδ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le)
    fun i ↦ ?_
  exact (measure_mono (hsub i)).trans ((measure_biUnion_finset_le _ _).trans
    (sum_le_sum fun n _ ↦ measure_union_le _ _))

/-- **The method of moments almost surely.** If almost surely every moment of the random
probability measures `μᵢ ω` is eventually finite and converges to the corresponding moment of a
moment-determinate law `μ`, then almost surely `μᵢ ω → μ` weakly. The exceptional null sets may
depend on the order of the moment. -/
theorem ae_tendsto_of_ae_tendsto_integral_pow {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {μs : ι → Ω → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ).IsMomentDeterminate)
    (hμs : ∀ n, ∀ᵐ ω ∂P, ∀ᶠ i in l, Integrable (fun x : ℝ ↦ x ^ n) (μs i ω : Measure ℝ))
    (h : ∀ n, ∀ᵐ ω ∂P, Tendsto (fun i ↦ ∫ x, x ^ n ∂(μs i ω : Measure ℝ)) l
      (𝓝 (∫ x, x ^ n ∂(μ : Measure ℝ)))) :
    ∀ᵐ ω ∂P, Tendsto (fun i ↦ μs i ω) l (𝓝 μ) := by
  filter_upwards [ae_all_iff.2 hμs, ae_all_iff.2 h] with ω hω₁ hω₂
  exact tendsto_of_tendsto_integral_pow_of_isMomentDeterminate hμ hω₁ hω₂

end MeasureTheory.ProbabilityMeasure

namespace MeasureTheory

/-- **The method of moments for random variables.** Real random variables `Xᵢ` whose moments are
eventually finite and converge to those of a random variable `Z`, whose law is determined by its
moments, converge to `Z` in distribution. -/
theorem tendstoInDistribution_of_tendsto_integral_pow {ι : Type*} {l : Filter ι}
    {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)} {P : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (P i)] {Ω' : Type*} {m' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X : (i : ι) → Ω i → ℝ} {Z : Ω' → ℝ}
    (hX : ∀ i, AEMeasurable (X i) (P i)) (hZ : AEMeasurable Z P')
    (hdet : (P'.map Z).IsMomentDeterminate)
    (hint : ∀ n, ∀ᶠ i in l, Integrable (fun ω ↦ X i ω ^ n) (P i))
    (h : ∀ n, Tendsto (fun i ↦ ∫ ω, X i ω ^ n ∂P i) l (𝓝 (∫ ω, Z ω ^ n ∂P'))) :
    TendstoInDistribution X l Z P P' := by
  refine ⟨hX, hZ, ProbabilityMeasure.tendsto_of_tendsto_integral_pow_of_isMomentDeterminate
    hdet (fun n ↦ (hint n).mono fun i hi ↦ ?_) fun n ↦ ?_⟩
  · exact (integrable_map_measure (by fun_prop) (hX i)).2 hi
  · simpa only [ProbabilityMeasure.coe_mk, integral_map (hX _) (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ ↦ x ^ n) _), integral_map hZ (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ ↦ x ^ n) _)] using h n

end MeasureTheory
