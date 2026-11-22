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
so the family is tight, and along every finer ultrafilter it converges to some `ν`. A bound on
the moment of order `2k` makes the positive and negative parts of `xⁿ`, for `n < 2k`, uniformly
integrable along the family (`TauCeti.tendsto_lintegral_of_forall_exists_setLIntegral_le`), so
`ν` has the limiting moments, and determinacy gives `ν = μ`. The random versions use the
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

/-- Off `[-S, S]` with `S ≥ 1`, the power `|x|ⁿ` is at most `x²ᵏ / S` when `n < 2k`. -/
private theorem abs_pow_le_pow_div {n k : ℕ} (hn : n < 2 * k) {S x : ℝ} (hS : 1 ≤ S)
    (hx : S ≤ |x|) : |x| ^ n ≤ x ^ (2 * k) / S := by
  rw [le_div_iff₀ (by linarith), ← (even_two_mul k).pow_abs]
  calc |x| ^ n * S ≤ |x| ^ n * |x| := by gcongr
    _ = |x| ^ (n + 1) := (pow_succ _ _).symm
    _ ≤ |x| ^ (2 * k) := pow_le_pow_right₀ (hS.trans hx) (by omega)

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
where `0 < n < 2k`: the tails of these integrals are uniformly small. -/
private theorem tendsto_lintegral_ofReal_of_abs_le_pow {μs : ι → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} (h : Tendsto μs l (𝓝 μ)) {k : ℕ} {C : ℝ}
    (hint : ∀ᶠ i in l, Integrable (fun x : ℝ ↦ x ^ (2 * k)) (μs i : Measure ℝ))
    (hC : ∀ᶠ i in l, ∫ x, x ^ (2 * k) ∂(μs i : Measure ℝ) ≤ C) {n : ℕ} (hn₀ : n ≠ 0)
    (hn : n < 2 * k) {f : ℝ → ℝ} (hf : Continuous f) (hfn : ∀ x, |f x| ≤ |x| ^ n) :
    Tendsto (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i : Measure ℝ)) l
      (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure ℝ))) := by
  simp_rw [← ENNReal.ofNNReal_toNNReal]
  refine tendsto_lintegral_of_forall_exists_setLIntegral_le (continuous_real_toNNReal.comp hf)
    ((tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds l).1 h) fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
  set S : ℝ := max 1 (C / δ)
  have hS : 1 ≤ S := le_max_left _ _
  have hCS : C / S ≤ δ := by
    rw [div_le_iff₀ (by linarith), ← div_le_iff₀' (by exact_mod_cast hδ)]
    exact le_max_right _ _
  -- On the tail `{x | Sⁿ ≤ f x}` we have `S ≤ |x|`, so the integrand is at most `x²ᵏ / S`.
  have htail (x : ℝ) (hx : (S ^ n).toNNReal ≤ (f x).toNNReal) :
      ((f x).toNNReal : ℝ≥0∞) ≤ ENNReal.ofReal (x ^ (2 * k)) * (ENNReal.ofReal S)⁻¹ := by
    have hSx : S ≤ |x| := (pow_le_pow_iff_left₀ (by linarith) (abs_nonneg x) hn₀).1
      ((((Real.toNNReal_le_toNNReal_iff_of_pos (by positivity)).1 hx).trans
        (le_abs_self _)).trans (hfn x))
    rw [ENNReal.ofNNReal_toNNReal, ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (by linarith)]
    exact ENNReal.ofReal_le_ofReal
      ((le_abs_self _).trans ((hfn x).trans (abs_pow_le_pow_div hn hS hSx)))
  refine ⟨(S ^ n).toNNReal, ?_⟩
  filter_upwards [hint, hC] with i hi hiC
  calc ∫⁻ x in {x | (S ^ n).toNNReal ≤ (f x).toNNReal}, ((f x).toNNReal : ℝ≥0∞)
        ∂(μs i : Measure ℝ)
      ≤ ∫⁻ x in {x | (S ^ n).toNNReal ≤ (f x).toNNReal},
          ENNReal.ofReal (x ^ (2 * k)) * (ENNReal.ofReal S)⁻¹ ∂(μs i : Measure ℝ) :=
        setLIntegral_mono' (measurableSet_le measurable_const (by fun_prop)) fun x hx ↦
          htail x hx
    _ ≤ ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) * (ENNReal.ofReal S)⁻¹ ∂(μs i : Measure ℝ) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ x, x ^ (2 * k) ∂(μs i : Measure ℝ)) * (ENNReal.ofReal S)⁻¹ := by
        rw [lintegral_mul_const _ (by fun_prop), ← ofReal_integral_eq_lintegral_ofReal hi
          (ae_of_all _ fun x ↦ (even_two_mul k).pow_nonneg x)]
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal S)⁻¹ := by gcongr
    _ = ENNReal.ofReal (C / S) := by
        rw [← div_eq_mul_inv, ENNReal.ofReal_div_of_pos (by linarith)]
    _ ≤ ε := (ENNReal.ofReal_le_ofReal hCS).trans_eq ENNReal.ofReal_coe_nnreal |>.trans hδε.le

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
  have hμ := integrable_pow_of_integrable_pow_two_mul hn.le
    (integrable_pow_two_mul_of_tendsto h hint hC)
  have hpos := tendsto_lintegral_ofReal_of_abs_le_pow h hint hC hn₀ hn (f := fun x ↦ x ^ n)
    (by fun_prop) fun x ↦ (abs_pow x n).le
  have hneg := tendsto_lintegral_ofReal_of_abs_le_pow h hint hC hn₀ hn (f := fun x ↦ -x ^ n)
    (by fun_prop) fun x ↦ by rw [abs_neg, abs_pow]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hμ]
  refine (((ENNReal.tendsto_toReal hμ.lintegral_lt_top.ne).comp hpos).sub
    ((ENNReal.tendsto_toReal hμ.neg.lintegral_lt_top.ne).comp hneg)).congr' ?_
  filter_upwards [hint] with i hi
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part
    (integrable_pow_of_integrable_pow_two_mul hn.le hi)).symm

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
  -- Every ultrafilter limit point `ν` has the limiting moments, hence is `μ`.
  refine (tendsto_iff_ultrafilter _ _ _).2 fun U hU ↦ ?_
  obtain ⟨ν, -, hν : Tendsto μs U (𝓝 ν)⟩ := hcomp.ultrafilter_le_nhds (U.map μs) <| by
    rw [Ultrafilter.coe_map, le_principal_iff]
    exact mem_map.2 (mem_of_superset (hU hs) fun i hi ↦ subset_closure (mem_image_of_mem μs hi))
  have hνint (n : ℕ) : Integrable (fun x : ℝ ↦ x ^ n) (ν : Measure ℝ) :=
    integrable_pow_of_integrable_pow_two_mul (by omega) (integrable_pow_two_mul_of_tendsto hν
      ((hμs (2 * n)).filter_mono hU) ((hbound n).filter_mono hU))
  have hνmom (n : ℕ) : ∫ x, x ^ n ∂(ν : Measure ℝ) = ∫ x, x ^ n ∂(μ : Measure ℝ) :=
    tendsto_nhds_unique (tendsto_integral_pow_of_tendsto hν
      ((hμs (2 * (n + 1))).filter_mono hU) ((hbound (n + 1)).filter_mono hU) (by omega))
      ((h n).mono_left hU)
  obtain rfl : ν = μ := toMeasure_injective (hμ.eq_of_forall_integral_pow_eq hνint hνmom)
  exact hν

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
