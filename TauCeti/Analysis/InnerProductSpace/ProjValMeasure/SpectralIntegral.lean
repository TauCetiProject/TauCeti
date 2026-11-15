/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.DominatedConvergence
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.MatrixElement
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore
import Mathlib.Analysis.MeanInequalities

/-!
# Unbounded spectral integrals against a projection-valued measure

Let `P : ProjValMeasure X H` be a normalized projection-valued measure on an arbitrary measurable
space `X` acting on a complex Hilbert space `H`. For bounded measurable symbols, `P.integral` gives
a unital star algebra homomorphism `BoundedBorelFunction X →⋆ₐ[ℂ] (H →L[ℂ] H)`. When the measurable
symbol `f : X → ℂ` is unbounded, its operator integral cannot in general act on all of `H`; instead
it is realized as a densely defined, closed partial linear operator
`P.spectralIntegral f hf : H →ₗ.[ℂ] H` on the second-moment domain
`{x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}`.

Two measure-theoretic inputs drive the construction without any topological or separability
assumptions on `X` or `H`:

* **Cauchy-Schwarz for polarized variation measures**
  (`lintegral_variation_polarizedComplexMeasure_le`,
  `integrable_polarizedComplexMeasure_of_memLp`): for every `u : X → ℝ≥0∞`,
  `∫⁻ t, u t ∂|μ_(ψ,ξ)| ≤ ‖ψ‖ₑ * (∫⁻ t, u t ^ 2 ∂(P.diag ξ)) ^ (2⁻¹ : ℝ)`. Consequently, whenever
  `f` belongs to `L²(P.diag x)`, `f` is integrable against `P.polarizedComplexMeasure y x` for
  every `y : H`.
* **Norm-window truncations**: the bounded symbols `f_n = {t | ‖f t‖ ≤ n}.indicator f` have
  bounded spectral integrals `P.integral f_n` that converge strongly on the second-moment domain.
  Passing to the limit identifies the matrix elements `⟪y, P.spectralIntegral f hf x⟫_ℂ` with the
  polarized vector-measure integrals `∫ᵛ t, f t ∂μ_(y, x)` and the squared norm
  `‖P.spectralIntegral f hf x‖ ^ 2` with the second moment `∫ t, ‖f t‖ ^ 2 ∂(P.diag x)`.

Testing the Hilbert adjoint against vectors in the ranges of the norm-window projections bounds the
truncated second moments of `star f` uniformly and shows via monotone convergence that
`(P.spectralIntegral f hf)†` equals the spectral integral of `star f`. Closedness, normality on the
common domain, the truncation graph core, and the characterization of self-adjointness by `P.ae`
real-valuedness follow immediately.

## Main definitions

* `TauCeti.ProjValMeasure.spectralIntegral`: the unbounded spectral integral
  `P.spectralIntegral f hf : H →ₗ.[ℂ] H` of a measurable symbol `f : X → ℂ` on its second-moment
  domain.

## Main statements

* `TauCeti.ProjValMeasure.lintegral_variation_polarizedComplexMeasure_le`: Lebesgue-integral
  Cauchy-Schwarz inequality bounding `|μ_(ψ,ξ)|` by `‖ψ‖ₑ` times the `L²(P.diag ξ)` seminorm.
* `TauCeti.ProjValMeasure.integrable_polarizedComplexMeasure_of_memLp`: every function in
  `MemLp f 2 (P.diag ξ)` is integrable against `P.polarizedComplexMeasure ψ ξ` for all `ψ : H`.
* `TauCeti.ProjValMeasure.inner_spectralIntegral` and
  `TauCeti.ProjValMeasure.eq_spectralIntegral_iff`: matrix-element formula and universal
  characterization of `P.spectralIntegral f hf` by its second-moment domain and polarized integrals.
* `TauCeti.ProjValMeasure.norm_sq_spectralIntegral_apply` and
  `TauCeti.ProjValMeasure.diag_spectralIntegral_apply`: second-moment norm identity and diagonal
  spectral measure of `P.spectralIntegral f hf x`.
* `TauCeti.ProjValMeasure.spectralIntegral_boundedBorelFunction` and
  `TauCeti.ProjValMeasure.spectralIntegral_eq_spectralIntegral_iff`: compatibility with bounded
  spectral integration and `P.ae`-uniqueness of symbols.
* `TauCeti.ProjValMeasure.smul_le_spectralIntegral_smul`,
  `TauCeti.ProjValMeasure.spectralIntegral_smul_of_ne_zero`,
  `TauCeti.ProjValMeasure.add_le_spectralIntegral_add`,
  `TauCeti.ProjValMeasure.spectralIntegral_add_boundedBorelFunction_left`,
  `TauCeti.ProjValMeasure.spectralIntegral_integral_eq_integral_spectralIntegral`, and
  `TauCeti.ProjValMeasure.mem_spectralIntegral_domain_spectralIntegral_apply_iff`: algebraic and
  multiplicative calculus rules (Teschl (3.26)-(3.27)).
* `TauCeti.ProjValMeasure.adjoint_spectralIntegral`,
  `TauCeti.ProjValMeasure.isClosed_spectralIntegral`,
  `TauCeti.ProjValMeasure.hasCore_iSup_proj_range_spectralIntegral`,
  `TauCeti.ProjValMeasure.isSelfAdjoint_spectralIntegral_iff`, and
  `TauCeti.ProjValMeasure.existsUnique_spectralIntegral`: Hilbert adjoint, closedness, truncation
  graph core, self-adjointness criterion, and existence-and-uniqueness package.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, Graduate Studies in Mathematics 99,
  American Mathematical Society, 2009, Section 3.1, Theorem 3.2 and (3.25)-(3.29).
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Graduate Texts in
  Mathematics 265, Springer, 2012, Section 4.3, Theorem 4.13 and Proposition 4.17.
* W. Rudin, *Functional Analysis*, 2nd ed., McGraw-Hill, 1991, Theorem 13.24.
-/

public section

noncomputable section

open MeasureTheory Filter Topology ContinuousLinearMap
open scoped InnerProductSpace ENNReal LinearPMap

namespace TauCeti.ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Second-moment integrability against polarized measures -/

/-- Cauchy-Schwarz inequality for the variation of a polarized spectral measure: for every
nonnegative extended-real function `u : X → ℝ≥0∞` (with no measurability assumption), the lower
Lebesgue integral against `|μ_(ψ,ξ)|` is bounded by `‖ψ‖ₑ` times the square root of the second
moment of `u` against `P.diag ξ`. -/
theorem lintegral_variation_polarizedComplexMeasure_le (P : ProjValMeasure X H) (ψ ξ : H)
    (u : X → ℝ≥0∞) :
    ∫⁻ t, u t ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
      ‖ψ‖ₑ * (∫⁻ t, u t ^ 2 ∂(P.diag ξ)) ^ (2⁻¹ : ℝ) := by
  rw [lintegral_def]
  refine iSup₂_le fun s hs => ?_
  have hstep : s.lintegral (P.polarizedComplexMeasure ψ ξ).variation ≤
      ∑ c ∈ s.range, ‖P.proj (s ⁻¹' {c}) (s.measurableSet_fiber c) ψ‖ₑ *
        (c * ‖P.proj (s ⁻¹' {c}) (s.measurableSet_fiber c) ξ‖ₑ) := by
    rw [SimpleFunc.lintegral]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [mul_left_comm]
    gcongr
    exact P.polarizedComplexMeasure_variation_apply_le ψ ξ (s.measurableSet_fiber c)
  have hholder := ENNReal.inner_le_Lp_mul_Lq (s := s.range)
    (fun c => ‖P.proj (s ⁻¹' {c}) (s.measurableSet_fiber c) ψ‖ₑ)
    (fun c => c * ‖P.proj (s ⁻¹' {c}) (s.measurableSet_fiber c) ξ‖ₑ) Real.HolderConjugate.two_two
  have hψ : (∑ c ∈ s.range,
      ‖P.proj (s ⁻¹' {c}) (s.measurableSet_fiber c) ψ‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = ‖ψ‖ₑ := by
    simp_rw [ENNReal.rpow_two, P.enorm_sq_proj_apply]
    have hsum : ∑ c ∈ s.range, P.diag ψ (s ⁻¹' {c}) = ‖ψ‖ₑ ^ 2 := by
      calc
        ∑ c ∈ s.range, P.diag ψ (s ⁻¹' {c}) =
            ∑ c ∈ s.range, (1 : ℝ≥0∞) * P.diag ψ (s ⁻¹' {c}) := by simp
        _ = (s.map fun _ => (1 : ℝ≥0∞)).lintegral (P.diag ψ) :=
          (SimpleFunc.map_lintegral (fun _ => (1 : ℝ≥0∞)) s).symm
        _ = ∫⁻ _, (1 : ℝ≥0∞) ∂(P.diag ψ) := (SimpleFunc.lintegral_eq_lintegral _ _).symm
        _ = ‖ψ‖ₑ ^ 2 := by rw [lintegral_one, P.diag_univ]
    rw [hsum, ← ENNReal.rpow_two, ← ENNReal.rpow_mul, mul_one_div_cancel two_ne_zero,
      ENNReal.rpow_one]
  have hξ : ∑ c ∈ s.range,
      (c * ‖P.proj (s ⁻¹' {c}) (s.measurableSet_fiber c) ξ‖ₑ) ^ (2 : ℝ) ≤
        ∫⁻ t, u t ^ 2 ∂(P.diag ξ) := by
    simp_rw [ENNReal.rpow_two, mul_pow, P.enorm_sq_proj_apply]
    rw [← SimpleFunc.map_lintegral (fun c => c ^ 2) s, ← SimpleFunc.lintegral_eq_lintegral]
    exact lintegral_mono fun t => pow_le_pow_left' (hs t) 2
  refine hstep.trans (hholder.trans ?_)
  rw [hψ, one_div]
  gcongr

/-- Any Banach-space-valued function in `L²(P.diag ξ)` is integrable with respect to the polarized
complex measure `P.polarizedComplexMeasure ψ ξ` for every `ψ : H`. -/
theorem integrable_polarizedComplexMeasure_of_memLp {E : Type*} [NormedAddCommGroup E]
    (P : ProjValMeasure X H) {f : X → E} {ξ : H} (hf : MemLp f 2 (P.diag ξ)) (ψ : H) :
    (P.polarizedComplexMeasure ψ ξ).Integrable f := by
  refine ⟨hf.aestronglyMeasurable.mono_ac
    (P.variation_polarizedComplexMeasure_absolutelyContinuous_right ψ ξ), ?_⟩
  rw [hasFiniteIntegral_iff_eNorm]
  have hlt : ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag ξ) < ∞ := by
    simpa [ENNReal.rpow_two] using
      lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
        hf.eLpNorm_lt_top
  exact (P.lintegral_variation_polarizedComplexMeasure_le ψ ξ (fun t => ‖f t‖ₑ)).trans_lt
    (ENNReal.mul_lt_top eNorm_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) hlt.ne))

/-- Norm-integral Cauchy-Schwarz inequality for polarized spectral measures: for `f` in
`L²(P.diag ξ)`, `∫ t, ‖f t‖ ∂|μ_(ψ,ξ)| ≤ ‖ψ‖ * √(∫ t, ‖f t‖ ^ 2 ∂(P.diag ξ))`. -/
theorem integral_norm_variation_polarizedComplexMeasure_le {E : Type*} [NormedAddCommGroup E]
    (P : ProjValMeasure X H) {f : X → E} {ξ : H} (hf : MemLp f 2 (P.diag ξ)) (ψ : H) :
    ∫ t, ‖f t‖ ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
      ‖ψ‖ * Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂(P.diag ξ)) := by
  have hint := P.integrable_polarizedComplexMeasure_of_memLp hf ψ
  have hsq : Integrable (fun t => ‖f t‖ ^ 2) (P.diag ξ) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hlt : ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag ξ) < ∞ := by
    simpa [ENNReal.rpow_two] using
      lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
        hf.eLpNorm_lt_top
  have hbound := ENNReal.toReal_mono
    (ENNReal.mul_lt_top eNorm_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) hlt.ne)).ne
    (P.lintegral_variation_polarizedComplexMeasure_le ψ ξ (fun t => ‖f t‖ₑ))
  have hcongr : (∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(P.diag ξ)) = ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag ξ) := by
    congr with t
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [integral_norm_eq_lintegral_eNorm hint.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
      hsq.aestronglyMeasurable, hcongr, Real.sqrt_eq_rpow, one_div]
  rwa [ENNReal.toReal_mul, toReal_eNorm, ← ENNReal.toReal_rpow] at hbound

/-! ### Second-moment domain, norm-window cutoffs, and definition of `spectralIntegral` -/

/-- The second-moment subspace `{x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}` of a symbol `f`. -/
private def spectralIntegralDomain (P : ProjValMeasure X H) (f : X → ℂ) : Submodule ℂ H where
  carrier := {x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    refine (lintegral_mono' (P.diag_add_le x y) le_rfl).trans_lt ?_
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, nsmul_eq_mul,
      nsmul_eq_mul, Nat.cast_ofNat]
    exact ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top ENNReal.ofNat_lt_top hx, ENNReal.mul_lt_top ENNReal.ofNat_lt_top hy⟩
  smul_mem' c x hx := by
    change ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag (c • x)) < ∞
    rw [P.diag_smul, lintegral_smul_measure, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top eNorm_lt_top) hx

private abbrev cutoffSet (f : X → ℂ) (r : ℝ) : Set X := {t | ‖f t‖ ≤ r}

private lemma measurableSet_cutoffSet {f : X → ℂ} (hf : Measurable f) (r : ℝ) :
    MeasurableSet (cutoffSet f r) :=
  measurableSet_le hf.norm measurable_const

omit [MeasurableSpace X] in
private lemma monotone_cutoffSet (f : X → ℂ) : Monotone (fun n : ℕ => cutoffSet f n) := by
  intro m n hmn t ht
  exact (show ‖f t‖ ≤ m from ht).trans (Nat.cast_le.2 hmn)

omit [MeasurableSpace X] in
private lemma iUnion_cutoffSet (f : X → ℂ) : (⋃ n : ℕ, cutoffSet f n) = Set.univ := by
  refine Set.eq_univ_of_forall fun t => Set.mem_iUnion.2 ⟨Nat.ceil ‖f t‖, ?_⟩
  exact Nat.le_ceil ‖f t‖

/-- Bounded Borel truncation `{t | ‖f t‖ ≤ r}.indicator f` of a measurable symbol `f`. -/
private def cutoffSymbol (f : X → ℂ) (hf : Measurable f) (r : ℝ) : BoundedBorelFunction X :=
  BoundedBorelFunction.ofFunction ((cutoffSet f r).indicator f)
    (hf.indicator (measurableSet_cutoffSet hf r))
    ⟨max r 0, le_max_right r 0, fun t => by
      by_cases ht : t ∈ cutoffSet f r
      · rw [Set.indicator_of_mem ht]
        exact (ht : ‖f t‖ ≤ r).trans (le_max_left r 0)
      · simp [ht]⟩

@[simp]
private lemma cutoffSymbol_apply {f : X → ℂ} (hf : Measurable f) (r : ℝ) (t : X) :
    cutoffSymbol f hf r t = (cutoffSet f r).indicator f t :=
  BoundedBorelFunction.ofFunction_apply _ _ _ t

private lemma norm_cutoffSymbol_le {f : X → ℂ} (hf : Measurable f) (r : ℝ) (t : X) :
    ‖cutoffSymbol f hf r t‖ ≤ ‖f t‖ := by
  rw [cutoffSymbol_apply]
  exact norm_indicator_le_norm_self f t

private lemma cutoffSymbol_star {f : X → ℂ} (hf : Measurable f) (r : ℝ) :
    cutoffSymbol (star f) (show Measurable (star f) from continuous_star.measurable.comp hf) r =
      star (cutoffSymbol f hf r) := by
  ext t
  by_cases ht : ‖f t‖ ≤ r <;> simp [cutoffSet, ht]

private lemma tendsto_cutoffSymbol {f : X → ℂ} (hf : Measurable f) (t : X) :
    Tendsto (fun n : ℕ => (cutoffSymbol f hf n t : ℂ)) atTop (𝓝 (f t)) := by
  refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil ‖f t‖) fun n hn => ?_
  have ht : t ∈ cutoffSet f n := (Nat.le_ceil ‖f t‖).trans (Nat.cast_le.2 hn)
  simp [ht]

private lemma memLp_of_mem_spectralIntegralDomain (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {x : H} (hx : x ∈ spectralIntegralDomain P f) :
    MemLp f 2 (P.diag x) := by
  have hx' : ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞ := hx
  exact (eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
    hf.aestronglyMeasurable).2 (by simpa [ENNReal.rpow_two] using hx')

private lemma cauchySeq_integral_cutoffSymbol (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {x : H} (hx : x ∈ spectralIntegralDomain P f) :
    CauchySeq (fun n : ℕ => P.integral (cutoffSymbol f hf n) x) := by
  rw [cauchySeq_iff_tendsto_dist_atTop_0]
  have hf_lp := memLp_of_mem_spectralIntegralDomain P hf hx
  have hf_sq : Integrable (fun t => 4 * ‖f t‖ ^ 2) (P.diag x) :=
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf_lp).const_mul 4
  have hsq : Tendsto (fun p : ℕ × ℕ =>
      ‖P.integral (cutoffSymbol f hf p.1) x - P.integral (cutoffSymbol f hf p.2) x‖ ^ 2)
      atTop (𝓝 0) := by
    rw [← prod_atTop_atTop_eq]
    simp_rw [← sub_apply, ← map_sub, P.norm_sq_integral_apply, BoundedBorelFunction.sub_apply]
    have hdom := tendsto_integral_filter_of_dominated_convergence (l := atTop ×ˢ atTop)
      (F := fun p : ℕ × ℕ => fun t => ‖cutoffSymbol f hf p.1 t - cutoffSymbol f hf p.2 t‖ ^ 2)
      (f := fun _ => (0 : ℝ))
      (fun t => 4 * ‖f t‖ ^ 2)
      (Eventually.of_forall fun p : ℕ × ℕ =>
        (((cutoffSymbol f hf p.1).measurable.sub
          (cutoffSymbol f hf p.2).measurable).norm.pow_const 2).aestronglyMeasurable)
      (Eventually.of_forall fun p : ℕ × ℕ => Eventually.of_forall fun t => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have hsum : ‖cutoffSymbol f hf p.1 t - cutoffSymbol f hf p.2 t‖ ≤ 2 * ‖f t‖ := by
          calc
            ‖cutoffSymbol f hf p.1 t - cutoffSymbol f hf p.2 t‖ ≤
                ‖cutoffSymbol f hf p.1 t‖ + ‖cutoffSymbol f hf p.2 t‖ := norm_sub_le _ _
            _ ≤ ‖f t‖ + ‖f t‖ :=
              add_le_add (norm_cutoffSymbol_le hf p.1 t) (norm_cutoffSymbol_le hf p.2 t)
            _ = 2 * ‖f t‖ := (two_mul _).symm
        nlinarith [norm_nonneg (cutoffSymbol f hf p.1 t - cutoffSymbol f hf p.2 t),
          norm_nonneg (f t)])
      hf_sq
      (Eventually.of_forall fun t => by
        have hsub : Tendsto (fun p : ℕ × ℕ =>
            (cutoffSymbol f hf p.1 t : ℂ) - cutoffSymbol f hf p.2 t)
            (atTop ×ˢ atTop) (𝓝 0) := by
          simpa using ((tendsto_cutoffSymbol hf t).comp tendsto_fst).sub
            ((tendsto_cutoffSymbol hf t).comp tendsto_snd)
        simpa using hsub.norm.pow 2)
    simpa using hdom
  have hrt : Tendsto (fun p : ℕ × ℕ =>
      Real.sqrt (‖P.integral (cutoffSymbol f hf p.1) x -
        P.integral (cutoffSymbol f hf p.2) x‖ ^ 2)) atTop (𝓝 0) := by
    simpa using hsq.sqrt
  refine hrt.congr fun p => ?_
  rw [Real.sqrt_sq (norm_nonneg _), dist_eq_norm]

/-- The unbounded spectral integral `∫ f dP` of a measurable symbol `f : X → ℂ` against a
projection-valued measure `P : ProjValMeasure X H`, realized as a partial linear operator on the
second-moment subspace `{x : H | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}`. -/
def spectralIntegral (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) : H →ₗ.[ℂ] H where
  domain := spectralIntegralDomain P f
  toFun :=
    { toFun x := limUnder atTop (fun n : ℕ => P.integral (cutoffSymbol f hf n) (x : H))
      map_add' x y := by
        have hx := (cauchySeq_integral_cutoffSymbol P hf x.2).tendsto_limUnder
        have hy := (cauchySeq_integral_cutoffSymbol P hf y.2).tendsto_limUnder
        have hxy := (cauchySeq_integral_cutoffSymbol P hf (x + y).2).tendsto_limUnder
        exact tendsto_nhds_unique hxy (by simpa only [Submodule.coe_add, map_add] using hx.add hy)
      map_smul' c x := by
        have hx := (cauchySeq_integral_cutoffSymbol P hf x.2).tendsto_limUnder
        have hcx := (cauchySeq_integral_cutoffSymbol P hf (c • x).2).tendsto_limUnder
        exact tendsto_nhds_unique hcx
          (by simpa only [Submodule.coe_smul, map_smul, RingHom.id_apply] using hx.const_smul c) }

private lemma tendsto_integral_cutoffSymbol (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    Tendsto (fun n : ℕ => P.integral (cutoffSymbol f hf n) (x : H))
      atTop (𝓝 (P.spectralIntegral f hf x)) :=
  (cauchySeq_integral_cutoffSymbol P hf x.2).tendsto_limUnder

omit [CompleteSpace H] in
private lemma linearPMap_congr_apply {S T : H →ₗ.[ℂ] H} (h : S = T) {x : H}
    (hxS : x ∈ S.domain) (hxT : x ∈ T.domain) :
    S ⟨x, hxS⟩ = T ⟨x, hxT⟩ := by
  subst h; rfl

/-! ### Domain, matrix elements, uniqueness characterization, and norm identities -/

/-- A vector belongs to the domain of `P.spectralIntegral f hf` iff its diagonal spectral measure
has finite second moment for `f`. -/
@[simp]
theorem mem_spectralIntegral_domain_iff (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : H) :
    x ∈ (P.spectralIntegral f hf).domain ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞ :=
  Iff.rfl

/-- Domain membership for `P.spectralIntegral f hf` is equivalent to `MemLp f 2 (P.diag x)`. -/
theorem mem_spectralIntegral_domain_iff_memLp (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : H) :
    x ∈ (P.spectralIntegral f hf).domain ↔ MemLp f 2 (P.diag x) :=
  ⟨memLp_of_mem_spectralIntegralDomain P hf, fun h => by
    simpa [ENNReal.rpow_two] using
      lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
        h.eLpNorm_lt_top⟩

/-- Domain membership for `P.spectralIntegral f hf` is equivalent to Bochner integrability of
`t ↦ ‖f t‖ ^ 2` against `P.diag x`. -/
theorem mem_spectralIntegral_domain_iff_integrable_norm_sq (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (x : H) :
    x ∈ (P.spectralIntegral f hf).domain ↔ Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) := by
  rw [P.mem_spectralIntegral_domain_iff_memLp hf,
    memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable]

/-- For every vector `x` in the domain of `P.spectralIntegral f hf` and every `y : H`, the symbol
`f` is integrable against the polarized complex measure `P.polarizedComplexMeasure y x`. -/
theorem integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain (P : ProjValMeasure X H)
    {f : X → ℂ} (hf : Measurable f) {x : H} (hx : x ∈ (P.spectralIntegral f hf).domain) (y : H) :
    (P.polarizedComplexMeasure y x).Integrable f :=
  P.integrable_polarizedComplexMeasure_of_memLp
    ((P.mem_spectralIntegral_domain_iff_memLp hf x).mp hx) y

/-- Matrix-element formula for the unbounded spectral integral: for every `x` in the domain and
every `y : H`, `⟪y, (∫ f dP) x⟫_ℂ` is the vector-measure integral of `f` against
`P.polarizedComplexMeasure y x`. -/
theorem inner_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) (y : H) :
    ⟪y, P.spectralIntegral f hf x⟫_ℂ =
      ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x] := by
  have hint := P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain hf x.2 y
  have hlhs : Tendsto (fun n : ℕ => ⟪y, P.integral (cutoffSymbol f hf n) (x : H)⟫_ℂ)
      atTop (𝓝 ⟪y, P.spectralIntegral f hf x⟫_ℂ) :=
    (continuous_const.inner continuous_id).continuousAt.tendsto.comp
      (tendsto_integral_cutoffSymbol P hf x)
  have hrhs : Tendsto (fun n : ℕ =>
      ∫ᵛ t, (cutoffSymbol f hf n t : ℂ) ∂[ContinuousLinearMap.mul ℝ ℂ;
        P.polarizedComplexMeasure y x])
      atTop (𝓝 (∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x])) :=
    VectorMeasure.tendsto_integral_of_dominated_convergence (fun t => ‖f t‖)
      (fun n => (cutoffSymbol f hf n).measurable.aestronglyMeasurable)
      hint.norm
      (fun n => Eventually.of_forall fun t => norm_cutoffSymbol_le hf n t)
      (Eventually.of_forall fun t => tendsto_cutoffSymbol hf t)
  simp_rw [P.integral_polarizedComplexMeasure_eq_inner_integral] at hrhs
  exact tendsto_nhds_unique hlhs hrhs

/-- Universal characterization of `P.spectralIntegral f hf`: a partial linear operator `T` equals
`P.spectralIntegral f hf` iff it has the second-moment domain and the polarized matrix elements of
`f`. -/
theorem eq_spectralIntegral_iff (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (T : H →ₗ.[ℂ] H) :
    T = P.spectralIntegral f hf ↔
      (∀ x : H, x ∈ T.domain ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞) ∧
      ∀ (x : T.domain) (y : H),
        ⟪y, T x⟫_ℂ = ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x] := by
  constructor
  · rintro rfl
    exact ⟨P.mem_spectralIntegral_domain_iff hf, P.inner_spectralIntegral hf⟩
  · rintro ⟨hdom, hinner⟩
    refine LinearPMap.ext (Submodule.ext hdom) fun x hxT hxP => ?_
    refine ext_inner_left ℂ fun y => ?_
    rw [hinner ⟨x, hxT⟩ y, P.inner_spectralIntegral hf ⟨x, hxP⟩ y]

/-- Second-moment isometry on the domain: `‖(∫ f dP) x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)`. -/
theorem norm_sq_spectralIntegral_apply (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    ‖P.spectralIntegral f hf x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x) := by
  have hf_sq : Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) :=
    (P.mem_spectralIntegral_domain_iff_integrable_norm_sq hf x).mp x.2
  have hlhs : Tendsto (fun n : ℕ => ‖P.integral (cutoffSymbol f hf n) (x : H)‖ ^ 2)
      atTop (𝓝 (‖P.spectralIntegral f hf x‖ ^ 2)) :=
    ((tendsto_integral_cutoffSymbol P hf x).norm).pow 2
  have hrhs : Tendsto (fun n : ℕ => ∫ t, ‖cutoffSymbol f hf n t‖ ^ 2 ∂(P.diag x))
      atTop (𝓝 (∫ t, ‖f t‖ ^ 2 ∂(P.diag x))) :=
    tendsto_integral_of_dominated_convergence (fun t => ‖f t‖ ^ 2)
      (fun n => ((cutoffSymbol f hf n).measurable.norm.pow_const 2).aestronglyMeasurable)
      hf_sq
      (fun n => Eventually.of_forall fun t => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_cutoffSymbol_le hf n t) 2)
      (Eventually.of_forall fun t => ((tendsto_cutoffSymbol hf t).norm).pow 2)
  simp_rw [← P.norm_sq_integral_apply] at hrhs
  exact tendsto_nhds_unique hlhs hrhs

/-- Extended-norm form of the second-moment identity:
`‖(∫ f dP) x‖ₑ ^ 2 = ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x)`. -/
theorem eNorm_sq_spectralIntegral_apply (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    ‖P.spectralIntegral f hf x‖ₑ ^ 2 = ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) := by
  have hf_sq : Integrable (fun t => ‖f t‖ ^ 2) (P.diag x) :=
    (P.mem_spectralIntegral_domain_iff_integrable_norm_sq hf x).mp x.2
  calc
    ‖P.spectralIntegral f hf x‖ₑ ^ 2 = ENNReal.ofReal (‖P.spectralIntegral f hf x‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ = ENNReal.ofReal (∫ t, ‖f t‖ ^ 2 ∂(P.diag x)) := by
      rw [P.norm_sq_spectralIntegral_apply hf x]
    _ = ∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(P.diag x) :=
      ofReal_integral_eq_lintegral_ofReal hf_sq (Eventually.of_forall fun _ => sq_nonneg _)
    _ = ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) := by
      congr with t
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- For `x` in the domain of `P.spectralIntegral f hf`, `(∫ f dP) x = 0` iff `f` vanishes
`P.diag x`-almost everywhere. -/
theorem spectralIntegral_apply_eq_zero_iff (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    P.spectralIntegral f hf x = 0 ↔ f =ᵐ[P.diag x] 0 := by
  rw [← eNorm_eq_zero, ← sq_eq_zero_iff, P.eNorm_sq_spectralIntegral_apply hf x,
    lintegral_eq_zero_iff (hf.eNorm.pow_const 2)]
  refine eventually_congr (Eventually.of_forall fun t => ?_)
  simp

/-! ### Bounded symbols, spectral cutoffs, density, and `P.ae`-invariance -/

/-- Compatibility with bounded Borel functional calculus: for a bounded Borel symbol `g`, the
unbounded spectral integral `P.spectralIntegral g g.measurable` has full domain `⊤` and agrees
with `(P.integral g).toLinearMap.toPMap ⊤`. -/
@[simp]
theorem spectralIntegral_boundedBorelFunction (P : ProjValMeasure X H)
    (g : BoundedBorelFunction X) :
    P.spectralIntegral g g.measurable = (P.integral g).toLinearMap.toPMap ⊤ := by
  symm
  rw [P.eq_spectralIntegral_iff g.measurable]
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · simp only [LinearMap.toPMap_domain, Submodule.mem_top, true_iff]
    calc
      ∫⁻ t, ‖g t‖ₑ ^ 2 ∂(P.diag x) ≤ ∫⁻ _, (‖g‖ₑ ^ 2) ∂(P.diag x) :=
        lintegral_mono fun t => pow_le_pow_left' (eNorm_le_iff_norm_le.2 (g.norm_coe_le_norm t)) 2
      _ = ‖g‖ₑ ^ 2 * P.diag x Set.univ := lintegral_const _
      _ < ∞ := ENNReal.mul_lt_top (ENNReal.pow_lt_top eNorm_lt_top) (measure_lt_top _ _)
  · change ⟪y, P.integral g (x : H)⟫_ℂ = _
    exact (P.integral_polarizedComplexMeasure_eq_inner_integral g y x).symm

/-- Spectral projections preserve the domain of every unbounded spectral integral. -/
theorem proj_mem_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    {B : Set X} (hB : MeasurableSet B) {x : H} (hx : x ∈ (P.spectralIntegral f hf).domain) :
    P.proj B hB x ∈ (P.spectralIntegral f hf).domain := by
  rw [P.mem_spectralIntegral_domain_iff hf, P.diag_proj hB]
  exact (setLIntegral_le_lintegral B _).trans_lt hx

/-- Every spectral projection `P.proj B hB` commutes with `P.spectralIntegral f hf` on its
domain. -/
theorem spectralIntegral_proj_apply (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    {B : Set X} (hB : MeasurableSet B) (x : (P.spectralIntegral f hf).domain) :
    P.spectralIntegral f hf ⟨P.proj B hB x, P.proj_mem_spectralIntegral_domain hf hB x.2⟩ =
      P.proj B hB (P.spectralIntegral f hf x) := by
  refine ext_inner_left ℂ fun y => ?_
  have hsym : ⟪y, P.proj B hB (P.spectralIntegral f hf x)⟫_ℂ =
      ⟪P.proj B hB y, P.spectralIntegral f hf x⟫_ℂ :=
    ((P.isSelfAdjoint_proj B hB).isSymmetric y _).symm
  rw [P.inner_spectralIntegral hf, hsym, P.inner_spectralIntegral hf,
    P.polarizedComplexMeasure_proj_right y (x : H) hB,
    P.polarizedComplexMeasure_proj_left y (x : H) hB]

/-- On any measurable set `B` where `f` is bounded in norm by `M`, the range of `P.proj B hB` lies
entirely inside `(P.spectralIntegral f hf).domain`. -/
theorem proj_mem_spectralIntegral_domain_of_norm_le (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {B : Set X} (hB : MeasurableSet B) {M : ℝ} (hM : ∀ t ∈ B, ‖f t‖ ≤ M)
    (x : H) :
    P.proj B hB x ∈ (P.spectralIntegral f hf).domain := by
  rw [P.mem_spectralIntegral_domain_iff hf, P.diag_proj hB]
  calc
    ∫⁻ t in B, ‖f t‖ₑ ^ 2 ∂(P.diag x) ≤ ∫⁻ _ in B, (ENNReal.ofReal M ^ 2) ∂(P.diag x) := by
      refine setLIntegral_mono measurable_const fun t ht => ?_
      rw [← ofReal_norm]
      exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal (hM t ht)) 2
    _ = ENNReal.ofReal M ^ 2 * P.diag x B := setLIntegral_const B _
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (measure_lt_top _ _)

/-- If a bounded Borel symbol `g` agrees with `f` on a measurable set `B`, then on the spectral
subspace `range (P.proj B hB)` the unbounded spectral integral `P.spectralIntegral f hf` agrees with
the bounded spectral integral `P.integral g`. -/
theorem spectralIntegral_proj_eq_integral_proj (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {B : Set X} (hB : MeasurableSet B) (g : BoundedBorelFunction X)
    (hg : ∀ t ∈ B, f t = g t) (x : H) (hx : P.proj B hB x ∈ (P.spectralIntegral f hf).domain) :
    P.spectralIntegral f hf ⟨P.proj B hB x, hx⟩ = P.integral g (P.proj B hB x) := by
  refine ext_inner_left ℂ fun y => ?_
  rw [P.inner_spectralIntegral hf, ← P.integral_polarizedComplexMeasure_eq_inner_integral,
    P.polarizedComplexMeasure_proj_right y x hB]
  exact VectorMeasure.integral_congr_ae <| by
    rw [VectorMeasure.variation_restrict hB]
    exact ae_restrict_of_forall_mem hB hg

/-- If a bounded Borel symbol `g` agrees with `B.indicator f` at every point, then applying
`P.spectralIntegral f hf` to `P.proj B hB x` equals `P.integral g x`. -/
theorem spectralIntegral_proj_eq_integral_of_eq_indicator (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {B : Set X} (hB : MeasurableSet B) (g : BoundedBorelFunction X)
    (hg : ∀ t, g t = B.indicator f t) (x : H)
    (hx : P.proj B hB x ∈ (P.spectralIntegral f hf).domain) :
    P.spectralIntegral f hf ⟨P.proj B hB x, hx⟩ = P.integral g x := by
  have hmul : g * BoundedBorelFunction.indicator B hB 1 = g := by
    ext t
    by_cases ht : t ∈ B <;> simp [hg t, ht]
  rw [P.spectralIntegral_proj_eq_integral_proj hf hB g
    (fun t ht => by rw [hg t, Set.indicator_of_mem ht]) x hx,
    ← P.integral_indicator hB, ← mul_apply_eq_comp, ← map_mul, hmul]

/-- The second-moment domain of `P.spectralIntegral f hf` is dense in `H`. -/
theorem dense_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    Dense ((P.spectralIntegral f hf).domain : Set H) := by
  intro x
  have hmem (n : ℕ) :
      P.proj (cutoffSet f n) (measurableSet_cutoffSet hf n) x ∈
        ((P.spectralIntegral f hf).domain : Set H) :=
    P.proj_mem_spectralIntegral_domain_of_norm_le hf (measurableSet_cutoffSet hf n)
      (fun _ ht => ht) x
  have hU : MeasurableSet (⋃ n : ℕ, cutoffSet f n) :=
    MeasurableSet.iUnion (fun n => measurableSet_cutoffSet hf n)
  have htend := P.tendsto_proj_of_monotone (f := fun n : ℕ => cutoffSet f n)
    (fun n => measurableSet_cutoffSet hf n) hU (monotone_cutoffSet f) x
  have hlim : P.proj (⋃ n : ℕ, cutoffSet f n) hU x = x := by
    rw [P.proj_congr (iUnion_cutoffSet f) hU MeasurableSet.univ, P.proj_univ]
    rfl
  rw [hlim] at htend
  exact mem_closure_of_tendsto htend (Eventually.of_forall hmem)

/-- The diagonal spectral measure at `(∫ f dP) x` has density `‖f t‖ₑ ^ 2` with respect to
`P.diag x`. -/
theorem diag_spectralIntegral_apply (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    P.diag (P.spectralIntegral f hf x) = (P.diag x).withDensity fun t => ‖f t‖ₑ ^ 2 := by
  refine Measure.ext fun B hB => ?_
  rw [← P.enorm_sq_proj_apply B hB, ← P.spectralIntegral_proj_apply hf hB x,
    P.eNorm_sq_spectralIntegral_apply hf, P.diag_proj hB, withDensity_apply _ hB]

/-- The unbounded spectral integral `P.spectralIntegral f hf` is the zero partial operator `0`
(with domain `⊤`) iff `f =ᶠ[P.ae] 0`. -/
theorem spectralIntegral_eq_zero_iff (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    P.spectralIntegral f hf = 0 ↔ f =ᶠ[P.ae] 0 := by
  constructor
  · intro h
    rw [EventuallyEq, P.eventually_ae_iff]
    intro x
    have hx : x ∈ (P.spectralIntegral f hf).domain := by rw [h]; trivial
    have hzero : P.spectralIntegral f hf ⟨x, hx⟩ = 0 :=
      linearPMap_congr_apply h hx Submodule.mem_top
    exact (P.spectralIntegral_apply_eq_zero_iff hf ⟨x, hx⟩).mp hzero
  · intro h
    rw [eq_comm, P.eq_spectralIntegral_iff hf]
    refine ⟨fun x => ?_, fun x y => ?_⟩
    · simp only [LinearPMap.zero_domain, Submodule.mem_top, true_iff]
      have hx : (fun t => ‖f t‖ₑ ^ 2) =ᵐ[P.diag x] (fun _ => 0) :=
        (P.ae_diag_of_ae x h).mono fun t ht => by simp [ht]
      rw [lintegral_congr_ae hx, lintegral_zero]
      exact ENNReal.zero_lt_top
    · have hyx : f =ᵐ[(P.polarizedComplexMeasure y x).variation] 0 :=
        (P.variation_polarizedComplexMeasure_absolutelyContinuous_right y x).ae_le
          (P.ae_diag_of_ae x h)
      simp [VectorMeasure.integral_congr_ae hyx]

/-- Measurable symbols that agree `P`-almost everywhere have equal unbounded spectral integrals. -/
theorem spectralIntegral_congr_ae (P : ProjValMeasure X H) {f g : X → ℂ}
    (hf : Measurable f) (hg : Measurable g) (h : f =ᶠ[P.ae] g) :
    P.spectralIntegral f hf = P.spectralIntegral g hg := by
  rw [P.eq_spectralIntegral_iff hg]
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · rw [P.mem_spectralIntegral_domain_iff hf]
    have hx : (fun t => ‖f t‖ₑ ^ 2) =ᵐ[P.diag x] (fun t => ‖g t‖ₑ ^ 2) :=
      (P.ae_diag_of_ae x h).mono fun t ht => by simp [ht]
    rw [lintegral_congr_ae hx]
  · rw [P.inner_spectralIntegral hf]
    have hyx : f =ᵐ[(P.polarizedComplexMeasure y x).variation] g :=
      (P.variation_polarizedComplexMeasure_absolutelyContinuous_right y x).ae_le
        (P.ae_diag_of_ae x h)
    exact VectorMeasure.integral_congr_ae hyx

/-- Two measurable symbols define the same unbounded spectral integral iff they agree
`P`-almost everywhere. -/
theorem spectralIntegral_eq_spectralIntegral_iff (P : ProjValMeasure X H) {f g : X → ℂ}
    (hf : Measurable f) (hg : Measurable g) :
    P.spectralIntegral f hf = P.spectralIntegral g hg ↔ f =ᶠ[P.ae] g := by
  refine ⟨fun h => ?_, P.spectralIntegral_congr_ae hf hg⟩
  rw [EventuallyEq, P.eventually_ae_iff]
  intro x
  let E (n : ℕ) : Set X := cutoffSet f n ∩ cutoffSet g n
  have hEm (n : ℕ) : MeasurableSet (E n) :=
    (measurableSet_cutoffSet hf n).inter (measurableSet_cutoffSet hg n)
  have hE_union : (⋃ n : ℕ, E n) = Set.univ := by
    refine Set.eq_univ_of_forall fun t => Set.mem_iUnion.2
      ⟨max (Nat.ceil ‖f t‖) (Nat.ceil ‖g t‖), ?_, ?_⟩
    · exact (Nat.le_ceil ‖f t‖).trans (Nat.cast_le.2 (le_max_left _ _))
    · exact (Nat.le_ceil ‖g t‖).trans (Nat.cast_le.2 (le_max_right _ _))
  have hrestr (n : ℕ) : ∀ᵐ t ∂(P.diag x).restrict (E n), f t = g t := by
    let xn := P.proj (E n) (hEm n) x
    have hxf : xn ∈ (P.spectralIntegral f hf).domain :=
      P.proj_mem_spectralIntegral_domain_of_norm_le hf (hEm n) (fun _ ht => ht.1) x
    have hxg : xn ∈ (P.spectralIntegral g hg).domain :=
      P.proj_mem_spectralIntegral_domain_of_norm_le hg (hEm n) (fun _ ht => ht.2) x
    have hxsub : xn ∈ (P.spectralIntegral (f - g) (hf.sub hg)).domain :=
      P.proj_mem_spectralIntegral_domain_of_norm_le (hf.sub hg) (hEm n)
        (fun t ht => (norm_sub_le _ _).trans (add_le_add ht.1 ht.2)) x
    have hzero : P.spectralIntegral (f - g) (hf.sub hg) ⟨xn, hxsub⟩ = 0 := by
      refine ext_inner_left ℂ fun y => ?_
      rw [inner_zero_right, P.inner_spectralIntegral (hf.sub hg)]
      have hintf := P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain hf hxf y
      have hintg := P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain hg hxg y
      rw [show (fun t => (f - g) t) = f - g from rfl,
        VectorMeasure.integral_sub hintf hintg, ← P.inner_spectralIntegral hf ⟨xn, hxf⟩ y,
        ← P.inner_spectralIntegral hg ⟨xn, hxg⟩ y,
        linearPMap_congr_apply h hxf hxg, sub_self]
    have hae := (P.spectralIntegral_apply_eq_zero_iff (hf.sub hg) ⟨xn, hxsub⟩).mp hzero
    rw [P.diag_proj (hEm n)] at hae
    exact hae.mono fun t ht => sub_eq_zero.mp ht
  rw [← Measure.restrict_univ (μ := P.diag x), ← hE_union, ae_restrict_iUnion_iff]
  exact hrestr

/-- The unbounded spectral integral of `0` is the globally defined zero partial operator `0`. -/
@[simp]
theorem spectralIntegral_zero (P : ProjValMeasure X H) :
    P.spectralIntegral 0 measurable_zero = 0 := by
  refine (P.spectralIntegral_congr_ae measurable_zero (0 : BoundedBorelFunction X).measurable
    (Eventually.of_forall fun _ => rfl)).trans ?_
  rw [P.spectralIntegral_boundedBorelFunction, map_zero]
  exact LinearPMap.ext rfl fun _ _ _ => rfl

/-- The unbounded spectral integral of `1` is the globally defined identity partial operator. -/
@[simp]
theorem spectralIntegral_one (P : ProjValMeasure X H) :
    P.spectralIntegral 1 measurable_one = LinearMap.id.toPMap ⊤ := by
  refine (P.spectralIntegral_congr_ae measurable_one (1 : BoundedBorelFunction X).measurable
    (Eventually.of_forall fun _ => rfl)).trans ?_
  rw [P.spectralIntegral_boundedBorelFunction, map_one]
  exact LinearPMap.ext rfl fun _ _ _ => rfl

/-- The unbounded spectral integral of a constant symbol `c` is `c • id` on the whole space `⊤`. -/
theorem spectralIntegral_const (P : ProjValMeasure X H) (c : ℂ) :
    P.spectralIntegral (fun _ => c) measurable_const = (c • LinearMap.id).toPMap ⊤ := by
  let g : BoundedBorelFunction X := algebraMap ℂ (BoundedBorelFunction X) c
  refine (P.spectralIntegral_congr_ae measurable_const g.measurable
    (Eventually.of_forall fun _ => rfl)).trans ?_
  rw [P.spectralIntegral_boundedBorelFunction]
  have hg : P.integral g = c • 1 := by
    simp [g, Algebra.algebraMap_eq_smul_one]
  rw [hg]
  exact LinearPMap.ext rfl fun _ _ _ => rfl

/-- The unbounded spectral integral of `{0, 1}`-indicator `B.indicator 1` is `P.proj B hB` on
the whole space `⊤`. -/
theorem spectralIntegral_indicator_one (P : ProjValMeasure X H) {B : Set X} (hB : MeasurableSet B) :
    P.spectralIntegral (B.indicator 1) (measurable_one.indicator hB) =
      (P.proj B hB).toLinearMap.toPMap ⊤ := by
  simpa [BoundedBorelFunction.coe_indicator, P.integral_indicator hB] using
    P.spectralIntegral_boundedBorelFunction (BoundedBorelFunction.indicator B hB 1)

/-! ### Algebraic and multiplicative calculus laws -/

/-- Multiplying a measurable symbol `f` on the left by a bounded Borel symbol `g` preserves all
second-moment domain vectors of `f`. -/
theorem mem_spectralIntegral_domain_mul_boundedBorelFunction_left (P : ProjValMeasure X H)
    (g : BoundedBorelFunction X) {f : X → ℂ} (hf : Measurable f) {x : H}
    (hx : x ∈ (P.spectralIntegral f hf).domain) :
    x ∈ (P.spectralIntegral (⇑g * f) (g.measurable.mul hf)).domain := by
  rw [P.mem_spectralIntegral_domain_iff (g.measurable.mul hf)]
  calc
    ∫⁻ t, ‖(⇑g * f) t‖ₑ ^ 2 ∂(P.diag x) ≤ ∫⁻ t, ‖g‖ₑ ^ 2 * ‖f t‖ₑ ^ 2 ∂(P.diag x) := by
      refine lintegral_mono fun t => ?_
      simp only [Pi.mul_apply, eNorm_mul, mul_pow]
      gcongr
      exact eNorm_le_iff_norm_le.2 (g.norm_coe_le_norm t)
    _ = ‖g‖ₑ ^ 2 * ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) :=
      lintegral_const_mul _ (hf.eNorm.pow_const 2)
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.pow_lt_top eNorm_lt_top) hx

/-- Multiplying a measurable symbol `f` on the right by a bounded Borel symbol `g` preserves all
second-moment domain vectors of `f`. -/
theorem mem_spectralIntegral_domain_mul_boundedBorelFunction_right (P : ProjValMeasure X H)
    (g : BoundedBorelFunction X) {f : X → ℂ} (hf : Measurable f) {x : H}
    (hx : x ∈ (P.spectralIntegral f hf).domain) :
    x ∈ (P.spectralIntegral (f * ⇑g) (hf.mul g.measurable)).domain := by
  have h := P.mem_spectralIntegral_domain_mul_boundedBorelFunction_left g hf hx
  rwa [P.mem_spectralIntegral_domain_iff (g.measurable.mul hf),
    mul_comm ⇑g f, ← P.mem_spectralIntegral_domain_iff (hf.mul g.measurable)] at h

/-- Every bounded spectral integral `P.integral g` intertwines `P.spectralIntegral f hf` with
`P.spectralIntegral (g * f)`. -/
theorem integral_spectralIntegral_apply (P : ProjValMeasure X H) (g : BoundedBorelFunction X)
    {f : X → ℂ} (hf : Measurable f) (x : (P.spectralIntegral f hf).domain) :
    P.integral g (P.spectralIntegral f hf x) =
      P.spectralIntegral (⇑g * f) (g.measurable.mul hf)
        ⟨x, P.mem_spectralIntegral_domain_mul_boundedBorelFunction_left g hf x.2⟩ := by
  refine ext_inner_left ℂ fun y => ?_
  have hadj : ContinuousLinearMap.adjoint (P.integral g) = P.integral (star g) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  rw [← ContinuousLinearMap.adjoint_inner_left, hadj, P.inner_spectralIntegral hf,
    P.integral_polarizedComplexMeasure_integral_left (star g) f y x,
    P.inner_spectralIntegral (g.measurable.mul hf)]
  congr with t
  simp [mul_comm]

/-- Negating the symbol negates the unbounded spectral integral. -/
@[simp]
theorem spectralIntegral_neg (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    P.spectralIntegral (-f) hf.neg = -P.spectralIntegral f hf := by
  symm
  rw [P.eq_spectralIntegral_iff hf.neg]
  refine ⟨fun x => by simp [P.mem_spectralIntegral_domain_iff hf], fun x y => ?_⟩
  change ⟪y, -P.spectralIntegral f hf x⟫_ℂ = _
  rw [inner_neg_right, P.inner_spectralIntegral hf x y, ← VectorMeasure.integral_neg]

/-- Scalar multiplication inclusion `c • (∫ f dP) ≤ ∫ (c • f) dP` for all `c : ℂ` (strict when
`c = 0` and `f` is unbounded). -/
theorem smul_le_spectralIntegral_smul (P : ProjValMeasure X H) (c : ℂ) {f : X → ℂ}
    (hf : Measurable f) :
    c • P.spectralIntegral f hf ≤ P.spectralIntegral (c • f) (hf.const_smul c) := by
  let g : BoundedBorelFunction X := algebraMap ℂ (BoundedBorelFunction X) c
  refine ⟨fun x hx => ?_, fun x y hxy => ?_⟩
  · rw [LinearPMap.smul_domain] at hx
    have h := P.mem_spectralIntegral_domain_mul_boundedBorelFunction_left g hf hx
    simpa [g] using h
  · have hx : (x : H) ∈ (P.spectralIntegral f hf).domain := x.2
    have hact := P.integral_spectralIntegral_apply g hf ⟨x, hx⟩
    have hcg : P.integral g (P.spectralIntegral f hf ⟨x, hx⟩) =
        c • P.spectralIntegral f hf ⟨x, hx⟩ := by
      simp [g, Algebra.algebraMap_eq_smul_one]
    have hfun : P.spectralIntegral (⇑g * f) (g.measurable.mul hf) =
        P.spectralIntegral (c • f) (hf.const_smul c) :=
      P.spectralIntegral_congr_ae (g.measurable.mul hf) (hf.const_smul c)
        (Eventually.of_forall fun _ => rfl)
    calc
      (c • P.spectralIntegral f hf) x = P.integral g (P.spectralIntegral f hf ⟨x, hx⟩) :=
        hcg.symm
      _ = P.spectralIntegral (⇑g * f) (g.measurable.mul hf)
            ⟨x, P.mem_spectralIntegral_domain_mul_boundedBorelFunction_left g hf hx⟩ := hact
      _ = P.spectralIntegral (c • f) (hf.const_smul c) ⟨x, hxy ▸ y.2⟩ :=
        linearPMap_congr_apply hfun _ _
      _ = P.spectralIntegral (c • f) (hf.const_smul c) y := congrArg _ (Subtype.ext hxy)

/-- For every nonzero scalar `c ≠ 0`, `∫ (c • f) dP = c • ∫ f dP` with identical domains. -/
theorem spectralIntegral_smul_of_ne_zero (P : ProjValMeasure X H) {c : ℂ} (hc : c ≠ 0) {f : X → ℂ}
    (hf : Measurable f) :
    P.spectralIntegral (c • f) (hf.const_smul c) = c • P.spectralIntegral f hf := by
  refine (LinearPMap.eq_of_le_of_domain_eq (P.smul_le_spectralIntegral_smul c hf) ?_).symm
  refine le_antisymm (P.smul_le_spectralIntegral_smul c hf).1 fun x hx => ?_
  rw [LinearPMap.smul_domain]
  have hinv := (P.smul_le_spectralIntegral_smul c⁻¹ (hf.const_smul c)).1 hx
  simpa [inv_smul_smul₀ hc] using hinv

/-- Sum inclusion `(∫ f dP) + (∫ g dP) ≤ ∫ (f + g) dP`: on the intersection of the second-moment
domains, the spectral integral of `f + g` agrees with the operator sum (strict when cancellations
enlarge the domain, such as `g = -f`). -/
theorem add_le_spectralIntegral_add (P : ProjValMeasure X H) {f g : X → ℂ}
    (hf : Measurable f) (hg : Measurable g) :
    P.spectralIntegral f hf + P.spectralIntegral g hg ≤
      P.spectralIntegral (f + g) (hf.add hg) := by
  refine ⟨fun x hx => ?_, fun x y hxy => ?_⟩
  · rw [LinearPMap.add_domain, Submodule.mem_inf, P.mem_spectralIntegral_domain_iff_memLp hf,
      P.mem_spectralIntegral_domain_iff_memLp hg] at hx
    rw [P.mem_spectralIntegral_domain_iff_memLp (hf.add hg)]
    exact hx.1.add hx.2
  · refine ext_inner_left ℂ fun z => ?_
    have hxf : (x : H) ∈ (P.spectralIntegral f hf).domain := x.2.1
    have hxg : (x : H) ∈ (P.spectralIntegral g hg).domain := x.2.2
    have hintf := P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain hf hxf z
    have hintg := P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain hg hxg z
    rw [LinearPMap.add_apply, inner_add_right, P.inner_spectralIntegral hf ⟨x, hxf⟩ z,
      P.inner_spectralIntegral hg ⟨x, hxg⟩ z, P.inner_spectralIntegral (hf.add hg) y z,
      ← hxy, ← VectorMeasure.integral_add hintf hintg]

/-- Adding a bounded Borel symbol `g` shifts `P.spectralIntegral f hf` by the globally defined
bounded operator `P.integral g` without changing its domain. -/
theorem spectralIntegral_add_boundedBorelFunction_left (P : ProjValMeasure X H)
    (g : BoundedBorelFunction X) {f : X → ℂ} (hf : Measurable f) :
    P.spectralIntegral (⇑g + f) (g.measurable.add hf) =
      (P.integral g).toLinearMap +ᵥ P.spectralIntegral f hf := by
  symm
  rw [P.eq_spectralIntegral_iff (g.measurable.add hf)]
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · rw [LinearPMap.vadd_domain, P.mem_spectralIntegral_domain_iff_memLp hf,
      ← P.mem_spectralIntegral_domain_iff (g.measurable.add hf),
      P.mem_spectralIntegral_domain_iff_memLp (g.measurable.add hf)]
    have hg_lp : MemLp (g : X → ℂ) 2 (P.diag x) := by
      rw [← P.mem_spectralIntegral_domain_iff_memLp g.measurable,
        P.spectralIntegral_boundedBorelFunction]
      trivial
    exact ⟨fun hx => hg_lp.add hx, fun hsum => by simpa using hg_lp.neg.add hsum⟩
  · have hfx : (x : H) ∈ (P.spectralIntegral f hf).domain := x.2
    have hintg : (P.polarizedComplexMeasure y x).Integrable (g : X → ℂ) := g.integrable _
    have hintf := P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain hf hfx y
    change ⟪y, P.integral g (x : H) + P.spectralIntegral f hf ⟨x, hfx⟩⟫_ℂ = _
    rw [inner_add_right, ← P.integral_polarizedComplexMeasure_eq_inner_integral g y x,
      P.inner_spectralIntegral hf ⟨x, hfx⟩ y, ← VectorMeasure.integral_add hintg hintf]

/-- Right-hand form of bounded perturbation: adding a bounded Borel symbol `g` on the right shifts
`P.spectralIntegral f hf` by `P.integral g` without changing its domain. -/
theorem spectralIntegral_add_boundedBorelFunction_right (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (g : BoundedBorelFunction X) :
    P.spectralIntegral (f + ⇑g) (hf.add g.measurable) =
      (P.integral g).toLinearMap +ᵥ P.spectralIntegral f hf := by
  rw [← P.spectralIntegral_add_boundedBorelFunction_left g hf]
  exact P.spectralIntegral_congr_ae (hf.add g.measurable) (g.measurable.add hf)
    (Eventually.of_forall fun t => add_comm (f t) (g t))

/-- Right-composing `P.spectralIntegral f hf` with a bounded spectral integral `P.integral g`:
`P.integral g x` belongs to `(P.spectralIntegral f hf).domain` iff `x` belongs to
`(P.spectralIntegral (f * g) (hf.mul g.measurable)).domain`. -/
theorem mem_spectralIntegral_domain_integral_iff (P : ProjValMeasure X H)
    (g : BoundedBorelFunction X) {f : X → ℂ} (hf : Measurable f) (x : H) :
    P.integral g x ∈ (P.spectralIntegral f hf).domain ↔
      x ∈ (P.spectralIntegral (f * ⇑g) (hf.mul g.measurable)).domain := by
  rw [P.mem_spectralIntegral_domain_iff hf, P.diag_integral g x,
    lintegral_withDensity_eq_lintegral_mul _ (g.measurable.eNorm.pow_const 2)
      (hf.eNorm.pow_const 2), P.mem_spectralIntegral_domain_iff (hf.mul g.measurable)]
  have hcongr : ((fun t => ‖g t‖ₑ ^ 2) * fun t => ‖f t‖ₑ ^ 2) = fun t => ‖(f * ⇑g) t‖ₑ ^ 2 := by
    ext t; simp [mul_pow, mul_comm]
  rw [hcongr]

/-- Applying `P.spectralIntegral f hf` to `P.integral g x` evaluates `P.spectralIntegral (f * g)`
at `x`. -/
theorem spectralIntegral_integral_apply (P : ProjValMeasure X H) (g : BoundedBorelFunction X)
    {f : X → ℂ} (hf : Measurable f) {x : H}
    (hx : x ∈ (P.spectralIntegral (f * ⇑g) (hf.mul g.measurable)).domain) :
    P.spectralIntegral f hf ⟨P.integral g x,
        (P.mem_spectralIntegral_domain_integral_iff g hf x).mpr hx⟩ =
      P.spectralIntegral (f * ⇑g) (hf.mul g.measurable) ⟨x, hx⟩ := by
  refine ext_inner_left ℂ fun y => ?_
  rw [P.inner_spectralIntegral hf, P.inner_spectralIntegral (hf.mul g.measurable),
    P.integral_polarizedComplexMeasure_integral_right g f y x]
  rfl

/-- Every bounded spectral integral `P.integral g` maps `(P.spectralIntegral f hf).domain` into
itself and commutes with `P.spectralIntegral f hf`. -/
theorem spectralIntegral_integral_eq_integral_spectralIntegral (P : ProjValMeasure X H)
    (g : BoundedBorelFunction X) {f : X → ℂ} (hf : Measurable f)
    (x : (P.spectralIntegral f hf).domain) :
    P.spectralIntegral f hf
        ⟨P.integral g x, (P.mem_spectralIntegral_domain_integral_iff g hf x).mpr
          (P.mem_spectralIntegral_domain_mul_boundedBorelFunction_right g hf x.2)⟩ =
      P.integral g (P.spectralIntegral f hf x) := by
  have hx_fg := P.mem_spectralIntegral_domain_mul_boundedBorelFunction_right g hf x.2
  rw [P.spectralIntegral_integral_apply g hf hx_fg, P.integral_spectralIntegral_apply g hf x]
  have heq : P.spectralIntegral (f * ⇑g) (hf.mul g.measurable) =
      P.spectralIntegral (⇑g * f) (g.measurable.mul hf) :=
    P.spectralIntegral_congr_ae (hf.mul g.measurable) (g.measurable.mul hf)
      (Eventually.of_forall (congrFun (mul_comm f ⇑g)))
  exact linearPMap_congr_apply heq _ _

/-- Multiplicative domain characterization for composing two unbounded spectral integrals
(Teschl (3.27)): for `x` in `(P.spectralIntegral f hf).domain`, `(∫ f dP) x` belongs to
`(P.spectralIntegral g hg).domain` iff `x` belongs to
`(P.spectralIntegral (g * f) (hg.mul hf)).domain`. -/
theorem mem_spectralIntegral_domain_spectralIntegral_apply_iff (P : ProjValMeasure X H)
    {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g)
    (x : (P.spectralIntegral f hf).domain) :
    P.spectralIntegral f hf x ∈ (P.spectralIntegral g hg).domain ↔
      (x : H) ∈ (P.spectralIntegral (g * f) (hg.mul hf)).domain := by
  rw [P.mem_spectralIntegral_domain_iff hg, P.diag_spectralIntegral_apply hf x,
    lintegral_withDensity_eq_lintegral_mul _ (hf.eNorm.pow_const 2) (hg.eNorm.pow_const 2),
    P.mem_spectralIntegral_domain_iff (hg.mul hf)]
  have hcongr : ((fun t => ‖f t‖ₑ ^ 2) * fun t => ‖g t‖ₑ ^ 2) = fun t => ‖(g * f) t‖ₑ ^ 2 := by
    ext t; simp [mul_pow, mul_comm]
  rw [hcongr]

/-- Multiplicative evaluation law for composing two unbounded spectral integrals (Teschl (3.27)):
whenever `x ∈ D(f(P))` and `f(P) x ∈ D(g(P))`, `g(P) (f(P) x) = (g * f)(P) x`. -/
theorem spectralIntegral_spectralIntegral_apply (P : ProjValMeasure X H)
    {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g)
    (x : (P.spectralIntegral f hf).domain)
    (hx : P.spectralIntegral f hf x ∈ (P.spectralIntegral g hg).domain) :
    P.spectralIntegral g hg ⟨P.spectralIntegral f hf x, hx⟩ =
      P.spectralIntegral (g * f) (hg.mul hf)
        ⟨x, (P.mem_spectralIntegral_domain_spectralIntegral_apply_iff hf hg x).mp hx⟩ := by
  let hx_gf := (P.mem_spectralIntegral_domain_spectralIntegral_apply_iff hf hg x).mp hx
  refine ext_inner_left ℂ fun y => ?_
  have hint :=
    P.integrable_polarizedComplexMeasure_of_mem_spectralIntegral_domain (hg.mul hf) hx_gf y
  have hlhs : Tendsto
      (fun n : ℕ => ⟪y, P.integral (cutoffSymbol g hg n) (P.spectralIntegral f hf x)⟫_ℂ)
      atTop (𝓝 ⟪y, P.spectralIntegral g hg ⟨P.spectralIntegral f hf x, hx⟩⟫_ℂ) :=
    (continuous_const.inner continuous_id).continuousAt.tendsto.comp
      (tendsto_integral_cutoffSymbol P hg ⟨P.spectralIntegral f hf x, hx⟩)
  have hrhs : Tendsto
      (fun n : ℕ => ∫ᵛ t, cutoffSymbol g hg n t * f t
        ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x])
      atTop (𝓝 (∫ᵛ t, (g * f) t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x])) :=
    VectorMeasure.tendsto_integral_of_dominated_convergence (fun t => ‖(g * f) t‖)
      (fun n => ((cutoffSymbol g hg n).measurable.mul hf).aestronglyMeasurable)
      hint.norm
      (fun n => Eventually.of_forall fun t => by
        simp only [Pi.mul_apply, norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_cutoffSymbol_le hg n t) (norm_nonneg _))
      (Eventually.of_forall fun t => (tendsto_cutoffSymbol hg t).mul tendsto_const_nhds)
  have hstep (n : ℕ) :
      ⟪y, P.integral (cutoffSymbol g hg n) (P.spectralIntegral f hf x)⟫_ℂ =
        ∫ᵛ t, cutoffSymbol g hg n t * f t
          ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x] := by
    rw [P.integral_spectralIntegral_apply (cutoffSymbol g hg n) hf x,
      P.inner_spectralIntegral ((cutoffSymbol g hg n).measurable.mul hf)]
    rfl
  simp_rw [← hstep] at hrhs
  rw [P.inner_spectralIntegral (hg.mul hf)]
  exact tendsto_nhds_unique hlhs hrhs

/-! ### Hilbert adjoint, closedness, truncation core, self-adjointness, and uniqueness -/

/-- `P.spectralIntegral (star f) ...` is a formal adjoint of `P.spectralIntegral f hf`. -/
theorem isFormalAdjoint_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) :
    (P.spectralIntegral f hf).IsFormalAdjoint
      (P.spectralIntegral (star f) (continuous_star.measurable.comp hf)) := by
  have hfs : Measurable (star f) := continuous_star.measurable.comp hf
  intro x y
  have hlhs : Tendsto (fun n : ℕ => ⟪P.integral (cutoffSymbol f hf n) (x : H), (y : H)⟫_ℂ)
      atTop (𝓝 ⟪P.spectralIntegral f hf x, (y : H)⟫_ℂ) :=
    (continuous_id.inner continuous_const).continuousAt.tendsto.comp
      (tendsto_integral_cutoffSymbol P hf x)
  have hrhs : Tendsto
      (fun n : ℕ => ⟪(x : H), P.integral (cutoffSymbol (star f) hfs n) (y : H)⟫_ℂ)
      atTop (𝓝 ⟪(x : H), P.spectralIntegral (star f) hfs y⟫_ℂ) :=
    (continuous_const.inner continuous_id).continuousAt.tendsto.comp
      (tendsto_integral_cutoffSymbol P hfs y)
  refine tendsto_nhds_unique hlhs (hrhs.congr fun n => ?_)
  have hadj : ContinuousLinearMap.adjoint (P.integral (cutoffSymbol f hf n)) =
      P.integral (cutoffSymbol (star f) hfs n) := by
    rw [cutoffSymbol_star, ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  rw [← hadj, ContinuousLinearMap.adjoint_inner_right]

private lemma integral_cutoffSymbol_star_adjoint_eq_proj (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (y : (P.spectralIntegral f hf)†.domain) (n : ℕ) :
    P.integral (cutoffSymbol (star f)
        (show Measurable (star f) from continuous_star.measurable.comp hf) n) (y : H) =
      P.proj (cutoffSet f n) (measurableSet_cutoffSet hf n) ((P.spectralIntegral f hf)† y) := by
  have hfs : Measurable (star f) := continuous_star.measurable.comp hf
  refine ext_inner_right ℂ fun w => ?_
  have hBn := measurableSet_cutoffSet hf n
  let xw : (P.spectralIntegral f hf).domain :=
    ⟨P.proj (cutoffSet f n) hBn w,
      P.proj_mem_spectralIntegral_domain_of_norm_le hf hBn (fun _ ht => ht) w⟩
  have hTxw : P.spectralIntegral f hf xw = P.integral (cutoffSymbol f hf n) w :=
    P.spectralIntegral_proj_eq_integral_of_eq_indicator hf hBn (cutoffSymbol f hf n)
      (cutoffSymbol_apply hf n) w xw.2
  have hform : ⟪(P.spectralIntegral f hf)† y, (xw : H)⟫_ℂ =
      ⟪(y : H), P.spectralIntegral f hf xw⟫_ℂ :=
    LinearPMap.adjoint_isFormalAdjoint (P.dense_spectralIntegral_domain hf) y xw
  have hsym : ⟪P.proj (cutoffSet f n) hBn ((P.spectralIntegral f hf)† y), w⟫_ℂ =
      ⟪(P.spectralIntegral f hf)† y, P.proj (cutoffSet f n) hBn w⟫_ℂ :=
    (P.isSelfAdjoint_proj (cutoffSet f n) hBn).isSymmetric _ w
  have hadj : ContinuousLinearMap.adjoint (P.integral (cutoffSymbol f hf n)) =
      P.integral (cutoffSymbol (star f) hfs n) := by
    rw [cutoffSymbol_star, ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  rw [← hadj, ContinuousLinearMap.adjoint_inner_left, ← hTxw, ← hform, hsym]

/-- The Hilbert-space adjoint of `P.spectralIntegral f hf` is the spectral integral of the
pointwise conjugate symbol `star f`. -/
@[simp]
theorem adjoint_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    (P.spectralIntegral f hf)† =
      P.spectralIntegral (star f) (continuous_star.measurable.comp hf) := by
  have hfs : Measurable (star f) := continuous_star.measurable.comp hf
  have hle := (P.isFormalAdjoint_spectralIntegral hf).le_adjoint
    (P.dense_spectralIntegral_domain hf)
  refine (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 ?_)).symm
  intro y hy
  let z : H := (P.spectralIntegral f hf)† ⟨y, hy⟩
  have hbound (n : ℕ) :
      ∫⁻ t, ‖cutoffSymbol (star f) hfs n t‖ₑ ^ 2 ∂(P.diag y) ≤ ‖z‖ₑ ^ 2 := by
    have hdiag : ∫⁻ t, ‖cutoffSymbol (star f) hfs n t‖ₑ ^ 2 ∂(P.diag y) =
        ‖P.integral (cutoffSymbol (star f) hfs n) y‖ₑ ^ 2 := by
      rw [← P.diag_univ, P.diag_integral, withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ]
    rw [hdiag, integral_cutoffSymbol_star_adjoint_eq_proj P hf ⟨y, hy⟩ n]
    exact pow_le_pow_left'
      (eNorm_le_iff_norm_le.2 (P.norm_proj_apply_le _ (measurableSet_cutoffSet hf n) z)) 2
  have hmono : Monotone (fun n : ℕ => fun t => ‖cutoffSymbol (star f) hfs n t‖ₑ ^ 2) := by
    intro m n hmn t
    by_cases htm : t ∈ cutoffSet (star f) m
    · have htn : t ∈ cutoffSet (star f) n := monotone_cutoffSet (star f) hmn htm
      simp [htm, htn]
    · simp [htm]
  have hsup (t : X) : (⨆ n : ℕ, ‖cutoffSymbol (star f) hfs n t‖ₑ ^ 2) = ‖star f t‖ₑ ^ 2 := by
    refine le_antisymm (iSup_le fun n => pow_le_pow_left'
      (eNorm_le_iff_norm_le.2 (norm_cutoffSymbol_le hfs n t)) 2) ?_
    refine le_iSup_of_le (Nat.ceil ‖f t‖) ?_
    have ht : t ∈ cutoffSet (star f) (Nat.ceil ‖f t‖) := by
      simpa [cutoffSet] using Nat.le_ceil ‖f t‖
    rw [cutoffSymbol_apply, Set.indicator_of_mem ht]
  rw [P.mem_spectralIntegral_domain_iff hfs]
  simp_rw [← hsup]
  rw [lintegral_iSup (fun n => (cutoffSymbol (star f) hfs n).measurable.eNorm.pow_const 2) hmono]
  exact (iSup_le hbound).trans_lt (ENNReal.pow_lt_top eNorm_lt_top)

/-- The Hilbert adjoint of `P.spectralIntegral f hf` has the same domain as
`P.spectralIntegral f hf`. -/
theorem adjoint_spectralIntegral_domain (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    (P.spectralIntegral f hf)†.domain = (P.spectralIntegral f hf).domain := by
  rw [P.adjoint_spectralIntegral hf]
  ext x
  simp [P.mem_spectralIntegral_domain_iff]

/-- Normality of unbounded spectral integrals: `P.spectralIntegral f hf` and its Hilbert adjoint
have the same domain and equal norms on every domain vector. -/
theorem norm_adjoint_spectralIntegral_apply (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) {x : H} (hx : x ∈ (P.spectralIntegral f hf).domain) :
    ‖(P.spectralIntegral f hf)† ⟨x, by rwa [P.adjoint_spectralIntegral_domain hf]⟩‖ =
      ‖P.spectralIntegral f hf ⟨x, hx⟩‖ := by
  have hfs : Measurable (star f) := continuous_star.measurable.comp hf
  have hx' : x ∈ (P.spectralIntegral (star f) hfs).domain := by
    simpa [P.mem_spectralIntegral_domain_iff] using hx
  have heq : (P.spectralIntegral f hf)† ⟨x, by rwa [P.adjoint_spectralIntegral_domain hf]⟩ =
      P.spectralIntegral (star f) hfs ⟨x, hx'⟩ :=
    linearPMap_congr_apply (P.adjoint_spectralIntegral hf) _ hx'
  rw [heq]
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [P.norm_sq_spectralIntegral_apply hfs ⟨x, hx'⟩,
    P.norm_sq_spectralIntegral_apply hf ⟨x, hx⟩]
  simp

/-- Every unbounded spectral integral `P.spectralIntegral f hf` is a closed partial linear
operator. -/
theorem isClosed_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f) :
    (P.spectralIntegral f hf).IsClosed := by
  have hfs : Measurable (star f) := continuous_star.measurable.comp hf
  have hfss : Measurable (star (star f)) := continuous_star.measurable.comp hfs
  have heq : P.spectralIntegral f hf = (P.spectralIntegral (star f) hfs)† := by
    rw [P.adjoint_spectralIntegral hfs]
    exact P.spectralIntegral_congr_ae hf hfss (Eventually.of_forall fun t => by simp)
  rw [heq]
  exact LinearPMap.adjoint_isClosed (P.dense_spectralIntegral_domain hfs)

/-- The increasing union (supremum) of the spectral subspaces `range (P {t | ‖f t‖ ≤ n})` is an
operator core (`LinearPMap.HasCore`) for `P.spectralIntegral f hf`. -/
theorem hasCore_iSup_proj_range_spectralIntegral (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) :
    (P.spectralIntegral f hf).HasCore
      (⨆ n : ℕ, LinearMap.range
        (P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const)).toLinearMap) := by
  let S : Submodule ℂ H := ⨆ n : ℕ, LinearMap.range
    (P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const)).toLinearMap
  have hS : S ≤ (P.spectralIntegral f hf).domain := by
    refine iSup_le fun n => ?_
    rintro _ ⟨w, rfl⟩
    exact P.proj_mem_spectralIntegral_domain_of_norm_le hf
      (measurableSet_le hf.norm measurable_const) (fun _ ht => ht) w
  rw [(P.isClosed_spectralIntegral hf).hasCore_iff_graph_subset_closure hS]
  intro p hp
  have hxp : p.1 ∈ (P.spectralIntegral f hf).domain := LinearPMap.mem_domain_of_mem_graph hp
  have hyp : p.2 = P.spectralIntegral f hf ⟨p.1, hxp⟩ :=
    (LinearPMap.image_iff hxp).2 hp
  let u (n : ℕ) : H := P.proj (cutoffSet f n) (measurableSet_cutoffSet hf n) p.1
  have huS (n : ℕ) : u n ∈ S :=
    Submodule.mem_iSup_of_mem n ⟨p.1, rfl⟩
  have huD (n : ℕ) : u n ∈ (P.spectralIntegral f hf).domain := hS (huS n)
  have huSD (n : ℕ) : u n ∈ ((P.spectralIntegral f hf).domRestrict S).domain :=
    Submodule.mem_inf.2 ⟨huS n, huD n⟩
  have hU : MeasurableSet (⋃ n : ℕ, cutoffSet f n) :=
    MeasurableSet.iUnion (fun n => measurableSet_cutoffSet hf n)
  have hu_lim : Tendsto u atTop (𝓝 p.1) := by
    have htend := P.tendsto_proj_of_monotone (f := fun n : ℕ => cutoffSet f n)
      (fun n => measurableSet_cutoffSet hf n) hU (monotone_cutoffSet f) p.1
    have hlim : P.proj (⋃ n : ℕ, cutoffSet f n) hU p.1 = p.1 := by
      rw [P.proj_congr (iUnion_cutoffSet f) hU MeasurableSet.univ, P.proj_univ]
      rfl
    rwa [hlim] at htend
  have hTu_lim : Tendsto (fun n : ℕ =>
      ((P.spectralIntegral f hf).domRestrict S) ⟨u n, huSD n⟩) atTop (𝓝 p.2) := by
    rw [hyp]
    refine (tendsto_integral_cutoffSymbol P hf ⟨p.1, hxp⟩).congr fun n => ?_
    have hdom : ((P.spectralIntegral f hf).domRestrict S) ⟨u n, huSD n⟩ =
        P.spectralIntegral f hf ⟨u n, huD n⟩ :=
      (P.spectralIntegral f hf).domRestrict_le.2 rfl
    rw [hdom, P.spectralIntegral_proj_eq_integral_of_eq_indicator hf
      (measurableSet_cutoffSet hf n) (cutoffSymbol f hf n) (cutoffSymbol_apply hf n) p.1 (huD n)]
  refine mem_closure_of_tendsto (hu_lim.prodMk_nhds hTu_lim) (Eventually.of_forall fun n => ?_)
  exact ((P.spectralIntegral f hf).domRestrict S).mem_graph ⟨u n, huSD n⟩

/-- The unbounded spectral integral `P.spectralIntegral f hf` is self-adjoint iff `f` is real-valued
`P`-almost everywhere (`star f =ᶠ[P.ae] f`). -/
theorem isSelfAdjoint_spectralIntegral_iff (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) :
    IsSelfAdjoint (P.spectralIntegral f hf) ↔ star f =ᶠ[P.ae] f := by
  have hfs : Measurable (star f) := continuous_star.measurable.comp hf
  rw [LinearPMap.isSelfAdjoint_def, P.adjoint_spectralIntegral hf]
  exact P.spectralIntegral_eq_spectralIntegral_iff hfs hf

/-- If `star f =ᶠ[P.ae] f`, then `P.spectralIntegral f hf` is self-adjoint. -/
theorem isSelfAdjoint_spectralIntegral_of_ae_star_eq (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (h : star f =ᶠ[P.ae] f) :
    IsSelfAdjoint (P.spectralIntegral f hf) :=
  (P.isSelfAdjoint_spectralIntegral_iff hf).2 h

/-- Existence and uniqueness of the unbounded spectral integral: for every projection-valued
measure `P` on a measurable space `X` and every measurable symbol `f : X → ℂ`, there is a unique
partial linear operator `T : H →ₗ.[ℂ] H` on the second-moment domain whose matrix elements are the
polarized vector-measure integrals of `f`; moreover `T` is densely defined and closed, satisfies
the second-moment norm identity, and has Hilbert adjoint with the same domain and the polarized
matrix elements of `star f`. -/
theorem existsUnique_spectralIntegral (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) :
    ∃! T : H →ₗ.[ℂ] H,
      (∀ x : H, x ∈ T.domain ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞) ∧
      (∀ (x : T.domain) (y : H),
        ⟪y, T x⟫_ℂ = ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) ∧
      Dense (T.domain : Set H) ∧ T.IsClosed ∧
      (∀ x : T.domain, ‖T x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)) ∧
      T.adjoint.domain = T.domain ∧
      (∀ (x : T.adjoint.domain) (y : H),
        ⟪y, T.adjoint x⟫_ℂ =
          ∫ᵛ t, star (f t) ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) := by
  have hfs : Measurable (star f) := continuous_star.measurable.comp hf
  refine ⟨P.spectralIntegral f hf, ?_,
    fun T hT => (P.eq_spectralIntegral_iff hf T).2 ⟨hT.1, hT.2.1⟩⟩
  refine ⟨P.mem_spectralIntegral_domain_iff hf, P.inner_spectralIntegral hf,
    P.dense_spectralIntegral_domain hf, P.isClosed_spectralIntegral hf,
    P.norm_sq_spectralIntegral_apply hf, P.adjoint_spectralIntegral_domain hf, fun x y => ?_⟩
  have hx0 : (x : H) ∈ (P.spectralIntegral f hf).domain :=
    (P.adjoint_spectralIntegral_domain hf) ▸ x.2
  have hx' : (x : H) ∈ (P.spectralIntegral (star f) hfs).domain := by
    simpa [P.mem_spectralIntegral_domain_iff] using hx0
  have heq : (P.spectralIntegral f hf).adjoint x = P.spectralIntegral (star f) hfs ⟨x, hx'⟩ :=
    linearPMap_congr_apply (P.adjoint_spectralIntegral hf) x.2 hx'
  rw [heq, P.inner_spectralIntegral hfs ⟨x, hx'⟩ y]
  rfl

end TauCeti.ProjValMeasure
