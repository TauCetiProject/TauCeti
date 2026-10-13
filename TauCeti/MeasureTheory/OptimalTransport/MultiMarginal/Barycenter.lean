/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.CompleteSquare
public import TauCeti.MeasureTheory.OptimalTransport.MultiMarginal.Basic
public import TauCeti.MeasureTheory.Measure.FrechetMean.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
import TauCeti.MeasureTheory.Measure.FrechetMean.Selection
import TauCeti.MeasureTheory.OptimalTransport.MultiMarginal.Existence
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.FrechetMean

/-!
# Wasserstein barycenters as a multi-marginal problem

Let `μ j` be finitely many probability laws on a metric space `X` and `w j` nonnegative weights
summing to `1`. The `p`-Wasserstein barycenter problem minimizes
`ν ↦ ∑ j, w j * W_p(ν, μ j) ^ p` over probability laws `ν`. It is equivalent to the multi-marginal
transport problem of the laws `μ j` for the cost

`c x = inf_z ∑ j, w j * d(z, x j) ^ p`,

the least value of the `p`-Fréchet power functional of the weighted law `∑ j, w j • δ_{x j}` of a
configuration `x : J → X`. If `T` is a measurable map sending each configuration to a minimizer,
the law of `T` under a multi-coupling `γ` costs at most `∫ c dγ`, because `(T x, x j)_# γ` couples
it with `μ j`; conversely, gluing optimal plans out of any law `ν` gives a multi-coupling of cost
at most that of `ν`. So the law of `T` under an optimal multi-coupling is a barycenter.

For `1 ≤ p < ∞` the cost `c` is continuous, so on a Polish metric space an optimal multi-coupling
exists. On a proper metric space the pointwise barycenter map `T` can moreover be chosen
measurably (`TauCeti.exists_measurable_isFrechetBarycenter_sum_smul_dirac`). Hence every law on
the Wasserstein space `P_p(X)` with finitely many atoms has a Fréchet barycenter. This is the
finitely supported case of Le Gouic and Loubes' existence theorem. `P_p(X)` need not be proper,
and no properness of it is used; the compactness used is that of the multi-couplings of finitely
many laws.

In the quadratic Euclidean case the pointwise barycenter is the weighted mean. Let `E` be a real
inner product space, `μ i` finitely many probability laws on `E` and `w i`
nonnegative weights summing to `1`. The quadratic Wasserstein barycenter problem minimizes

`ν ↦ ∑ i, w i * W₂(ν, μ i) ^ 2`

over probability laws `ν`. Writing `m x = ∑ j, w j • x j` for the weighted mean of a configuration
`x : ι → E`, the multi-marginal problem minimizes

`γ ↦ ∫ ∑ i, w i * ‖m x - x i‖ ^ 2 dγ(x)`

over the multi-marginal couplings `γ` of the family `μ`. The two problems are equivalent.

* Every multi-coupling `γ` yields the candidate law `γ.map m`, whose barycentric cost is at most
  the multi-marginal cost of `γ`: the plan `(m x, x i)_# γ` couples `γ.map m` with `μ i`.
* Conversely, for every probability law `ν`, gluing optimal plans from `ν` to each `μ i` along
  their common marginal `ν` gives a multi-coupling `γ` with
  `∫ ∑ i, w i * ‖m x - x i‖ ^ 2 dγ + W₂(ν, γ.map m) ^ 2 ≤ ∑ i, w i * W₂(ν, μ i) ^ 2`.
  This is the weighted variance decomposition `Finset.sum_mul_edist_sq_eq` integrated against the
  glued plan.

Hence the two infima agree, the weighted mean of an optimal multi-coupling is a barycenter, and
every barycenter of finite cost is the weighted mean of an optimal multi-coupling. These
statements take their values in `[0, ∞]` and need no moment hypotheses. For laws of finite second
moment they identify the quadratic Fréchet barycenters in the Wasserstein space `P₂ (E)` of the
finitely supported law `∑ i, w i • δ_{μ i}`.

The space `E` is assumed separable throughout. The first comparison holds in any separable real
normed space, while the gluing step and the separation of laws by `W₂` use the inner product and
completeness.

## Main statements

* `TauCeti.sum_mul_wassersteinEDist_rpow_map_le` — the barycentric cost of the law of a measurable
  map `T` under a multi-coupling is at most `∫ ∑ j, w j * d(T x, x j) ^ p dγ`.
* `TauCeti.exists_isMultiCoupling_lintegral_iInf_le` — on a Polish space, every probability law
  costs at least the multi-marginal cost of some multi-coupling.
* `TauCeti.isMinOn_sum_mul_wassersteinEDist_rpow_map` — the law of a measurable choice of pointwise
  barycenters under an optimal multi-coupling is a barycenter.
* `TauCeti.exists_isMultiCoupling_isMinOn_lintegral_iInf` — on a Polish space, the multi-marginal
  problem is attained.
* `TauCeti.WassersteinSpace.isMinOn_sum_mul_wassersteinEDist_rpow_of_isFrechetBarycenter` — on a
  Polish space, a barycenter in `P_p(X)` of `∑ j, w j • δ_{μ j}` minimizes the weighted cost over
  all laws.
* `TauCeti.iInf_sum_mul_wassersteinEDist_rpow_eq` — on a proper space, the multi-marginal problem
  has the same value as the barycenter problem.
* `TauCeti.WassersteinSpace.exists_isFrechetBarycenter_sum_smul_dirac` — on a proper space, every
  law `∑ j, w j • δ_{μ j}` on `P_p(X)` has a Fréchet barycenter.
* `TauCeti.WassersteinSpace.exists_ae_isFrechetBarycenter_sum_smul_dirac` — conversely, every such
  barycenter is the first marginal of a joint law with a multi-coupling of the laws `μ j`, under
  which almost every point is a pointwise barycenter of its configuration.
* `TauCeti.sum_mul_wassersteinEDist_sq_map_le` — the barycentric cost of the weighted mean of a
  multi-coupling is at most its multi-marginal cost.
* `TauCeti.exists_isMultiCoupling_lintegral_add_wassersteinEDist_sq_le` — every probability law
  is dominated, in the sense above, by the weighted mean of some multi-coupling.
* `TauCeti.iInf_sum_mul_wassersteinEDist_sq_eq` — the barycentric and multi-marginal infima
  coincide.
* `TauCeti.isMinOn_sum_mul_wassersteinEDist_sq_map` — the weighted mean of an optimal
  multi-coupling is a barycenter.
* `TauCeti.exists_isMinOn_lintegral_map_eq` — a barycenter of finite cost is the weighted mean of
  an optimal multi-coupling.
* `TauCeti.isFrechetBarycenter_two_iff_exists_isMinOn_lintegral_map_eq` — in `P₂ (E)`, the
  quadratic Fréchet barycenters of `∑ i, w i • δ_{μ i}` are exactly the weighted means of the
  optimal multi-couplings of the laws `μ i`.

## References

* T. Le Gouic and J.-M. Loubes, *Existence and consistency of Wasserstein barycenters*,
  Probab. Theory Relat. Fields 168 (2017), 901--917, Theorem 8, for the existence of barycenters
  of finitely supported laws through the multi-marginal problem on a proper space.
* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43
  (2011), 904--924, Section 4, for the multi-marginal formulation of the barycenter problem.
* W. Gangbo and A. Święch, *Optimal maps for the multidimensional Monge--Kantorovich problem*,
  Comm. Pure Appl. Math. 51 (1998), 23--45, for the multi-marginal quadratic transport problem.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

section General

variable {J X : Type*} [Fintype J] [PseudoEMetricSpace X] [MeasurableSpace X] {w : J → ℝ≥0}
  {p : ℝ≥0∞}

/-- **The law of a measurable selection is a competitor for the barycenter.** For every
multi-marginal coupling `γ` of the laws `μ j` and every measurable map `T : (J → X) → X`, the
weighted `p`-Wasserstein cost of the law of `T` under `γ` is at most
`∫ ∑ j, w j * d(T x, x j) ^ p dγ`: the law of `(T x, x j)` under `γ` couples the law of `T` with
`μ j`. -/
theorem sum_mul_wassersteinEDist_rpow_map_le (hd : Measurable fun z : X × X ↦ edist z.1 z.2)
    (hp0 : p ≠ 0) (hp : p ≠ ∞) {μ : J → Measure X} {γ : Measure (J → X)}
    (hγ : Measure.IsMultiCoupling γ μ) {T : (J → X) → X} (hT : Measurable T) :
    ∑ j, (w j : ℝ≥0∞) * wassersteinEDist p (γ.map T) (μ j) ^ p.toReal ≤
      ∫⁻ x, ∑ j, (w j : ℝ≥0∞) * edist (T x) (x j) ^ p.toReal ∂γ := by
  have hm (j : J) : Measurable fun x : J → X ↦ edist (T x) (x j) ^ p.toReal :=
    (hd.comp (hT.prodMk (measurable_pi_apply j))).pow_const _
  rw [lintegral_finsetSum _ fun j _ ↦ (hm j).const_mul _]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rw [lintegral_const_mul _ (hm j)]
  refine mul_le_mul_right ?_ _
  have hc : IsCoupling (γ.map fun x ↦ (T x, x j)) (γ.map T) (μ j) :=
    ⟨Measure.fst_map_prodMk hT (measurable_pi_apply j),
      (Measure.snd_map_prodMk hT (measurable_pi_apply j)).trans (hγ.marginal_eq j)⟩
  refine (wassersteinEDist_rpow_le_lintegral hd hp0 hp hc).trans_eq ?_
  rw [lintegral_map (hd.pow_const _) (hT.prodMk (measurable_pi_apply j))]

end General

section NormedSpace

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {w : ι → ℝ≥0}

omit [BorelSpace E] [SecondCountableTopology E] in
/-- For weights summing to `1`, the weighted mean of a multi-coupling of probability laws is a
probability law. -/
private theorem isProbabilityMeasure_map_sum_smul (hw : ∑ i, w i = 1) {μ : ι → Measure E}
    [∀ i, IsProbabilityMeasure (μ i)] {γ : Measure (ι → E)} (hγ : Measure.IsMultiCoupling γ μ) :
    IsProbabilityMeasure (γ.map fun x ↦ ∑ j, (w j : ℝ) • x j) := by
  obtain ⟨i, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hw.trans_ne one_ne_zero)
  have := hγ.isProbabilityMeasure i
  infer_instance

/-- **The weighted mean of a multi-coupling is a competitor for the barycenter.** For every
multi-marginal coupling `γ` of the laws `μ i`, the weighted quadratic Wasserstein cost of the law
of the weighted mean `m x = ∑ j, w j • x j` under `γ` is at most the multi-marginal cost
`∫ ∑ i, w i * ‖m x - x i‖ ^ 2 dγ`. This needs neither an inner product nor normalized weights:
it is the case `T = m`, `p = 2` of `TauCeti.sum_mul_wassersteinEDist_rpow_map_le`. -/
theorem sum_mul_wassersteinEDist_sq_map_le {μ : ι → Measure E} {γ : Measure (ι → E)}
    (hγ : Measure.IsMultiCoupling γ μ) :
    ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 (γ.map fun x ↦ ∑ j, (w j : ℝ) • x j) (μ i) ^ 2 ≤
      ∫⁻ x, ∑ i, (w i : ℝ≥0∞) * edist (∑ j, (w j : ℝ) • x j) (x i) ^ 2 ∂γ := by
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] using
    sum_mul_wassersteinEDist_rpow_map_le (w := w) measurable_edist two_ne_zero
      ENNReal.ofNat_ne_top hγ (T := fun x ↦ ∑ j, (w j : ℝ) • x j) (by fun_prop)

end NormedSpace

section Polish

variable {J X : Type*} [Fintype J] [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X] {w : J → ℝ≥0} {p : ℝ≥0∞}

omit [Fintype J] in
/-- Gluing optimal plans from `ν` to each `μ j` along their common first marginal `ν` gives a
joint law `Γ` of a point and a multi-coupling of the laws `μ j` whose `j`th pair has cost
`W_p(ν, μ j) ^ p`. -/
private theorem exists_glue_wassersteinEDist_rpow_eq [Finite J] (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (μ : J → Measure X) [∀ j, IsProbabilityMeasure (μ j)] (ν : Measure X)
    [IsProbabilityMeasure ν] :
    ∃ Γ : Measure (X × (J → X)), Γ.fst = ν ∧ Measure.IsMultiCoupling Γ.snd μ ∧
      ∀ j, wassersteinEDist p ν (μ j) ^ p.toReal = ∫⁻ q, edist q.1 (q.2 j) ^ p.toReal ∂Γ := by
  choose π hπ hπW using fun j ↦ exists_isCoupling_eLpNorm_eq_wassersteinEDist hp0 hp ν (μ j)
    ⟨_, isCoupling_prod ν (μ j)⟩
  obtain ⟨Γ, hΓfst, hΓ⟩ := Measure.exists_glue_pi_of_fst_eq fun j ↦ (hπ j).fst_eq
  have he (j : J) : Measurable (Prod.map (id : X → X) (Function.eval j : (J → X) → X)) :=
    measurable_id.prodMap (measurable_pi_apply j)
  have hΓj (j : J) : Γ.snd.map (Function.eval j) = (π j).snd := by
    rw [← hΓ j, Measure.snd, Measure.snd, Measure.map_map (measurable_pi_apply j) measurable_snd,
      Measure.map_map measurable_snd (he j)]
    rfl
  refine ⟨Γ, hΓfst, ⟨fun j ↦ (hΓj j).trans (hπ j).snd_eq⟩, fun j ↦ ?_⟩
  rw [← hπW j, eLpNorm_rpow_eq_lintegral hp0 hp measurable_edist.aemeasurable, ← hΓ j,
    lintegral_map (measurable_edist.pow_const _) (he j)]
  rfl

/-- **A barycenter in `P_p(X)` minimizes over all probability laws.** On a Polish metric space and
for `1 ≤ p < ∞`, a `p`-Fréchet barycenter `ν` in `P_p(X)` of the finitely supported law
`∑ j, w j • δ_{μ j}`, with weights summing to `1`, minimizes the weighted `p`-Wasserstein cost
`ν' ↦ ∑ j, w j * W_p(ν', μ j) ^ p` over all probability laws `ν'` on `X`, not only over `P_p(X)`.
-/
theorem WassersteinSpace.isMinOn_sum_mul_wassersteinEDist_rpow_of_isFrechetBarycenter
    [Fact (1 ≤ p)] (hp_top : p ≠ ∞) (hw : ∑ j, w j = 1) {μ : J → WassersteinSpace p X}
    {ν : WassersteinSpace p X} (hν : IsFrechetBarycenter p (∑ j, w j • Measure.dirac (μ j)) ν) :
    IsMinOn (fun ν' ↦ ∑ j, (w j : ℝ≥0∞) *
        wassersteinEDist p ν' ((μ j : ProbabilityMeasure X) : Measure X) ^ p.toReal)
      {ν' | IsProbabilityMeasure ν'} ((ν : ProbabilityMeasure X) : Measure X) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hmin := (WassersteinSpace.isFrechetBarycenter_sum_smul_dirac_iff_isMinOn hp_top μ ν).1 hν
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hw.trans_ne one_ne_zero)
  refine isMinOn_iff.2 fun ν' (hν' : IsProbabilityMeasure ν') ↦ ?_
  by_cases htop : ∑ j, (w j : ℝ≥0∞) *
      wassersteinEDist p ν' ((μ j : ProbabilityMeasure X) : Measure X) ^ p.toReal = ∞
  · exact htop ▸ le_top
  -- A law of finite barycentric cost has finite `p`-th moment, so it is a point of `P_p(X)`.
  have hmom := hasFiniteMoment_of_sum_mul_wassersteinEDist_rpow_ne_top measurable_edist
    (Finset.mem_univ j₀) (ENNReal.coe_ne_zero.2 hj₀) (μ j₀).hasFiniteMoment
    (ENNReal.toReal_pos hp0 hp_top) htop
  have hcoe : ((WassersteinSpace.mk ⟨ν', hν'⟩ hmom : ProbabilityMeasure X) : Measure X) = ν' :=
    congrArg ProbabilityMeasure.toMeasure (WassersteinSpace.coe_mk _ _)
  have hz := isMinOn_iff.1 hmin (WassersteinSpace.mk ⟨ν', hν'⟩ hmom) (mem_univ _)
  rwa [hcoe] at hz

end Polish

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {w : ι → ℝ≥0}

/-- The weighted variance decomposition, integrated against a joint law `Γ` of a point `y` and a
configuration `x`: the weighted quadratic cost from `y` to the `x i` splits as the quadratic cost
from `y` to the weighted mean `m x` plus the multi-marginal cost of the law of `x`. -/
private theorem sum_mul_lintegral_edist_sq_eq_add (hw : ∑ i, w i = 1) (Γ : Measure (E × (ι → E))) :
    ∑ i, (w i : ℝ≥0∞) * ∫⁻ q, edist q.1 (q.2 i) ^ 2 ∂Γ =
      ∫⁻ q, edist q.1 (∑ j, (w j : ℝ) • q.2 j) ^ 2 ∂Γ +
        ∫⁻ x, ∑ i, (w i : ℝ≥0∞) * edist (∑ j, (w j : ℝ) • x j) (x i) ^ 2 ∂Γ.snd := by
  rw [Measure.snd, lintegral_map (by fun_prop) measurable_snd,
    ← lintegral_add_left (by fun_prop)]
  simp only [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  rw [← lintegral_finsetSum _ fun i _ ↦ by fun_prop]
  exact lintegral_congr fun q ↦ Finset.univ.sum_mul_edist_sq_eq hw q.1 q.2

variable [CompleteSpace E]

/-- **Every law is dominated by the weighted mean of a multi-coupling.** For weights summing to
`1` and every probability law `ν`, there is a multi-marginal coupling `γ` of the laws `μ i` whose
multi-marginal cost, plus the squared `W₂` distance from `ν` to the law of the weighted mean
`m x = ∑ j, w j • x j` under `γ`, is at most the weighted quadratic Wasserstein cost of `ν`.

The coupling glues optimal plans from `ν` to each `μ i` along `ν`; the inequality is the weighted
variance decomposition `∑ i, w i * ‖y - x i‖ ^ 2 = ‖y - m x‖ ^ 2 + ∑ i, w i * ‖m x - x i‖ ^ 2`
integrated against the glued plan. -/
theorem exists_isMultiCoupling_lintegral_add_wassersteinEDist_sq_le (hw : ∑ i, w i = 1)
    (μ : ι → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (ν : Measure E)
    [IsProbabilityMeasure ν] :
    ∃ γ : Measure (ι → E), Measure.IsMultiCoupling γ μ ∧
      ∫⁻ x, ∑ i, (w i : ℝ≥0∞) * edist (∑ j, (w j : ℝ) • x j) (x i) ^ 2 ∂γ +
          wassersteinEDist 2 ν (γ.map fun x ↦ ∑ j, (w j : ℝ) • x j) ^ 2 ≤
        ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 ν (μ i) ^ 2 := by
  have hm : Measurable fun x : ι → E ↦ ∑ j, (w j : ℝ) • x j := by fun_prop
  have hm₂ : Measurable fun q : E × (ι → E) ↦ ∑ j, (w j : ℝ) • q.2 j := hm.comp measurable_snd
  -- Optimal plans from `ν` to each `μ i`, glued along their common first marginal `ν`; the
  -- squared distance from `ν` to `μ i` is the quadratic cost of the `i`th glued pair.
  obtain ⟨Γ, hΓfst, hΓ, hW⟩ :=
    exists_glue_wassersteinEDist_rpow_eq two_ne_zero ENNReal.ofNat_ne_top μ ν
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] at hW
  refine ⟨Γ.snd, hΓ, ?_⟩
  -- The law of `(y, m x)` under the glued plan couples `ν` with the law of `m x`.
  have hc : IsCoupling (Γ.map fun q ↦ (q.1, ∑ j, (w j : ℝ) • q.2 j)) ν
      (Γ.snd.map fun x ↦ ∑ j, (w j : ℝ) • x j) := by
    refine ⟨(Measure.fst_map_prodMk measurable_fst hm₂).trans hΓfst, ?_⟩
    rw [Measure.snd_map_prodMk measurable_fst hm₂, Measure.snd, Measure.map_map hm measurable_snd]
    rfl
  have hle : wassersteinEDist 2 ν (Γ.snd.map fun x ↦ ∑ j, (w j : ℝ) • x j) ^ 2 ≤
      ∫⁻ q, edist q.1 (∑ j, (w j : ℝ) • q.2 j) ^ 2 ∂Γ := by
    have h := wassersteinEDist_rpow_le_lintegral measurable_edist two_ne_zero
      ENNReal.ofNat_ne_top hc
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] at h
    refine h.trans_eq ?_
    rw [lintegral_map (by fun_prop) (measurable_fst.prodMk hm₂)]
  simp only [hW]
  rw [sum_mul_lintegral_edist_sq_eq_add hw Γ, add_comm]
  gcongr

/-- **The barycentric and multi-marginal problems have the same value.** For weights summing to
`1`, the infimum over probability laws `ν` of the weighted quadratic Wasserstein cost
`∑ i, w i * W₂(ν, μ i) ^ 2` equals the infimum over multi-marginal couplings `γ` of the laws `μ i`
of the multi-marginal cost `∫ ∑ i, w i * ‖m x - x i‖ ^ 2 dγ`, where `m x = ∑ j, w j • x j`. -/
theorem iInf_sum_mul_wassersteinEDist_sq_eq (hw : ∑ i, w i = 1) (μ : ι → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] :
    ⨅ (ν : Measure E) (_ : IsProbabilityMeasure ν),
        ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 ν (μ i) ^ 2 =
      ⨅ (γ : Measure (ι → E)) (_ : Measure.IsMultiCoupling γ μ),
        ∫⁻ x, ∑ i, (w i : ℝ≥0∞) * edist (∑ j, (w j : ℝ) • x j) (x i) ^ 2 ∂γ := by
  refine le_antisymm (le_iInf₂ fun γ hγ ↦ ?_) (le_iInf₂ fun ν _ ↦ ?_)
  · exact (iInf₂_le _ (isProbabilityMeasure_map_sum_smul hw hγ)).trans
      (sum_mul_wassersteinEDist_sq_map_le hγ)
  · obtain ⟨γ, hγ, hle⟩ := exists_isMultiCoupling_lintegral_add_wassersteinEDist_sq_le hw μ ν
    exact (iInf₂_le γ hγ).trans (le_self_add.trans hle)

/-- **The weighted mean of an optimal multi-coupling is a barycenter.** For weights summing to
`1`, if a multi-marginal coupling `γ` of the laws `μ i` minimizes the multi-marginal cost
`∫ ∑ i, w i * ‖m x - x i‖ ^ 2 dγ`, then the law of the weighted mean `m x = ∑ j, w j • x j`
under `γ` minimizes the weighted quadratic Wasserstein cost `ν ↦ ∑ i, w i * W₂(ν, μ i) ^ 2` among
probability laws. -/
theorem isMinOn_sum_mul_wassersteinEDist_sq_map (hw : ∑ i, w i = 1) {μ : ι → Measure E}
    [∀ i, IsProbabilityMeasure (μ i)] {γ : Measure (ι → E)} (hγ : Measure.IsMultiCoupling γ μ)
    (hmin : IsMinOn
      (fun γ' ↦ ∫⁻ x, ∑ i, (w i : ℝ≥0∞) * edist (∑ j, (w j : ℝ) • x j) (x i) ^ 2 ∂γ')
      {γ' | Measure.IsMultiCoupling γ' μ} γ) :
    IsMinOn (fun ν ↦ ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 ν (μ i) ^ 2)
      {ν | IsProbabilityMeasure ν} (γ.map fun x ↦ ∑ j, (w j : ℝ) • x j) := by
  intro ν (hν : IsProbabilityMeasure ν)
  obtain ⟨γ', hγ', hle⟩ := exists_isMultiCoupling_lintegral_add_wassersteinEDist_sq_le hw μ ν
  exact (sum_mul_wassersteinEDist_sq_map_le hγ).trans
    ((isMinOn_iff.1 hmin γ' hγ').trans (le_self_add.trans hle))

/-- **A barycenter of finite cost is the weighted mean of an optimal multi-coupling.** For weights
summing to `1`, if a probability law `ν` minimizes the weighted quadratic Wasserstein cost
`∑ i, w i * W₂(ν, μ i) ^ 2` among probability laws, and that minimum is finite, then `ν` is the
law of the weighted mean `m x = ∑ j, w j • x j` under some multi-marginal coupling `γ` of the laws
`μ i` that minimizes the multi-marginal cost `∫ ∑ i, w i * ‖m x - x i‖ ^ 2 dγ`. -/
theorem exists_isMinOn_lintegral_map_eq (hw : ∑ i, w i = 1) {μ : ι → Measure E}
    [∀ i, IsProbabilityMeasure (μ i)] {ν : Measure E} [IsProbabilityMeasure ν]
    (hν : IsMinOn (fun ν' ↦ ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 ν' (μ i) ^ 2)
      {ν' | IsProbabilityMeasure ν'} ν)
    (hfin : ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 ν (μ i) ^ 2 ≠ ∞) :
    ∃ γ : Measure (ι → E), Measure.IsMultiCoupling γ μ ∧
      IsMinOn
        (fun γ' ↦ ∫⁻ x, ∑ i, (w i : ℝ≥0∞) * edist (∑ j, (w j : ℝ) • x j) (x i) ^ 2 ∂γ')
        {γ' | Measure.IsMultiCoupling γ' μ} γ ∧
      γ.map (fun x ↦ ∑ j, (w j : ℝ) • x j) = ν := by
  obtain ⟨γ, hγ, hle⟩ := exists_isMultiCoupling_lintegral_add_wassersteinEDist_sq_le hw μ ν
  set c := ∫⁻ x, ∑ i, (w i : ℝ≥0∞) * edist (∑ j, (w j : ℝ) • x j) (x i) ^ 2 ∂γ
  -- The cost of `ν` is at most that of the weighted mean of `γ`, which is at most `c`.
  have hνc : ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 ν (μ i) ^ 2 ≤ c :=
    (isMinOn_iff.1 hν _ (isProbabilityMeasure_map_sum_smul hw hγ)).trans
      (sum_mul_wassersteinEDist_sq_map_le hγ)
  have hcfin : c ≠ ∞ := ne_top_of_le_ne_top hfin (le_self_add.trans hle)
  refine ⟨γ, hγ, fun γ' (hγ' : Measure.IsMultiCoupling γ' μ) ↦ ?_, ?_⟩
  · exact (le_self_add.trans hle).trans ((isMinOn_iff.1 hν _
      (isProbabilityMeasure_map_sum_smul hw hγ')).trans (sum_mul_wassersteinEDist_sq_map_le hγ'))
  · -- Squeezing `c + W₂(ν, γ.map m) ^ 2 ≤ c` forces `W₂(ν, γ.map m) = 0`.
    have h0 : wassersteinEDist 2 ν (γ.map fun x ↦ ∑ j, (w j : ℝ) • x j) ^ 2 = 0 := by
      refine nonpos_iff_eq_zero.1 (ENNReal.le_of_add_le_add_left hcfin ?_)
      rw [add_zero]
      exact hle.trans hνc
    exact (eq_of_wassersteinEDist_eq_zero two_ne_zero ν _
      (pow_eq_zero_iff two_ne_zero |>.1 h0)).symm

/-! ### Barycenters in `P₂ (E)` -/

/-- **Quadratic Wasserstein barycenters are weighted means of optimal multi-couplings.** For
weights summing to `1` and laws `μ i` of finite second moment, a law `ν` of finite second moment
is a quadratic Fréchet barycenter in `P₂ (E)` of the finitely supported law `∑ i, w i • δ_{μ i}`
exactly when it is the law of the weighted mean `m x = ∑ j, w j • x j` under a multi-marginal
coupling `γ` of the laws `μ i` minimizing the multi-marginal cost `∫ ∑ i, w i * ‖m x - x i‖ ^ 2 dγ`.
-/
theorem isFrechetBarycenter_two_iff_exists_isMinOn_lintegral_map_eq (hw : ∑ i, w i = 1)
    (μ : ι → WassersteinSpace 2 E) (ν : WassersteinSpace 2 E) :
    IsFrechetBarycenter 2 (∑ i, w i • Measure.dirac (μ i)) ν ↔
      ∃ γ : Measure (ι → E),
        Measure.IsMultiCoupling γ (fun i ↦ ((μ i : ProbabilityMeasure E) : Measure E)) ∧
        IsMinOn
          (fun γ' ↦ ∫⁻ x, ∑ i, (w i : ℝ≥0∞) * edist (∑ j, (w j : ℝ) • x j) (x i) ^ 2 ∂γ')
          {γ' | Measure.IsMultiCoupling γ' (fun i ↦ ((μ i : ProbabilityMeasure E) : Measure E))}
          γ ∧
        γ.map (fun x ↦ ∑ j, (w j : ℝ) • x j) = ((ν : ProbabilityMeasure E) : Measure E) := by
  refine ⟨fun h ↦ ?_, fun ⟨γ, hγ, hmin, hγν⟩ ↦ ?_⟩
  · have hfin := WassersteinSpace.sum_mul_wassersteinEDist_rpow_ne_top (w := w) μ ν
    have hmin := WassersteinSpace.isMinOn_sum_mul_wassersteinEDist_rpow_of_isFrechetBarycenter
      ENNReal.ofNat_ne_top hw h
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] at hfin hmin
    exact exists_isMinOn_lintegral_map_eq hw hmin hfin
  · rw [WassersteinSpace.isFrechetBarycenter_sum_smul_dirac_iff_isMinOn ENNReal.ofNat_ne_top μ ν,
      isMinOn_univ_iff]
    intro z
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
    have hmin' := isMinOn_sum_mul_wassersteinEDist_sq_map hw hγ hmin
    rw [hγν] at hmin'
    exact isMinOn_iff.1 hmin' ((z : ProbabilityMeasure E) : Measure E)
      (inferInstance : IsProbabilityMeasure ((z : ProbabilityMeasure E) : Measure E))

/-! ### Barycenters in proper metric spaces

For a general exponent and a general metric space the weighted mean is replaced by a pointwise
barycenter: the multi-marginal cost of a configuration `x : J → X` is the least value
`inf_z ∑ j, w j * d(z, x j) ^ p` of the Fréchet power functional of the weighted law
`∑ j, w j • δ_{x j}`, and a barycenter of the laws `μ j` is the law of a measurable choice of its
minimizers under an optimal multi-coupling. -/

section Polish

variable {J X : Type*} [Fintype J] [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X] {w : J → ℝ≥0} {p : ℝ≥0∞}

/-- **Every law is dominated by a multi-coupling.** On a Polish metric space, for every
probability law `ν` there is a multi-marginal coupling `γ` of the laws `μ j` whose multi-marginal
cost `∫ inf_z ∑ j, w j * d(z, x j) ^ p dγ` is at most the weighted `p`-Wasserstein cost
`∑ j, w j * W_p(ν, μ j) ^ p` of `ν`. The coupling glues optimal plans from `ν` to each `μ j`
along `ν`, and the infimum is bounded by its value at the glued `ν`-coordinate. -/
theorem exists_isMultiCoupling_lintegral_iInf_le (hp0 : p ≠ 0) (hp : p ≠ ∞) (μ : J → Measure X)
    [∀ j, IsProbabilityMeasure (μ j)] (ν : Measure X) [IsProbabilityMeasure ν] :
    ∃ γ : Measure (J → X), Measure.IsMultiCoupling γ μ ∧
      ∫⁻ x, ⨅ z, ∑ j, (w j : ℝ≥0∞) * edist z (x j) ^ p.toReal ∂γ ≤
        ∑ j, (w j : ℝ≥0∞) * wassersteinEDist p ν (μ j) ^ p.toReal := by
  -- Optimal plans from `ν` to each `μ j`, glued along their common first marginal `ν`; the
  -- `p`-th power of `W_p(ν, μ j)` is the cost of the `j`th glued pair.
  obtain ⟨Γ, -, hΓ, hW⟩ := exists_glue_wassersteinEDist_rpow_eq hp0 hp μ ν
  refine ⟨Γ.snd, hΓ, ?_⟩
  have hm (j : J) : Measurable fun q : X × (J → X) ↦ edist q.1 (q.2 j) ^ p.toReal :=
    by fun_prop
  simp only [hW, ← lintegral_const_mul _ (hm _)]
  rw [← lintegral_finsetSum _ fun j _ ↦ (hm j).const_mul _]
  calc ∫⁻ x, ⨅ z, ∑ j, (w j : ℝ≥0∞) * edist z (x j) ^ p.toReal ∂Γ.snd
      ≤ ∫⁻ q, ⨅ z, ∑ j, (w j : ℝ≥0∞) * edist z (q.2 j) ^ p.toReal ∂Γ :=
        lintegral_map_le _ measurable_snd.aemeasurable
    _ ≤ ∫⁻ q, ∑ j, (w j : ℝ≥0∞) * edist q.1 (q.2 j) ^ p.toReal ∂Γ :=
        lintegral_mono fun q ↦ iInf_le _ q.1

/-- **A measurable choice of barycenters of an optimal multi-coupling is a barycenter.** On a
Polish metric space, let `γ` be a multi-marginal coupling of the laws `μ j` minimizing the
multi-marginal cost `∫ inf_z ∑ j, w j * d(z, x j) ^ p dγ`, and let `T : (J → X) → X` be a
measurable map sending each configuration `x` to a `p`-Fréchet barycenter of
`∑ j, w j • δ_{x j}`. Then the law of `T` under `γ` minimizes the weighted `p`-Wasserstein cost
`ν ↦ ∑ j, w j * W_p(ν, μ j) ^ p` among probability laws. -/
theorem isMinOn_sum_mul_wassersteinEDist_rpow_map (hp0 : p ≠ 0) (hp : p ≠ ∞)
    {μ : J → Measure X} [∀ j, IsProbabilityMeasure (μ j)] {γ : Measure (J → X)}
    (hγ : Measure.IsMultiCoupling γ μ)
    (hmin : IsMinOn (fun γ' ↦ ∫⁻ x, ⨅ z, ∑ j, (w j : ℝ≥0∞) * edist z (x j) ^ p.toReal ∂γ')
      {γ' | Measure.IsMultiCoupling γ' μ} γ)
    {T : (J → X) → X} (hT : Measurable T)
    (hTb : ∀ x, IsFrechetBarycenter p (∑ j, w j • Measure.dirac (x j)) (T x)) :
    IsMinOn (fun ν ↦ ∑ j, (w j : ℝ≥0∞) * wassersteinEDist p ν (μ j) ^ p.toReal)
      {ν | IsProbabilityMeasure ν} (γ.map T) := by
  intro ν (hν : IsProbabilityMeasure ν)
  obtain ⟨γ', hγ', hle⟩ := exists_isMultiCoupling_lintegral_iInf_le (w := w) hp0 hp μ ν
  refine (sum_mul_wassersteinEDist_rpow_map_le measurable_edist hp0 hp hγ hT).trans ?_
  simp only [(hTb _).sum_mul_edist_rpow_eq_iInf hp0 hp]
  exact (isMinOn_iff.1 hmin γ' hγ').trans hle

/-- **The multi-marginal problem has a solution.** On a Polish metric space, for `1 ≤ p < ∞` and
weights summing to `1`, some multi-marginal coupling of the laws `μ j` minimizes the
multi-marginal cost `∫ inf_z ∑ j, w j * d(z, x j) ^ p dγ`. The cost is continuous by
`TauCeti.continuous_iInf_frechetPower_sum_smul_dirac`, so this is an instance of
`TauCeti.exists_isMultiCoupling_isMinOn_lintegral`. -/
theorem exists_isMultiCoupling_isMinOn_lintegral_iInf (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hw : ∑ j, w j = 1) (μ : J → Measure X) [∀ j, IsProbabilityMeasure (μ j)] :
    ∃ γ : Measure (J → X), Measure.IsMultiCoupling γ μ ∧
      IsMinOn (fun γ' ↦ ∫⁻ x, ⨅ z, ∑ j, (w j : ℝ≥0∞) * edist z (x j) ^ p.toReal ∂γ')
        {γ' | Measure.IsMultiCoupling γ' μ} γ := by
  have : Nonempty J := by
    by_contra hJ
    simp [not_nonempty_iff.1 hJ] at hw
  have hc := continuous_iInf_frechetPower_sum_smul_dirac (X := X) hp hp_top hw
  simp only [frechetPower_sum_smul_dirac, ENNReal.smul_def, smul_eq_mul] at hc
  exact exists_isMultiCoupling_isMinOn_lintegral (fun _ ↦ isTightMeasureSet_singleton)
    hc.lowerSemicontinuous

end Polish

section Proper

variable {J X : Type*} [Fintype J] [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {w : J → ℝ≥0} {p : ℝ≥0∞}

/-- **The barycentric and multi-marginal problems have the same value.** On a proper metric
space, for `1 ≤ p < ∞` and weights summing to `1`, the infimum over probability laws `ν` of the
weighted `p`-Wasserstein cost `∑ j, w j * W_p(ν, μ j) ^ p` equals the infimum over multi-marginal
couplings `γ` of the laws `μ j` of the multi-marginal cost `∫ inf_z ∑ j, w j * d(z, x j) ^ p dγ`.
-/
theorem iInf_sum_mul_wassersteinEDist_rpow_eq (hp : 1 ≤ p) (hp_top : p ≠ ∞) (hw : ∑ j, w j = 1)
    (μ : J → Measure X) [∀ j, IsProbabilityMeasure (μ j)] :
    ⨅ (ν : Measure X) (_ : IsProbabilityMeasure ν),
        ∑ j, (w j : ℝ≥0∞) * wassersteinEDist p ν (μ j) ^ p.toReal =
      ⨅ (γ : Measure (J → X)) (_ : Measure.IsMultiCoupling γ μ),
        ∫⁻ x, ⨅ z, ∑ j, (w j : ℝ≥0∞) * edist z (x j) ^ p.toReal ∂γ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  obtain ⟨j₀, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hw.trans_ne one_ne_zero)
  obtain ⟨T, hT, hTb⟩ := exists_measurable_isFrechetBarycenter_sum_smul_dirac (X := X) hp hp_top hw
  refine le_antisymm (le_iInf₂ fun γ hγ ↦ ?_) (le_iInf₂ fun ν _ ↦ ?_)
  · have := hγ.isProbabilityMeasure j₀
    refine (iInf₂_le (γ.map T) (inferInstance : IsProbabilityMeasure (γ.map T))).trans ?_
    refine (sum_mul_wassersteinEDist_rpow_map_le measurable_edist hp0 hp_top hγ hT).trans_eq ?_
    simp only [(hTb _).sum_mul_edist_rpow_eq_iInf hp0 hp_top]
  · obtain ⟨γ, hγ, hle⟩ := exists_isMultiCoupling_lintegral_iInf_le (w := w) hp0 hp_top μ ν
    exact (iInf₂_le γ hγ).trans hle

/-- **Existence of Wasserstein barycenters of finitely many laws** (Le Gouic–Loubes). On a proper
metric space, for `1 ≤ p < ∞` and weights summing to `1`, every finitely supported law
`∑ j, w j • δ_{μ j}` on the Wasserstein space `P_p(X)` has a `p`-Fréchet barycenter in `P_p(X)`.
By `TauCeti.isMinOn_sum_mul_wassersteinEDist_rpow_map`, one is the law of a measurable choice of
pointwise barycenters under an optimal multi-coupling of the laws `μ j`. -/
theorem WassersteinSpace.exists_isFrechetBarycenter_sum_smul_dirac [Fact (1 ≤ p)]
    (hp_top : p ≠ ∞) (hw : ∑ j, w j = 1) (μ : J → WassersteinSpace p X) :
    ∃ ν : WassersteinSpace p X, IsFrechetBarycenter p (∑ j, w j • Measure.dirac (μ j)) ν := by
  have hp : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  set μ' := fun j ↦ ((μ j : ProbabilityMeasure X) : Measure X)
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hw.trans_ne one_ne_zero)
  obtain ⟨T, hT, hTb⟩ := exists_measurable_isFrechetBarycenter_sum_smul_dirac (X := X) hp hp_top hw
  obtain ⟨γ, hγ, hmin⟩ := exists_isMultiCoupling_isMinOn_lintegral_iInf hp hp_top hw μ'
  have := hγ.isProbabilityMeasure j₀
  have hν₀ : IsProbabilityMeasure (γ.map T) := inferInstance
  have hνmin := isMinOn_sum_mul_wassersteinEDist_rpow_map hp0 hp_top hγ hmin hT hTb
  -- The law of `T` under `γ` costs no more than `μ j₀`, so it has finite `p`-th moment.
  have hmom : HasFiniteMoment p (γ.map T) :=
    hasFiniteMoment_of_sum_mul_wassersteinEDist_rpow_ne_top measurable_edist (Finset.mem_univ j₀)
      (ENNReal.coe_ne_zero.2 hj₀) (μ j₀).hasFiniteMoment (ENNReal.toReal_pos hp0 hp_top)
      (ne_top_of_le_ne_top (WassersteinSpace.sum_mul_wassersteinEDist_rpow_ne_top μ (μ j₀))
        (isMinOn_iff.1 hνmin (μ' j₀) (inferInstance : IsProbabilityMeasure (μ' j₀))))
  set ν := WassersteinSpace.mk ⟨γ.map T, hν₀⟩ hmom
  have hνc : ((ν : ProbabilityMeasure X) : Measure X) = γ.map T :=
    congrArg ProbabilityMeasure.toMeasure (WassersteinSpace.coe_mk _ _)
  refine ⟨ν, (WassersteinSpace.isFrechetBarycenter_sum_smul_dirac_iff_isMinOn hp_top μ ν).2
    (isMinOn_iff.2 fun z _ ↦ ?_)⟩
  simp only [hνc]
  exact isMinOn_iff.1 hνmin _
    (inferInstance : IsProbabilityMeasure ((z : ProbabilityMeasure X) : Measure X))

/-- **Every Wasserstein barycenter is a mixture of pointwise barycenters.** On a proper metric
space, for `1 ≤ p < ∞` and weights summing to `1`, let `ν` be a `p`-Fréchet barycenter in `P_p(X)`
of the finitely supported law `∑ j, w j • δ_{μ j}`. Then `ν` is the first marginal of a joint law
`Γ` of a point and a configuration, whose second marginal is a multi-coupling of the laws `μ j`,
such that for `Γ`-almost every pair `(y, x)` the point `y` is a `p`-Fréchet barycenter of the
weighted law `∑ j, w j • δ_{x j}`. -/
theorem WassersteinSpace.exists_ae_isFrechetBarycenter_sum_smul_dirac [Fact (1 ≤ p)]
    (hp_top : p ≠ ∞) (hw : ∑ j, w j = 1) {μ : J → WassersteinSpace p X}
    {ν : WassersteinSpace p X} (hν : IsFrechetBarycenter p (∑ j, w j • Measure.dirac (μ j)) ν) :
    ∃ Γ : Measure (X × (J → X)), Γ.fst = ((ν : ProbabilityMeasure X) : Measure X) ∧
      Measure.IsMultiCoupling Γ.snd (fun j ↦ ((μ j : ProbabilityMeasure X) : Measure X)) ∧
      ∀ᵐ q ∂Γ, IsFrechetBarycenter p (∑ j, w j • Measure.dirac (q.2 j)) q.1 := by
  have hp : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  set μ' := fun j ↦ ((μ j : ProbabilityMeasure X) : Measure X)
  obtain ⟨Γ, hΓfst, hΓ, hW⟩ :=
    exists_glue_wassersteinEDist_rpow_eq hp0 hp_top μ' ((ν : ProbabilityMeasure X) : Measure X)
  refine ⟨Γ, hΓfst, hΓ, ?_⟩
  -- `f q` is the weighted cost of the point `q.1` against the configuration `q.2`, and `c q.2` is
  -- its least value over all points.
  set f : X × (J → X) → ℝ≥0∞ := fun q ↦ ∑ j, (w j : ℝ≥0∞) * edist q.1 (q.2 j) ^ p.toReal
  set c : (J → X) → ℝ≥0∞ := fun x ↦ ⨅ z, ∑ j, (w j : ℝ≥0∞) * edist z (x j) ^ p.toReal
  have hc : Continuous c := by
    have := continuous_iInf_frechetPower_sum_smul_dirac (X := X) hp hp_top hw
    simpa only [frechetPower_sum_smul_dirac, ENNReal.smul_def, smul_eq_mul] using this
  have hm (j : J) : Measurable fun q : X × (J → X) ↦ edist q.1 (q.2 j) ^ p.toReal := by
    fun_prop
  have hf : Measurable f := Finset.measurable_sum _ fun j _ ↦ (hm j).const_mul _
  have hcf (q : X × (J → X)) : c q.2 ≤ f q := iInf_le _ q.1
  -- The weighted cost of `Γ` is the barycentric cost of `ν`, which is finite.
  have hΓf : ∫⁻ q, f q ∂Γ = ∑ j, (w j : ℝ≥0∞) *
      wassersteinEDist p ((ν : ProbabilityMeasure X) : Measure X) (μ' j) ^ p.toReal := by
    simp only [f, hW, ← lintegral_const_mul _ (hm _)]
    exact lintegral_finsetSum _ fun j _ ↦ (hm j).const_mul _
  have hfin : ∫⁻ q, f q ∂Γ ≠ ∞ := hΓf ▸ WassersteinSpace.sum_mul_wassersteinEDist_rpow_ne_top μ ν
  -- That cost is at most the least multi-marginal cost, attained here by the law of `q.2`.
  have hle : ∫⁻ q, f q ∂Γ ≤ ∫⁻ q, c q.2 ∂Γ := by
    have hmin := WassersteinSpace.isMinOn_sum_mul_wassersteinEDist_rpow_of_isFrechetBarycenter
      hp_top hw hν
    rw [hΓf, ← lintegral_map hc.measurable measurable_snd]
    refine le_trans ?_ (iInf₂_le (f := fun (γ : Measure (J → X))
      (_ : Measure.IsMultiCoupling γ μ') ↦ ∫⁻ x, c x ∂γ) Γ.snd hΓ)
    rw [← iInf_sum_mul_wassersteinEDist_rpow_eq hp hp_top hw μ']
    exact le_iInf₂ fun ν' hν' ↦ isMinOn_iff.1 hmin ν' hν'
  -- Hence the weighted cost of `q.1` equals its least value almost everywhere.
  have hae : (fun q ↦ c q.2) =ᵐ[Γ] f :=
    ae_eq_of_ae_le_of_lintegral_le (.of_forall hcf) (ne_top_of_le_ne_top hfin
      (lintegral_mono hcf)) hf.aemeasurable hle
  filter_upwards [hae] with q hq
  exact (isFrechetBarycenter_sum_smul_dirac_iff hp0 hp_top).2 hq.symm

end Proper

end TauCeti
