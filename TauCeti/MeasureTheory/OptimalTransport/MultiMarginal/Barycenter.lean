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
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Borel

/-!
# Quadratic Wasserstein barycenters as a multi-marginal problem

Let `E` be a real inner product space, `μ i` finitely many probability laws on `E` and `w i`
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
`∫ ∑ i, w i * ‖m x - x i‖ ^ 2 dγ`. This needs neither an inner product nor normalized weights. -/
theorem sum_mul_wassersteinEDist_sq_map_le {μ : ι → Measure E} {γ : Measure (ι → E)}
    (hγ : Measure.IsMultiCoupling γ μ) :
    ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 (γ.map fun x ↦ ∑ j, (w j : ℝ) • x j) (μ i) ^ 2 ≤
      ∫⁻ x, ∑ i, (w i : ℝ≥0∞) * edist (∑ j, (w j : ℝ) • x j) (x i) ^ 2 ∂γ := by
  have hm : Measurable fun x : ι → E ↦ ∑ j, (w j : ℝ) • x j := by fun_prop
  rw [lintegral_finsetSum _ fun i _ ↦ by fun_prop]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [lintegral_const_mul _ (by fun_prop)]
  refine mul_le_mul_right ?_ _
  -- The law of `(m x, x i)` under `γ` couples the law of `m x` with `μ i`.
  have hc : IsCoupling (γ.map fun x ↦ (∑ j, (w j : ℝ) • x j, x i))
      (γ.map fun x ↦ ∑ j, (w j : ℝ) • x j) (μ i) :=
    ⟨Measure.fst_map_prodMk hm (measurable_pi_apply i),
      (Measure.snd_map_prodMk hm (measurable_pi_apply i)).trans (hγ.marginal_eq i)⟩
  have h := wassersteinEDist_rpow_le_lintegral measurable_edist two_ne_zero
    ENNReal.ofNat_ne_top hc
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] at h
  refine h.trans_eq ?_
  rw [lintegral_map (by fun_prop) (by fun_prop)]

end NormedSpace

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
  -- Optimal plans from `ν` to each `μ i`, glued along their common first marginal `ν`.
  choose π hπ hπW using fun i ↦ exists_isCoupling_eLpNorm_eq_wassersteinEDist two_ne_zero
    ENNReal.ofNat_ne_top ν (μ i) ⟨_, isCoupling_prod ν (μ i)⟩
  obtain ⟨Γ, hΓfst, hΓ⟩ := Measure.exists_glue_pi_of_fst_eq fun i ↦ (hπ i).fst_eq
  have he (i : ι) : Measurable (Prod.map (id : E → E) (Function.eval i : (ι → E) → E)) :=
    measurable_id.prodMap (measurable_pi_apply i)
  have hΓi (i : ι) : Γ.snd.map (Function.eval i) = (π i).snd := by
    rw [← hΓ i, Measure.snd, Measure.snd, Measure.map_map (measurable_pi_apply i) measurable_snd,
      Measure.map_map measurable_snd (he i)]
    rfl
  refine ⟨Γ.snd, ⟨fun i ↦ (hΓi i).trans (hπ i).snd_eq⟩, ?_⟩
  -- The squared distance from `ν` to `μ i` is the quadratic cost of the `i`th glued pair.
  have hW (i : ι) : wassersteinEDist 2 ν (μ i) ^ 2 = ∫⁻ q, edist q.1 (q.2 i) ^ 2 ∂Γ := by
    have h := eLpNorm_rpow_eq_lintegral two_ne_zero ENNReal.ofNat_ne_top
      (measurable_edist (α := E)).aemeasurable (μ := π i)
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, hπW i] at h
    rw [h, ← hΓ i, lintegral_map (by fun_prop) (he i)]
    rfl
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
  have := WassersteinSpace.borelSpace (X := E) (p := 2) ENNReal.ofNat_ne_top
  set μ' := fun i ↦ ((μ i : ProbabilityMeasure E) : Measure E)
  set P := ∑ i, w i • Measure.dirac (μ i)
  have hd : Measurable fun z : E × E ↦ edist z.1 z.2 := measurable_edist
  have hm (z : WassersteinSpace 2 E) : AEMeasurable (fun y ↦ edist z y) P :=
    (continuous_const.edist continuous_id).measurable.aemeasurable
  have hF (z : WassersteinSpace 2 E) : frechetPower 2 P z =
      ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 (z : ProbabilityMeasure E) (μ' i) ^ 2 := by
    simp only [P, μ', frechetPower_sum_smul_dirac, WassersteinSpace.edist_def, ENNReal.smul_def,
      smul_eq_mul, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  have hfinF (z : WassersteinSpace 2 E) : frechetPower 2 P z ≠ ∞ := by
    rw [hF]
    exact ENNReal.sum_ne_top.2 fun i _ ↦ ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.pow_ne_top (WassersteinSpace.wassersteinEDist_ne_top hd _ _))
  have hR : frechetRadius 2 P ν ≠ ∞ := by
    intro h
    have := frechetRadius_rpow_eq_frechetPower two_ne_zero ENNReal.ofNat_ne_top (hm ν)
    rw [h, ENNReal.top_rpow_of_pos (by simp)] at this
    exact hfinF ν this.symm
  rw [isFrechetBarycenter_iff_forall_frechetPower_le two_ne_zero ENNReal.ofNat_ne_top (hm ν) hm,
    and_iff_right hR]
  simp only [hF]
  refine ⟨fun h ↦ ?_, fun ⟨γ, hγ, hmin, hγν⟩ z ↦ ?_⟩
  · -- A competitor of finite cost has finite second moment, so it is a point of `P₂ (E)`.
    refine exists_isMinOn_lintegral_map_eq hw
      (isMinOn_iff.2 fun ν' (hν' : IsProbabilityMeasure ν') ↦ ?_) (by simpa only [hF] using hfinF ν)
    by_cases htop : ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 ν' (μ' i) ^ 2 = ∞
    · exact htop ▸ le_top
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hw.trans_ne one_ne_zero)
    have hmom := hasFiniteMoment_of_sum_mul_wassersteinEDist_pow_ne_top hd (Finset.mem_univ i₀)
      (ENNReal.coe_ne_zero.2 hi₀) (μ i₀).hasFiniteMoment two_ne_zero htop
    have hc : ((WassersteinSpace.mk ⟨ν', hν'⟩ hmom : ProbabilityMeasure E) : Measure E) = ν' :=
      congrArg ProbabilityMeasure.toMeasure (WassersteinSpace.coe_mk _ _)
    have hz := h (WassersteinSpace.mk ⟨ν', hν'⟩ hmom)
    rwa [hc] at hz
  · have hmin' := isMinOn_sum_mul_wassersteinEDist_sq_map hw hγ hmin
    rw [hγν] at hmin'
    exact isMinOn_iff.1 hmin' ((z : ProbabilityMeasure E) : Measure E)
      (inferInstance : IsProbabilityMeasure ((z : ProbabilityMeasure E) : Measure E))

end TauCeti
