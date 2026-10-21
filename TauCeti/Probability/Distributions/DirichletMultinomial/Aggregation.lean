/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.DirichletMultinomial.Basic
public import TauCeti.Probability.Distributions.Dirichlet.Aggregation
public import TauCeti.Probability.Distributions.Dirichlet.Marginal
public import TauCeti.Probability.Distributions.Multinomial.Aggregation
public import TauCeti.Probability.Distributions.Multinomial.Marginal
public import TauCeti.Probability.Distributions.BetaBinomial.Basic
import TauCeti.Geometry.Convex.ConvexSpace.Defs

/-!
# Aggregation and marginals of Dirichlet-multinomial laws

Merging categories of a Dirichlet-multinomial count vector again gives a Dirichlet-multinomial
law, with concentrations summed over the same fibres. A coordinate, or the total in a proper
nonempty block of categories, has a beta-binomial law. Surjectivity of the aggregation map
ensures positive target concentrations; the coordinate result requires at least two categories.
The one-category Dirac law is supplied by
`dirichletMultinomialMeasure_eq_dirac_of_subsingleton`.

These identities follow the mixture construction: aggregate both the multinomial counts and
their Dirichlet probabilities, or take their binomial and Beta marginals. They allow count
models to be coarsened without evaluating sums of Gamma-ratio masses.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 40.
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Merging categories along a surjection preserves the Dirichlet-multinomial family and
sums the concentration parameters over each fibre. -/
@[simp]
theorem map_funOnFinite_map_dirichletMultinomialMeasure [Nonempty ι] [Nonempty κ]
    [DecidableEq κ] {f : ι → κ}
    (hf : Function.Surjective f) {a : ι → ℝ} (ha : ∀ i, 0 < a i) (n : ℕ) :
    (dirichletMultinomialMeasure n a).map (FunOnFinite.map (M := ℕ) f) =
      dirichletMultinomialMeasure n (fun j ↦ ∑ i with f i = j, a i) := by
  classical
  let p : EuclideanSpace ℝ ι → StdSimplex ℝ≥0 ι := fun x ↦
    (StdSimplex.single (Classical.arbitrary ι) : StdSimplex ℝ≥0 ι).extendWeights
      (fun i ↦ (x i).toNNReal)
  let q : EuclideanSpace ℝ κ → StdSimplex ℝ≥0 κ := fun x ↦
    (StdSimplex.single (Classical.arbitrary κ) : StdSimplex ℝ≥0 κ).extendWeights
      (fun j ↦ (x j).toNNReal)
  have hp : Measurable p := (StdSimplex.measurable_extendWeights _).comp (by fun_prop)
  have hkernel : Measurable (fun x ↦ multinomialMeasure n (p x)) :=
    measurable_multinomialMeasure.comp (measurable_const.prodMk hp)
  have hq : Measurable q := (StdSimplex.measurable_extendWeights _).comp (by fun_prop)
  have hkernelq : Measurable (fun x ↦ multinomialMeasure n (q x)) :=
    measurable_multinomialMeasure.comp (measurable_const.prodMk hq)
  have hpos (j : κ) : 0 < ∑ i with f i = j, a i := by
    obtain ⟨i, hi⟩ := hf j
    exact Finset.sum_pos (fun k _ ↦ ha k) ⟨i, by simp [hi]⟩
  have hweights : ∀ᵐ x ∂dirichletMeasure a, ∀ i, ((p x).weights i : ℝ) = x i :=
    ae_extendWeights_dirichletMeasure ha (StdSimplex.single (Classical.arbitrary ι))
  have hmerged : ∀ᵐ x ∂dirichletMeasure (fun j ↦ ∑ i with f i = j, a i),
      ∀ j, ((q x).weights j : ℝ) = x j :=
    ae_extendWeights_dirichletMeasure hpos (StdSimplex.single (Classical.arbitrary κ))
  rw [← map_euclideanFiberSum_dirichletMeasure hf ha] at hmerged
  have hmerged' := ae_of_ae_map (measurable_euclideanFiberSum f).aemeasurable hmerged
  rw [dirichletMultinomialMeasure_eq_bind n p hweights,
    Measure.map_bind hkernel.aemeasurable (.of_discrete),
    dirichletMultinomialMeasure_eq_bind n q
      (ae_extendWeights_dirichletMeasure hpos (StdSimplex.single (Classical.arbitrary κ))),
    ← map_euclideanFiberSum_dirichletMeasure hf ha,
    Measure.bind_map (measurable_euclideanFiberSum f).aemeasurable
      hkernelq.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [hweights, hmerged'] with x hx hy
  rw [map_funOnFinite_map_multinomialMeasure]
  congr 1
  apply StdSimplex.ext
  ext j
  rw [StdSimplex.weights_map_apply, NNReal.coe_sum]
  simpa only [hx, euclideanFiberSum_apply] using (hy j).symm

/-- Each coordinate count is beta-binomial, with shapes given by its own concentration and
the total concentration of the other categories. -/
@[simp]
theorem map_eval_dirichletMultinomialMeasure [DecidableEq ι] [Nontrivial ι]
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) (n : ℕ) (i : ι) :
    (dirichletMultinomialMeasure n a).map (fun k ↦ k i) =
      betaBinomialMeasure n (a i) (∑ j with j ≠ i, a j) := by
  classical
  let p : EuclideanSpace ℝ ι → StdSimplex ℝ≥0 ι := fun x ↦
    (StdSimplex.single (Classical.arbitrary ι) : StdSimplex ℝ≥0 ι).extendWeights
      (fun j ↦ (x j).toNNReal)
  have hp : Measurable p := (StdSimplex.measurable_extendWeights _).comp (by fun_prop)
  have hkernel : Measurable (fun x ↦ multinomialMeasure n (p x)) :=
    measurable_multinomialMeasure.comp (measurable_const.prodMk hp)
  have hweights : ∀ᵐ x ∂dirichletMeasure a, ∀ i, ((p x).weights i : ℝ) = x i :=
    ae_extendWeights_dirichletMeasure ha (StdSimplex.single (Classical.arbitrary ι))
  have hrest : 0 < ∑ j with j ≠ i, a j := by
    obtain ⟨j, hj⟩ := exists_ne i
    exact Finset.sum_pos (fun k _ ↦ ha k) ⟨j, by simp [hj]⟩
  rw [dirichletMultinomialMeasure_eq_bind n p hweights,
    Measure.map_bind hkernel.aemeasurable (.of_discrete),
    betaBinomialMeasure_eq_bind (ha i) hrest,
    ← map_eval_dirichletMeasure ha i,
    Measure.bind_map (by fun_prop) (by fun_prop)]
  apply Measure.bind_congr_right
  filter_upwards [hweights] with x hx
  rw [map_eval_multinomialMeasure]
  congr 1
  apply Subtype.ext
  rw [StdSimplex.coe_multinomialCellProbability, ← hx i]
  exact (congrArg Subtype.val (Set.projIcc_of_mem zero_le_one
    ⟨NNReal.coe_nonneg _, by exact_mod_cast (p x).weights_apply_le_one i⟩)).symm

/-- The total count in a nonempty proper block has the beta-binomial law whose shapes are
the total concentrations in the block and in its complement. -/
@[simp]
theorem map_sum_dirichletMultinomialMeasure [Nonempty ι] [DecidableEq ι] {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (n : ℕ) {s : Finset ι} (hs : s.Nonempty) (hsc : sᶜ.Nonempty) :
    (dirichletMultinomialMeasure n a).map (fun k ↦ ∑ i ∈ s, k i) =
      betaBinomialMeasure n (∑ i ∈ s, a i) (∑ i ∈ sᶜ, a i) := by
  classical
  let f : ι → Fin 2 := fun i ↦ if i ∈ s then 0 else 1
  have hf : Function.Surjective f := by
    intro j
    fin_cases j
    · obtain ⟨i, hi⟩ := hs
      exact ⟨i, by simp [f, hi]⟩
    · obtain ⟨i, hi⟩ := hsc
      exact ⟨i, by simpa [f] using hi⟩
  have hpos (j : Fin 2) : 0 < ∑ i with f i = j, a i := by
    obtain ⟨i, hi⟩ := hf j
    exact Finset.sum_pos (fun k _ ↦ ha k) ⟨i, by simp [hi]⟩
  have h := map_eval_dirichletMultinomialMeasure hpos n 0
  rw [← map_funOnFinite_map_dirichletMultinomialMeasure hf ha n,
    Measure.map_map (by fun_prop) (.of_discrete)] at h
  have hcompl : (∑ i, if i ∈ s then (0 : ℝ) else a i) = ∑ i ∈ sᶜ, a i := by
    simpa [Finset.filter_notMem_eq_sdiff, Finset.compl_eq_univ_sdiff] using
      (Finset.sum_filter (s := Finset.univ) (p := fun i ↦ i ∈ sᶜ) (f := a)).symm
  simpa [Function.comp_def, FunOnFinite.map_apply_apply, f, Fin.sum_univ_two,
    Finset.sum_filter, hcompl] using h

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {Ω ι κ : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [Fintype ι] [Fintype κ]

/-- Merging the categories of a Dirichlet-multinomial random count vector adds their
concentrations along the same fibres. -/
theorem funOnFinite_map_dirichletMultinomialMeasure [Nonempty ι] [Nonempty κ]
    [DecidableEq κ] {X : Ω → (ι → ℕ)} {a : ι → ℝ} {n : ℕ}
    (hX : HasLaw X (dirichletMultinomialMeasure n a) P) {f : ι → κ}
    (hf : Function.Surjective f) (ha : ∀ i, 0 < a i) :
    HasLaw (fun ω ↦ FunOnFinite.map (M := ℕ) f (X ω))
      (dirichletMultinomialMeasure n (fun j ↦ ∑ i with f i = j, a i)) P := by
  exact HasLaw.fun_comp
    ⟨.of_discrete, map_funOnFinite_map_dirichletMultinomialMeasure hf ha n⟩ hX

/-- A coordinate of a Dirichlet-multinomial random count vector has the beta-binomial law. -/
theorem eval_dirichletMultinomialMeasure [DecidableEq ι] [Nontrivial ι]
    {X : Ω → (ι → ℕ)} {a : ι → ℝ} {n : ℕ}
    (hX : HasLaw X (dirichletMultinomialMeasure n a) P) (ha : ∀ i, 0 < a i) (i : ι) :
    HasLaw (fun ω ↦ X ω i) (betaBinomialMeasure n (a i) (∑ j with j ≠ i, a j)) P := by
  exact HasLaw.fun_comp ⟨.of_discrete, map_eval_dirichletMultinomialMeasure ha n i⟩ hX

end ProbabilityTheory.HasLaw
