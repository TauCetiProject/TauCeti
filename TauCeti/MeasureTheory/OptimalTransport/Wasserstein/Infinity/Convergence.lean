/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Infinity.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space

/-!
# Convergence in the infinite-exponent Wasserstein distance

On a Polish metric space, convergence in `W_∞` is exactly convergence through couplings whose
essential-supremum displacements tend to zero. More precisely, for a filtered family of probability
measures `μᵢ` and a probability measure `μ`, the following are equivalent:

* `W_∞(μᵢ, μ) → 0`;
* there are couplings `πᵢ` of `μᵢ` and `μ` for which
  `‖(x, y) ↦ edist x y‖_{L^∞(πᵢ)} → 0`.

The forward implication uses attainment of the `W_∞` infimum, while the reverse implication is
the defining infimum bound. The result is stated first for bundled probability measures at the raw
distance level and then as the convergence criterion for an arbitrary anchored finite-`W_∞`
component. The latter is the topological form: it characterizes convergence in the component's
Wasserstein metric by a family of transport plans.

## Main statements

* `TauCeti.tendsto_wassersteinEDist_top_iff_exists_couplings` characterizes convergence of the raw
  `W_∞` values by coupling-wise essential-supremum displacement;
* `TauCeti.WassersteinComponent.tendsto_iff_exists_couplings_eLpNorm_top` gives the corresponding
  characterization of convergence in every anchored finite-`W_∞` component;
* `TauCeti.WassersteinSpace.tendsto_iff_exists_couplings_eLpNorm_top` specializes it to probability
  measures at essentially bounded distance from a basepoint.

## References

* C. R. Givens and R. M. Shortt, *A class of Wasserstein metrics for probability distributions*,
  Michigan Math. J. 31 (1984), 231–240, Proposition 1, for attainment of `W_∞` on Polish spaces.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace TauCeti

universe u v

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X]

/-- **Coupling characterization of `W_∞` convergence.** A filtered family of probability
measures has `W_∞` distance to `ν` tending to zero if and only if one can choose a coupling at
each index whose essential-supremum displacement tends to zero.

The selected couplings in the forward direction attain `W_∞` exactly. No bounded-support or
finite-moment hypothesis is needed: convergence to zero itself eventually supplies finite
distance, while attainment is valid even when the value at some indices is infinite. -/
theorem tendsto_wassersteinEDist_top_iff_exists_couplings
    {I : Type v} {l : Filter I} {mus : I → ProbabilityMeasure X}
    {nu : ProbabilityMeasure X} :
    Tendsto (fun i ↦ wassersteinEDist ∞ (mus i : Measure X) (nu : Measure X)) l (nhds 0) ↔
      ∃ pis : I → Measure (X × X),
        (∀ i, IsCoupling (pis i) (mus i : Measure X) (nu : Measure X)) ∧
          Tendsto (fun i ↦ eLpNorm (fun z : X × X ↦ edist z.1 z.2) ∞ (pis i)) l (nhds 0) := by
  constructor
  · intro h
    have hopt : ∀ i, ∃ pi, IsCoupling pi (mus i : Measure X) (nu : Measure X) ∧
        eLpNorm (fun z : X × X ↦ edist z.1 z.2) ∞ pi =
          wassersteinEDist ∞ (mus i : Measure X) (nu : Measure X) := by
      intro i
      exact exists_isCoupling_eLpNorm_top_eq_wassersteinEDist (mus i : Measure X) (nu : Measure X)
        ⟨(mus i : Measure X).prod (nu : Measure X),
          isCoupling_prod (mus i : Measure X) (nu : Measure X)⟩
    choose pis hpis hval using hopt
    exact ⟨pis, hpis, (tendsto_congr hval).2 h⟩
  · rintro ⟨pis, hpis, hdisp⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdisp
      (Eventually.of_forall fun _ ↦ bot_le)
      (Eventually.of_forall fun i ↦ wassersteinEDist_le (hpis i) ∞)

namespace WassersteinComponent

variable {mu0 : ProbabilityMeasure X}

/-- Convergence in an anchored finite-`W_∞` component is equivalent to the existence of
couplings to the limit whose essential-supremum displacements tend to zero. -/
theorem tendsto_iff_exists_couplings_eLpNorm_top
    {I : Type v} {l : Filter I} {mus : I → WassersteinComponent ∞ mu0}
    {nu : WassersteinComponent ∞ mu0} :
    Tendsto mus l (nhds nu) ↔
      ∃ pis : I → Measure (X × X),
        (∀ i, IsCoupling (pis i)
          (((mus i : WassersteinComponent ∞ mu0) : ProbabilityMeasure X) : Measure X)
          (((nu : WassersteinComponent ∞ mu0) : ProbabilityMeasure X) : Measure X)) ∧
        Tendsto (fun i ↦ eLpNorm (fun z : X × X ↦ edist z.1 z.2) ∞ (pis i)) l (nhds 0) := by
  rw [tendsto_iff_edist_tendsto_0]
  simp only [edist_def]
  exact tendsto_wassersteinEDist_top_iff_exists_couplings
    (mus := fun i ↦ toProbabilityMeasure (mus i)) (nu := toProbabilityMeasure nu)

end WassersteinComponent

namespace WassersteinSpace

/-- Convergence in `P_∞(X)` is equivalent to the existence of couplings to the limit whose
essential-supremum displacements tend to zero. -/
theorem tendsto_iff_exists_couplings_eLpNorm_top
    {I : Type v} {l : Filter I} {mus : I → WassersteinSpace ∞ X}
    {nu : WassersteinSpace ∞ X} :
    Tendsto mus l (nhds nu) ↔
      ∃ pis : I → Measure (X × X),
        (∀ i, IsCoupling (pis i)
          (((mus i : WassersteinSpace ∞ X) : ProbabilityMeasure X) : Measure X)
          (((nu : WassersteinSpace ∞ X) : ProbabilityMeasure X) : Measure X)) ∧
        Tendsto (fun i ↦ eLpNorm (fun z : X × X ↦ edist z.1 z.2) ∞ (pis i)) l (nhds 0) := by
  rw [tendsto_iff_edist_tendsto_0]
  simp only [edist_def]
  exact tendsto_wassersteinEDist_top_iff_exists_couplings
    (mus := fun i ↦ toProbabilityMeasure (mus i)) (nu := toProbabilityMeasure nu)

end WassersteinSpace

end TauCeti
