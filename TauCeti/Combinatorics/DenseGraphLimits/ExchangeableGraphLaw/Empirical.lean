/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Mixture
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Unbiased
public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.HomDensity
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.FiniteGraph.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Empirical mixing measures of an exchangeable graph law

Every exchangeable graph law `L` produces a sequence of candidate mixing measures on the graphon
space over the unit interval: sample an `n`-vertex graph from the level-`n` marginal of `L` and
take the graphon class of its step graphon. This is the *empirical mixing measure*
`empiricalMixing L n`, the pushforward of `L.law n` along `G ↦ ⟦W_G⟧`.

The point of these measures is that they recover the upper masses of `L` in the limit. The
average of `t(F, ·)` against `empiricalMixing L n` is, for positive `n` (or an empty pattern), the
mean ordinary homomorphism density `E[t(F, G)]` of an `L`-sample `G` on `n` vertices. Its injective
counterpart is exact: by consistency of `L`, each of the `(n)_k` vertex embeddings of a `k`-vertex
pattern `F` sees the pattern with probability `upperMass F`, so `E[t₀(F, G)] = upperMass F`
whenever `k ≤ n`. The two densities differ by at most `C(k, 2) / n`, the union bound on
the proportion of non-injective vertex maps, which gives the **collision estimate**
`|∫ t(F, ·) d(empiricalMixing L (n + 1)) - upperMass F| ≤ C(k, 2) / (n + 1)`
and hence convergence of the empirical hom-density averages to the upper masses. Each descended
density `t(F, ·)` is bounded and continuous, so weak convergence carries these averages to any weak
limit point `P` of the empirical mixing measures: the mixture law of `P` then has the upper masses
of `L`, and since upper masses determine an exchangeable graph law, it *is* `L`. This limit
identification is how the Diaconis–Janson representation of exchangeable graph laws by graphon
mixtures is obtained.

## Main definitions

* `TauCeti.DenseGraphLimits.empiricalMixing` — the graphon class of an `n`-vertex sample from an
  exchangeable graph law, as a probability measure on graphon space.

## Main results

* `TauCeti.DenseGraphLimits.integral_homDensityOnSpace_empiricalMixing` — averaging `t(F, ·)`
  against an empirical mixing measure is taking the mean homomorphism
  density of a sample;
* `TauCeti.DenseGraphLimits.abs_integral_homDensityOnSpace_empiricalMixing_sub_le` — the collision
  estimate;
* `TauCeti.DenseGraphLimits.tendsto_integral_homDensityOnSpace_empiricalMixing` — the empirical
  hom-density averages converge to the upper masses;
* `TauCeti.DenseGraphLimits.mixtureExchangeableLaw_eq_of_tendsto_empiricalMixing` — every weak
  limit of the empirical mixing measures along a diverging sequence of sample sizes is a mixing
  measure for the law.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Section 5.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Sections 5.2 and 11.3.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/MixtureExistence.lean`. The
  empirical mixing measures and the collision estimate follow its existence argument.
-/

public section

noncomputable section

open MeasureTheory Filter Topology BoundedContinuousFunction

namespace TauCeti

namespace DenseGraphLimits

variable (L : ExchangeableGraphLaw)

/-- **Empirical mixing measures.** The graphon class of an `n`-vertex sample from an exchangeable
graph law: the pushforward of the level-`n` marginal along `G ↦ ⟦W_G⟧`, where `W_G` is the step
graphon of `G` on the unit interval. -/
def empiricalMixing (n : ℕ) : ProbabilityMeasure GraphonSpaceI :=
  ⟨(L.law n).map fun G => SeparationQuotient.mk (finiteGraphGraphon G),
    inferInstance⟩

/-- The empirical mixing measure is the pushforward of the level-`n` marginal along the graphon
class of the step graphon. -/
@[simp]
theorem toMeasure_empiricalMixing (n : ℕ) :
    (empiricalMixing L n : Measure GraphonSpaceI) =
      (L.law n).map fun G => SeparationQuotient.mk (finiteGraphGraphon G) := (rfl)

/-- Averaging a homomorphism density against an empirical mixing measure is taking the mean
homomorphism density of a sample from the law. Positivity of `n` is needed when `V` is nonempty,
since the finite density of a nonempty pattern in the empty graph is `0`; an empty pattern has
density `1` on both sides. -/
theorem integral_homDensityOnSpace_empiricalMixing {V : Type*} [Fintype V] (F : SimpleGraph V)
    [DecidableRel F.Adj] {n : ℕ} (hn : Nonempty V → 0 < n) :
    ∫ x, homDensityOnSpace F x ∂(empiricalMixing L n : Measure GraphonSpaceI) =
      ∫ G, homDensityFin F G ∂L.law n := by
  rw [toMeasure_empiricalMixing, integral_map Measurable.of_discrete.aemeasurable
    (continuous_homDensityOnSpace F).aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun G => ?_)
  simp only [homDensityOnSpace_mk]
  rcases n.eq_zero_or_pos with rfl | hn
  · -- With no sample vertices the pattern is empty, and both densities are `1`.
    have : IsEmpty V := not_nonempty_iff.mp fun h => (hn h).false
    simp [homDensity_def, homDensityFin_def, Finset.eq_empty_of_isEmpty F.edgeFinset]
  · exact homDensity_finiteGraphGraphon F hn G

/-- **The collision estimate.** Averaging `t(F, ·)` against the empirical mixing measure of an
exchangeable graph law at sample size `n + 1` recovers the upper mass of `F` up to
`C(k, 2) / (n + 1)`, where `k` is the number of vertices of `F`. -/
theorem abs_integral_homDensityOnSpace_empiricalMixing_sub_le (n : ℕ) {k : ℕ}
    (F : SimpleGraph (Fin k)) [DecidableRel F.Adj] :
    |(∫ x, homDensityOnSpace F x ∂(empiricalMixing L (n + 1) : Measure GraphonSpaceI)) -
        L.upperMass F| ≤ (k.choose 2 : ℝ) / (n + 1) := by
  rw [integral_homDensityOnSpace_empiricalMixing L F fun _ => n.succ_pos]
  exact_mod_cast L.abs_integral_homDensityFin_law_sub_upperMass_le F n.succ_pos

/-- The average of `t(F, ·)` against the empirical mixing measures of an exchangeable graph law
converges to the upper mass of `F`. -/
theorem tendsto_integral_homDensityOnSpace_empiricalMixing {k : ℕ} (F : SimpleGraph (Fin k))
    [DecidableRel F.Adj] :
    Tendsto (fun n =>
        ∫ x, homDensityOnSpace F x ∂(empiricalMixing L n : Measure GraphonSpaceI))
      atTop (𝓝 (L.upperMass F)) := by
  refine (tendsto_add_atTop_iff_nat 1).1 ?_
  have hbound : Tendsto (fun n : ℕ => (k.choose 2 : ℝ) / (n + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (k.choose 2 : ℝ)
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _)
    (fun n => ?_) hbound)
  rw [Real.norm_eq_abs]
  exact abs_integral_homDensityOnSpace_empiricalMixing_sub_le L n F

/-- **Limit identification.** A weak limit `P` of the empirical mixing measures of an exchangeable
graph law `L`, along any diverging sequence of sample sizes, is a mixing measure for `L`: the
mixture law of `P` is `L`. -/
theorem mixtureExchangeableLaw_eq_of_tendsto_empiricalMixing {P : ProbabilityMeasure GraphonSpaceI}
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (hconv : Tendsto (fun m => empiricalMixing L (φ m)) atTop (𝓝 P)) :
    mixtureExchangeableLaw P = L := by
  classical
  -- Both upper masses are limits of the empirical averages of `t(F, ·)`: under `P` by weak
  -- convergence, under `L` by the collision estimate.
  refine ExchangeableGraphLaw.ext_upperMass fun k F => ?_
  rw [upperMass_mixtureExchangeableLaw]
  have hP := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hconv (homDensityBCF F)
  simp only [homDensityBCF_apply] at hP
  exact tendsto_nhds_unique hP ((tendsto_integral_homDensityOnSpace_empiricalMixing L F).comp hφ)

end DenseGraphLimits

end TauCeti
