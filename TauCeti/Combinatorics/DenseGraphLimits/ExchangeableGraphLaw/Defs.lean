/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Measurable
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Exchangeable graph laws

An exchangeable random graph on an unbounded label set is presented here by its finite marginals:
a probability law on `SimpleGraph (Fin k)` for every `k`, consistent under pulling a graph back
along every injection of labels `Fin k ↪ Fin l`. Consistency along *all* injections is a single
hypothesis doing two jobs: the permutations of `Fin k` give invariance under relabelling, and the
inclusions `Fin k ↪ Fin (k + 1)` give the projectivity that makes the family the
finite-dimensional distributions of one random graph.

The observable through which a graph parameter reads off such a law is the **upper mass** of a
finite pattern `F`: the probability `P(F ≤ ·)` that the level-`k` sample contains `F`. Upper
masses take values in `[0, 1]`, take the value `1` at the edgeless pattern, and are unchanged by
relabelling a pattern along an injection — the consistency hypothesis seen on upper events.

The label set is always a finite `Fin k`, so its graphs form a finite measurable space and every
set of them is measurable; no measurability side conditions appear below.

## Main definitions

* `TauCeti.DenseGraphLimits.ExchangeableGraphLaw` — a consistent family of finite graph laws, with
  each marginal a probability measure by instance;
* `TauCeti.DenseGraphLimits.ExchangeableGraphLaw.upperMass` — the probability that the sample
  contains a fixed finite pattern.

## Main results

* `TauCeti.DenseGraphLimits.ExchangeableGraphLaw.upperMass_map` — upper masses are unchanged by
  relabelling the pattern along an injection;
* `TauCeti.DenseGraphLimits.ExchangeableGraphLaw.upperMass_bot`,
  `TauCeti.DenseGraphLimits.ExchangeableGraphLaw.upperMass_nonneg` and
  `TauCeti.DenseGraphLimits.ExchangeableGraphLaw.upperMass_le_one` — the range of an upper mass.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Section 5.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0,
  `Graphon/ExchangeableGraphLaw.lean`. The presentation by consistent finite marginals and the
  upper-mass observable follow its formulation.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

/-- An exchangeable random graph presented by its consistent finite marginals: a probability law
on the graphs with labels `Fin k` for every `k`, consistent under pulling back along every
injection of labels. -/
structure ExchangeableGraphLaw where
  /-- The level-`k` marginal law. -/
  law : (k : ℕ) → Measure (SimpleGraph (Fin k))
  /-- Every marginal is a probability measure. -/
  prob : ∀ k, IsProbabilityMeasure (law k)
  /-- Consistency under restriction along every injection of labels. -/
  consistent : ∀ {k l : ℕ} (f : Fin k ↪ Fin l),
    (law l).map (SimpleGraph.comap ⇑f) = law k

namespace ExchangeableGraphLaw

instance instIsProbabilityMeasureLaw (L : ExchangeableGraphLaw) (k : ℕ) :
    IsProbabilityMeasure (L.law k) := L.prob k

variable (L : ExchangeableGraphLaw) {k l : ℕ}

/-- The upper mass of a pattern `F`: the probability that the level-`k` sample contains `F`. -/
def upperMass (F : SimpleGraph (Fin k)) : ℝ := (L.law k {G | F ≤ G}).toReal

/-- The defining probability of an upper mass. -/
theorem upperMass_def (F : SimpleGraph (Fin k)) :
    L.upperMass F = (L.law k {G | F ≤ G}).toReal := (rfl)

/-- An upper mass is nonnegative. -/
theorem upperMass_nonneg (F : SimpleGraph (Fin k)) : 0 ≤ L.upperMass F :=
  ENNReal.toReal_nonneg

/-- An upper mass is at most `1`. -/
theorem upperMass_le_one (F : SimpleGraph (Fin k)) : L.upperMass F ≤ 1 := by
  rw [upperMass_def, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one

/-- Every graph contains the edgeless pattern, so its upper mass is `1`. -/
@[simp]
theorem upperMass_bot : L.upperMass (⊥ : SimpleGraph (Fin k)) = 1 := by
  have hset : {G : SimpleGraph (Fin k) | ⊥ ≤ G} = Set.univ := by simp
  rw [upperMass_def, hset, measure_univ, ENNReal.toReal_one]

/-- Upper masses are unchanged by relabelling the pattern along an injection: the event that the
level-`l` sample contains the relabelled pattern is the event that its restriction to the window
contains the original one. -/
@[simp]
theorem upperMass_map (F : SimpleGraph (Fin k)) (f : Fin k ↪ Fin l) :
    L.upperMass (F.map ⇑f) = L.upperMass F := by
  have hset : {G : SimpleGraph (Fin l) | F.map ⇑f ≤ G} =
      SimpleGraph.comap ⇑f ⁻¹' {H : SimpleGraph (Fin k) | F ≤ H} :=
    Set.ext fun G => SimpleGraph.map_le_iff_le_comap f F G
  rw [upperMass_def, upperMass_def, hset,
    ← Measure.map_apply (SimpleGraph.measurable_comap ⇑f) MeasurableSet.of_discrete,
    L.consistent f]

end ExchangeableGraphLaw

end DenseGraphLimits

end TauCeti
