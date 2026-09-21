/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Defs
public import TauCeti.Combinatorics.SimpleGraph.Sum
public import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.MeasureTheory.Measure.FiniteOrder

/-!
# Dissociated exchangeable graph laws

An exchangeable graph law is **dissociated** when the random graph restricted to two disjoint
windows of labels consists of two independent pieces: the level-`(k + l)` marginal, pushed to the
pair of graphs it induces on the first `k` and on the last `l` labels, is the product of the
level-`k` and level-`l` marginals. By exchangeability two disjoint windows of sizes `k` and `l`
can be relabelled as the first `k` and the next `l` labels, and by consistency the labels beyond
them can then be dropped, so the first `k` and the last `l` labels of `Fin (k + l)` suffice.

Dissociation is an identity between two laws on pairs of graphs, while the upper masses of a law
only see its upper events. The two meet in the bridge `isDissociated_iff_upperMass_mul`: a law is
dissociated exactly when its upper masses are multiplicative over disjoint unions of patterns.
One direction reads the multiplicativity off the upper rectangles. The other needs that the upper
rectangles determine a law on pairs of graphs, which is Möbius inversion over the product of the
two finite lattices of graphs — the downward induction of
`MeasureTheory.Measure.ext_of_Ici_of_finite`, since the upper ray at a pair of patterns is the
rectangle of their upper events.

## Main definitions

* `TauCeti.DenseGraphLimits.ExchangeableGraphLaw.IsDissociated` — restrictions to disjoint label
  windows are independent.

## Main results

* `TauCeti.DenseGraphLimits.ExchangeableGraphLaw.isDissociated_iff` — the defining identity of a
  dissociated law;
* `TauCeti.DenseGraphLimits.ExchangeableGraphLaw.upperMass_map_sum` — the upper mass of a disjoint
  union of patterns is the mass of a rectangle under the law of the pair of windows;
* `TauCeti.DenseGraphLimits.isDissociated_iff_upperMass_mul` — a law is dissociated iff its upper
  masses are multiplicative over disjoint unions of patterns.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Section 5.
-/

-- Provenance: the body of `IsDissociated` and the signature of `isDissociated_iff_upperMass_mul`
-- follow `TauCetiRoadmap/DenseGraphLimits/Suggested.lean`.

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

namespace ExchangeableGraphLaw

variable (L : ExchangeableGraphLaw) {k l : ℕ}

/-- A law is **dissociated** when restrictions to disjoint label windows are independent: the
level-`(k + l)` marginal pushed to the pair of windows is the product of the level-`k` and
level-`l` marginals. -/
def IsDissociated : Prop :=
  ∀ k l : ℕ,
    (L.law (k + l)).map
        (fun G => (SimpleGraph.comap (Fin.castAdd l) G, SimpleGraph.comap (Fin.natAdd k) G))
      = (L.law k).prod (L.law l)

/-- The defining identity of a dissociated law: the level-`(k + l)` marginal pushed to the pair of
windows is the product of the level-`k` and level-`l` marginals. -/
@[simp]
theorem isDissociated_iff :
    L.IsDissociated ↔
      ∀ k l : ℕ,
        (L.law (k + l)).map
            (fun G => (SimpleGraph.comap (Fin.castAdd l) G, SimpleGraph.comap (Fin.natAdd k) G))
          = (L.law k).prod (L.law l) := (Iff.rfl)

/-- The upper mass of a disjoint union of two patterns, placed on the first `k` and the last `l`
labels, is the mass of the rectangle of their two upper events under the law of the pair of
windows: a graph contains the union exactly when its two windows contain the two patterns. -/
theorem upperMass_map_sum (F₁ : SimpleGraph (Fin k)) (F₂ : SimpleGraph (Fin l)) :
    L.upperMass ((F₁ ⊕g F₂).map finSumFinEquiv.toEmbedding) =
      ((L.law (k + l)).map
          (fun G => (SimpleGraph.comap (Fin.castAdd l) G, SimpleGraph.comap (Fin.natAdd k) G))
        (Set.Ici F₁ ×ˢ Set.Ici F₂)).toReal := by
  have hinl : ⇑finSumFinEquiv.toEmbedding ∘ Sum.inl = (Fin.castAdd l : Fin k → Fin (k + l)) := by
    funext i
    simp
  have hinr : ⇑finSumFinEquiv.toEmbedding ∘ Sum.inr = (Fin.natAdd k : Fin l → Fin (k + l)) := by
    funext i
    simp
  rw [upperMass_def, Measure.map_apply (by fun_prop) MeasurableSet.of_discrete]
  congr 2
  ext G
  rw [Set.mem_ofPred_eq, SimpleGraph.map_le_iff_le_comap, SimpleGraph.sum_le_iff,
    SimpleGraph.comap_comap, SimpleGraph.comap_comap, hinl, hinr]
  rfl

end ExchangeableGraphLaw

/-- **Dissociation via upper masses.** A law is dissociated iff its upper masses are multiplicative
over disjoint unions of patterns. The forward direction evaluates the two laws on upper
rectangles; the converse holds because the upper rectangles are the upper rays of the product of
the two finite lattices of graphs, which determine a finite law on it. -/
theorem isDissociated_iff_upperMass_mul (L : ExchangeableGraphLaw) :
    L.IsDissociated ↔
      ∀ (k l : ℕ) (F₁ : SimpleGraph (Fin k)) (F₂ : SimpleGraph (Fin l)),
        L.upperMass ((F₁ ⊕g F₂).map finSumFinEquiv.toEmbedding) =
          L.upperMass F₁ * L.upperMass F₂ := by
  constructor
  · intro h k l F₁ F₂
    rw [ExchangeableGraphLaw.upperMass_map_sum, h k l, Measure.prod_prod, ENNReal.toReal_mul,
      ExchangeableGraphLaw.upperMass_def, ExchangeableGraphLaw.upperMass_def]
    rfl
  · intro h k l
    refine Measure.ext_of_Ici_of_finite _ _ fun F => ?_
    rw [← Set.Ici_prod_Ici, Measure.prod_prod]
    refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ?_).1 ?_
    · exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
    · rw [ENNReal.toReal_mul, ← ExchangeableGraphLaw.upperMass_map_sum, h k l F.1 F.2,
        ExchangeableGraphLaw.upperMass_def, ExchangeableGraphLaw.upperMass_def]
      rfl

end DenseGraphLimits

end TauCeti
