/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Representability.Moebius
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Dissociated
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# The exchangeable graph law of a graph parameter

A graph parameter `f` satisfying the four structural conditions of the Lovász–Szegedy
representability theorem — isomorphism invariance, multiplicativity, normalization and reflection
positivity — defines a random graph: its level-`n` law gives each graph `H` on `Fin n` the Möbius
mass `f†(H)`.  The Möbius masses are nonnegative and sum to one at each level, and they are
consistent along label injections, so these laws form an exchangeable graph law `L_f`.  By Möbius
inversion its upper masses `P(F ≤ ·)` are the values `f(F)`, and multiplicativity of `f` then says
exactly that `L_f` is dissociated.

This is the random object behind the classical proof of representability: a dissociated
exchangeable graph law is the sampling law of a graphon `W`, whose upper masses are the homomorphism
densities `t(·, W)`, so `f = t(·, W)`.  No graphon is involved in the construction here.

## Main definitions

* `TauCeti.DenseGraphLimits.paramGraphLaw` — the measure on the graphs on `Fin n` with mass `f†(H)`
  at each `H`, as a weighted sum of Dirac masses;
* `TauCeti.DenseGraphLimits.paramExchangeableLaw` — the exchangeable graph law `L_f` with these
  level measures.

## Main results

* `TauCeti.DenseGraphLimits.paramGraphLaw_apply` — the mass of a set of graphs is the sum of the
  Möbius masses of its members;
* `TauCeti.DenseGraphLimits.paramGraphLaw_isProbabilityMeasure` — each level is a probability
  measure;
* `TauCeti.DenseGraphLimits.paramGraphLaw_map_comap` — the levels are consistent along label
  injections;
* `TauCeti.DenseGraphLimits.paramExchangeableLaw_upperMass` — the upper masses of `L_f` are the
  values of `f`;
* `TauCeti.DenseGraphLimits.isDissociated_paramExchangeableLaw` — `L_f` is dissociated.

## Implementation

The weights of `paramGraphLaw` are `ENNReal.ofReal (f†(H))`, so the measure is defined for every
parameter; the structural conditions enter only through the theorems.  Nonnegativity of `f†`, a
consequence of isomorphism invariance and reflection positivity, is what makes these weights
faithful to the real identities of the Möbius calculus, which is why reflection positivity is a
hypothesis of the consistency theorem even though the underlying identity
`graphParamMobius_sum_comap` does not need it.

## References

* L. Lovász, B. Szegedy, *Limits of dense graph sequences*, JCTB 96 (2006), 933–957, Section 2 —
  the random graph with probabilities `f†` in the proof of Theorem 2.2.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Section 5.3 and Chapter 11.
-/

-- Provenance: the names and signatures of the declarations below follow
-- `TauCetiRoadmap/DenseGraphLimits/Suggested.lean`; `paramGraphLaw_isProbabilityMeasure` also
-- assumes isomorphism invariance, which the nonnegativity of `f†` needs.

public section

noncomputable section

open Finset MeasureTheory

namespace TauCeti.DenseGraphLimits

/-- The **level-`n` law of a graph parameter**: the measure on the graphs on `Fin n` with mass
`f†(H)` at each `H`, clipped at `0`.  For a parameter satisfying the structural conditions it is a
probability measure (`paramGraphLaw_isProbabilityMeasure`). -/
def paramGraphLaw (f : GraphParam) (n : ℕ) : Measure (SimpleGraph (Fin n)) :=
  ∑ H : SimpleGraph (Fin n), ENNReal.ofReal (graphParamMobius f n H) • Measure.dirac H

open Classical in
/-- The mass of a set of graphs under `paramGraphLaw` is the sum of the Möbius masses of its
members. -/
theorem paramGraphLaw_apply (f : GraphParam) (n : ℕ) (s : Set (SimpleGraph (Fin n))) :
    paramGraphLaw f n s =
      ∑ H ∈ univ.filter (· ∈ s), ENNReal.ofReal (graphParamMobius f n H) := by
  simp [paramGraphLaw, Measure.dirac_apply' _ (MeasurableSet.of_discrete (s := s)),
    Set.indicator_apply, sum_filter]

/-- The mass of a single graph under `paramGraphLaw` is its Möbius mass. -/
@[simp]
theorem paramGraphLaw_singleton (f : GraphParam) (n : ℕ) (H : SimpleGraph (Fin n)) :
    paramGraphLaw f n {H} = ENNReal.ofReal (graphParamMobius f n H) := by
  classical
  rw [paramGraphLaw_apply, sum_filter]
  simp

/-- For a parameter satisfying the structural conditions, each level law is a probability
measure: the Möbius masses are nonnegative and sum to one. -/
theorem paramGraphLaw_isProbabilityMeasure (f : GraphParam) (hiso : IsIsoInvariant f)
    (hmul : IsMultiplicative f) (hnorm : IsNormalized f) (hrp : IsReflectionPositive f)
    (n : ℕ) : IsProbabilityMeasure (paramGraphLaw f n) := by
  classical
  constructor
  rw [paramGraphLaw_apply, ← ENNReal.ofReal_sum_of_nonneg
    fun H _ => graphParamMobius_nonneg f hiso hrp n H]
  simp [graphParamMobius_sum_eq_one f hmul hnorm n]

/-- **Consistency of the level laws.** For a parameter satisfying the structural conditions,
restricting the level-`n` law along a label injection `e : Fin k ↪ Fin n` gives the level-`k`
law. -/
theorem paramGraphLaw_map_comap (f : GraphParam) (hiso : IsIsoInvariant f)
    (hmul : IsMultiplicative f) (hnorm : IsNormalized f) (hrp : IsReflectionPositive f)
    {k n : ℕ} (e : Fin k ↪ Fin n) :
    (paramGraphLaw f n).map (SimpleGraph.comap ⇑e) = paramGraphLaw f k := by
  classical
  refine Measure.ext_of_singleton fun G => ?_
  rw [Measure.map_apply (SimpleGraph.measurable_comap _) MeasurableSet.of_discrete,
    paramGraphLaw_apply, paramGraphLaw_singleton, graphParamMobius_sum_comap f hiso hmul hnorm e,
    ENNReal.ofReal_sum_of_nonneg fun H _ => graphParamMobius_nonneg f hiso hrp n H]
  simp only [Set.mem_preimage, Set.mem_singleton_iff]

/-- The **exchangeable graph law `L_f`** of a parameter satisfying the structural conditions: its
level-`n` marginal gives each graph `H` on `Fin n` the Möbius mass `f†(H)`. -/
def paramExchangeableLaw (f : GraphParam) (hiso : IsIsoInvariant f) (hmul : IsMultiplicative f)
    (hnorm : IsNormalized f) (hrp : IsReflectionPositive f) : ExchangeableGraphLaw where
  law := paramGraphLaw f
  prob := paramGraphLaw_isProbabilityMeasure f hiso hmul hnorm hrp
  consistent := paramGraphLaw_map_comap f hiso hmul hnorm hrp

/-- The marginals of `L_f` are the level laws `paramGraphLaw f`. -/
@[simp]
theorem paramExchangeableLaw_law (f : GraphParam) (hiso : IsIsoInvariant f)
    (hmul : IsMultiplicative f) (hnorm : IsNormalized f) (hrp : IsReflectionPositive f) (n : ℕ) :
    (paramExchangeableLaw f hiso hmul hnorm hrp).law n = paramGraphLaw f n := (rfl)

/-- **The upper masses of `L_f` are the values of `f`.**  By Möbius inversion, the probability
that the level-`k` sample contains `F` is `∑_{G ≥ F} f†(G) = f(F)`. -/
@[simp]
theorem paramExchangeableLaw_upperMass (f : GraphParam) (hiso : IsIsoInvariant f)
    (hmul : IsMultiplicative f) (hnorm : IsNormalized f) (hrp : IsReflectionPositive f)
    {k : ℕ} (F : SimpleGraph (Fin k)) :
    (paramExchangeableLaw f hiso hmul hnorm hrp).upperMass F = f k F := by
  rw [ExchangeableGraphLaw.upperMass_eq_sum, ← sum_graphParamMobius_filter_le f F]
  refine sum_congr rfl fun G _ => ?_
  rw [paramExchangeableLaw_law, paramGraphLaw_singleton,
    ENNReal.toReal_ofReal (graphParamMobius_nonneg f hiso hrp k G)]

/-- **`L_f` is dissociated.**  Its upper masses are the values of `f`, which are multiplicative
over disjoint unions. -/
theorem isDissociated_paramExchangeableLaw (f : GraphParam) (hiso : IsIsoInvariant f)
    (hmul : IsMultiplicative f) (hnorm : IsNormalized f) (hrp : IsReflectionPositive f) :
    (paramExchangeableLaw f hiso hmul hnorm hrp).IsDissociated :=
  (isDissociated_iff_upperMass_mul _).2 fun k l F₁ F₂ => by
    simpa only [paramExchangeableLaw_upperMass] using isMultiplicative_iff.1 hmul k l F₁ F₂

end TauCeti.DenseGraphLimits
