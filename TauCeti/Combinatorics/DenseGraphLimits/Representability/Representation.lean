/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Representability.ParamLaw
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.DissociatedRepresentation
public import TauCeti.Combinatorics.DenseGraphLimits.Representability.HomDensity

/-!
# The Lovász–Szegedy characterization of homomorphism densities

A graph parameter is the homomorphism density `t(·, W)` of a graphon `W` on the unit interval if and
only if it is isomorphism invariant, multiplicative, normalized and reflection positive
(`lovasz_szegedy_representability`).

The hard direction is `exists_graphon_of_representability_axioms`: a parameter `f` satisfying the
four axioms is `t(·, W)` for a graphon `W` on the unit interval.  The easy direction is that
`t(·, W)` satisfies them, for a graphon on any probability space
(`isReflectionPositive_homDensityParam` and its three companions).

As a consequence such a parameter takes values in `[0, 1]`
(`graphParam_mem_Icc_of_representability_axioms`): boundedness follows from the four axioms and is
not one of them.

## Main results

* `TauCeti.DenseGraphLimits.lovasz_szegedy_representability` — **a graph parameter is `t(·, W)`
  for a graphon `W` on the unit interval iff it satisfies the four representability axioms.**
* `TauCeti.DenseGraphLimits.exists_graphon_of_representability_axioms` — the hard direction: a
  graph parameter satisfying the four representability axioms is `t(·, W)` for a graphon `W` on
  the unit interval.
* `TauCeti.DenseGraphLimits.graphParam_mem_Icc_of_representability_axioms` — such a parameter
  takes values in `[0, 1]`.

## References

* L. Lovász, B. Szegedy, *Limits of dense graph sequences*, JCTB 96 (2006), 933–957,
  Theorem 2.2.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Section 11.3.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.DenseGraphLimits

/-- **Representability, hard direction.** An isomorphism-invariant, multiplicative, normalized,
reflection-positive graph parameter is the homomorphism density of a graphon on the unit
interval. -/
theorem exists_graphon_of_representability_axioms (f : GraphParam) (hiso : IsIsoInvariant f)
    (hmul : IsMultiplicative f) (hnorm : IsNormalized f) (hrp : IsReflectionPositive f) :
    ∃ W : Graphon unitInterval (volume : Measure unitInterval),
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj], f n F = homDensity F W := by
  obtain ⟨W, hW⟩ := exists_graphon_of_isDissociated _
    (isDissociated_paramExchangeableLaw f hiso hmul hnorm hrp)
  refine ⟨W, fun n F _ => ?_⟩
  rw [← paramExchangeableLaw_upperMass f hiso hmul hnorm hrp F, hW,
    upperMass_sampleExchangeableLaw]

/-- A graph parameter satisfying the four representability axioms takes values in `[0, 1]`. -/
theorem graphParam_mem_Icc_of_representability_axioms (f : GraphParam) (hiso : IsIsoInvariant f)
    (hmul : IsMultiplicative f) (hnorm : IsNormalized f) (hrp : IsReflectionPositive f)
    (n : ℕ) (F : SimpleGraph (Fin n)) : f n F ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  obtain ⟨W, hW⟩ := exists_graphon_of_representability_axioms f hiso hmul hnorm hrp
  rw [hW n F]
  exact ⟨homDensity_nonneg F W, homDensity_le_one F W⟩

/-- **The Lovász–Szegedy characterization of homomorphism densities.** A graph parameter is the
homomorphism density of a graphon on the unit interval if and only if it is isomorphism invariant,
multiplicative, normalized and reflection positive. -/
theorem lovasz_szegedy_representability (f : GraphParam) :
    (∃ W : Graphon unitInterval (volume : Measure unitInterval),
        ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj], f n F = homDensity F W) ↔
      IsIsoInvariant f ∧ IsMultiplicative f ∧ IsNormalized f ∧ IsReflectionPositive f := by
  refine ⟨fun ⟨W, hW⟩ => ?_, fun ⟨hiso, hmul, hnorm, hrp⟩ =>
    exists_graphon_of_representability_axioms f hiso hmul hnorm hrp⟩
  have hf : f = homDensityParam W := by
    classical
    funext n F
    rw [hW n F, homDensityParam_apply]
  subst hf
  exact ⟨isIsoInvariant_homDensityParam W, isMultiplicative_homDensityParam W,
    isNormalized_homDensityParam W, isReflectionPositive_homDensityParam W⟩

end TauCeti.DenseGraphLimits
