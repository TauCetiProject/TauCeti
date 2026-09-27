/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Correspondence
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.DissociatedRepresentation
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.InfiniteSampling

/-!
# Graphon mixtures and exchangeable laws on infinite graphs

Every exchangeable probability law on infinite graphs corresponds to a unique probability
measure on the graphon quotient. The correspondence transports the finite-marginal mixture
equivalence through extension to infinite graphs. Its finite upper masses are integrals of
homomorphism densities. Dirac mixing measures give the joint sampling law of one graphon, and
these are exactly the dissociated laws.

This is the graphon-mixture correspondence of Diaconis and Janson, *Graph limits and
exchangeable random graphs*, Section 5.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

/-- A graphon mixture is dissociated exactly when its mixing measure is concentrated at one
graphon class. -/
theorem isDissociated_mixtureExchangeableLaw_iff (P : ProbabilityMeasure GraphonSpaceI) :
    (mixtureExchangeableLaw P).IsDissociated ↔
      ∃ W : Graphon unitInterval (volume : Measure unitInterval),
        P = diracProba (SeparationQuotient.mk W) := by
  constructor
  · intro h
    obtain ⟨W, hW⟩ := exists_graphon_of_isDissociated (mixtureExchangeableLaw P) h
    refine ⟨W, mixtureExchangeableLaw_injective ?_⟩
    rw [mixtureExchangeableLaw_diracProba]
    exact hW
  · rintro ⟨W, rfl⟩
    rw [mixtureExchangeableLaw_diracProba]
    exact isDissociated_sampleExchangeableLaw W

/-- The Diaconis–Janson correspondence between mixing measures on graphon space and
exchangeable probability laws on infinite graphs. -/
def graphonMixtureLawEquiv :
    ProbabilityMeasure GraphonSpaceI ≃ InfiniteExchangeableGraphLaw :=
  mixtureExchangeableLawEquiv.trans exchangeableGraphLawEquivInfinite

/-- A Dirac mixing measure gives the infinite joint sampling law of its graphon. -/
@[simp]
theorem graphonMixtureLawEquiv_dirac
    (W : Graphon unitInterval (volume : Measure unitInterval)) :
    graphonMixtureLawEquiv (diracProba (SeparationQuotient.mk W)) =
      exchangeableGraphLawEquivInfinite (sampleExchangeableLaw W) := by
  rw [graphonMixtureLawEquiv, Equiv.trans_apply, mixtureExchangeableLawEquiv_apply,
    mixtureExchangeableLaw_diracProba]

/-- The upper mass of each finite window of a graphon mixture is the mixing average of its
homomorphism density. -/
@[simp]
theorem graphonMixtureLawEquiv_upperMass (P : ProbabilityMeasure GraphonSpaceI)
    {k : ℕ} (F : SimpleGraph (Fin k)) [DecidableRel F.Adj] :
    (exchangeableGraphLawEquivInfinite.symm (graphonMixtureLawEquiv P)).upperMass F =
      ∫ x, homDensityOnSpace F x ∂(P : Measure GraphonSpaceI) := by
  rw [graphonMixtureLawEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    mixtureExchangeableLawEquiv_apply, upperMass_mixtureExchangeableLaw]

end DenseGraphLimits

end TauCeti
