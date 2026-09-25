/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Existence
import Mathlib.Probability.Moments.Variance

/-!
# Dissociated exchangeable graph laws are sampling laws

A dissociated exchangeable graph law is the sampling law of a single graphon on the unit interval
(`exists_graphon_of_isDissociated`). Together with `isDissociated_sampleExchangeableLaw` this
identifies the dissociated exchangeable graph laws with the sampling laws of graphons.

The graphon comes from a mixing measure of the law, which exists by
`exists_mixtureExchangeableLaw_eq`. Under any mixing measure of a dissociated law, every
homomorphism density is almost surely equal to the corresponding upper mass
(`ae_homDensityOnSpace_eq_upperMass_of_isDissociated`), and a graphon class in the full-measure set
on which this holds for all finite patterns at once has the upper masses of the law. The theorem
does not say that the mixing measure is a Dirac mass or that the graphon is unique.

## Main results

* `TauCeti.DenseGraphLimits.ae_homDensityOnSpace_eq_upperMass_of_isDissociated` — under a mixing
  measure of a dissociated law, `t(F, ·)` is almost surely the upper mass of `F`.
* `TauCeti.DenseGraphLimits.exists_graphon_of_isDissociated` — **every dissociated exchangeable
  graph law is the sampling law of a graphon on the unit interval.**

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33–61, Section 5.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Section 11.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Under a mixing measure of a dissociated exchangeable graph law, each homomorphism density is
almost surely constant, equal to the upper mass of the pattern. Dissociation makes the upper mass of
two disjoint copies of `F` the square of the upper mass of `F`, so `t(F, ·)` has second moment equal
to the square of its mean, and hence variance zero. -/
theorem ae_homDensityOnSpace_eq_upperMass_of_isDissociated
    (P : ProbabilityMeasure (GraphonSpace Ω μ)) (h : (mixtureExchangeableLaw P).IsDissociated)
    {k : ℕ} (F : SimpleGraph (Fin k)) [DecidableRel F.Adj] :
    ∀ᵐ x ∂(P : Measure (GraphonSpace Ω μ)),
      homDensityOnSpace F x = (mixtureExchangeableLaw P).upperMass F := by
  classical
  have hsq : ∀ x : GraphonSpace Ω μ,
      homDensityOnSpace ((F ⊕g F).map finSumFinEquiv.toEmbedding) x =
        homDensityOnSpace F x ^ 2 := by
    refine SeparationQuotient.surjective_mk.forall.2 fun W => ?_
    rw [homDensityOnSpace_mk, homDensityOnSpace_mk, homDensity_map_embedding, homDensity_sum, sq]
  have hmem : MemLp (homDensityOnSpace (μ := μ) F) 2 (P : Measure (GraphonSpace Ω μ)) :=
    MemLp.of_bound (continuous_homDensityOnSpace F).aestronglyMeasurable 1
      (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (homDensityOnSpace_nonneg F x)]
        exact homDensityOnSpace_le_one F x)
  have hmul := (isDissociated_iff_upperMass_mul _).1 h k k F F
  rw [upperMass_mixtureExchangeableLaw, upperMass_mixtureExchangeableLaw] at hmul
  simp_rw [hsq] at hmul
  have hvar : Var[homDensityOnSpace (μ := μ) F; (P : Measure (GraphonSpace Ω μ))] = 0 := by
    rw [variance_eq_sub hmem]
    simp only [Pi.pow_apply]
    rw [hmul, sq, sub_self]
  filter_upwards [ae_eq_integral_of_variance_eq_zero hmem hvar] with x hx
  rw [hx, upperMass_mixtureExchangeableLaw]

/-- **Dissociated laws are sampling laws.** Every dissociated exchangeable graph law is the
sampling law of a graphon on the unit interval. -/
theorem exists_graphon_of_isDissociated (L : ExchangeableGraphLaw) (h : L.IsDissociated) :
    ∃ W : Graphon unitInterval (volume : Measure unitInterval), L = sampleExchangeableLaw W := by
  classical
  obtain ⟨P, rfl⟩ := exists_mixtureExchangeableLaw_eq L
  -- one graphon class on which every homomorphism density takes its upper-mass value
  have hall : ∀ᵐ x ∂(P : Measure GraphonSpaceI), ∀ (k : ℕ) (F : SimpleGraph (Fin k)),
      homDensityOnSpace F x = (mixtureExchangeableLaw P).upperMass F :=
    ae_all_iff.2 fun k => ae_all_iff.2 fun F =>
      ae_homDensityOnSpace_eq_upperMass_of_isDissociated P h F
  obtain ⟨x, hx⟩ := hall.exists
  obtain ⟨W, rfl⟩ := SeparationQuotient.surjective_mk x
  refine ⟨W, ExchangeableGraphLaw.ext_upperMass fun k F => ?_⟩
  rw [upperMass_sampleExchangeableLaw, ← homDensityOnSpace_mk, hx]

end DenseGraphLimits

end TauCeti
