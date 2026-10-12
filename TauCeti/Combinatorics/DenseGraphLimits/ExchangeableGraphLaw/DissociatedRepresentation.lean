/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Existence
import Mathlib.Probability.Moments.Variance
import TauCeti.Combinatorics.DenseGraphLimits.Separation.Inverse

/-!
# Dissociated exchangeable graph laws are sampling laws

A graphon mixture over an arbitrary probability carrier is dissociated exactly when its mixing
measure is the Dirac mass at one graphon class (`isDissociated_mixtureExchangeableLaw_iff`). Hence a
dissociated exchangeable graph law is the sampling law of a single graphon, which can be taken on
any atomless standard Borel carrier, such as the unit interval (`exists_graphon_of_isDissociated`).
Together with `isDissociated_sampleExchangeableLaw` this identifies the dissociated exchangeable
graph laws with the sampling laws of graphons.

The route is through the homomorphism-density coordinates. Under any mixing measure of a
dissociated law, every homomorphism density is almost surely equal to the corresponding upper mass
(`ae_homDensityOnSpace_eq_upperMass_of_isDissociated`), so all homomorphism-density coordinates are
almost surely constant at once; since they separate graphon classes, almost every class is the same
one. The representing graphon is unique only up to cut distance zero.

## Main results

* `TauCeti.DenseGraphLimits.ae_homDensityOnSpace_eq_upperMass_of_isDissociated` — under a mixing
  measure of a dissociated law, `t(F, ·)` is almost surely the upper mass of `F`.
* `TauCeti.DenseGraphLimits.isDissociated_mixtureExchangeableLaw_iff` — a graphon mixture is
  dissociated exactly when its mixing measure is a Dirac mass.
* `TauCeti.DenseGraphLimits.exists_graphon_of_isDissociated` — **every dissociated exchangeable
  graph law is the sampling law of a graphon on every atomless standard Borel carrier.**

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
almost surely constant, equal to the upper mass of the pattern. -/
theorem ae_homDensityOnSpace_eq_upperMass_of_isDissociated
    (P : ProbabilityMeasure (GraphonSpace Ω μ)) (h : (mixtureExchangeableLaw P).IsDissociated)
    {k : ℕ} (F : SimpleGraph (Fin k)) [DecidableRel F.Adj] :
    ∀ᵐ x ∂(P : Measure (GraphonSpace Ω μ)),
      homDensityOnSpace F x = (mixtureExchangeableLaw P).upperMass F := by
  classical
  -- two disjoint copies of `F` have density `t(F, ·)²`, so by dissociation the second moment of
  -- `t(F, ·)` is the square of its mean, and its variance is zero
  have hsq : ∀ x : GraphonSpace Ω μ,
      homDensityOnSpace ((F ⊕g F).map finSumFinEquiv.toEmbedding) x =
        homDensityOnSpace F x ^ 2 := fun x => by
    rw [homDensityOnSpace_map_embedding, homDensityOnSpace_sum, sq]
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

/-- **Dissociated mixtures are Dirac mixtures.** A graphon mixture, over an arbitrary probability
carrier, is dissociated exactly when its mixing measure is the Dirac mass at one graphon class. -/
theorem isDissociated_mixtureExchangeableLaw_iff (P : ProbabilityMeasure (GraphonSpace Ω μ)) :
    (mixtureExchangeableLaw P).IsDissociated ↔
      ∃ W : Graphon Ω μ, P = diracProba (SeparationQuotient.mk W) := by
  classical
  refine ⟨fun h => ?_, fun ⟨W, hW⟩ => ?_⟩
  · -- one graphon class on which every homomorphism density takes its upper-mass value
    have hall : ∀ᵐ x ∂(P : Measure (GraphonSpace Ω μ)), ∀ (k : ℕ) (F : SimpleGraph (Fin k)),
        homDensityOnSpace F x = (mixtureExchangeableLaw P).upperMass F :=
      ae_all_iff.2 fun k => ae_all_iff.2 fun F =>
        ae_homDensityOnSpace_eq_upperMass_of_isDissociated P h F
    obtain ⟨x, hx⟩ := hall.exists
    obtain ⟨W, rfl⟩ := SeparationQuotient.surjective_mk x
    -- by separation, almost every class is that one
    have hW : (id : GraphonSpace Ω μ → GraphonSpace Ω μ) =ᵐ[(P : Measure (GraphonSpace Ω μ))]
        fun _ => SeparationQuotient.mk W := by
      filter_upwards [hall] with y hy
      refine (graphonSpace_ext_iff_homDensity y _).2 fun k F _ => ?_
      -- `convert` reconciles the given decidability instance with the classical one in `hall`
      convert (hy k F).trans (hx k F).symm
    refine ⟨W, ProbabilityMeasure.toMeasure_injective ?_⟩
    -- the measure underlying `diracProba x` is `Measure.dirac x`
    exact calc (P : Measure (GraphonSpace Ω μ))
        _ = (P : Measure (GraphonSpace Ω μ)).map id := Measure.map_id.symm
        _ = (P : Measure (GraphonSpace Ω μ)).map fun _ => SeparationQuotient.mk W :=
          Measure.map_congr hW
        _ = Measure.dirac (SeparationQuotient.mk W) := by simp [Measure.map_const]
  · rw [hW, mixtureExchangeableLaw_diracProba]
    exact isDissociated_sampleExchangeableLaw W

variable (μ) in
/-- **Dissociated laws are sampling laws.** Every dissociated exchangeable graph law is the
sampling law of a graphon on every atomless standard Borel carrier `(Ω, μ)`, such as the unit
interval. -/
theorem exists_graphon_of_isDissociated [StandardBorelSpace Ω] [NullSingletonClass μ]
    (L : ExchangeableGraphLaw) (h : L.IsDissociated) :
    ∃ W : Graphon Ω μ, L = sampleExchangeableLaw W := by
  obtain ⟨P, rfl⟩ := exists_mixtureExchangeableLaw_eq L
  obtain ⟨U, rfl⟩ := (isDissociated_mixtureExchangeableLaw_iff P).1 h
  obtain ⟨W, hW⟩ := exists_graphon_cutDist_eq_zero μ U
  refine ⟨W, ?_⟩
  rw [mixtureExchangeableLaw_diracProba, sampleExchangeableLaw_eq_of_cutDist_eq_zero U W hW]

end DenseGraphLimits

end TauCeti
