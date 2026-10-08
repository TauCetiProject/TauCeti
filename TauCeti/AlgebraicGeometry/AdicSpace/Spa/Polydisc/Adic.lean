/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.StronglyNoetherian
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
public import TauCeti.RingTheory.Huber.Restricted.Noetherian
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

/-!
# Closed polydiscs as adic spaces

Over a complete nonarchimedean normed field `K`, the spectrum `Spa(K, K°)` and every closed unit
polydisc are affinoid adic spaces. The polydisc is presented by the ordinary restricted-series
ring over `K`; completeness identifies that ring with the completed Tate algebra, so its strong
noetherianness follows from the strong noetherianness of `K`.

The construction keeps a pair of definition explicit. This is the same presentation dependence
as `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpace`; the underlying adic spectrum and
the sheafiness conclusion do not choose a global pair of definition.

## Main definitions

* `TauCeti.ValuationSpectrum.closedPolydiscPreAdicSpace`: the presentation-limit pre-adic space
  whose underlying topological space is the closed polydisc, with
  `closedPolydiscPreAdicSpace_def` as its characteristic equation.

## Main results

* `TauCeti.ValuationSpectrum.isAdic_spa_powerBounded_of_normedField`: `Spa(K, K°)` with its
  presentation-limit structure sheaf is an adic space.
* `TauCeti.ValuationSpectrum.isAdic_closedPolydiscPreAdicSpace`: every closed unit polydisc over
  `K` is an affinoid adic space.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.6, for strong noetherianness of Tate
  algebras.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57 and
  Theorem 8.28(b).
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

universe u

section BaseField

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]
  [CompleteSpace K] [IsTateRing K]

/-- **The adic spectrum `Spa(K, K°)` of a complete nonarchimedean field is an adic space.**
Here `K°` is the power-bounded subring and `P` is any pair of definition of the Tate field. -/
theorem isAdic_spa_powerBounded_of_normedField (P : PairOfDefinition K) :
    PreAdicSpace.isAdic
      (presentationLimitPreAdicSpace P (powerBoundedSubring K)
        (fun _ ha ↦ mem_powerBoundedSubring.mp ha) P.le_powerBoundedSubring) :=
  isAdic_presentationLimitPreAdicSpace_of_isStronglyNoetherian P P.le_powerBoundedSubring
    (fun _ ha ↦ mem_powerBoundedSubring.mp ha)

end BaseField

section Polydisc

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]
  [CompleteSpace K] [IsTateRing K]

variable (k : ℕ) (P : PairOfDefinition K)

/-- **The presentation-limit pre-adic space of the closed unit `k`-polydisc over `K`.** Its
coordinate ring is the ordinary restricted-series ring, its plus ring is the power-bounded
subring, and its pair of definition is obtained from `P` coefficientwise. -/
noncomputable def closedPolydiscPreAdicSpace : PreAdicSpace.{u} :=
  let B := weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
    isWeightFamily_one_weight
  let Q : PairOfDefinition B := P.weighted (T := fun _ : Fin k ↦ ({1} : Set K))
    isWeightFamily_one_weight
  presentationLimitPreAdicSpace Q (powerBoundedSubring B)
    (fun _ ha ↦ mem_powerBoundedSubring.mp ha) Q.le_powerBoundedSubring

omit [IsUltrametricDist K] [CompleteSpace K] [IsTateRing K] in
/-- The closed-polydisc pre-adic space is the presentation-limit spectrum for the coefficientwise
pair of definition and the power-bounded plus ring. -/
lemma closedPolydiscPreAdicSpace_def :
    closedPolydiscPreAdicSpace k P =
      presentationLimitPreAdicSpace
        (P.weighted (T := fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight)
        (powerBoundedSubring
          (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
            isWeightFamily_one_weight))
        (fun _ ha ↦ mem_powerBoundedSubring.mp ha)
        (P.weighted (T := fun _ : Fin k ↦ ({1} : Set K))
          isWeightFamily_one_weight).le_powerBoundedSubring :=
  (rfl)

omit [IsUltrametricDist K] [CompleteSpace K] [IsTateRing K] in
/-- The topological space underlying `closedPolydiscPreAdicSpace` is the closed polydisc
`Spa(K⟨T₁, …, Tₖ⟩, K⟨T₁, …, Tₖ⟩°)`. -/
@[simp]
theorem closedPolydiscPreAdicSpace_carrier :
    ((closedPolydiscPreAdicSpace k P).toPresheafedSpace : TopCat) =
      TopCat.of ↥(closedPolydisc k K) := by
  rw [closedPolydiscPreAdicSpace_def, presentationLimitPreAdicSpace_carrier,
    closedPolydisc_def]

/-- **Every closed unit polydisc over a complete nonarchimedean field is an affinoid adic
space.** Its restricted-series coordinate ring is complete, Tate, and strongly noetherian. -/
theorem isAdic_closedPolydiscPreAdicSpace :
    PreAdicSpace.isAdic (closedPolydiscPreAdicSpace k P) := by
  rw [closedPolydiscPreAdicSpace_def]
  let B := weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
    isWeightFamily_one_weight
  let Q : PairOfDefinition B := P.weighted (T := fun _ : Fin k ↦ ({1} : Set K))
    isWeightFamily_one_weight
  exact isAdic_presentationLimitPreAdicSpace_of_isStronglyNoetherian Q
    Q.le_powerBoundedSubring (fun _ ha ↦ mem_powerBoundedSubring.mp ha)

end Polydisc

end TauCeti.ValuationSpectrum

end
