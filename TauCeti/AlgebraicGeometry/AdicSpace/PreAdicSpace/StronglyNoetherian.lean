/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StronglyNoetherian
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Huber.Restricted.Noetherian
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

/-!
# Affinoid adic spaces of strongly noetherian Tate rings

For a strongly noetherian Tate ring `A` and a ring of integral elements `A⁺`, the structure
presheaf of `Spa(A, A⁺)` is a sheaf (Wedhorn, Theorem 8.28(b)), so `Spa(A, A⁺)`, with its
presentation-limit structure presheaf and point valuations, is an affinoid adic space.

Over a complete Hausdorff strongly noetherian Tate ring `A` the ring `A⟨T₁, …, Tₖ⟩` of restricted
power series is again complete, Hausdorff, Tate and strongly noetherian, being its own completion
(`TauCeti.Huber.IsStronglyNoetherian.weightedRestrictedSubring_one_weight`), so the closed unit
polydisc `Spa(A⟨T₁, …, Tₖ⟩, A⟨T₁, …, Tₖ⟩°)` is an affinoid adic space too.

These are the first examples of rigid geometry. A complete nontrivially normed field `K` with an
ultrametric norm — a complete rank-one nonarchimedean field — is a Tate ring
(`TauCeti.Huber.IsTateRing.of_nontriviallyNormedField`) and strongly noetherian by
Bosch–Güntzer–Remmert §5.2.6 (`TauCeti.Huber.IsStronglyNoetherian.of_normedField`). Hence
`Spa(K, K°)` and the closed unit polydiscs over `K`, whose points are the sets `closedPolydisc k K`
of `TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic`, are affinoid adic spaces; the closed
unit disc is the case `k = 1`. The `example`s at the end of the file record this.

Each statement holds for every pair of definition, since the structure presheaf is built from
one: for the plus ring `A°`, every ring of definition lies in it
(`TauCeti.Huber.PairOfDefinition.le_powerBoundedSubring`).

## Main results

* `TauCeti.ValuationSpectrum.isAdic_presentationLimitPreAdicSpace_of_isStronglyNoetherian`:
  `Spa(A, A⁺)` is an adic space for a strongly noetherian Tate ring `A`.
* `TauCeti.ValuationSpectrum.isAdic_presentationLimitPreAdicSpace_powerBoundedSubring`: the case
  `A⁺ = A°`; for a complete rank-one nonarchimedean field this is `Spa(K, K°)`.
* `TauCeti.ValuationSpectrum.isAdic_presentationLimitPreAdicSpace_closedPolydisc`: the closed unit
  polydisc over a complete Hausdorff strongly noetherian Tate ring is an adic space.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 7.56, Example 7.57,
  Theorem 8.28(b) and Definition 8.22.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.2.6.
-/

public section

open CategoryTheory TauCeti.Huber

universe u

namespace TauCeti.ValuationSpectrum

section StronglyNoetherian

variable {A : Type u} [CommRing A] [UniformSpace A] [IsTopologicalRing A] [IsTateRing A]
  [IsStronglyNoetherian A] (P : PairOfDefinition A)

/-- **`Spa(A, A⁺)` of a strongly noetherian Tate ring is an affinoid adic space.** Its structure
presheaf is a sheaf by Wedhorn's Theorem 8.28(b). Here `P` is a pair of definition whose ring of
definition lies in the subring `A⁺` of power-bounded elements; `A` need not be complete or
Hausdorff. -/
theorem isAdic_presentationLimitPreAdicSpace_of_isStronglyNoetherian {Aplus : Subring A}
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus) :
    PreAdicSpace.isAdic (presentationLimitPreAdicSpace P Aplus hAplus hP) :=
  isAdic_presentationLimitPreAdicSpace P Aplus hAplus hP
    (isSheaf_presentationLimitPresheaf_of_isStronglyNoetherian P hP hAplus)

/-- **`Spa(A, A°)` of a strongly noetherian Tate ring is an affinoid adic space**, for every pair
of definition: its ring of definition is contained in `A°`. -/
theorem isAdic_presentationLimitPreAdicSpace_powerBoundedSubring :
    PreAdicSpace.isAdic (presentationLimitPreAdicSpace P (powerBoundedSubring A)
      (fun _ ↦ mem_powerBoundedSubring.mp) P.le_powerBoundedSubring) :=
  isAdic_presentationLimitPreAdicSpace_of_isStronglyNoetherian P _ _

end StronglyNoetherian

section Polydisc

variable (k : ℕ) {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [IsTateRing A] [IsStronglyNoetherian A] [CompleteSpace A] [T0Space A]

/-- **The closed unit polydisc over a complete Hausdorff strongly noetherian Tate ring is an
affinoid adic space**: `Spa(A⟨T₁, …, Tₖ⟩, A⟨T₁, …, Tₖ⟩°)`, with the structure presheaf built from
any pair of definition of `A⟨T₁, …, Tₖ⟩`. The ring of restricted power series is a Tate ring
because `A` is, and strongly noetherian because it is complete and Hausdorff
(`TauCeti.Huber.IsStronglyNoetherian.weightedRestrictedSubring_one_weight`). -/
theorem isAdic_presentationLimitPreAdicSpace_closedPolydisc
    (P : PairOfDefinition
      (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)) :
    PreAdicSpace.isAdic (presentationLimitPreAdicSpace P (powerBoundedSubring _)
      (fun _ ↦ mem_powerBoundedSubring.mp) P.le_powerBoundedSubring) :=
  isAdic_presentationLimitPreAdicSpace_powerBoundedSubring P

end Polydisc

/-! ### Complete rank-one nonarchimedean fields

A complete nontrivially normed field `K` with an ultrametric norm is a Tate ring and strongly
noetherian by instances, so both results apply to it: `Spa(K, K°)` and the closed unit polydiscs
over `K` — the closed unit disc is the case `k = 1` — are affinoid adic spaces. -/

example {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PairOfDefinition K) :
    PreAdicSpace.isAdic (presentationLimitPreAdicSpace P (powerBoundedSubring K)
      (fun _ ↦ mem_powerBoundedSubring.mp) P.le_powerBoundedSubring) :=
  isAdic_presentationLimitPreAdicSpace_powerBoundedSubring P

example (k : ℕ) {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PairOfDefinition
      (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight)) :
    PreAdicSpace.isAdic (presentationLimitPreAdicSpace P (powerBoundedSubring _)
      (fun _ ↦ mem_powerBoundedSubring.mp) P.le_powerBoundedSubring) :=
  isAdic_presentationLimitPreAdicSpace_closedPolydisc k P

end TauCeti.ValuationSpectrum
