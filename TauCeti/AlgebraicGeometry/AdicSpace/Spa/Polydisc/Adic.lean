/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.StronglyNoetherian
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Huber.Restricted.Noetherian
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

/-!
# Closed polydiscs as adic spaces

Over a complete nonarchimedean normed field `K`, the spectrum `Spa(K, K°)` and every closed unit
polydisc are affinoid adic spaces. The polydisc is presented by the ordinary restricted-series
ring over `K`; completeness identifies that ring with the completed Tate algebra, so its strong
noetherianness follows from the strong noetherianness of `K`.

For a complete nontrivially normed field with an ultrametric norm — a complete rank-one
nonarchimedean field — the Tate-ring hypothesis is supplied by
`TauCeti.Huber.IsTateRing.of_nontriviallyNormedField`, and the `example`s at the end of the file
record that both results then apply with no further hypotheses.

The construction keeps a pair of definition explicit. This is the same presentation dependence
as `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpace`; the underlying adic spectrum and
the sheafiness conclusion do not choose a global pair of definition.

## Main definitions

* `TauCeti.ValuationSpectrum.closedPolydiscPreAdicSpace`: the presentation-limit pre-adic space
  whose underlying topological space is the closed polydisc, with
  `closedPolydiscPreAdicSpace_def` as its characteristic equation.
* `TauCeti.ValuationSpectrum.closedPolydiscBasicOpen`: a rational open of the closed-polydisc
  pre-adic space.
* `TauCeti.ValuationSpectrum.closedPolydiscBasicOpenIso`: the restriction to an admissible
  rational open is the pre-adic space of the completed rational localisation.
* `TauCeti.ValuationSpectrum.closedPolydiscPreAdicSpaceHomeomorph`: the points of the
  closed-polydisc pre-adic space are the points of the closed polydisc.

## Main results

* `TauCeti.ValuationSpectrum.isAdic_spa_powerBounded_of_normedField`: `Spa(K, K°)` with its
  presentation-limit structure sheaf is an adic space.
* `TauCeti.ValuationSpectrum.isAdic_closedPolydiscPreAdicSpace`: every closed unit polydisc over
  `K` is an affinoid adic space.
* `TauCeti.ValuationSpectrum.closedPolydiscBasicOpen_mem_affinoidOpens`: admissible rational
  opens are open affinoid subspaces.

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

/- The declarations below are stated for `closedPolydiscPreAdicSpace k P` but built from the
presentation-limit API, elaborating against the unfolding recorded by the definitional equation
`closedPolydiscPreAdicSpace_def`. That equation cannot be used with `rw` here: the opens, their
restrictions, and `affinoidOpens` all have types depending on `closedPolydiscPreAdicSpace k P`,
so the rewrite motive is not type correct. -/

/-- A basic rational open of the closed-polydisc pre-adic space. -/
noncomputable def closedPolydiscBasicOpen
    (T : Finset (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
      isWeightFamily_one_weight))
    (s : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
      isWeightFamily_one_weight) : Opens (closedPolydiscPreAdicSpace k P) :=
  spaBasicOpen (powerBoundedSubring _) T s

omit [IsUltrametricDist K] [CompleteSpace K] [IsTateRing K] in
/-- A rational open of the closed polydisc whose numerators span an open ideal is an open
affinoid subspace. -/
theorem closedPolydiscBasicOpen_mem_affinoidOpens
    {T : Finset (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
      isWeightFamily_one_weight)}
    {s : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
      isWeightFamily_one_weight}
    (hT : IsOpen
      (Ideal.span (T : Set (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
        isWeightFamily_one_weight)) :
        Set (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
          isWeightFamily_one_weight))) :
    closedPolydiscBasicOpen k P T s ∈ (closedPolydiscPreAdicSpace k P).affinoidOpens :=
  spaBasicOpen_mem_affinoidOpens _ _ _ _ hT

open PairOfDefinition in
/-- **The coordinate ring of an admissible rational open of the closed polydisc.** Restricting
the closed polydisc to `R(T/s)`, for numerators spanning an open ideal, gives the
presentation-limit pre-adic space of the completed rational localisation `A⟨T/s⟩`, where `A` is
the restricted-series ring. -/
noncomputable def closedPolydiscBasicOpenIso
    {T : Finset (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
      isWeightFamily_one_weight)}
    {s : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
      isWeightFamily_one_weight}
    (hT : IsOpen
      (Ideal.span (T : Set (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
        isWeightFamily_one_weight)) :
        Set (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
          isWeightFamily_one_weight))) :
    letI Q := P.weighted (T := fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight
    letI hden := hasDenominatorPower_of_isOpen_span Q T s (Localization.Away s) hT
    letI := locUniformSpace Q T s (Localization.Away s) hden
    letI := isUniformAddGroup_locUniformSpace Q T s (Localization.Away s) hden
    letI := isTopologicalRing_locUniformSpace Q T s (Localization.Away s) hden
    (closedPolydiscPreAdicSpace k P).restrict (closedPolydiscBasicOpen k P T s).isOpenEmbedding ≅
      presentationLimitPreAdicSpace (completionLocalization Q T s (Localization.Away s) hden)
        (completedPlusSubring Q (powerBoundedSubring _) T s (Localization.Away s) hden)
        (isPowerBounded_of_mem_completedPlusSubring Q (powerBoundedSubring _)
          (fun _ ha ↦ mem_powerBoundedSubring.mp ha) T s (Localization.Away s) hden)
        (completionLocalization_ringOfDefinition_le_completedPlusSubring Q (powerBoundedSubring _)
          Q.le_powerBoundedSubring T s (Localization.Away s) hden) := by
  letI Q := P.weighted (T := fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight
  letI hden := hasDenominatorPower_of_isOpen_span Q T s (Localization.Away s) hT
  letI := locUniformSpace Q T s (Localization.Away s) hden
  letI := isUniformAddGroup_locUniformSpace Q T s (Localization.Away s) hden
  letI := isTopologicalRing_locUniformSpace Q T s (Localization.Away s) hden
  -- Transport `presentationLimitPreAdicSpaceLocIso` through `closedPolydiscPreAdicSpace_def`.
  have hrange : Set.range (Opens.inclusion' (spaBasicOpen (powerBoundedSubring _) T s)) =
      Set.range (spaComapLocHom Q (powerBoundedSubring _) T s _ hden) := by
    rw [Opens.set_range_inclusion', coe_spaComapLocHom,
      range_spaComapLoc Q _ Q.le_powerBoundedSubring T s _ hden]
  exact ((presentationLimitPreAdicSpace Q (powerBoundedSubring _)
      (fun _ ha ↦ mem_powerBoundedSubring.mp ha) Q.le_powerBoundedSubring).restrictIsoOfRangeEq
      (spaBasicOpen (powerBoundedSubring _) T s).isOpenEmbedding
      (isOpenEmbedding_spaComapLocHom Q (powerBoundedSubring _) Q.le_powerBoundedSubring T s _
        hden) hrange ≪≫
    presentationLimitPreAdicSpaceLocIso Q (powerBoundedSubring _) T s _ hden
      (fun _ ha ↦ mem_powerBoundedSubring.mp ha) Q.le_powerBoundedSubring hT :)

omit [IsUltrametricDist K] [CompleteSpace K] [IsTateRing K] in
/-- The topological space underlying `closedPolydiscPreAdicSpace` is the closed polydisc
`Spa(K⟨T₁, …, Tₖ⟩, K⟨T₁, …, Tₖ⟩°)`. -/
@[simp]
theorem closedPolydiscPreAdicSpace_carrier :
    ((closedPolydiscPreAdicSpace k P).toPresheafedSpace : TopCat) =
      TopCat.of ↥(closedPolydisc k K) := by
  rw [closedPolydiscPreAdicSpace_def, presentationLimitPreAdicSpace_carrier,
    closedPolydisc_def]

/-- The points of the closed-polydisc pre-adic space are the points of the closed polydisc. On
underlying valuations this is the identity. -/
noncomputable def closedPolydiscPreAdicSpaceHomeomorph :
    closedPolydiscPreAdicSpace k P ≃ₜ closedPolydisc k K :=
  Homeomorph.setCongr (closedPolydisc_def k K).symm

omit [IsUltrametricDist K] [CompleteSpace K] [IsTateRing K] in
/-- A point lies in the basic rational open `R(T/s)` of the closed-polydisc pre-adic space
exactly when the corresponding point of the closed polydisc lies in `R(T/s)`. -/
@[simp]
theorem mem_closedPolydiscBasicOpen
    {T : Finset (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
      isWeightFamily_one_weight)}
    {s : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
      isWeightFamily_one_weight} {x : closedPolydiscPreAdicSpace k P} :
    x ∈ closedPolydiscBasicOpen k P T s ↔
      (closedPolydiscPreAdicSpaceHomeomorph k P x : Spv _) ∈
        rationalSubset (powerBoundedSubring _) T s :=
  mem_spaBasicOpen

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

/-! ### Complete rank-one nonarchimedean fields

A complete nontrivially normed field with an ultrametric norm is a Tate ring, hence
nonarchimedean, by instances, so both results apply to it. -/

example {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PairOfDefinition K) :
    PreAdicSpace.isAdic
      (presentationLimitPreAdicSpace P (powerBoundedSubring K)
        (fun _ ha ↦ mem_powerBoundedSubring.mp ha) P.le_powerBoundedSubring) :=
  isAdic_spa_powerBounded_of_normedField P

example (k : ℕ) {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PairOfDefinition K) :
    PreAdicSpace.isAdic (closedPolydiscPreAdicSpace k P) :=
  isAdic_closedPolydiscPreAdicSpace k P

end TauCeti.ValuationSpectrum

end
