/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Basic

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
import TauCeti.Topology.Algebra.IsUniformGroup.Quotient

/-!
# Algebras topologically of finite type are complete, separated and Tate

Let `φ : A → B` be a ring homomorphism topologically of finite type, so that `B` is presented by an
open quotient map `π` out of the completion of a weighted restricted power-series ring over `A`;
over a Tate ring `A` the presentation can be taken to be `π : A⟨X₁, …, Xₖ⟩ ↠ B`
(`TauCeti.Huber.IsTopologicallyFiniteType.isStrictlyTopologicallyFiniteType`). Only a topology is
asked of `B`. This file shows that `B` then has the structure that Wedhorn's definitions assume.

* Over a Huber ring, `B` is complete for every uniformity making it a uniform additive group, as an
  open quotient of a complete first countable group (`IsOpenQuotientMap.completeSpace`).
* Over a Tate ring, `B` is a Tate ring: the image of a ring of definition of `A⟨X₁, …, Xₖ⟩` is an
  open bounded subring of `B`, and the image of a pseudouniformiser of `A` is a pseudouniformiser
  of `B`.
* Over a strongly noetherian Tate ring, `A⟨X₁, …, Xₖ⟩` is a complete metrisable noetherian Tate
  ring, so every ideal of it is closed (`Ideal.isClosed_restrictedMvPowerSeriesCompletion`), the
  kernel of `π` among them. Hence `B` is Hausdorff, and it is noetherian.

Over a complete nonarchimedean field `k` these are Wedhorn's Propositions 5.58 and 5.59. A
topological `k`-algebra `B` is *topologically of finite type* (Wedhorn, Definition 5.57) when it
admits a continuous open surjection of `k`-algebras from the Tate algebra `Tₙ = k⟨X₁, …, Xₙ⟩`,
which is `IsTopologicallyFiniteType (algebraMap k B)`; such a `B` is complete, Hausdorff and
noetherian. Together with its power-bounded subring, `(B, B°)` (`TauCeti.Huber.Pair.powerBounded`)
is what Wedhorn's Definition 7.56 calls an affinoid `k`-algebra topologically of finite type, and
`TauCeti.ValuationSpectrum.isAdic_presentationLimitPreAdicSpace_of_isTopologicallyFiniteType`
makes its adic spectrum an affinoid adic space.

## Main results

* `TauCeti.Huber.IsTopologicallyFiniteType.completeSpace`: over a Huber ring, an algebra
  topologically of finite type is complete for any uniformity compatible with its additive group
  structure.
* `TauCeti.Huber.IsTopologicallyFiniteType.isTateRing`: over a Tate ring, it is a Tate ring.
* `TauCeti.Huber.IsTopologicallyFiniteType.t2Space`: over a strongly noetherian Tate ring, an
  algebra topologically of finite type is Hausdorff.
* `TauCeti.Huber.IsTopologicallyFiniteType.isNoetherianRing`: over a strongly noetherian Tate
  ring, it is noetherian.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 5.57,
  Propositions 5.58 and 5.59, Proposition 6.34, and Definition 7.56.
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.1.
-/

public section

open Topology UniformSpace
open scoped Uniformity

namespace TauCeti.Huber

/-- **An algebra topologically of finite type over a Huber ring is complete** (Wedhorn,
Proposition 5.58, over a field), for every uniformity making it a uniform additive group: it is an
open quotient of the completion of a weighted restricted power-series ring over `A`, a complete
first countable group. -/
theorem IsTopologicallyFiniteType.completeSpace {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] {B : Type*} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] {φ : A →+* B} (hφ : IsTopologicallyFiniteType φ) :
    CompleteSpace B := by
  obtain ⟨k, T, -, hT, π, hπ, -⟩ := isTopologicallyFiniteType_iff.mp hφ
  exact hπ.completeSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] {φ : A →+* B}

/-- **An algebra topologically of finite type over a Tate ring is a Tate ring** (the remark after
Wedhorn's Proposition 6.34). For a presentation `π : A⟨X₁, …, Xₖ⟩ ↠ B`, the image of a ring of
definition of `A⟨X₁, …, Xₖ⟩` is open and bounded in `B` because `π` is open, and `φ` carries a
pseudouniformiser of `A` to one of `B`. No completeness of `B` is needed. -/
theorem IsTopologicallyFiniteType.isTateRing (hφ : IsTopologicallyFiniteType φ) :
    IsTateRing B := by
  obtain ⟨k, π, hπ, rfl⟩ :=
    isStrictlyTopologicallyFiniteType_iff.mp hφ.isStrictlyTopologicallyFiniteType
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := restrictedMvPowerSeriesCompletion k A)
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  refine IsTateRing.of_isOpen_isBounded (P.ringOfDefinition.map π) ?_ ?_
    (hϖ.map (φ := π.comp (algebraMap A _))
      (hπ.continuous.comp (continuous_algebraMap_restrictedMvPowerSeriesCompletion k A)))
  · rw [Subring.coe_map]
    exact hπ.isOpenMap _ P.isOpen_ringOfDefinition
  · rw [Subring.coe_map]
    exact P.isBounded_ringOfDefinition.image_of_isOpenMap hπ.continuous.continuousAt hπ.isOpenMap

variable [IsStronglyNoetherian A]

omit [IsTopologicalRing B] in
/-- **An algebra topologically of finite type over a strongly noetherian Tate ring is Hausdorff**
(Wedhorn, Proposition 5.58, over a field): `{0}` is closed in it, because its preimage in
`A⟨X₁, …, Xₖ⟩` is an ideal, and every ideal there is closed. Only the additive group of `B` need
be topological. -/
theorem IsTopologicallyFiniteType.t2Space [IsTopologicalAddGroup B]
    (hφ : IsTopologicallyFiniteType φ) : T2Space B := by
  obtain ⟨k, π, hπ, -⟩ :=
    isStrictlyTopologicallyFiniteType_iff.mp hφ.isStrictlyTopologicallyFiniteType
  -- `{0}` is closed in `B`, since its preimage under the quotient map `π` is the closed kernel
  have h0 : IsClosed ({0} : Set B) := hπ.isQuotientMap.isClosed_preimage.mp
    (Ideal.isClosed_restrictedMvPowerSeriesCompletion (RingHom.ker π))
  have : T1Space B := IsTopologicalAddGroup.t1Space B h0
  infer_instance

omit [IsTopologicalRing B] in
/-- **An algebra topologically of finite type over a strongly noetherian Tate ring is noetherian**
(Wedhorn, Proposition 5.59, over a field): it is a quotient of the noetherian ring
`A⟨X₁, …, Xₖ⟩`. -/
theorem IsTopologicallyFiniteType.isNoetherianRing (hφ : IsTopologicallyFiniteType φ) :
    IsNoetherianRing B := by
  obtain ⟨k, π, hπ, -⟩ :=
    isStrictlyTopologicallyFiniteType_iff.mp hφ.isStrictlyTopologicallyFiniteType
  exact isNoetherianRing_of_surjective _ _ π hπ.surjective

end TauCeti.Huber
