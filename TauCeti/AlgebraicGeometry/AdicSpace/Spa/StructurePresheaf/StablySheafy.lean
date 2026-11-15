/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SheafyRing
public import TauCeti.RingTheory.Huber.LocalizationTopology.CompleteSeparated.Basic

import TauCeti.RingTheory.Huber.LocalizationTopology.WeightedEvaluation
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Cancel
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Comp

/-!
# Permanence of stable sheafiness under topological finite type and rational localisation

If `A` is a stably sheafy Huber ring (`TauCeti.Huber.IsStablySheafyRing`) and `φ : A →+* B` is a
ring homomorphism topologically of finite type (`TauCeti.Huber.IsTopologicallyFiniteType`) into a
uniform Huber ring `B`, then `B` is again stably sheafy: the induced homomorphism on completions
`Â →+* B̂` is topologically of finite type by composition and right-cancellation along the dense
completion maps `A →+* Â` and `B →+* B̂`, so any complete Hausdorff Huber ring topologically of
finite type over `B̂` is topologically of finite type over `Â` (`IsTopologicallyFiniteType.comp`)
and therefore sheafy (Wedhorn, Proposition 6.33 and Definition 8.26).

In particular, since the structure map `A →+* A⟨T/s⟩` of a rational localisation (for `T ∪ {s}`
spanning an open ideal) is topologically of finite type
(`TauCeti.Huber.PairOfDefinition.isTopologicallyFiniteType_toCompletionLoc`), every completed
rational localisation `A⟨T/s⟩` of a stably sheafy Huber ring is stably sheafy. Neither completeness
nor Hausdorffness of `A` is required.

## Main results

* `TauCeti.Huber.IsTopologicallyFiniteType.completion_mapRingHom`: if `φ : A →+* B` is topologically
  of finite type between uniform Huber rings, then so is `Completion.mapRingHom φ : Â →+* B̂`.
* `TauCeti.Huber.IsStablySheafyRing.of_isTopologicallyFiniteType`: stable sheafiness ascends along
  ring homomorphisms topologically of finite type between uniform Huber rings.
* `TauCeti.Huber.isStablySheafyRing_congr_topology`: stable sheafiness depends only on the topology
  induced by the uniform additive group structure.
* `TauCeti.Huber.PairOfDefinition.isStablySheafyRing_completion_locTopology`: completed rational
  localisations `A⟨T/s⟩` of a stably sheafy Huber ring are stably sheafy.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 6.33,
  Definition 8.26, and Remark 8.27.
-/

public section

open UniformSpace

namespace TauCeti.Huber

universe u v w

/-- **Completion preserves topological finite type between uniform Huber rings**: if `φ : A →+* B`
is topologically of finite type between uniform Huber rings, then the induced map
`Completion.mapRingHom φ : Â →+* B̂` is topologically of finite type. -/
theorem IsTopologicallyFiniteType.completion_mapRingHom
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [IsHuberRing A]
    {B : Type w} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [IsHuberRing B]
    {φ : A →+* B} (hφ : IsTopologicallyFiniteType φ) :
    IsTopologicallyFiniteType (Completion.mapRingHom φ hφ.continuous) := by
  have hcomp : (Completion.mapRingHom φ hφ.continuous).comp Completion.coeRingHom =
      (Completion.coeRingHom : B →+* Completion B).comp φ :=
    RingHom.ext fun a ↦ Completion.mapRingHom_coe hφ.continuous a
  have htft : IsTopologicallyFiniteType ((Completion.coeRingHom : B →+* Completion B).comp φ) :=
    isStrictlyTopologicallyFiniteType_coeRingHom.isTopologicallyFiniteType.comp hφ
  rw [← hcomp] at htft
  exact htft.of_comp (Completion.uniformContinuous_coe A).continuous
    (Completion.uniformContinuous_extension).continuous

/-- **Stable sheafiness ascends along homomorphisms topologically of finite type** (Wedhorn,
Proposition 6.33(1) and Definition 8.26): if `A` is stably sheafy and `φ : A →+* B` is topologically
of finite type into a uniform Huber ring `B`, then `B` is stably sheafy. Neither completeness nor
Hausdorffness of `A` or `B` is required, and the test universe `v` is preserved unchanged. -/
theorem IsStablySheafyRing.of_isTopologicallyFiniteType
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [IsHuberRing A]
    {B : Type w} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [IsHuberRing B]
    {φ : A →+* B} (hφ : IsTopologicallyFiniteType φ) (hA : IsStablySheafyRing.{u, v} A) :
    IsStablySheafyRing.{w, v} B :=
  isStablySheafyRing_iff.mpr fun C _ _ _ _ _ _ _ ψ hψ ↦
    isStablySheafyRing_iff.mp hA C (ψ.comp (Completion.mapRingHom φ hφ.continuous))
      (hψ.comp hφ.completion_mapRingHom)

/-- **Stable sheafiness depends only on the topology**: two uniform additive group structures on the
same commutative ring with equal induced topologies are stably sheafy together. -/
theorem isStablySheafyRing_congr_topology {R : Type u} [CommRing R]
    {u₁ u₂ : UniformSpace R} [hg₁ : @IsUniformAddGroup R u₁ _]
    [ht₁ : @IsTopologicalRing R u₁.toTopologicalSpace _]
    [hh₁ : @IsHuberRing R _ u₁.toTopologicalSpace ht₁]
    [hg₂ : @IsUniformAddGroup R u₂ _]
    [ht₂ : @IsTopologicalRing R u₂.toTopologicalSpace _]
    [hh₂ : @IsHuberRing R _ u₂.toTopologicalSpace ht₂]
    (ht : u₁.toTopologicalSpace = u₂.toTopologicalSpace) :
    @IsStablySheafyRing.{u, v} R _ u₁ hg₁ ht₁ hh₁ ↔
      @IsStablySheafyRing.{u, v} R _ u₂ hg₂ ht₂ hh₂ :=
  @isStablySheafyRing_iff_of_ringEquiv.{u, v, u} R _ u₁ hg₁ ht₁ hh₁ R _ u₂ hg₂ ht₂ hh₂
    (RingEquiv.refl R)
    (@continuous_def R R u₁.toTopologicalSpace u₂.toTopologicalSpace _ |>.mpr fun _ hs ↦ ht ▸ hs)
    (@continuous_def R R u₂.toTopologicalSpace u₁.toTopologicalSpace _ |>.mpr fun _ hs ↦
      ht.symm ▸ hs)

/-- **Rational localisation preserves stable sheafiness** (Wedhorn, Remark 8.27): if `A` is a stably
sheafy Huber ring and `T ∪ {s}` spans an open ideal of `A`, then the completed rational localisation
`A⟨T/s⟩` is stably sheafy, regardless of the pair of definition `P` used to form its topology and
without completeness or Hausdorffness hypotheses on `A`. -/
theorem PairOfDefinition.isStablySheafyRing_completion_locTopology
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [IsHuberRing A] (P : PairOfDefinition A) {T : Finset A} {s : A}
    (hT : IsOpen (Ideal.span (insert s (T : Set A)) : Set A))
    (S : Type w) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : P.HasDenominatorPower T s S) (hA : IsStablySheafyRing.{u, v} A) :
    letI := P.locUniformSpace T s S hden
    letI := P.isUniformAddGroup_locUniformSpace T s S hden
    letI := P.isTopologicalRing_locUniformSpace T s S hden
    letI := P.isHuberRing_completion_locTopology T s S hden
    IsStablySheafyRing.{w, v} (Completion S) :=
  letI := P.locUniformSpace T s S hden
  letI := P.isUniformAddGroup_locUniformSpace T s S hden
  letI := P.isTopologicalRing_locUniformSpace T s S hden
  letI := P.isHuberRing_completion_locTopology T s S hden
  hA.of_isTopologicallyFiniteType (P.isTopologicallyFiniteType_toCompletionLoc T s S hden hT)

end TauCeti.Huber

end
