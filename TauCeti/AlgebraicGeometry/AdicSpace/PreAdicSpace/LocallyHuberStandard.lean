/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Analytic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyNoetherian
public import TauCeti.RingTheory.Huber.NoetherianType.HuberStandard

import TauCeti.RingTheory.Huber.LocalizationTopology.Noetherian
import TauCeti.RingTheory.Huber.NoetherianType.Tate

/-!
# Adic spaces locally of Huber's standing class

Huber's theory of unramified, smooth, and étale morphisms of adic spaces is developed over adic
spaces covered by open affinoids whose coordinate rings belong to Huber's standing class
(`TauCeti.Huber.IsHuberStandard`, Huber 1996, (1.1.1)): Huber rings that are finite type over a
noetherian ring of definition, are strongly noetherian Tate rings, or carry the discrete topology.
No condition is placed on the plus rings beyond being rings of integral elements.

An object of `𝒱^pre` is an *affinoid of Huber's standing class*
(`TauCeti.PreAdicSpace.isHuberStandardAffinoid`) when it is isomorphic to `Spa(A, A⁺)` for a
complete Hausdorff Huber pair with `A` in Huber's standing class (completeness and Hausdorffness are
imposed by this affinoid predicate rather than by `IsHuberStandard`), and an adic space `X` is
*locally of Huber's standing class* (`TauCeti.AdicSpace.IsLocallyHuberStandard`) when every point of
`X` has an open neighbourhood of this form (`TauCeti.PreAdicSpace.huberStandardAffinoidOpens`).

Since Huber's standing class is contained in the class of rings of noetherian type, every adic space
locally of Huber's standing class is locally noetherian. Rational localisation preserves Huber's
standing class
(`TauCeti.Huber.PairOfDefinition.isHuberStandard_completion_locTopology_of_isHuberStandard`), so the
open affinoids of Huber's standing class form a basis of `Spa(A, A⁺)` when `A` is in Huber's
standing class, and therefore form a basis of every adic space locally of Huber's standing class.
Open subspaces of adic spaces locally of Huber's standing class remain locally of Huber's standing
class.

Around an analytic point, the two finiteness conditions agree. Any analytic point of a
noetherian-type adic spectrum `Spa(A, A⁺)` lies in a standard rational chart `R(G/g)` where `g`
becomes a pseudouniformiser, so `A⟨G/g⟩` is a Tate ring of noetherian type and therefore belongs to
Huber's standing class (`TauCeti.Huber.isHuberStandard_iff_isNoetherianType`). Consequently, on an
analytic adic space `IsLocallyHuberStandard` and `IsLocallyNoetherian` are equivalent, and the
analytic locus `X_a` of any locally noetherian adic space `X` is locally of Huber's standing class.

## Main definitions

* `TauCeti.PreAdicSpace.isHuberStandardAffinoid`: the objects of `𝒱^pre` isomorphic to `Spa(A, A⁺)`
  for a complete Hausdorff Huber pair with `A` in Huber's standing class.
* `TauCeti.PreAdicSpace.huberStandardAffinoidOpens`: the open affinoids of Huber's standing class.
* `TauCeti.AdicSpace.IsLocallyHuberStandard`: adic spaces locally of Huber's standing class.

## Main results

* `TauCeti.ValuationSpectrum.isBasis_huberStandardAffinoidOpens_presentationLimitPreAdicSpace`: for
  `A` in Huber's standing class, the open affinoids of Huber's standing class form a basis of
  `Spa(A, A⁺)`.
* `TauCeti.AdicSpace.IsLocallyHuberStandard.isLocallyNoetherian`: every adic space locally of
  Huber's standing class is locally noetherian.
* `TauCeti.AdicSpace.IsLocallyHuberStandard.isBasis_huberStandardAffinoidOpens` and
  `TauCeti.AdicSpace.isLocallyHuberStandard_iff_isBasis_huberStandardAffinoidOpens`: on an adic
  space locally of Huber's standing class, the open affinoids of Huber's standing class form a basis
  of the topology, and conversely.
* `TauCeti.AdicSpace.IsLocallyHuberStandard.of_isOpenImmersion`: the source of an open immersion
  into an adic space locally of Huber's standing class is locally of Huber's standing class.
* `TauCeti.AdicSpace.IsLocallyHuberStandard.spa`: sheafy `Spa(A, A⁺)` is locally of Huber's
  standing class when `A` is in Huber's standing class.
* `TauCeti.AdicSpace.isLocallyHuberStandard_iff_isLocallyNoetherian_of_analyticPoints_eq_univ`: on
  an analytic adic space, `IsLocallyHuberStandard` and `IsLocallyNoetherian` agree.
* `TauCeti.AdicSpace.IsLocallyNoetherian.isLocallyHuberStandard_analyticLocus`: the analytic locus
  of a locally noetherian adic space is locally of Huber's standing class.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), (1.1.1) and §1.1.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 6.37, Remark 8.8, and
  Remark 8.37.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber ValuationSpectrum

universe u

namespace PreAdicSpace

/-! ### Affinoids of Huber's standing class -/

/-- An object of `𝒱^pre` is an *affinoid of Huber's standing class* when it is isomorphic to the
presentation-limit pre-adic space `Spa(A, A⁺)` of a complete Hausdorff Huber pair whose ring `A`
belongs to Huber's standing class (`TauCeti.Huber.IsHuberStandard`). -/
def isHuberStandardAffinoid : ObjectProperty PreAdicSpace.{u} := fun X ↦
  ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
    (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsHuberRing A)
    (_ : IsHuberStandard A) (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus),
    Nonempty (X ≅ presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)

/-- Unfolding lemma for `TauCeti.PreAdicSpace.isHuberStandardAffinoid`. -/
theorem isHuberStandardAffinoid_iff (X : PreAdicSpace.{u}) : isHuberStandardAffinoid X ↔
    ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
      (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsHuberRing A)
      (_ : IsHuberStandard A) (S : Pair A) (P : PairOfDefinition A)
      (hP : P.ringOfDefinition ≤ S.plus),
      Nonempty (X ≅ presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
  Iff.rfl

/-- Being an affinoid of Huber's standing class is invariant under isomorphism in `𝒱^pre`. -/
instance isHuberStandardAffinoid.instIsClosedUnderIsomorphisms :
    isHuberStandardAffinoid.{u}.IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨A, iA, uA, hgA, htA, hcA, h2A, hA, hsA, S, P, hP, ⟨e'⟩⟩ ↦
    ⟨A, iA, uA, hgA, htA, hcA, h2A, hA, hsA, S, P, hP, ⟨e.symm ≪≫ e'⟩⟩

/-- An affinoid of Huber's standing class is an affinoid of noetherian type. -/
theorem isHuberStandardAffinoid.isNoetherianAffinoid {X : PreAdicSpace.{u}}
    (hX : isHuberStandardAffinoid X) : isNoetherianAffinoid X := by
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, e⟩ := hX
  have := IsHuberStandard.isNoetherianType (A := A)
  exact (isNoetherianAffinoid_iff X).mpr ⟨A, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP, e⟩

/-- An affinoid of Huber's standing class is affinoid. -/
theorem isHuberStandardAffinoid.isAffinoid {X : PreAdicSpace.{u}}
    (hX : isHuberStandardAffinoid X) : isAffinoid X :=
  hX.isNoetherianAffinoid.isAffinoid

/-- The presentation-limit pre-adic space of a complete Hausdorff Huber pair whose ring is in
Huber's standing class is an affinoid of Huber's standing class. -/
theorem isHuberStandardAffinoid_presentationLimitPreAdicSpace {A : Type u} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T2Space A]
    [IsHuberRing A] [IsHuberStandard A] (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus) :
    isHuberStandardAffinoid (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
  ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, ⟨Iso.refl _⟩⟩

variable (X : PreAdicSpace.{u})

/-- The *open affinoids of Huber's standing class* of an object `X` of `𝒱^pre`: the opens `U` such
that `X` restricted to `U` is an affinoid of Huber's standing class. -/
abbrev huberStandardAffinoidOpens : Set (Opens X) :=
  X.propOpens isHuberStandardAffinoid

variable {X}

/-- An open affinoid of Huber's standing class is an open affinoid of noetherian type. -/
theorem huberStandardAffinoidOpens_subset_noetherianAffinoidOpens :
    X.huberStandardAffinoidOpens ⊆ X.noetherianAffinoidOpens :=
  fun _ hU ↦ (mem_propOpens_iff _).mpr
    (isHuberStandardAffinoid.isNoetherianAffinoid ((mem_propOpens_iff _).mp hU))

/-- An open affinoid of Huber's standing class is an open affinoid subspace. -/
theorem huberStandardAffinoidOpens_subset_affinoidOpens :
    X.huberStandardAffinoidOpens ⊆ X.affinoidOpens :=
  huberStandardAffinoidOpens_subset_noetherianAffinoidOpens.trans
    noetherianAffinoidOpens_subset_affinoidOpens

end PreAdicSpace

namespace ValuationSpectrum

open PairOfDefinition

section HuberStandard

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [IsHuberStandard A] (P : PairOfDefinition A) (Aplus : Subring A)
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)

/-- **Rational subsets of `Spa(A, A⁺)` for `A` in Huber's standing class are open affinoids of
Huber's standing class.** For `T` spanning an open ideal, the restriction of `Spa(A, A⁺)` to
`R(T/s)` is `Spa(A⟨T/s⟩, A_U⁺)` (`restrictSpaBasicOpenIso`), and `A⟨T/s⟩` is a complete Hausdorff
Huber ring in Huber's standing class. The ring `A` itself need not be complete. -/
theorem spaBasicOpen_mem_huberStandardAffinoidOpens {T : Finset A} {s : A}
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) :
    spaBasicOpen Aplus T s ∈
      (presentationLimitPreAdicSpace P Aplus hAplus hP).huberStandardAffinoidOpens := by
  have hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  let _ := locUniformSpace P T s _ hden
  have _ := isUniformAddGroup_locUniformSpace P T s _ hden
  have _ := isTopologicalRing_locUniformSpace P T s _ hden
  have _ := isHuberRing_completion_locTopology P T s _ hden
  have _ := isHuberStandard_completion_locTopology_of_isHuberStandard P
    (Ideal.isOpen_of_isOpen_subideal (Ideal.span_mono (Set.subset_insert _ _)) hT) _ hden
  exact spaBasicOpen_mem_propOpens P Aplus T s _ hden hAplus hP hT
    PreAdicSpace.isHuberStandardAffinoid
    (PreAdicSpace.isHuberStandardAffinoid_presentationLimitPreAdicSpace _ _ _)

/-- **The open affinoids of Huber's standing class form a basis of `Spa(A, A⁺)`** when `A` is in
Huber's standing class, since the rational opens do. -/
theorem isBasis_huberStandardAffinoidOpens_presentationLimitPreAdicSpace :
    Opens.IsBasis (presentationLimitPreAdicSpace P Aplus hAplus hP).huberStandardAffinoidOpens := by
  refine Opens.isBasis_iff_nbhd.mpr fun {U x} hx ↦ ?_
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens Aplus) hx
  obtain ⟨T, s, hT, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hV
  exact ⟨_, spaBasicOpen_mem_huberStandardAffinoidOpens P Aplus hAplus hP hT, hxV, hVU⟩

end HuberStandard

section Analytic

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [IsNoetherianType A] (P : PairOfDefinition A) (Aplus : Subring A)
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)

/-- **Every analytic point of a noetherian-type `Spa(A, A⁺)` has an open affinoid neighbourhood of
Huber's standing class.** An analytic point lies in a standard rational chart `R(G/g)` with `g` in
an ideal of definition; the completed localisation `A⟨G/g⟩` is then a Tate ring of noetherian type,
hence in Huber's standing class (`isHuberStandard_iff_isNoetherianType`). -/
theorem exists_mem_huberStandardAffinoidOpens_of_mem_analyticPoints_presentationLimitPreAdicSpace
    {x : presentationLimitPreAdicSpace P Aplus hAplus hP}
    (hx : x ∈ (presentationLimitPreAdicSpace P Aplus hAplus hP).analyticPoints) :
    ∃ U ∈ (presentationLimitPreAdicSpace P Aplus hAplus hP).huberStandardAffinoidOpens, x ∈ U := by
  rw [analyticPoints_presentationLimitPreAdicSpace] at hx
  obtain ⟨T, g, hT, hxg, hnil⟩ :=
    exists_mem_rationalSubset_isTopologicallyNilpotent_of_mem_spaAnalytic P Aplus hx
  let L := Localization.Away g
  have hden := P.hasDenominatorPower_of_isOpen_span T g L hT
  let _ := locUniformSpace P T g L hden
  have _ := isUniformAddGroup_locUniformSpace P T g L hden
  have _ := isTopologicalRing_locUniformSpace P T g L hden
  have _ := isHuberRing_completion_locTopology P T g L hden
  have _ := isTateRing_completion_locTopology_of_isTopologicallyNilpotent P T g L hden hnil
  have _ := isNoetherianType_completion_locTopology_of_isNoetherianType P
    (Ideal.isOpen_of_isOpen_subideal (Ideal.span_mono (Set.subset_insert _ _)) hT) L hden
  have _ : IsHuberStandard (UniformSpace.Completion L) :=
    isHuberStandard_iff_isNoetherianType.mpr inferInstance
  exact ⟨spaBasicOpen Aplus T g,
    spaBasicOpen_mem_propOpens P Aplus T g L hden hAplus hP hT
      PreAdicSpace.isHuberStandardAffinoid
      (PreAdicSpace.isHuberStandardAffinoid_presentationLimitPreAdicSpace _ _ _),
    mem_spaBasicOpen.mpr hxg⟩

end Analytic

end ValuationSpectrum

namespace PreAdicSpace

/-- **On an affinoid of Huber's standing class the open affinoids of Huber's standing class form a
basis.** -/
theorem isHuberStandardAffinoid.isBasis_huberStandardAffinoidOpens {X : PreAdicSpace.{u}}
    (hX : isHuberStandardAffinoid X) : Opens.IsBasis X.huberStandardAffinoidOpens :=
  let ⟨_, _, _, _, _, _, _, _, _, S, P, hP, ⟨e⟩⟩ := hX
  isBasis_propOpens_of_iso isHuberStandardAffinoid e
    (isBasis_huberStandardAffinoidOpens_presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)

end PreAdicSpace

/-! ### Adic spaces locally of Huber's standing class -/

namespace AdicSpace

open PreAdicSpace

/-- **Adic spaces locally of Huber's standing class** (Huber 1996, (1.1.1) and §1.1): an adic space
`X` is *locally of Huber's standing class* when every point has an open affinoid neighbourhood of
Huber's standing class, that is, an open `U` with `X|_U ≅ Spa(A, A⁺)` for a complete Hausdorff Huber
pair with `A` in Huber's standing class (`TauCeti.Huber.IsHuberStandard`). -/
def IsLocallyHuberStandard (X : AdicSpace.{u}) : Prop :=
  ∀ x : X.obj, ∃ U ∈ X.obj.huberStandardAffinoidOpens, x ∈ U

variable {X Y : AdicSpace.{u}}

/-- Unfolding lemma for `TauCeti.AdicSpace.IsLocallyHuberStandard`. -/
theorem isLocallyHuberStandard_iff :
    X.IsLocallyHuberStandard ↔ ∀ x : X.obj, ∃ U ∈ X.obj.huberStandardAffinoidOpens, x ∈ U :=
  Iff.rfl

/-- **Every adic space locally of Huber's standing class is locally noetherian.** -/
theorem IsLocallyHuberStandard.isLocallyNoetherian (hX : X.IsLocallyHuberStandard) :
    X.IsLocallyNoetherian :=
  isLocallyNoetherian_iff.mpr fun x ↦
    let ⟨U, hU, hxU⟩ := hX x
    ⟨U, huberStandardAffinoidOpens_subset_noetherianAffinoidOpens hU, hxU⟩

/-- **The open affinoids of Huber's standing class form a basis of the topology** on an adic space
locally of Huber's standing class. -/
theorem IsLocallyHuberStandard.isBasis_huberStandardAffinoidOpens
    (hX : X.IsLocallyHuberStandard) : Opens.IsBasis X.obj.huberStandardAffinoidOpens :=
  isBasis_propOpens isHuberStandardAffinoid
    (fun _ ↦ isHuberStandardAffinoid.isBasis_huberStandardAffinoidOpens) hX

/-- An adic space is locally of Huber's standing class exactly when its open affinoids of Huber's
standing class form a basis of its topology. -/
theorem isLocallyHuberStandard_iff_isBasis_huberStandardAffinoidOpens :
    X.IsLocallyHuberStandard ↔ Opens.IsBasis X.obj.huberStandardAffinoidOpens :=
  ⟨IsLocallyHuberStandard.isBasis_huberStandardAffinoidOpens, exists_mem_propOpens_of_isBasis⟩

/-- **Open subspaces of adic spaces locally of Huber's standing class are locally of Huber's
standing class**: the source of an open immersion into an adic space locally of Huber's standing
class is locally of Huber's standing class. In particular, being locally of Huber's standing class
is invariant under isomorphism. -/
theorem IsLocallyHuberStandard.of_isOpenImmersion (f : Y ⟶ X) [IsOpenImmersion f.hom]
    (hX : X.IsLocallyHuberStandard) : Y.IsLocallyHuberStandard :=
  exists_mem_propOpens_of_iso isHuberStandardAffinoid (IsOpenImmersion.isoRestrict f.hom)
    (exists_mem_propOpens_restrict f.hom.isOpenEmbedding isHuberStandardAffinoid
      hX.isBasis_huberStandardAffinoidOpens)

section Spa

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [IsHuberStandard A] (P : PairOfDefinition A) (Aplus : Subring A)
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)

/-- **`Spa(A, A⁺)` is locally of Huber's standing class** when `A` is in Huber's standing class and
the structure presheaf is a sheaf. Neither completeness of `A` nor any condition on `A⁺` beyond
being a plus ring of power-bounded elements containing a ring of definition is needed. -/
theorem IsLocallyHuberStandard.spa
    (hs : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus)) :
    IsLocallyHuberStandard ⟨presentationLimitPreAdicSpace P Aplus hAplus hP,
      isAdic_presentationLimitPreAdicSpace P Aplus hAplus hP hs⟩ :=
  isLocallyHuberStandard_iff_isBasis_huberStandardAffinoidOpens.mpr
    (isBasis_huberStandardAffinoidOpens_presentationLimitPreAdicSpace P Aplus hAplus hP)

end Spa

/-! ### Comparison on analytic points and the analytic locus -/

/-- **Every analytic point of a locally noetherian adic space has an open affinoid neighbourhood of
Huber's standing class.** Choosing a noetherian affinoid chart around `x` reduces to
`exists_mem_huberStandardAffinoidOpens_of_mem_analyticPoints_presentationLimitPreAdicSpace`. -/
theorem IsLocallyNoetherian.exists_mem_huberStandardAffinoidOpens_of_mem_analyticPoints
    (hX : X.IsLocallyNoetherian) {x : X.obj} (hx : x ∈ X.obj.analyticPoints) :
    ∃ V ∈ X.obj.huberStandardAffinoidOpens, x ∈ V := by
  obtain ⟨U, hU, hxU⟩ := isLocallyNoetherian_iff.mp hX x
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, ⟨e⟩⟩ := (isNoetherianAffinoid_iff _).mp
    ((mem_propOpens_iff _).mp hU)
  have hx' : (⟨x, hxU⟩ : X.obj.restrict U.isOpenEmbedding) ∈
      (X.obj.restrict U.isOpenEmbedding).analyticPoints := by
    rw [analyticPoints_restrict]
    exact hx
  obtain ⟨W, hW, hxW⟩ :=
    exists_mem_huberStandardAffinoidOpens_of_mem_analyticPoints_presentationLimitPreAdicSpace
      P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP
      (mapsTo_analyticPoints_of_isOpenImmersion e.hom hx')
  have hW' : (Opens.map e.hom.base).obj W ∈
      (X.obj.restrict U.isOpenEmbedding).huberStandardAffinoidOpens :=
    (map_hom_base_mem_propOpens_iff isHuberStandardAffinoid e).mpr hW
  exact ⟨U.isOpenEmbedding.isOpenMap.functor.obj ((Opens.map e.hom.base).obj W),
    (mem_propOpens_restrict_iff X.obj U.isOpenEmbedding isHuberStandardAffinoid _).mp hW',
    ⟨x, hxU⟩, hxW, rfl⟩

/-- **An analytic locally noetherian adic space is locally of Huber's standing class.** When every
point of `X` is analytic (`X.obj.analyticPoints = Set.univ`), every point has a Tate rational
affinoid neighbourhood of noetherian type, whose coordinate ring is strongly noetherian and hence in
Huber's standing class. -/
theorem IsLocallyNoetherian.isLocallyHuberStandard_of_analyticPoints_eq_univ
    (ha : X.obj.analyticPoints = Set.univ) (hX : X.IsLocallyNoetherian) :
    X.IsLocallyHuberStandard :=
  fun x ↦ hX.exists_mem_huberStandardAffinoidOpens_of_mem_analyticPoints (ha ▸ Set.mem_univ x)

/-- **On an analytic adic space, `IsLocallyHuberStandard` and `IsLocallyNoetherian` coincide.** -/
theorem isLocallyHuberStandard_iff_isLocallyNoetherian_of_analyticPoints_eq_univ
    (ha : X.obj.analyticPoints = Set.univ) :
    X.IsLocallyHuberStandard ↔ X.IsLocallyNoetherian :=
  ⟨IsLocallyHuberStandard.isLocallyNoetherian,
    IsLocallyNoetherian.isLocallyHuberStandard_of_analyticPoints_eq_univ ha⟩

/-- **The analytic locus of a locally noetherian adic space is locally of Huber's standing class.**
The analytic locus `X_a` is an open subspace of `X`, hence locally noetherian, and all of its points
are analytic (`analyticPoints_analyticLocus`). -/
theorem IsLocallyNoetherian.isLocallyHuberStandard_analyticLocus (hX : X.IsLocallyNoetherian) :
    X.analyticLocus.IsLocallyHuberStandard :=
  (hX.of_isOpenImmersion (analyticLocus.ι X)).isLocallyHuberStandard_of_analyticPoints_eq_univ
    (by rw [analyticLocus_obj, analyticPoints_analyticLocus])

end AdicSpace

end TauCeti
