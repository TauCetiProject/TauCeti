/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.PresentationLimit
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Analytic

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Cofinality
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.Basic

/-!
# Analytic points and the analytic locus of a pre-adic space

A point `x` of a pre-adic space `X` is *analytic* if some open neighbourhood `U` of `x` has a
pseudouniformiser, a topologically nilpotent unit, in `𝒪_X(U)`. This is the intrinsic form of
Huber's analytic points, which on an affinoid `Spa(A, A⁺)` are the points whose support is not
open. The analytic points form an open subset by definition, and they are compatible with
restriction to open subspaces.

On the adic spectrum `Spa(A, A⁺)` with its presentation-limit structure presheaf the two notions
agree. A section of a neighbourhood of `x` which is a pseudouniformiser restricts to one of a
completed rational localisation `A⟨T/s⟩` with `x ∈ R(T/s)`, and `A → A⟨T/s⟩` is adic, so `x` is
analytic in Huber's sense
(`TauCeti.ValuationSpectrum.rationalSubset_subset_spaAnalytic_of_isTateRing`).
Conversely an analytic point lies in a chart `R(G/g)` of the standard rational cover of the
analytic locus, `g` running over generators of an ideal of definition, and the image of `g` is a
pseudouniformiser of the sections `A⟨G/g⟩` over that chart.

Every morphism of pre-adic spaces pulls analytic points back to analytic points, since its maps
on sections are continuous and so preserve pseudouniformisers; the converse inclusion is what a
morphism must satisfy to restrict to analytic loci.

The *analytic locus* `X_a` is the open subspace of `X` on its analytic points (Wedhorn,
Remark 8.37), with its inclusion `analyticLocus.ι : X_a ⟶ X`, an open immersion. Every point of
`X_a` is analytic, `ι` is an isomorphism exactly when every point of `X` is analytic, and a
morphism into `X` factors through `X_a` exactly when its image consists of analytic points. A
morphism sending analytic points to analytic points restricts to the analytic loci, functorially;
by Wedhorn, Proposition 8.39, adic morphisms are of this kind. The analytic locus of an adic space
is an open adic subspace, `TauCeti.AdicSpace.analyticLocus`. It is the setting in which
constructions on Tate affinoids, such as completed tensor products, apply to non-Tate spaces like
`Spa(ℤ_p⟦T⟧)`.

## Main definitions

* `TauCeti.PreAdicSpace.analyticPoints`: the analytic points of a pre-adic space.
* `TauCeti.PreAdicSpace.analyticLocus`, `TauCeti.PreAdicSpace.analyticLocus.ι`: the analytic
  locus `X_a` and its inclusion into `X`.
* `TauCeti.PreAdicSpace.analyticLocus.lift`: the factorisation through `X_a` of a morphism whose
  image consists of analytic points.
* `TauCeti.PreAdicSpace.analyticLocusMap`: the restriction `Y_a ⟶ X_a` of a morphism `Y ⟶ X`
  sending analytic points to analytic points.
* `TauCeti.AdicSpace.analyticLocus`, `TauCeti.AdicSpace.analyticLocus.ι`: the analytic locus of an
  adic space, as an adic space, and its inclusion.

## Main results

* `TauCeti.PreAdicSpace.isOpen_analyticPoints`: the analytic points form an open subset.
* `TauCeti.PreAdicSpace.analyticPoints_restrict`: the analytic points of the restriction of `X`
  along an open embedding `f` are the preimage under `f` of those of `X`.
* `TauCeti.ValuationSpectrum.analyticPoints_presentationLimitPreAdicSpace`: the analytic points of
  `Spa(A, A⁺)` are the points of its analytic locus `Spa(A, A⁺)ᵃ`.
* `TauCeti.PreAdicSpace.preimage_analyticPoints_subset`: a point over an analytic point is
  analytic.
* `TauCeti.PreAdicSpace.analyticPoints_analyticLocus`: every point of `X_a` is analytic.
* `TauCeti.PreAdicSpace.isIso_analyticLocus_ι_iff`: `X_a ⟶ X` is an isomorphism exactly when
  every point of `X` is analytic.
* `TauCeti.PreAdicSpace.analyticLocus.exists_comp_ι_eq_iff`: a morphism factors through `X_a`
  exactly when its image consists of analytic points.
* `TauCeti.PreAdicSpace.analyticLocusMap_id`, `TauCeti.PreAdicSpace.analyticLocusMap_comp`:
  restriction to analytic loci is functorial.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 7.39,
  Proposition 7.49, Proposition and Definition 8.36, Remark 8.37 and Proposition 8.39.
* [R. Huber, *A generalization of formal schemes and rigid analytic varieties*], §3.
-/

public section

open CategoryTheory TopologicalSpace Opposite Topology

namespace TauCeti

open Huber

universe u

namespace PreAdicSpace

variable (X : PreAdicSpace.{u})

/-- **Analytic points of a pre-adic space** (Wedhorn, Proposition and Definition 8.36): the points
`x` having an open neighbourhood `U` such that `𝒪_X(U)` contains a pseudouniformiser, that is, a
topologically nilpotent unit. On `Spa(A, A⁺)` these are the points whose support is not open
(`TauCeti.ValuationSpectrum.analyticPoints_presentationLimitPreAdicSpace`). -/
def analyticPoints : Set X :=
  {x | ∃ U : Opens X, x ∈ U ∧
    ∃ f : X.toPresheafedSpace.presheaf.obj (op U), IsPseudoUniformizer f}

variable {X}

/-- Unfolding lemma for `TauCeti.PreAdicSpace.analyticPoints`. -/
theorem mem_analyticPoints_iff {x : X} : x ∈ X.analyticPoints ↔ ∃ U : Opens X, x ∈ U ∧
    ∃ f : X.toPresheafedSpace.presheaf.obj (op U), IsPseudoUniformizer f :=
  Iff.rfl

/-- **The analytic points form an open subset** of a pre-adic space. -/
theorem isOpen_analyticPoints : IsOpen X.analyticPoints :=
  isOpen_iff_forall_mem_open.mpr fun _ ⟨U, hxU, f, hf⟩ ↦
    ⟨U, fun _ hy ↦ ⟨U, hy, f, hf⟩, U.isOpen, hxU⟩

/-- **Analytic points of an open subspace** (Wedhorn, Remark 8.37(2)): the analytic points of the
restriction of `X` along an open embedding `f` are the points that `f` sends to analytic points of
`X`. -/
@[simp]
theorem analyticPoints_restrict {U : TopCat.{u}} {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f) :
    (X.restrict h).analyticPoints = f ⁻¹' X.analyticPoints := by
  ext x
  refine ⟨fun ⟨V, hxV, g, hg⟩ ↦ ⟨h.isOpenMap.functor.obj V, ⟨x, hxV, rfl⟩, g, hg⟩, fun hx ↦ ?_⟩
  obtain ⟨W, hxW, g, hg⟩ := hx
  -- the preimage of `W` is a neighbourhood of `x` whose image lies in `W`
  have hle : h.isOpenMap.functor.obj ((Opens.map f).obj W) ≤ W :=
    Set.image_preimage_subset f W
  exact ⟨(Opens.map f).obj W, hxW, _,
    hg.map (X.toPresheafedSpace.presheaf.map (homOfLE hle).op).hom.2⟩

/-! ### Analytic points along morphisms -/

section Morphisms

variable {Y : PreAdicSpace.{u}}

/-- **A point over an analytic point is analytic**: a morphism of pre-adic spaces pulls the
analytic points of its target back into those of its source, because its maps on sections are
continuous ring homomorphisms, which send pseudouniformisers to pseudouniformisers. -/
theorem preimage_analyticPoints_subset (f : Y ⟶ X) :
    f.base ⁻¹' X.analyticPoints ⊆ Y.analyticPoints :=
  fun _ ⟨U, hxU, _, hg⟩ ↦ ⟨(Opens.map f.base).obj U, hxU, _, hg.map (f.c.app (op U)).hom.2⟩

/-- A morphism of pre-adic spaces sends analytic points to analytic points exactly when the
analytic points of its source are the preimage of those of its target. -/
theorem preimage_analyticPoints_eq_iff_mapsTo (f : Y ⟶ X) :
    f.base ⁻¹' X.analyticPoints = Y.analyticPoints ↔
      Set.MapsTo f.base Y.analyticPoints X.analyticPoints :=
  ⟨fun h ↦ Set.mapsTo_iff_subset_preimage.mpr h.ge,
    fun h ↦ (preimage_analyticPoints_subset f).antisymm (Set.mapsTo_iff_subset_preimage.mp h)⟩

end Morphisms

/-! ### The analytic locus -/

variable (X)

/-- **The analytic locus** `X_a` of a pre-adic space `X` (Wedhorn, Remark 8.37): the open
subspace of `X` on its analytic points. -/
noncomputable def analyticLocus : PreAdicSpace.{u} :=
  X.restrict (Opens.isOpenEmbedding ⟨X.analyticPoints, X.isOpen_analyticPoints⟩)

/-- The inclusion `X_a ⟶ X` of the analytic locus, an open immersion. -/
noncomputable def analyticLocus.ι : X.analyticLocus ⟶ X :=
  X.ofRestrict _

instance : IsOpenImmersion (analyticLocus.ι X) :=
  IsOpenImmersion.ofRestrict X _

/-- The image of the analytic locus is the set of analytic points. -/
@[simp]
theorem analyticLocus.range_ι : Set.range (analyticLocus.ι X).base = X.analyticPoints := by
  rw [analyticLocus.ι, ofRestrict_base]
  exact Opens.set_range_inclusion' _

/-- **The analytic locus is analytic**: every point of `X_a` is analytic. -/
@[simp]
theorem analyticPoints_analyticLocus : X.analyticLocus.analyticPoints = Set.univ := by
  rw [analyticLocus, analyticPoints_restrict]
  exact Set.eq_univ_of_forall fun x ↦ x.2

/-- The inclusion of the analytic locus is an isomorphism exactly when every point of `X` is
analytic. -/
theorem isIso_analyticLocus_ι_iff : IsIso (analyticLocus.ι X) ↔ X.analyticPoints = Set.univ := by
  refine ⟨fun _ ↦ ?_, fun h ↦ ?_⟩
  · rw [← analyticLocus.range_ι, Set.range_eq_univ]
    exact (TopCat.homeoOfIso (forgetToTop.mapIso (asIso (analyticLocus.ι X)))).surjective
  · have e : Set.range (analyticLocus.ι X).base = Set.range (𝟙 X : X ⟶ X).base := by
      simp [h]
    rw [← IsOpenImmersion.isoOfRangeEq_hom_comp (analyticLocus.ι X) (𝟙 X) e, Category.comp_id]
    infer_instance

section Lift

variable {X} {T : PreAdicSpace.{u}} (g : T ⟶ X)

/-- **The universal property of the analytic locus**: a morphism whose image consists of analytic
points factors through `X_a`, uniquely (`analyticLocus.lift_uniq`). -/
noncomputable def analyticLocus.lift (hg : Set.range g.base ⊆ X.analyticPoints) :
    T ⟶ X.analyticLocus :=
  IsOpenImmersion.lift (analyticLocus.ι X) g (by rwa [analyticLocus.range_ι])

/-- The factorisation through the analytic locus composes with the inclusion to the original
morphism. -/
@[reassoc (attr := simp)]
theorem analyticLocus.lift_ι (hg : Set.range g.base ⊆ X.analyticPoints) :
    analyticLocus.lift g hg ≫ analyticLocus.ι X = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- A factorisation through the analytic locus is the lift. -/
theorem analyticLocus.lift_uniq (hg : Set.range g.base ⊆ X.analyticPoints)
    (l : T ⟶ X.analyticLocus) (hl : l ≫ analyticLocus.ι X = g) : l = analyticLocus.lift g hg :=
  IsOpenImmersion.lift_uniq _ _ _ l hl

/-- A morphism factors through the analytic locus exactly when its image consists of analytic
points. -/
theorem analyticLocus.exists_comp_ι_eq_iff :
    (∃ l : T ⟶ X.analyticLocus, l ≫ analyticLocus.ι X = g) ↔
      Set.range g.base ⊆ X.analyticPoints := by
  refine ⟨?_, fun hg ↦ ⟨analyticLocus.lift g hg, analyticLocus.lift_ι g hg⟩⟩
  rintro ⟨l, rfl⟩
  rw [← analyticLocus.range_ι, comp_base, TopCat.coe_comp]
  exact Set.range_comp_subset_range _ _

end Lift

section Map

variable {X} {Y Z : PreAdicSpace.{u}} (f : Y ⟶ X)
  (hf : Set.MapsTo f.base Y.analyticPoints X.analyticPoints)

/-- **Restriction of a morphism to analytic loci**: a morphism sending analytic points to
analytic points, for instance an adic morphism (Wedhorn, Proposition 8.39), restricts to a
morphism `Y_a ⟶ X_a`, the unique one compatible with the inclusions (`analyticLocusMap_ι`). -/
noncomputable def analyticLocusMap : Y.analyticLocus ⟶ X.analyticLocus :=
  analyticLocus.lift (analyticLocus.ι Y ≫ f) <| by
    rintro _ ⟨y, rfl⟩
    exact hf (analyticLocus.range_ι Y ▸ Set.mem_range_self y)

/-- The restriction to analytic loci commutes with the inclusions. -/
@[reassoc (attr := simp)]
theorem analyticLocusMap_ι :
    analyticLocusMap f hf ≫ analyticLocus.ι X = analyticLocus.ι Y ≫ f :=
  analyticLocus.lift_ι _ _

/-- The restriction of the identity to the analytic locus is the identity. -/
@[simp]
theorem analyticLocusMap_id
    (h : Set.MapsTo (𝟙 X : X ⟶ X).base X.analyticPoints X.analyticPoints) :
    analyticLocusMap (𝟙 X) h = 𝟙 X.analyticLocus := by
  rw [← cancel_mono (analyticLocus.ι X), analyticLocusMap_ι, Category.id_comp, Category.comp_id]

/-- The restriction of a composite to analytic loci is the composite of the restrictions. -/
theorem analyticLocusMap_comp (g : X ⟶ Z)
    (hg : Set.MapsTo g.base X.analyticPoints Z.analyticPoints)
    (hfg : Set.MapsTo (f ≫ g).base Y.analyticPoints Z.analyticPoints) :
    analyticLocusMap (f ≫ g) hfg = analyticLocusMap f hf ≫ analyticLocusMap g hg := by
  rw [← cancel_mono (analyticLocus.ι Z), analyticLocusMap_ι, Category.assoc, analyticLocusMap_ι,
    analyticLocusMap_ι_assoc]

end Map

/-- The analytic locus of an adic space is an adic space, an open adic subspace. -/
theorem isAdic_analyticLocus (hX : isAdic X) : isAdic X.analyticLocus :=
  isAdic_restrict _ hX

end PreAdicSpace

namespace ValuationSpectrum

open PairOfDefinition

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
  (hP : P.ringOfDefinition ≤ Aplus)

/-- **The analytic points of `Spa(A, A⁺)` are its analytic locus** (Wedhorn, Proposition and
Definition 8.36): a point of the adic spectrum has a neighbourhood whose sections contain a
pseudouniformiser exactly when its support is not open. The ring `A` need not be complete. -/
@[simp]
theorem analyticPoints_presentationLimitPreAdicSpace :
    (presentationLimitPreAdicSpace P Aplus hAplus hP).analyticPoints =
      (Subtype.val ⁻¹' spaAnalytic Aplus : Set (spa Aplus)) := by
  ext x
  constructor
  · rintro ⟨U, hxU, f, hf⟩
    -- restrict `f` to a rational neighbourhood `R(T/s) ⊆ U` of `x`, whose sections are `A⟨T/s⟩`
    obtain ⟨i, hi⟩ := exists_presentationIndex_mem (P := P) hxU
    let _ := locUniformSpace P i.pres.num i.pres.den _ i.pres.hasDenominatorPower
    have _ := isUniformAddGroup_locUniformSpace P i.pres.num i.pres.den _ i.pres.hasDenominatorPower
    have _ := isTopologicalRing_locUniformSpace P i.pres.num i.pres.den _
      i.pres.hasDenominatorPower
    have _ := isHuberRing_completion_locTopology P i.pres.num i.pres.den _
      i.pres.hasDenominatorPower
    let φ := (eqToHom (presentationLimitPresheaf_obj P Aplus (op U))).hom ≫
      (presentationLimitπToPresentation Aplus U i).hom ≫
      eqToHom (completionLocObj_obj P i.pres.num i.pres.den _ i.pres.hasDenominatorPower)
    -- the image of `f` is a pseudouniformiser of `A⟨T/s⟩`, which is therefore a Tate ring
    exact rationalSubset_subset_spaAnalytic_of_isTateRing P hP i.pres.num i.pres.den _
      i.pres.hasDenominatorPower i.isOpen_span ⟨⟨_, hf.map φ.2⟩⟩ (mem_spaBasicOpen.mp hi)
  · intro hx
    -- `x` lies in a chart `R(G/g)` of the standard rational cover of the analytic locus
    classical
    obtain ⟨G, hG⟩ := P.fg_idealOfDefinition
    replace hx : x.1 ∈ spaAnalytic Aplus := hx
    rw [spaAnalytic_eq_biUnion_rationalSubset P Aplus G hG] at hx
    obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.mp hx
    set T := G.image ((↑) : P.ringOfDefinition → A)
    have hT : IsOpen (Ideal.span (T : Set A) : Set A) :=
      P.span_image_eq_extendedIdealOfDefinition G hG ▸ P.isOpen_extendedIdealOfDefinition
    let p : Presentation P := ⟨T, g, P.hasDenominatorPower_of_isOpen_span _ _ _ hT⟩
    let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    -- the image of `g` in `A⟨G/g⟩`, the sections over `R(G/g)`, is a pseudouniformiser
    let ψ := eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower).symm ≫
      (presentationLimitRationalIso Aplus hAplus p hT).inv.hom ≫
      (eqToHom (presentationLimitPresheaf_obj P Aplus (op (spaBasicOpen Aplus T g))).symm).hom
    exact ⟨spaBasicOpen Aplus T g, mem_spaBasicOpen.mpr hxg, _,
      (isPseudoUniformizer_toCompletionLoc P _ _ _ p.hasDenominatorPower
        (P.isTopologicallyNilpotent_of_mem_idealOfDefinition
          (hG ▸ Ideal.subset_span (Finset.mem_coe.mpr hg)))).map ψ.2⟩

end ValuationSpectrum

namespace AdicSpace

variable (X : AdicSpace.{u})

/-- **The analytic locus** `X_a` of an adic space `X` (Wedhorn, Remark 8.37): the open adic
subspace of `X` on its analytic points. -/
noncomputable def analyticLocus : AdicSpace.{u} :=
  ⟨X.obj.analyticLocus, PreAdicSpace.isAdic_analyticLocus X.obj X.property⟩

/-- The pre-adic space underlying the analytic locus of an adic space is the analytic locus of
the underlying pre-adic space. -/
@[simp]
theorem analyticLocus_obj : X.analyticLocus.obj = X.obj.analyticLocus :=
  (rfl)

/-- The inclusion `X_a ⟶ X` of the analytic locus of an adic space, transported along
`analyticLocus_obj` from the inclusion of the analytic locus of the underlying pre-adic space. -/
noncomputable def analyticLocus.ι : X.analyticLocus ⟶ X :=
  ObjectProperty.homMk (eqToHom (analyticLocus_obj X) ≫ PreAdicSpace.analyticLocus.ι X.obj)

/-- The underlying morphism of pre-adic spaces of the inclusion of the analytic locus. -/
@[simp]
theorem analyticLocus.ι_hom :
    (analyticLocus.ι X).hom = eqToHom (analyticLocus_obj X) ≫ PreAdicSpace.analyticLocus.ι X.obj :=
  (rfl)

instance : PreAdicSpace.IsOpenImmersion (analyticLocus.ι X).hom := by
  rw [analyticLocus.ι_hom]
  infer_instance

end AdicSpace

end TauCeti
