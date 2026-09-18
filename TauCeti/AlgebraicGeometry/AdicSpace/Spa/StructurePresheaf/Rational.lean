/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.PresentationIndependence
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Basic

/-!
# The presentation limit on a rational open is `A⟨T/s⟩`

Wedhorn §8.1 defines `𝒪_X(V)` for an open `V ⊆ Spa(A,A⁺)` as the limit of `A⟨T/s⟩` over the
rational subsets `R(T/s) ⊆ V`, and states that on a rational open `U = R(T/s)` this limit is
`A_U = A⟨T/s⟩` again. This file proves that statement for `presentationLimit`, the limit indexed by
admissible presentations: when `A⁺` consists of power-bounded elements, the projection of
`presentationLimit Aplus R(T/s)` at the presentation `(T, s)` itself is an isomorphism, and under
these isomorphisms the restriction maps of `presentationLimitPresheaf` between rational opens are
the comparison maps of Wedhorn's Proposition 8.2(1).

## The argument

For a containment `R(T'/s') ⊆ R(T/s)` there is a unique continuous homomorphism
`A⟨T/s⟩ → A⟨T'/s'⟩` compatible with the structure maps from `A`
(`existsUnique_continuous_ringHom_of_rationalSubset_subset`); `homOfRationalSubsetSubset` is it as
a morphism of `CompleteSeparatedTopCommRingCat`. Uniqueness makes these maps functorial, and
identifies every restriction map of a refinement with one of them.

If `V ⊆ R(T/s)` and `(T, s)` is an index of `V`, the comparison maps out of `A⟨T/s⟩` form a cone
over the diagram of `V`, which gives an inverse to the projection at `(T, s)`. That the projection
is also injective comes from the key identity `presentationLimitπ_eq_π_comp`: the projection at any
index `j` factors through the projection at any index `i` with `R(j) ⊆ R(i)`. To prove it, pass to
the common refinement `k` of `i` and `j`, which presents `R(i) ∩ R(j) = R(j)`. The restriction map
`A_j → A_k` is then a split monomorphism, since the comparison map back is a left inverse.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.Presentation.toCompletionLocObjHom` : the structure map
  `A → A⟨p⟩` as a morphism of `CompleteSeparatedTopCommRingCat`.
* `TauCeti.ValuationSpectrum.homOfRationalSubsetSubset` : the comparison morphism
  `A⟨T/s⟩ ⟶ A⟨T'/s'⟩` of a containment `R(T'/s') ⊆ R(T/s)`.
* `TauCeti.ValuationSpectrum.presentationLimitRationalIso` : the isomorphism
  `presentationLimit Aplus R(T/s) ≅ A⟨T/s⟩` for an admissible presentation `(T, s)`.

## Main results

* `TauCeti.Huber.PairOfDefinition.Presentation.toCompletionLocObjHom_comp_completionLocObjHom`
  and `TauCeti.Huber.PairOfDefinition.Presentation.toCompletionLocObjHom_comp_restrictionHom` :
  comparison and restriction morphisms commute with the structure maps.
* `TauCeti.ValuationSpectrum.restrictionHom_eq_homOfRationalSubsetSubset` : the restriction
  morphism of a refinement is the comparison morphism of the containment it induces.
* `TauCeti.ValuationSpectrum.presentationLimitπ_eq_π_comp` : projections of the limit factor
  through each other along comparison morphisms.
* `TauCeti.ValuationSpectrum.isIso_presentationLimitπ` : the projection at an index whose
  rational subset contains `V` is an isomorphism.
* `TauCeti.ValuationSpectrum.presentationLimitRationalIso_inv_comp_map_comp_hom` : between rational
  opens, the restriction maps of `presentationLimitPresheaf` are the comparison morphisms.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1 and Proposition 8.2(1).
-/

open CategoryTheory CategoryTheory.Limits _root_.TopologicalSpace

public section

universe v

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type v} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] {P : PairOfDefinition A}

/-! ### The structure maps as morphisms -/

/-- **The structure map `A → A⟨p⟩`** of a presentation, as a morphism of
`CompleteSeparatedTopCommRingCat` out of the complete Hausdorff ring `A`. -/
noncomputable def Presentation.toCompletionLocObjHom
    (p : Presentation P) : CompleteSeparatedTopCommRingCat.of A ⟶ p.completionLocObj := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  exact ObjectProperty.homMk (eqToHom (CompleteSeparatedTopCommRingCat.of_obj A) ≫
    (⟨toCompletionLoc P p.num p.den _ p.hasDenominatorPower,
        continuous_toCompletionLoc P p.num p.den _ p.hasDenominatorPower⟩ :
      TopCommRingCat.of A ⟶
        TopCommRingCat.of (UniformSpace.Completion (Localization.Away p.den))) ≫
    eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower).symm)

/-- The underlying morphism of `Presentation.toCompletionLocObjHom` is the structure map
`toCompletionLoc`, transported across `CompleteSeparatedTopCommRingCat.of_obj` and
`completionLocObj_obj`. -/
@[simp]
theorem Presentation.toCompletionLocObjHom_hom (p : Presentation P) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    p.toCompletionLocObjHom.hom = eqToHom (CompleteSeparatedTopCommRingCat.of_obj A) ≫
      (⟨toCompletionLoc P p.num p.den _ p.hasDenominatorPower,
          continuous_toCompletionLoc P p.num p.den _ p.hasDenominatorPower⟩ :
        TopCommRingCat.of A ⟶
          TopCommRingCat.of (UniformSpace.Completion (Localization.Away p.den))) ≫
      eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower).symm :=
  (rfl)

/-- **Comparison morphisms over `A` commute with the structure maps**: a continuous ring
homomorphism `A⟨p⟩ → A⟨q⟩` compatible with the structure maps from `A`, as a morphism, carries the
structure morphism of `p` to that of `q`. -/
theorem Presentation.toCompletionLocObjHom_comp_completionLocObjHom
    (p q : Presentation P) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := locUniformSpace P q.num q.den _ q.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P q.num q.den _ q.hasDenominatorPower
    ∀ (g : UniformSpace.Completion (Localization.Away p.den) →+*
        UniformSpace.Completion (Localization.Away q.den)) (hg : Continuous g),
      g.comp (toCompletionLoc P p.num p.den _ p.hasDenominatorPower) =
          toCompletionLoc P q.num q.den _ q.hasDenominatorPower →
        p.toCompletionLocObjHom ≫
            completionLocObjHom P p.num p.den _ p.hasDenominatorPower q.num q.den _
              q.hasDenominatorPower g hg =
          q.toCompletionLocObjHom := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := locUniformSpace P q.num q.den _ q.hasDenominatorPower
  let _ := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  let _ := isTopologicalRing_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  intro g hg hgc
  let F : TopCommRingCat.of A ⟶
      TopCommRingCat.of (UniformSpace.Completion (Localization.Away p.den)) :=
    ⟨_, continuous_toCompletionLoc P p.num p.den _ p.hasDenominatorPower⟩
  let G : TopCommRingCat.of (UniformSpace.Completion (Localization.Away p.den)) ⟶
      TopCommRingCat.of (UniformSpace.Completion (Localization.Away q.den)) := ⟨g, hg⟩
  let H : TopCommRingCat.of A ⟶
      TopCommRingCat.of (UniformSpace.Completion (Localization.Away q.den)) :=
    ⟨_, continuous_toCompletionLoc P q.num q.den _ q.hasDenominatorPower⟩
  have hH : F ≫ G = H := Subtype.ext hgc
  apply InducedCategory.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, completionLocObjHom_hom,
    Presentation.toCompletionLocObjHom_hom, Presentation.toCompletionLocObjHom_hom]
  -- after the two `_hom` rewrites the underlying morphisms are `F`, `G` and `H` between
  -- transports; `change` names them so that `hH` applies
  change (eqToHom _ ≫ F ≫ eqToHom _) ≫ eqToHom _ ≫ G ≫ eqToHom _ = eqToHom _ ≫ H ≫ eqToHom _
  simp [reassoc_of% hH]

/-- **Restriction commutes with the structure maps**: the restriction morphism
`A⟨p⟩ → A⟨q⟩` of a refinement `p ≤ q` carries the structure morphism of `p` to that of `q`. -/
@[reassoc (attr := simp)]
theorem Presentation.toCompletionLocObjHom_comp_restrictionHom
    {p q : Presentation P} (h : p ≤ q) :
    p.toCompletionLocObjHom ≫ Presentation.restrictionHom h = q.toCompletionLocObjHom := by
  obtain ⟨r, hr, hT⟩ := Presentation.le_def.mp h
  rw [Presentation.restrictionHom_eq h r hr hT, restrictionObjHom_eq_completionLocObjHom]
  exact p.toCompletionLocObjHom_comp_completionLocObjHom q _ _
    (restrictionRingHom_comp_toCompletionLoc P _ _ _ _ _ _ _ _ r hr hT)

end TauCeti.Huber.PairOfDefinition

namespace TauCeti.ValuationSpectrum

open CategoryTheory CategoryTheory.Limits _root_.TopologicalSpace TauCeti.Huber
  TauCeti.Huber.PairOfDefinition

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : PairOfDefinition A}

/-! ### The projections of the presentation limit -/

variable {Aplus : Subring A} {V : Opens ↥(spa Aplus)}

/-- **Projections factor through comparison morphisms**: if `R(j) ⊆ R(i)` for two indices of `V`,
the projection of the limit at `j` is the projection at `i` followed by the comparison morphism
`A⟨i⟩ → A⟨j⟩`. -/
theorem presentationLimitπ_eq_π_comp (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (i j : PresentationIndex (P := P) Aplus V)
    (h : rationalSubset Aplus j.pres.num j.pres.den ⊆ rationalSubset Aplus i.pres.num i.pres.den) :
    presentationLimitπToPresentation Aplus V j =
      presentationLimitπToPresentation Aplus V i ≫
        homOfRationalSubsetSubset Aplus hAplus h := by
  -- `k` refines `j` and `i`, and presents `R(j) ∩ R(i) = R(j)`
  let k := j.commonRefinement i
  have hk : rationalSubset Aplus j.pres.num j.pres.den ⊆
      rationalSubset Aplus k.pres.num k.pres.den := by
    rw [PresentationIndex.commonRefinement_pres, rationalSubset_commonRefinement]
    exact Set.subset_inter subset_rfl h
  -- the restriction `A_j → A_k` has the comparison map back as a left inverse
  have hsplit : Presentation.restrictionHom (j.le_commonRefinement_left i) ≫
      homOfRationalSubsetSubset Aplus hAplus hk = 𝟙 _ := by
    rw [restrictionHom_eq_homOfRationalSubsetSubset Aplus hAplus, homOfRationalSubsetSubset_comp,
      homOfRationalSubsetSubset_self]
  calc presentationLimitπToPresentation Aplus V j
      = presentationLimitπToPresentation Aplus V j ≫
          Presentation.restrictionHom (j.le_commonRefinement_left i) ≫
          homOfRationalSubsetSubset Aplus hAplus hk := by rw [hsplit, Category.comp_id]
    _ = presentationLimitπToPresentation Aplus V k ≫
        homOfRationalSubsetSubset Aplus hAplus hk := by
        rw [← Category.assoc, presentationLimitπ_comp_restriction (P := P)
          (j.le_commonRefinement_left i)]
    _ = presentationLimitπToPresentation Aplus V i ≫
        homOfRationalSubsetSubset Aplus hAplus h := by
        rw [← presentationLimitπ_comp_restriction (P := P)
            (j.le_commonRefinement_right i),
          Category.assoc, restrictionHom_eq_homOfRationalSubsetSubset Aplus hAplus,
          homOfRationalSubsetSubset_comp]

/-- **The projection at an index whose rational subset contains `V` is an isomorphism**: then
`R(i) = V`, and the limit over the presentations inside `V` is `A⟨i⟩`. -/
theorem isIso_presentationLimitπ (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (i : PresentationIndex (P := P) Aplus V) (hV : V ≤ spaBasicOpen Aplus i.pres.num i.pres.den) :
    IsIso (presentationLimitπToPresentation Aplus V i) := by
  -- the comparison morphisms out of `A⟨i⟩` form a cone over the diagram of `V`
  let app (j : PresentationIndex (P := P) Aplus V) :=
    homOfRationalSubsetSubset Aplus hAplus (j.rationalSubset_subset hV)
  have naturality {j₁ j₂ : PresentationIndex (P := P) Aplus V} (f : j₁ ⟶ j₂) :
      app j₁ ≫ Presentation.restrictionHom f.le = app j₂ := by
    dsimp [app]
    rw [restrictionHom_eq_homOfRationalSubsetSubset Aplus hAplus,
      homOfRationalSubsetSubset_comp]
  let c := presentationIndexCone Aplus V i.pres.completionLocObj app naturality
  let inv := eqToHom
      (presentationIndexCone_pt Aplus V i.pres.completionLocObj app naturality).symm ≫
    presentationLimitLift Aplus V c
  refine ⟨inv, ?_, ?_⟩
  · refine presentationLimit_hom_ext_toPresentation fun j ↦ ?_
    dsimp [inv, c]
    simp only [Category.assoc]
    rw [presentationIndexCone_lift_comp_πToPresentation]
    exact (presentationLimitπ_eq_π_comp hAplus i j _).symm
  · dsimp [inv, c]
    simp only [Category.assoc]
    rw [presentationIndexCone_lift_comp_πToPresentation]
    exact homOfRationalSubsetSubset_self Aplus hAplus _

variable (Aplus) in
/-- **The presentation limit on a rational open is its coordinate ring**: for an admissible
presentation `p`, the limit over the presentations inside `R(p)` is isomorphic to `A⟨p⟩` by the
projection at `p` itself (`presentationLimitRationalIso_hom`). This is Wedhorn §8.1's
`𝒪_X(U) = A_U`, stated for `presentationLimit`. -/
noncomputable def presentationLimitRationalIso (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (p : Presentation P) (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) :
    presentationLimit (P := P) Aplus (spaBasicOpen Aplus p.num p.den) ≅ p.completionLocObj :=
  haveI := isIso_presentationLimitπ (V := spaBasicOpen Aplus p.num p.den) hAplus ⟨p, hp, le_rfl⟩
    le_rfl
  asIso (presentationLimitπToPresentation Aplus _ ⟨p, hp, le_rfl⟩)

variable (Aplus) in
/-- The isomorphism `presentationLimitRationalIso` is the projection at the presentation itself. -/
@[simp]
theorem presentationLimitRationalIso_hom (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (p : Presentation P) (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) :
    (presentationLimitRationalIso Aplus hAplus p hp).hom =
      presentationLimitπToPresentation Aplus (spaBasicOpen Aplus p.num p.den)
        ⟨p, hp, le_rfl⟩ :=
  (rfl)

variable (Aplus) in
/-- The inverse of `presentationLimitRationalIso`, followed by the projection at an index `j`, is
the comparison morphism `A⟨p⟩ → A⟨j⟩`. -/
@[simp]
theorem presentationLimitRationalIso_inv_comp_π (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (p : Presentation P) (hp : IsOpen (Ideal.span (p.num : Set A) : Set A))
    (j : PresentationIndex (P := P) Aplus (spaBasicOpen Aplus p.num p.den)) :
    (presentationLimitRationalIso Aplus hAplus p hp).inv ≫
        presentationLimitπToPresentation Aplus (spaBasicOpen Aplus p.num p.den) j =
      homOfRationalSubsetSubset Aplus hAplus (j.rationalSubset_subset le_rfl) := by
  rw [Iso.inv_comp_eq, presentationLimitRationalIso_hom]
  exact presentationLimitπ_eq_π_comp hAplus _ j _

/-- A comparison morphism followed by the transport along an equality of presentations is again
a comparison morphism. -/
private theorem homOfRationalSubsetSubset_comp_eqToHom
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {p q q' : Presentation P} (e : q = q')
    (h : rationalSubset Aplus q.num q.den ⊆ rationalSubset Aplus p.num p.den)
    (h' : rationalSubset Aplus q'.num q'.den ⊆ rationalSubset Aplus p.num p.den)
    (e' : q.completionLocObj = q'.completionLocObj) :
    homOfRationalSubsetSubset Aplus hAplus h ≫ eqToHom e' =
      homOfRationalSubsetSubset Aplus hAplus h' := by
  subst e
  rw [eqToHom_refl, Category.comp_id]

variable (Aplus) in
/-- **Between rational opens, restriction is the comparison morphism**: for admissible
presentations `p` and `q` with `R(q) ⊆ R(p)`, the restriction map of the presentation limit from
`R(p)` to `R(q)` becomes, under `presentationLimitRationalIso`, the comparison morphism of
Wedhorn's Proposition 8.2(1). -/
theorem presentationLimitRationalIso_inv_comp_map_comp_hom
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (p q : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A))
    (hq : IsOpen (Ideal.span (q.num : Set A) : Set A))
    (h : spaBasicOpen Aplus q.num q.den ≤ spaBasicOpen Aplus p.num p.den) :
    (presentationLimitRationalIso Aplus hAplus p hp).inv ≫ presentationLimitMap (P := P) h ≫
        (presentationLimitRationalIso Aplus hAplus q hq).hom =
      homOfRationalSubsetSubset Aplus hAplus
        (spaBasicOpen_le_spaBasicOpen_iff.mp h) := by
  rw [presentationLimitRationalIso_hom, presentationLimitMap_comp_πToPresentation,
    reassoc_of% presentationLimitRationalIso_inv_comp_π]
  exact homOfRationalSubsetSubset_comp_eqToHom hAplus (presentationIndexRestrict_obj_pres h _) _ _ _

end TauCeti.ValuationSpectrum

end
