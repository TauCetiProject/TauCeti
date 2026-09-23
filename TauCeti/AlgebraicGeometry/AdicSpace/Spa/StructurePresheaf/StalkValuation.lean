/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Stalks
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.PlusComparison
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.OfDirected
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# The valuation on a stalk of the presentation-limit presheaf

Let `x` be a point of `X = Spa(A,A⁺)`. Every rational neighbourhood `R(p)` of `x` has coordinate
ring `A⟨p⟩`, and `x` determines a point of `Spa (A⟨p⟩, A_p⁺)` through the homeomorphism
`Spa (A⟨p⟩, A_p⁺) ≃ₜ R(p)` of Wedhorn's Proposition 8.2(2). This file glues these points along
the germ maps `A⟨p⟩ → 𝒪_{X,x}` into a point of the valuation spectrum of the stalk: the valuation
`v_x` on `𝒪_{X,x}` which Wedhorn attaches to `x` in §8.1. It is the valuation through which the
stalks of an adic space carry their valuations.

The gluing is `TauCeti.ValuationSpectrum.ofDirected`. Its hypotheses are supplied here: every germ
is the germ of an element of some `A⟨p⟩`; a germ vanishes only if some restriction to a smaller
rational neighbourhood does; and the points of `x` on the rings `A⟨p⟩` are compatible with the
comparison maps of Wedhorn's Proposition 8.2(1). Two lifts of one germ therefore differ, on a
common rational neighbourhood, by an element of the support of the point of `x`, and so they have
the same value.

The stalk is the ring colimit of `presentationLimitPresheafInCommRingCat`; no topology on it is
used. `A⁺` is assumed to consist of power-bounded elements, as for every ring of integral
elements, and to contain the ring of definition of the chosen pair of definition, as
`spaCompletedLocalizationHomeomorph` requires.

## Main definitions

* `TauCeti.ValuationSpectrum.rationalLocalizationPoint`: the point of `A⟨p⟩` determined by
  `x ∈ R(p)`.
* `TauCeti.ValuationSpectrum.presentationLimitStalkValuation`: the valuation on the stalk at `x`.

## Main results

* `TauCeti.ValuationSpectrum.comap_presentationLimitRationalGerm_presentationLimitStalkValuation`:
  pulled back along the germ map of a rational neighbourhood `R(p)`, the stalk valuation is the
  point of `A⟨p⟩` determined by `x`.
* `TauCeti.ValuationSpectrum.eq_presentationLimitStalkValuation`: it is the only point of the
  valuation spectrum of the stalk with this property.
* `TauCeti.ValuationSpectrum.comap_presentationLimitStalkValuation`: pulled back to `A`, the stalk
  valuation is `x` itself.
* `TauCeti.ValuationSpectrum.exists_presentationLimitRationalGerm_eq` and
  `TauCeti.ValuationSpectrum.exists_map_homOfRationalSubsetSubset_eq_zero`: every germ comes from
  a rational coordinate ring, and a germ vanishes exactly when a restriction does.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1 and Proposition 8.2.
-/

namespace TauCeti.ValuationSpectrum

open AlgebraicGeometry CategoryTheory _root_.TopologicalSpace TauCeti.Huber
  TauCeti.Huber.PairOfDefinition

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : PairOfDefinition A} {Aplus : Subring A}

/-- The underlying commutative ring of `p.completionLocObj` is the completed rational localisation
`A⟨p⟩ = UniformSpace.Completion (Localization.Away p.den)`: the transport along
`completionLocObj_obj`, with its target stated as `CommRingCat.of` of the completion so that
maps out of `A⟨p⟩` compose with it on the nose. -/
noncomputable def completionLocObjCommRingCatIso (p : Presentation P) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).obj
        p.completionLocObj ≅
      CommRingCat.of (UniformSpace.Completion (Localization.Away p.den)) :=
  letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  (forget₂ TopCommRingCat CommRingCat).mapIso
    (eqToIso (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower))

/-- Transporting a morphism of topological commutative rings along equalities of its endpoints
and then forgetting the topology commutes with the transports. -/
private theorem forget₂_map_eqToHom_comp_comp_eqToHom {X X' Y Y' : TopCommRingCat}
    (eX : X = X') (g : X' ⟶ Y') (eY : Y = Y') :
    (forget₂ TopCommRingCat CommRingCat).map (eqToHom eX ≫ g ≫ eqToHom eY.symm) ≫
        (forget₂ TopCommRingCat CommRingCat).map (eqToHom eY) =
      (forget₂ TopCommRingCat CommRingCat).map (eqToHom eX) ≫
        (forget₂ TopCommRingCat CommRingCat).map g := by
  subst eX eY
  simp

/-- **Comparison maps through the identification with `A⟨p⟩`**: under
`completionLocObjCommRingCatIso`, the underlying ring map of the comparison morphism of
`R(q) ⊆ R(p)` is the comparison ring homomorphism `ringHomOfRationalSubsetSubset`. -/
theorem map_homOfRationalSubsetSubset_comp_completionLocObjCommRingCatIso_hom
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {p q : Presentation P}
    (h : rationalSubset Aplus q.num q.den ⊆ rationalSubset Aplus p.num p.den) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := locUniformSpace P q.num q.den _ q.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P q.num q.den _ q.hasDenominatorPower
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
        (homOfRationalSubsetSubset Aplus hAplus h) ≫ (completionLocObjCommRingCatIso q).hom =
      (completionLocObjCommRingCatIso p).hom ≫
        CommRingCat.ofHom (ringHomOfRationalSubsetSubset P Aplus hAplus p.num p.den _
          p.hasDenominatorPower q.num q.den _ q.hasDenominatorPower h) := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  rw [homOfRationalSubsetSubset_def, Functor.comp_map, ObjectProperty.ι_map,
    completionLocObjHom_hom]
  -- the underlying ring map of the comparison morphism is `ringHomOfRationalSubsetSubset` between
  -- two transports along `completionLocObj_obj`, which `completionLocObjCommRingCatIso` undoes
  exact forget₂_map_eqToHom_comp_comp_eqToHom
    (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower) _
    (completionLocObj_obj P q.num q.den _ q.hasDenominatorPower)

/-- The point of the rational coordinate ring `A⟨p⟩` determined by a point `x` of the rational
subset `R(p)`: the preimage of `x` under the homeomorphism `Spa (A⟨p⟩, A_p⁺) ≃ₜ R(p)` of
Wedhorn's Proposition 8.2(2), read on the underlying ring of `p.completionLocObj`. -/
noncomputable def rationalLocalizationPoint (hP : P.ringOfDefinition ≤ Aplus) (p : Presentation P)
    (x : spa Aplus) (hx : x ∈ spaBasicOpen Aplus p.num p.den) :
    Spv ((TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).obj
      p.completionLocObj) :=
  letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  comap (completionLocObjCommRingCatIso p).hom.hom
    ((spaCompletedLocalizationHomeomorph P Aplus hP p.num p.den _ p.hasDenominatorPower).symm
      ⟨x, mem_spaBasicOpen.mp hx⟩).1

/-- Pulling back along two composable morphisms of commutative rings is pulling back along their
composite. -/
private theorem comap_hom_comap_hom {X Y Z : CommRingCat} (φ : X ⟶ Y) (ψ : Y ⟶ Z) (w : Spv Z) :
    comap φ.hom (comap ψ.hom w) = comap (φ ≫ ψ).hom w := by
  rw [CommRingCat.hom_comp, comap_comp, Function.comp_apply]

/-- **The rational point lies over `x`**: pulled back along the structure map `A → A⟨p⟩`, the
point of `A⟨p⟩` determined by `x ∈ R(p)` is `x` itself. -/
theorem comap_rationalLocalizationPoint (hP : P.ringOfDefinition ≤ Aplus) (p : Presentation P)
    (x : spa Aplus) (hx : x ∈ spaBasicOpen Aplus p.num p.den) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    comap (CommRingCat.ofHom (toCompletionLoc P p.num p.den _ p.hasDenominatorPower) ≫
        (completionLocObjCommRingCatIso p).inv).hom (rationalLocalizationPoint hP p x hx) = x := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  set w := (spaCompletedLocalizationHomeomorph P Aplus hP p.num p.den _ p.hasDenominatorPower).symm
    ⟨x, mem_spaBasicOpen.mp hx⟩
  have hw := spaCompletedLocalizationHomeomorph_apply P Aplus hP p.num p.den _
    p.hasDenominatorPower w
  rw [Homeomorph.apply_symm_apply] at hw
  rw [rationalLocalizationPoint, comap_hom_comap_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, CommRingCat.hom_ofHom]
  have hxw := congrArg (fun y ↦ y.1.1) hw
  simp only [spaLocToRationalSubset_val, spaComapLoc_val] at hxw
  exact hxw.symm

/-- The comparison map `A⟨p⟩ → A⟨q⟩` of a containment `R(q) ⊆ R(p)` pulls the point of `A⟨q⟩`
determined by `x ∈ R(q)` back to the point of `A⟨p⟩` determined by `x`. This is
`spaCompletedLocalizationHomeomorph_spaComap_pairHomOfRationalSubsetSubset` read through the
inverse homeomorphisms. -/
private theorem comap_ringHomOfRationalSubsetSubset_symm (hP : P.ringOfDefinition ≤ Aplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (p q : Presentation P)
    (h : rationalSubset Aplus q.num q.den ⊆ rationalSubset Aplus p.num p.den) (x : spa Aplus)
    (hx : x ∈ spaBasicOpen Aplus q.num q.den) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := locUniformSpace P q.num q.den _ q.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P q.num q.den _ q.hasDenominatorPower
    comap (ringHomOfRationalSubsetSubset P Aplus hAplus p.num p.den _ p.hasDenominatorPower
        q.num q.den _ q.hasDenominatorPower h)
      ((spaCompletedLocalizationHomeomorph P Aplus hP q.num q.den _ q.hasDenominatorPower).symm
        ⟨x, mem_spaBasicOpen.mp hx⟩).1 =
      ((spaCompletedLocalizationHomeomorph P Aplus hP p.num p.den _ p.hasDenominatorPower).symm
        ⟨x, h (mem_spaBasicOpen.mp hx)⟩).1 := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology P p.num p.den _ p.hasDenominatorPower
  let _ := locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology P q.num q.den _ q.hasDenominatorPower
  set w := (spaCompletedLocalizationHomeomorph P Aplus hP q.num q.den _ q.hasDenominatorPower).symm
    ⟨x, mem_spaBasicOpen.mp hx⟩
  have key := spaCompletedLocalizationHomeomorph_spaComap_pairHomOfRationalSubsetSubset P Aplus hP
    hAplus p.num p.den _ p.hasDenominatorPower q.num q.den _ q.hasDenominatorPower h w
  rw [Homeomorph.apply_symm_apply, ← Homeomorph.eq_symm_apply] at key
  rw [← key, Huber.Pair.Hom.spaComap_val, pairHomOfRationalSubsetSubset_toRingHom]

/-- **The rational points are compatible with the comparison maps**: for a containment
`R(q) ⊆ R(p)` and `x ∈ R(q)`, the comparison map `A⟨p⟩ → A⟨q⟩` pulls the point of `A⟨q⟩`
determined by `x` back to the point of `A⟨p⟩` determined by `x`. -/
theorem comap_homOfRationalSubsetSubset_rationalLocalizationPoint (hP : P.ringOfDefinition ≤ Aplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (p q : Presentation P)
    (h : spaBasicOpen Aplus q.num q.den ≤ spaBasicOpen Aplus p.num p.den) (x : spa Aplus)
    (hx : x ∈ spaBasicOpen Aplus q.num q.den) :
    comap ((TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
        (homOfRationalSubsetSubset Aplus hAplus (spaBasicOpen_le_spaBasicOpen_iff.mp h))).hom
      (rationalLocalizationPoint hP q x hx) = rationalLocalizationPoint hP p x (h hx) := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  rw [rationalLocalizationPoint, rationalLocalizationPoint, comap_hom_comap_hom,
    map_homOfRationalSubsetSubset_comp_completionLocObjCommRingCatIso_hom, ← comap_hom_comap_hom,
    CommRingCat.hom_ofHom, comap_ringHomOfRationalSubsetSubset_symm hP hAplus p q _ x hx]

/-- Every neighbourhood of a point of `Spa(A,A⁺)` contains the rational subset of an admissible
presentation containing the point. -/
theorem exists_presentation_mem_spaBasicOpen_le (P : PairOfDefinition A) {U : Opens (spa Aplus)}
    {x : spa Aplus} (hx : x ∈ U) :
    ∃ p : Presentation P, IsOpen (Ideal.span (p.num : Set A) : Set A) ∧
      x ∈ spaBasicOpen Aplus p.num p.den ∧ spaBasicOpen Aplus p.num p.den ≤ U := by
  obtain ⟨W, hW, hxW, hWU⟩ :=
    (isTopologicalBasis_spaRationalFamily_of_pairOfDefinition P Aplus).exists_subset_of_mem_open
      hx U.isOpen
  obtain ⟨T, s, hT, rfl⟩ := mem_spaRationalFamily_iff.mp hW
  exact ⟨⟨T, s, P.hasDenominatorPower_of_isOpen_span T s _ hT⟩, hT, mem_spaBasicOpen.mpr hxW,
    fun y hy ↦ hWU (mem_spaBasicOpen.mp hy)⟩

variable (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)

/-- **Every germ is a rational germ**: each element of the stalk at `x` is the germ of an
element of the coordinate ring `A⟨p⟩` of some rational neighbourhood `R(p)` of `x`. -/
theorem exists_presentationLimitRationalGerm_eq (x : spa Aplus)
    (t : (presentationLimitPresheafInCommRingCat P Aplus).stalk x) :
    ∃ (p : Presentation P) (hp : IsOpen (Ideal.span (p.num : Set A) : Set A))
      (hx : x ∈ spaBasicOpen Aplus p.num p.den) (a : _),
      (presentationLimitRationalGerm hAplus p hp x hx).hom a = t := by
  obtain ⟨U, hxU, s, rfl⟩ := (presentationLimitPresheafInCommRingCat P Aplus).exists_germ_eq t
  obtain ⟨p, hp, hxp, hpU⟩ := exists_presentation_mem_spaBasicOpen_le P hxU
  refine ⟨p, hp, hxp, (presentationLimitRationalIsoInCommRingCat hAplus p hp).hom
    ((presentationLimitPresheafInCommRingCat P Aplus).map (homOfLE hpU).op s), ?_⟩
  rw [presentationLimitRationalGerm_def, CommRingCat.comp_apply, Iso.hom_inv_id_apply,
    TopCat.Presheaf.germ_res_apply]

/-- **A rational germ vanishes only if a restriction does**: if an element of `A⟨p⟩` has zero
germ at `x`, then its image in the coordinate ring of some smaller rational neighbourhood of `x`
is already zero. -/
theorem exists_map_homOfRationalSubsetSubset_eq_zero {x : spa Aplus} {p : Presentation P}
    {hp : IsOpen (Ideal.span (p.num : Set A) : Set A)} {hx : x ∈ spaBasicOpen Aplus p.num p.den}
    {a : (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).obj
      p.completionLocObj}
    (ha : (presentationLimitRationalGerm hAplus p hp x hx).hom a = 0) :
    ∃ (q : Presentation P) (_ : IsOpen (Ideal.span (q.num : Set A) : Set A))
      (_ : x ∈ spaBasicOpen Aplus q.num q.den)
      (h : spaBasicOpen Aplus q.num q.den ≤ spaBasicOpen Aplus p.num p.den),
      ((TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
        (homOfRationalSubsetSubset Aplus hAplus (spaBasicOpen_le_spaBasicOpen_iff.mp h))).hom a =
        0 := by
  set F := presentationLimitPresheafInCommRingCat P Aplus
  rw [presentationLimitRationalGerm_def, CommRingCat.comp_apply,
    ← map_zero (ConcreteCategory.hom (F.germ _ x hx))] at ha
  obtain ⟨W, hxW, iU, iV, hW⟩ := F.germ_eq x hx hx _ _ ha
  obtain ⟨q, hq, hxq, hqW⟩ := exists_presentation_mem_spaBasicOpen_le P hxW
  have h : spaBasicOpen Aplus q.num q.den ≤ spaBasicOpen Aplus p.num p.den := hqW.trans iU.le
  refine ⟨q, hq, hxq, h, ?_⟩
  have hres : F.map (homOfLE h).op ((presentationLimitRationalIsoInCommRingCat hAplus p hp).inv a)
      = 0 := by
    have := congrArg (F.map (homOfLE hqW).op) hW
    rwa [map_zero, map_zero, ← CommRingCat.comp_apply, ← F.map_comp] at this
  rw [← presentationLimitRationalIsoInCommRingCat_inv_comp_map_comp_hom hAplus p q hp hq h,
    CommRingCat.comp_apply, CommRingCat.comp_apply, hres, map_zero]

/-! ### The stalk valuation -/

variable (P) in
/-- The rational neighbourhoods of `x`: admissible presentations whose rational subset contains
`x`. They index the rational germ maps into the stalk at `x`. -/
private abbrev RationalNhd (x : spa Aplus) : Type v :=
  {p : Presentation P //
    IsOpen (Ideal.span (p.num : Set A) : Set A) ∧ x ∈ spaBasicOpen Aplus p.num p.den}

/-- The rational germ map of a rational neighbourhood of `x`, as a ring homomorphism. -/
private noncomputable abbrev rationalNhdGerm {x : spa Aplus} (i : RationalNhd P x) :
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).obj
        i.1.completionLocObj →+* (presentationLimitPresheafInCommRingCat P Aplus).stalk x :=
  (presentationLimitRationalGerm hAplus i.1 i.2.1 x i.2.2).hom

/-- The comparison map between the coordinate rings of two rational neighbourhoods of `x`, as a
ring homomorphism. -/
private noncomputable abbrev rationalNhdMap {x : spa Aplus} {i j : RationalNhd P x}
    (h : spaBasicOpen Aplus j.1.num j.1.den ≤ spaBasicOpen Aplus i.1.num i.1.den) :
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).obj
        i.1.completionLocObj →+*
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).obj
        j.1.completionLocObj :=
  ((TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
    (homOfRationalSubsetSubset Aplus hAplus (spaBasicOpen_le_spaBasicOpen_iff.mp h))).hom

omit hAplus in
/-- Two rational neighbourhoods of `x` contain a third, the rational subset of their common
refinement. -/
private theorem exists_rationalNhd_le_le {x : spa Aplus} (i j : RationalNhd P x) :
    ∃ k : RationalNhd P x, spaBasicOpen Aplus k.1.num k.1.den ≤ spaBasicOpen Aplus i.1.num i.1.den ∧
      spaBasicOpen Aplus k.1.num k.1.den ≤ spaBasicOpen Aplus j.1.num j.1.den := by
  classical
  have hk (y : spa Aplus) : y ∈ spaBasicOpen Aplus (i.1.commonRefinement j.1).num
      (i.1.commonRefinement j.1).den ↔
        y ∈ spaBasicOpen Aplus i.1.num i.1.den ∧ y ∈ spaBasicOpen Aplus j.1.num j.1.den := by
    simp only [mem_spaBasicOpen, rationalSubset_commonRefinement, Set.mem_inter_iff]
  refine ⟨⟨i.1.commonRefinement j.1, ?_, (hk x).mpr ⟨i.2.2, j.2.2⟩⟩,
    fun y hy ↦ ((hk y).mp hy).1, fun y hy ↦ ((hk y).mp hy).2⟩
  rw [PairOfDefinition.Presentation.commonRefinement_num]
  exact P.isOpen_span_insert_mul_insert i.2.1 j.2.1

/-- Rational germs are compatible with the comparison maps. -/
private theorem rationalNhdGerm_rationalNhdMap {x : spa Aplus} {i j : RationalNhd P x}
    (h : spaBasicOpen Aplus j.1.num j.1.den ≤ spaBasicOpen Aplus i.1.num i.1.den) (a) :
    rationalNhdGerm hAplus j (rationalNhdMap hAplus h a) = rationalNhdGerm hAplus i a := by
  rw [rationalNhdGerm, rationalNhdGerm, rationalNhdMap, ← CommRingCat.comp_apply,
    presentationLimitRationalGerm_res hAplus i.1 j.1 i.2.1 j.2.1 h x j.2.2]

/-- The germ maps of the rational neighbourhoods of `x` have directed images. -/
private theorem directed_range_rationalNhdGerm (x : spa Aplus) :
    Directed (· ≤ ·) fun i : RationalNhd P x ↦ (rationalNhdGerm hAplus i).range := by
  intro i j
  obtain ⟨k, hki, hkj⟩ := exists_rationalNhd_le_le i j
  refine ⟨k, ?_, ?_⟩ <;> rintro _ ⟨a, rfl⟩
  · exact ⟨_, rationalNhdGerm_rationalNhdMap hAplus hki a⟩
  · exact ⟨_, rationalNhdGerm_rationalNhdMap hAplus hkj a⟩

/-- The germ maps of the rational neighbourhoods of `x` jointly cover the stalk. -/
private theorem exists_mem_range_rationalNhdGerm (x : spa Aplus)
    (t : (presentationLimitPresheafInCommRingCat P Aplus).stalk x) :
    ∃ i : RationalNhd P x, t ∈ (rationalNhdGerm hAplus i).range := by
  obtain ⟨p, hp, hx, a, rfl⟩ := exists_presentationLimitRationalGerm_eq hAplus x t
  exact ⟨⟨p, hp, hx⟩, a, rfl⟩

variable (hP : P.ringOfDefinition ≤ Aplus)

/-- The point of a rational neighbourhood is a pullback of the point of any smaller one. -/
private theorem comap_rationalNhdMap {x : spa Aplus} {i j : RationalNhd P x}
    (h : spaBasicOpen Aplus j.1.num j.1.den ≤ spaBasicOpen Aplus i.1.num i.1.den) :
    comap (rationalNhdMap hAplus h) (rationalLocalizationPoint hP j.1 x j.2.2) =
      rationalLocalizationPoint hP i.1 x i.2.2 :=
  comap_homOfRationalSubsetSubset_rationalLocalizationPoint hP hAplus i.1 j.1 h x j.2.2

/-- An element of a rational coordinate ring with zero germ at `x` is in the support of the point
of `x`. -/
private theorem vle_zero_of_rationalNhdGerm_eq_zero {x : spa Aplus} {i : RationalNhd P x} {a}
    (ha : rationalNhdGerm hAplus i a = 0) :
    (rationalLocalizationPoint hP i.1 x i.2.2).toValuativeRel.vle a 0 := by
  obtain ⟨q, hq, hxq, h, hqa⟩ := exists_map_homOfRationalSubsetSubset_eq_zero hAplus ha
  have hqa' : rationalNhdMap hAplus (j := ⟨q, hq, hxq⟩) h a = 0 := hqa
  rw [← comap_rationalNhdMap hAplus hP (j := ⟨q, hq, hxq⟩) h, comap_vle, map_zero, hqa']
  exact (rationalLocalizationPoint hP q x hxq).toValuativeRel.vle_refl 0

/-- Elements with the same germ compare in the same way under the points of their rational
neighbourhoods. -/
private theorem rationalNhd_compat {x : spa Aplus} (i j : RationalNhd P x) (a b) (a' b')
    (ha : rationalNhdGerm hAplus i a = rationalNhdGerm hAplus j a')
    (hb : rationalNhdGerm hAplus i b = rationalNhdGerm hAplus j b')
    (hab : (rationalLocalizationPoint hP i.1 x i.2.2).toValuativeRel.vle a b) :
    (rationalLocalizationPoint hP j.1 x j.2.2).toValuativeRel.vle a' b' := by
  obtain ⟨k, hki, hkj⟩ := exists_rationalNhd_le_le i j
  set w := rationalLocalizationPoint hP k.1 x k.2.2
  -- in the common neighbourhood `k`, the two lifts of each germ differ by an element of the
  -- support, so they have the same value
  have hsupp {c c' : _} (hc : rationalNhdGerm hAplus i c = rationalNhdGerm hAplus j c') :
      w.valuation (rationalNhdMap hAplus hkj c') = w.valuation (rationalNhdMap hAplus hki c) := by
    have hmem : rationalNhdMap hAplus hkj c' - rationalNhdMap hAplus hki c ∈ w.supp := by
      rw [mem_supp_iff]
      refine vle_zero_of_rationalNhdGerm_eq_zero hAplus hP ?_
      rw [map_sub, rationalNhdGerm_rationalNhdMap, rationalNhdGerm_rationalNhdMap, hc, sub_self]
    rw [supp_eq_valuation_supp] at hmem
    simpa using w.valuation.map_add_supp (rationalNhdMap hAplus hki c) hmem
  rw [← comap_rationalNhdMap hAplus hP hki, comap_vle, ← valuation_le_iff] at hab
  rw [← comap_rationalNhdMap hAplus hP hkj, comap_vle, ← valuation_le_iff, hsupp ha, hsupp hb]
  exact hab

/-- **The valuation on the stalk** of the presentation-limit presheaf at a point `x` of
`Spa(A,A⁺)`: the point of `Spv 𝒪_{X,x}` which, on the germs of every rational neighbourhood
`R(p)` of `x`, is the point of `A⟨p⟩` that `x` determines under
`Spa (A⟨p⟩, A_p⁺) ≃ₜ R(p)`. -/
noncomputable def presentationLimitStalkValuation (x : spa Aplus) :
    Spv ((presentationLimitPresheafInCommRingCat P Aplus).stalk x) :=
  ofDirected (fun i : RationalNhd P x ↦ rationalNhdGerm hAplus i)
    (w := fun i ↦ rationalLocalizationPoint hP i.1 x i.2.2) (rationalNhd_compat hAplus hP)
    (directed_range_rationalNhdGerm hAplus x) (exists_mem_range_rationalNhdGerm hAplus x)

/-- **The stalk valuation restricts to the rational points**: its pullback along the germ map of
a rational neighbourhood `R(p)` of `x` is the point of `A⟨p⟩` determined by `x`. -/
@[simp]
theorem comap_presentationLimitRationalGerm_presentationLimitStalkValuation (p : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) (x : spa Aplus)
    (hx : x ∈ spaBasicOpen Aplus p.num p.den) :
    comap (presentationLimitRationalGerm hAplus p hp x hx).hom
        (presentationLimitStalkValuation hAplus hP x) =
      rationalLocalizationPoint hP p x hx :=
  comap_ofDirected (fun i : RationalNhd P x ↦ rationalNhdGerm hAplus i) _ _ _ ⟨p, hp, hx⟩

/-- **Uniqueness of the stalk valuation**: a point of the valuation spectrum of the stalk at `x`
whose pullback along the germ map of every rational neighbourhood `R(p)` of `x` is the point of
`A⟨p⟩` determined by `x` is `presentationLimitStalkValuation`. -/
theorem eq_presentationLimitStalkValuation {x : spa Aplus}
    {v : Spv ((presentationLimitPresheafInCommRingCat P Aplus).stalk x)}
    (hv : ∀ (p : Presentation P) (hp : IsOpen (Ideal.span (p.num : Set A) : Set A))
      (hx : x ∈ spaBasicOpen Aplus p.num p.den),
      comap (presentationLimitRationalGerm hAplus p hp x hx).hom v =
        rationalLocalizationPoint hP p x hx) :
    v = presentationLimitStalkValuation hAplus hP x :=
  eq_ofDirected _ _ _ _ fun i ↦ hv i.1 i.2.1 i.2.2

/-- **The stalk valuation lies over `x`**: pulled back to `A` along the structure map `A → A⟨p⟩`
and the germ map of a rational neighbourhood `R(p)` of `x`, the stalk valuation at `x` is `x`. -/
theorem comap_presentationLimitStalkValuation (p : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) (x : spa Aplus)
    (hx : x ∈ spaBasicOpen Aplus p.num p.den) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    comap (CommRingCat.ofHom (toCompletionLoc P p.num p.den _ p.hasDenominatorPower) ≫
        (completionLocObjCommRingCatIso p).inv ≫ presentationLimitRationalGerm hAplus p hp x hx).hom
        (presentationLimitStalkValuation hAplus hP x) = x := by
  rw [← Category.assoc, ← comap_hom_comap_hom,
    comap_presentationLimitRationalGerm_presentationLimitStalkValuation,
    comap_rationalLocalizationPoint]

end

end TauCeti.ValuationSpectrum
