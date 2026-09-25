/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational
public import Mathlib.Geometry.RingedSpace.Stalks
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# The presentation-limit presheaf and its stalks as rings

The presentation-limit presheaf is naturally valued in complete separated topological
commutative rings. Stalks, however, are algebraic colimits: their topology is discarded. This
file forgets the topology on sections, packages the result as a `CommRingCat`-valued
presheafed space, and constructs the canonical germ map from the coordinate ring of every
rational neighbourhood to the stalk.

## Main definitions

* `TauCeti.ValuationSpectrum.presentationLimitPresheafInCommRingCat` is the underlying
  commutative-ring presheaf.
* `TauCeti.ValuationSpectrum.presentationLimitPresheafedSpace` packages it on `Spa(A,A⁺)`.
* `TauCeti.ValuationSpectrum.presentationLimitRationalGerm` maps the coordinate ring of a
  rational neighbourhood to the stalk at a point.

## Main result

`TauCeti.ValuationSpectrum.presentationLimitRationalGerm_res` says that these rational germ
maps are compatible with the comparison morphisms between rational coordinate rings.
`exists_presentationLimitRationalGerm_eq` says every germ comes from a rational coordinate ring,
and `exists_map_homOfRationalSubsetSubset_eq_zero` says a zero germ restricts to zero on some
smaller rational neighbourhood.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1.
-/

namespace TauCeti.ValuationSpectrum

open AlgebraicGeometry CategoryTheory _root_.TopologicalSpace TauCeti.Huber
  TauCeti.Huber.PairOfDefinition

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The presentation-limit presheaf after forgetting the topology on its section rings.

This is the presheaf whose stalks are the ring colimits used in the locally ringed-space
structure. The topology is forgotten only after taking the limits that define sections. -/
noncomputable def presentationLimitPresheafInCommRingCat (P : PairOfDefinition A)
    (Aplus : Subring A) : (TopCat.of ↥(spa Aplus)).Presheaf CommRingCat.{v} :=
  presentationLimitPresheaf P Aplus ⋙
    TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat

private theorem presentationLimitPresheafInCommRingCat_def (P : PairOfDefinition A)
    (Aplus : Subring A) :
    presentationLimitPresheafInCommRingCat P Aplus = presentationLimitPresheaf P Aplus ⋙
      TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat :=
  rfl

/-- Evaluating the underlying ring presheaf on an open gives the underlying ring of the
presentation limit over that open. -/
@[simp]
theorem presentationLimitPresheafInCommRingCat_obj (P : PairOfDefinition A)
    (Aplus : Subring A) (V : (Opens ↥(spa Aplus))ᵒᵖ) :
    (presentationLimitPresheafInCommRingCat P Aplus).obj V =
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).obj
        (presentationLimit (P := P) Aplus V.unop) :=
  (Functor.congr_obj (presentationLimitPresheafInCommRingCat_def P Aplus) V).trans <|
    congrArg (TopCommRingCat.isCompleteSeparated.ι ⋙
      forget₂ TopCommRingCat CommRingCat).obj (presentationLimitPresheaf_obj P Aplus V)

/-- Restriction in the underlying ring presheaf is the underlying morphism of the reindexing map
between presentation limits. The equality transports account for the sealed evaluation theorem
`presentationLimitPresheaf_obj`. -/
@[simp]
theorem presentationLimitPresheafInCommRingCat_map (P : PairOfDefinition A)
    (Aplus : Subring A) {V W : (Opens ↥(spa Aplus))ᵒᵖ} (h : V ⟶ W) :
    (presentationLimitPresheafInCommRingCat P Aplus).map h ≫
        eqToHom (presentationLimitPresheafInCommRingCat_obj P Aplus W) =
      eqToHom (presentationLimitPresheafInCommRingCat_obj P Aplus V) ≫
        (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
          (presentationLimitMap (P := P) (leOfHom h.unop)) := by
  let e := presentationLimitPresheafInCommRingCat_def P Aplus
  let eV := congrArg
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).obj
    (presentationLimitPresheaf_obj P Aplus V)
  let eW := congrArg
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).obj
    (presentationLimitPresheaf_obj P Aplus W)
  have hV : presentationLimitPresheafInCommRingCat_obj P Aplus V =
      (Functor.congr_obj e V).trans eV := Subsingleton.elim _ _
  have hW : presentationLimitPresheafInCommRingCat_obj P Aplus W =
      (Functor.congr_obj e W).trans eW := Subsingleton.elim _ _
  rw [hV, hW, ← eqToHom_trans (Functor.congr_obj e W) eW,
    ← eqToHom_trans (Functor.congr_obj e V) eV, ← eqToHom_app e W,
    ← eqToHom_app e V, (eqToHom e).naturality_assoc]
  simp only [Functor.comp_map, presentationLimitPresheaf_map, Functor.map_comp, eqToHom_map,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- `Spa(A,A⁺)` equipped with the underlying commutative-ring presentation-limit presheaf. -/
noncomputable def presentationLimitPresheafedSpace (P : PairOfDefinition A)
    (Aplus : Subring A) : PresheafedSpace CommRingCat.{v} where
  carrier := TopCat.of ↥(spa Aplus)
  presheaf := presentationLimitPresheafInCommRingCat P Aplus

private theorem presentationLimitPresheafedSpace_def (P : PairOfDefinition A)
    (Aplus : Subring A) :
    presentationLimitPresheafedSpace P Aplus =
      { carrier := TopCat.of ↥(spa Aplus)
        presheaf := presentationLimitPresheafInCommRingCat P Aplus } :=
  rfl

@[simp]
theorem presentationLimitPresheafedSpace_carrier (P : PairOfDefinition A)
    (Aplus : Subring A) :
    (presentationLimitPresheafedSpace P Aplus : TopCat) = TopCat.of ↥(spa Aplus) :=
  congrArg PresheafedSpace.carrier (presentationLimitPresheafedSpace_def P Aplus)

@[simp]
theorem presentationLimitPresheafedSpace_presheaf (P : PairOfDefinition A)
    (Aplus : Subring A) :
    @HEq (TopCat.Presheaf CommRingCat
      (presentationLimitPresheafedSpace P Aplus).carrier)
      (presentationLimitPresheafedSpace P Aplus).presheaf
      (TopCat.Presheaf CommRingCat (TopCat.of ↥(spa Aplus)))
      (presentationLimitPresheafInCommRingCat P Aplus) := by
  rw [presentationLimitPresheafedSpace_def]

variable {P : PairOfDefinition A} {Aplus : Subring A}

/-- On a rational open, the underlying ring of the presentation limit is the underlying ring of
its rational coordinate ring. -/
noncomputable def presentationLimitRationalIsoInCommRingCat
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (p : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) :
    (presentationLimitPresheafInCommRingCat P Aplus).obj
        (Opposite.op (spaBasicOpen Aplus p.num p.den)) ≅
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).obj
        p.completionLocObj :=
  (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).mapIso
    (eqToIso (presentationLimitPresheaf_obj P Aplus
      (Opposite.op (spaBasicOpen Aplus p.num p.den))) ≪≫
        presentationLimitRationalIso Aplus hAplus p hp)

private theorem presentationLimitRationalIsoInCommRingCat_def
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (p : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) :
    presentationLimitRationalIsoInCommRingCat hAplus p hp =
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).mapIso
        (eqToIso (presentationLimitPresheaf_obj P Aplus
          (Opposite.op (spaBasicOpen Aplus p.num p.den))) ≪≫
            presentationLimitRationalIso Aplus hAplus p hp) :=
  rfl

/-- The rational comparison isomorphism is the underlying ring map of the comparison
`presentationLimitRationalIso`, after transporting along `presentationLimitPresheaf_obj`. -/
@[simp]
theorem presentationLimitRationalIsoInCommRingCat_hom
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (p : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) :
    (presentationLimitRationalIsoInCommRingCat hAplus p hp).hom =
      eqToHom (presentationLimitPresheafInCommRingCat_obj P Aplus
          (Opposite.op (spaBasicOpen Aplus p.num p.den))) ≫
        (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
          (presentationLimitRationalIso Aplus hAplus p hp).hom := by
  rw [presentationLimitRationalIsoInCommRingCat_def]
  simp only [Functor.mapIso_hom, Iso.trans_hom, eqToIso.hom, Functor.comp_map,
    Functor.map_comp, eqToHom_map]
  rfl

/-- The inverse rational comparison is the underlying inverse comparison followed by transport
along `presentationLimitPresheafInCommRingCat_obj`. -/
@[simp]
theorem presentationLimitRationalIsoInCommRingCat_inv
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (p : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) :
    (presentationLimitRationalIsoInCommRingCat hAplus p hp).inv =
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
          (presentationLimitRationalIso Aplus hAplus p hp).inv ≫
        eqToHom (presentationLimitPresheafInCommRingCat_obj P Aplus
          (Opposite.op (spaBasicOpen Aplus p.num p.den))).symm := by
  rw [presentationLimitRationalIsoInCommRingCat_def]
  simp only [Functor.mapIso_inv, Iso.trans_inv, eqToIso.inv, Functor.comp_map,
    Functor.map_comp, eqToHom_map]
  rfl

/-- The rational-open comparison isomorphisms identify restriction with the comparison map of
rational coordinate rings, after forgetting topology. -/
theorem presentationLimitRationalIsoInCommRingCat_inv_comp_map_comp_hom
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (p q : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A))
    (hq : IsOpen (Ideal.span (q.num : Set A) : Set A))
    (h : spaBasicOpen Aplus q.num q.den ≤ spaBasicOpen Aplus p.num p.den) :
    (presentationLimitRationalIsoInCommRingCat hAplus p hp).inv ≫
        (presentationLimitPresheafInCommRingCat P Aplus).map
          (homOfLE h).op ≫
        (presentationLimitRationalIsoInCommRingCat hAplus q hq).hom =
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
        (homOfRationalSubsetSubset Aplus hAplus
          (spaBasicOpen_le_spaBasicOpen_iff.mp h)) := by
  simpa only [presentationLimitRationalIsoInCommRingCat,
    presentationLimitPresheafInCommRingCat, Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.comp_map,
    presentationLimitPresheaf_map, ← Functor.map_comp, Category.assoc, eqToIso.hom,
    eqToIso.inv, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Functor.map_id,
    Category.id_comp, Category.comp_id] using congrArg
      (fun f ↦ (TopCommRingCat.isCompleteSeparated.ι ⋙
        forget₂ TopCommRingCat CommRingCat).map f)
      (presentationLimitRationalIso_inv_comp_map_comp_hom Aplus hAplus p q hp hq h)

/-- The germ map from a rational coordinate ring to the stalk at a point of the corresponding
rational open. It first identifies the coordinate ring with the presentation-limit sections and
then applies the ordinary presheaf germ map. -/
noncomputable def presentationLimitRationalGerm
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (p : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) (x : spa Aplus)
    (hx : x ∈ spaBasicOpen Aplus p.num p.den) :
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).obj
        p.completionLocObj ⟶
      (presentationLimitPresheafInCommRingCat P Aplus).stalk x :=
  (presentationLimitRationalIsoInCommRingCat hAplus p hp).inv ≫
    (presentationLimitPresheafInCommRingCat P Aplus).germ
      (spaBasicOpen Aplus p.num p.den) x hx

/-- The rational germ map is the inverse comparison isomorphism followed by the presheaf germ
map on the rational open. -/
@[simp]
theorem presentationLimitRationalGerm_def
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (p : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) (x : spa Aplus)
    (hx : x ∈ spaBasicOpen Aplus p.num p.den) :
    presentationLimitRationalGerm hAplus p hp x hx =
      (presentationLimitRationalIsoInCommRingCat hAplus p hp).inv ≫
        (presentationLimitPresheafInCommRingCat P Aplus).germ
          (spaBasicOpen Aplus p.num p.den) x hx := by
  rw [presentationLimitRationalGerm]

/-- Rational germ maps commute with restriction: passing from a rational neighbourhood to a
smaller one does not change the resulting germ in the stalk. -/
@[reassoc]
theorem presentationLimitRationalGerm_res
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (p q : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A))
    (hq : IsOpen (Ideal.span (q.num : Set A) : Set A))
    (h : spaBasicOpen Aplus q.num q.den ≤ spaBasicOpen Aplus p.num p.den)
    (x : spa Aplus) (hx : x ∈ spaBasicOpen Aplus q.num q.den) :
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
          (homOfRationalSubsetSubset Aplus hAplus
            (spaBasicOpen_le_spaBasicOpen_iff.mp h)) ≫
        presentationLimitRationalGerm hAplus q hq x hx =
      presentationLimitRationalGerm hAplus p hp x (h hx) := by
  rw [presentationLimitRationalGerm_def, presentationLimitRationalGerm_def,
    ← presentationLimitRationalIsoInCommRingCat_inv_comp_map_comp_hom hAplus p q hp hq h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ (presentationLimitRationalIsoInCommRingCat hAplus p hp).inv ≫ f)
    ((presentationLimitPresheafInCommRingCat P Aplus).germ_res (homOfLE h) x hx)

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

end

end TauCeti.ValuationSpectrum
