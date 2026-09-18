/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational
public import Mathlib.Geometry.RingedSpace.Stalks

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
maps are compatible with the comparison morphisms between rational coordinate rings. It is the
compatibility needed to define and study the valuation on a stalk from the valuations on its
rational neighbourhoods.

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
@[expose] noncomputable def presentationLimitPresheafInCommRingCat (P : PairOfDefinition A)
    (Aplus : Subring A) : (TopCat.of ↥(spa Aplus)).Presheaf CommRingCat.{v} :=
  presentationLimitPresheaf P Aplus ⋙
    TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat

/-- Evaluating the underlying ring presheaf on an open gives the underlying ring of the
presentation limit over that open. -/
@[simp]
theorem presentationLimitPresheafInCommRingCat_obj (P : PairOfDefinition A)
    (Aplus : Subring A) (V : (Opens ↥(spa Aplus))ᵒᵖ) :
    (presentationLimitPresheafInCommRingCat P Aplus).obj V =
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).obj
        (presentationLimit (P := P) Aplus V.unop) :=
  congrArg
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).obj
    (presentationLimitPresheaf_obj P Aplus V)

/-- Restriction in the underlying ring presheaf is the underlying morphism of the reindexing map
between presentation limits. The equality transports account for the sealed evaluation theorem
`presentationLimitPresheaf_obj`. -/
@[simp]
theorem presentationLimitPresheafInCommRingCat_map (P : PairOfDefinition A)
    (Aplus : Subring A) {V W : (Opens ↥(spa Aplus))ᵒᵖ} (h : V ⟶ W) :
    (presentationLimitPresheafInCommRingCat P Aplus).map h =
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
        (eqToHom (presentationLimitPresheaf_obj P Aplus V) ≫
          presentationLimitMap (P := P) (leOfHom h.unop) ≫
            eqToHom (presentationLimitPresheaf_obj P Aplus W).symm) := by
  unfold presentationLimitPresheafInCommRingCat
  rw [Functor.comp_map, presentationLimitPresheaf_map]

/-- `Spa(A,A⁺)` equipped with the underlying commutative-ring presentation-limit presheaf. -/
@[expose] noncomputable def presentationLimitPresheafedSpace (P : PairOfDefinition A)
    (Aplus : Subring A) : PresheafedSpace CommRingCat.{v} where
  carrier := TopCat.of ↥(spa Aplus)
  presheaf := presentationLimitPresheafInCommRingCat P Aplus

@[simp]
theorem presentationLimitPresheafedSpace_carrier (P : PairOfDefinition A)
    (Aplus : Subring A) :
    (presentationLimitPresheafedSpace P Aplus : TopCat) = TopCat.of ↥(spa Aplus) :=
  rfl

@[simp]
theorem presentationLimitPresheafedSpace_presheaf (P : PairOfDefinition A)
    (Aplus : Subring A) :
    (presentationLimitPresheafedSpace P Aplus).presheaf =
      presentationLimitPresheafInCommRingCat P Aplus :=
  rfl

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

/-- The rational comparison isomorphism is the underlying ring map of the comparison
`presentationLimitRationalIso`, after transporting along `presentationLimitPresheaf_obj`. -/
theorem presentationLimitRationalIsoInCommRingCat_hom
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (p : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) :
    (presentationLimitRationalIsoInCommRingCat hAplus p hp).hom =
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
        (eqToHom (presentationLimitPresheaf_obj P Aplus
            (Opposite.op (spaBasicOpen Aplus p.num p.den))) ≫
          (presentationLimitRationalIso Aplus hAplus p hp).hom) := by
  rw [presentationLimitRationalIsoInCommRingCat, Functor.mapIso_hom, Iso.trans_hom, eqToIso.hom]

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

end

end TauCeti.ValuationSpectrum
