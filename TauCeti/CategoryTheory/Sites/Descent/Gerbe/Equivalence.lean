/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.BandEquivalence
public import TauCeti.CategoryTheory.Sites.Descent.Gerbe.HomSheaf
public import TauCeti.CategoryTheory.Sites.Descent.RelativeGerbe

/-!
# Band-preserving morphisms of gerbes are equivalences

Let `F` and `G` be gerbes on a site `(C, J)` banded by the same sheaf `A` of abelian groups, and let
`η : F ⟶ G` be a band-preserving strong transformation. Its component functors are fully faithful
(`BandedMorphism.fullyFaithful`). They are also essentially surjective (`BandedMorphism.essSurj`):
an object `z` of `G` over `U` is, along the arrows of a covering sieve, isomorphic to images of
objects of `F`, because `F` has objects locally and any two objects of `G` are locally isomorphic;
full faithfulness lifts the descent datum of `z` to a descent datum for `F`, which descends since
`F` is a stack, and the image of the descended object is isomorphic to `z` since `G` is a prestack
(`StrongTrans.essSurj_of_isLocallyEssSurj`).

So every component functor is an equivalence of categories (`BandedMorphism.isEquivalence`), and
`η` is an equivalence in the bicategory of pseudofunctors (`BandedMorphism.equivalence`), whose
inverse has the chosen quasi-inverses of the components of `η` as components and whose unit and
counit have their units and counits as components (`StrongTrans.equivalenceOfIsEquivalence`). The
inverse is band-preserving (`BandedMorphism.bandPreserving_equivalence_inv`), by
`GerbeBandEquivalence.inverse_preserving`. This is Olsson, Lemma 31.3.

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.BandedMorphism`:

* `essSurj`, `isEquivalence`: the component functors of a band-preserving morphism of gerbes are
  essentially surjective, hence equivalences of categories.
* `equivalence`: a band-preserving morphism of gerbes is an equivalence of pseudofunctors, with
  `equivalence_hom`.
* `bandPreserving_equivalence_inv`: its inverse is band-preserving.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Lemma 31.3
-/

public section

universe w v u v' u'

open CategoryTheory Opposite Bicategory
open scoped Pseudofunctor.StrongTrans

namespace CategoryTheory.Pseudofunctor.BandedMorphism

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{w}} (bF : F.AbelianBanding J A)
  (bG : G.AbelianBanding J A) (η : StrongTrans F G) [BandPreserving bF bG η]
  [F.IsGerbe J] [G.IsGerbe J]

include bF bG in
/-- **Essential surjectivity.** The component functors of a band-preserving morphism of gerbes are
essentially surjective (Olsson, Lemma 31.3). -/
theorem essSurj (U : C) : (η.app (.mk (op U))).toFunctor.EssSurj :=
  -- A morphism of gerbes is locally essentially surjective: over a covering sieve on which `F`
  -- has objects `x`, the objects `η x` and the pullback of `z` are locally isomorphic.
  have : η.IsLocallyEssSurj J := ⟨fun {U} z ↦ by
    obtain ⟨R, hR, hx⟩ := IsGerbe.exists_covering_nonempty (F := F) (J := J) U
    choose S hS e using fun (V : C) (f : V ⟶ U) (hf : R f) ↦ IsGerbe.exists_covering_iso (J := J)
      ((η.app (.mk (op V))).toFunctor.obj (hx f hf).some) ((G.map f.op.toLoc).toFunctor.obj z)
    refine ⟨Sieve.bind R fun V f hf ↦ S V f hf, J.bind_covering hR fun V f hf ↦ hS V f hf, ?_⟩
    rintro W _ ⟨V, g, f, hf, hg, rfl⟩
    exact ⟨(F.map g.op.toLoc).toFunctor.obj (hx f hf).some,
      ⟨η.naturalityObjIso g.op.toLoc _ ≪≫ (e V f hf g hg).some ≪≫
        ((Cat.Hom.toNatIso (G.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc
          (by rw [op_comp, Quiver.Hom.comp_toLoc]))).app z).symm⟩⟩⟩
  StrongTrans.essSurj_of_isLocallyEssSurj (J := J) η (fullyFaithful bF bG η) U

include bF bG in
/-- The component functors of a band-preserving morphism of gerbes are equivalences of
categories (Olsson, Lemma 31.3). -/
theorem isEquivalence (U : C) : (η.app (.mk (op U))).toFunctor.IsEquivalence :=
  have := (fullyFaithful bF bG η U).full
  have := (fullyFaithful bF bG η U).faithful
  have := essSurj bF bG η U
  { }

/-- **A band-preserving morphism of gerbes is an equivalence** of pseudofunctors (Olsson,
Lemma 31.3). The components of its inverse are the chosen quasi-inverses of the components of
`η`, and the components of its unit and counit are their units and counits
(`StrongTrans.equivalenceOfIsEquivalence`). -/
noncomputable def equivalence : Bicategory.Equivalence F G :=
  have (a : LocallyDiscrete Cᵒᵖ) : (η.app a).toFunctor.IsEquivalence := isEquivalence bF bG η _
  η.equivalenceOfIsEquivalence

/-- The equivalence of a band-preserving morphism of gerbes has that morphism as its forward
transformation. -/
@[simp]
theorem equivalence_hom : (equivalence bF bG η).hom = η :=
  (rfl)

/-- **The inverse of a band-preserving morphism of gerbes preserves the band.** -/
instance bandPreserving_equivalence_inv : BandPreserving bG bF (equivalence bF bG η).inv :=
  have (U : C) : (η.app (.mk (op U))).toFunctor.IsEquivalence := isEquivalence bF bG η U
  -- The components of the inverse are the quasi-inverses of the components of `η`
  -- (`StrongTrans.equivalenceOfIsEquivalence_inv_app`).
  GerbeBandEquivalence.inverse_preserving (η := η) _ fun _ ↦ Iso.refl _

end CategoryTheory.Pseudofunctor.BandedMorphism
