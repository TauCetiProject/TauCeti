/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Coproducts in the homotopy category

Let `C` be a preadditive category. Coproducts of homological complexes are computed degreewise,
and homotopies between maps out of a coproduct can be chosen on each summand and glued
(`Homotopy.ofIsColimit`). Hence the quotient functor from complexes to the homotopy category
preserves coproducts, and the homotopy category has all coproducts that `C` has
(`HomotopyCategory.quotient` preserves colimits of every discrete shape `Discrete J` for which `C`
has colimits).

Together with K-injective resolutions, this gives coproducts in unbounded derived categories,
see `TauCeti.Algebra.Homology.DerivedCategory.Coproduct`.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  {J : Type w} {K : Discrete J ⥤ HomologicalComplex C c} {s : Cocone K}

namespace Homotopy

/-- Homotopies glue along a coproduct of complexes which is computed degreewise: two maps out of
the coproduct are homotopic as soon as their restrictions to every summand are. -/
def ofIsColimit (hs : ∀ i, IsColimit ((HomologicalComplex.eval C c i).mapCocone s))
    {L : HomologicalComplex C c} {f g : s.pt ⟶ L}
    (h : ∀ j, Homotopy (s.ι.app j ≫ f) (s.ι.app j ≫ g)) : Homotopy f g :=
  let H (i i' : ι) : s.pt.X i ⟶ L.X i' :=
    (hs i).desc (Cocone.mk _ (Discrete.natTrans fun j ↦ (h j).hom i i'))
  have hH (j : Discrete J) : (fun i i' ↦ (s.ι.app j).f i ≫ H i i') = (h j).hom :=
    funext₂ fun i _ ↦ (hs i).fac _ j
  { hom := H
    zero i i' hii' := (hs i).hom_ext fun j ↦ by
      rw [comp_zero]
      exact ((hs i).fac _ j).trans ((h j).zero i i' hii')
    comm i := (hs i).hom_ext fun j ↦ by
      simp only [Functor.mapCocone_ι_app, HomologicalComplex.eval_map]
      rw [Preadditive.comp_add, Preadditive.comp_add, ← dNext_comp_left, ← prevD_comp_left,
        hH, ← HomologicalComplex.comp_f, (h j).comm i, HomologicalComplex.comp_f] }

@[simp]
lemma ofIsColimit_hom (hs : ∀ i, IsColimit ((HomologicalComplex.eval C c i).mapCocone s))
    {L : HomologicalComplex C c} {f g : s.pt ⟶ L}
    (h : ∀ j, Homotopy (s.ι.app j ≫ f) (s.ι.app j ≫ g)) (j : Discrete J) (i i' : ι) :
    (s.ι.app j).f i ≫ (ofIsColimit hs h).hom i i' = (h j).hom i i' :=
  (hs i).fac _ j

end Homotopy

namespace HomotopyCategory

/-- The image in the homotopy category of a coproduct of complexes which is computed degreewise
is a coproduct. -/
def isColimitMapCoconeQuotient (hs : IsColimit s)
    (hs' : ∀ i, IsColimit ((HomologicalComplex.eval C c i).mapCocone s)) :
    IsColimit ((quotient C c).mapCocone s) where
  desc t := (quotient C c).map (hs.desc (Cocone.mk ((quotient C c).objPreimage t.pt)
      (Discrete.natTrans fun j ↦ (quotient C c).preimage
        (t.ι.app j ≫ ((quotient C c).objObjPreimageIso t.pt).inv)))) ≫
    ((quotient C c).objObjPreimageIso t.pt).hom
  fac t j := by
    rw [Functor.mapCocone_ι_app, ← Functor.map_comp_assoc, hs.fac]
    simp
  uniq t m hm := by
    rw [← Iso.comp_inv_eq]
    obtain ⟨m', hm'⟩ :=
      (quotient C c).map_surjective (m ≫ ((quotient C c).objObjPreimageIso t.pt).inv)
    rw [← hm']
    -- two maps out of the coproduct which agree on the summands up to homotopy are homotopic
    refine eq_of_homotopy _ _ (Homotopy.ofIsColimit hs' fun j ↦ homotopyOfEq _ _ ?_)
    rw [Functor.map_comp, Functor.map_comp, hm', ← Functor.mapCocone_ι_app, reassoc_of% (hm j),
      Functor.mapCocone_ι_app, ← Functor.map_comp, hs.fac]
    simp

variable [HasColimitsOfShape (Discrete J) C]

/-- The quotient functor from complexes to the homotopy category preserves coproducts. -/
instance : PreservesColimitsOfShape (Discrete J) (quotient C c) where
  preservesColimit {K} := preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K)
    (isColimitMapCoconeQuotient (colimit.isColimit K)
      (fun _ ↦ isColimitOfPreserves _ (colimit.isColimit K)))

/-- The homotopy category has the coproducts which exist in `C`. -/
instance : HasColimitsOfShape (Discrete J) (HomotopyCategory C c) where
  has_colimit G := by
    let K : Discrete J ⥤ HomologicalComplex C c := Discrete.functor fun j ↦ (G.obj ⟨j⟩).as
    have : HasColimit (K ⋙ quotient C c) :=
      ⟨⟨⟨_, isColimitOfPreserves (quotient C c) (colimit.isColimit K)⟩⟩⟩
    exact hasColimit_of_iso (Discrete.natIso fun j ↦ Iso.refl _ : G ≅ K ⋙ quotient C c)

end HomotopyCategory
