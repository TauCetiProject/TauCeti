/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# The homology sequence of a short exact sequence with a biproduct middle term

Let `X ⟶ A ⊞ B ⟶ Z` be a short exact sequence of homological complexes in an abelian category,
with first map `(f₁, f₂)` and second map `g₁ + g₂`. Since homology commutes with binary
biproducts, its homology long exact sequence can be written through `H(A) ⊞ H(B)`:
`⋯ ⟶ Hᵢ(X) ⟶ Hᵢ(A) ⊞ Hᵢ(B) ⟶ Hᵢ(Z) ⟶ Hⱼ(X) ⟶ ⋯`, with first map `(f₁_*, f₂_*)`, second map
`g₁_* + g₂_*` and the connecting morphism of the short exact sequence. This is the form of the
Mayer–Vietoris sequences, both in homology and in cohomology.

## Main results

* `CategoryTheory.ShortComplex.ShortExact.biprod_homology_exact₁`,
  `CategoryTheory.ShortComplex.ShortExact.biprod_homology_exact₂`,
  `CategoryTheory.ShortComplex.ShortExact.biprod_homology_exact₃`: exactness of this sequence at
  `Hⱼ(X)`, at `Hᵢ(A) ⊞ Hᵢ(B)` and at `Hᵢ(Z)`.
-/

public section

open CategoryTheory Limits

attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct

namespace HomologicalComplex

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {X A B Z : HomologicalComplex C c} {f₁ : X ⟶ A} {f₂ : X ⟶ B} {g₁ : A ⟶ Z} {g₂ : B ⟶ Z}

/-- The maps induced on homology by the components of `X ⟶ A ⊞ B ⟶ Z` compose to zero. -/
@[reassoc]
lemma biprod_lift_homologyMap_comp_desc_homologyMap
    (w : biprod.lift f₁ f₂ ≫ biprod.desc g₁ g₂ = 0) (i : ι) :
    biprod.lift (homologyMap f₁ i) (homologyMap f₂ i) ≫
      biprod.desc (homologyMap g₁ i) (homologyMap g₂ i) = 0 := by
  rw [biprod.lift_desc, ← homologyMap_comp, ← homologyMap_comp, ← homologyMap_add,
    ← biprod.lift_desc, w, homologyMap_zero]

variable (A B) in
/-- Homology commutes with the binary biproduct `A ⊞ B`. -/
private noncomputable abbrev homologyBiprodIso (i : ι) :
    (A ⊞ B).homology i ≅ A.homology i ⊞ B.homology i :=
  (homologyFunctor C c i).mapBiprod A B

private lemma homologyMap_lift_comp_homologyBiprodIso_hom (i : ι) :
    homologyMap (biprod.lift f₁ f₂) i ≫ (homologyBiprodIso A B i).hom =
      biprod.lift (homologyMap f₁ i) (homologyMap f₂ i) :=
  biprod.map_lift_mapBiprod (homologyFunctor C c i) _ _ _ _

@[reassoc]
private lemma homologyBiprodIso_hom_comp_desc_homologyMap (i : ι) :
    (homologyBiprodIso A B i).hom ≫
        biprod.desc (homologyMap g₁ i) (homologyMap g₂ i) =
      homologyMap (biprod.desc g₁ g₂) i :=
  biprod.mapBiprod_hom_desc (homologyFunctor C c i) _ _ _ _

/-- The map `Hᵢ(X) ⟶ Hᵢ(A) ⊞ Hᵢ(B)` induced by `(f₁, f₂)` is a monomorphism when the map induced
by `biprod.lift f₁ f₂` is. -/
lemma mono_biprod_lift_homologyMap (i : ι) [Mono (homologyMap (biprod.lift f₁ f₂) i)] :
    Mono (biprod.lift (homologyMap f₁ i) (homologyMap f₂ i)) := by
  rw [← homologyMap_lift_comp_homologyBiprodIso_hom]
  infer_instance

/-- The map `Hᵢ(A) ⊞ Hᵢ(B) ⟶ Hᵢ(Z)` induced by `g₁ + g₂` is an epimorphism when the map induced
by `biprod.desc g₁ g₂` is. -/
lemma epi_biprod_desc_homologyMap (i : ι) [Epi (homologyMap (biprod.desc g₁ g₂) i)] :
    Epi (biprod.desc (homologyMap g₁ i) (homologyMap g₂ i)) :=
  (epi_comp_iff_of_epi (homologyBiprodIso A B i).hom _).1
    (by rw [homologyBiprodIso_hom_comp_desc_homologyMap]; infer_instance)

end HomologicalComplex

namespace CategoryTheory.ShortComplex.ShortExact

open HomologicalComplex

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {X A B Z : HomologicalComplex C c} {f₁ : X ⟶ A} {f₂ : X ⟶ B} {g₁ : A ⟶ Z} {g₂ : B ⟶ Z}
  {w : biprod.lift f₁ f₂ ≫ biprod.desc g₁ g₂ = 0} (hS : (ShortComplex.mk _ _ w).ShortExact)

include hS

/-- The connecting morphism of a short exact sequence `X ⟶ A ⊞ B ⟶ Z` followed by the map
`Hⱼ(X) ⟶ Hⱼ(A) ⊞ Hⱼ(B)` is zero. -/
@[reassoc (attr := simp)]
lemma δ_comp_biprod_lift_homologyMap (i j : ι) (hij : c.Rel i j) :
    hS.δ i j hij ≫
      biprod.lift (HomologicalComplex.homologyMap f₁ j) (HomologicalComplex.homologyMap f₂ j) =
        0 := by
  rw [← homologyMap_lift_comp_homologyBiprodIso_hom]
  exact hS.δ_comp_assoc i j hij _ |>.trans zero_comp

/-- The map `Hᵢ(A) ⊞ Hᵢ(B) ⟶ Hᵢ(Z)` induced by a short exact sequence `X ⟶ A ⊞ B ⟶ Z` followed
by its connecting morphism is zero. -/
@[reassoc (attr := simp)]
lemma biprod_desc_homologyMap_comp_δ (i j : ι) (hij : c.Rel i j) :
    biprod.desc (HomologicalComplex.homologyMap g₁ i) (HomologicalComplex.homologyMap g₂ i) ≫
      hS.δ i j hij = 0 := by
  rw [← cancel_epi (homologyBiprodIso A B i).hom, comp_zero,
    homologyBiprodIso_hom_comp_desc_homologyMap_assoc]
  exact hS.comp_δ i j hij

/-- Exactness at `Hⱼ(X)` of the homology sequence of a short exact sequence `X ⟶ A ⊞ B ⟶ Z`. -/
lemma biprod_homology_exact₁ (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk _ _ (hS.δ_comp_biprod_lift_homologyMap i j hij)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1 (hS.homology_exact₁ i j hij)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (homologyBiprodIso A B j) ?_ ?_
  · simp
  · exact (Category.id_comp _).trans (homologyMap_lift_comp_homologyBiprodIso_hom j).symm

/-- Exactness at `Hᵢ(A) ⊞ Hᵢ(B)` of the homology sequence of a short exact sequence
`X ⟶ A ⊞ B ⟶ Z`. -/
lemma biprod_homology_exact₂ (i : ι) :
    (ShortComplex.mk _ _
      (HomologicalComplex.biprod_lift_homologyMap_comp_desc_homologyMap w i)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1 (hS.homology_exact₂ i)
  refine ShortComplex.isoMk (Iso.refl _)
    (homologyBiprodIso A B i) (Iso.refl _) ?_ ?_
  · exact (Category.id_comp _).trans (homologyMap_lift_comp_homologyBiprodIso_hom i).symm
  · exact (homologyBiprodIso_hom_comp_desc_homologyMap i).trans (Category.comp_id _).symm

/-- Exactness at `Hᵢ(Z)` of the homology sequence of a short exact sequence `X ⟶ A ⊞ B ⟶ Z`. -/
lemma biprod_homology_exact₃ (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk _ _ (hS.biprod_desc_homologyMap_comp_δ i j hij)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1 (hS.homology_exact₃ i j hij)
  refine ShortComplex.isoMk (homologyBiprodIso A B i)
    (Iso.refl _) (Iso.refl _) ?_ ?_
  · exact (homologyBiprodIso_hom_comp_desc_homologyMap i).trans (Category.comp_id _).symm
  · simp

end CategoryTheory.ShortComplex.ShortExact
