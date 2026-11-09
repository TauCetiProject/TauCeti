/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Homology of a biproduct of homological complexes

Homology commutes with binary biproducts: `Hᵢ(A ⊞ B) ≅ Hᵢ(A) ⊞ Hᵢ(B)`
(`HomologicalComplex.homologyBiprodIso`). Hence a biproduct `A ⊞ B` of homological complexes is
exact in a degree, or acyclic, exactly when both of its summands are, and the maps induced on
homology by morphisms into and out of `A ⊞ B` can be read off from their components.

## Main results

* `HomologicalComplex.exactAt_biprod_iff`, `HomologicalComplex.acyclic_biprod_iff`: `A ⊞ B` is
  exact in a degree, or acyclic, if and only if `A` and `B` both are.
* `HomologicalComplex.mono_biprod_lift_homologyMap_iff`,
  `HomologicalComplex.epi_biprod_desc_homologyMap_iff`: the map `Hᵢ(X) ⟶ Hᵢ(A) ⊞ Hᵢ(B)` induced
  by `(f₁, f₂)` is mono, and the map `Hᵢ(A) ⊞ Hᵢ(B) ⟶ Hᵢ(Z)` induced by `g₁ + g₂` is epi, exactly
  when the map induced on `Hᵢ(A ⊞ B)` is.
-/

public section

open CategoryTheory Limits

attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct

namespace HomologicalComplex

variable {C ι : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
  [CategoryWithHomology C] {c : ComplexShape ι} (A B : HomologicalComplex C c)

/-- The binary biproduct `A ⊞ B` is exact in degree `i` if and only if `A` and `B` both are. -/
@[simp]
lemma exactAt_biprod_iff (i : ι) : (A ⊞ B).ExactAt i ↔ A.ExactAt i ∧ B.ExactAt i := by
  rw [exactAt_iff_isZero_homology, exactAt_iff_isZero_homology, exactAt_iff_isZero_homology,
    ← biprod_isZero_iff]
  exact ((homologyFunctor C c i).mapBiprod A B).isZero_iff

/-- The binary biproduct `A ⊞ B` is acyclic if and only if `A` and `B` both are. -/
@[simp]
lemma acyclic_biprod_iff : (A ⊞ B).Acyclic ↔ A.Acyclic ∧ B.Acyclic := by
  simp only [Acyclic, exactAt_biprod_iff, forall_and]

/-- Homology commutes with the binary biproduct `A ⊞ B`. -/
noncomputable abbrev homologyBiprodIso (i : ι) :
    (A ⊞ B).homology i ≅ A.homology i ⊞ B.homology i :=
  (homologyFunctor C c i).mapBiprod A B

section

variable {A B} {X Z : HomologicalComplex C c} {f₁ : X ⟶ A} {f₂ : X ⟶ B} {g₁ : A ⟶ Z}
  {g₂ : B ⟶ Z}

/-- The maps induced on homology by the components of `X ⟶ A ⊞ B ⟶ Z` compose to zero. -/
@[reassoc]
lemma biprod_lift_homologyMap_comp_desc_homologyMap
    (w : biprod.lift f₁ f₂ ≫ biprod.desc g₁ g₂ = 0) (i : ι) :
    biprod.lift (homologyMap f₁ i) (homologyMap f₂ i) ≫
      biprod.desc (homologyMap g₁ i) (homologyMap g₂ i) = 0 := by
  rw [biprod.lift_desc, ← homologyMap_comp, ← homologyMap_comp, ← homologyMap_add,
    ← biprod.lift_desc, w, homologyMap_zero]

/-- Under `Hᵢ(A ⊞ B) ≅ Hᵢ(A) ⊞ Hᵢ(B)`, the map induced by `biprod.lift f₁ f₂` becomes the lift of
the maps induced by `f₁` and `f₂`. -/
lemma homologyMap_biprod_lift_comp_homologyBiprodIso_hom (i : ι) :
    homologyMap (biprod.lift f₁ f₂) i ≫ (homologyBiprodIso A B i).hom =
      biprod.lift (homologyMap f₁ i) (homologyMap f₂ i) :=
  biprod.map_lift_mapBiprod (homologyFunctor C c i) _ _ _ _

/-- Under `Hᵢ(A ⊞ B) ≅ Hᵢ(A) ⊞ Hᵢ(B)`, the map induced by `biprod.desc g₁ g₂` becomes the
descent of the maps induced by `g₁` and `g₂`. -/
@[reassoc]
lemma homologyBiprodIso_hom_comp_biprod_desc_homologyMap (i : ι) :
    (homologyBiprodIso A B i).hom ≫
        biprod.desc (homologyMap g₁ i) (homologyMap g₂ i) =
      homologyMap (biprod.desc g₁ g₂) i :=
  biprod.mapBiprod_hom_desc (homologyFunctor C c i) _ _ _ _

/-- The map `Hᵢ(X) ⟶ Hᵢ(A) ⊞ Hᵢ(B)` induced by `(f₁, f₂)` is a monomorphism if and only if the
map induced by `biprod.lift f₁ f₂` is. -/
lemma mono_biprod_lift_homologyMap_iff (i : ι) :
    Mono (biprod.lift (homologyMap f₁ i) (homologyMap f₂ i)) ↔
      Mono (homologyMap (biprod.lift f₁ f₂) i) := by
  rw [← homologyMap_biprod_lift_comp_homologyBiprodIso_hom, mono_comp_iff_of_mono]

/-- The map `Hᵢ(A) ⊞ Hᵢ(B) ⟶ Hᵢ(Z)` induced by `g₁ + g₂` is an epimorphism if and only if the
map induced by `biprod.desc g₁ g₂` is. -/
lemma epi_biprod_desc_homologyMap_iff (i : ι) :
    Epi (biprod.desc (homologyMap g₁ i) (homologyMap g₂ i)) ↔
      Epi (homologyMap (biprod.desc g₁ g₂) i) := by
  rw [← homologyBiprodIso_hom_comp_biprod_desc_homologyMap, epi_comp_iff_of_epi]

end

end HomologicalComplex
