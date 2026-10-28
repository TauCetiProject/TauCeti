/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import TauCeti.CategoryTheory.DG.ClosedCategory
public import TauCeti.CategoryTheory.DG.CochainComplex.Basic

/-!
# The homotopy category of the DG category of cochain complexes

Cochain complexes in an `R`-linear preadditive category `C` form a differential graded category
through the linear Hom complexes `CochainComplex.linearHomComplex`. This file identifies the
ordinary
categories attached to that DG category with Mathlib's categories of cochain complexes:

* the closed degree-zero morphisms `F ⟶ G` are exactly the cochain maps, as an `R`-linear
  equivalence with Mathlib's morphisms of complexes;
* two cochain maps differ by the differential of a degree `-1` morphism exactly when they are
  homotopic;
* hence the underlying category of the enrichment, Mathlib's `ForgetEnrichment`, is equivalent to
  `CochainComplex C ℤ`, and the homotopy category `H⁰` of the DG category is equivalent to
  Mathlib's `HomotopyCategory C (ComplexShape.up ℤ)`, compatibly with the two quotient functors.

These identifications are what allow constructions with the DG category of complexes, such as
its differential graded nerve, to be compared with Mathlib's homotopy and derived categories of
`C`. For instance, `C` may be the category of sheaves of modules on a ringed site.

## Main definitions

* `TauCeti.cochainHomLinearEquivDGCycles`: cochain maps are the closed degree-zero morphisms.
* `TauCeti.cochainComplexToDGClosed`: the functor from `CochainComplex C ℤ` to the underlying
  category of the DG enrichment. It is fully faithful (`fullyFaithfulCochainComplexToDGClosed`)
  and an equivalence.
* `TauCeti.homotopyCategoryToDGHomotopyCategory`: the induced functor from Mathlib's homotopy
  category to `H⁰` of the DG category. It is an `R`-linear equivalence.

## Main results

* `TauCeti.cochainHomLinearEquivDGCycles_sub_mem_dgBoundaries_iff`: the difference of two cochain
  maps is a boundary exactly when the maps are homotopic.
* `TauCeti.homOf_cochainHomLinearEquivDGCycles_eq_iff`: two cochain maps have the same class in
  `H⁰` exactly when they are homotopic.
* `TauCeti.quotient_comp_homotopyCategoryToDGHomotopyCategory`: the comparison of homotopy
  categories is compatible with the quotient functors.

## References

* J. Lurie, *Higher Algebra*, Definition 1.3.2.1 and Remark 1.3.2.2.
* B. Keller, *Deriving DG categories*, Section 2.2.
-/

public section

noncomputable section

open CategoryTheory CochainComplex.HomComplex

namespace TauCeti

universe v u

variable (R : Type v) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-! ### Closed morphisms are cochain maps -/

/-- **Closed degree-zero morphisms of cochain complexes are cochain maps**: the closed
degree-zero elements of the Hom complex from `F` to `G` are exactly the cochains `Cochain.ofHom f`
of cochain maps `f : F ⟶ G`. -/
def cochainHomLinearEquivDGCycles (F G : CochainComplex C ℤ) :
    (F ⟶ G) ≃ₗ[R] dgCycles R F G where
  toFun f := ⟨(Cochain.ofHom f : ModuleCat.of R (Cochain F G 0)),
    (mem_dgCycles R).2 ((dgDifferential_linearHomComplex R 0 _).trans (δ_ofHom f))⟩
  invFun z := Cocycle.homOf ⟨z.1, (Cocycle.mem_iff 0 1 (zero_add 1) _).2
    ((dgDifferential_linearHomComplex R 0 z.1).symm.trans ((mem_dgCycles R).1 z.2))⟩
  left_inv f := Cocycle.homOf_ofHom_eq_self f
  right_inv _ := Subtype.ext (Cocycle.cochain_ofHom_homOf_eq_coe _)
  map_add' f g := Subtype.ext (Cochain.ofHom_add f g)
  map_smul' r f := Subtype.ext (Cochain.ofHom_smul r f)

/-- The closed morphism attached to a cochain map `f` is the cochain `Cochain.ofHom f`. -/
@[simp]
theorem cochainHomLinearEquivDGCycles_apply_coe {F G : CochainComplex C ℤ} (f : F ⟶ G) :
    ((cochainHomLinearEquivDGCycles R F G f : DGHom R 0 F G) : Cochain F G 0) = Cochain.ofHom f :=
  (rfl)

/-- The cochain map attached to a closed degree-zero morphism `z` has the diagonal components of
`z` as its components. -/
@[simp]
theorem cochainHomLinearEquivDGCycles_symm_apply_f {F G : CochainComplex C ℤ}
    (z : dgCycles R F G) (n : ℤ) :
    ((cochainHomLinearEquivDGCycles R F G).symm z).f n =
      ((z : DGHom R 0 F G) : Cochain F G 0).v n n (add_zero n) :=
  (rfl)

/-- **Boundaries are homotopies**: two cochain maps differ by the differential of a degree `-1`
morphism of the DG category of cochain complexes exactly when they are homotopic. -/
theorem cochainHomLinearEquivDGCycles_sub_mem_dgBoundaries_iff {F G : CochainComplex C ℤ}
    (f g : F ⟶ G) :
    (cochainHomLinearEquivDGCycles R F G f : DGHom R 0 F G) -
        cochainHomLinearEquivDGCycles R F G g ∈ dgBoundaries R F G ↔
      Nonempty (Homotopy f g) := by
  rw [mem_dgBoundaries]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨(Cochain.equivHomotopy f g).symm
      ⟨h, sub_eq_iff_eq_add.1 ((dgDifferential_linearHomComplex R (-1) h).symm.trans hh).symm⟩⟩
  · rintro ⟨H⟩
    obtain ⟨h, hh⟩ := Cochain.equivHomotopy f g H
    exact ⟨h, (dgDifferential_linearHomComplex R (-1) h).trans (sub_eq_iff_eq_add.2 hh).symm⟩

/-- Composition of closed degree-zero morphisms of cochain complexes is composition of cochain
maps. -/
theorem dgCompZero_cochainHomLinearEquivDGCycles {F G K : CochainComplex C ℤ} (f : F ⟶ G)
    (g : G ⟶ K) :
    dgCompZero R (cochainHomLinearEquivDGCycles R F G f : DGHom R 0 F G)
        (cochainHomLinearEquivDGCycles R G K g) =
      (cochainHomLinearEquivDGCycles R F K (f ≫ g) : DGHom R 0 F K) :=
  (dgCompZero_def R _ _).trans ((dgComp_linearHomComplex R _ _ (zero_add 0)).trans (by
    rw [mul_zero, Int.negOnePow_zero, one_smul]
    exact (Cochain.ofHom_comp f g).symm))

/-- The identity cochain map is the identity of the DG category of cochain complexes. -/
theorem cochainHomLinearEquivDGCycles_id (K : CochainComplex C ℤ) :
    (cochainHomLinearEquivDGCycles R K K (𝟙 K) : DGHom R 0 K K) = dgId R K :=
  (dgId_linearHomComplex R K).symm

/-! ### The underlying category -/

variable (C) in
/-- The functor regarding a cochain map as a closed degree-zero morphism of the DG category of
cochain complexes, that is, as a morphism of Mathlib's underlying category `ForgetEnrichment` of
the enrichment. It is the identity on objects and an equivalence of categories. -/
@[expose]
def cochainComplexToDGClosed :
    CochainComplex C ℤ ⥤
      ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) (CochainComplex C ℤ) where
  obj K := ForgetEnrichment.of _ K
  map {F G} f := dgClosedHomOf R _ (cochainHomLinearEquivDGCycles R F G f).2
  map_id K := dgClosedHom_injective R (by
    rw [dgClosedHom_dgClosedHomOf, dgClosedHom_id]
    exact cochainHomLinearEquivDGCycles_id R K)
  map_comp f g := dgClosedHom_injective R (by
    rw [dgClosedHom_dgClosedHomOf, dgClosedHom_comp, dgClosedHom_dgClosedHomOf,
      dgClosedHom_dgClosedHomOf]
    exact (dgCompZero_cochainHomLinearEquivDGCycles R f g).symm)

/-- The functor `TauCeti.cochainComplexToDGClosed` is the identity on complexes. -/
@[simp]
theorem cochainComplexToDGClosed_obj (K : CochainComplex C ℤ) :
    (cochainComplexToDGClosed R C).obj K = ForgetEnrichment.of _ K :=
  (rfl)

/-- The closed degree-zero component of the image of a cochain map `f` is `Cochain.ofHom f`. -/
@[simp]
theorem dgClosedHom_cochainComplexToDGClosed_map {F G : CochainComplex C ℤ} (f : F ⟶ G) :
    dgClosedHom R ((cochainComplexToDGClosed R C).map f) =
      (cochainHomLinearEquivDGCycles R F G f).1 :=
  dgClosedHom_dgClosedHomOf R _ _

/-- The functor `TauCeti.cochainComplexToDGClosed` is fully faithful: a morphism of the underlying
category is the image of the cochain map corresponding to its closed degree-zero component. -/
def fullyFaithfulCochainComplexToDGClosed : (cochainComplexToDGClosed R C).FullyFaithful where
  preimage {F G} g :=
    (cochainHomLinearEquivDGCycles R F G).symm ⟨dgClosedHom R g, dgClosedHom_mem_dgCycles R g⟩
  map_preimage {F G} _ := dgClosedHom_injective R
    ((dgClosedHom_cochainComplexToDGClosed_map R _).trans
      (congrArg Subtype.val ((cochainHomLinearEquivDGCycles R F G).apply_symm_apply _)))
  preimage_map {F G} f := (cochainHomLinearEquivDGCycles R F G).symm_apply_eq.2
    (Subtype.ext (dgClosedHom_cochainComplexToDGClosed_map R f))

instance : (cochainComplexToDGClosed R C).Full :=
  (fullyFaithfulCochainComplexToDGClosed R).full

instance : (cochainComplexToDGClosed R C).Faithful :=
  (fullyFaithfulCochainComplexToDGClosed R).faithful

instance : (cochainComplexToDGClosed R C).EssSurj where
  mem_essImage K := ⟨ForgetEnrichment.to _ K, ⟨Iso.refl _⟩⟩

instance : (cochainComplexToDGClosed R C).IsEquivalence where

/-! ### The homotopy category -/

/-- Two cochain maps have the same class in the homotopy category of the DG category of cochain
complexes exactly when they are homotopic. -/
theorem homOf_cochainHomLinearEquivDGCycles_eq_iff {F G : CochainComplex C ℤ} (f g : F ⟶ G) :
    DGHomotopyCategory.homOf R _ (cochainHomLinearEquivDGCycles R F G f).2 =
        DGHomotopyCategory.homOf R _ (cochainHomLinearEquivDGCycles R F G g).2 ↔
      Nonempty (Homotopy f g) := by
  rw [DGHomotopyCategory.homOf_eq_iff, cochainHomLinearEquivDGCycles_sub_mem_dgBoundaries_iff]

/-- The quotient functor from the underlying category of the DG enrichment sends a cochain map to
the homotopy class of the corresponding closed degree-zero morphism. -/
theorem cochainComplexToDGClosed_comp_dgClosedToHomotopy_map {F G : CochainComplex C ℤ}
    (f : F ⟶ G) :
    (cochainComplexToDGClosed R C ⋙ dgClosedToHomotopy R).map f =
      DGHomotopyCategory.homOf R _ (cochainHomLinearEquivDGCycles R F G f).2 := by
  simp only [Functor.comp_map, dgClosedToHomotopy_map, dgClosedHom_cochainComplexToDGClosed_map]
  -- The two sides now agree except that the Hom type on the left is written with the objects
  -- `(cochainComplexToDGClosed R C ⋙ dgClosedToHomotopy R).obj K`, which reduce to
  -- `DGHomotopyCategory.of R K`.
  rfl

variable (C) in
/-- The functor from Mathlib's homotopy category of cochain complexes to the homotopy category
`H⁰` of the DG category of cochain complexes, sending the class of a cochain map to the class of
the corresponding closed degree-zero morphism. It is an `R`-linear equivalence of categories. -/
@[expose]
def homotopyCategoryToDGHomotopyCategory :
    HomotopyCategory C (ComplexShape.up ℤ) ⥤ DGHomotopyCategory R (CochainComplex C ℤ) :=
  CategoryTheory.Quotient.lift _ (cochainComplexToDGClosed R C ⋙ dgClosedToHomotopy R)
    fun _ _ f g ⟨h⟩ ↦ (cochainComplexToDGClosed_comp_dgClosedToHomotopy_map R f).trans
      (((homOf_cochainHomLinearEquivDGCycles_eq_iff R f g).2 ⟨h⟩).trans
        (cochainComplexToDGClosed_comp_dgClosedToHomotopy_map R g).symm)

/-- The comparison of homotopy categories is compatible with the quotient functors from
cochain complexes and from the underlying category of the DG enrichment. -/
theorem quotient_comp_homotopyCategoryToDGHomotopyCategory :
    HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ homotopyCategoryToDGHomotopyCategory R C =
      cochainComplexToDGClosed R C ⋙ dgClosedToHomotopy R :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- The comparison functor is the identity on underlying complexes. -/
@[simp]
theorem homotopyCategoryToDGHomotopyCategory_obj_quotient_obj (K : CochainComplex C ℤ) :
    (homotopyCategoryToDGHomotopyCategory R C).obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) =
      DGHomotopyCategory.of R K :=
  (rfl)

/-- The comparison functor sends the homotopy class of a cochain map `f` to the class in `H⁰` of
the closed degree-zero morphism `Cochain.ofHom f`. -/
@[simp]
theorem homotopyCategoryToDGHomotopyCategory_map_quotient_map {F G : CochainComplex C ℤ}
    (f : F ⟶ G) :
    (homotopyCategoryToDGHomotopyCategory R C).map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) =
      DGHomotopyCategory.homOf R _ (cochainHomLinearEquivDGCycles R F G f).2 :=
  (CategoryTheory.Quotient.lift_map_functor_map _ _ _ f).trans
    (cochainComplexToDGClosed_comp_dgClosedToHomotopy_map R f)

instance : (homotopyCategoryToDGHomotopyCategory R C).Full where
  map_surjective {X Y} g := by
    obtain ⟨F, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨z, hz, rfl⟩ := DGHomotopyCategory.exists_homOf_eq R g
    refine ⟨(HomotopyCategory.quotient C _).map
      ((cochainHomLinearEquivDGCycles R F G).symm ⟨z, hz⟩), ?_⟩
    refine (homotopyCategoryToDGHomotopyCategory_map_quotient_map R _).trans ?_
    simp only [LinearEquiv.apply_symm_apply]
    -- As above, the Hom types on the two sides differ only by the reduction of the objects
    -- `(homotopyCategoryToDGHomotopyCategory R C).obj ((HomotopyCategory.quotient C _).obj K)`.
    rfl

instance : (homotopyCategoryToDGHomotopyCategory R C).Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨F, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C _).map_surjective f
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C _).map_surjective g
    refine HomotopyCategory.eq_of_homotopy f g ((homOf_cochainHomLinearEquivDGCycles_eq_iff R f g).1
      ?_).some
    exact (homotopyCategoryToDGHomotopyCategory_map_quotient_map R f).symm.trans
      (h.trans (homotopyCategoryToDGHomotopyCategory_map_quotient_map R g))

instance : (homotopyCategoryToDGHomotopyCategory R C).EssSurj where
  mem_essImage X := ⟨(HomotopyCategory.quotient C _).obj (DGHomotopyCategory.underlying R X),
    ⟨eqToIso (DGHomotopyCategory.of_underlying R X)⟩⟩

instance : (homotopyCategoryToDGHomotopyCategory R C).IsEquivalence where

instance : (homotopyCategoryToDGHomotopyCategory R C).Linear R where
  map_smul {X Y} f r := by
    obtain ⟨F, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C _).map_surjective f
    rw [← Functor.map_smul]
    refine (homotopyCategoryToDGHomotopyCategory_map_quotient_map R (r • f)).trans ?_
    refine Eq.trans ?_
      (congrArg (r • ·) (homotopyCategoryToDGHomotopyCategory_map_quotient_map R f)).symm
    simp only [map_smul, Submodule.coe_smul]
    exact DGHomotopyCategory.homOf_smul R r _ _

end TauCeti
