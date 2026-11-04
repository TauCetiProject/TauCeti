/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.KInjective
public import TauCeti.AlgebraicTopology.DGNerve.HomotopyCategory
public import TauCeti.CategoryTheory.DG.CochainComplex.HomotopyCategory
public import TauCeti.CategoryTheory.DG.QuasiEquivalence

/-!
# The K-injective DG model of the derived category

Let `C` be an `R`-linear abelian category. The K-injective cochain complexes in `C` form a full
DG subcategory `TauCeti.KInjectiveDGCategory C` of the DG category of cochain complexes. Its
homotopy category `H⁰` embeds fully faithfully into Mathlib's homotopy category `K(C)`, with
the K-injective complexes as image. Morphisms in `K(C)` into a K-injective complex are the
morphisms in the derived category (`CochainComplex.IsKInjective.Qh_map_bijective`), so the
localization functor `DerivedCategory.Qh` restricts to a fully faithful functor
`TauCeti.KInjectiveDGCategory.toDerivedCategory R C : H⁰ ⥤ D(C)`. When every complex, bounded or
not, has a K-injective resolution (`TauCeti.HasKInjectiveResolutions C`), it is essentially
surjective, hence an equivalence.

Combined with the identification of the homotopy category of a differential graded nerve with
`H⁰` (`TauCeti.dgNerve.homotopyCategoryEquiv`), under `TauCeti.HasKInjectiveResolutions C` this
shows that the differential graded nerve of the K-injective complexes, which is a quasicategory,
has homotopy category `D(C)`
(`TauCeti.KInjectiveDGCategory.dgNerveHomotopyCategoryEquiv`). This is the classical
enhancement of an unbounded derived category: its higher simplices record homotopies between
chain maps and the coherences among them, which the derived category forgets.

## Main definitions

* `TauCeti.KInjectiveDGCategory C`: the full DG subcategory of K-injective cochain complexes.
* `TauCeti.KInjectiveDGCategory.toDerivedCategory R C`: the comparison functor from its homotopy
  category to `DerivedCategory C`, sending a K-injective complex `K` to `Qh` of its class.
* `TauCeti.KInjectiveDGCategory.dgNerveHomotopyCategoryEquiv R C`: the equivalence between the
  homotopy category of the differential graded nerve of K-injective complexes and
  `DerivedCategory C`.

## Main results

* `TauCeti.KInjectiveDGCategory.toDerivedCategory_map_homOf`: the comparison functor sends the class
  of a chain map `f` to `Qh` of its homotopy class.
* The comparison functor is full and faithful, and, under `TauCeti.HasKInjectiveResolutions C`,
  essentially surjective, so it is an equivalence.

## References

* J. Lurie, *Higher Algebra*, Definition 1.3.5.8 and Proposition 1.3.5.15.
* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
* B. Keller, *Deriving DG categories*, Section 2.
-/

public section

noncomputable section

open CategoryTheory DerivedCategory

namespace TauCeti

universe w v u

variable (R : Type v) [CommRing R] (C : Type u) [Category.{v} C] [Abelian C]

/-- The full DG subcategory of the DG category of cochain complexes in `C` on the K-injective
complexes. -/
abbrev KInjectiveDGCategory :=
  DGFullSubcategory (fun K : CochainComplex C ℤ ↦ K.IsKInjective)

namespace KInjectiveDGCategory

variable [Linear R C]

variable [HasDerivedCategory.{w} C]

/-- The comparison functor from the homotopy category `H⁰` of the K-injective complexes to the
derived category. It sends a K-injective complex `K` to `Qh` of its class in `K(C)`, and the class
of a closed degree-zero morphism to `Qh` of the corresponding homotopy class of chain maps. -/
@[expose]
def toDerivedCategory : DGHomotopyCategory R (KInjectiveDGCategory C) ⥤ DerivedCategory C where
  obj X := Qh.obj ((HomotopyCategory.quotient C _).obj (DGHomotopyCategory.underlying R X).obj)
  map {X Y} f := Qh.map ((homotopyCategoryToDGHomotopyCategory R C).preimage
    (eqToHom (DGFullSubcategory.homotopyCategoryToDGHomotopyCategory_obj_eq R X) ≫
      (DGFullSubcategory.inclusion (R := R)).mapDGHomotopyCategory.map f ≫
        eqToHom (DGFullSubcategory.homotopyCategoryToDGHomotopyCategory_obj_eq R Y).symm))
  map_id X := by simp
  map_comp f g := by
    rw [← Functor.map_comp, ← Functor.preimage_comp]
    simp

/-- The comparison functor sends a K-injective complex to `Qh` of its class in `K(C)`. -/
@[simp]
theorem toDerivedCategory_obj (X : DGHomotopyCategory R (KInjectiveDGCategory C)) :
    (toDerivedCategory R C).obj X =
      Qh.obj ((HomotopyCategory.quotient C _).obj (DGHomotopyCategory.underlying R X).obj) :=
  (rfl)

variable {C} in
/-- The comparison functor acts on a morphism through its image in `H⁰` of all cochain complexes,
identified with a morphism of Mathlib's homotopy category. -/
theorem toDerivedCategory_map {X Y : DGHomotopyCategory R (KInjectiveDGCategory C)}
    (f : X ⟶ Y) :
    (toDerivedCategory R C).map f = Qh.map ((homotopyCategoryToDGHomotopyCategory R C).preimage
      (eqToHom (DGFullSubcategory.homotopyCategoryToDGHomotopyCategory_obj_eq R X) ≫
        (DGFullSubcategory.inclusion (R := R)).mapDGHomotopyCategory.map f ≫
          eqToHom (DGFullSubcategory.homotopyCategoryToDGHomotopyCategory_obj_eq R Y).symm)) :=
  (rfl)

/-- The comparison functor sends the class of the closed degree-zero morphism `Cochain.ofHom f`
given by a chain map `f : K ⟶ L` of K-injective complexes to `Qh` of the homotopy class of `f`. -/
@[simp]
theorem toDerivedCategory_map_homOf {K L : CochainComplex C ℤ} [K.IsKInjective]
    [L.IsKInjective] (f : K ⟶ L)
    (hf : CochainComplex.HomComplex.Cochain.ofHom f ∈
      dgCycles R (⟨K, ‹_›⟩ : KInjectiveDGCategory C) ⟨L, ‹_›⟩) :
    (toDerivedCategory R C).map (DGHomotopyCategory.homOf R _ hf) =
      Qh.map ((HomotopyCategory.quotient C _).map f) := by
  rw [toDerivedCategory_map]
  congr 1
  apply (homotopyCategoryToDGHomotopyCategory R C).map_injective
  simp only [Functor.map_preimage, DGFullSubcategory.mapDGHomotopyCategory_inclusion_map_homOf,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  have h := homotopyCategoryToDGHomotopyCategory_map_quotient_map R f
  simp only [cochainHomLinearEquivDGCycles_apply_coe] at h
  refine Eq.trans ?_ h.symm
  exact ((conj_eqToHom_iff_heq' _ _ _ _).2 HEq.rfl).symm

instance : (toDerivedCategory R C).Faithful where
  map_injective {X Y} f g h := by
    have := (DGFullSubcategory.isQuasiFullyFaithful_inclusion (R := R)
      (P := fun K : CochainComplex C ℤ ↦ K.IsKInjective)).faithful_mapDGHomotopyCategory
    have : (DGHomotopyCategory.underlying R Y).obj.IsKInjective :=
      (DGHomotopyCategory.underlying R Y).property
    rw [toDerivedCategory_map, toDerivedCategory_map] at h
    have h' := congrArg (homotopyCategoryToDGHomotopyCategory R C).map
      ((CochainComplex.IsKInjective.Qh_map_bijective _ _).injective h)
    simpa only [Functor.map_preimage, cancel_epi, cancel_mono, Functor.map_injective_iff] using h'

instance : (toDerivedCategory R C).Full where
  map_surjective {X Y} g := by
    have := (DGFullSubcategory.isQuasiFullyFaithful_inclusion (R := R)
      (P := fun K : CochainComplex C ℤ ↦ K.IsKInjective)).full_mapDGHomotopyCategory
    have : (DGHomotopyCategory.underlying R Y).obj.IsKInjective :=
      (DGHomotopyCategory.underlying R Y).property
    obtain ⟨h, rfl⟩ := (CochainComplex.IsKInjective.Qh_map_bijective _ _).surjective g
    obtain ⟨f, hf⟩ := (DGFullSubcategory.inclusion (R := R)).mapDGHomotopyCategory.map_surjective
      (eqToHom (DGFullSubcategory.homotopyCategoryToDGHomotopyCategory_obj_eq R X).symm ≫
        (homotopyCategoryToDGHomotopyCategory R C).map h ≫
          eqToHom (DGFullSubcategory.homotopyCategoryToDGHomotopyCategory_obj_eq R Y))
    refine ⟨f, ?_⟩
    rw [toDerivedCategory_map, hf]
    congr 1
    apply (homotopyCategoryToDGHomotopyCategory R C).map_injective
    simp

/-- The comparison functor is fully faithful: morphisms in the derived category between
K-injective complexes are homotopy classes of chain maps. -/
def fullyFaithfulToDerivedCategory : (toDerivedCategory R C).FullyFaithful :=
  .ofFullyFaithful _

/-- When every complex has a K-injective resolution, every object of the derived category is
isomorphic to the image of a K-injective complex. -/
instance [HasKInjectiveResolutions C] : (toDerivedCategory R C).EssSurj where
  mem_essImage D := ⟨DGHomotopyCategory.of R ⟨((kInjectiveReplacement C).obj D).as, inferInstance⟩,
    ⟨(asIso (kInjectiveReplacementAdjunction C).counit).app D⟩⟩

/-- When every complex has a K-injective resolution, the comparison functor is an equivalence
between the homotopy category of the K-injective complexes and the derived category. -/
instance [HasKInjectiveResolutions C] : (toDerivedCategory R C).IsEquivalence where

/-- **The homotopy category of the differential graded nerve of K-injective complexes is the
derived category.** When every complex has a K-injective resolution, the quasicategory
`dgNerve R (KInjectiveDGCategory C)` enhances `DerivedCategory C`. The functor is the inverse
`TauCeti.dgNerve.fromHomotopyCategory` of the identification of the homotopy category of the nerve
with `H⁰`, followed by the comparison functor `TauCeti.KInjectiveDGCategory.toDerivedCategory`. -/
def dgNerveHomotopyCategoryEquiv [HasKInjectiveResolutions C] :
    (dgNerve R (KInjectiveDGCategory C)).HomotopyCategory ≌ DerivedCategory C :=
  (dgNerve.homotopyCategoryEquiv R _).symm.trans (toDerivedCategory R C).asEquivalence

/-- The functor of `TauCeti.KInjectiveDGCategory.dgNerveHomotopyCategoryEquiv` sends an edge of
the differential graded nerve to the image of its homotopy class under the comparison functor. -/
@[simp]
theorem dgNerveHomotopyCategoryEquiv_functor [HasKInjectiveResolutions C] :
    (dgNerveHomotopyCategoryEquiv R C).functor =
      dgNerve.fromHomotopyCategory R (KInjectiveDGCategory C) ⋙ toDerivedCategory R C := by
  simp [dgNerveHomotopyCategoryEquiv]

end KInjectiveDGCategory

end TauCeti
