/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.DerivedHom
public import TauCeti.AlgebraicTopology.DGNerve.Equivalence
public import TauCeti.AlgebraicTopology.DGNerve.HomotopyGroups
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

The mapping spaces of this enhancement compute derived Hom groups. For K-injective complexes `K`
and `L`, the path components of the right mapping space from `K` to `L` are the morphisms
`K ⟶ L` in `D(C)`, and its `(n + 1)`-st homotopy group at zero is `K ⟶ L⟦-(n + 1)⟧`, so
`πᵢ Map(K, L) = H⁻ⁱ RHom(K, L)` for all `i ≥ 0`. This combines the Dold–Kan description of the
mapping spaces of a differential graded nerve with the computation of morphisms into a K-injective
complex (`TauCeti.linearHomComplexHomologyLinearEquivOfIsKInjective`). It needs no K-injective
resolutions of other complexes.

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
* `TauCeti.KInjectiveDGCategory.isEquivalence_edgeMk_iff_quasiIso`: an edge represented by a
  chain map is an equivalence precisely when that map is a quasi-isomorphism. Equivalently,
  every integer cohomology map is invertible.
* `TauCeti.KInjectiveDGCategory.rightMappingSpacePiZeroEquiv` and
  `TauCeti.KInjectiveDGCategory.rightMappingSpacePiAddEquiv`: the homotopy groups of the mapping
  spaces are the morphisms `K ⟶ L⟦-i⟧` in the derived category.

## References

* J. Lurie, *Higher Algebra*, Definition 1.3.5.8, Remark 1.3.1.12 and Proposition 1.3.5.15.
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

/-- A chain map between K-injective complexes gives a closed degree-zero morphism in their
full DG subcategory. -/
theorem ofHom_mem_dgCycles {K L : CochainComplex C ℤ} [K.IsKInjective]
    [L.IsKInjective] (f : K ⟶ L) :
    CochainComplex.HomComplex.Cochain.ofHom f ∈
      dgCycles R (⟨K, ‹_›⟩ : KInjectiveDGCategory C) ⟨L, ‹_›⟩ := by
  apply (mem_dgCycles R).2
  rw [DGFullSubcategory.dgDifferential_eq, dgDifferential_linearHomComplex]
  exact CochainComplex.HomComplex.δ_ofHom f

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

omit [HasDerivedCategory C] in
/-- An edge represented by a map of K-injective complexes is an equivalence in the dg nerve
exactly when the map is a quasi-isomorphism. Existence of K-injective resolutions for other
complexes is not required. -/
theorem isEquivalence_edgeMk_iff_quasiIso {K L : CochainComplex C ℤ} [K.IsKInjective]
    [L.IsKInjective] (f : K ⟶ L)
    (hf : CochainComplex.HomComplex.Cochain.ofHom f ∈
      dgCycles R (⟨K, ‹_›⟩ : KInjectiveDGCategory C) ⟨L, ‹_›⟩ := ofHom_mem_dgCycles R C f) :
    (dgNerve.edgeMk R (KInjectiveDGCategory C) ⟨_, hf⟩).IsEquivalence ↔ QuasiIso f := by
  let := HasDerivedCategory.standard C
  rw [dgNerve.isEquivalence_edgeMk_iff]
  refine (isIso_iff_of_reflects_iso _ (toDerivedCategory R C)).symm.trans ?_
  -- Rewriting the map leaves IsIso's implicit endpoints in the comparison functor's image.
  -- Transport the predicate as a whole to avoid an ill-typed intermediate rewrite target.
  have h := congrArg (fun g ↦ IsIso g) (toDerivedCategory_map_homOf R C f hf)
  exact (Iff.of_eq h).trans ((DerivedCategory.isIso_Qh_map_iff _).trans
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).trans
      (HomologicalComplex.mem_quasiIso_iff f)))

omit [HasDerivedCategory C] in
/-- Equivalences between K-injective models are detected by their maps on every integer
cohomology object; there is no boundedness restriction. -/
theorem isEquivalence_edgeMk_iff_isIso_homologyMap {K L : CochainComplex C ℤ}
    [K.IsKInjective] [L.IsKInjective] (f : K ⟶ L)
    (hf : CochainComplex.HomComplex.Cochain.ofHom f ∈
      dgCycles R (⟨K, ‹_›⟩ : KInjectiveDGCategory C) ⟨L, ‹_›⟩ := ofHom_mem_dgCycles R C f) :
    (dgNerve.edgeMk R (KInjectiveDGCategory C) ⟨_, hf⟩).IsEquivalence ↔
      ∀ n : ℤ, IsIso (HomologicalComplex.homologyMap f n) := by
  rw [isEquivalence_edgeMk_iff_quasiIso R C f hf, quasiIso_iff]
  exact forall_congr' fun n ↦ quasiIsoAt_iff_isIso_homologyMap f n

/-! ### Mapping spaces -/

variable {C}

/-- **Higher homotopy groups of mapping spaces in the K-injective enhancement.** For K-injective
complexes `K` and `L`, the `(n + 1)`-st homotopy group, based at zero, of the right mapping space
from `K` to `L` in the differential graded nerve is the group of morphisms
`K ⟶ L⟦-(n + 1)⟧` in the derived category. These groups are invisible in the derived category's
morphisms `K ⟶ L` themselves. -/
def rightMappingSpacePiAddEquiv (K L : KInjectiveDGCategory C) (n : ℕ) :
    Additive (SSet.KanComplex.π (n + 1)
      ((dgNerve R (KInjectiveDGCategory C)).rightMappingSpace
        ((dgNerveEquiv R (KInjectiveDGCategory C)).symm K)
        ((dgNerveEquiv R (KInjectiveDGCategory C)).symm L))
      (dgNerve.rightMappingSpaceZero (R := R) K L)) ≃+
      (Q.obj K.obj ⟶ (Q.obj L.obj)⟦-((n + 1 : ℕ) : ℤ)⟧) :=
  have := L.property
  -- The Hom complex `dgHomComplex R K L` of the full DG subcategory is the ambient one
  -- (`DGFullSubcategory.dgHomComplex_eq`), which is `linearHomComplex R K.obj L.obj` by the
  -- definition of the enrichment of cochain complexes; both identifications hold by `rfl`.
  (dgNerve.rightMappingSpacePiAddEquivHomology K L n).trans
    (linearHomComplexHomologyLinearEquivOfIsKInjective R K.obj L.obj _).toAddEquiv

/-- `rightMappingSpacePiAddEquiv` is the Dold–Kan comparison
`dgNerve.rightMappingSpacePiAddEquivHomology` followed by the K-injective cohomology comparison
`linearHomComplexHomologyLinearEquivOfIsKInjective`. Together with
`linearHomComplexHomologyLinearEquivOfIsKInjective_symm_mk`, this computes it on any element whose
cohomology class is represented by a cocycle. -/
theorem rightMappingSpacePiAddEquiv_apply (K L : KInjectiveDGCategory C) (n : ℕ)
    (a : Additive (SSet.KanComplex.π (n + 1)
      ((dgNerve R (KInjectiveDGCategory C)).rightMappingSpace
        ((dgNerveEquiv R (KInjectiveDGCategory C)).symm K)
        ((dgNerveEquiv R (KInjectiveDGCategory C)).symm L))
      (dgNerve.rightMappingSpaceZero (R := R) K L))) :
    have := L.property
    rightMappingSpacePiAddEquiv R K L n a =
      linearHomComplexHomologyLinearEquivOfIsKInjective R K.obj L.obj _
        (dgNerve.rightMappingSpacePiAddEquivHomology K L n a) :=
  (rfl)

/-- **Path components of mapping spaces in the K-injective enhancement.** For K-injective
complexes `K` and `L`, the path components of the right mapping space from `K` to `L` in the
differential graded nerve are the morphisms `K ⟶ L` in the derived category. -/
def rightMappingSpacePiZeroEquiv (K L : KInjectiveDGCategory C) :
    SSet.KanComplex.π 0
      ((dgNerve R (KInjectiveDGCategory C)).rightMappingSpace
        ((dgNerveEquiv R (KInjectiveDGCategory C)).symm K)
        ((dgNerveEquiv R (KInjectiveDGCategory C)).symm L))
      (dgNerve.rightMappingSpaceZero (R := R) K L) ≃
      (Q.obj K.obj ⟶ Q.obj L.obj) :=
  have := L.property
  -- As for `rightMappingSpacePiAddEquiv`, `dgHomComplex R K L` is `linearHomComplex R K.obj L.obj`
  -- by `rfl`.
  (dgNerve.rightMappingSpacePiZeroEquivHomology K L).trans
    ((linearHomComplexHomologyLinearEquivOfIsKInjective R K.obj L.obj 0).toEquiv.trans
      ((Iso.refl _).homCongr ((shiftFunctorZero (DerivedCategory C) ℤ).app _)))

/-- `rightMappingSpacePiZeroEquiv` is the Dold–Kan comparison
`dgNerve.rightMappingSpacePiZeroEquivHomology` followed by the K-injective cohomology comparison
`linearHomComplexHomologyLinearEquivOfIsKInjective` in degree zero and the identification
`L⟦0⟧ ≅ L`. Together with `linearHomComplexHomologyLinearEquivOfIsKInjective_symm_mk`, this
computes it on any element whose cohomology class is represented by a cocycle. -/
theorem rightMappingSpacePiZeroEquiv_apply (K L : KInjectiveDGCategory C)
    (a : SSet.KanComplex.π 0
      ((dgNerve R (KInjectiveDGCategory C)).rightMappingSpace
        ((dgNerveEquiv R (KInjectiveDGCategory C)).symm K)
        ((dgNerveEquiv R (KInjectiveDGCategory C)).symm L))
      (dgNerve.rightMappingSpaceZero (R := R) K L)) :
    have := L.property
    rightMappingSpacePiZeroEquiv R K L a =
      linearHomComplexHomologyLinearEquivOfIsKInjective R K.obj L.obj 0
          (dgNerve.rightMappingSpacePiZeroEquivHomology K L a) ≫
        (shiftFunctorZero (DerivedCategory C) ℤ).hom.app _ := by
  simp [rightMappingSpacePiZeroEquiv, Iso.homCongr_apply]

end KInjectiveDGCategory

end TauCeti
