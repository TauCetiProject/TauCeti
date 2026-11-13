/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import TauCeti.CategoryTheory.DG.Karoubi.Basic
public import TauCeti.CategoryTheory.Linear.Karoubi

/-!
# The homotopy category of the DG Karoubi envelope

For objects `P = (X, p)` and `Q = (Y, q)` of the DG Karoubi envelope of a DG category `C`, the Hom
complex from `P` to `Q` is a retract of the Hom complex from `X` to `Y`
(`TauCeti.DGKaroubi.homComplexRetract`): the inclusion sends a morphism to its underlying morphism,
and the retraction is `f ↦ p ≫ f ≫ q`.  Passing to degree-zero cohomology, the morphisms from `P`
to `Q` in `H⁰` of the envelope are identified with the morphisms `φ : X ⟶ Y` of `H⁰(C)` with
`[p] ≫ φ ≫ [q] = φ`, which are exactly the morphisms from `(X, [p])` to `(Y, [q])` in the
idempotent completion `Karoubi H⁰(C)`.

This gives a fully faithful functor `H⁰(Kar C) ⥤ Karoubi H⁰(C)` sending `(X, p)` to `(X, [p])`,
compatible with the embeddings of `H⁰(C)` into both sides.  It is not claimed to be essentially
surjective: an idempotent of `H⁰(C)` need not be the class of a closed idempotent of `C`.

## Main definitions

* `TauCeti.DGKaroubi.homotopyCategoryToKaroubi`: the comparison functor
  `H⁰(Kar C) ⥤ Karoubi H⁰(C)`, `(X, p) ↦ (X, [p])`.
* `TauCeti.DGKaroubi.toDGKaroubiCompHomotopyCategoryToKaroubiIso`: its composite with `H⁰` of the
  embedding `C ⥤ Kar C` is the embedding `H⁰(C) ⥤ Karoubi H⁰(C)`.

## Main results

* `TauCeti.DGKaroubi.homotopyCategoryToKaroubi_map_homOf_f`: the comparison functor sends the
  class of a closed morphism to the class of its underlying morphism.
* `TauCeti.DGKaroubi.homotopyCategoryToKaroubiFullyFaithful`: the comparison functor is fully
  faithful.

## References

* P. Balmer and M. Schlichting, *Idempotent completion of triangulated categories*, Journal of
  Algebra 236 (2001), Section 1.
* B. Keller, *On differential graded categories*, ICM 2006, Section 4.5.
-/

public section

open CategoryTheory Idempotents

namespace TauCeti

namespace DGKaroubi

universe v u

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

noncomputable section

/-! ### Cohomology classes -/

/-- The idempotent of an object of the Karoubi envelope is closed of degree zero. -/
theorem p_mem_dgCycles (P : DGKaroubi R C) : P.p ∈ dgCycles R P.X P.X :=
  (mem_dgCycles R).2 P.dgDifferential_p

/-- The underlying morphism of a closed morphism of degree zero of the Karoubi envelope is
closed. -/
theorem dgHomVal_mem_dgCycles {P Q : DGKaroubi R C} {f : DGHom R 0 P Q}
    (hf : f ∈ dgCycles R P Q) : dgHomVal 0 f ∈ dgCycles R P.X Q.X :=
  homComplexRetract_i_f_apply P Q f ▸ map_mem_dgCycles R (homComplexRetract P Q).i hf

/-- The projection `f ↦ p ≫ f ≫ q` of a closed morphism of degree zero is closed. -/
theorem homProj_mem_dgCycles {P Q : DGKaroubi R C} {f : DGHom R 0 P.X Q.X}
    (hf : f ∈ dgCycles R P.X Q.X) : homProj P Q 0 f ∈ dgCycles R P Q :=
  homComplexRetract_r_f_apply P Q f ▸ map_mem_dgCycles R (homComplexRetract P Q).r hf

/-- On degree-zero cohomology, the idempotent `ι ∘ π` of the Hom complex of the underlying objects
acts by `x ↦ [p] ≫ x ≫ [q]`. -/
theorem homologyMap_i_homologyMap_r (P Q : DGKaroubi R C)
    (x : DGHomotopyCategory.of R P.X ⟶ DGHomotopyCategory.of R Q.X) :
    (HomologicalComplex.homologyMap (homComplexRetract P Q).i 0).hom
        ((HomologicalComplex.homologyMap (homComplexRetract P Q).r 0).hom x) =
      DGHomotopyCategory.homOf R P.p (p_mem_dgCycles P) ≫ x ≫
        DGHomotopyCategory.homOf R Q.p (p_mem_dgCycles Q) := by
  obtain ⟨g, hg, rfl⟩ := DGHomotopyCategory.exists_homOf_eq R x
  simp only [DGHomotopyCategory.homOf_def, homologyMap_dgHomotopyClass]
  simp only [← DGHomotopyCategory.homOf_def, DGHomotopyCategory.homOf_comp, dgCompZero_def,
    homComplexRetract_i_f_apply, homComplexRetract_r_f_apply, dgHomVal_homProj]
  -- Both sides are now the class of `p ≫ g ≫ q`; they differ only in the proofs of the degree
  -- equations `0 + 0 = 0`.
  rfl

/-! ### The comparison functor -/

/-- Taking underlying morphisms is compatible with the composition of homotopy classes. -/
private theorem homologyMap_i_dgHomotopyComp {P Q S : DGKaroubi R C}
    (φ : DGHomotopyClass R P Q) (ψ : DGHomotopyClass R Q S) :
    (HomologicalComplex.homologyMap (homComplexRetract P S).i 0).hom
        (dgHomotopyComp R P Q S φ ψ) =
      dgHomotopyComp R P.X Q.X S.X
        ((HomologicalComplex.homologyMap (homComplexRetract P Q).i 0).hom φ)
        ((HomologicalComplex.homologyMap (homComplexRetract Q S).i 0).hom ψ) := by
  obtain ⟨f, hf, rfl⟩ := exists_dgHomotopyClass_eq R φ
  obtain ⟨g, hg, rfl⟩ := exists_dgHomotopyClass_eq R ψ
  simp_rw [dgHomotopyComp_dgHomotopyClass, homologyMap_dgHomotopyClass,
    dgHomotopyComp_dgHomotopyClass, dgCompZero_def, homComplexRetract_i_f_apply, dgHomVal_dgComp]

variable (R C) in
/-- The **comparison functor** from `H⁰` of the DG Karoubi envelope of `C` to the idempotent
completion of `H⁰(C)`.  It sends `(X, p)` to `(X, [p])`, and the class of a closed morphism to the
class of its underlying morphism. -/
-- The body is exposed so that the image of `P` has `of R P.X` as its underlying object, which
-- makes the morphisms of `H⁰(C)` out of `P.X` usable as morphisms out of that object.
@[expose]
def homotopyCategoryToKaroubi :
    DGHomotopyCategory R (DGKaroubi R C) ⥤ Karoubi (DGHomotopyCategory R C) where
  obj P :=
    { X := DGHomotopyCategory.of R (DGHomotopyCategory.underlying R P).X
      p := DGHomotopyCategory.homOf R _ (p_mem_dgCycles (DGHomotopyCategory.underlying R P))
      idem := DGHomotopyCategory.homOf_comp_eq_homOf_of_dgComp_eq R _ _ _
        (DGHomotopyCategory.underlying R P).idem }
  map {P Q} φ :=
    { f := (HomologicalComplex.homologyMap (homComplexRetract _ _).i 0).hom φ
      comm := by
        obtain ⟨f, hf, rfl⟩ := exists_dgHomotopyClass_eq R φ
        rw [homologyMap_dgHomotopyClass, ← DGHomotopyCategory.homOf_def,
          DGHomotopyCategory.homOf_comp, DGHomotopyCategory.homOf_comp]
        simp only [dgCompZero_def, homComplexRetract_i_f_apply, dgHomVal_dgComp_p,
          p_dgComp_dgHomVal] }
  map_id P := by
    ext
    simp only [DGHomotopyCategory.id_def, homologyMap_dgHomotopyClass,
      homComplexRetract_i_f_apply, dgHomVal_dgId, Karoubi.id_f, DGHomotopyCategory.homOf_def]
    -- Both sides are the class of `p`, read in `H⁰(C)` between `of R P.X` and the object
    -- `(obj P).X`, which is `of R P.X` by definition.
    rfl
  map_comp {P Q S} φ ψ := by
    ext
    rw [Karoubi.comp_f]
    exact homologyMap_i_dgHomotopyComp φ ψ

/-- The comparison functor sends `(X, p)` to the summand of `X` cut out by `[p]`. -/
@[simp]
theorem homotopyCategoryToKaroubi_obj_X (P : DGHomotopyCategory R (DGKaroubi R C)) :
    ((homotopyCategoryToKaroubi R C).obj P).X =
      DGHomotopyCategory.of R (DGHomotopyCategory.underlying R P).X :=
  (rfl)

/-- The idempotent of the image of `(X, p)` under the comparison functor is `[p]`. -/
@[simp]
theorem homotopyCategoryToKaroubi_obj_p (P : DGHomotopyCategory R (DGKaroubi R C)) :
    ((homotopyCategoryToKaroubi R C).obj P).p =
      DGHomotopyCategory.homOf R _ (p_mem_dgCycles (DGHomotopyCategory.underlying R P)) :=
  (rfl)

/-- The idempotent of the image of `of R (X, p)` under the comparison functor is `[p]`. -/
@[simp high]
theorem homotopyCategoryToKaroubi_obj_of_p (P : DGKaroubi R C) :
    ((homotopyCategoryToKaroubi R C).obj (DGHomotopyCategory.of R P)).p =
      DGHomotopyCategory.homOf R P.p (p_mem_dgCycles P) :=
  (rfl)

/-- The comparison functor acts on morphisms by the map induced on degree-zero cohomology by the
inclusion of Hom complexes. -/
theorem homotopyCategoryToKaroubi_map_f {P Q : DGHomotopyCategory R (DGKaroubi R C)}
    (φ : P ⟶ Q) :
    ((homotopyCategoryToKaroubi R C).map φ).f =
      (HomologicalComplex.homologyMap (homComplexRetract _ _).i 0).hom φ :=
  (rfl)

/-- The comparison functor sends the class of a closed morphism of degree zero to the class of
its underlying morphism. -/
@[simp]
theorem homotopyCategoryToKaroubi_map_homOf_f {P Q : DGKaroubi R C} (f : DGHom R 0 P Q)
    (hf : f ∈ dgCycles R P Q) :
    ((homotopyCategoryToKaroubi R C).map (DGHomotopyCategory.homOf R f hf)).f =
      DGHomotopyCategory.homOf R (dgHomVal 0 f) (dgHomVal_mem_dgCycles hf) := by
  rw [homotopyCategoryToKaroubi_map_f, DGHomotopyCategory.homOf_def,
    DGHomotopyCategory.homOf_def]
  exact (homologyMap_dgHomotopyClass R (homComplexRetract P Q).i hf).trans
    (by simp only [homComplexRetract_i_f_apply])

variable (R C) in
/-- **`H⁰` of the DG Karoubi envelope is a full subcategory of the idempotent completion of
`H⁰(C)`.**  The preimage of a morphism `φ : (X, [p]) ⟶ (Y, [q])` is the class of `p ≫ f ≫ q` for
any closed representative `f` of `φ`. -/
def homotopyCategoryToKaroubiFullyFaithful : (homotopyCategoryToKaroubi R C).FullyFaithful where
  preimage {P Q} φ := (HomologicalComplex.homologyMap (homComplexRetract _ _).r 0).hom φ.f
  map_preimage {P Q} φ := by
    ext
    exact (homologyMap_i_homologyMap_r _ _ φ.f).trans φ.comm
  preimage_map {P Q} φ := by
    rw [homotopyCategoryToKaroubi_map_f, ← ModuleCat.comp_apply,
      ← HomologicalComplex.homologyMap_comp, (homComplexRetract _ _).retract,
      HomologicalComplex.homologyMap_id, ModuleCat.id_apply]

/-- The preimage under the comparison functor is the map induced on degree-zero cohomology by the
retraction of Hom complexes. -/
theorem homotopyCategoryToKaroubiFullyFaithful_preimage
    {P Q : DGHomotopyCategory R (DGKaroubi R C)}
    (φ : (homotopyCategoryToKaroubi R C).obj P ⟶ (homotopyCategoryToKaroubi R C).obj Q) :
    (homotopyCategoryToKaroubiFullyFaithful R C).preimage φ =
      (HomologicalComplex.homologyMap (homComplexRetract _ _).r 0).hom φ.f :=
  (rfl)

/-- The preimage under the comparison functor of the class of a closed morphism `f` is the class
of `p ≫ f ≫ q`. -/
@[simp]
theorem homotopyCategoryToKaroubiFullyFaithful_preimage_mk_homOf {P Q : DGKaroubi R C}
    (f : DGHom R 0 P.X Q.X) (hf : f ∈ dgCycles R P.X Q.X)
    (comm : DGHomotopyCategory.homOf R P.p (p_mem_dgCycles P) ≫ DGHomotopyCategory.homOf R f hf ≫
      DGHomotopyCategory.homOf R Q.p (p_mem_dgCycles Q) = DGHomotopyCategory.homOf R f hf) :
    (homotopyCategoryToKaroubiFullyFaithful R C).preimage (X := DGHomotopyCategory.of R P)
        (Y := DGHomotopyCategory.of R Q) ⟨DGHomotopyCategory.homOf R f hf, comm⟩ =
      DGHomotopyCategory.homOf R (homProj P Q 0 f) (homProj_mem_dgCycles hf) := by
  rw [homotopyCategoryToKaroubiFullyFaithful_preimage]
  refine (congrArg (HomologicalComplex.homologyMap (homComplexRetract P Q).r 0).hom
    (DGHomotopyCategory.homOf_def R f hf)).trans ((homologyMap_dgHomotopyClass R _ hf).trans ?_)
  simp only [homComplexRetract_r_f_apply, DGHomotopyCategory.homOf_def]

instance : (homotopyCategoryToKaroubi R C).Full :=
  (homotopyCategoryToKaroubiFullyFaithful R C).full

instance : (homotopyCategoryToKaroubi R C).Faithful :=
  (homotopyCategoryToKaroubiFullyFaithful R C).faithful

instance : (homotopyCategoryToKaroubi R C).Additive where
  map_add {P Q} φ ψ := by
    ext
    exact map_add (HomologicalComplex.homologyMap (homComplexRetract _ _).i 0).hom φ ψ

instance : (homotopyCategoryToKaroubi R C).Linear R where
  map_smul {P Q} φ r := by
    ext
    exact map_smul (HomologicalComplex.homologyMap (homComplexRetract _ _).i 0).hom r φ

/-- The image of `(X, 1)` under the comparison functor is `X` with the identity idempotent. -/
@[simp↓]
theorem toDGKaroubi_comp_homotopyCategoryToKaroubi_obj_p (X : DGHomotopyCategory R C) :
    ((homotopyCategoryToKaroubi R C).obj ((toDGKaroubi R C).mapDGHomotopyCategory.obj X)).p =
      𝟙 X :=
  DGHomotopyCategory.homOf_dgId R _

/-- On morphisms between objects `(X, 1)`, the comparison functor is the identity. -/
@[simp↓]
theorem toDGKaroubi_comp_homotopyCategoryToKaroubi_map_f {X Y : DGHomotopyCategory R C}
    (φ : X ⟶ Y) :
    ((homotopyCategoryToKaroubi R C).map ((toDGKaroubi R C).mapDGHomotopyCategory.map φ)).f =
      φ := by
  obtain ⟨f, hf, rfl⟩ := exists_dgHomotopyClass_eq R φ
  rw [homotopyCategoryToKaroubi_map_f,
    EnrichedFunctor.mapDGHomotopyCategory_map, homologyMap_dgHomotopyClass]
  refine (homologyMap_dgHomotopyClass R (homComplexRetract _ _).i _).trans ?_
  congr 1
  rw [← EnrichedFunctor.dgMap_apply]
  exact (homComplexRetract_i_f_apply _ _ _).trans (dgHomVal_dgMap_toDGKaroubi f)

variable (R C) in
/-- The comparison functor extends the embedding of `H⁰(C)` into its idempotent completion:
precomposed with `H⁰` of the embedding `X ↦ (X, 1)` of `C` into its DG Karoubi envelope, it is
`toKaroubi`. -/
def toDGKaroubiCompHomotopyCategoryToKaroubiIso :
    (toDGKaroubi R C).mapDGHomotopyCategory ⋙ homotopyCategoryToKaroubi R C ≅
      toKaroubi (DGHomotopyCategory R C) :=
  NatIso.ofComponents (fun X ↦
    { hom := ⟨𝟙 X, (Category.assoc _ _ _).symm.trans <| (Category.comp_id _).trans <|
        (Category.comp_id _).trans (toDGKaroubi_comp_homotopyCategoryToKaroubi_obj_p X)⟩
      inv := ⟨𝟙 X, (Category.id_comp _).trans
        ((Category.id_comp _).trans (toDGKaroubi_comp_homotopyCategoryToKaroubi_obj_p X))⟩
      hom_inv_id := by
        ext
        exact (Category.id_comp _).trans
          (toDGKaroubi_comp_homotopyCategoryToKaroubi_obj_p X).symm
      inv_hom_id := by
        ext
        exact Category.id_comp _ }) fun {X Y} φ ↦ by
    ext
    exact (Category.comp_id _).trans ((toDGKaroubi_comp_homotopyCategoryToKaroubi_map_f φ).trans
      (Category.id_comp _).symm)

/-- The components of `toDGKaroubiCompHomotopyCategoryToKaroubiIso` are identities. -/
@[simp]
theorem toDGKaroubiCompHomotopyCategoryToKaroubiIso_hom_app_f (X : DGHomotopyCategory R C) :
    ((toDGKaroubiCompHomotopyCategoryToKaroubiIso R C).hom.app X).f = 𝟙 X :=
  (rfl)

/-- The components of the inverse of `toDGKaroubiCompHomotopyCategoryToKaroubiIso` are
identities. -/
@[simp]
theorem toDGKaroubiCompHomotopyCategoryToKaroubiIso_inv_app_f (X : DGHomotopyCategory R C) :
    ((toDGKaroubiCompHomotopyCategoryToKaroubiIso R C).inv.app X).f = 𝟙 X :=
  (rfl)

end

end DGKaroubi

end TauCeti
