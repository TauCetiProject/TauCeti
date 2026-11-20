/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.Functor.Basic
public import TauCeti.CategoryTheory.DG.Karoubi.Basic
public import TauCeti.CategoryTheory.DG.QuasiEquivalence
public import TauCeti.CategoryTheory.Linear.Karoubi
public import TauCeti.CategoryTheory.ObjectProperty.Retract

/-!
# The homotopy category of the DG Karoubi envelope

This file compares the homotopy category `H⁰(Kar C)` of the DG Karoubi envelope of a DG category
`C` with the idempotent completion `Karoubi (H⁰ C)` of the homotopy category of `C`.

An object `(X, p)` of the DG Karoubi envelope carries a closed idempotent `p` of degree zero, so
its class `[p]` is an idempotent of `X` in `H⁰(C)`, and `(X, [p])` is an object of the idempotent
completion of `H⁰(C)`.  The Hom complex from `(X, p)` to `(Y, q)` in the envelope is the
subcomplex `p Hom(X, Y) q` of `Hom(X, Y)`, and compression `f ↦ p f q` is a retraction of
complexes onto it, because `p` and `q` are closed of degree zero.  Taking degree-zero cohomology,
the classes of degree-zero cocycles of `p Hom(X, Y) q` are exactly the classes `c` of `H⁰(C)`
with `[p] c [q] = c`, with the same homotopy relation.  Hence `(X, p) ↦ (X, [p])` is a **fully
faithful** functor `H⁰(Kar C) ⥤ Karoubi (H⁰ C)`, and its restriction along the embedding
`C ⥤ Kar C` is the embedding `H⁰ C ⥤ Karoubi (H⁰ C)`.

It is not essentially surjective in general: an idempotent of `H⁰(C)` is a closed degree-zero
morphism which is idempotent only up to homotopy, and it need not be homotopic to a strictly
idempotent one.  Since every object of `Karoubi (H⁰ C)` is a retract of an object of `H⁰(C)`, the
functor is an equivalence exactly when idempotents split in `H⁰(Kar C)`.  When idempotents already
split in `H⁰(C)`, all three categories agree: `H⁰(C) ⥤ H⁰(Kar C)` and `H⁰(Kar C) ⥤ Karoubi (H⁰ C)`
are equivalences, so the embedding of `C` into its DG Karoubi envelope is a quasi-equivalence.

## Main definitions

* `TauCeti.DGKaroubi.dgHomotopyCategoryToKaroubi`: the functor `H⁰(Kar C) ⥤ Karoubi (H⁰ C)`
  sending `(X, p)` to `(X, [p])` and the class of a closed morphism to the class of its underlying
  morphism.
* `TauCeti.DGKaroubi.fullyFaithfulDGHomotopyCategoryToKaroubi`: it is fully faithful.
* `TauCeti.DGKaroubi.mapDGHomotopyCategoryToDGKaroubiCompIso`: its restriction along
  `H⁰(C) ⥤ H⁰(Kar C)` is the embedding `toKaroubi (H⁰ C)`.

## Main results

* `TauCeti.DGKaroubi.isEquivalence_dgHomotopyCategoryToKaroubi_iff`: the comparison functor is an
  equivalence if and only if `H⁰(Kar C)` is idempotent complete.
* `TauCeti.DGKaroubi.isIdempotentComplete_dgHomotopyCategory`: if `H⁰(C)` is idempotent complete,
  so is `H⁰(Kar C)`.
* `TauCeti.DGKaroubi.isEquivalence_mapDGHomotopyCategory_toDGKaroubi` and
  `TauCeti.DGKaroubi.isQuasiEquivalence_toDGKaroubi`: if `H⁰(C)` is idempotent complete, the
  embedding `C ⥤ Kar C` induces an equivalence on homotopy categories and is a
  quasi-equivalence.

## References

* P. Balmer and M. Schlichting, *Idempotent completion of triangulated categories*, Journal of
  Algebra 236 (2001), Section 1.
* Joël Riou and the Mathlib contributors, `Mathlib.CategoryTheory.Idempotents.Karoubi`, whose
  idempotent completion is the target of the comparison.
-/

public section

open CategoryTheory Idempotents

namespace TauCeti

namespace DGKaroubi

universe v u

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

noncomputable section

/-! ### Compression onto the Hom complexes of the envelope -/

/-- The underlying morphism of a closed degree-zero morphism of the Karoubi envelope is closed. -/
theorem dgHomVal_mem_dgCycles {P Q : DGKaroubi R C} {f : DGHom R 0 P Q}
    (hf : f ∈ dgCycles R P Q) : dgHomVal 0 f ∈ dgCycles R P.X Q.X := by
  rw [mem_dgCycles] at hf ⊢
  rw [← dgHomVal_dgDifferential, hf, map_zero]

/-- Compressing a morphism `f` of the underlying objects to `p f q` gives a morphism absorbing
both idempotents. -/
private theorem compress_mem_homSubmodule {P Q : DGKaroubi R C} {n : ℤ}
    (f : DGHom R n P.X Q.X) :
    dgComp R (dgComp R P.p f (zero_add n)) Q.p (add_zero n) ∈ homSubmodule P Q n := by
  refine mem_homSubmodule.2 ⟨?_, ?_⟩
  · rw [← dgComp_assoc R P.p (dgComp R P.p f (zero_add n)) Q.p (zero_add n) (add_zero n)
      (by omega), ← dgComp_assoc R P.p P.p f (zero_add 0) (zero_add n) (by omega), P.idem]
  · rw [dgComp_assoc R (dgComp R P.p f (zero_add n)) Q.p Q.p (add_zero n) (add_zero 0)
      (by omega), Q.idem]

/-- The compression `p f q` of a morphism `f : P.X ⟶ Q.X` of the underlying objects, as a
morphism of the Karoubi envelope from `P` to `Q`. -/
private def compress {P Q : DGKaroubi R C} {n : ℤ} (f : DGHom R n P.X Q.X) : DGHom R n P Q :=
  dgHomMk _ (compress_mem_homSubmodule f)

private theorem dgHomVal_compress {P Q : DGKaroubi R C} {n : ℤ} (f : DGHom R n P.X Q.X) :
    dgHomVal n (compress f) = dgComp R (dgComp R P.p f (zero_add n)) Q.p (add_zero n) :=
  dgHomVal_dgHomMk _ _

/-- Compression is left inverse to taking underlying morphisms. -/
private theorem compress_dgHomVal {P Q : DGKaroubi R C} {n : ℤ} (f : DGHom R n P Q) :
    compress (dgHomVal n f) = f :=
  dgHom_ext (by rw [dgHomVal_compress, p_dgComp_dgHomVal, dgHomVal_dgComp_p])

/-- Compression commutes with the differential, since the idempotents are closed of degree
zero. -/
private theorem dgDifferential_compress {P Q : DGKaroubi R C} {n : ℤ} (f : DGHom R n P.X Q.X) :
    dgDifferential R n (compress f) = compress (dgDifferential R n f) :=
  dgHom_ext (by
    simp only [dgHomVal_dgDifferential, dgHomVal_compress, dgDifferential_dgComp,
      dgDifferential_p, zero_dgComp, dgComp_zero, smul_zero, add_zero, zero_add,
      Int.negOnePow_zero, one_smul])

/-! ### The inclusion of Hom complexes -/

/-- The inclusion of the Hom complex from `P` to `Q` in the Karoubi envelope into the Hom complex
of the underlying objects, sending a morphism to its underlying morphism of `C`. -/
def homComplexInclusion (P Q : DGKaroubi R C) :
    dgHomComplex R P Q ⟶ dgHomComplex R P.X Q.X where
  f n := ModuleCat.ofHom (dgHomVal n)
  comm' n m hnm := by
    obtain rfl : n + 1 = m := hnm
    ext f
    exact (dgHomVal_dgDifferential f).symm

@[simp]
theorem homComplexInclusion_f_apply (P Q : DGKaroubi R C) {n : ℤ} (f : DGHom R n P Q) :
    ((homComplexInclusion P Q).f n).hom f = dgHomVal n f :=
  (rfl)

/-- The inclusion of Hom complexes sends the homotopy class of a closed degree-zero morphism of
the envelope to the homotopy class of its underlying morphism. -/
theorem homologyMap_homComplexInclusion_dgHomotopyClass {P Q : DGKaroubi R C}
    {f : DGHom R 0 P Q} (hf : f ∈ dgCycles R P Q) :
    (HomologicalComplex.homologyMap (homComplexInclusion P Q) 0).hom (dgHomotopyClass R f hf) =
      dgHomotopyClass R (dgHomVal 0 f) (dgHomVal_mem_dgCycles hf) :=
  homologyMap_dgHomotopyClass R (homComplexInclusion P Q) hf

/-- The inclusion of Hom complexes is compatible with the composition of homotopy classes. -/
theorem homologyMap_homComplexInclusion_dgHomotopyComp {P Q S : DGKaroubi R C}
    (a : DGHomotopyClass R P Q) (b : DGHomotopyClass R Q S) :
    (HomologicalComplex.homologyMap (homComplexInclusion P S) 0).hom (dgHomotopyComp R P Q S a b) =
      dgHomotopyComp R P.X Q.X S.X
        ((HomologicalComplex.homologyMap (homComplexInclusion P Q) 0).hom a)
        ((HomologicalComplex.homologyMap (homComplexInclusion Q S) 0).hom b) := by
  obtain ⟨f, hf, rfl⟩ := exists_dgHomotopyClass_eq R a
  obtain ⟨g, hg, rfl⟩ := exists_dgHomotopyClass_eq R b
  simp_rw [dgHomotopyComp_dgHomotopyClass, homologyMap_homComplexInclusion_dgHomotopyClass,
    dgHomotopyComp_dgHomotopyClass, dgCompZero_def, dgHomVal_dgComp]

/-! ### The comparison functor -/

variable (R C) in
/-- The **comparison functor** `H⁰(Kar C) ⥤ Karoubi (H⁰ C)` from the homotopy category of the DG
Karoubi envelope of `C` to the idempotent completion of the homotopy category of `C`.  It sends
`(X, p)` to `(X, [p])` and the class of a closed degree-zero morphism to the class of its
underlying morphism of `C`; see `TauCeti.DGKaroubi.dgHomotopyCategoryToKaroubi_map_homOf_f`. -/
-- The body is exposed so that the object `(X, [p])` has underlying object `X` definitionally;
-- otherwise the class `[p]` could not be stated to be its idempotent.
@[expose]
def dgHomotopyCategoryToKaroubi :
    DGHomotopyCategory R (DGKaroubi R C) ⥤ Karoubi (DGHomotopyCategory R C) where
  obj P :=
    { X := DGHomotopyCategory.of R (DGHomotopyCategory.underlying R P).X
      p := DGHomotopyCategory.homOf R (DGHomotopyCategory.underlying R P).p
        ((mem_dgCycles R).2 (DGHomotopyCategory.underlying R P).dgDifferential_p)
      idem := DGHomotopyCategory.homOf_comp_eq_homOf_of_dgComp_eq R _ _ _
        (DGHomotopyCategory.underlying R P).idem }
  map {P Q} f :=
    ⟨(HomologicalComplex.homologyMap (homComplexInclusion _ _) 0).hom f, by
      obtain ⟨f, hf, rfl⟩ := exists_dgHomotopyClass_eq R f
      rw [homologyMap_homComplexInclusion_dgHomotopyClass, ← DGHomotopyCategory.homOf_def]
      simp only [DGHomotopyCategory.homOf_comp, dgCompZero_def, p_dgComp_dgHomVal,
        dgHomVal_dgComp_p]⟩
  map_id P := Karoubi.hom_ext _ _ <| by
    dsimp only
    rw [Karoubi.id_f, DGHomotopyCategory.id_def, homologyMap_homComplexInclusion_dgHomotopyClass,
      ← DGHomotopyCategory.homOf_def]
    simp only [dgHomVal_dgId]
  map_comp f g := Karoubi.hom_ext _ _ (homologyMap_homComplexInclusion_dgHomotopyComp f g)

/-- The comparison functor sends `(X, p)` to an object with underlying object `X`. -/
@[simp]
theorem dgHomotopyCategoryToKaroubi_obj_X (P : DGKaroubi R C) :
    ((dgHomotopyCategoryToKaroubi R C).obj (DGHomotopyCategory.of R P)).X =
      DGHomotopyCategory.of R P.X :=
  (rfl)

/-- The comparison functor sends `(X, p)` to an object with idempotent the class `[p]`. -/
@[simp]
theorem dgHomotopyCategoryToKaroubi_obj_p (P : DGKaroubi R C) :
    ((dgHomotopyCategoryToKaroubi R C).obj (DGHomotopyCategory.of R P)).p =
      DGHomotopyCategory.homOf R P.p ((mem_dgCycles R).2 P.dgDifferential_p) :=
  (rfl)

/-- The comparison functor sends the class of a closed degree-zero morphism `f` of the envelope to
the class of its underlying morphism of `C`. -/
@[simp]
theorem dgHomotopyCategoryToKaroubi_map_homOf_f {P Q : DGKaroubi R C} (f : DGHom R 0 P Q)
    (hf : f ∈ dgCycles R P Q) :
    ((dgHomotopyCategoryToKaroubi R C).map (DGHomotopyCategory.homOf R f hf)).f =
      DGHomotopyCategory.homOf R (dgHomVal 0 f) (dgHomVal_mem_dgCycles hf) := by
  rw [DGHomotopyCategory.homOf_def, DGHomotopyCategory.homOf_def]
  exact homologyMap_homComplexInclusion_dgHomotopyClass hf

instance : (dgHomotopyCategoryToKaroubi R C).Additive where
  map_add {P Q} f g := Karoubi.hom_ext _ _ <|
    map_add (HomologicalComplex.homologyMap (homComplexInclusion (DGHomotopyCategory.underlying R P)
      (DGHomotopyCategory.underlying R Q)) 0).hom f g

instance : (dgHomotopyCategoryToKaroubi R C).Linear R where
  map_smul {P Q} f r := Karoubi.hom_ext _ _ <|
    map_smul (HomologicalComplex.homologyMap (homComplexInclusion
      (DGHomotopyCategory.underlying R P) (DGHomotopyCategory.underlying R Q)) 0).hom r f

/-! ### Full faithfulness -/

/-- A closed degree-zero morphism of the envelope whose underlying morphism is a boundary in `C`
is a boundary in the envelope: compress a degree `-1` primitive. -/
private theorem mem_dgBoundaries_of_dgHomVal_mem {P Q : DGKaroubi R C} {f : DGHom R 0 P Q}
    (hf : dgHomVal 0 f ∈ dgBoundaries R P.X Q.X) : f ∈ dgBoundaries R P Q := by
  obtain ⟨h, hh⟩ := (mem_dgBoundaries R).1 hf
  refine (mem_dgBoundaries R).2 ⟨compress h, ?_⟩
  rw [dgDifferential_compress]
  -- The differential `dgDifferential R (-1)` lands in degree `-1 + 1`, which is `0` only
  -- propositionally, so the primitive is transported along `hh` by a degree cast.
  exact (congrArg compress hh).trans (compress_dgHomVal f)

/-- The compression of a closed morphism is closed. -/
private theorem compress_mem_dgCycles {P Q : DGKaroubi R C} {g : DGHom R 0 P.X Q.X}
    (hg : g ∈ dgCycles R P.X Q.X) : compress g ∈ dgCycles R P Q := by
  rw [mem_dgCycles, dgDifferential_compress, (mem_dgCycles R).1 hg]
  exact dgHom_ext (by rw [dgHomVal_compress, dgComp_zero, zero_dgComp, map_zero])

/-- The class of the compression `p g q` of a closed morphism `g` is `[p] ≫ [g] ≫ [q]`. -/
private theorem homOf_dgHomVal_compress {P Q : DGKaroubi R C} {g : DGHom R 0 P.X Q.X}
    (hg : g ∈ dgCycles R P.X Q.X) :
    DGHomotopyCategory.homOf R (dgHomVal 0 (compress g))
        (dgHomVal_mem_dgCycles (compress_mem_dgCycles hg)) =
      DGHomotopyCategory.homOf R P.p ((mem_dgCycles R).2 P.dgDifferential_p) ≫
        DGHomotopyCategory.homOf R g hg ≫
          DGHomotopyCategory.homOf R Q.p ((mem_dgCycles R).2 Q.dgDifferential_p) := by
  simp only [DGHomotopyCategory.homOf_comp, dgCompZero_def, dgHomVal_compress]
  rw [DGHomotopyCategory.homOf_eq_iff, dgComp_assoc R P.p g Q.p (zero_add 0) (add_zero 0)
    (by omega), sub_self]
  exact zero_mem _

instance : (dgHomotopyCategoryToKaroubi R C).Faithful where
  map_injective {P Q} a b hab := by
    obtain ⟨P, rfl⟩ := DGHomotopyCategory.of_surjective R P
    obtain ⟨Q, rfl⟩ := DGHomotopyCategory.of_surjective R Q
    obtain ⟨f, hf, rfl⟩ := DGHomotopyCategory.exists_homOf_eq R a
    obtain ⟨g, hg, rfl⟩ := DGHomotopyCategory.exists_homOf_eq R b
    have hfg := congrArg Karoubi.Hom.f hab
    rw [dgHomotopyCategoryToKaroubi_map_homOf_f, dgHomotopyCategoryToKaroubi_map_homOf_f] at hfg
    rw [DGHomotopyCategory.homOf_eq_iff]
    refine mem_dgBoundaries_of_dgHomVal_mem ?_
    rw [map_sub]
    exact (DGHomotopyCategory.homOf_eq_iff R _ _).1 hfg

instance : (dgHomotopyCategoryToKaroubi R C).Full where
  map_surjective {P Q} φ := by
    obtain ⟨P, rfl⟩ := DGHomotopyCategory.of_surjective R P
    obtain ⟨Q, rfl⟩ := DGHomotopyCategory.of_surjective R Q
    obtain ⟨g, hg, hφ⟩ : ∃ (g : DGHom R 0 P.X Q.X) (hg : g ∈ dgCycles R P.X Q.X),
        DGHomotopyCategory.homOf R g hg = φ.f :=
      DGHomotopyCategory.exists_homOf_eq R φ.f
    have hcomm := φ.comm
    rw [← hφ] at hcomm
    refine ⟨DGHomotopyCategory.homOf R (compress g) (compress_mem_dgCycles hg),
      Karoubi.hom_ext _ _ ?_⟩
    rw [dgHomotopyCategoryToKaroubi_map_homOf_f, ← hφ]
    exact (homOf_dgHomVal_compress hg).trans hcomm

variable (R C) in
/-- **The comparison functor `H⁰(Kar C) ⥤ Karoubi (H⁰ C)` is fully faithful.**  The classes of
degree-zero cocycles from `(X, p)` to `(Y, q)` in the envelope are the classes `c` of `H⁰(C)` with
`[p] c [q] = c`, with the same homotopy relation, because compression `f ↦ p f q` is a retraction
of complexes onto the Hom complex of the envelope. -/
def fullyFaithfulDGHomotopyCategoryToKaroubi :
    (dgHomotopyCategoryToKaroubi R C).FullyFaithful :=
  .ofFullyFaithful (dgHomotopyCategoryToKaroubi R C)

/-! ### Restriction along the embedding -/

/-- The image of an object `X` of `H⁰(C)` under `H⁰(C) ⥤ H⁰(Kar C) ⥤ Karoubi (H⁰ C)` has the
identity of `X` as its idempotent. -/
private theorem p_obj_mapDGHomotopyCategory_toDGKaroubi (X : DGHomotopyCategory R C) :
    (((toDGKaroubi R C).mapDGHomotopyCategory ⋙ dgHomotopyCategoryToKaroubi R C).obj X).p = 𝟙 X :=
  DGHomotopyCategory.homOf_dgId R (DGHomotopyCategory.underlying R X)

/-- The comparison functor sends the image in `H⁰(Kar C)` of a morphism `f` of `H⁰(C)` to a
morphism with underlying morphism `f`. -/
private theorem map_mapDGHomotopyCategory_toDGKaroubi_f {X Y : DGHomotopyCategory R C}
    (f : X ⟶ Y) :
    ((dgHomotopyCategoryToKaroubi R C).map ((toDGKaroubi R C).mapDGHomotopyCategory.map f)).f =
      f := by
  obtain ⟨X, rfl⟩ := DGHomotopyCategory.of_surjective R X
  obtain ⟨Y, rfl⟩ := DGHomotopyCategory.of_surjective R Y
  obtain ⟨f, hf, rfl⟩ := DGHomotopyCategory.exists_homOf_eq R f
  rw [EnrichedFunctor.mapDGHomotopyCategory_map_homOf]
  -- After `dgHomVal_dgMap_toDGKaroubi`, the two classes differ only in the cycle proof and in the
  -- spelling `((toDGKaroubi R C).obj X).X` of `X`, which is definitional by `toDGKaroubi_obj_X`.
  exact (dgHomotopyCategoryToKaroubi_map_homOf_f (P := (toDGKaroubi R C).obj X)
    (Q := (toDGKaroubi R C).obj Y) _ _).trans (by simp only [dgHomVal_dgMap_toDGKaroubi]; rfl)

variable (R C) in
/-- The comparison functor restricts, along the functor `H⁰(C) ⥤ H⁰(Kar C)` induced by the
embedding `X ↦ (X, 1)`, to the embedding `toKaroubi (H⁰ C)` of `H⁰(C)` into its idempotent
completion.  Its components have the identity of `X` as underlying morphism. -/
def mapDGHomotopyCategoryToDGKaroubiCompIso :
    (toDGKaroubi R C).mapDGHomotopyCategory ⋙ dgHomotopyCategoryToKaroubi R C ≅
      toKaroubi (DGHomotopyCategory R C) :=
  NatIso.ofComponents
    (fun X ↦
      { hom := ⟨𝟙 X, by
          rw [p_obj_mapDGHomotopyCategory_toDGKaroubi, toKaroubi_obj_p]
          exact (Category.id_comp _).trans (Category.id_comp _)⟩
        inv := ⟨𝟙 X, by
          rw [p_obj_mapDGHomotopyCategory_toDGKaroubi, toKaroubi_obj_p]
          exact (Category.id_comp _).trans (Category.id_comp _)⟩
        -- The underlying morphisms compose to `𝟙 X`, the idempotent of either object.
        hom_inv_id := Karoubi.hom_ext _ _
          ((Category.comp_id (𝟙 X)).trans (p_obj_mapDGHomotopyCategory_toDGKaroubi X).symm)
        inv_hom_id := Karoubi.hom_ext _ _ (Category.comp_id (𝟙 X)) })
    fun f ↦ Karoubi.hom_ext _ _ <| by
      rw [Karoubi.comp_f, Karoubi.comp_f, Functor.comp_map, map_mapDGHomotopyCategory_toDGKaroubi_f,
        toKaroubi_map_f]
      exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The components of `TauCeti.DGKaroubi.mapDGHomotopyCategoryToDGKaroubiCompIso` have the identity
as underlying morphism. -/
@[simp]
theorem mapDGHomotopyCategoryToDGKaroubiCompIso_hom_app_f (X : DGHomotopyCategory R C) :
    ((mapDGHomotopyCategoryToDGKaroubiCompIso R C).hom.app X).f = 𝟙 X :=
  (rfl)

/-- The inverse components of `TauCeti.DGKaroubi.mapDGHomotopyCategoryToDGKaroubiCompIso` have the
identity as underlying morphism. -/
@[simp]
theorem mapDGHomotopyCategoryToDGKaroubiCompIso_inv_app_f (X : DGHomotopyCategory R C) :
    ((mapDGHomotopyCategoryToDGKaroubiCompIso R C).inv.app X).f = 𝟙 X :=
  (rfl)

/-- Every object of the idempotent completion of `H⁰(C)` lying in the image of `H⁰(C)` lies in
the essential image of the comparison functor. -/
private theorem toKaroubi_obj_mem_essImage (X : DGHomotopyCategory R C) :
    (dgHomotopyCategoryToKaroubi R C).essImage ((toKaroubi _).obj X) :=
  ⟨(toDGKaroubi R C).mapDGHomotopyCategory.obj X,
    ⟨(mapDGHomotopyCategoryToDGKaroubiCompIso R C).app X⟩⟩

/-! ### Idempotent completeness -/

/-- If idempotents split in `H⁰(Kar C)`, the comparison functor is essentially surjective: every
object of `Karoubi (H⁰ C)` is a retract of an object of `H⁰(C)`, and the essential image of a fully
faithful functor out of an idempotent-complete category is stable under retracts. -/
instance [IsIdempotentComplete (DGHomotopyCategory R (DGKaroubi R C))] :
    (dgHomotopyCategoryToKaroubi R C).EssSurj where
  mem_essImage P := (dgHomotopyCategoryToKaroubi R C).essImage.prop_of_retract (Karoubi.retract P)
    (toKaroubi_obj_mem_essImage P.X)

instance [IsIdempotentComplete (DGHomotopyCategory R (DGKaroubi R C))] :
    (dgHomotopyCategoryToKaroubi R C).IsEquivalence where

/-- **The comparison functor `H⁰(Kar C) ⥤ Karoubi (H⁰ C)` is an equivalence if and only if
idempotents split in `H⁰(Kar C)`.** -/
theorem isEquivalence_dgHomotopyCategoryToKaroubi_iff :
    (dgHomotopyCategoryToKaroubi R C).IsEquivalence ↔
      IsIdempotentComplete (DGHomotopyCategory R (DGKaroubi R C)) :=
  ⟨fun _ ↦ (isIdempotentComplete_iff_of_equivalence
      (dgHomotopyCategoryToKaroubi R C).asEquivalence).2 inferInstance,
    fun _ ↦ inferInstance⟩

/-- If idempotents split in `H⁰(C)`, the comparison functor is essentially surjective: every
object of `Karoubi (H⁰ C)` is then isomorphic to an object of `H⁰(C)`. -/
private theorem essSurj_dgHomotopyCategoryToKaroubi_of_isIdempotentComplete
    [IsIdempotentComplete (DGHomotopyCategory R C)] :
    (dgHomotopyCategoryToKaroubi R C).EssSurj where
  mem_essImage P := (dgHomotopyCategoryToKaroubi R C).essImage.prop_of_iso
    ((toKaroubi _).objObjPreimageIso P) (toKaroubi_obj_mem_essImage _)

/-- **If idempotents split in `H⁰(C)`, they split in `H⁰(Kar C)`.** -/
instance isIdempotentComplete_dgHomotopyCategory [IsIdempotentComplete (DGHomotopyCategory R C)] :
    IsIdempotentComplete (DGHomotopyCategory R (DGKaroubi R C)) :=
  have := essSurj_dgHomotopyCategoryToKaroubi_of_isIdempotentComplete (R := R) (C := C)
  have : (dgHomotopyCategoryToKaroubi R C).IsEquivalence := { }
  isEquivalence_dgHomotopyCategoryToKaroubi_iff.1 this

/-- **If idempotents split in `H⁰(C)`, the embedding `C ⥤ Kar C` induces an equivalence of
homotopy categories.** -/
instance isEquivalence_mapDGHomotopyCategory_toDGKaroubi
    [IsIdempotentComplete (DGHomotopyCategory R C)] :
    (toDGKaroubi R C).mapDGHomotopyCategory.IsEquivalence :=
  have :
      ((toDGKaroubi R C).mapDGHomotopyCategory ⋙ dgHomotopyCategoryToKaroubi R C).IsEquivalence :=
    Functor.isEquivalence_of_iso (mapDGHomotopyCategoryToDGKaroubiCompIso R C).symm
  Functor.isEquivalence_of_comp_right _ (dgHomotopyCategoryToKaroubi R C)

variable (R C) in
/-- **If idempotents split in `H⁰(C)`, the embedding of `C` into its DG Karoubi envelope is a
quasi-equivalence.** -/
theorem isQuasiEquivalence_toDGKaroubi [IsIdempotentComplete (DGHomotopyCategory R C)] :
    (toDGKaroubi R C).IsQuasiEquivalence :=
  (EnrichedFunctor.isQuasiEquivalence_iff_isQuasiFullyFaithful_and_essSurj _).2
    ⟨isQuasiFullyFaithful_toDGKaroubi R C, inferInstance⟩

end

end DGKaroubi

end TauCeti
