/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.Karoubi.Basic
public import TauCeti.CategoryTheory.Linear.Karoubi
public import TauCeti.CategoryTheory.ObjectProperty.Retract

/-!
# The homotopy category of the DG Karoubi envelope

The DG Karoubi envelope `Kar(C)` of a DG category `C` splits the closed idempotents of degree
zero at the level of Hom complexes (`TauCeti/CategoryTheory/DG/Karoubi/Basic.lean`).  This file
compares its homotopy category `H⁰(Kar(C))` with the idempotent completion `Karoubi (H⁰(C))` of the
homotopy category of `C`, Mathlib's `CategoryTheory.Idempotents.Karoubi`.

The comparison functor sends `(X, p)` to `(X, [p])` and the class of a closed morphism to the
class of its underlying morphism in `C`.  It is fully faithful.  The Hom complex of `Kar(C)` from
`(X, p)` to `(Y, q)` is a direct summand of `Hom(X, Y)`: the morphism `f ↦ p ≫ f ≫ q` cuts it out
and commutes with the differential because `p` and `q` are closed of degree zero.  So a closed
morphism of `Kar(C)` which is a boundary in `C` is already a boundary in `Kar(C)`, and every class
`φ` of `Karoubi (H⁰(C))`, which satisfies `φ = [p] ≫ φ ≫ [q]`, is the class of the cut-out of any
representative.  Following the embedding `C ⟶ Kar(C)` by the comparison gives Mathlib's
`toKaroubi`.

Essential surjectivity is a separate question: it asks whether every idempotent of `H⁰(C)` is,
up to isomorphism in `Karoubi (H⁰(C))`, the class of a closed idempotent of degree zero of
`C`.  The comparison is an equivalence exactly when `H⁰(Kar(C))` is idempotent complete, since
every object of `Karoubi (H⁰(C))` is a retract of an object of `H⁰(C)`.  When `H⁰(C)` is
itself idempotent complete, every object of `Kar(C)` is isomorphic in `H⁰` to an object of `C`,
so the embedding `C ⟶ Kar(C)` is a quasi-equivalence.

## Main definitions

* `TauCeti.DGKaroubi.cutHom`: the morphism `p ≫ f ≫ q` of `Kar(C)` cut out of a morphism
  `f : X ⟶ Y` of `C`.
* `TauCeti.DGKaroubi.homComplexInclusion`: the inclusion of the Hom complex of `Kar(C)` into the
  Hom complex of the underlying objects, and `TauCeti.DGKaroubi.homotopyClassMap` the map it
  induces on morphisms of homotopy categories.
* `TauCeti.DGKaroubi.toKaroubiDGHomotopyCategory`: the comparison functor
  `H⁰(Kar(C)) ⥤ Karoubi (H⁰(C))`.
* `TauCeti.DGKaroubi.fullyFaithfulToKaroubiDGHomotopyCategory`: it is fully faithful.
* `TauCeti.DGKaroubi.toDGKaroubiCompToKaroubiDGHomotopyCategoryIso`: following `H⁰` of the
  embedding `C ⟶ Kar(C)` by the comparison is `toKaroubi (H⁰(C))`.

## Main results

* `TauCeti.DGKaroubi.dgHomVal_mem_dgBoundaries_iff`: a closed morphism of `Kar(C)` is a boundary
  exactly when its underlying morphism is a boundary in `C`.
* `TauCeti.DGKaroubi.isEquivalence_toKaroubiDGHomotopyCategory_iff`: the comparison is an
  equivalence exactly when `H⁰(Kar(C))` is idempotent complete.
* `TauCeti.DGKaroubi.isQuasiEquivalence_toDGKaroubi`: if `H⁰(C)` is idempotent complete, the
  embedding `C ⟶ Kar(C)` is a quasi-equivalence.
* `TauCeti.DGKaroubi.isEquivalence_toKaroubiDGHomotopyCategory`: if `H⁰(C)` is idempotent
  complete, the comparison is an equivalence.

## References

* P. Balmer and M. Schlichting, *Idempotent completion of triangulated categories*, Journal of
  Algebra 236 (2001), Section 1.
* Joël Riou and the Mathlib contributors, `Mathlib.CategoryTheory.Idempotents.Karoubi`, the
  idempotent completion compared with here.
-/

public section

open CategoryTheory Idempotents

namespace TauCeti

namespace DGKaroubi

universe v u

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

/-! ### Cutting a morphism of `C` down by the idempotents -/

/-- For a morphism `f : P.X ⟶ Q.X` of `C`, the morphism `p ≫ f ≫ q` absorbs both idempotents. -/
theorem dgComp_dgComp_mem_homSubmodule (P Q : DGKaroubi R C) {n : ℤ} (f : DGHom R n P.X Q.X) :
    dgComp R P.p (dgComp R f Q.p (add_zero n)) (zero_add n) ∈ homSubmodule P Q n :=
  mem_homSubmodule.2
    ⟨by rw [← dgComp_assoc R P.p P.p _ (zero_add 0) (zero_add n) (by omega), P.idem],
    by rw [dgComp_assoc R P.p _ Q.p (zero_add n) (add_zero n) (by omega),
      dgComp_assoc R f Q.p Q.p (add_zero n) (zero_add 0) (by omega), Q.idem]⟩

/-- The morphism of the Karoubi envelope from `P` to `Q` cut out of a morphism
`f : P.X ⟶ Q.X` of `C` by the idempotents: its underlying morphism is `p ≫ f ≫ q`.  It is a
retraction of `TauCeti.DGKaroubi.dgHomVal` (`TauCeti.DGKaroubi.cutHom_dgHomVal`) commuting with
the differentials (`TauCeti.DGKaroubi.dgDifferential_cutHom`). -/
noncomputable def cutHom (P Q : DGKaroubi R C) (n : ℤ) :
    DGHom R n P.X Q.X →ₗ[R] DGHom R n P Q where
  toFun f := dgHomMk _ (dgComp_dgComp_mem_homSubmodule P Q f)
  map_add' f g := dgHom_ext (by simp only [dgHomVal_dgHomMk, add_dgComp, dgComp_add, map_add])
  map_smul' r f := dgHom_ext (by
    simp only [dgHomVal_dgHomMk, smul_dgComp, dgComp_smul, map_smul, RingHom.id_apply])

@[simp]
theorem dgHomVal_cutHom {P Q : DGKaroubi R C} {n : ℤ} (f : DGHom R n P.X Q.X) :
    dgHomVal n (cutHom P Q n f) = dgComp R P.p (dgComp R f Q.p (add_zero n)) (zero_add n) :=
  dgHomVal_dgHomMk _ _

/-- Cutting the underlying morphism of a morphism of the Karoubi envelope gives it back. -/
@[simp]
theorem cutHom_dgHomVal {P Q : DGKaroubi R C} {n : ℤ} (f : DGHom R n P Q) :
    cutHom P Q n (dgHomVal n f) = f :=
  dgHom_ext (by rw [dgHomVal_cutHom, dgHomVal_dgComp_p, p_dgComp_dgHomVal])

/-- Cutting down by the idempotents commutes with the differentials, since the idempotents are
closed of degree zero. -/
theorem dgDifferential_cutHom {P Q : DGKaroubi R C} {n : ℤ} (f : DGHom R n P.X Q.X) :
    dgDifferential R n (cutHom P Q n f) = cutHom P Q (n + 1) (dgDifferential R n f) :=
  dgHom_ext (by
    rw [dgHomVal_dgDifferential, dgHomVal_cutHom, dgHomVal_cutHom,
      dgDifferential_dgComp_of_dgDifferential_eq_zero_left R P.dgDifferential_p,
      dgDifferential_dgComp_of_dgDifferential_eq_zero_right R f Q.dgDifferential_p])

/-- Cutting a closed morphism of degree zero down by the idempotents gives a closed morphism. -/
theorem cutHom_mem_dgCycles {P Q : DGKaroubi R C} {f : DGHom R 0 P.X Q.X}
    (hf : f ∈ dgCycles R P.X Q.X) : cutHom P Q 0 f ∈ dgCycles R P Q := by
  rw [mem_dgCycles] at hf ⊢
  rw [dgDifferential_cutHom, hf, map_zero]

/-- A morphism of degree zero of the Karoubi envelope is closed exactly when its underlying
morphism is closed in `C`. -/
theorem dgHomVal_mem_dgCycles_iff {P Q : DGKaroubi R C} {f : DGHom R 0 P Q} :
    dgHomVal 0 f ∈ dgCycles R P.X Q.X ↔ f ∈ dgCycles R P Q := by
  rw [mem_dgCycles, mem_dgCycles, ← dgHomVal_dgDifferential,
    dgHomVal_injective.eq_iff' (map_zero _)]

/-- The underlying morphism of a closed morphism of degree zero of the Karoubi envelope is
closed. -/
theorem dgHomVal_mem_dgCycles {P Q : DGKaroubi R C} {f : DGHom R 0 P Q}
    (hf : f ∈ dgCycles R P Q) : dgHomVal 0 f ∈ dgCycles R P.X Q.X :=
  dgHomVal_mem_dgCycles_iff.2 hf

/-- **A closed morphism of the Karoubi envelope is a boundary exactly when its underlying morphism
is a boundary in `C`.**  If `dgHomVal f = d h`, then `f = d (cutHom h)`. -/
theorem dgHomVal_mem_dgBoundaries_iff {P Q : DGKaroubi R C} {f : DGHom R 0 P Q} :
    dgHomVal 0 f ∈ dgBoundaries R P.X Q.X ↔ f ∈ dgBoundaries R P Q := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · obtain ⟨h, hh⟩ := (mem_dgBoundaries R).1 hf
    exact (mem_dgBoundaries R).2 ⟨cutHom P Q (-1) h, by rw [dgDifferential_cutHom]; simp [hh]⟩
  · obtain ⟨h, rfl⟩ := (mem_dgBoundaries R).1 hf
    exact (mem_dgBoundaries R).2 ⟨dgHomVal (-1) h, (dgHomVal_dgDifferential h).symm⟩

/-! ### The inclusion of Hom complexes -/

/-- The inclusion of the Hom complex of the Karoubi envelope from `P` to `Q` into the Hom complex
of `C` from `P.X` to `Q.X`, acting by `TauCeti.DGKaroubi.dgHomVal` in every degree. -/
noncomputable def homComplexInclusion (P Q : DGKaroubi R C) :
    dgHomComplex R P Q ⟶ dgHomComplex R P.X Q.X where
  f n := ModuleCat.ofHom (dgHomVal n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    ext f
    exact (dgHomVal_dgDifferential f).symm

@[simp]
theorem homComplexInclusion_f_apply {P Q : DGKaroubi R C} {n : ℤ} (f : DGHom R n P Q) :
    ((homComplexInclusion P Q).f n).hom f = dgHomVal n f :=
  (rfl)

/-- The map on morphisms of the homotopy categories induced by the inclusion of the Hom complex of
the Karoubi envelope into the Hom complex of the underlying objects: the map on degree-zero
cohomology of `TauCeti.DGKaroubi.homComplexInclusion`. -/
noncomputable def homotopyClassMap (P Q : DGKaroubi R C) :
    (DGHomotopyCategory.of R P ⟶ DGHomotopyCategory.of R Q) →ₗ[R]
      (DGHomotopyCategory.of R P.X ⟶ DGHomotopyCategory.of R Q.X) :=
  (HomologicalComplex.homologyMap (homComplexInclusion P Q) 0).hom

/-- The map induced by the inclusion of Hom complexes sends the class of a closed morphism of the
Karoubi envelope to the class of its underlying morphism. -/
@[simp]
theorem homotopyClassMap_homOf {P Q : DGKaroubi R C} {f : DGHom R 0 P Q}
    (hf : f ∈ dgCycles R P Q) :
    homotopyClassMap P Q (DGHomotopyCategory.homOf R f hf) =
      DGHomotopyCategory.homOf R (dgHomVal 0 f) (dgHomVal_mem_dgCycles hf) := by
  rw [DGHomotopyCategory.homOf_def, DGHomotopyCategory.homOf_def]
  exact homologyMap_dgHomotopyClass R _ hf

/-- The image of a morphism under `TauCeti.DGKaroubi.homotopyClassMap` absorbs the classes of
both idempotents. -/
theorem homOf_p_comp_homotopyClassMap_comp_homOf_p (P Q : DGKaroubi R C)
    (c : DGHomotopyCategory.of R P ⟶ DGHomotopyCategory.of R Q) :
    DGHomotopyCategory.homOf R P.p ((mem_dgCycles R).2 P.dgDifferential_p) ≫
        homotopyClassMap P Q c ≫
          DGHomotopyCategory.homOf R Q.p ((mem_dgCycles R).2 Q.dgDifferential_p) =
      homotopyClassMap P Q c := by
  obtain ⟨f, hf, rfl⟩ := DGHomotopyCategory.exists_homOf_eq R c
  simp only [homotopyClassMap_homOf, DGHomotopyCategory.homOf_comp, dgCompZero_def,
    dgHomVal_dgComp_p, p_dgComp_dgHomVal]

variable (R C) in
/-- The **comparison functor** `H⁰(Kar(C)) ⥤ Karoubi (H⁰(C))` from the homotopy category of the
DG Karoubi envelope to the idempotent completion of the homotopy category.  It sends `(X, p)` to
`(X, [p])` and acts on morphisms by `TauCeti.DGKaroubi.homotopyClassMap`, the map induced on
degree-zero cohomology by the inclusion of Hom complexes; by
`TauCeti.DGKaroubi.toKaroubiDGHomotopyCategory_map_homOf_f` it sends the class of a closed
morphism to the class of its underlying morphism. -/
-- The body is exposed so that the underlying object of the image of `(X, p)` is definitionally
-- `X`; otherwise classes of morphisms of `C` out of `X` could not be used as morphisms out of it.
@[expose]
noncomputable def toKaroubiDGHomotopyCategory :
    DGHomotopyCategory R (DGKaroubi R C) ⥤ Karoubi (DGHomotopyCategory R C) where
  obj P :=
    { X := DGHomotopyCategory.of R (DGHomotopyCategory.underlying R P).X
      p := DGHomotopyCategory.homOf R (DGHomotopyCategory.underlying R P).p
        ((mem_dgCycles R).2 (DGHomotopyCategory.underlying R P).dgDifferential_p)
      idem :=
        let hp := (mem_dgCycles R).2 (DGHomotopyCategory.underlying R P).dgDifferential_p
        DGHomotopyCategory.homOf_comp_eq_homOf_of_dgComp_eq R hp hp hp
          (DGHomotopyCategory.underlying R P).idem }
  map {P Q} f :=
    { f := homotopyClassMap (DGHomotopyCategory.underlying R P)
        (DGHomotopyCategory.underlying R Q) f
      comm := homOf_p_comp_homotopyClassMap_comp_homOf_p _ _ f }
  map_id P := by
    obtain ⟨P, rfl⟩ := DGHomotopyCategory.of_surjective R P
    refine Karoubi.hom_ext _ _ ?_
    rw [Karoubi.id_f, ← DGHomotopyCategory.homOf_dgId]
    refine (homotopyClassMap_homOf _).trans ((DGHomotopyCategory.homOf_eq_iff R _ _).2 ?_)
    -- The difference is formed in the Hom module of the underlying object of `of R P`, which is
    -- definitionally `P`.
    have h : dgHomVal 0 (dgId R P) - P.p ∈ dgBoundaries R P.X P.X := by
      rw [dgHomVal_dgId, sub_self]
      exact zero_mem _
    exact h
  map_comp {P Q S} f g := by
    obtain ⟨P, rfl⟩ := DGHomotopyCategory.of_surjective R P
    obtain ⟨Q, rfl⟩ := DGHomotopyCategory.of_surjective R Q
    obtain ⟨S, rfl⟩ := DGHomotopyCategory.of_surjective R S
    obtain ⟨f, hf, rfl⟩ := DGHomotopyCategory.exists_homOf_eq R f
    obtain ⟨g, hg, rfl⟩ := DGHomotopyCategory.exists_homOf_eq R g
    refine Karoubi.hom_ext _ _ ?_
    rw [Karoubi.comp_f, DGHomotopyCategory.homOf_comp]
    have key : DGHomotopyCategory.homOf R (dgHomVal 0 (dgCompZero R f g))
        (dgHomVal_mem_dgCycles (dgCompZero_mem_dgCycles R hf hg)) =
          DGHomotopyCategory.homOf R (dgHomVal 0 f) (dgHomVal_mem_dgCycles hf) ≫
            DGHomotopyCategory.homOf R (dgHomVal 0 g) (dgHomVal_mem_dgCycles hg) := by
      simp only [DGHomotopyCategory.homOf_comp, dgCompZero_def, dgHomVal_dgComp]
    exact (homotopyClassMap_homOf _).trans (key.trans
      (congrArg₂ (· ≫ ·) (homotopyClassMap_homOf hf) (homotopyClassMap_homOf hg)).symm)

@[simp]
theorem toKaroubiDGHomotopyCategory_obj_X (P : DGKaroubi R C) :
    ((toKaroubiDGHomotopyCategory R C).obj (DGHomotopyCategory.of R P)).X =
      DGHomotopyCategory.of R P.X :=
  (rfl)

@[simp]
theorem toKaroubiDGHomotopyCategory_obj_p (P : DGKaroubi R C) :
    ((toKaroubiDGHomotopyCategory R C).obj (DGHomotopyCategory.of R P)).p =
      DGHomotopyCategory.homOf R P.p ((mem_dgCycles R).2 P.dgDifferential_p) :=
  (rfl)

/-- The comparison functor sends the class of a closed morphism of the Karoubi envelope to the
class of its underlying morphism. -/
@[simp]
theorem toKaroubiDGHomotopyCategory_map_homOf_f {P Q : DGKaroubi R C} (f : DGHom R 0 P Q)
    (hf : f ∈ dgCycles R P Q) :
    ((toKaroubiDGHomotopyCategory R C).map (DGHomotopyCategory.homOf R f hf)).f =
      DGHomotopyCategory.homOf R (dgHomVal 0 f) (dgHomVal_mem_dgCycles hf) :=
  homotopyClassMap_homOf hf

instance : (toKaroubiDGHomotopyCategory R C).Additive where
  map_add {P Q} f g := by
    ext
    exact map_add (homotopyClassMap (DGHomotopyCategory.underlying R P)
      (DGHomotopyCategory.underlying R Q)) f g

instance : (toKaroubiDGHomotopyCategory R C).Linear R where
  map_smul {P Q} f r := by
    ext
    exact map_smul (homotopyClassMap (DGHomotopyCategory.underlying R P)
      (DGHomotopyCategory.underlying R Q)) r f

/-! ### Full faithfulness -/

instance : (toKaroubiDGHomotopyCategory R C).Faithful where
  map_injective {P Q} a b h := by
    obtain ⟨P, rfl⟩ := DGHomotopyCategory.of_surjective R P
    obtain ⟨Q, rfl⟩ := DGHomotopyCategory.of_surjective R Q
    obtain ⟨f, hf, rfl⟩ := DGHomotopyCategory.exists_homOf_eq R a
    obtain ⟨g, hg, rfl⟩ := DGHomotopyCategory.exists_homOf_eq R b
    have h' := congrArg Karoubi.Hom.f h
    rw [toKaroubiDGHomotopyCategory_map_homOf_f, toKaroubiDGHomotopyCategory_map_homOf_f] at h'
    have h'' := (DGHomotopyCategory.homOf_eq_iff R _ _).1 h'
    rw [← map_sub, dgHomVal_mem_dgBoundaries_iff] at h''
    exact (DGHomotopyCategory.homOf_eq_iff R hf hg).2 h''

instance : (toKaroubiDGHomotopyCategory R C).Full where
  map_surjective {P Q} φ := by
    obtain ⟨P, rfl⟩ := DGHomotopyCategory.of_surjective R P
    obtain ⟨Q, rfl⟩ := DGHomotopyCategory.of_surjective R Q
    obtain ⟨g, hg, hφ⟩ := DGHomotopyCategory.exists_homOf_eq R (X := P.X) (Y := Q.X) φ.f
    refine ⟨DGHomotopyCategory.homOf R (cutHom P Q 0 g) (cutHom_mem_dgCycles hg),
      Karoubi.hom_ext _ _ ?_⟩
    have key : DGHomotopyCategory.homOf R (dgHomVal 0 (cutHom P Q 0 g))
        (dgHomVal_mem_dgCycles (cutHom_mem_dgCycles hg)) =
          DGHomotopyCategory.homOf R P.p ((mem_dgCycles R).2 P.dgDifferential_p) ≫
            DGHomotopyCategory.homOf R g hg ≫
              DGHomotopyCategory.homOf R Q.p ((mem_dgCycles R).2 Q.dgDifferential_p) := by
      simp only [DGHomotopyCategory.homOf_comp, dgCompZero_def, dgHomVal_cutHom]
    refine (toKaroubiDGHomotopyCategory_map_homOf_f _ _).trans (key.trans ?_)
    rw [hφ]
    exact φ.comm

variable (R C) in
/-- **The comparison functor `H⁰(Kar(C)) ⥤ Karoubi (H⁰(C))` is fully faithful.** -/
noncomputable def fullyFaithfulToKaroubiDGHomotopyCategory :
    (toKaroubiDGHomotopyCategory R C).FullyFaithful :=
  .ofFullyFaithful _

/-! ### Compatibility with the embeddings -/

/-- The image of `(X, 1)` under the comparison functor has the class of the identity of `X` as
its idempotent. -/
theorem toKaroubiDGHomotopyCategory_obj_toDGKaroubi_obj_p (X : C) :
    ((toKaroubiDGHomotopyCategory R C).obj
        (DGHomotopyCategory.of R ((toDGKaroubi R C).obj X))).p =
      𝟙 (DGHomotopyCategory.of R X) :=
  DGHomotopyCategory.homOf_dgId R X

/-- The comparison functor sends the image under `H⁰` of the embedding `C ⟶ Kar(C)` of a
morphism `f` of `H⁰(C)` to a morphism with underlying morphism `f`. -/
@[simp]
theorem toKaroubiDGHomotopyCategory_map_mapDGHomotopyCategory_toDGKaroubi_map_f {X Y : C}
    (f : DGHomotopyCategory.of R X ⟶ DGHomotopyCategory.of R Y) :
    ((toKaroubiDGHomotopyCategory R C).map
        ((toDGKaroubi R C).mapDGHomotopyCategory.map f)).f = f := by
  obtain ⟨f, hf, rfl⟩ := DGHomotopyCategory.exists_homOf_eq R f
  refine (congrArg (fun φ ↦ ((toKaroubiDGHomotopyCategory R C).map φ).f)
    (EnrichedFunctor.mapDGHomotopyCategory_map_homOf _ f hf)).trans
      ((toKaroubiDGHomotopyCategory_map_homOf_f _ _).trans
        ((DGHomotopyCategory.homOf_eq_iff R _ _).2 ?_))
  rw [dgHomVal_dgMap_toDGKaroubi]
  -- The difference `f - f` is formed in the Hom module of `(X, 1)`, definitionally that of `X`.
  have h : f - f ∈ dgBoundaries R X Y := by
    rw [sub_self]
    exact zero_mem _
  exact h

variable (R C) in
/-- The image of `(X, 1)` under the comparison functor is isomorphic to `toKaroubi` of `X`, by the
morphisms with underlying morphism the class of the identity of `X`. -/
noncomputable def toKaroubiDGHomotopyCategoryObjToDGKaroubiObjIso (X : C) :
    (toKaroubiDGHomotopyCategory R C).obj (DGHomotopyCategory.of R ((toDGKaroubi R C).obj X)) ≅
      (toKaroubi (DGHomotopyCategory R C)).obj (DGHomotopyCategory.of R X) where
  hom := Karoubi.decompId_i _
  inv := Karoubi.decompId_p
    ((toKaroubiDGHomotopyCategory R C).obj (DGHomotopyCategory.of R ((toDGKaroubi R C).obj X)))
  hom_inv_id := (Karoubi.decompId _).symm
  inv_hom_id := (Karoubi.decomp_p _).symm.trans
    ((congrArg (toKaroubi _).map
      (toKaroubiDGHomotopyCategory_obj_toDGKaroubi_obj_p (R := R) X)).trans
      ((toKaroubi _).map_id _))

@[simp]
theorem toKaroubiDGHomotopyCategoryObjToDGKaroubiObjIso_hom_f (X : C) :
    (toKaroubiDGHomotopyCategoryObjToDGKaroubiObjIso R C X).hom.f =
      𝟙 (DGHomotopyCategory.of R X) :=
  (Karoubi.decompId_i_f _).trans (toKaroubiDGHomotopyCategory_obj_toDGKaroubi_obj_p (R := R) X)

@[simp]
theorem toKaroubiDGHomotopyCategoryObjToDGKaroubiObjIso_inv_f (X : C) :
    (toKaroubiDGHomotopyCategoryObjToDGKaroubiObjIso R C X).inv.f =
      𝟙 (DGHomotopyCategory.of R X) :=
  (Karoubi.decompId_p_f _).trans (toKaroubiDGHomotopyCategory_obj_toDGKaroubi_obj_p (R := R) X)

variable (R C) in
/-- `H⁰` of the embedding `C ⟶ Kar(C)` followed by the comparison functor is Mathlib's embedding
`toKaroubi` of `H⁰(C)` into its idempotent completion.  Its components have the identity of `X`
as underlying morphism. -/
noncomputable def toDGKaroubiCompToKaroubiDGHomotopyCategoryIso :
    (toDGKaroubi R C).mapDGHomotopyCategory ⋙ toKaroubiDGHomotopyCategory R C ≅
      toKaroubi (DGHomotopyCategory R C) :=
  NatIso.ofComponents
    (fun X ↦
      toKaroubiDGHomotopyCategoryObjToDGKaroubiObjIso R C (DGHomotopyCategory.underlying R X))
    fun {X Y} f ↦ by
      obtain ⟨X, rfl⟩ := DGHomotopyCategory.of_surjective R X
      obtain ⟨Y, rfl⟩ := DGHomotopyCategory.of_surjective R Y
      refine Karoubi.hom_ext _ _ ?_
      -- Both sides reduce to `f`; the identities are on `of R (underlying R (of R X))`, which is
      -- only definitionally `of R X`, so `simp` leaves them for `comp_id` and `id_comp`.
      simp only [Functor.comp_map, Karoubi.comp_f, toKaroubi_map_f,
        toKaroubiDGHomotopyCategory_map_mapDGHomotopyCategory_toDGKaroubi_map_f,
        toKaroubiDGHomotopyCategoryObjToDGKaroubiObjIso_hom_f]
      exact (Category.comp_id f).trans (Category.id_comp f).symm

@[simp]
theorem toDGKaroubiCompToKaroubiDGHomotopyCategoryIso_app (X : C) :
    (toDGKaroubiCompToKaroubiDGHomotopyCategoryIso R C).app (DGHomotopyCategory.of R X) =
      toKaroubiDGHomotopyCategoryObjToDGKaroubiObjIso R C X :=
  (rfl)

/-! ### When the comparison is an equivalence -/

variable (R C) in
/-- **The comparison functor `H⁰(Kar(C)) ⥤ Karoubi (H⁰(C))` is an equivalence exactly when
`H⁰(Kar(C))` is idempotent complete.**  Conversely to the transport of idempotent completeness
from `Karoubi (H⁰(C))`, every object `(X, e)` of `Karoubi (H⁰(C))` is a retract of the image of
`(X, 1)`, and the essential image of a fully faithful functor out of an idempotent-complete
category is stable under retracts. -/
theorem isEquivalence_toKaroubiDGHomotopyCategory_iff :
    (toKaroubiDGHomotopyCategory R C).IsEquivalence ↔
      IsIdempotentComplete (DGHomotopyCategory R (DGKaroubi R C)) := by
  refine ⟨fun _ ↦ (isIdempotentComplete_iff_of_equivalence
    (toKaroubiDGHomotopyCategory R C).asEquivalence).2 inferInstance, fun _ ↦ ?_⟩
  refine { essSurj := ⟨fun Y ↦ ?_⟩ }
  exact (toKaroubiDGHomotopyCategory R C).essImage.prop_of_retract (Karoubi.retract Y)
    ⟨(toDGKaroubi R C).mapDGHomotopyCategory.obj Y.X,
      ⟨(toDGKaroubiCompToKaroubiDGHomotopyCategoryIso R C).app Y.X⟩⟩

variable (R C) in
/-- **If `H⁰(C)` is idempotent complete, the embedding `C ⟶ Kar(C)` into the DG Karoubi envelope
is a quasi-equivalence**: every object `(X, p)` is isomorphic in `H⁰` to an object of `C`, namely
to a splitting in `H⁰(C)` of the idempotent `[p]`. -/
theorem isQuasiEquivalence_toDGKaroubi [IsIdempotentComplete (DGHomotopyCategory R C)] :
    (toDGKaroubi R C).IsQuasiEquivalence := by
  refine (EnrichedFunctor.isQuasiEquivalence_iff_isQuasiFullyFaithful_and_essSurj _).2
    ⟨isQuasiFullyFaithful_toDGKaroubi R C, ⟨fun P ↦ ?_⟩⟩
  obtain ⟨Y, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (toKaroubi (DGHomotopyCategory R C))
    ((toKaroubiDGHomotopyCategory R C).obj P)
  exact ⟨Y,
    ⟨(fullyFaithfulToKaroubiDGHomotopyCategory R C).preimageIso
    ((toDGKaroubiCompToKaroubiDGHomotopyCategoryIso R C).app Y ≪≫ e)⟩⟩

variable (R C) in
/-- If `H⁰(C)` is idempotent complete, the comparison functor `H⁰(Kar(C)) ⥤ Karoubi (H⁰(C))` is an
equivalence. -/
theorem isEquivalence_toKaroubiDGHomotopyCategory
    [IsIdempotentComplete (DGHomotopyCategory R C)] :
    (toKaroubiDGHomotopyCategory R C).IsEquivalence := by
  have := (isQuasiEquivalence_toDGKaroubi R C).isEquivalence_mapDGHomotopyCategory
  exact (isEquivalence_toKaroubiDGHomotopyCategory_iff R C).2
    ((isIdempotentComplete_iff_of_equivalence
      (toDGKaroubi R C).mapDGHomotopyCategory.asEquivalence).1 inferInstance)

end DGKaroubi

end TauCeti
