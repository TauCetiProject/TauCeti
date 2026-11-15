/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.Twisted.OneSided
public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Triangulated functors between homotopy categories of twisted complexes

Let `F : C ⥤ D` be a DG functor.  It induces DG functors between the shift closures
(`CategoryTheory.EnrichedFunctor.mapDGShiftClosure`), their additive closures, and the twisted
objects of those; the composite `F.mapDGTwistedComplex` sends a twisted complex
`(⊕ᵢ Xᵢ[rᵢ], δ)` to `(⊕ᵢ (F Xᵢ)[rᵢ], F δ)`.  This file shows that the induced functor
`H⁰(F)` between the homotopy categories of twisted complexes is a **triangulated functor** for the
triangulated structures of `TauCeti/CategoryTheory/DG/Twisted/Triangulated.lean`, and that it
preserves one-sided twisted complexes, the objects of the pretriangulated envelope.

* **Shifts.** The twisted complexes `F (P⟦n⟧)` and `(F P)⟦n⟧` have the same underlying object, and
  their twists agree because the induced functor commutes with shifting every summand.  The closed
  degree-zero morphism whose matrix is the identity
  (`CategoryTheory.EnrichedFunctor.mapDGTwistedComplexShiftHom`) is therefore an isomorphism,
  natural in `P`; it carries the images of the comparison morphisms of shifts to the comparison
  morphisms of the images.  Its classes make `H⁰(F)` commute with the shift of the homotopy
  categories (`Functor.CommShift`).
* **Extensions and cones.** A DG functor preserves extensions up to a closed isomorphism built
  from the biproduct structure maps (`CategoryTheory.EnrichedFunctor.mapExtensionIso`, in
  `TauCeti/CategoryTheory/DG/Twisted/Extension.lean`), for any DG functor between the underlying
  categories, not only for functors on shift closures.  Applied to
  a cone, which is an extension along `P⟦1⟧ ⟶ P ⟶ Q`, and combined with the shift isomorphism,
  this identifies the image of the cone triangle of `u` with the cone triangle of `F u`
  (`CategoryTheory.EnrichedFunctor.mapConeTriangleIso`).  Since the distinguished triangles are
  the triangles isomorphic to cone triangles, `H⁰(F)` is triangulated.

This functoriality is what is needed to compare the pretriangulated envelopes of two DG categories
along a DG functor between them, for instance along a quasi-equivalence.

## Main definitions

* `CategoryTheory.EnrichedFunctor.mapDGTwistedComplex`: the DG functor induced by a DG functor on
  twisted objects of the additive closure of the shift closure.
* `CategoryTheory.EnrichedFunctor.mapDGTwistedComplexShiftHom`: the closed isomorphism
  `F (P⟦n⟧) ⟶ (F P)⟦n⟧`.
* `CategoryTheory.EnrichedFunctor.mapDGTwistedComplexShiftIso`: the induced natural isomorphism
  of functors on homotopy categories, the data of `Functor.CommShift`.
* `CategoryTheory.EnrichedFunctor.mapConeTriangleIso`: the image of a cone triangle is isomorphic
  to the cone triangle of the image.

## Main results

* `CategoryTheory.EnrichedFunctor.dgComp_dgMap_shiftFunctor_mapDGTwistedComplexShiftHom`: the
  shift isomorphism is natural.
* `CategoryTheory.EnrichedFunctor.dgHomEquiv_dgMap_mapDGTwistedComplex_shiftAddHom`: the induced
  functor preserves the comparison `P⟦a + b⟧ ⟶ P⟦a⟧⟦b⟧` of iterated shifts.
* The instances `Functor.CommShift ℤ` and `Functor.IsTriangulated` for
  `F.mapDGTwistedComplex.mapDGHomotopyCategory`.
* `CategoryTheory.EnrichedFunctor.oneSided_mapDGHomotopyCategory_obj`: `H⁰(F)` sends the
  pretriangulated envelope of `C` into that of `D`.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
-/

public section

open CategoryTheory Pretriangulated

namespace CategoryTheory.EnrichedFunctor

open TauCeti DGTwistedObject DGHomotopyCategory

universe v u u₂

variable {R : Type v} [CommRing R] {C : Type u} {D : Type u₂} [DGCategory R C] [DGCategory R D]
  (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D)

/-! ### Twisted complexes -/

/-- The DG functor induced by `F` on twisted complexes, the twisted objects of the additive closure
of the shift closure: it sends `(⊕ᵢ Xᵢ[rᵢ], δ)` to `(⊕ᵢ (F Xᵢ)[rᵢ], F δ)` and applies `F` to every
matrix entry. -/
-- This is reducible so that the image of a twisted complex is reducibly the image under the
-- composite of the induced functors, whose API then applies.
noncomputable abbrev mapDGTwistedComplex :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ)
      (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))
      (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure D))) :=
  F.mapDGShiftClosure.mapDGAdditiveClosure.mapDGTwistedObject

section shift

variable (P : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))) (n : ℤ)

/-- The DG functor induced by `F` commutes with the shift of twisted complexes: a morphism has the
same matrix under the two composites. -/
theorem dgHomEquiv_dgMap_mapDGTwistedComplex_dgMap_shiftFunctor
    {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} {p : ℤ}
    (f : DGHom R p P Q) :
    DGTwistedObject.dgHomEquiv R _ _ p
        (F.mapDGTwistedComplex.dgMap p ((DGTwistedObject.shiftFunctor R n).dgMap p f)) =
      DGTwistedObject.dgHomEquiv R _ _ p
        ((DGTwistedObject.shiftFunctor R n).dgMap p (F.mapDGTwistedComplex.dgMap p f)) := by
  rw [dgHomEquiv_dgMap_mapDGTwistedObject, dgHomEquiv_dgMap_mapDGTwistedObject,
    dgHomEquiv_dgMap_mapDGTwistedObject, dgHomEquiv_dgMap_mapDGTwistedObject,
    mapDGShiftClosure_mapDGAdditiveClosure_dgMap_shiftFunctor]

/-- The closed isomorphism `F (P⟦n⟧) ⟶ (F P)⟦n⟧` whose matrix is the identity.  The two twisted
complexes have the same underlying object `⊕ᵢ (F Xᵢ)[rᵢ + n]`, and the same twist by
`CategoryTheory.EnrichedFunctor.dgHomEquiv_dgMap_mapDGTwistedComplex_dgMap_shiftFunctor`. -/
-- The identity of the underlying object of `F (P⟦n⟧)` is a matrix between the underlying objects
-- of the two twisted complexes because both are reducibly `⊕ᵢ (F Xᵢ)[rᵢ + n]`, built from the
-- reducible induced functors.
noncomputable def mapDGTwistedComplexShiftHom :
    DGHom R 0 (F.mapDGTwistedComplex.obj ((DGTwistedObject.shiftFunctor R n).obj P))
      ((DGTwistedObject.shiftFunctor R n).obj (F.mapDGTwistedComplex.obj P)) :=
  (DGTwistedObject.dgHomEquiv R _ _ 0).symm (dgId R _)

/-- The inverse `(F P)⟦n⟧ ⟶ F (P⟦n⟧)` of
`CategoryTheory.EnrichedFunctor.mapDGTwistedComplexShiftHom`, whose matrix is the identity. -/
noncomputable def mapDGTwistedComplexShiftInv :
    DGHom R 0 ((DGTwistedObject.shiftFunctor R n).obj (F.mapDGTwistedComplex.obj P))
      (F.mapDGTwistedComplex.obj ((DGTwistedObject.shiftFunctor R n).obj P)) :=
  (DGTwistedObject.dgHomEquiv R _ _ 0).symm (dgId R _)

/-- The matrix of `F (P⟦n⟧) ⟶ (F P)⟦n⟧` is the identity. -/
@[simp]
theorem dgHomEquiv_mapDGTwistedComplexShiftHom :
    DGTwistedObject.dgHomEquiv R _ _ 0 (F.mapDGTwistedComplexShiftHom P n) = dgId R _ :=
  LinearEquiv.apply_symm_apply _ _

/-- The matrix of `(F P)⟦n⟧ ⟶ F (P⟦n⟧)` is the identity. -/
@[simp]
theorem dgHomEquiv_mapDGTwistedComplexShiftInv :
    DGTwistedObject.dgHomEquiv R _ _ 0 (F.mapDGTwistedComplexShiftInv P n) = dgId R _ :=
  LinearEquiv.apply_symm_apply _ _

/-- The isomorphism `F (P⟦n⟧) ⟶ (F P)⟦n⟧` is closed: the twists of the two twisted complexes
agree. -/
@[simp↓]
theorem dgDifferential_mapDGTwistedComplexShiftHom :
    dgDifferential R 0 (F.mapDGTwistedComplexShiftHom P n) = 0 :=
  (DGTwistedObject.dgHomEquiv R _ _ (0 + 1)).injective <| by
    rw [DGTwistedObject.dgHomEquiv_dgDifferential, dgHomEquiv_mapDGTwistedComplexShiftHom,
      dgDifferential_dgId, dgId_dgComp, dgComp_dgId, Int.negOnePow_zero, one_smul, map_zero]
    simp only [zero_add]
    exact sub_eq_zero.mpr
      (F.mapDGShiftClosure_mapDGAdditiveClosure_dgMap_shiftFunctor n P.twist).symm

/-- `F (P⟦n⟧) ⟶ (F P)⟦n⟧ ⟶ F (P⟦n⟧)` is the identity. -/
@[simp↓]
theorem dgComp_mapDGTwistedComplexShiftHom_mapDGTwistedComplexShiftInv :
    dgComp R (F.mapDGTwistedComplexShiftHom P n) (F.mapDGTwistedComplexShiftInv P n)
      (add_zero 0) = dgId R _ :=
  (DGTwistedObject.dgHomEquiv R _ _ 0).injective <| by
    rw [DGTwistedObject.dgHomEquiv_dgComp, dgHomEquiv_mapDGTwistedComplexShiftHom,
      dgHomEquiv_mapDGTwistedComplexShiftInv, dgId_dgComp, DGTwistedObject.dgHomEquiv_dgId]

/-- `(F P)⟦n⟧ ⟶ F (P⟦n⟧) ⟶ (F P)⟦n⟧` is the identity. -/
@[simp↓]
theorem dgComp_mapDGTwistedComplexShiftInv_mapDGTwistedComplexShiftHom :
    dgComp R (F.mapDGTwistedComplexShiftInv P n) (F.mapDGTwistedComplexShiftHom P n)
      (add_zero 0) = dgId R _ :=
  (DGTwistedObject.dgHomEquiv R _ _ 0).injective <| by
    rw [DGTwistedObject.dgHomEquiv_dgComp, dgHomEquiv_mapDGTwistedComplexShiftHom,
      dgHomEquiv_mapDGTwistedComplexShiftInv, dgId_dgComp, DGTwistedObject.dgHomEquiv_dgId]

/-- The isomorphism `(F P)⟦n⟧ ⟶ F (P⟦n⟧)` is closed. -/
@[simp↓]
theorem dgDifferential_mapDGTwistedComplexShiftInv :
    dgDifferential R 0 (F.mapDGTwistedComplexShiftInv P n) = 0 :=
  dgDifferential_eq_zero_of_dgComp_eq_dgId R (F.dgDifferential_mapDGTwistedComplexShiftHom P n)
    (add_zero 0) (F.dgComp_mapDGTwistedComplexShiftHom_mapDGTwistedComplexShiftInv P n)
    (F.dgComp_mapDGTwistedComplexShiftInv_mapDGTwistedComplexShiftHom P n)

variable {P} in
/-- **The isomorphism `F (P⟦n⟧) ⟶ (F P)⟦n⟧` is natural in `P`.** -/
theorem dgComp_dgMap_shiftFunctor_mapDGTwistedComplexShiftHom
    {Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} {p : ℤ} (f : DGHom R p P Q) :
    dgComp R (F.mapDGTwistedComplex.dgMap p ((DGTwistedObject.shiftFunctor R n).dgMap p f))
        (F.mapDGTwistedComplexShiftHom Q n) (add_zero p) =
      dgComp R (F.mapDGTwistedComplexShiftHom P n)
        ((DGTwistedObject.shiftFunctor R n).dgMap p (F.mapDGTwistedComplex.dgMap p f))
        (zero_add p) :=
  (DGTwistedObject.dgHomEquiv R _ _ p).injective <| by
    rw [DGTwistedObject.dgHomEquiv_dgComp, DGTwistedObject.dgHomEquiv_dgComp,
      dgHomEquiv_mapDGTwistedComplexShiftHom, dgHomEquiv_mapDGTwistedComplexShiftHom, dgComp_dgId,
      dgId_dgComp]
    exact F.dgHomEquiv_dgMap_mapDGTwistedComplex_dgMap_shiftFunctor n f

/-- The image of the comparison morphism `P⟦n⟧ ⟶ P` has the matrix of the comparison morphism
`(F P)⟦n⟧ ⟶ F P`. -/
theorem dgHomEquiv_dgMap_mapDGTwistedComplex_fromShift :
    DGTwistedObject.dgHomEquiv R _ _ n (F.mapDGTwistedComplex.dgMap n (fromShift P n)) =
      DGTwistedObject.dgHomEquiv R _ _ n (fromShift (F.mapDGTwistedComplex.obj P) n) := by
  rw [dgHomEquiv_dgMap_mapDGTwistedObject, DGTwistedObject.dgHomEquiv_fromShift,
    DGTwistedObject.dgHomEquiv_fromShift, mapDGShiftClosure_mapDGAdditiveClosure_dgMap_fromShift]

/-- The image of the comparison morphism `P ⟶ P⟦n⟧` has the matrix of the comparison morphism
`F P ⟶ (F P)⟦n⟧`. -/
theorem dgHomEquiv_dgMap_mapDGTwistedComplex_toShift :
    DGTwistedObject.dgHomEquiv R _ _ (-n) (F.mapDGTwistedComplex.dgMap (-n) (toShift P n)) =
      DGTwistedObject.dgHomEquiv R _ _ (-n) (toShift (F.mapDGTwistedComplex.obj P) n) := by
  rw [dgHomEquiv_dgMap_mapDGTwistedObject, DGTwistedObject.dgHomEquiv_toShift,
    DGTwistedObject.dgHomEquiv_toShift, mapDGShiftClosure_mapDGAdditiveClosure_dgMap_toShift]

/-- The image of the comparison morphism `P⟦n⟧ ⟶ P` is the isomorphism `F (P⟦n⟧) ⟶ (F P)⟦n⟧`
followed by the comparison morphism `(F P)⟦n⟧ ⟶ F P`. -/
theorem dgComp_mapDGTwistedComplexShiftHom_fromShift :
    dgComp R (F.mapDGTwistedComplexShiftHom P n) (fromShift (F.mapDGTwistedComplex.obj P) n)
      (zero_add n) = F.mapDGTwistedComplex.dgMap n (fromShift P n) :=
  (DGTwistedObject.dgHomEquiv R _ _ n).injective <| by
    rw [DGTwistedObject.dgHomEquiv_dgComp, dgHomEquiv_mapDGTwistedComplexShiftHom, dgId_dgComp,
      dgHomEquiv_dgMap_mapDGTwistedComplex_fromShift]

/-- The image of the comparison morphism `P ⟶ P⟦n⟧`, followed by the isomorphism
`F (P⟦n⟧) ⟶ (F P)⟦n⟧`, is the comparison morphism `F P ⟶ (F P)⟦n⟧`. -/
theorem dgComp_dgMap_toShift_mapDGTwistedComplexShiftHom :
    dgComp R (F.mapDGTwistedComplex.dgMap (-n) (toShift P n))
      (F.mapDGTwistedComplexShiftHom P n) (add_zero (-n)) =
        toShift (F.mapDGTwistedComplex.obj P) n :=
  (DGTwistedObject.dgHomEquiv R _ _ (-n)).injective <| by
    rw [DGTwistedObject.dgHomEquiv_dgComp, dgHomEquiv_mapDGTwistedComplexShiftHom, dgComp_dgId,
      dgHomEquiv_dgMap_mapDGTwistedComplex_toShift]

private theorem dgHomEquiv_dgMap_shiftFunctor_dgMap_mapDGTwistedComplex_toShift (a b : ℤ) :
    DGTwistedObject.dgHomEquiv R _ _ (-a) ((DGTwistedObject.shiftFunctor R b).dgMap (-a)
        (F.mapDGTwistedComplex.dgMap (-a) (toShift P a))) =
      DGTwistedObject.dgHomEquiv R _ _ (-a) ((DGTwistedObject.shiftFunctor R b).dgMap (-a)
        (toShift (F.mapDGTwistedComplex.obj P) a)) := by
  rw [dgHomEquiv_dgMap_mapDGTwistedObject, F.dgHomEquiv_dgMap_mapDGTwistedComplex_toShift P a,
    dgHomEquiv_dgMap_mapDGTwistedObject]

/-- The image of the comparison `P⟦a + b⟧ ⟶ P⟦a⟧⟦b⟧` of iterated shifts has the matrix of the
comparison `(F P)⟦a + b⟧ ⟶ (F P)⟦a⟧⟦b⟧`. -/
theorem dgHomEquiv_dgMap_mapDGTwistedComplex_shiftAddHom (a b : ℤ) :
    DGTwistedObject.dgHomEquiv R _ _ 0 (F.mapDGTwistedComplex.dgMap 0 (shiftAddHom P a b)) =
      DGTwistedObject.dgHomEquiv R _ _ 0 (shiftAddHom (F.mapDGTwistedComplex.obj P) a b) := by
  rw [shiftAddHom_def, shiftAddHom_def, EnrichedFunctor.dgMap_dgComp,
    EnrichedFunctor.dgMap_dgComp, DGTwistedObject.dgHomEquiv_dgComp,
    DGTwistedObject.dgHomEquiv_dgComp, DGTwistedObject.dgHomEquiv_dgComp,
    DGTwistedObject.dgHomEquiv_dgComp, F.dgHomEquiv_dgMap_mapDGTwistedComplex_fromShift P (a + b),
    F.dgHomEquiv_dgMap_mapDGTwistedComplex_toShift P b,
    F.dgHomEquiv_dgMap_mapDGTwistedComplex_dgMap_shiftFunctor b,
    F.dgHomEquiv_dgMap_shiftFunctor_dgMap_mapDGTwistedComplex_toShift P a b]

end shift

/-! ### Commutation with the shift of the homotopy category -/

section commShift

variable (n : ℤ)

/-- The natural isomorphism `F (P⟦n⟧) ≅ (F P)⟦n⟧` of functors between the homotopy categories of
twisted complexes, the classes of `CategoryTheory.EnrichedFunctor.mapDGTwistedComplexShiftHom`.
It is the isomorphism `Functor.commShiftIso` of the `Functor.CommShift` instance. -/
noncomputable def mapDGTwistedComplexShiftIso :
    shiftFunctor
        (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) n ⋙
        F.mapDGTwistedComplex.mapDGHomotopyCategory ≅
      F.mapDGTwistedComplex.mapDGHomotopyCategory ⋙
        shiftFunctor
          (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure D)))) n :=
  NatIso.ofComponents (fun X ↦
      { hom := homOf R (F.mapDGTwistedComplexShiftHom (underlying R X) n)
          ((mem_dgCycles R).mpr (F.dgDifferential_mapDGTwistedComplexShiftHom _ n))
        inv := homOf R (F.mapDGTwistedComplexShiftInv (underlying R X) n)
          ((mem_dgCycles R).mpr (F.dgDifferential_mapDGTwistedComplexShiftInv _ n))
        hom_inv_id := homOf_comp_eq_id_of_dgComp_eq_dgId R _ _
          (F.dgComp_mapDGTwistedComplexShiftHom_mapDGTwistedComplexShiftInv _ n)
        inv_hom_id := homOf_comp_eq_id_of_dgComp_eq_dgId R _ _
          (F.dgComp_mapDGTwistedComplexShiftInv_mapDGTwistedComplexShiftHom _ n) })
    fun {X Y} f ↦ by
      obtain ⟨P, rfl⟩ := of_surjective R X
      obtain ⟨Q, rfl⟩ := of_surjective R Y
      obtain ⟨f, hf, rfl⟩ := exists_homOf_eq R f
      have h₁ : F.mapDGTwistedComplex.mapDGHomotopyCategory.map
          ((shiftFunctor (DGHomotopyCategory R
            (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) n).map (homOf R f hf)) =
            homOf R (F.mapDGTwistedComplex.dgMap 0 ((DGTwistedObject.shiftFunctor R n).dgMap 0 f))
              (F.mapDGTwistedComplex.dgMap_mem_dgCycles
                ((DGTwistedObject.shiftFunctor R n).dgMap_mem_dgCycles hf)) := by
        rw [DGTwistedObject.shiftFunctor_map_homOf]
        exact mapDGHomotopyCategory_map_homOf _ _ _
      have h₂ : (shiftFunctor (DGHomotopyCategory R
            (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure D)))) n).map
          (F.mapDGTwistedComplex.mapDGHomotopyCategory.map (homOf R f hf)) =
            homOf R ((DGTwistedObject.shiftFunctor R n).dgMap 0 (F.mapDGTwistedComplex.dgMap 0 f))
              ((DGTwistedObject.shiftFunctor R n).dgMap_mem_dgCycles
                (F.mapDGTwistedComplex.dgMap_mem_dgCycles hf)) := by
        rw [mapDGHomotopyCategory_map_homOf]
        exact DGTwistedObject.shiftFunctor_map_homOf n _ _
      rw [Functor.comp_map, Functor.comp_map, h₁, h₂]
      exact (homOf_comp_eq_homOf_of_dgComp_eq R _ _
        (dgCompZero_mem_dgCycles R
          ((mem_dgCycles R).mpr (F.dgDifferential_mapDGTwistedComplexShiftHom P n))
          ((DGTwistedObject.shiftFunctor R n).dgMap_mem_dgCycles
            (F.mapDGTwistedComplex.dgMap_mem_dgCycles hf)))
        ((F.dgComp_dgMap_shiftFunctor_mapDGTwistedComplexShiftHom n f).trans
          (dgCompZero_def R _ _).symm)).trans (homOf_comp R _ _ _ _).symm

/-- The component of the shift isomorphism at a twisted complex. -/
@[simp]
theorem mapDGTwistedComplexShiftIso_hom_app_of
    (P : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))) :
    (F.mapDGTwistedComplexShiftIso n).hom.app (of R P) =
      homOf R (F.mapDGTwistedComplexShiftHom P n)
        ((mem_dgCycles R).mpr (F.dgDifferential_mapDGTwistedComplexShiftHom P n)) :=
  (rfl)

/-- The inverse of the component of the shift isomorphism at a twisted complex. -/
@[simp]
theorem mapDGTwistedComplexShiftIso_inv_app_of
    (P : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))) :
    (F.mapDGTwistedComplexShiftIso n).inv.app (of R P) =
      homOf R (F.mapDGTwistedComplexShiftInv P n)
        ((mem_dgCycles R).mpr (F.dgDifferential_mapDGTwistedComplexShiftInv P n)) :=
  (rfl)

/-- The shift isomorphism by zero is the canonical one, given by the isomorphisms `P⟦0⟧ ≅ P`. -/
theorem mapDGTwistedComplexShiftIso_zero :
    F.mapDGTwistedComplexShiftIso 0 =
      Functor.CommShift.isoZero F.mapDGTwistedComplex.mapDGHomotopyCategory ℤ := by
  ext X
  obtain ⟨P, rfl⟩ := of_surjective R X
  have h : F.mapDGTwistedComplex.mapDGHomotopyCategory.map
      ((shiftFunctorZero (DGHomotopyCategory R
        (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) ℤ).hom.app (of R P)) =
        homOf R (F.mapDGTwistedComplex.dgMap 0 (fromShift P 0))
          (F.mapDGTwistedComplex.dgMap_mem_dgCycles
            ((mem_dgCycles R).mpr (dgDifferential_fromShift P 0))) := by
    rw [DGTwistedObject.shiftFunctorZero_hom_app_of]
    exact mapDGHomotopyCategory_map_homOf _ _ _
  have h' : (shiftFunctorZero (DGHomotopyCategory R
      (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure D)))) ℤ).inv.app
        (F.mapDGTwistedComplex.mapDGHomotopyCategory.obj (of R P)) =
        homOf R (toShift (F.mapDGTwistedComplex.obj P) 0)
          ((mem_dgCycles R).mpr (dgDifferential_toShift _ 0)) :=
    DGTwistedObject.shiftFunctorZero_inv_app_of _
  rw [mapDGTwistedComplexShiftIso_hom_app_of, Functor.CommShift.isoZero_hom_app, h, h']
  refine (homOf_comp_eq_homOf_of_dgComp_eq R _ _ _
    ((DGTwistedObject.dgHomEquiv R _ _ 0).injective ?_)).symm
  rw [DGTwistedObject.dgHomEquiv_dgComp, F.dgHomEquiv_dgMap_mapDGTwistedComplex_fromShift P 0,
    ← DGTwistedObject.dgHomEquiv_dgComp, dgComp_fromShift_toShift,
    dgHomEquiv_mapDGTwistedComplexShiftHom, DGTwistedObject.dgHomEquiv_dgId]

/-- The class of `F (P⟦a + b⟧) ⟶ (F P)⟦a + b⟧` factors through the images of the comparisons of
iterated shifts. -/
private theorem homOf_comp_homOf_comp_homOf_comp_homOf (P : DGTwistedObject R
    (DGAdditiveClosure (DGShiftClosure C))) (a b : ℤ) :
    homOf R (F.mapDGTwistedComplex.dgMap 0 (shiftAddHom P a b))
        (F.mapDGTwistedComplex.dgMap_mem_dgCycles
          ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom P a b))) ≫
      homOf R (F.mapDGTwistedComplexShiftHom ((DGTwistedObject.shiftFunctor R a).obj P) b)
        ((mem_dgCycles R).mpr (F.dgDifferential_mapDGTwistedComplexShiftHom _ b)) ≫
      homOf R ((DGTwistedObject.shiftFunctor R b).dgMap 0 (F.mapDGTwistedComplexShiftHom P a))
        ((DGTwistedObject.shiftFunctor R b).dgMap_mem_dgCycles
          ((mem_dgCycles R).mpr (F.dgDifferential_mapDGTwistedComplexShiftHom P a))) ≫
      homOf R (shiftAddInv (F.mapDGTwistedComplex.obj P) a b)
        ((mem_dgCycles R).mpr (dgDifferential_shiftAddInv _ a b)) =
    homOf R (F.mapDGTwistedComplexShiftHom P (a + b))
      ((mem_dgCycles R).mpr (F.dgDifferential_mapDGTwistedComplexShiftHom P (a + b))) := by
  rw [homOf_comp, homOf_comp, homOf_comp]
  congr 1
  simp only [dgCompZero_def]
  refine (DGTwistedObject.dgHomEquiv R _ _ 0).injective ?_
  rw [DGTwistedObject.dgHomEquiv_dgComp, DGTwistedObject.dgHomEquiv_dgComp,
    DGTwistedObject.dgHomEquiv_dgComp,
    F.dgHomEquiv_mapDGTwistedComplexShiftHom ((DGTwistedObject.shiftFunctor R a).obj P) b,
    F.dgHomEquiv_dgMap_mapDGTwistedComplex_shiftAddHom P a b, dgHomEquiv_dgMap_mapDGTwistedObject,
    F.dgHomEquiv_mapDGTwistedComplexShiftHom P a, dgMap_dgId, dgId_dgComp, dgId_dgComp,
    ← DGTwistedObject.dgHomEquiv_dgComp, dgComp_shiftAddHom_shiftAddInv,
    DGTwistedObject.dgHomEquiv_dgId, F.dgHomEquiv_mapDGTwistedComplexShiftHom P (a + b)]

/-- The shift isomorphism by `a + b` is obtained from those by `a` and by `b` through the
isomorphisms `P⟦a + b⟧ ≅ P⟦a⟧⟦b⟧`. -/
theorem mapDGTwistedComplexShiftIso_add (a b : ℤ) :
    F.mapDGTwistedComplexShiftIso (a + b) =
      Functor.CommShift.isoAdd (F.mapDGTwistedComplexShiftIso a)
        (F.mapDGTwistedComplexShiftIso b) := by
  ext X
  obtain ⟨P, rfl⟩ := of_surjective R X
  have h₁ : F.mapDGTwistedComplex.mapDGHomotopyCategory.map
      ((shiftFunctorAdd (DGHomotopyCategory R
        (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) a b).hom.app (of R P)) =
        homOf R (F.mapDGTwistedComplex.dgMap 0 (shiftAddHom P a b))
          (F.mapDGTwistedComplex.dgMap_mem_dgCycles
            ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom P a b))) := by
    rw [DGTwistedObject.shiftFunctorAdd_hom_app_of]
    exact mapDGHomotopyCategory_map_homOf _ _ _
  have h₃ : (shiftFunctor (DGHomotopyCategory R
      (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure D)))) b).map
        ((F.mapDGTwistedComplexShiftIso a).hom.app (of R P)) =
        homOf R ((DGTwistedObject.shiftFunctor R b).dgMap 0 (F.mapDGTwistedComplexShiftHom P a))
          ((DGTwistedObject.shiftFunctor R b).dgMap_mem_dgCycles
            ((mem_dgCycles R).mpr (F.dgDifferential_mapDGTwistedComplexShiftHom P a))) := by
    rw [mapDGTwistedComplexShiftIso_hom_app_of]
    exact DGTwistedObject.shiftFunctor_map_homOf b _ _
  rw [mapDGTwistedComplexShiftIso_hom_app_of, Functor.CommShift.isoAdd_hom_app, h₁, h₃]
  exact (F.homOf_comp_homOf_comp_homOf_comp_homOf P a b).symm.trans
    (congrArg (_ ≫ _ ≫ _ ≫ ·) (DGTwistedObject.shiftFunctorAdd_inv_app_of _ a b).symm)

/-- **The functor induced by a DG functor on homotopy categories of twisted complexes commutes
with the shifts.** -/
noncomputable instance : F.mapDGTwistedComplex.mapDGHomotopyCategory.CommShift ℤ where
  commShiftIso := F.mapDGTwistedComplexShiftIso
  commShiftIso_zero := F.mapDGTwistedComplexShiftIso_zero
  commShiftIso_add := F.mapDGTwistedComplexShiftIso_add

/-- The isomorphism `H⁰(F) (P⟦n⟧) ≅ (H⁰(F) P)⟦n⟧` of the shift structure is the class of
`CategoryTheory.EnrichedFunctor.mapDGTwistedComplexShiftHom`. -/
@[simp]
theorem commShiftIso_mapDGTwistedComplex_hom_app_of
    (P : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))) :
    (F.mapDGTwistedComplex.mapDGHomotopyCategory.commShiftIso n).hom.app (of R P) =
      homOf R (F.mapDGTwistedComplexShiftHom P n)
        ((mem_dgCycles R).mpr (F.dgDifferential_mapDGTwistedComplexShiftHom P n)) :=
  (rfl)

/-- The inverse isomorphism `(H⁰(F) P)⟦n⟧ ≅ H⁰(F) (P⟦n⟧)` of the shift structure is the class of
`CategoryTheory.EnrichedFunctor.mapDGTwistedComplexShiftInv`. -/
@[simp]
theorem commShiftIso_mapDGTwistedComplex_inv_app_of
    (P : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))) :
    (F.mapDGTwistedComplex.mapDGHomotopyCategory.commShiftIso n).inv.app (of R P) =
      homOf R (F.mapDGTwistedComplexShiftInv P n)
        ((mem_dgCycles R).mpr (F.dgDifferential_mapDGTwistedComplexShiftInv P n)) :=
  (rfl)

end commShift

/-! ### Cone triangles -/

section cone

variable {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} {u : DGHom R 0 P Q}
  (hu : dgDifferential R 0 u = 0)

/-- The isomorphism `F (P⟦1⟧) ⟶ (F P)⟦1⟧` followed by the degree-one morphism underlying `F u` is
the image of the degree-one morphism underlying `u`, the gluing morphism of its cone. -/
theorem dgComp_mapDGTwistedComplexShiftHom_coneMorphism (u : DGHom R 0 P Q) :
    dgComp R (F.mapDGTwistedComplexShiftHom P 1) (coneMorphism R (F.mapDGTwistedComplex.dgMap 0 u))
      (zero_add 1) = F.mapDGTwistedComplex.dgMap 1 (coneMorphism R u) :=
  (DGTwistedObject.dgHomEquiv R _ _ 1).injective <| by
    rw [coneMorphism_def, coneMorphism_def, EnrichedFunctor.dgMap_dgComp,
      DGTwistedObject.dgHomEquiv_dgComp, DGTwistedObject.dgHomEquiv_dgComp,
      DGTwistedObject.dgHomEquiv_dgComp, dgHomEquiv_mapDGTwistedComplexShiftHom, dgId_dgComp,
      F.dgHomEquiv_dgMap_mapDGTwistedComplex_fromShift P 1]

/-- **A DG functor preserves cones**: the image of the cone of a closed morphism `u` is isomorphic
in the homotopy category to the cone of `F u`. -/
noncomputable def mapConeIso :
    of R (F.mapDGTwistedComplex.obj (cone u hu)) ≅
      of R (cone (F.mapDGTwistedComplex.dgMap 0 u)
        (F.mapDGTwistedComplex.dgDifferential_dgMap_eq_zero hu)) :=
  F.mapDGShiftClosure.mapExtensionIso (dgDifferential_coneMorphism hu) ≪≫
    extensionIsoOfIso R (F.dgDifferential_mapDGTwistedComplexShiftHom P 1)
      (F.dgComp_mapDGTwistedComplexShiftHom_mapDGTwistedComplexShiftInv P 1)
      (F.dgComp_mapDGTwistedComplexShiftInv_mapDGTwistedComplexShiftHom P 1)
      (F.dgComp_mapDGTwistedComplexShiftHom_coneMorphism u)

/-- The isomorphism of cones is the comparison of the image of an extension with the extension of
the images, followed by the isomorphism of extensions induced by `F (P⟦1⟧) ⟶ (F P)⟦1⟧`. -/
@[simp]
theorem mapConeIso_hom :
    (F.mapConeIso hu).hom =
      (F.mapDGShiftClosure.mapExtensionIso (dgDifferential_coneMorphism hu)).hom ≫
        (extensionIsoOfIso R (F.dgDifferential_mapDGTwistedComplexShiftHom P 1)
          (F.dgComp_mapDGTwistedComplexShiftHom_mapDGTwistedComplexShiftInv P 1)
          (F.dgComp_mapDGTwistedComplexShiftInv_mapDGTwistedComplexShiftHom P 1)
          (F.dgComp_mapDGTwistedComplexShiftHom_coneMorphism u)).hom :=
  (rfl)

/-- The inverse of the isomorphism of cones is the isomorphism of extensions induced by
`(F P)⟦1⟧ ⟶ F (P⟦1⟧)`, followed by the comparison of the extension of the images with the image of
an extension. -/
@[simp]
theorem mapConeIso_inv :
    (F.mapConeIso hu).inv =
      (extensionIsoOfIso R (F.dgDifferential_mapDGTwistedComplexShiftHom P 1)
          (F.dgComp_mapDGTwistedComplexShiftHom_mapDGTwistedComplexShiftInv P 1)
          (F.dgComp_mapDGTwistedComplexShiftInv_mapDGTwistedComplexShiftHom P 1)
          (F.dgComp_mapDGTwistedComplexShiftHom_coneMorphism u)).inv ≫
        (F.mapDGShiftClosure.mapExtensionIso (dgDifferential_coneMorphism hu)).inv :=
  (rfl)

/-- The image of the inclusion `Q ⟶ cone u`, followed by the isomorphism of cones, is the inclusion
`F Q ⟶ cone (F u)`. -/
@[reassoc]
theorem homOf_dgMap_extensionInl_comp_mapConeIso_hom :
    homOf R (F.mapDGTwistedComplex.dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu)))
        (F.mapDGTwistedComplex.dgMap_mem_dgCycles
          ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _))) ≫ (F.mapConeIso hu).hom =
      homOf R (extensionInl R (dgDifferential_coneMorphism
          (F.mapDGTwistedComplex.dgDifferential_dgMap_eq_zero hu)))
        ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _)) := by
  simp only [mapConeIso_hom, mapExtensionIso_hom, extensionIsoOfIso_hom, homOf_comp,
    dgCompZero_def]
  congr 1
  rw [← dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_dgMap_extensionInl_mapExtensionHom, dgComp_extensionInl_extensionMap]

/-- The isomorphism of cones, followed by the projection `cone (F u) ⟶ (F P)⟦1⟧`, is the image of
the projection `cone u ⟶ P⟦1⟧` followed by the isomorphism `F (P⟦1⟧) ⟶ (F P)⟦1⟧`. -/
@[reassoc]
theorem mapConeIso_hom_comp_homOf_extensionSnd :
    (F.mapConeIso hu).hom ≫ homOf R (extensionSnd R (dgDifferential_coneMorphism
          (F.mapDGTwistedComplex.dgDifferential_dgMap_eq_zero hu)))
        ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) =
      homOf R (F.mapDGTwistedComplex.dgMap 0 (extensionSnd R (dgDifferential_coneMorphism hu)))
          (F.mapDGTwistedComplex.dgMap_mem_dgCycles
            ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _))) ≫
        homOf R (F.mapDGTwistedComplexShiftHom P 1)
          ((mem_dgCycles R).mpr (F.dgDifferential_mapDGTwistedComplexShiftHom P 1)) := by
  simp only [mapConeIso_hom, mapExtensionIso_hom, extensionIsoOfIso_hom, homOf_comp,
    dgCompZero_def]
  congr 1
  rw [dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_extensionMap_extensionSnd,
    ← dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_mapExtensionHom_extensionSnd]

/-- **The image of a cone triangle is the cone triangle of the image**: the image under `H⁰(F)` of
the cone triangle `P ⟶ Q ⟶ cone u ⟶ P⟦1⟧` is isomorphic to the cone triangle of `F u`, by the
identities of `F P` and `F Q` and the isomorphism of cones. -/
noncomputable def mapConeTriangleIso :
    F.mapDGTwistedComplex.mapDGHomotopyCategory.mapTriangle.obj (coneTriangle u hu) ≅
      coneTriangle (F.mapDGTwistedComplex.dgMap 0 u)
        (F.mapDGTwistedComplex.dgDifferential_dgMap_eq_zero hu) :=
  Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (F.mapConeIso hu)
    -- Each square is the corresponding compatibility of the isomorphism of cones, with identities
    -- on the first two objects.  The objects of the image of the cone triangle agree with those of
    -- the cone triangle of `F u` only after unfolding `H⁰(F)`, so the squares cannot be rewritten
    -- and are closed by composing with `Category.comp_id` and `Category.id_comp`.
    (by
      have h := F.mapDGTwistedComplex.mapDGHomotopyCategory_map_homOf u ((mem_dgCycles R).mpr hu)
      exact (Category.comp_id _).trans (h.trans (Category.id_comp _).symm))
    (by
      have h := F.homOf_dgMap_extensionInl_comp_mapConeIso_hom hu
      rw [← mapDGHomotopyCategory_map_homOf] at h
      exact h.trans (Category.id_comp _).symm)
    (by
      have h := F.mapConeIso_hom_comp_homOf_extensionSnd hu
      rw [← mapDGHomotopyCategory_map_homOf _ _
        ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _))] at h
      exact (congrArg (_ ≫ ·) (Functor.map_id _ _)).trans ((Category.comp_id _).trans h.symm))

@[simp]
theorem mapConeTriangleIso_hom_hom₃ :
    (F.mapConeTriangleIso hu).hom.hom₃ = (F.mapConeIso hu).hom :=
  (rfl)

@[simp]
theorem mapConeTriangleIso_inv_hom₃ :
    (F.mapConeTriangleIso hu).inv.hom₃ = (F.mapConeIso hu).inv :=
  (rfl)

/-- **The functor induced by a DG functor on homotopy categories of twisted complexes is
triangulated**: it sends cone triangles to triangles isomorphic to cone triangles. -/
instance : F.mapDGTwistedComplex.mapDGHomotopyCategory.IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨P, Q, u, hu, ⟨e⟩⟩ := mem_distinguishedTriangles_iff.mp hT
    exact mem_distinguishedTriangles_iff.mpr ⟨_, _, _, _,
      ⟨F.mapDGTwistedComplex.mapDGHomotopyCategory.mapTriangle.mapIso e ≪≫
        F.mapConeTriangleIso hu⟩⟩

end cone


/-- **`H⁰(F)` preserves the pretriangulated envelope**: it sends one-sided twisted complexes to
one-sided twisted complexes. -/
theorem oneSided_mapDGHomotopyCategory_obj
    {X : DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))}
    (hX : oneSided R C X) : oneSided R D (F.mapDGTwistedComplex.mapDGHomotopyCategory.obj X) :=
  (oneSided_iff _).mpr (DGTwistedObject.IsOneSided.map (G := F.mapDGShiftClosure)
    ((oneSided_iff X).mp hX))

end CategoryTheory.EnrichedFunctor
