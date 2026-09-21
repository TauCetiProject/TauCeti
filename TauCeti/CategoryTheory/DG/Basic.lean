/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Enriched.Basic
public import TauCeti.Algebra.Homology.Monoidal.Summand
public import TauCeti.Algebra.Homology.Monoidal.TensorDifferential

/-!
# Differential graded categories

A differential graded category over a commutative ring `R` is a category enriched in cochain
complexes of `R`-modules: every Hom object is a complex `Hom(X, Y)`, and composition is a closed
degree-zero map out of the tensor product of two Hom complexes.

This file fixes that definition and unpacks the enriched data into the calculus one actually
computes with: the `R`-module `DGHom R n X Y` of morphisms of degree `n`, the differential raising
the degree by one, the composition of two homogeneous morphisms, and the identity.  The enriched
axioms then become the associativity and unit laws for that composition, and the fact that
composition is a chain map out of the tensor product becomes the graded Leibniz rule

`d (dgComp f g) = dgComp (d f) g + (-1) ^ |f| • dgComp f (d g)`.

The factor order is Mathlib's: `CategoryTheory.eComp` composes
`Hom(X, Y) ⊗ Hom(Y, Z) ⟶ Hom(X, Z)`, so `dgComp f g` is `f` followed by `g` and the Leibniz sign
is carried by the degree of the *first* argument, exactly as in
`CochainComplex.HomComplex.δ_comp`.

The identity is a degree-zero cycle, so the closed degree-zero morphisms form an ordinary
category; that category and its quotient by homotopy are not built here.

## Main definitions

* `TauCeti.DGCategory`: a differential graded category over `R`.
* `TauCeti.dgHomComplex`: its Hom complex.
* `TauCeti.DGHom`: the `R`-module of morphisms of a fixed degree.
* `TauCeti.dgDifferential`: the differential of the Hom complex.
* `TauCeti.dgComp`: composition of two homogeneous morphisms.
* `TauCeti.dgId`: the identity, a degree-zero morphism.

## Main results

* `TauCeti.dgDifferential_dgComp`: the graded Leibniz rule.
* `TauCeti.dgComp_assoc`: composition of homogeneous morphisms is associative.
* `TauCeti.dgId_dgComp` and `TauCeti.dgComp_dgId`: the identity is a two-sided unit.
* `TauCeti.dgDifferential_dgId`: the identity is a cycle.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the sign
  conventions.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.
-/

public section

open CategoryTheory MonoidalCategory HomologicalComplex

namespace TauCeti

universe v u

/-- A **differential graded category** over a commutative ring `R`: a category enriched in
cochain complexes of `R`-modules.  Its Hom complexes are `TauCeti.dgHomComplex`, and the
morphisms of a fixed degree, their differential, and their composition are `TauCeti.DGHom`,
`TauCeti.dgDifferential` and `TauCeti.dgComp`. -/
abbrev DGCategory (R : Type v) [CommRing R] (C : Type u) :=
  EnrichedCategory (CochainComplex (ModuleCat.{v} R) ℤ) C

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

/-- The Hom complex of a differential graded category. -/
abbrev dgHomComplex (X Y : C) : CochainComplex (ModuleCat.{v} R) ℤ :=
  X ⟶[CochainComplex (ModuleCat.{v} R) ℤ] Y

/-- The `R`-module of morphisms `X ⟶ Y` of degree `n` in a differential graded category. -/
abbrev DGHom (n : ℤ) (X Y : C) : Type v := (dgHomComplex R X Y).X n

/-- The differential of a differential graded category, raising the degree of a morphism by
one. -/
noncomputable abbrev dgDifferential {X Y : C} (n : ℤ) :
    DGHom R n X Y →ₗ[R] DGHom R (n + 1) X Y :=
  ((dgHomComplex R X Y).d n (n + 1)).hom

/-- The differential of a differential graded category squares to zero. -/
@[simp]
theorem dgDifferential_dgDifferential {X Y : C} {n : ℤ} (f : DGHom R n X Y) :
    dgDifferential R (n + 1) (dgDifferential R n f) = 0 := by
  rw [← ModuleCat.comp_apply, (dgHomComplex R X Y).d_comp_d]
  simp

/-! ### Composition -/

/-- The bidegree-`(p, q)` component of the enriched composition of a differential graded
category: it computes `TauCeti.dgComp` on a pure tensor. -/
noncomputable def dgCompMap (X Y Z : C) (p q n : ℤ) (h : p + q = n) :
    (dgHomComplex R X Y).X p ⊗ (dgHomComplex R Y Z).X q ⟶ (dgHomComplex R X Z).X n :=
  ιTensorObj (dgHomComplex R X Y) (dgHomComplex R Y Z) p q n h ≫
    (eComp (CochainComplex (ModuleCat.{v} R) ℤ) X Y Z).f n

/-- The bidegree component of enriched composition is the inclusion of that summand of the tensor
product of the two Hom complexes, followed by the enriched composition. -/
theorem dgCompMap_def (X Y Z : C) (p q n : ℤ) (h : p + q = n) :
    dgCompMap R X Y Z p q n h =
      ιTensorObj (dgHomComplex R X Y) (dgHomComplex R Y Z) p q n h ≫
        (eComp (CochainComplex (ModuleCat.{v} R) ℤ) X Y Z).f n :=
  (rfl)

/-- Composition of a morphism of degree `p` from `X` to `Y` with a morphism of degree `q` from
`Y` to `Z`, in Mathlib's enriched factor order: `dgComp f g` is `f` followed by `g`. -/
noncomputable def dgComp {X Y Z : C} {p q n : ℤ} (f : DGHom R p X Y) (g : DGHom R q Y Z)
    (h : p + q = n) : DGHom R n X Z :=
  (dgCompMap R X Y Z p q n h).hom (f ⊗ₜ g)

@[simp]
theorem dgCompMap_tmul {X Y Z : C} {p q n : ℤ} (h : p + q = n) (f : DGHom R p X Y)
    (g : DGHom R q Y Z) :
    (dgCompMap R X Y Z p q n h).hom (f ⊗ₜ g) = dgComp R f g h :=
  (rfl)

@[simp]
theorem zero_dgComp {X Y Z : C} {p q n : ℤ} (g : DGHom R q Y Z) (h : p + q = n) :
    dgComp R (0 : DGHom R p X Y) g h = 0 := by
  rw [dgComp, TensorProduct.zero_tmul, map_zero]

@[simp]
theorem dgComp_zero {X Y Z : C} {p q n : ℤ} (f : DGHom R p X Y) (h : p + q = n) :
    dgComp R f (0 : DGHom R q Y Z) h = 0 := by
  rw [dgComp, TensorProduct.tmul_zero, map_zero]

@[simp]
theorem add_dgComp {X Y Z : C} {p q n : ℤ} (f f' : DGHom R p X Y) (g : DGHom R q Y Z)
    (h : p + q = n) : dgComp R (f + f') g h = dgComp R f g h + dgComp R f' g h := by
  rw [dgComp, dgComp, dgComp, TensorProduct.add_tmul, map_add]

@[simp]
theorem dgComp_add {X Y Z : C} {p q n : ℤ} (f : DGHom R p X Y) (g g' : DGHom R q Y Z)
    (h : p + q = n) : dgComp R f (g + g') h = dgComp R f g h + dgComp R f g' h := by
  rw [dgComp, dgComp, dgComp, TensorProduct.tmul_add, map_add]

@[simp]
theorem neg_dgComp {X Y Z : C} {p q n : ℤ} (f : DGHom R p X Y) (g : DGHom R q Y Z)
    (h : p + q = n) : dgComp R (-f) g h = -dgComp R f g h := by
  rw [dgComp, dgComp, TensorProduct.neg_tmul, map_neg]

@[simp]
theorem dgComp_neg {X Y Z : C} {p q n : ℤ} (f : DGHom R p X Y) (g : DGHom R q Y Z)
    (h : p + q = n) : dgComp R f (-g) h = -dgComp R f g h := by
  rw [dgComp, dgComp, TensorProduct.tmul_neg, map_neg]

@[simp]
theorem smul_dgComp {X Y Z : C} {p q n : ℤ} (r : R) (f : DGHom R p X Y) (g : DGHom R q Y Z)
    (h : p + q = n) : dgComp R (r • f) g h = r • dgComp R f g h := by
  rw [dgComp, dgComp, ← TensorProduct.smul_tmul', map_smul]

@[simp]
theorem dgComp_smul {X Y Z : C} {p q n : ℤ} (r : R) (f : DGHom R p X Y) (g : DGHom R q Y Z)
    (h : p + q = n) : dgComp R f (r • g) h = r • dgComp R f g h := by
  rw [dgComp, dgComp, TensorProduct.tmul_smul, map_smul]

/-! ### The Leibniz rule -/

/- Composition is a chain map out of the tensor product of the two Hom complexes; restricting
that equation to a bidegree summand is the Leibniz rule before evaluation. -/
private lemma dgCompMap_comp_d (X Y Z : C) (p q n : ℤ) (h : p + q = n) :
    dgCompMap R X Y Z p q n h ≫ (dgHomComplex R X Z).d n (n + 1) =
      ((dgHomComplex R X Y).d p (p + 1) ▷ (dgHomComplex R Y Z).X q) ≫
          dgCompMap R X Y Z (p + 1) q (n + 1) (by omega) +
        p.negOnePow • (((dgHomComplex R X Y).X p ◁ (dgHomComplex R Y Z).d q (q + 1)) ≫
          dgCompMap R X Y Z p (q + 1) (n + 1) (by omega)) := by
  rw [dgCompMap, Category.assoc,
    (eComp (CochainComplex (ModuleCat.{v} R) ℤ) X Y Z).comm n (n + 1), ← Category.assoc,
    ι_tensorObj_d]
  simp [dgCompMap]

/-- **The graded Leibniz rule** in a differential graded category: the differential of a
composite differentiates each factor, with the Koszul sign carried by the degree of the first
factor. -/
theorem dgDifferential_dgComp {X Y Z : C} {p q n : ℤ} (f : DGHom R p X Y) (g : DGHom R q Y Z)
    (h : p + q = n) :
    dgDifferential R n (dgComp R f g h) =
      dgComp R (dgDifferential R p f) g (by omega) +
        p.negOnePow • dgComp R f (dgDifferential R q g) (by omega) := by
  have key := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (dgCompMap_comp_d R X Y Z p q n h)) (f ⊗ₜ g)
  simpa only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, dgCompMap_tmul,
    ModuleCat.hom_add, ModuleCat.hom_smul, LinearMap.add_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, LinearMap.smul_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply] using key

/-! ### Associativity -/

/- The enriched associativity axiom, restricted to a summand of the triple tensor product of Hom
complexes. -/
private lemma dgCompMap_assoc (W X Y Z : C) (p q r n : ℤ) (h : p + q + r = n) :
    (dgCompMap R W X Y p q (p + q) rfl ▷ (dgHomComplex R Y Z).X r) ≫
        dgCompMap R W Y Z (p + q) r n h =
      (α_ ((dgHomComplex R W X).X p) ((dgHomComplex R X Y).X q)
          ((dgHomComplex R Y Z).X r)).hom ≫
        ((dgHomComplex R W X).X p ◁ dgCompMap R X Y Z q r (q + r) rfl) ≫
          dgCompMap R W X Z p (q + r) n (by omega) := by
  rw [dgCompMap, dgCompMap, comp_whiskerRight, Category.assoc, ← ι_whiskerRight_assoc,
    ← HomologicalComplex.comp_f, ← e_assoc' (CochainComplex (ModuleCat.{v} R) ℤ) W X Y Z,
    HomologicalComplex.comp_f, HomologicalComplex.comp_f, ι_ι_associator_hom_assoc,
    dgCompMap, dgCompMap]
  simp only [ι_whiskerLeft_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]

/-- Composition of homogeneous morphisms in a differential graded category is associative. -/
theorem dgComp_assoc {W X Y Z : C} {p q r pq qr n : ℤ} (f : DGHom R p W X) (g : DGHom R q X Y)
    (k : DGHom R r Y Z) (hpq : p + q = pq) (hqr : q + r = qr) (hn : p + q + r = n) :
    dgComp R (dgComp R f g hpq) k (show pq + r = n by rw [← hpq, hn]) =
      dgComp R f (dgComp R g k hqr) (by rw [← hqr, ← hn, add_assoc]) := by
  subst hpq
  subst hqr
  have key := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (dgCompMap_assoc R W X Y Z p q r n hn)) ((f ⊗ₜ g) ⊗ₜ k)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.associator_hom_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, dgCompMap_tmul] at key
  exact key

/-! ### The identity -/

/-- The identity morphism of an object of a differential graded category: the degree-zero
morphism named by the enriched identity, that is, the image of `1` under the degree-zero
component of `CategoryTheory.eId`. -/
noncomputable def dgId (X : C) : DGHom R 0 X X :=
  ((eId (CochainComplex (ModuleCat.{v} R) ℤ) X).f 0).hom
    ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).inv 1)

/-- The identity is the image of `1` under the degree-zero component of the enriched identity. -/
theorem dgId_def (X : C) :
    dgId R X = ((eId (CochainComplex (ModuleCat.{v} R) ℤ) X).f 0).hom
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).inv 1) :=
  (rfl)

/-- The identity of a differential graded category is a cycle, so it is a morphism of the
underlying category of closed degree-zero morphisms. -/
@[simp]
theorem dgDifferential_dgId (X : C) : dgDifferential R 0 (dgId R X) = 0 := by
  have hu : (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)).d 0 (0 + 1) = 0 :=
    HomologicalComplex.single_obj_d (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{v} R)) 0 (0 + 1)
  rw [dgId, ← ModuleCat.comp_apply,
    (eId (CochainComplex (ModuleCat.{v} R) ℤ) X).comm 0 (0 + 1), hu, Limits.zero_comp]
  simp

/-- The identity is a left unit for composition. -/
@[simp]
theorem dgId_dgComp {X Y : C} {q : ℤ} (g : DGHom R q X Y) :
    dgComp R (dgId R X) g (zero_add q) = g := by
  have h := HomologicalComplex.congr_hom
    (e_id_comp (CochainComplex (ModuleCat.{v} R) ℤ) X Y) q
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, leftUnitor_inv_f,
    HomologicalComplex.leftUnitor'_inv, Category.assoc, Category.assoc,
    ι_whiskerRight_assoc, HomologicalComplex.id_f] at h
  have key := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) g
  simpa only [dgComp, dgCompMap, ModuleCat.hom_comp, dgId, LinearMap.coe_comp,
    Function.comp_apply, ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, ModuleCat.hom_id, LinearMap.id_coe,
    id_eq] using key

/-- The identity is a right unit for composition. -/
@[simp]
theorem dgComp_dgId {X Y : C} {p : ℤ} (f : DGHom R p X Y) :
    dgComp R f (dgId R Y) (add_zero p) = f := by
  have h := HomologicalComplex.congr_hom
    (e_comp_id (CochainComplex (ModuleCat.{v} R) ℤ) X Y) p
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, rightUnitor_inv_f,
    HomologicalComplex.rightUnitor'_inv, Category.assoc, Category.assoc,
    ι_whiskerLeft_assoc, HomologicalComplex.id_f] at h
  have key := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) f
  simpa only [dgComp, dgCompMap, ModuleCat.hom_comp, dgId, LinearMap.coe_comp,
    Function.comp_apply, ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply, ModuleCat.hom_id, LinearMap.id_coe,
    id_eq] using key

end TauCeti
