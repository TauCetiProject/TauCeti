/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.CategoryTheory.Limits.Shapes.Countable

import Mathlib.Algebra.Module.Basic
import Mathlib.CategoryTheory.Linear.Basic

/-!
# Product total complexes

The product total complex of a commuting double cochain complex has a product over each
antidiagonal. Its differential is horizontal plus the vertical differential multiplied by
`(-1)^p` in column `p`. Unlike direct-sum totalisation, this construction accepts families
with infinite support. The projections characterize morphisms into the total complex.

The convention agrees with Mathlib's direct-sum total complex. See the Stacks Project,
Homological Algebra, Lemma 26.3 (tag 09J0), for product totalisation.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace HomologicalComplex₂

variable {C : Type*} [Category* C]

section

variable [HasZeroMorphisms C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- A double complex admits product totalisation if its antidiagonal products exist. -/
abbrev HasProductTotal :=
  ∀ n : ℤ, HasProduct (fun i : {pq : ℤ × ℤ // pq.1 + pq.2 = n} => (K.X i.1.1).X i.1.2)

instance [HasCountableProducts C] : K.HasProductTotal := fun _ => inferInstance

end

variable [Preadditive C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [K.HasProductTotal]

private noncomputable abbrev productX (n : ℤ) : C :=
  ∏ᶜ (fun i : {pq : ℤ × ℤ // pq.1 + pq.2 = n} => (K.X i.1.1).X i.1.2)

private noncomputable abbrev productπ (p q n : ℤ) (h : p + q = n) :
    productX K n ⟶ (K.X p).X q :=
  Pi.π (fun i : {pq : ℤ × ℤ // pq.1 + pq.2 = n} =>
    (K.X i.1.1).X i.1.2) ⟨(p, q), h⟩

private noncomputable def productD (n : ℤ) : productX K n ⟶ productX K (n + 1) :=
  Pi.lift (f := fun i : {pq : ℤ × ℤ // pq.1 + pq.2 = n + 1} =>
    (K.X i.1.1).X i.1.2) fun ⟨⟨p, q⟩, h⟩ =>
    productπ K (p - 1) q n (by omega) ≫ (K.d (p - 1) p).f q +
      p.negOnePow • (productπ K p (q - 1) n (by omega) ≫ (K.X p).d (q - 1) q)

@[reassoc (attr := simp)]
private lemma productD_π (n p q : ℤ) (h : p + q = n + 1) :
    productD K n ≫ productπ K p q (n + 1) h =
      productπ K (p - 1) q n (by omega) ≫ (K.d (p - 1) p).f q +
        p.negOnePow • (productπ K p (q - 1) n (by omega) ≫ (K.X p).d (q - 1) q) := by
  simp [productD, productπ]

private lemma productD_comp (n : ℤ) : productD K n ≫ productD K (n + 1) = 0 := by
  apply Pi.hom_ext
  rintro ⟨⟨p, q⟩, h⟩
  simp only [Category.assoc, productD_π, productD_π_assoc, comp_add, zero_comp,
    Linear.comp_units_smul, add_comp, Linear.units_smul_comp]
  simp only [d_f_comp_d_f, HomologicalComplex.d_comp_d, comp_zero,
    smul_zero, zero_add, add_zero, d_comm]
  have hs : (p - 1).negOnePow = -p.negOnePow := by
    have := Int.negOnePow_succ (p - 1)
    simp only [sub_add_cancel] at this
    rw [this, neg_neg]
  simp [hs, Units.neg_smul]

/-- The product total cochain complex, with differential `d₁ + (-1)^p d₂` in column `p`. -/
noncomputable def productTotal : CochainComplex C ℤ :=
  CochainComplex.of (productX K) (productD K) (productD_comp K)

/-- Projection from a term of the product total complex to an antidiagonal factor. -/
noncomputable def πProductTotal (p q n : ℤ) (h : p + q = n) :
    (K.productTotal).X n ⟶ (K.X p).X q :=
  productπ K p q n h

/-- The component formula for the product total differential, including the column sign. -/
@[reassoc (attr := simp)]
lemma productTotal_d_π (n p q : ℤ) (h : p + q = n + 1) :
    K.productTotal.d n (n + 1) ≫ K.πProductTotal p q (n + 1) h =
      K.πProductTotal (p - 1) q n (by omega) ≫ (K.d (p - 1) p).f q +
        p.negOnePow • (K.πProductTotal p (q - 1) n (by omega) ≫
          (K.X p).d (q - 1) q) := by
  dsimp [productTotal, πProductTotal]
  rw [CochainComplex.of_d]
  exact productD_π K n p q h

/-- Maps into a product-total term are determined by the antidiagonal projections. -/
@[ext]
lemma productTotal_hom_ext {n : ℤ} {A : C} {f g : A ⟶ K.productTotal.X n}
    (h : ∀ p q (hpq : p + q = n),
      f ≫ K.πProductTotal p q n hpq = g ≫ K.πProductTotal p q n hpq) : f = g := by
  dsimp [productTotal, πProductTotal] at h ⊢
  exact Pi.hom_ext _ _ (fun ⟨⟨p, q⟩, hpq⟩ => h p q hpq)

/-- Assemble a map into a product-total term from its components. -/
noncomputable def productTotalLift {A : C} (n : ℤ)
    (f : ∀ p q, p + q = n → (A ⟶ (K.X p).X q)) : A ⟶ K.productTotal.X n :=
  Pi.lift (f := fun i : {pq : ℤ × ℤ // pq.1 + pq.2 = n} =>
    (K.X i.1.1).X i.1.2) fun i => f i.1.1 i.1.2 i.2

@[reassoc (attr := simp)]
lemma productTotalLift_π {A : C} (n : ℤ)
    (f : ∀ p q, p + q = n → (A ⟶ (K.X p).X q)) (p q : ℤ) (h : p + q = n) :
    K.productTotalLift n f ≫ K.πProductTotal p q n h = f p q h := by
  dsimp [productTotalLift, πProductTotal, productTotal, productπ]
  exact Pi.lift_comp_π _ _

/-- A chain map into a product total complex is determined by all its projections. -/
lemma productTotal_chainMap_ext {A : CochainComplex C ℤ} {f g : A ⟶ K.productTotal}
    (h : ∀ n p q (hpq : p + q = n),
      f.f n ≫ K.πProductTotal p q n hpq = g.f n ≫ K.πProductTotal p q n hpq) : f = g := by
  apply HomologicalComplex.hom_ext
  intro n
  exact K.productTotal_hom_ext (h n)

/-- Construct a chain map into the product total complex from components satisfying
its signed differential formula. -/
noncomputable def mkHomProductTotal (A : CochainComplex C ℤ)
    (f : ∀ n p q, p + q = n → (A.X n ⟶ (K.X p).X q))
    (comm : ∀ n p q (h : p + q = n + 1),
      A.d n (n + 1) ≫ f (n + 1) p q h =
        f n (p - 1) q (by omega) ≫ (K.d (p - 1) p).f q +
          p.negOnePow • (f n p (q - 1) (by omega) ≫ (K.X p).d (q - 1) q)) :
    A ⟶ K.productTotal :=
  CochainComplex.ofHom (fun n => K.productTotalLift n (f n)) (fun n => by
    apply K.productTotal_hom_ext
    intro p q h
    simpa [comp_add, Linear.comp_units_smul] using (comm n p q h).symm)

@[reassoc (attr := simp)]
lemma mkHomProductTotal_f_π (A : CochainComplex C ℤ)
    (f : ∀ n p q, p + q = n → (A.X n ⟶ (K.X p).X q))
    (comm : ∀ n p q (h : p + q = n + 1),
      A.d n (n + 1) ≫ f (n + 1) p q h =
        f n (p - 1) q (by omega) ≫ (K.d (p - 1) p).f q +
          p.negOnePow • (f n p (q - 1) (by omega) ≫ (K.X p).d (q - 1) q))
    (n p q : ℤ) (h : p + q = n) :
    (K.mkHomProductTotal A f comm).f n ≫ K.πProductTotal p q n h = f n p q h := by
  simp [mkHomProductTotal]

namespace productTotal

variable {K} {L M : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
  [L.HasProductTotal] [M.HasProductTotal]

/-- The map on product totals induced by a morphism of double complexes. -/
noncomputable def map (f : K ⟶ L) : K.productTotal ⟶ L.productTotal :=
  L.mkHomProductTotal K.productTotal
    (fun n p q h => K.πProductTotal p q n h ≫ (f.f p).f q)
    (by
      intro n p q h
      simp [Linear.units_smul_comp, comm_f, HomologicalComplex.Hom.comm])

@[reassoc (attr := simp)]
lemma map_f_π (f : K ⟶ L) (n p q : ℤ) (h : p + q = n) :
    (map f).f n ≫ L.πProductTotal p q n h =
      K.πProductTotal p q n h ≫ (f.f p).f q := by
  simp [map]

@[simp]
lemma map_id : map (𝟙 K) = 𝟙 K.productTotal := by
  apply K.productTotal_chainMap_ext
  intros
  simp

@[simp]
lemma map_comp (f : K ⟶ L) (g : L ⟶ M) : map (f ≫ g) = map f ≫ map g := by
  apply M.productTotal_chainMap_ext
  intros
  simp

@[simp]
lemma map_add (f g : K ⟶ L) : map (f + g) = map f + map g := by
  apply L.productTotal_chainMap_ext
  intros
  simp [comp_add, add_comp]

end productTotal

variable [∀ K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ),
  K.HasProductTotal]

/-- Product totalisation as an additive functor, when all antidiagonal products exist.
The functor is exposed so its object types reduce in statements about morphisms. -/
@[expose, simps]
noncomputable def productTotalFunctor :
    HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⥤ CochainComplex C ℤ where
  obj K := K.productTotal
  map f := productTotal.map f
  map_id _ := productTotal.map_id
  map_comp _ _ := productTotal.map_comp _ _

instance : (productTotalFunctor (C := C)).Additive where
  map_add {_ _ f g} := productTotal.map_add f g

end HomologicalComplex₂
