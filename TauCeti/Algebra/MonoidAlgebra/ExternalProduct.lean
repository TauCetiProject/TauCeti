/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.BigOperators.Ring.Finset
import TauCeti.Algebra.MonoidAlgebra.Basic

/-!
# External products in finite group algebras

The external product of elements in a finite family of group algebras lies in the group algebra
of the product group. Its coefficients are products of the local coefficients. This extends the
binary coefficient formula `MonoidAlgebra.coeff_tensorEquiv_tmul` to a finite family and is
compatible with convolution.
-/

public section

open scoped BigOperators

namespace MonoidAlgebra

variable {R ι : Type*} {G : ι → Type*} [CommSemiring R] [Fintype ι] [∀ i, Fintype (G i)]

/-- The external product in the group algebra of the product group, with one factor at each
index. Its coefficient at a tuple is the product of the coefficients at its coordinates. -/
noncomputable def externalProduct (a : ∀ i, MonoidAlgebra R (G i)) :
    MonoidAlgebra R (∀ i, G i) := by
  classical
  exact ofCoeff (Finsupp.equivFunOnFinite.symm fun g ↦ ∏ i, (a i).coeff (g i))

/-- Evaluate the external product at a tuple of group elements. -/
@[simp] theorem coeff_externalProduct (a : ∀ i, MonoidAlgebra R (G i)) (g : ∀ i, G i) :
    (externalProduct a).coeff g = ∏ i, (a i).coeff (g i) := by
  classical
  simp [externalProduct, coeff_ofCoeff]

/-- The external product of single terms is the single term at the tuple of their positions. -/
@[simp] theorem externalProduct_single (g : ∀ i, G i) (a : ι → R) :
    externalProduct (fun i ↦ single (g i) (a i)) = single g (∏ i, a i) := by
  classical
  ext h
  rw [coeff_externalProduct]
  by_cases hh : g = h
  · subst h
    simp
  · obtain ⟨i, hi⟩ : ∃ i, g i ≠ h i := by simpa [funext_iff] using hh
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    simp [hh]

/-- The external product of the local identities is the identity of the product monoid algebra. -/
@[simp] theorem externalProduct_one [∀ i, One (G i)] :
    externalProduct (fun i ↦ (1 : MonoidAlgebra R (G i))) = 1 := by
  simpa only [Pi.one_apply, ← one_def, Finset.prod_const_one] using
    (externalProduct_single (R := R) (1 : ∀ i, G i) (fun _ ↦ 1))

/-- A vanishing factor makes an external product vanish. -/
theorem externalProduct_eq_zero_of (a : ∀ i, MonoidAlgebra R (G i)) (i : ι) (hi : a i = 0) :
    externalProduct a = 0 := by
  ext g
  rw [coeff_externalProduct, coeff_zero]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

section Group

variable [∀ i, Group (G i)]

/-- Convolution of external products is the external product of the local convolutions. -/
@[simp] theorem externalProduct_mul (a b : ∀ i, MonoidAlgebra R (G i)) :
    externalProduct (fun i ↦ a i * b i) = externalProduct a * externalProduct b := by
  classical
  ext g
  rw [coeff_externalProduct, coeff_mul_eq_sum]
  simp only [coeff_mul_eq_sum, coeff_externalProduct, ← Finset.prod_mul_distrib,
    Pi.mul_apply, Pi.inv_apply]
  exact Fintype.prod_sum _

/-- The external product of central elements is central. -/
theorem externalProduct_mem_center (a : ∀ i, MonoidAlgebra R (G i))
    (ha : ∀ i, a i ∈ Subalgebra.center R (MonoidAlgebra R (G i))) :
    externalProduct a ∈ Subalgebra.center R (MonoidAlgebra R (∀ i, G i)) := by
  rw [Subalgebra.mem_center_iff]
  intro x
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  | single g r =>
    -- Put the scalar on the whole basis element, not in every factor.
    rw [← smul_of, smul_mul_assoc, mul_smul_comm, of_apply]
    congr 1
    have hsingle : externalProduct (fun i ↦ single (g i) (1 : R)) = single g 1 := by
      simpa only [Finset.prod_const_one] using externalProduct_single g (fun _ ↦ (1 : R))
    simp only [← hsingle, ← externalProduct_mul]
    congr 1
    funext i
    exact Subalgebra.mem_center_iff.mp (ha i) _

/-- Products of local orthogonal idempotents form an orthogonal family indexed by tuples. -/
theorem orthogonalIdempotents_externalProduct {J : ι → Type*}
    {e : ∀ i, J i → MonoidAlgebra R (G i)} (he : ∀ i, OrthogonalIdempotents (e i)) :
    OrthogonalIdempotents (fun j : ∀ i, J i ↦ externalProduct (fun i ↦ e i (j i))) where
  idem j := by
    rw [IsIdempotentElem, ← externalProduct_mul]
    simp only [fun i ↦ ((he i).idem (j i)).eq]
  ortho j k hjk := by
    obtain ⟨i, hi⟩ : ∃ i, j i ≠ k i := by simpa [funext_iff] using hjk
    rw [← externalProduct_mul]
    exact externalProduct_eq_zero_of _ i ((he i).ortho hi)

end Group

end MonoidAlgebra
