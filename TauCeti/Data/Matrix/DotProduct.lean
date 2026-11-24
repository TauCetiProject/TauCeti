/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots

/-!
# Dot product lemmas

A nonnegative vector paired with strictly positive weights has dot product zero precisely when
the vector is zero.

Over an infinite integral domain, finitely many nonzero vectors are simultaneously paired
nontrivially with a single vector: no finite union of the hyperplanes `v ⬝ᵥ w = 0` covers the whole
space. The vector can be taken of the form `w i = M ^ e i` for a numbering `e` of the coordinates,
because `w ⬝ᵥ v` is then the value at `M` of a nonzero polynomial with coefficients `v`.

A ring homomorphism carries the bilinear form `v ⬝ᵥ A *ᵥ w` of a (possibly rectangular) matrix
to the form of the image matrix at the image vectors.

## Main results

* `RingHom.map_dotProduct_mulVec`: a ring homomorphism commutes with the bilinear form
  `v ⬝ᵥ A *ᵥ w`.
* `Matrix.intCast_dotProduct`: the dot product of the casts of integer vectors is the cast of their
  integer dot product.
* `Matrix.intCast_dotProduct_mulVec`: the form of the cast of an integer matrix, at the casts of
  integer vectors, is the cast of the integer value of the form.
* `TauCeti.dotProduct_eq_zero_iff_of_pos`: a nonnegative vector is zero if and only if its pairing
  with strictly positive weights vanishes.
* `Finset.exists_forall_dotProduct_ne_zero`: over an infinite domain, some vector has nonzero dot
  product with each of finitely many nonzero vectors.
-/

public section

open scoped Matrix

namespace RingHom

variable {m n R S : Type*} [Fintype m] [Fintype n] [NonAssocSemiring R] [NonAssocSemiring S]

/-- A ring homomorphism `f` carries the bilinear form `v ⬝ᵥ A *ᵥ w` of a matrix `A` to the form of
`A.map f` at `f ∘ v` and `f ∘ w`. -/
theorem map_dotProduct_mulVec (f : R →+* S) (A : Matrix m n R) (v : m → R) (w : n → R) :
    f (v ⬝ᵥ A *ᵥ w) = (f ∘ v) ⬝ᵥ A.map f *ᵥ (f ∘ w) := by
  simp only [f.map_dotProduct, Function.comp_def, f.map_mulVec]

end RingHom

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The dot product of the casts of integer vectors is the cast of their integer dot product. -/
theorem intCast_dotProduct {R : Type*} [NonAssocRing R] (v w : m → ℤ) :
    (fun i ↦ (v i : R)) ⬝ᵥ (fun i ↦ (w i : R)) = ((v ⬝ᵥ w : ℤ) : R) :=
  ((Int.castRingHom R).map_dotProduct v w).symm

/-- The form of the cast of an integer matrix, at the casts of integer vectors, is the cast of the
integer value of the form. -/
theorem intCast_dotProduct_mulVec {R : Type*} [NonAssocRing R] (A : Matrix m n ℤ) (v : m → ℤ)
    (w : n → ℤ) :
    (fun i ↦ (v i : R)) ⬝ᵥ A.map (Int.cast : ℤ → R) *ᵥ (fun i ↦ (w i : R)) =
      ((v ⬝ᵥ A *ᵥ w : ℤ) : R) :=
  ((Int.castRingHom R).map_dotProduct_mulVec A v w).symm

end Matrix

namespace TauCeti

/-- For a vector `c` of strictly positive weights and a nonnegative vector `x`, the pairing
`c ⬝ᵥ x` vanishes only when `x` does. -/
@[simp]
theorem dotProduct_eq_zero_iff_of_pos {ι R : Type*} [Fintype ι] [NonUnitalNonAssocSemiring R]
    [PartialOrder R] [IsOrderedAddMonoid R] [PosMulMono R] [NoZeroDivisors R]
    {c x : ι → R} (hc : ∀ i, 0 < c i) (hx : 0 ≤ x) :
    c ⬝ᵥ x = 0 ↔ x = 0 := by
  simp [dotProduct, Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ mul_nonneg (hc j).le (hx j),
    (hc _).ne', funext_iff]

end TauCeti

namespace Finset

open Polynomial in
/-- Over an infinite integral domain, for finitely many nonzero vectors `v` there is a vector `w`
with `w ⬝ᵥ v ≠ 0` for each of them. -/
theorem exists_forall_dotProduct_ne_zero {ι R : Type*} [Fintype ι] [CommRing R] [IsDomain R]
    [Infinite R] (V : Finset (ι → R)) (hV : ∀ v ∈ V, v ≠ 0) :
    ∃ w : ι → R, ∀ v ∈ V, w ⬝ᵥ v ≠ 0 := by
  classical
  -- Number the coordinates by `e`; then `(M ^ e ·) ⬝ᵥ v` is the value at `M` of the nonzero
  -- polynomial `P v` whose coefficients are the coordinates of `v`.
  let e := Fintype.equivFin ι
  let P : (ι → R) → R[X] := fun v => ofFn _ (v ∘ e.symm)
  have hP (v : ι → R) (M : R) : (P v).eval M = (fun i => M ^ (e i : ℕ)) ⬝ᵥ v := by
    simp only [P]
    rw [ofFn_eq_sum_monomial, eval_finsetSum, dotProduct, ← e.symm.sum_comp]
    simp [mul_comm]
  have hP0 (v : ι → R) (hv : v ≠ 0) : P v ≠ 0 := by
    intro h
    refine hv (funext fun i => ?_)
    simpa [P] using congrFun ((injective_ofFn _).eq_iff.1 (h.trans (map_zero _).symm)) (e i)
  obtain ⟨M, hM⟩ : ∃ M : R, (∏ v ∈ V, P v).eval M ≠ 0 := by
    by_contra! h
    exact Finset.prod_ne_zero_iff.2 (fun v hv => hP0 v (hV v hv))
      (Polynomial.funext fun M => by simpa using h M)
  rw [eval_prod, Finset.prod_ne_zero_iff] at hM
  exact ⟨fun i => M ^ (e i : ℕ), fun v hv => by rw [← hP]; exact hM v hv⟩

end Finset
