/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.VertexOperator
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Normal ordering of fields

The normal-ordered product places negative modes of the first field on the left and
nonnegative modes on the right. For fields `A` and `B`, its normalized coefficients are

`(:AB:)[[n]] v = ∑ᶠ i : ℕ, A[[-i-1]] (B[[n+i]] v) +
                 ∑ᶠ i : ℕ, B[[n-i-1]] (A[[i]] v)`.

Both sums are finite on each vector, though generally not finite as sums of endomorphisms.
We prove that these coefficients again define a field, without assuming mutual locality.
This is the binary operation needed to form quadratic current fields.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §2.3, for normal ordering.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.4.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset

namespace VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

private theorem support_normalOrder_left_subset (A B : VertexOperator R V) (n : ℤ) (v : V)
    {P : ℕ} (hP : ∀ i : ℕ, P ≤ i → (B[[n + i]]) v = 0) :
    (Function.support fun i : ℕ ↦ (A[[-(i : ℤ) - 1]]) ((B[[n + i]]) v)) ⊆ range P := by
  intro i hi
  simp only [mem_coe, mem_range]
  by_contra! h
  exact hi (by simp only [hP i h, map_zero])

private theorem support_normalOrder_right_subset (A B : VertexOperator R V) (n : ℤ) (v : V)
    {Q : ℕ} (hQ : ∀ i : ℕ, Q ≤ i → (A[[(i : ℤ)]]) v = 0) :
    (Function.support fun i : ℕ ↦ (B[[n - i - 1]]) ((A[[(i : ℤ)]]) v)) ⊆ range Q := by
  intro i hi
  simp only [mem_coe, mem_range]
  by_contra! h
  exact hi (by simp only [hQ i h, map_zero])

private theorem finite_support_normalOrder_left (A B : VertexOperator R V) (n : ℤ) (v : V) :
    (Function.support fun i : ℕ ↦ (A[[-(i : ℤ) - 1]]) ((B[[n + i]]) v)).Finite := by
  obtain ⟨N, hN⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  exact (finite_toSet (range (N + n.natAbs))).subset
    (support_normalOrder_left_subset A B n v (fun i hi ↦ hN _ (by omega)))

private theorem finite_support_normalOrder_right (A B : VertexOperator R V) (n : ℤ) (v : V) :
    (Function.support fun i : ℕ ↦ (B[[n - i - 1]]) ((A[[(i : ℤ)]]) v)).Finite := by
  obtain ⟨N, hN⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  exact (finite_toSet (range N)).subset
    (support_normalOrder_right_subset A B n v (fun i hi ↦ hN _ (by omega)))

private theorem normalOrder_sums_add (A B C D : VertexOperator R V) (n : ℤ) (v w : V) :
    (∑ᶠ i : ℕ, ((A[[-(i : ℤ) - 1]]) ((B[[n + i]]) v) +
      (C[[-(i : ℤ) - 1]]) ((D[[n + i]]) w))) +
      (∑ᶠ i : ℕ, ((B[[n - i - 1]]) ((A[[(i : ℤ)]]) v) +
        (D[[n - i - 1]]) ((C[[(i : ℤ)]]) w))) =
    ((∑ᶠ i : ℕ, (A[[-(i : ℤ) - 1]]) ((B[[n + i]]) v)) +
      ∑ᶠ i : ℕ, (B[[n - i - 1]]) ((A[[(i : ℤ)]]) v)) +
    ((∑ᶠ i : ℕ, (C[[-(i : ℤ) - 1]]) ((D[[n + i]]) w)) +
      ∑ᶠ i : ℕ, (D[[n - i - 1]]) ((C[[(i : ℤ)]]) w)) := by
  rw [finsum_add_distrib (finite_support_normalOrder_left A B n v)
    (finite_support_normalOrder_left C D n w),
    finsum_add_distrib (finite_support_normalOrder_right A B n v)
    (finite_support_normalOrder_right C D n w)]
  abel

private theorem normalOrder_sums_smul (r : R) (A B : VertexOperator R V) (n : ℤ) (v : V) :
    (∑ᶠ i : ℕ, r • (A[[-(i : ℤ) - 1]]) ((B[[n + i]]) v)) +
      (∑ᶠ i : ℕ, r • (B[[n - i - 1]]) ((A[[(i : ℤ)]]) v)) =
    r • ((∑ᶠ i : ℕ, (A[[-(i : ℤ) - 1]]) ((B[[n + i]]) v)) +
      ∑ᶠ i : ℕ, (B[[n - i - 1]]) ((A[[(i : ℤ)]]) v)) := by
  rw [← smul_finsum' r (finite_support_normalOrder_left A B n v),
    ← smul_finsum' r (finite_support_normalOrder_right A B n v), smul_add]

/-- The normalized coefficient of the normal-ordered product. The sums are finite on each
vector, with negative modes of `A` on the left and nonnegative modes of `A` on the right. -/
def normalOrderCoeff (A B : VertexOperator R V) (n : ℤ) : Module.End R V where
  toFun v := (∑ᶠ i : ℕ, (A[[-(i : ℤ) - 1]]) ((B[[n + i]]) v)) +
    ∑ᶠ i : ℕ, (B[[n - i - 1]]) ((A[[(i : ℤ)]]) v)
  map_add' v w := by
    simpa only [map_add] using normalOrder_sums_add A B A B n v w
  map_smul' r v := by
    simpa only [map_smul, RingHom.id_apply] using normalOrder_sums_smul r A B n v

/-- The two pointwise finite sums defining a normal-ordered coefficient. -/
@[simp]
theorem normalOrderCoeff_apply (A B : VertexOperator R V) (n : ℤ) (v : V) :
    normalOrderCoeff A B n v =
      (∑ᶠ i : ℕ, (A[[-(i : ℤ) - 1]]) ((B[[n + i]]) v)) +
        ∑ᶠ i : ℕ, (B[[n - i - 1]]) ((A[[(i : ℤ)]]) v) := (rfl)

/-- Cutoffs for `B` on `v` and for `A` on `v` turn normal ordering into two explicit finite
sums. The first cutoff controls `B[[n+i]] v`; the second controls `A[[i]] v`. -/
theorem normalOrderCoeff_eq_sum (A B : VertexOperator R V) (n : ℤ) (v : V)
    {P Q : ℕ} (hP : ∀ i : ℕ, P ≤ i → (B[[n + i]]) v = 0)
    (hQ : ∀ i : ℕ, Q ≤ i → (A[[(i : ℤ)]]) v = 0) :
    normalOrderCoeff A B n v =
      (∑ i ∈ range P, (A[[-(i : ℤ) - 1]]) ((B[[n + i]]) v)) +
        ∑ i ∈ range Q, (B[[n - i - 1]]) ((A[[(i : ℤ)]]) v) := by
  rw [normalOrderCoeff_apply]
  rw [finsum_eq_sum_of_support_subset _ (support_normalOrder_left_subset A B n v hP),
    finsum_eq_sum_of_support_subset _ (support_normalOrder_right_subset A B n v hQ)]

/-- Normal-ordered coefficients kill each vector in all sufficiently high degrees. -/
private theorem exists_forall_normalOrderCoeff_eq_zero (A B : VertexOperator R V) (v : V) :
    ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ n → normalOrderCoeff A B n v = 0 := by
  obtain ⟨P, hP⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q, hQ⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  choose C hC using fun i : ℕ ↦ B.exists_forall_ncoeff_apply_eq_zero ((A[[(i : ℤ)]]) v)
  refine ⟨max P (Q + ∑ i ∈ range Q, C i), fun n hn ↦ ?_⟩
  rw [normalOrderCoeff_eq_sum A B n v (P := 0) (Q := Q)
    (fun i _ ↦ hP _ (by omega)) (fun i hi ↦ hQ _ (by omega))]
  simp only [range_zero, sum_empty, zero_add]
  apply sum_eq_zero
  intro i hi
  apply hC i
  have := single_le_sum (f := C) (fun j _ ↦ Nat.zero_le (C j)) hi
  have := mem_range.1 hi
  omega

/-- The normal-ordered product of two fields, placing negative modes of the first field on
the left and its nonnegative modes on the right. No locality assumption is required. -/
def normalOrder (A B : VertexOperator R V) : VertexOperator R V :=
  of_coeff (fun k ↦ normalOrderCoeff A B (-k - 1)) fun v ↦ by
    obtain ⟨N, hN⟩ := exists_forall_normalOrderCoeff_eq_zero A B v
    refine ⟨-(N : ℤ), fun k hk ↦ ?_⟩
    by_contra! h
    exact hk (hN _ (by omega))

/-- The normalized coefficients of the normal-ordered product. -/
@[simp]
theorem ncoeff_normalOrder (A B : VertexOperator R V) (n : ℤ) :
    (normalOrder A B)[[n]] = normalOrderCoeff A B n := by
  simp [normalOrder]

/-- Normal-ordered coefficients are additive in the first field. -/
@[simp]
theorem normalOrderCoeff_add_left (A B C : VertexOperator R V) (n : ℤ) :
    normalOrderCoeff (A + B) C n = normalOrderCoeff A C n + normalOrderCoeff B C n := by
  ext v
  simpa only [map_add, Pi.add_apply, LinearMap.add_apply, normalOrderCoeff_apply] using
    normalOrder_sums_add A C B C n v v

/-- Normal-ordered coefficients are additive in the second field. -/
@[simp]
theorem normalOrderCoeff_add_right (A B C : VertexOperator R V) (n : ℤ) :
    normalOrderCoeff A (B + C) n = normalOrderCoeff A B n + normalOrderCoeff A C n := by
  ext v
  simpa only [map_add, Pi.add_apply, LinearMap.add_apply, normalOrderCoeff_apply] using
    normalOrder_sums_add A B A C n v v

/-- Normal-ordered coefficients respect scalar multiplication in the first field. -/
@[simp]
theorem normalOrderCoeff_smul_left (r : R) (A B : VertexOperator R V) (n : ℤ) :
    normalOrderCoeff (r • A) B n = r • normalOrderCoeff A B n := by
  ext v
  simpa only [map_smul, Pi.smul_apply, LinearMap.smul_apply, normalOrderCoeff_apply] using
    normalOrder_sums_smul r A B n v

/-- Normal-ordered coefficients respect scalar multiplication in the second field. -/
@[simp]
theorem normalOrderCoeff_smul_right (r : R) (A B : VertexOperator R V) (n : ℤ) :
    normalOrderCoeff A (r • B) n = r • normalOrderCoeff A B n := by
  ext v
  simpa only [map_smul, Pi.smul_apply, LinearMap.smul_apply, normalOrderCoeff_apply] using
    normalOrder_sums_smul r A B n v

/-- Normal ordering is additive in the first field. -/
@[simp]
theorem normalOrder_add_left (A B C : VertexOperator R V) :
    normalOrder (A + B) C = normalOrder A C + normalOrder B C := by
  apply ext_ncoeff
  intro n
  simp

/-- Normal ordering is additive in the second field. -/
@[simp]
theorem normalOrder_add_right (A B C : VertexOperator R V) :
    normalOrder A (B + C) = normalOrder A B + normalOrder A C := by
  apply ext_ncoeff
  intro n
  simp

/-- Normal ordering is coefficient-linear in the first field. -/
@[simp]
theorem normalOrder_smul_left (r : R) (A B : VertexOperator R V) :
    normalOrder (r • A) B = r • normalOrder A B := by
  apply ext_ncoeff
  intro n
  simp

/-- Normal ordering is coefficient-linear in the second field. -/
@[simp]
theorem normalOrder_smul_right (r : R) (A B : VertexOperator R V) :
    normalOrder A (r • B) = r • normalOrder A B := by
  apply ext_ncoeff
  intro n
  simp

/-- Normal ordering as a bilinear map on fields. -/
def normalOrderₗ : VertexOperator R V →ₗ[R] VertexOperator R V →ₗ[R] VertexOperator R V where
  toFun A :=
    { toFun := normalOrder A
      map_add' := normalOrder_add_right A
      map_smul' := fun r B ↦ normalOrder_smul_right r A B }
  map_add' A B := LinearMap.ext fun C ↦ normalOrder_add_left A B C
  map_smul' r A := LinearMap.ext fun B ↦ normalOrder_smul_left r A B

/-- Applying the bundled normal-ordering map gives the normal-ordered product. -/
@[simp]
theorem normalOrderₗ_apply (A B : VertexOperator R V) :
    normalOrderₗ A B = normalOrder A B := (rfl)

@[simp]
theorem normalOrder_zero_left (B : VertexOperator R V) : normalOrder 0 B = 0 :=
  LinearMap.map_zero₂ normalOrderₗ B

@[simp]
theorem normalOrder_zero_right (A : VertexOperator R V) : normalOrder A 0 = 0 :=
  map_zero (normalOrderₗ A)

@[simp]
theorem normalOrder_neg_left (A B : VertexOperator R V) :
    normalOrder (-A) B = -normalOrder A B :=
  LinearMap.map_neg₂ normalOrderₗ A B

@[simp]
theorem normalOrder_neg_right (A B : VertexOperator R V) :
    normalOrder A (-B) = -normalOrder A B :=
  map_neg (normalOrderₗ A) B

@[simp]
theorem normalOrder_sub_left (A B C : VertexOperator R V) :
    normalOrder (A - B) C = normalOrder A C - normalOrder B C :=
  LinearMap.map_sub₂ normalOrderₗ A B C

@[simp]
theorem normalOrder_sub_right (A B C : VertexOperator R V) :
    normalOrder A (B - C) = normalOrder A B - normalOrder A C :=
  map_sub (normalOrderₗ A) B C

/-- Normal ordering distributes over finite sums in the first field. -/
@[simp]
theorem normalOrder_sum_left {ι : Type*} (s : Finset ι) (A : ι → VertexOperator R V)
    (B : VertexOperator R V) :
    normalOrder (∑ i ∈ s, A i) B = ∑ i ∈ s, normalOrder (A i) B :=
  LinearMap.map_sum₂ normalOrderₗ s A B

/-- Normal ordering distributes over finite sums in the second field. -/
@[simp]
theorem normalOrder_sum_right {ι : Type*} (A : VertexOperator R V) (s : Finset ι)
    (B : ι → VertexOperator R V) :
    normalOrder A (∑ i ∈ s, B i) = ∑ i ∈ s, normalOrder A (B i) :=
  map_sum (normalOrderₗ A) B s

end VertexOperator
