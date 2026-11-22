/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Basic properties of derivations

A derivation vanishes on the image `(n : A)` of a natural number (`Derivation.map_natCast`). A
numeric literal `(OfNat.ofNat n : A)` with `2 ≤ n` is not syntactically such a cast, so `simp`
does not apply that lemma to it. This file adds the literal form `Derivation.map_ofNat`, so that
`simp` differentiates polynomial expressions with numeric coefficients, for instance partial
derivatives `MvPolynomial.pderiv i (3 * X 0 ^ 2)`.

A derivation differentiates a finite product termwise: `D (∏ i ∈ s, f i)` is the sum over
`j ∈ s` of `D (f j)` times the product of the other factors. In particular, a derivation `δ`
with `δ tⱼ = δᵢⱼ` sends a monomial `∏ⱼ tⱼ ^ βⱼ` to `βᵢ ∏ⱼ tⱼ ^ (β - eᵢ)ⱼ`.

Iterates of a derivation remain linear over the scalars, so they commute with finite scalar
linear combinations. On products they satisfy the general Leibniz rule
`Dⁿ (a * b) = ∑ (n choose i) Dⁱ a Dⁿ⁻ⁱ b`.

The derivative of the total inverse `Ring.inverse a` is `-(Ring.inverse a) ^ 2 • D a`, as for
`⅟a`; for instance a derivation kills the inverse of every invertible natural number. Hence, if
`D x = 1`, the divided power `x ^ (j + 1) / (j + 1)!` differentiates to `x ^ j / j!` whenever
`(j + 1)!` is a unit.

An element whose derivative is a unit is squarefree, since a square factor `x * x` of `a` makes
`x` divide `D a`. This detects squarefreeness of a polynomial from a partial derivative that is a
unit, without factoring it.

A derivation over any scalars `S` which vanishes on the image of `R` is `R`-linear
(`Derivation.ofMapAlgebraMap`). An `R`-algebra isomorphism `e : A ≃ₐ[R] B` transports a derivation
`D` of `A` to the derivation `e ∘ D ∘ e⁻¹` of `B` (`Derivation.conjAlgEquiv`).

## Main results

* `Derivation.map_ofNat`: a derivation vanishes on numeric literals.
* `Derivation.leibniz_prod`: the Leibniz rule for finite products.
* `Derivation.apply_prod_pow_of_apply_eq`: a derivation dual to the `i`-th coordinate
  differentiates a monomial in the coordinates by lowering its `i`-th exponent.
* `Derivation.iterate_sum_smul`: iterated differentiation commutes with scalar linear combinations.
* `Derivation.iterate_apply_mul`: the general Leibniz rule for iterates of a derivation.
* `Derivation.iterate_smul_apply`: iterates of scalar multiples of a derivation.
* `Derivation.exists_iterate_smul_eq_zero`: scalar multiples preserve local nilpotence.
* `Derivation.leibniz_ringInverse`: the derivative of `Ring.inverse a`.
* `Derivation.leibniz_ringInverse_factorial_mul_pow_succ`: the derivative of the divided power
  `x ^ (j + 1) / (j + 1)!` when `D x = 1`.
* `Derivation.squarefree_of_isUnit`: an element whose derivative is a unit is squarefree.
* `Derivation.ofMapAlgebraMap`: a derivation killing the image of `R` as an `R`-derivation.
* `Derivation.conjAlgEquiv`: a derivation transported along an algebra isomorphism.
* `Derivation.hochschildCoeff`: recursive coefficients in the triangular expansion of `(a • D)^[n]`.
* `Derivation.iterate_smul_eq_sum_hochschildCoeff`: triangular expansion of `(f a • E)^[n]`.
-/

public section

namespace Derivation

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [AddCommMonoid M] [Algebra R A]
  [Module A M] [Module R M] (D : Derivation R A M)

/-- A derivation vanishes on numeric literals. -/
@[simp]
theorem map_ofNat (n : ℕ) [n.AtLeastTwo] : D (no_index (OfNat.ofNat n : A)) = 0 := by
  rw [← Nat.cast_ofNat, map_natCast]

/-- **Leibniz rule for finite products**: `D (∏ i ∈ s, f i)` is the sum over `j ∈ s` of
`D (f j)` times the product of the other factors. -/
theorem leibniz_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → A) :
    D (∏ i ∈ s, f i) = ∑ j ∈ s, (∏ i ∈ s.erase j, f i) • D (f j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, leibniz, ih, Finset.sum_insert ha, Finset.erase_insert ha,
      Finset.smul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hj ha).symm,
      Finset.prod_insert fun h => ha (Finset.mem_of_mem_erase h), smul_smul]

/-- A derivation dual to the `i`-th coordinate differentiates a monomial `∏ⱼ tⱼ ^ βⱼ` in the
coordinates to `βᵢ ∏ⱼ tⱼ ^ (β - eᵢ)ⱼ`. -/
theorem apply_prod_pow_of_apply_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (δ : Derivation R A A) {t : ι → A} {i : ι} (ht : ∀ j, δ (t j) = if j = i then 1 else 0)
    (β : ι → ℕ) :
    δ (∏ j, t j ^ β j) = β i • ∏ j, t j ^ (β - Pi.single i 1 : ι → ℕ) j := by
  have hrest : δ (∏ j ∈ Finset.univ.erase i, t j ^ β j) = 0 :=
    Finset.prod_induction _ (fun a ↦ δ a = 0) (fun a b ha hb ↦ by simp [leibniz, ha, hb])
      (by simp) fun j hj ↦ by simp [leibniz_pow, ht, Finset.ne_of_mem_erase hj]
  have hcongr : ∏ j ∈ Finset.univ.erase i, t j ^ (β - Pi.single i 1 : ι → ℕ) j =
      ∏ j ∈ Finset.univ.erase i, t j ^ β j :=
    Finset.prod_congr rfl fun j hj ↦ by simp [Finset.ne_of_mem_erase hj]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), hcongr, leibniz, hrest,
    leibniz_pow, ht]
  simp only [ite_true, smul_eq_mul, mul_one, nsmul_eq_mul, Pi.sub_apply,
    Pi.single_eq_same]
  ring

/-- Iterated differentiation commutes with finite scalar linear combinations. -/
theorem iterate_sum_smul {ι : Type*} (D : Derivation R A A) (m : ℕ) (s : Finset ι)
    (c : ι → R) (f : ι → A) :
    (D : A → A)^[m] (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • (D : A → A)^[m] (f i) := by
  have h := map_sum (D.toLinearMap ^ m) (fun i ↦ c i • f i) s
  simp only [LinearMap.map_smul] at h
  simpa only [pow_apply_eq_iterate, coeFn_coe] using h

/-- **General Leibniz rule** for iterates of a derivation of a commutative algebra.

The statement and proof are adapted from Mathlib's `LieDerivation.iterate_apply_lie`
(`Mathlib/Algebra/Lie/Derivation/Basic.lean`). -/
theorem iterate_apply_mul (D : Derivation R A A) (n : ℕ) (a b : A) :
    D^[n] (a * b) =
      ∑ ij ∈ Finset.antidiagonal n, n.choose ij.1 • (D^[ij.1] a * D^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul (M := A) (fun i j => D^[i] a * D^[j] b) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, leibniz, smul_eq_mul,
      nsmul_add, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [n.choose_symm_of_eq_add (Finset.mem_antidiagonal.1 hij).symm, mul_comm]

/-- Iterating a scalar multiple of a derivation scales its iterates by the corresponding power. -/
theorem iterate_smul_apply (D : Derivation R A A) (r : R) (n : ℕ) (a : A) :
    (r • D)^[n] a = r ^ n • D^[n] a := by
  simpa [_root_.pow_apply_eq_iterate, coeFn_coe] using
    LinearMap.congr_fun (smul_pow r D.toLinearMap n) a

/-- Scalar multiples of a locally nilpotent derivation are locally nilpotent. -/
theorem exists_iterate_smul_eq_zero (D : Derivation R A A)
    (hD : ∀ a, ∃ n, D^[n] a = 0) (r : R) (a : A) : ∃ n, (r • D)^[n] a = 0 := by
  obtain ⟨n, hn⟩ := hD a
  exact ⟨n, by rw [iterate_smul_apply, hn, smul_zero]⟩

/-- An element whose derivative is a unit is squarefree: if `a = x * x * y`, then `x` divides
`D a = x * D (x * y) + x * y * D x`. -/
theorem squarefree_of_isUnit (D : Derivation R A A) {a : A} (ha : IsUnit (D a)) :
    Squarefree a := by
  rintro x ⟨y, rfl⟩
  refine isUnit_of_dvd_unit ?_ ha
  rw [mul_assoc, leibniz, smul_eq_mul, smul_eq_mul]
  exact dvd_add (dvd_mul_right x _) (dvd_mul_of_dvd_left (dvd_mul_right x y) _)

section Ring

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module A M]
  [Module R M]

/-- The derivative of the ring inverse: `D (Ring.inverse a) = -(Ring.inverse a) ^ 2 • D a`, the
form of `Derivation.leibniz_invOf` for the total inverse. When `a` is not a unit, both sides
vanish. -/
theorem leibniz_ringInverse (D : Derivation R A M) (a : A) :
    D (Ring.inverse a) = -Ring.inverse a ^ 2 • D a := by
  by_cases ha : IsUnit a
  · exact D.leibniz_of_mul_eq_one (Ring.inverse_mul_cancel a ha)
  · simp [Ring.inverse_non_unit a ha]

open scoped Nat in
/-- If `D x = 1` and `(j + 1)!` is a unit, the derivative of the divided power
`x ^ (j + 1) / (j + 1)!` is `x ^ j / j!`. -/
theorem leibniz_ringInverse_factorial_mul_pow_succ (D : Derivation R A A) {x : A} (hx : D x = 1)
    {j : ℕ} (hj : IsUnit ((j + 1)! : A)) :
    D (Ring.inverse ((j + 1)! : A) * x ^ (j + 1)) = Ring.inverse (j ! : A) * x ^ j := by
  have hfac : ((j + 1)! : A) = (j + 1 : A) * j ! := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  have hj₁ : IsUnit (j + 1 : A) := isUnit_of_mul_isUnit_left (hfac ▸ hj)
  -- The constant `(j + 1)!⁻¹` has derivative zero, and `D (x ^ (j + 1)) = (j + 1) x ^ j`.
  calc D (Ring.inverse ((j + 1)! : A) * x ^ (j + 1))
      = Ring.inverse ((j + 1)! : A) * ((j + 1 : A) * x ^ j) := by
        simp [leibniz_ringInverse, leibniz_pow, hx, mul_comm]
    _ = Ring.inverse (j ! : A) * x ^ j := by
        rw [hfac, Ring.inverse_mul (.inl hj₁), mul_assoc, Ring.inverse_mul_cancel_left _ _ hj₁]

end Ring

end Derivation

namespace Derivation

section Rescale

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- Recursive coefficients `P n k` in the triangular expansion
`((a • D)^[n]) y = ∑ k ∈ Finset.range (n + 1), P n k * D^[k] y` over any commutative semiring. -/
def hochschildCoeff (D : Derivation R A A) (a : A) : ℕ → ℕ → A
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => a * D (hochschildCoeff D a n (k + 1)) + a * hochschildCoeff D a n k

/-- `hochschildCoeff D a n k` vanishes whenever `n < k`. -/
theorem hochschildCoeff_eq_zero_of_lt (D : Derivation R A A) (a : A) :
    ∀ {n k : ℕ}, n < k → hochschildCoeff D a n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    have h1 : n < k + 1 := Nat.lt_trans (Nat.lt_of_succ_lt_succ h) (Nat.lt_succ_self k)
    have h2 : n < k := Nat.lt_of_succ_lt_succ h
    simp [hochschildCoeff, hochschildCoeff_eq_zero_of_lt D a h1,
      hochschildCoeff_eq_zero_of_lt D a h2]

/-- The diagonal Hochschild coefficient `hochschildCoeff D a n n` equals `a ^ n`. -/
@[simp]
theorem hochschildCoeff_self (D : Derivation R A A) (a : A) :
    ∀ n : ℕ, hochschildCoeff D a n n = a ^ n
  | 0 => (pow_zero a).symm
  | n + 1 => by
    simp only [hochschildCoeff, hochschildCoeff_eq_zero_of_lt D a (Nat.lt_succ_self n),
      map_zero, mul_zero, zero_add, hochschildCoeff_self D a n, pow_succ']

/-- For `0 < n`, the zeroth Hochschild coefficient `hochschildCoeff D a n 0` vanishes. -/
theorem hochschildCoeff_zero_of_pos (D : Derivation R A A) (a : A) {n : ℕ} (hn : 0 < n) :
    hochschildCoeff D a n 0 = 0 := by
  cases n with
  | zero => omega
  | succ m => rfl

/-- The first-column Hochschild coefficient `hochschildCoeff D a (n + 1) 1` equals
`(⇑(a • D))^[n] a`. -/
theorem hochschildCoeff_one (D : Derivation R A A) (a : A) :
    ∀ n : ℕ, hochschildCoeff D a (n + 1) 1 = (⇑(a • D))^[n] a
  | 0 => by simp [hochschildCoeff]
  | n + 1 => by
    rw [hochschildCoeff, hochschildCoeff_zero_of_pos D a (Nat.succ_pos n), mul_zero, add_zero,
      hochschildCoeff_one D a n, Function.iterate_succ_apply', smul_apply, smul_eq_mul]

private theorem map_hochschildCoeff_zero (D : Derivation R A A) (a : A) (n : ℕ) :
    D (hochschildCoeff D a n 0) = 0 := by
  cases n with
  | zero => exact D.map_one_eq_zero
  | succ m => exact map_zero D

/-- Universal triangular expansion of `(f a • E)^[n] y` along any ring homomorphism
`f : A →+* B` and derivation `E : Derivation R B B` intertwining `D` via `f`. -/
theorem iterate_smul_eq_sum_hochschildCoeff {B : Type*} [CommSemiring B] [Algebra R B]
    (D : Derivation R A A) (E : Derivation R B B) (f : A →+* B)
    (hf : ∀ x : A, E (f x) = f (D x)) (a : A) :
    ∀ (n : ℕ) (y : B),
      (⇑(f a • E))^[n] y =
        ∑ k ∈ Finset.range (n + 1), f (hochschildCoeff D a n k) * E^[k] y
  | 0, y => by simp [hochschildCoeff]
  | n + 1, y => by
    rw [Function.iterate_succ_apply', iterate_smul_eq_sum_hochschildCoeff D E f hf a n y]
    rw [smul_apply, smul_eq_mul, map_sum, Finset.mul_sum]
    have hstep : ∀ k ∈ Finset.range (n + 1),
        f a * E (f (hochschildCoeff D a n k) * E^[k] y) =
          f (a * D (hochschildCoeff D a n k)) * E^[k] y +
            f (a * hochschildCoeff D a n k) * E^[k + 1] y := by
      intro k _
      rw [E.leibniz, smul_eq_mul, smul_eq_mul, hf, map_mul, map_mul, Function.iterate_succ_apply']
      ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
    have hsum1 : ∑ k ∈ Finset.range (n + 1),
          f (a * D (hochschildCoeff D a n k)) * E^[k] y =
        ∑ k ∈ Finset.range (n + 1),
          f (a * D (hochschildCoeff D a n (k + 1))) * E^[k + 1] y := by
      rw [Finset.sum_range_succ' (fun k => f (a * D (hochschildCoeff D a n k)) * E^[k] y) n,
        map_hochschildCoeff_zero, mul_zero, map_zero, zero_mul, add_zero]
      rw [Finset.sum_range_succ (fun k =>
        f (a * D (hochschildCoeff D a n (k + 1))) * E^[k + 1] y) n]
      rw [hochschildCoeff_eq_zero_of_lt D a (Nat.lt_succ_self n), map_zero, mul_zero, map_zero,
        zero_mul, add_zero]
    rw [hsum1, ← Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' (fun k => f (hochschildCoeff D a (n + 1) k) * E^[k] y) (n + 1)]
    rw [hochschildCoeff_zero_of_pos D a (Nat.succ_pos n), map_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hochschildCoeff, map_add, add_mul]

end Rescale

section OfMapAlgebraMap

variable {S R A M : Type*} [CommSemiring S] [CommSemiring R] [CommSemiring A] [AddCommMonoid M]
  [Algebra S A] [Algebra R A] [Module A M] [Module S M] [Module R M] [IsScalarTower R A M]

/-- A derivation over `S` that vanishes on the image of `R` is `R`-linear. -/
def ofMapAlgebraMap (D : Derivation S A M) (hD : ∀ r : R, D (algebraMap R A r) = 0) :
    Derivation R A M where
  toFun := D
  map_add' := D.map_add
  map_smul' r a := by
    rw [RingHom.id_apply, Algebra.smul_def, D.leibniz, hD, smul_zero, add_zero, algebraMap_smul]
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' := D.leibniz

@[simp]
theorem coe_ofMapAlgebraMap (D : Derivation S A M) (hD : ∀ r : R, D (algebraMap R A r) = 0) :
    ⇑(D.ofMapAlgebraMap hD) = D :=
  (rfl)

end OfMapAlgebraMap

section ConjAlgEquiv

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B] [Algebra R A]
  [Algebra R B]

/-- A derivation of `A` transported along an `R`-algebra isomorphism `e : A ≃ₐ[R] B`: the
derivation `e ∘ D ∘ e⁻¹` of `B`. -/
def conjAlgEquiv (D : Derivation R A A) (e : A ≃ₐ[R] B) : Derivation R B B where
  toLinearMap := (e.toLinearMap : A →ₗ[R] B) ∘ₗ D.toLinearMap ∘ₗ (e.symm.toLinearMap : B →ₗ[R] A)
  map_one_eq_zero' := by simp
  leibniz' x y := by simp [D.leibniz, smul_eq_mul]

@[simp]
theorem conjAlgEquiv_apply (D : Derivation R A A) (e : A ≃ₐ[R] B) (x : B) :
    D.conjAlgEquiv e x = e (D (e.symm x)) :=
  (rfl)

end ConjAlgEquiv

end Derivation
