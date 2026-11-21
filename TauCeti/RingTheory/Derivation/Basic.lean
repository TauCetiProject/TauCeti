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
`Dⁿ (a * b) = ∑ (n choose i) Dⁱ a Dⁿ⁻ⁱ b`. The iterates of a multiple `b • D` by `b : A` are
combinations `(b • D)^[n] = ∑ k ≤ n, c n k * D^[k]` of the iterates of `D`, with coefficients
`c n k = smulIterCoeff D b n k` given by an explicit recursion; the coefficient of `D` in
`(b • D)^[n + 1]` is `(b • D)^[n] b`.

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
* `Derivation.iterate_apply_pow_of_apply_eq_one`: if `D x = 1`, then `D^[j] (x ^ k)` is the
  descending factorial `k (k - 1) ⋯ (k - j + 1)` times `x ^ (k - j)`.
* `Derivation.iterate_smul_apply`: iterates of scalar multiples of a derivation.
* `Derivation.exists_iterate_smul_eq_zero`: scalar multiples preserve local nilpotence.
* `Derivation.smulIterCoeff`: the coefficients of the expansion of `(b • D)^[n]`, `b : A`.
* `Derivation.iterate_smul_apply_eq_sum`: `(b • D)^[n]` as a combination of the `D^[k]`.
* `Derivation.smulIterCoeff_succ_one`: the coefficient of `D` in `(b • D)^[n + 1]`.
* `Derivation.map_smulIterCoeff`: the coefficients are natural in the ring.
* `Derivation.leibniz_ringInverse`: the derivative of `Ring.inverse a`.
* `Derivation.leibniz_ringInverse_factorial_mul_pow_succ`: the derivative of the divided power
  `x ^ (j + 1) / (j + 1)!` when `D x = 1`.
* `Derivation.squarefree_of_isUnit`: an element whose derivative is a unit is squarefree.
* `Derivation.ofMapAlgebraMap`: a derivation killing the image of `R` as an `R`-derivation.
* `Derivation.conjAlgEquiv`: a derivation transported along an algebra isomorphism.
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

/-- **Iterated derivatives of powers of a coordinate.** If `D x = 1`, then
`D^[j] (x ^ k)` is the descending factorial `k (k - 1) ⋯ (k - j + 1)` times `x ^ (k - j)`. In
particular `D^[k] (x ^ k) = k !`, and `D^[j] (x ^ k) = 0` for `j > k`. -/
theorem iterate_apply_pow_of_apply_eq_one (D : Derivation R A A) {x : A} (hx : D x = 1)
    (k j : ℕ) : D^[j] (x ^ k) = k.descFactorial j * x ^ (k - j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, leibniz, leibniz_pow, hx, map_natCast,
      Nat.descFactorial_succ, Nat.sub_sub]
    simp only [smul_eq_mul, nsmul_eq_mul, mul_one, mul_zero, add_zero, Nat.cast_mul]
    ring

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

/-- The coefficients `c n k` of the expansion `(b • D)^[n] = ∑ k ≤ n, c n k * D^[k]` for `b : A`
(`iterate_smul_apply_eq_sum`): `c 0 k` is `1` for `k = 0` and `0` otherwise, and
`c (n + 1) k = b * D (c n k) + b * c n (k - 1)`, the second term absent for `k = 0`. -/
def smulIterCoeff (D : Derivation R A A) (b : A) : ℕ → ℕ → A
  | 0, k => if k = 0 then 1 else 0
  | n + 1, 0 => b * D (smulIterCoeff D b n 0)
  | n + 1, k + 1 => b * D (smulIterCoeff D b n (k + 1)) + b * smulIterCoeff D b n k

/-- The coefficients of `(b • D)^[0]`: `1` for `k = 0` and `0` otherwise. -/
theorem smulIterCoeff_zero_left (D : Derivation R A A) (b : A) (k : ℕ) :
    smulIterCoeff D b 0 k = if k = 0 then 1 else 0 := by
  rw [smulIterCoeff]

/-- The recursion for the coefficients of `(b • D)^[n + 1]` beyond the constant term. -/
theorem smulIterCoeff_succ_succ (D : Derivation R A A) (b : A) (n k : ℕ) :
    smulIterCoeff D b (n + 1) (k + 1) =
      b * D (smulIterCoeff D b n (k + 1)) + b * smulIterCoeff D b n k := by
  rw [smulIterCoeff]

/-- For `n ≥ 1`, the expansion of `(b • D)^[n]` has no constant term. -/
@[simp]
theorem smulIterCoeff_succ_zero (D : Derivation R A A) (b : A) (n : ℕ) :
    smulIterCoeff D b (n + 1) 0 = 0 := by
  induction n with
  | zero => simp [smulIterCoeff]
  | succ n ih => rw [smulIterCoeff, ih, map_zero, mul_zero]

/-- The expansion of `(b • D)^[n]` involves only the iterates `D^[k]` with `k ≤ n`. -/
theorem smulIterCoeff_of_lt (D : Derivation R A A) (b : A) {n k : ℕ} (h : n < k) :
    smulIterCoeff D b n k = 0 := by
  induction n generalizing k with
  | zero => simp [smulIterCoeff_zero_left, h.ne']
  | succ n ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : k ≠ 0)
    simp [smulIterCoeff_succ_succ, ih (by omega : n < k + 1), ih (by omega : n < k)]

/-- The leading coefficient of the expansion of `(b • D)^[n]` is `b ^ n`. -/
@[simp]
theorem smulIterCoeff_self (D : Derivation R A A) (b : A) (n : ℕ) :
    smulIterCoeff D b n n = b ^ n := by
  induction n with
  | zero => simp [smulIterCoeff_zero_left]
  | succ n ih =>
    simp [smulIterCoeff_succ_succ, ih, smulIterCoeff_of_lt D b n.lt_succ_self, pow_succ']

/-- The coefficient of `D` in the expansion of `(b • D)^[n + 1]` is `(b • D)^[n] b`. -/
theorem smulIterCoeff_succ_one (D : Derivation R A A) (b : A) (n : ℕ) :
    smulIterCoeff D b (n + 1) 1 = (b • D)^[n] b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [smulIterCoeff_succ_succ, ih, smulIterCoeff_succ_zero, mul_zero, add_zero,
      Function.iterate_succ_apply', smul_apply, smul_eq_mul]

/-- The coefficients `smulIterCoeff` are natural: a ring homomorphism `f` intertwining `D` with
`E` carries the coefficients of `D` and `b` to those of `E` and `f b`. -/
theorem map_smulIterCoeff {S B : Type*} [CommSemiring S] [CommSemiring B] [Algebra S B]
    (f : A →+* B) (D : Derivation R A A) (E : Derivation S B B) (hf : ∀ y, f (D y) = E (f y))
    (b : A) (n k : ℕ) : f (smulIterCoeff D b n k) = smulIterCoeff E (f b) n k := by
  induction n generalizing k with
  | zero => simp only [smulIterCoeff_zero_left]; split_ifs <;> simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => simp [smulIterCoeff_succ_succ, hf, ih]

/-- **Iterates of `b • D`** for `b : A`: the `n`-th iterate is a combination of the iterates
`D^[k]`, `k ≤ n`, with coefficients `smulIterCoeff D b n k`. -/
theorem iterate_smul_apply_eq_sum (D : Derivation R A A) (b y : A) (n : ℕ) :
    (b • D)^[n] y = ∑ k ∈ Finset.range (n + 1), smulIterCoeff D b n k * D^[k] y := by
  induction n with
  | zero => simp [smulIterCoeff_zero_left]
  | succ n ih =>
    -- Differentiating the coefficients shifts the index by one; the top term vanishes.
    have hshift : ∑ k ∈ Finset.range (n + 1), b * (D^[k] y * D (smulIterCoeff D b n k)) =
        ∑ k ∈ Finset.range (n + 1), b * D (smulIterCoeff D b n (k + 1)) * D (D^[k] y) +
          b * D (smulIterCoeff D b n 0) * y := by
      have key (f : ℕ → A) (hf : f (n + 1) = 0) :
          ∑ k ∈ Finset.range (n + 1), f k = ∑ k ∈ Finset.range (n + 1), f (k + 1) + f 0 := by
        rw [← Finset.sum_range_succ', Finset.sum_range_succ f (n + 1), hf, add_zero]
      rw [key]
      · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
        congr 1
        · exact Finset.sum_congr rfl fun k _ ↦ by ring
        · ring
      · simp [smulIterCoeff_of_lt D b n.lt_succ_self]
    rw [Function.iterate_succ_apply', ih, smul_apply, map_sum, Finset.sum_range_succ' _ (n + 1)]
    simp only [leibniz, smul_eq_mul, smulIterCoeff, Finset.sum_add_distrib, add_mul,
      Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, hshift]
    simp only [mul_assoc]
    ring

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
