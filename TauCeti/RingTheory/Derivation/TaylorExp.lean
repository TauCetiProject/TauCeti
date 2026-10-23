/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Algebra.Polynomial.Taylor
public import TauCeti.Algebra.Polynomial.Derivative
public import TauCeti.RingTheory.Derivation.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Tactic.FieldSimp

/-!
# Taylor exponentials of locally nilpotent derivations

Let `D` be a derivation of a commutative algebra `A` over `ℚ` which is *locally nilpotent*:
every element is killed by some iterate of `D`. Its **Taylor exponential**

```text
exp D a = ∑ Dⁿ a / n!
```

is then a finite sum for each `a`, and it is an algebra endomorphism of `A`. No global
nilpotence bound is needed, so the construction applies to the invariant vector fields of
unipotent groups on their infinite-dimensional coordinate rings.

Multiplicativity comes from the general Leibniz rule `Derivation.iterate_apply_mul`,
`Dⁿ (a * b) = ∑ (n choose i) Dⁱ a Dⁿ⁻ⁱ b`. After division by factorials it says that the Taylor
expansion `a ↦ ∑ (Dⁿ a / n!) Xⁿ` is an algebra homomorphism into the polynomial ring `A[X]`; the
Taylor exponential is its evaluation at `X = 1`.

If a locally nilpotent derivation maps an ideal into itself, so does its Taylor exponential.
For the derivative `d / dX` of a
polynomial ring, scaled by `r`, the Taylor exponential is the Taylor shift `p ↦ p (X + r)`.

## Main declarations

* `Derivation.taylorExpPolynomial`: the Taylor expansion `a ↦ ∑ (Dⁿ a / n!) Xⁿ` of a locally
  nilpotent derivation, as an algebra homomorphism into `A[X]`.
* `Derivation.taylorExp`: the Taylor exponential of a locally nilpotent derivation, as an algebra
  homomorphism.
* `Derivation.taylorExp_apply_eq_sum`: any iterate killing `a` gives a finite expansion of
  `taylorExp D a`.
* `Derivation.taylorExp_apply_mem`: the Taylor exponential preserves every ideal mapped into
  itself by the derivation.
* `Derivation.map_taylorExp`: Taylor exponentials are natural for additive maps intertwining
  two derivations.
* `Polynomial.taylorExp_smul_derivative'`: for the scaled derivative of a polynomial ring the
  Taylor exponential is `Polynomial.taylorAlgHom`.

## References

* G. Freudenburg, *Algebraic Theory of Locally Nilpotent Derivations*, Encyclopaedia of
  Mathematical Sciences 136, Springer (2006), Chapter 1.
-/

public section

open Finset Polynomial

open scoped Nat

namespace Derivation

variable {R : Type*} [CommSemiring R]

section TaylorExp

variable {A : Type*} [CommRing A] [Algebra R A] [Algebra ℚ A]

/-- The **divided Leibniz rule**: dividing the general Leibniz rule by `n!` removes the
binomial coefficients. -/
theorem inv_factorial_smul_iterate_apply_mul (D : Derivation R A A) (n : ℕ) (a b : A) :
    (n ! : ℚ)⁻¹ • D^[n] (a * b) =
      ∑ ij ∈ antidiagonal n, ((ij.1 ! : ℚ)⁻¹ • D^[ij.1] a) * ((ij.2 ! : ℚ)⁻¹ • D^[ij.2] b) := by
  rw [iterate_apply_mul, smul_sum]
  refine sum_congr rfl fun ij hij => ?_
  rw [mem_antidiagonal] at hij
  subst n
  rw [smul_mul_smul_comm, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  have h : ((ij.1 + ij.2).choose ij.1 * ij.1 ! * ij.2 ! : ℚ) = (ij.1 + ij.2)! := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right ij.1 ij.2)
    rw [Nat.add_sub_cancel_left] at this
    exact_mod_cast this
  have hc : ((ij.1 + ij.2).choose ij.1 : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right ij.1 ij.2)).ne'
  rw [← h]
  field_simp

variable (D : Derivation R A A) (hD : ∀ a, ∃ n, D^[n] a = 0)

open scoped Classical in
/-- The Taylor coefficients `Dⁿ a / n!` of `a`, as a polynomial in an auxiliary variable. -/
private noncomputable def taylorPolynomial (a : A) : A[X] :=
  ∑ i ∈ range (Nat.find (hD a)), monomial i ((i ! : ℚ)⁻¹ • D^[i] a)

private theorem coeff_taylorPolynomial (a : A) (n : ℕ) :
    (taylorPolynomial D hD a).coeff n = (n ! : ℚ)⁻¹ • D^[n] a := by
  classical
  simp only [taylorPolynomial, finsetSum_coeff, coeff_monomial]
  rw [sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [mem_range, not_lt] at h
    have hfind : (D.toLinearMap ^ Nat.find (hD a)) a = 0 := by
      simpa [Module.End.pow_apply] using Nat.find_spec (hD a)
    rw [← coeFn_coe, ← Module.End.pow_apply, Module.End.pow_map_zero_of_le h hfind, smul_zero]

/-- The **Taylor expansion** `a ↦ ∑ (Dⁿ a / n!) Xⁿ` of a locally nilpotent derivation `D`, an
algebra homomorphism into `A[X]`. Its evaluation at `X = 1` is the Taylor exponential. -/
noncomputable def taylorExpPolynomial : A →ₐ[R] A[X] where
  toFun := taylorPolynomial D hD
  map_one' := by
    ext n
    rw [coeff_taylorPolynomial, coeff_one]
    rcases n with _ | n
    · simp
    · rw [Function.iterate_succ_apply, map_one_eq_zero, iterate_map_zero, smul_zero]
      simp
  map_mul' a b := by
    ext n
    simp only [coeff_taylorPolynomial, coeff_mul, inv_factorial_smul_iterate_apply_mul]
  map_zero' := by
    ext n
    rw [coeff_taylorPolynomial, iterate_map_zero, smul_zero, coeff_zero]
  map_add' a b := by
    ext n
    simp only [coeff_taylorPolynomial, coeff_add, iterate_map_add, smul_add]
  commutes' r := by
    ext n
    rw [coeff_taylorPolynomial, Polynomial.algebraMap_apply, coeff_C]
    rcases n with _ | n
    · simp
    · rw [Function.iterate_succ_apply, map_algebraMap, iterate_map_zero, smul_zero]
      simp

/-- The coefficients of the Taylor expansion are the Taylor terms `Dⁿ a / n!`. -/
@[simp]
theorem coeff_taylorExpPolynomial (a : A) (n : ℕ) :
    (taylorExpPolynomial D hD a).coeff n = (n ! : ℚ)⁻¹ • D^[n] a :=
  coeff_taylorPolynomial D hD a n

/-- The **Taylor exponential** `a ↦ ∑ Dⁿ a / n!` of a locally nilpotent derivation `D` of a
commutative `ℚ`-algebra. The sum is finite because some iterate of `D` kills `a`, and the map is
an algebra endomorphism by the general Leibniz rule. -/
noncomputable def taylorExp : A →ₐ[R] A :=
  ((aeval (1 : A)).restrictScalars R).comp (taylorExpPolynomial D hD)

/-- The Taylor exponential is the evaluation of the Taylor expansion at `X = 1`. -/
@[simp]
theorem aeval_one_taylorExpPolynomial (a : A) :
    aeval (1 : A) (taylorExpPolynomial D hD a) = taylorExp D hD a :=
  (rfl)

/-- **Finite expansion of the Taylor exponential.** If `D^[n]` kills `a`, then the Taylor
exponential of `a` is the sum of its first `n` Taylor terms. -/
theorem taylorExp_apply_eq_sum {a : A} {n : ℕ} (hn : D^[n] a = 0) :
    taylorExp D hD a = ∑ i ∈ range n, (i ! : ℚ)⁻¹ • D^[i] a := by
  -- The Taylor coefficients vanish from `n` on, so the Taylor expansion is supported in
  -- `range n`.
  have hsupp : (taylorExpPolynomial D hD a).support ⊆ range n := fun i hi => by
    rw [mem_support_iff, coeff_taylorExpPolynomial] at hi
    rw [mem_range]
    by_contra! h
    have hn' : (D.toLinearMap ^ n) a = 0 := by simpa [Module.End.pow_apply] using hn
    rw [← coeFn_coe, ← Module.End.pow_apply, Module.End.pow_map_zero_of_le h hn',
      smul_zero] at hi
    exact hi rfl
  rw [← aeval_one_taylorExpPolynomial, aeval_def, eval₂_eq_sum,
    Polynomial.sum_eq_of_subset _ (fun i => by rw [map_zero, zero_mul]) hsupp]
  simp

/-- The Taylor exponential of the zero derivation is the identity. -/
@[simp]
theorem taylorExp_zero (hD : ∀ a, ∃ n, (0 : Derivation R A A)^[n] a = 0) :
    taylorExp 0 hD = AlgHom.id R A := by
  ext a
  rw [taylorExp_apply_eq_sum 0 hD (n := 1) (by simp)]
  simp

/-- **The Taylor exponential preserves stable ideals.** If a locally nilpotent derivation maps an
ideal into itself, so does its Taylor exponential. -/
theorem taylorExp_apply_mem {I : Ideal A} (hI : ∀ x ∈ I, D x ∈ I) {a : A} (ha : a ∈ I) :
    taylorExp D hD a ∈ I := by
  obtain ⟨n, hn⟩ := hD a
  have hiter : ∀ i, D^[i] a ∈ I := fun i => by
    induction i with
    | zero => exact ha
    | succ i ih => exact Function.iterate_succ_apply' D i a ▸ hI _ ih
  rw [taylorExp_apply_eq_sum D hD hn]
  refine sum_mem fun i _ => ?_
  have hi := hiter i
  rw [← algebraMap_smul A, smul_eq_mul]
  exact I.mul_mem_left _ hi

/-- **Naturality of Taylor exponentials.** An additive map intertwining two locally nilpotent
derivations, possibly over different base rings, intertwines their Taylor exponentials. -/
theorem map_taylorExp {R' B : Type*} [CommSemiring R'] [CommRing B] [Algebra R' B] [Algebra ℚ B]
    (D' : Derivation R' B B) (hD' : ∀ b, ∃ n, D'^[n] b = 0) {F : Type*} [FunLike F A B]
    [AddMonoidHomClass F A B] (f : F) (hf : ∀ a, f (D a) = D' (f a)) (a : A) :
    f (taylorExp D hD a) = taylorExp D' hD' (f a) := by
  have hiter : ∀ i, f (D^[i] a) = D'^[i] (f a) := fun i =>
    Function.Semiconj.iterate_right hf i a
  obtain ⟨n, hn⟩ := hD a
  have hn' : D'^[n] (f a) = 0 := by rw [← hiter, hn, map_zero]
  rw [taylorExp_apply_eq_sum D hD hn, taylorExp_apply_eq_sum D' hD' hn', map_sum]
  exact sum_congr rfl fun i _ => by rw [map_rat_smul, hiter]

end TaylorExp

end Derivation

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- **Taylor's formula for polynomials.** Over a `ℚ`-algebra, the Taylor exponential of the
scaled derivative `r • d / dX` is the Taylor shift `p ↦ p (X + r)`. -/
theorem taylorExp_smul_derivative' (r : R) :
    (r • derivative' : Derivation R R[X] R[X]).taylorExp
        (exists_iterate_smul_derivative'_apply_eq_zero r) = taylorAlgHom r := by
  refine algHom_ext ?_
  rw [Derivation.taylorExp_apply_eq_sum _ _ (n := 2) (by simp [derivative'_apply])]
  simp [sum_range_succ, derivative'_apply, smul_eq_C_mul]

end Polynomial
