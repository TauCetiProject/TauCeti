/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
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

Multiplicativity comes from the general Leibniz rule `Dⁿ (a * b) = ∑ (n choose i) Dⁱ a Dⁿ⁻ⁱ b`.
After division by factorials it says that `a ↦ ∑ (Dⁿ a / n!) Xⁿ` is a ring homomorphism into the
polynomial ring `A[X]`; the Taylor exponential is its evaluation at `X = 1`.

A locally nilpotent derivation preserves an ideal it maps into itself, so the same holds for its
Taylor exponential. Local nilpotence may be checked on algebra generators. For the derivative
`d / dX` of a polynomial ring, scaled by `r`, the Taylor exponential is the Taylor shift
`p ↦ p (X + r)`.

## Main declarations

* `Derivation.iterate_apply_mul`: the general Leibniz rule for iterates of a derivation.
* `Derivation.exists_iterate_apply_eq_zero_of_adjoin_eq_top`: a derivation which is locally
  nilpotent on a set of algebra generators is locally nilpotent.
* `Derivation.taylorExp`: the Taylor exponential of a locally nilpotent derivation, as an algebra
  homomorphism.
* `Derivation.taylorExp_apply_eq_sum`: any iterate killing `a` gives a finite expansion of
  `taylorExp D a`.
* `Derivation.taylorExp_apply_mem`: the Taylor exponential preserves every ideal mapped into
  itself by the derivation.
* `Derivation.map_taylorExp`: Taylor exponentials are natural for algebra homomorphisms
  intertwining two derivations.
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

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- **General Leibniz rule** for iterates of a derivation of a commutative algebra. -/
theorem iterate_apply_mul (D : Derivation R A A) (n : ℕ) (a b : A) :
    D^[n] (a * b) = ∑ ij ∈ antidiagonal n, n.choose ij.1 • (D^[ij.1] a * D^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul (M := A) (fun i j => D^[i] a * D^[j] b) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, leibniz, smul_eq_mul,
      nsmul_add, sum_add_distrib]
    congr 1
    refine sum_congr rfl fun ij hij => ?_
    rw [n.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm, mul_comm]

/-- An iterate of a derivation which kills an element kills it from then on. -/
theorem iterate_apply_eq_zero_of_le (D : Derivation R A A) {a : A} {m n : ℕ}
    (hm : D^[m] a = 0) (hmn : m ≤ n) : D^[n] a = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [add_comm, Function.iterate_add_apply, hm, iterate_map_zero]

/-- A product of elements killed by the iterates `D^[m]` and `D^[n]` is killed by `D^[m + n]`. -/
theorem iterate_apply_mul_eq_zero (D : Derivation R A A) {a b : A} {m n : ℕ}
    (ha : D^[m] a = 0) (hb : D^[n] b = 0) : D^[m + n] (a * b) = 0 := by
  rw [iterate_apply_mul]
  refine sum_eq_zero fun ij hij => ?_
  rw [mem_antidiagonal] at hij
  rcases le_or_gt m ij.1 with h | h
  · rw [D.iterate_apply_eq_zero_of_le ha h, zero_mul, smul_zero]
  · rw [D.iterate_apply_eq_zero_of_le hb (by omega), mul_zero, smul_zero]

/-- **Local nilpotence can be checked on generators.** If every element of a set generating `A`
as an `R`-algebra is killed by some iterate of a derivation, then so is every element of `A`. -/
theorem exists_iterate_apply_eq_zero_of_adjoin_eq_top (D : Derivation R A A) {s : Set A}
    (hs : Algebra.adjoin R s = ⊤) (hD : ∀ x ∈ s, ∃ n, D^[n] x = 0) (a : A) :
    ∃ n, D^[n] a = 0 := by
  have ha : a ∈ Algebra.adjoin R s := hs ▸ Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact hD x hx
  | algebraMap r =>
    refine ⟨1, ?_⟩
    rw [Function.iterate_one, map_algebraMap]
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨max m n, ?_⟩
    rw [iterate_map_add, D.iterate_apply_eq_zero_of_le hm (le_max_left m n),
      D.iterate_apply_eq_zero_of_le hn (le_max_right m n), add_zero]
  | mul x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    exact ⟨m + n, D.iterate_apply_mul_eq_zero hm hn⟩

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
  · rw [mem_range] at h
    rw [D.iterate_apply_eq_zero_of_le (Nat.find_spec (hD a)) (not_lt.mp h), smul_zero]

/-- The Taylor expansion `a ↦ ∑ (Dⁿ a / n!) Xⁿ`, an algebra homomorphism into `A[X]`. -/
private noncomputable def taylorPolynomialAlgHom : A →ₐ[R] A[X] where
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

/-- The **Taylor exponential** `a ↦ ∑ Dⁿ a / n!` of a locally nilpotent derivation `D` of a
commutative `ℚ`-algebra. The sum is finite because some iterate of `D` kills `a`, and the map is
an algebra endomorphism by the general Leibniz rule. -/
noncomputable def taylorExp : A →ₐ[R] A :=
  ((aeval (1 : A)).restrictScalars R).comp (taylorPolynomialAlgHom D hD)

/-- **Finite expansion of the Taylor exponential.** If `D^[n]` kills `a`, then the Taylor
exponential of `a` is the sum of its first `n` Taylor terms. -/
theorem taylorExp_apply_eq_sum {a : A} {n : ℕ} (hn : D^[n] a = 0) :
    taylorExp D hD a = ∑ i ∈ range n, (i ! : ℚ)⁻¹ • D^[i] a := by
  classical
  -- `taylorExp` evaluates the Taylor polynomial at `1`; its terms are the Taylor terms below
  -- the least iterate killing `a`.
  have h : taylorExp D hD a = ∑ i ∈ range (Nat.find (hD a)), (i ! : ℚ)⁻¹ • D^[i] a := by
    change aeval (1 : A) (taylorPolynomial D hD a) = _
    simp only [taylorPolynomial, map_sum, aeval_monomial, Algebra.algebraMap_self,
      RingHom.id_apply, one_pow, mul_one]
  rw [h]
  refine sum_subset (range_mono (Nat.find_min' (hD a) hn)) fun i _ hi => ?_
  rw [mem_range, not_lt] at hi
  rw [D.iterate_apply_eq_zero_of_le (Nat.find_spec (hD a)) hi, smul_zero]

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

/-- **Naturality of Taylor exponentials.** An algebra homomorphism intertwining two locally
nilpotent derivations intertwines their Taylor exponentials. -/
theorem map_taylorExp {B : Type*} [CommRing B] [Algebra R B] [Algebra ℚ B]
    (D' : Derivation R B B) (hD' : ∀ b, ∃ n, D'^[n] b = 0) (f : A →ₐ[R] B)
    (hf : ∀ a, f (D a) = D' (f a)) (a : A) :
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

variable {R : Type*} [CommRing R]

/-- Every iterate of the scaled derivative `r • d / dX` is eventually zero on each polynomial. -/
theorem exists_iterate_smul_derivative'_apply_eq_zero (r : R) (p : R[X]) :
    ∃ n, (r • derivative' : Derivation R R[X] R[X])^[n] p = 0 := by
  refine Derivation.exists_iterate_apply_eq_zero_of_adjoin_eq_top _ adjoin_X ?_ p
  rintro x rfl
  exact ⟨2, by simp⟩

variable [Algebra ℚ R]

/-- **Taylor's formula for polynomials.** Over a `ℚ`-algebra, the Taylor exponential of the
scaled derivative `r • d / dX` is the Taylor shift `p ↦ p (X + r)`. -/
theorem taylorExp_smul_derivative' (r : R) :
    (r • derivative' : Derivation R R[X] R[X]).taylorExp
        (exists_iterate_smul_derivative'_apply_eq_zero r) = taylorAlgHom r := by
  refine algHom_ext ?_
  rw [Derivation.taylorExp_apply_eq_sum _ _ (n := 2) (by simp [derivative'_apply])]
  simp [sum_range_succ, derivative'_apply, smul_eq_C_mul]

end Polynomial
