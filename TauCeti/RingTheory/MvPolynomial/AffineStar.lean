/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Basic
import TauCeti.Algebra.Ring.Commutator.Binomial

/-!
# The ordered product for the relation `xy = y(x + h)`

Write `x = X 0` and `y = X 1` for the two variables of `MvPolynomial (Fin 2) S`, and fix a
parameter `h : S`. If two elements `x`, `y` of an `S`-algebra satisfy `x y = y (x + h)`, then
`x ^ b y ^ c = y ^ c (x + c h) ^ b`, so a product of two ordered monomials `y ^ a x ^ b` and
`y ^ c x ^ d` is again a finite combination of ordered monomials:

```text
(y ^ a x ^ b) ⋆ (y ^ c x ^ d) = ∑ n ∈ [0, b], (b choose n) c ^ n h ^ n y ^ (a + c) x ^ (b + d - n)
```

At `h = 1` this is the multiplication of the enveloping algebra of the two-dimensional
nonabelian Lie algebra `[x, y] = y`, transported to polynomials through the ordered monomials,
which form its Poincaré–Birkhoff–Witt basis. At `h = t`, the deformation parameter, ordered
evaluation into the PBW Rees algebra carries the ordered product to the Rees multiplication. No
factorial is divided, so everything holds over an arbitrary commutative semiring.

## Main definitions

* `TauCeti.affineStar h`: the `S`-bilinear ordered product on `MvPolynomial (Fin 2) S`.
* `TauCeti.orderedEval x y`: the `S`-linear map sending `y ^ a x ^ b` to `y ^ a * x ^ b`.

## Main results

* `TauCeti.affineStar_X_pow_mul_X_pow`: the product of two ordered monomials.
* `TauCeti.affineStar_one_left`, `TauCeti.affineStar_one_right`: `1` is a two-sided unit.
* `TauCeti.map_affineStar`: compatibility with a change of coefficients, which specializes the
  parameter.
* `TauCeti.affineStar_zero`: at `h = 0` the ordered product is the commutative product.
* `TauCeti.affineStar_eq_mul_add_of_mul_self_eq_zero`: if `ε ^ 2 = 0` then
  `p ⋆ q = p q + ε (∂ₓ p) y (∂_y q)`; the first-order coefficient is not alternating, as
  `TauCeti.affineStar_X_zero_X_one` and `TauCeti.affineStar_X_one_X_zero` show.
* `TauCeti.orderedEval_affineStar`: if `x y = y (x + h)` in an `S`-algebra, ordered evaluation
  turns the ordered product into the multiplication of the algebra.

Associativity, `TauCeti.affineStar_assoc`, is proved in
`TauCeti.Algebra.Lie.UniversalEnveloping.Rees.AffineLine`, through the Poincaré–Birkhoff–Witt
basis of the enveloping algebra of `[x, y] = y`.

## References

* S. Gutt, *Deformation Quantization and Symmetries*, lectures, Würzburg (2019), Lecture 1, for
  ordered and symmetrized products.
-/

public section

open MvPolynomial Finset

namespace TauCeti

variable {S : Type*} [CommSemiring S]

/-- The ordered product of the basis monomials `y ^ (s 1) x ^ (s 0)` and `y ^ (t 1) x ^ (t 0)`. -/
private noncomputable def affineStarTerm (h : S) (s t : Fin 2 →₀ ℕ) : MvPolynomial (Fin 2) S :=
  ∑ n ∈ range (s 0 + 1),
    C ((s 0).choose n * t 1 ^ n * h ^ n : S) * (X 1 ^ (s 1 + t 1) * X 0 ^ (s 0 + t 0 - n))

/-- The ordered product with parameter `h` on polynomials in `x = X 0` and `y = X 1`: the
`S`-bilinear map with `(y ^ a x ^ b) ⋆ (y ^ c x ^ d)` equal to
`∑ n ∈ [0, b], (b choose n) c ^ n h ^ n y ^ (a + c) x ^ (b + d - n)`, see
`TauCeti.affineStar_X_pow_mul_X_pow`. It is the multiplication of `x`, `y` with `x y = y (x + h)`,
read through ordered monomials (`TauCeti.orderedEval_affineStar`). -/
noncomputable def affineStar (h : S) :
    MvPolynomial (Fin 2) S →ₗ[S] MvPolynomial (Fin 2) S →ₗ[S] MvPolynomial (Fin 2) S :=
  (basisMonomials (Fin 2) S).constr S fun s ↦
    (basisMonomials (Fin 2) S).constr S fun t ↦ affineStarTerm h s t

/-- A monomial in two variables is a scalar multiple of the ordered monomial
`X 1 ^ s 1 * X 0 ^ s 0`. -/
theorem _root_.MvPolynomial.monomial_eq_smul_X_one_pow_mul_X_zero_pow (s : Fin 2 →₀ ℕ) (a : S) :
    monomial s a = a • (X 1 ^ s 1 * X 0 ^ s 0 : MvPolynomial (Fin 2) S) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Fin.prod_univ_two, C_mul',
    mul_comm]

/-- The ordered monomial `X 1 ^ a * X 0 ^ b` as a monomial with coefficient `1`. -/
theorem _root_.MvPolynomial.X_one_pow_mul_X_zero_pow_eq_monomial (a b : ℕ) :
    (X 1 ^ a * X 0 ^ b : MvPolynomial (Fin 2) S) =
      monomial (Finsupp.single 1 a + Finsupp.single 0 b) 1 := by
  rw [monomial_eq_smul_X_one_pow_mul_X_zero_pow, one_smul]
  simp

/-- **The ordered product of two ordered monomials.** -/
theorem affineStar_X_pow_mul_X_pow (h : S) (a b c d : ℕ) :
    affineStar h (X 1 ^ a * X 0 ^ b) (X 1 ^ c * X 0 ^ d) =
      ∑ n ∈ range (b + 1),
        C (b.choose n * c ^ n * h ^ n : S) * (X 1 ^ (a + c) * X 0 ^ (b + d - n)) := by
  rw [X_one_pow_mul_X_zero_pow_eq_monomial a b, X_one_pow_mul_X_zero_pow_eq_monomial c d,
    ← congrFun (coe_basisMonomials _ S), ← congrFun (coe_basisMonomials _ S), affineStar,
    Module.Basis.constr_basis, Module.Basis.constr_basis, affineStarTerm]
  simp

/-- Induction on a polynomial in two variables through scalar multiples and sums of the ordered
monomials `X 1 ^ a * X 0 ^ b`. -/
@[elab_as_elim]
theorem _root_.MvPolynomial.induction_on_X_pow_mul_X_pow {P : MvPolynomial (Fin 2) S → Prop}
    (p : MvPolynomial (Fin 2) S) (smul : ∀ (a : S) p, P p → P (a • p))
    (add : ∀ p q, P p → P q → P (p + q)) (X_pow : ∀ a b : ℕ, P (X 1 ^ a * X 0 ^ b)) : P p := by
  induction p using MvPolynomial.induction_on' with
  | monomial s a => rw [monomial_eq_smul_X_one_pow_mul_X_zero_pow]; exact smul _ _ (X_pow _ _)
  | add p q hp hq => exact add p q hp hq

/-- The constant `1` is a left unit for the ordered product. -/
@[simp]
theorem affineStar_one_left (h : S) (p : MvPolynomial (Fin 2) S) : affineStar h 1 p = p := by
  induction p using MvPolynomial.induction_on_X_pow_mul_X_pow with
  | smul a p hp => rw [map_smul, hp]
  | add p q hp hq => rw [map_add, hp, hq]
  | X_pow a b =>
      have h1 : (1 : MvPolynomial (Fin 2) S) = X 1 ^ 0 * X 0 ^ 0 := by simp
      rw [h1, affineStar_X_pow_mul_X_pow]
      simp

/-- The constant `1` is a right unit for the ordered product. -/
@[simp]
theorem affineStar_one_right (h : S) (p : MvPolynomial (Fin 2) S) : affineStar h p 1 = p := by
  induction p using MvPolynomial.induction_on_X_pow_mul_X_pow with
  | smul a p hp => rw [map_smul, LinearMap.smul_apply, hp]
  | add p q hp hq => rw [map_add, LinearMap.add_apply, hp, hq]
  | X_pow a b =>
      have h1 : (1 : MvPolynomial (Fin 2) S) = X 1 ^ 0 * X 0 ^ 0 := by simp
      rw [h1, affineStar_X_pow_mul_X_pow, sum_range_succ']
      simp

/-- **Specialization of the parameter.** A change of coefficients `φ` carries the ordered
product with parameter `h` to the ordered product with parameter `φ h`. -/
theorem map_affineStar {S' : Type*} [CommSemiring S'] (φ : S →+* S') (h : S)
    (p q : MvPolynomial (Fin 2) S) :
    map φ (affineStar h p q) = affineStar (φ h) (map φ p) (map φ q) := by
  have hmap (a : S) (p : MvPolynomial (Fin 2) S) : map φ (a • p) = φ a • map φ p := by
    rw [smul_eq_C_mul, map_mul, map_C, smul_eq_C_mul]
  induction p using MvPolynomial.induction_on_X_pow_mul_X_pow with
  | smul a p hp => simp only [hmap, map_smul, LinearMap.smul_apply, hp]
  | add p p' hp hp' => simp only [map_add, LinearMap.add_apply, hp, hp']
  | X_pow a b =>
      induction q using MvPolynomial.induction_on_X_pow_mul_X_pow with
      | smul c q hq => simp only [hmap, map_smul, hq]
      | add q q' hq hq' => simp only [map_add, hq, hq']
      | X_pow c d => simp [affineStar_X_pow_mul_X_pow]

/-- The ordered product of two ordered monomials when `ε ^ 2 = 0`: only the terms `n = 0, 1` of
`TauCeti.affineStar_X_pow_mul_X_pow` survive. -/
private theorem affineStar_X_pow_mul_X_pow_of_mul_self_eq_zero {ε : S} (hε : ε * ε = 0)
    (a b c d : ℕ) :
    affineStar ε (X 1 ^ a * X 0 ^ b) (X 1 ^ c * X 0 ^ d) =
      X 1 ^ (a + c) * X 0 ^ (b + d) + C (b * c * ε : S) * (X 1 ^ (a + c) * X 0 ^ (b + d - 1)) := by
  rw [affineStar_X_pow_mul_X_pow]
  rcases b with _ | b
  · simp
  -- Split off the terms `n = 0, 1`; the others carry `ε ^ (n + 2) = 0`.
  rw [sum_range_succ', sum_range_succ', sum_eq_zero fun n _ ↦ by simp [pow_succ, mul_assoc, hε]]
  simp [show b + 1 + d - 1 = b + d by omega]
  ring

/-- **The first-order coefficient of the ordered product.** If `ε ^ 2 = 0`, the ordered product
with parameter `ε` is the commutative product plus `ε` times `(∂ₓ p) y (∂_y q)`. -/
theorem affineStar_eq_mul_add_of_mul_self_eq_zero {ε : S} (hε : ε * ε = 0)
    (p q : MvPolynomial (Fin 2) S) :
    affineStar ε p q = p * q + C ε * (pderiv 0 p * X 1 * pderiv 1 q) := by
  induction p using MvPolynomial.induction_on_X_pow_mul_X_pow with
  | smul a p hp =>
      rw [map_smul, LinearMap.smul_apply, hp]
      simp only [smul_eq_C_mul, Derivation.leibniz, pderiv_C, smul_eq_mul]
      ring
  | add p p' hp hp' =>
      simp only [map_add, LinearMap.add_apply, hp, hp']
      ring
  | X_pow a b =>
      induction q using MvPolynomial.induction_on_X_pow_mul_X_pow with
      | smul c q hq =>
          rw [map_smul, hq]
          simp only [smul_eq_C_mul, Derivation.leibniz, pderiv_C, smul_eq_mul]
          ring
      | add q q' hq hq' =>
          simp only [map_add, hq, hq']
          ring
      | X_pow c d =>
          rw [affineStar_X_pow_mul_X_pow_of_mul_self_eq_zero hε]
          have h10 : (1 : Fin 2) ≠ 0 := by decide
          simp only [Derivation.leibniz, Derivation.leibniz_pow, pderiv_X_self, pderiv_X_of_ne h10,
            pderiv_X_of_ne h10.symm, smul_eq_mul, mul_one, nsmul_eq_mul]
          rcases b with _ | b
          · simp [pow_add, mul_assoc]
          rcases c with _ | c
          · simp [pow_add, mul_assoc]
          simp only [map_mul, map_natCast, show b + 1 + d - 1 = b + d by omega,
            Nat.add_sub_cancel]
          ring

/-- **At parameter zero the ordered product is the commutative product.** -/
theorem affineStar_zero :
    affineStar (0 : S) = LinearMap.mul S (MvPolynomial (Fin 2) S) :=
  LinearMap.ext₂ fun p q ↦ by
    simpa using affineStar_eq_mul_add_of_mul_self_eq_zero (mul_zero (0 : S)) p q

/-- The Rees relation in ordered form: `x ⋆ y = y x + h y`. -/
theorem affineStar_X_zero_X_one (h : S) :
    affineStar h (X 0) (X 1) = X 1 * X 0 + C h * X 1 := by
  simpa [sum_range_succ, add_comm] using affineStar_X_pow_mul_X_pow h 0 1 1 0

/-- `y ⋆ x = y x`: an ordered monomial times `x` needs no reordering. -/
theorem affineStar_X_one_X_zero (h : S) : affineStar h (X 1) (X 0) = X 1 * X 0 := by
  simpa using affineStar_X_pow_mul_X_pow h 1 0 0 1

section OrderedEval

variable {A : Type*} [Semiring A] [Algebra S A]

/-- Ordered evaluation: the `S`-linear map sending the ordered monomial `y ^ a x ^ b` to
`y ^ a * x ^ b`, with all powers of `y` to the left of all powers of `x`. -/
noncomputable def orderedEval (x y : A) : MvPolynomial (Fin 2) S →ₗ[S] A :=
  (basisMonomials (Fin 2) S).constr S fun s ↦ y ^ s 1 * x ^ s 0

@[simp]
theorem orderedEval_X_pow_mul_X_pow (x y : A) (a b : ℕ) :
    orderedEval x y (X 1 ^ a * X 0 ^ b : MvPolynomial (Fin 2) S) = y ^ a * x ^ b := by
  rw [X_one_pow_mul_X_zero_pow_eq_monomial, ← congrFun (coe_basisMonomials _ S), orderedEval,
    Module.Basis.constr_basis]
  simp

@[simp]
theorem orderedEval_monomial (x y : A) (s : Fin 2 →₀ ℕ) (a : S) :
    orderedEval x y (monomial s a) = a • (y ^ s 1 * x ^ s 0) := by
  rw [monomial_eq_smul_X_one_pow_mul_X_zero_pow, map_smul, orderedEval_X_pow_mul_X_pow]

@[simp]
theorem orderedEval_one (x y : A) : orderedEval x y (1 : MvPolynomial (Fin 2) S) = 1 := by
  simpa using orderedEval_X_pow_mul_X_pow (S := S) x y 0 0

@[simp]
theorem orderedEval_X_zero (x y : A) : orderedEval x y (X 0 : MvPolynomial (Fin 2) S) = x := by
  simpa using orderedEval_X_pow_mul_X_pow (S := S) x y 0 1

@[simp]
theorem orderedEval_X_one (x y : A) : orderedEval x y (X 1 : MvPolynomial (Fin 2) S) = y := by
  simpa using orderedEval_X_pow_mul_X_pow (S := S) x y 1 0

/-- **Ordered evaluation is multiplicative for the ordered product.** If `x y = y (x + h)` in an
`S`-algebra, then ordered evaluation carries the ordered product with parameter `h` to the
multiplication of the algebra. -/
theorem orderedEval_affineStar {x y : A} {h : S} (hxy : x * y = y * (x + algebraMap S A h))
    (p q : MvPolynomial (Fin 2) S) :
    orderedEval x y (affineStar h p q) = orderedEval x y p * orderedEval x y q := by
  induction p using MvPolynomial.induction_on_X_pow_mul_X_pow with
  | smul a p hp => simp only [map_smul, LinearMap.smul_apply, hp, smul_mul_assoc]
  | add p p' hp hp' => simp only [map_add, LinearMap.add_apply, hp, hp', add_mul]
  | X_pow a b =>
      induction q using MvPolynomial.induction_on_X_pow_mul_X_pow with
      | smul c q hq => simp only [map_smul, hq, mul_smul_comm]
      | add q q' hq hq' => simp only [map_add, hq, hq', mul_add]
      | X_pow c d =>
          rw [affineStar_X_pow_mul_X_pow, orderedEval_X_pow_mul_X_pow, orderedEval_X_pow_mul_X_pow,
            mul_assoc, ← mul_assoc (x ^ b), Associative.pow_mul_pow_eq_sum_smul hxy, sum_mul,
            mul_sum, map_sum]
          refine sum_congr rfl fun n hn ↦ ?_
          rw [← smul_eq_C_mul, map_smul, orderedEval_X_pow_mul_X_pow, smul_mul_assoc,
            mul_smul_comm, Nat.sub_add_comm (Nat.lt_succ_iff.mp (mem_range.mp hn)), pow_add,
            pow_add]
          simp only [mul_assoc]

end OrderedEval

end TauCeti
