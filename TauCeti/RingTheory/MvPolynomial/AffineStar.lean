/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.RingTheory.MvPolynomial.Rescale
import Mathlib.Algebra.MvPolynomial.Coeff
import TauCeti.Algebra.MvPolynomial.Fin.Two.Ordered
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

* `TauCeti.affineStar_X_one_pow_mul_X_zero_pow`: the product of two ordered monomials.
* `TauCeti.affineStar_one_left`, `TauCeti.affineStar_one_right`: `1` is a two-sided unit.
* `TauCeti.map_affineStar`: compatibility with a change of coefficients, which specializes the
  parameter.
* `TauCeti.rescale_affineStar`: rescaling the variables by `u` and `v` carries the ordered product
  with parameter `u h` to the ordered product with parameter `h`.
* `TauCeti.affineStar_zero`: at `h = 0` the ordered product is the commutative product.
* `TauCeti.affineStar_eq_mul_add_of_mul_self_eq_zero`: if `ε ^ 2 = 0` then
  `p ⋆ q = p q + ε (∂ₓ p) y (∂_y q)`; the first-order coefficient is not alternating, as
  `TauCeti.affineStar_X_zero_X_one` and `TauCeti.affineStar_X_one_X_zero` show.
* `TauCeti.orderedEval_affineStar`: if `x y = y (x + h)` in an `S`-algebra, ordered evaluation
  turns the ordered product into the multiplication of the algebra.
* `TauCeti.map_orderedEval`: ordered evaluation is natural in ring homomorphisms compatible with a
  change of coefficients.

Associativity, `TauCeti.affineStar_assoc`, is proved in
`TauCeti.Algebra.Lie.UniversalEnveloping.PBW.AffineLine`, through the Poincaré–Birkhoff–Witt
basis of the enveloping algebra of `[x, y] = y`.

## References

* S. Gutt, *Deformation Quantization and Symmetries*, lectures, Würzburg (2019), Lecture 1, as
  background on star products on duals of Lie algebras.
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
`TauCeti.affineStar_X_one_pow_mul_X_zero_pow`. It is the multiplication of `x`, `y` with
`x y = y (x + h)`, read through ordered monomials (`TauCeti.orderedEval_affineStar`). -/
noncomputable def affineStar (h : S) :
    MvPolynomial (Fin 2) S →ₗ[S] MvPolynomial (Fin 2) S →ₗ[S] MvPolynomial (Fin 2) S :=
  (basisMonomials (Fin 2) S).constr S fun s ↦
    (basisMonomials (Fin 2) S).constr S fun t ↦ affineStarTerm h s t

/-- **The ordered product of two ordered monomials.** -/
theorem affineStar_X_one_pow_mul_X_zero_pow (h : S) (a b c d : ℕ) :
    affineStar h (X 1 ^ a * X 0 ^ b) (X 1 ^ c * X 0 ^ d) =
      ∑ n ∈ range (b + 1),
        C (b.choose n * c ^ n * h ^ n : S) * (X 1 ^ (a + c) * X 0 ^ (b + d - n)) := by
  conv_lhs => simp only [X_pow_eq_monomial, monomial_mul_monomial, mul_one]
  rw [← congrFun (coe_basisMonomials _ S), ← congrFun (coe_basisMonomials _ S), affineStar,
    Module.Basis.constr_basis, Module.Basis.constr_basis, affineStarTerm]
  simp

/-- The constant `1` is a left unit for the ordered product. -/
@[simp]
theorem affineStar_one_left (h : S) (p : MvPolynomial (Fin 2) S) : affineStar h 1 p = p := by
  have h1 : (1 : MvPolynomial (Fin 2) S) = X 1 ^ 0 * X 0 ^ 0 := by simp
  refine LinearMap.congr_fun (linearMap_ext_X_one_pow_mul_X_zero_pow
    (f := affineStar h 1) (g := LinearMap.id) fun a b ↦ ?_) p
  rw [h1, affineStar_X_one_pow_mul_X_zero_pow]
  simp

/-- The constant `1` is a right unit for the ordered product. -/
@[simp]
theorem affineStar_one_right (h : S) (p : MvPolynomial (Fin 2) S) : affineStar h p 1 = p := by
  have h1 : (1 : MvPolynomial (Fin 2) S) = X 1 ^ 0 * X 0 ^ 0 := by simp
  refine LinearMap.congr_fun (linearMap_ext_X_one_pow_mul_X_zero_pow
    (f := (affineStar h).flip 1) (g := LinearMap.id) fun a b ↦ ?_) p
  rw [LinearMap.flip_apply, h1, affineStar_X_one_pow_mul_X_zero_pow, sum_range_succ']
  simp

/-- A constant on the left multiplies by that constant. -/
@[simp]
theorem affineStar_C_left (h r : S) (p : MvPolynomial (Fin 2) S) :
    affineStar h (C r) p = C r * p := by
  rw [← smul_eq_C_mul, ← mul_one (C r), ← smul_eq_C_mul, map_smul, LinearMap.smul_apply,
    affineStar_one_left]

/-- A constant on the right multiplies by that constant. -/
@[simp]
theorem affineStar_C_right (h r : S) (p : MvPolynomial (Fin 2) S) :
    affineStar h p (C r) = p * C r := by
  rw [mul_comm, ← smul_eq_C_mul, ← mul_one (C r), ← smul_eq_C_mul, map_smul,
    affineStar_one_right]

/-- **Specialization of the parameter.** A change of coefficients `φ` carries the ordered
product with parameter `h` to the ordered product with parameter `φ h`. -/
@[simp]
theorem map_affineStar {S' : Type*} [CommSemiring S'] (φ : S →+* S') (h : S)
    (p q : MvPolynomial (Fin 2) S) :
    map φ (affineStar h p q) = affineStar (φ h) (map φ p) (map φ q) := by
  have hmap (a : S) (p : MvPolynomial (Fin 2) S) : map φ (a • p) = φ a • map φ p := by
    rw [smul_eq_C_mul, map_mul, map_C, smul_eq_C_mul]
  induction p using MvPolynomial.induction_on_X_one_pow_mul_X_zero_pow with
  | smul a p hp => simp only [hmap, map_smul, LinearMap.smul_apply, hp]
  | add p p' hp hp' => simp only [map_add, LinearMap.add_apply, hp, hp']
  | X_pow a b =>
      induction q using MvPolynomial.induction_on_X_one_pow_mul_X_zero_pow with
      | smul c q hq => simp only [hmap, map_smul, hq]
      | add q q' hq hq' => simp only [map_add, hq, hq']
      | X_pow c d => simp [affineStar_X_one_pow_mul_X_zero_pow]

/-- The ordered product of two ordered monomials when `ε ^ 2 = 0`: only the terms `n = 0, 1` of
`TauCeti.affineStar_X_one_pow_mul_X_zero_pow` survive. -/
private theorem affineStar_X_one_pow_mul_X_zero_pow_of_mul_self_eq_zero {ε : S} (hε : ε * ε = 0)
    (a b c d : ℕ) :
    affineStar ε (X 1 ^ a * X 0 ^ b) (X 1 ^ c * X 0 ^ d) =
      X 1 ^ (a + c) * X 0 ^ (b + d) + C (b * c * ε : S) * (X 1 ^ (a + c) * X 0 ^ (b + d - 1)) := by
  rw [affineStar_X_one_pow_mul_X_zero_pow]
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
  have key : affineStar ε = LinearMap.mul S _ + ε • (LinearMap.mul S _).compl₁₂
      (LinearMap.mulRight S (X 1) ∘ₗ (pderiv 0).toLinearMap) (pderiv 1).toLinearMap := by
    refine linearMap_ext₂_X_one_pow_mul_X_zero_pow fun a b c d ↦ ?_
    rw [affineStar_X_one_pow_mul_X_zero_pow_of_mul_self_eq_zero hε]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply,
      LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mul_apply', Derivation.coeFn_coe,
      Derivation.leibniz, Derivation.leibniz_pow, pderiv_X_self, pderiv_X_of_ne h10,
      pderiv_X_of_ne h10.symm, smul_eq_mul, mul_one, nsmul_eq_mul, smul_eq_C_mul]
    rcases b with _ | b
    · simp [pow_add, mul_assoc]
    rcases c with _ | c
    · simp [pow_add, mul_assoc]
    simp only [map_mul, map_natCast, show b + 1 + d - 1 = b + d by omega, Nat.add_sub_cancel]
    ring
  simpa [smul_eq_C_mul] using LinearMap.congr_fun₂ key p q

/-- **At parameter zero the ordered product is the commutative product.** -/
@[simp]
theorem affineStar_zero :
    affineStar (0 : S) = LinearMap.mul S (MvPolynomial (Fin 2) S) :=
  LinearMap.ext₂ fun p q ↦ by
    simpa using affineStar_eq_mul_add_of_mul_self_eq_zero (mul_zero (0 : S)) p q

/-- The Rees relation in ordered form: `x ⋆ y = y x + h y`. -/
@[simp]
theorem affineStar_X_zero_X_one (h : S) :
    affineStar h (X 0) (X 1) = X 1 * X 0 + C h * X 1 := by
  simpa [sum_range_succ, add_comm] using affineStar_X_one_pow_mul_X_zero_pow h 0 1 1 0

/-- `y ⋆ x = y x`: an ordered monomial times `x` needs no reordering. -/
@[simp]
theorem affineStar_X_one_X_zero (h : S) : affineStar h (X 1) (X 0) = X 1 * X 0 := by
  simpa using affineStar_X_one_pow_mul_X_zero_pow h 1 0 0 1

/-- Rescaling an ordered monomial multiplies it by the matching product of scalars. -/
private theorem rescale_X_one_pow_mul_X_zero_pow (s : Fin 2 → S) (a b : ℕ) :
    rescale s (X 1 ^ a * X 0 ^ b : MvPolynomial (Fin 2) S) =
      (s 1 ^ a * s 0 ^ b) • (X 1 ^ a * X 0 ^ b) := by
  simp only [map_mul, map_pow, rescale_X, mul_pow, smul_eq_C_mul]
  ring

/-- **Rescaling the variables.** Rescaling `x` by `u` and `y` by `v` carries the ordered product
with parameter `u h` to the ordered product with parameter `h`. -/
theorem rescale_affineStar (u v h : S) (p q : MvPolynomial (Fin 2) S) :
    rescale ![u, v] (affineStar (u * h) p q) =
      affineStar h (rescale ![u, v] p) (rescale ![u, v] q) := by
  have key : (affineStar (u * h)).compr₂ (rescale ![u, v]).toLinearMap =
      (affineStar h).compl₁₂ (rescale ![u, v]).toLinearMap (rescale ![u, v]).toLinearMap := by
    refine linearMap_ext₂_X_one_pow_mul_X_zero_pow fun a b c d ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, AlgHom.toLinearMap_apply]
    rw [rescale_X_one_pow_mul_X_zero_pow, rescale_X_one_pow_mul_X_zero_pow, map_smul,
      map_smul, LinearMap.smul_apply, affineStar_X_one_pow_mul_X_zero_pow,
      affineStar_X_one_pow_mul_X_zero_pow, map_sum, smul_sum, smul_sum]
    refine sum_congr rfl fun n hn ↦ ?_
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (mem_range.mp hn))
    simp only [← smul_eq_C_mul, map_smul, rescale_X_one_pow_mul_X_zero_pow, smul_smul,
      show n + k + d - n = k + d by omega, Matrix.cons_val_zero, Matrix.cons_val_one]
    congr 1
    ring
  exact LinearMap.congr_fun₂ key p q

section OrderedEval

variable {A : Type*} [Semiring A] [Algebra S A]

/-- Ordered evaluation: the `S`-linear map sending the ordered monomial `X 1 ^ a * X 0 ^ b` to
`y ^ a * x ^ b`, with all powers of `y` to the left of all powers of `x`; so `X 0 ↦ x` and
`X 1 ↦ y`. -/
noncomputable def orderedEval (x y : A) : MvPolynomial (Fin 2) S →ₗ[S] A :=
  (basisMonomials (Fin 2) S).constr S fun s ↦ y ^ s 1 * x ^ s 0

theorem orderedEval_X_one_pow_mul_X_zero_pow (x y : A) (a b : ℕ) :
    orderedEval x y (X 1 ^ a * X 0 ^ b : MvPolynomial (Fin 2) S) = y ^ a * x ^ b := by
  simp only [X_pow_eq_monomial, monomial_mul_monomial, mul_one]
  rw [← congrFun (coe_basisMonomials _ S), orderedEval, Module.Basis.constr_basis]
  simp

@[simp]
theorem orderedEval_monomial (x y : A) (s : Fin 2 →₀ ℕ) (a : S) :
    orderedEval x y (monomial s a) = a • (y ^ s 1 * x ^ s 0) := by
  rw [monomial_fin_two, mul_assoc, mul_comm (X 0 ^ _), ← smul_eq_C_mul, map_smul,
    orderedEval_X_one_pow_mul_X_zero_pow]

@[simp]
theorem orderedEval_one (x y : A) : orderedEval x y (1 : MvPolynomial (Fin 2) S) = 1 := by
  simpa using orderedEval_X_one_pow_mul_X_zero_pow (S := S) x y 0 0

@[simp]
theorem orderedEval_C (x y : A) (r : S) :
    orderedEval x y (C r : MvPolynomial (Fin 2) S) = algebraMap S A r := by
  rw [← mul_one (C r), ← smul_eq_C_mul, map_smul, orderedEval_one, Algebra.algebraMap_eq_smul_one]

@[simp]
theorem orderedEval_X_zero (x y : A) : orderedEval x y (X 0 : MvPolynomial (Fin 2) S) = x := by
  simpa using orderedEval_X_one_pow_mul_X_zero_pow (S := S) x y 0 1

@[simp]
theorem orderedEval_X_one (x y : A) : orderedEval x y (X 1 : MvPolynomial (Fin 2) S) = y := by
  simpa using orderedEval_X_one_pow_mul_X_zero_pow (S := S) x y 1 0

/-- **Ordered evaluation is multiplicative for the ordered product.** If `x y = y (x + h)` in an
`S`-algebra, then ordered evaluation carries the ordered product with parameter `h` to the
multiplication of the algebra. -/
theorem orderedEval_affineStar {x y : A} {h : S} (hxy : x * y = y * (x + algebraMap S A h))
    (p q : MvPolynomial (Fin 2) S) :
    orderedEval x y (affineStar h p q) = orderedEval x y p * orderedEval x y q := by
  have key : (affineStar h).compr₂ (orderedEval x y) =
      (LinearMap.mul S A).compl₁₂ (orderedEval x y) (orderedEval x y) := by
    refine linearMap_ext₂_X_one_pow_mul_X_zero_pow fun a b c d ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      affineStar_X_one_pow_mul_X_zero_pow, orderedEval_X_one_pow_mul_X_zero_pow, mul_assoc,
      ← mul_assoc (x ^ b),
      Associative.pow_mul_pow_eq_sum_smul hxy, sum_mul, mul_sum, map_sum]
    refine sum_congr rfl fun n hn ↦ ?_
    rw [Nat.sub_add_comm (Nat.lt_succ_iff.mp (mem_range.mp hn)), ← smul_eq_C_mul, map_smul,
      orderedEval_X_one_pow_mul_X_zero_pow]
    simp [pow_add, mul_assoc]
  exact LinearMap.congr_fun₂ key p q

@[simp]
theorem orderedEval_X_one_mul (x y : A) (p : MvPolynomial (Fin 2) S) :
    orderedEval x y (X 1 * p) = y * orderedEval x y p := by
  have key : orderedEval x y ∘ₗ LinearMap.mulLeft S (X 1) =
      LinearMap.mulLeft S y ∘ₗ orderedEval x y := by
    refine linearMap_ext_X_one_pow_mul_X_zero_pow fun a b ↦ ?_
    simp [orderedEval_X_one_pow_mul_X_zero_pow, ← mul_assoc, ← pow_succ']
  exact LinearMap.congr_fun key p

@[simp]
theorem orderedEval_mul_X_zero (x y : A) (p : MvPolynomial (Fin 2) S) :
    orderedEval x y (p * X 0) = orderedEval x y p * x := by
  have key : orderedEval x y ∘ₗ LinearMap.mulRight S (X 0) =
      LinearMap.mulRight S x ∘ₗ orderedEval x y := by
    refine linearMap_ext_X_one_pow_mul_X_zero_pow fun a b ↦ ?_
    simp [orderedEval_X_one_pow_mul_X_zero_pow, mul_assoc, ← pow_succ]
  exact LinearMap.congr_fun key p

@[simp]
theorem orderedEval_X_one_pow_mul (x y : A) (a : ℕ) (p : MvPolynomial (Fin 2) S) :
    orderedEval x y (X 1 ^ a * p) = y ^ a * orderedEval x y p := by
  induction a with
  | zero => simp
  | succ a ih => rw [pow_succ', mul_assoc, orderedEval_X_one_mul, ih, pow_succ', mul_assoc]

@[simp]
theorem orderedEval_mul_X_zero_pow (x y : A) (b : ℕ) (p : MvPolynomial (Fin 2) S) :
    orderedEval x y (p * X 0 ^ b) = orderedEval x y p * x ^ b := by
  induction b with
  | zero => simp
  | succ b ih => rw [pow_succ, ← mul_assoc, orderedEval_mul_X_zero, ih, pow_succ, mul_assoc]

@[simp]
theorem orderedEval_X_one_pow (x y : A) (a : ℕ) :
    orderedEval x y (X 1 ^ a : MvPolynomial (Fin 2) S) = y ^ a := by
  simpa using orderedEval_X_one_pow_mul_X_zero_pow (S := S) x y a 0

@[simp]
theorem orderedEval_X_zero_pow (x y : A) (b : ℕ) :
    orderedEval x y (X 0 ^ b : MvPolynomial (Fin 2) S) = x ^ b := by
  simpa using orderedEval_X_one_pow_mul_X_zero_pow (S := S) x y 0 b

@[simp]
theorem orderedEval_C_mul (x y : A) (r : S) (p : MvPolynomial (Fin 2) S) :
    orderedEval x y (C r * p) = algebraMap S A r * orderedEval x y p := by
  rw [← smul_eq_C_mul, map_smul, Algebra.smul_def]

@[simp]
theorem orderedEval_mul_C (x y : A) (r : S) (p : MvPolynomial (Fin 2) S) :
    orderedEval x y (p * C r) = orderedEval x y p * algebraMap S A r := by
  rw [mul_comm, orderedEval_C_mul, Algebra.commutes]

/-- Rescaling the variables by `s` before ordered evaluation rescales the evaluation points. -/
theorem orderedEval_rescale (x y : A) (s : Fin 2 → S) (p : MvPolynomial (Fin 2) S) :
    orderedEval x y (rescale s p) = orderedEval (s 0 • x) (s 1 • y) p := by
  have key : orderedEval x y ∘ₗ (rescale s).toLinearMap = orderedEval (s 0 • x) (s 1 • y) := by
    refine linearMap_ext_X_one_pow_mul_X_zero_pow fun a b ↦ ?_
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, rescale_X_one_pow_mul_X_zero_pow, map_smul,
      orderedEval_X_one_pow_mul_X_zero_pow, orderedEval_X_one_pow_mul_X_zero_pow, smul_pow,
      smul_pow, smul_mul_smul_comm]
  exact LinearMap.congr_fun key p

/-- **Naturality of ordered evaluation.** A ring homomorphism `ψ` compatible with a change of
coefficients `φ` carries ordered evaluation at `x`, `y` to ordered evaluation at `ψ x`, `ψ y` of
the polynomial with coefficients changed by `φ`. -/
theorem map_orderedEval {S' B F : Type*} [CommSemiring S'] [Semiring B] [Algebra S' B]
    [FunLike F A B] [RingHomClass F A B] (φ : S →+* S') (ψ : F)
    (hψ : ∀ s, ψ (algebraMap S A s) = algebraMap S' B (φ s)) (x y : A)
    (p : MvPolynomial (Fin 2) S) :
    ψ (orderedEval x y p) = orderedEval (ψ x) (ψ y) (map φ p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial s a => simp [Algebra.smul_def, hψ]
  | add p q hp hq => simp only [map_add, hp, hq]

end OrderedEval

end TauCeti
