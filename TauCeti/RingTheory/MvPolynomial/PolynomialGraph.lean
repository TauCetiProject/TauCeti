/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.Finsupp.Weight

import Mathlib.Algebra.MvPolynomial.Degrees
import TauCeti.Data.Finsupp.Weight
import TauCeti.RingTheory.MvPolynomial.Kronecker

/-!
# The base-`B` Kronecker substitution (`MvPolynomial.polynomialGraph`)

For a commutative semiring `k` and natural numbers `m, B`, the base-`B` Kronecker substitution
`MvPolynomial.polynomialGraph k m B : MvPolynomial (Fin m) k →+* Polynomial k` fixes constants and
sends the `i`-th variable `X i` to `T ^ (B ^ i)` (with variables numbered from zero, so
`X 0 ↦ T`). Geometrically, over a commutative ring its spectrum is the polynomial graph
`a_B : 𝔸¹_k → 𝔸^m_k`, `T ↦ (T, T ^ B, T ^ (B ^ 2), …, T ^ (B ^ (m - 1)))`.

This specialises the general Kronecker substitution of `TauCeti.RingTheory.MvPolynomial.Kronecker`
to the explicit weight `i ↦ B ^ i`. On the box of exponent vectors with all entries strictly less
than `B`, the weight `Finsupp.weight (fun i ↦ B ^ (i : ℕ))` is injective
(`Finsupp.injOn_weight_pow`), by uniqueness of base-`B` digit representations for `B ≥ 2` and
subsingleton triviality for `B ≤ 1`. Consequently, whenever `B` exceeds every exponent occurring in
a multivariate polynomial `h`, every coefficient of `h` survives as a coefficient of
`polynomialGraph k m B h` (`MvPolynomial.polynomialGraph_coeff`), and `polynomialGraph k m B` is
injective on polynomials supported in that box (`MvPolynomial.injOn_polynomialGraph`).

For `m > 0`, `polynomialGraph k m B` has the explicit right inverse `T ↦ X 0` and is therefore
surjective for every `B` (`MvPolynomial.polynomialGraph_surjective`). Over a nontrivial semiring,
surjectivity holds if and only if `0 < m`, injectivity holds if and only if `m ≤ 1`, and the
constant-term homomorphism is preserved if and only if `1 ≤ B ∨ m ≤ 1`.

## Main declarations

* `MvPolynomial.polynomialGraph`: the ring homomorphism `k[X_0, …, X_{m-1}] →+* k[T]` sending
  `X i ↦ T ^ (B ^ i)` and fixing constants.
* `MvPolynomial.polynomialGraph_eq_aeval`: `polynomialGraph k m B` is the ring homomorphism
  underlying `MvPolynomial.aeval fun i ↦ T ^ (B ^ i)`.
* `MvPolynomial.constantCoeff_comp_polynomialGraph`,
  `MvPolynomial.constantCoeff_comp_polynomialGraph_of_le_one`,
  `MvPolynomial.constantCoeff_comp_polynomialGraph_iff`: preservation of the constant term (for
  `1 ≤ B` or `m ≤ 1`, and sharp characterization `1 ≤ B ∨ m ≤ 1` when `k` is nontrivial).
* `MvPolynomial.polynomialGraph_zero`, `MvPolynomial.polynomialGraph_one`: explicit
  identifications in `0` and `1` variables.
* `MvPolynomial.polynomialGraph_comp_map`, `MvPolynomial.polynomialGraph_map`: naturality under
  coefficient ring homomorphisms.
* `MvPolynomial.polynomialGraph_injective_of_le_one`,
  `MvPolynomial.polynomialGraph_injective_iff`: injectivity for `m ≤ 1` and non-injectivity for
  `2 ≤ m` over a nontrivial semiring.
* `MvPolynomial.polynomialGraph_surjective`, `MvPolynomial.polynomialGraph_surjective_iff`:
  surjectivity for `0 < m` and non-surjectivity for `m = 0` over a nontrivial semiring.
* `MvPolynomial.polynomialGraph_coeff`: for `h` with every exponent `< B` and any `e` with every
  `e i < B`, the coefficient of `T ^ (weight (fun i ↦ B ^ i) e)` in `polynomialGraph k m B h` is
  `h.coeff e`.
* `MvPolynomial.injOn_polynomialGraph`, `MvPolynomial.polynomialGraph_eq_zero_iff`: injectivity
  and triviality of the kernel on polynomials with all exponents `< B`.
* `MvPolynomial.exists_polynomialGraph_ne_zero`: every nonzero `h` admits a base `B ≥ 2` exceeding
  all exponents of `h` such that `polynomialGraph k m B h ≠ 0`.

## References

* L. Pottmeyer, *Diophantine Approximation*, lecture notes (version of 17 January 2022), §3.3,
  Exercise 3.5(a), for the base-`B` Kronecker substitution on monomials with bounded partial
  degrees.
* M. Kisin and R. Zhou, *Independence of ℓ for Frobenius conjugacy classes attached to abelian
  varieties*, arXiv:2103.09945v2, proofs of Corollary 5.2.7 (pp. 52–53) and Proposition 5.3.5
  (p. 54), where polynomial graphs avoiding hypersurfaces are used to construct curves through
  smooth rational points over the base field.
-/

public section

noncomputable section

namespace MvPolynomial

section CommSemiring

variable {k K : Type*} [CommSemiring k] [CommSemiring K]

/-- The **base-`B` Kronecker substitution** `k[X_0, …, X_{m-1}] →+* k[T]` fixing constants and
sending `X i` to `T ^ (B ^ i)`. Because variables are indexed from zero, `X 0 ↦ T` whenever
`0 < m`. Over a commutative ring, its spectrum is the graph `T ↦ (T, T ^ B, …, T ^ (B ^ (m - 1)))`
from the affine line to `m`-dimensional affine space. -/
def polynomialGraph (k : Type*) [CommSemiring k] (m B : ℕ) :
    MvPolynomial (Fin m) k →+* Polynomial k :=
  eval₂Hom Polynomial.C fun i : Fin m ↦ Polynomial.X ^ (B ^ (i : ℕ))

/-- Explicit unfolding of `polynomialGraph` as `MvPolynomial.eval₂Hom`. -/
theorem polynomialGraph_def (k : Type*) [CommSemiring k] (m B : ℕ) :
    polynomialGraph k m B = eval₂Hom Polynomial.C fun i : Fin m ↦ Polynomial.X ^ (B ^ (i : ℕ)) :=
  (rfl)

/-- `polynomialGraph` acts as the identity on constants. -/
@[simp]
theorem polynomialGraph_C {m B : ℕ} (a : k) :
    polynomialGraph k m B (C a) = Polynomial.C a := by
  simp [polynomialGraph_def]

/-- `polynomialGraph` sends the `i`-th variable `X i` to `T ^ (B ^ i)`. -/
@[simp]
theorem polynomialGraph_X {m B : ℕ} (i : Fin m) :
    polynomialGraph k m B (X i) = Polynomial.X ^ (B ^ (i : ℕ)) := by
  simp [polynomialGraph_def]

/-- `polynomialGraph k m B` is the ring homomorphism underlying the `k`-algebra evaluation map
`MvPolynomial.aeval fun i ↦ T ^ (B ^ i)`. -/
theorem polynomialGraph_eq_aeval (k : Type*) [CommSemiring k] (m B : ℕ) :
    polynomialGraph k m B =
      (aeval fun i : Fin m ↦ (Polynomial.X : Polynomial k) ^ (B ^ (i : ℕ))).toRingHom := by
  ext <;> simp [polynomialGraph_def]

/-- `polynomialGraph` sends a monomial `a X ^ d` to `a T ^ (weight (fun i ↦ B ^ i) d)`. -/
@[simp]
theorem polynomialGraph_monomial {m B : ℕ} (d : Fin m →₀ ℕ) (a : k) :
    polynomialGraph k m B (monomial d a) =
      Polynomial.monomial (Finsupp.weight (fun i : Fin m ↦ B ^ (i : ℕ)) d) a := by
  rw [polynomialGraph_eq_aeval]
  exact aeval_X_pow_left_monomial (fun i : Fin m ↦ B ^ (i : ℕ)) d a

/-- `polynomialGraph` commutes with the constant inclusions `k →+* k[X_0, …, X_{m-1}]` and
`k →+* k[T]`. -/
@[simp]
theorem polynomialGraph_comp_C (k : Type*) [CommSemiring k] (m B : ℕ) :
    (polynomialGraph k m B).comp C = Polynomial.C := by
  ext a
  simp

/-- Evaluating `polynomialGraph k m B h` at an element `a` of a `k`-algebra `K` gives
`h(a, a ^ B, …, a ^ (B ^ (m - 1)))`. -/
@[simp]
theorem aeval_polynomialGraph [Algebra k K] {m B : ℕ} (a : K) (h : MvPolynomial (Fin m) k) :
    Polynomial.aeval a (polynomialGraph k m B h) =
      aeval (fun i : Fin m ↦ a ^ (B ^ (i : ℕ))) h := by
  induction h using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- Evaluating `polynomialGraph k m B h` at `a : k` gives `h(a, a ^ B, …, a ^ (B ^ (m - 1)))`. -/
@[simp]
theorem eval_polynomialGraph {m B : ℕ} (a : k) (h : MvPolynomial (Fin m) k) :
    (polynomialGraph k m B h).eval a = eval (fun i : Fin m ↦ a ^ (B ^ (i : ℕ))) h := by
  rw [← Polynomial.coe_aeval_eq_eval, ← aeval_eq_eval]
  exact aeval_polynomialGraph a h

/-- For `1 ≤ B`, `polynomialGraph k m B` intertwines the constant-coefficient homomorphisms
(geometrically, the graph passes through the origin). -/
@[simp]
theorem constantCoeff_comp_polynomialGraph (k : Type*) [CommSemiring k] (m : ℕ) {B : ℕ}
    (hB : 1 ≤ B) :
    Polynomial.constantCoeff.comp (polynomialGraph k m B) = constantCoeff := by
  refine ringHom_ext (fun a ↦ by simp) fun i ↦ ?_
  have hpos : B ^ (i : ℕ) ≠ 0 := (pow_pos (Nat.pos_of_ne_zero (by omega)) _).ne'
  simp [Polynomial.coeff_X_pow, hpos.symm]

/-- For `1 ≤ B`, the constant term of `polynomialGraph k m B h` equals the constant term of `h`. -/
@[simp]
theorem coeff_zero_polynomialGraph {m B : ℕ} (hB : 1 ≤ B) (h : MvPolynomial (Fin m) k) :
    (polynomialGraph k m B h).coeff 0 = h.coeff 0 :=
  DFunLike.congr_fun (constantCoeff_comp_polynomialGraph k m hB) h

/-- In at most one variable, `polynomialGraph k m B` intertwines the constant-coefficient
homomorphisms for every `B` (including `B = 0`). -/
theorem constantCoeff_comp_polynomialGraph_of_le_one (k : Type*) [CommSemiring k] {m : ℕ}
    (hm : m ≤ 1) (B : ℕ) :
    Polynomial.constantCoeff.comp (polynomialGraph k m B) = constantCoeff := by
  refine ringHom_ext (fun a ↦ by simp) fun i ↦ ?_
  have hi : (i : ℕ) = 0 := by omega
  simp [hi]

/-- Over a nontrivial commutative semiring, `polynomialGraph k m B` preserves constant terms if and
only if `1 ≤ B` or `m ≤ 1`. When `B = 0` and `2 ≤ m`, `X 1` maps to `1` rather than a polynomial
with zero constant term. -/
theorem constantCoeff_comp_polynomialGraph_iff (k : Type*) [CommSemiring k] [Nontrivial k]
    (m B : ℕ) :
    Polynomial.constantCoeff.comp (polynomialGraph k m B) = constantCoeff ↔ 1 ≤ B ∨ m ≤ 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra h'
    obtain ⟨hB0, hm⟩ : B = 0 ∧ 2 ≤ m := by omega
    subst hB0
    have hval := DFunLike.congr_fun h (X ⟨1, by omega⟩)
    simp at hval
  · rcases h with hB | hm
    · exact constantCoeff_comp_polynomialGraph k m hB
    · exact constantCoeff_comp_polynomialGraph_of_le_one k hm B

/-- In zero variables, `polynomialGraph k 0 B` is `Polynomial.C` composed with the canonical
identification `k[] ≃+* k`. -/
theorem polynomialGraph_zero (k : Type*) [CommSemiring k] (B : ℕ) :
    polynomialGraph k 0 B = Polynomial.C.comp (isEmptyRingEquiv k (Fin 0)).toRingHom := by
  refine ringHom_ext (fun a ↦ by simp) fun i ↦ i.elim0

/-- In one variable, `polynomialGraph k 1 B` is the canonical identification `k[X_0] ≃+* k[T]`
sending `X 0 ↦ T`, for every `B` including `B = 0`. -/
theorem polynomialGraph_one (k : Type*) [CommSemiring k] (B : ℕ) :
    polynomialGraph k 1 B = (uniqueAlgEquiv k (Fin 1)).toRingEquiv.toRingHom := by
  refine ringHom_ext (fun a ↦ by simp) fun i ↦ ?_
  fin_cases i
  simp

/-- `polynomialGraph` commutes with changing coefficients along a ring homomorphism
`f : k →+* K`. -/
theorem polynomialGraph_comp_map (f : k →+* K) (m B : ℕ) :
    (polynomialGraph K m B).comp (map f) =
      (Polynomial.mapRingHom f).comp (polynomialGraph k m B) := by
  refine ringHom_ext (fun a ↦ by simp) fun i ↦ by simp

/-- Naturality of `polynomialGraph` under a ring homomorphism `f : k →+* K` of the coefficients. -/
@[simp]
theorem polynomialGraph_map (f : k →+* K) (m B : ℕ) (h : MvPolynomial (Fin m) k) :
    polynomialGraph K m B (map f h) = Polynomial.map f (polynomialGraph k m B h) :=
  DFunLike.congr_fun (polynomialGraph_comp_map f m B) h

/-- In at most one variable, `polynomialGraph k m B` is injective for every `B`. -/
theorem polynomialGraph_injective_of_le_one (k : Type*) [CommSemiring k] {m : ℕ} (hm : m ≤ 1)
    (B : ℕ) : Function.Injective (polynomialGraph k m B) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl
  · rw [polynomialGraph_zero]
    exact Polynomial.C_injective.comp (isEmptyRingEquiv k (Fin 0)).injective
  · rw [polynomialGraph_one]
    exact (uniqueAlgEquiv k (Fin 1)).injective

/-- Over a nontrivial commutative semiring, `polynomialGraph k m B` is injective if and only if
`m ≤ 1`. For `2 ≤ m`, the distinct polynomials `X 1` and `X 0 ^ B` have the same image `T ^ B`. -/
theorem polynomialGraph_injective_iff (k : Type*) [CommSemiring k] [Nontrivial k] (m B : ℕ) :
    Function.Injective (polynomialGraph k m B) ↔ m ≤ 1 := by
  refine ⟨fun hinj ↦ ?_, fun hm ↦ polynomialGraph_injective_of_le_one k hm B⟩
  by_contra hm
  have h0 : 0 < m := by omega
  have h1 : 1 < m := by omega
  have heq : (X ⟨1, h1⟩ : MvPolynomial (Fin m) k) = X ⟨0, h0⟩ ^ B :=
    hinj (by simp)
  have hcoeff := congrArg (fun p : MvPolynomial (Fin m) k ↦ p.coeff (Finsupp.single ⟨1, h1⟩ 1)) heq
  have hne : Finsupp.single (⟨0, h0⟩ : Fin m) B ≠ Finsupp.single ⟨1, h1⟩ 1 := by
    intro h
    have hval := DFunLike.congr_fun h ⟨1, h1⟩
    simp at hval
  simp [X_pow_eq_monomial, coeff_monomial, hne] at hcoeff

/-- For `0 < m`, substituting `T ↦ X 0` is a right inverse to `polynomialGraph k m B`. -/
@[simp]
theorem polynomialGraph_comp_eval₂RingHom (k : Type*) [CommSemiring k] {m : ℕ} (hm : 0 < m)
    (B : ℕ) :
    (polynomialGraph k m B).comp (Polynomial.eval₂RingHom C (X ⟨0, hm⟩)) =
      RingHom.id (Polynomial k) := by
  ext <;> simp

/-- For `0 < m`, `polynomialGraph k m B` is surjective for every `B` (including `B = 0`). -/
theorem polynomialGraph_surjective (k : Type*) [CommSemiring k] {m : ℕ} (hm : 0 < m) (B : ℕ) :
    Function.Surjective (polynomialGraph k m B) :=
  Function.RightInverse.surjective (DFunLike.congr_fun (polynomialGraph_comp_eval₂RingHom k hm B))

/-- Over a nontrivial commutative semiring, `polynomialGraph k m B` is surjective if and only if
`0 < m`. For `m = 0`, the image consists only of constant polynomials and misses `T`. -/
theorem polynomialGraph_surjective_iff (k : Type*) [CommSemiring k] [Nontrivial k] (m B : ℕ) :
    Function.Surjective (polynomialGraph k m B) ↔ 0 < m := by
  refine ⟨fun hsurj ↦ ?_, fun hm ↦ polynomialGraph_surjective k hm B⟩
  by_contra hm
  have hm0 : m = 0 := by omega
  subst hm0
  obtain ⟨p, hp⟩ := hsurj Polynomial.X
  rw [polynomialGraph_zero] at hp
  have hcoeff := congrArg (fun q : Polynomial k ↦ q.coeff 1) hp
  simp at hcoeff

/-- **Coefficients survive bounded Kronecker substitution.** Over any commutative semiring, if
every exponent `d i` of every monomial in the support of `h` is strictly less than `B`, then for
every exponent vector `e` with all `e i < B`, the coefficient of
`T ^ (weight (fun i ↦ B ^ i) e)` in `polynomialGraph k m B h` equals `h.coeff e`. -/
theorem polynomialGraph_coeff {m B : ℕ} (h : MvPolynomial (Fin m) k)
    (hh : ∀ d ∈ h.support, ∀ i, d i < B) (e : Fin m →₀ ℕ) (he : ∀ i, e i < B) :
    (polynomialGraph k m B h).coeff (Finsupp.weight (fun i : Fin m ↦ B ^ (i : ℕ)) e) =
      h.coeff e := by
  rw [polynomialGraph_eq_aeval]
  exact coeff_aeval_X_pow_weight (Finsupp.injOn_weight_pow m B) hh he

/-- `polynomialGraph k m B` is injective on the polynomials all of whose exponents in every variable
are strictly less than `B`. -/
theorem injOn_polynomialGraph (k : Type*) [CommSemiring k] (m B : ℕ) :
    Set.InjOn (polynomialGraph k m B)
      {h : MvPolynomial (Fin m) k | ∀ d ∈ h.support, ∀ i, d i < B} := by
  rw [polynomialGraph_eq_aeval]
  exact (injOn_aeval_X_pow (Finsupp.injOn_weight_pow m B)).mono fun _ hh ↦
    (mem_restrictSupport_iff (R := k)).mpr hh

/-- If every exponent occurring in `h` is strictly less than `B`, then `polynomialGraph k m B h = 0`
if and only if `h = 0`. -/
theorem polynomialGraph_eq_zero_iff {m B : ℕ} {h : MvPolynomial (Fin m) k}
    (hh : ∀ d ∈ h.support, ∀ i, d i < B) :
    polynomialGraph k m B h = 0 ↔ h = 0 :=
  ⟨fun h0 ↦ injOn_polynomialGraph k m B hh (by simp) (by simpa using h0),
    fun h0 ↦ by simp [h0]⟩

/-- Every nonzero polynomial `h` in `m` variables over a commutative semiring admits a base `B ≥ 2`
strictly exceeding every exponent in the support of `h` such that `polynomialGraph k m B h ≠ 0`. -/
theorem exists_polynomialGraph_ne_zero {m : ℕ} {h : MvPolynomial (Fin m) k} (hh : h ≠ 0) :
    ∃ B : ℕ, 2 ≤ B ∧ (∀ d ∈ h.support, ∀ i, d i < B) ∧ polynomialGraph k m B h ≠ 0 := by
  have hB : ∀ d ∈ h.support, ∀ i, d i < 2 + h.totalDegree := fun d hd i ↦ by
    have hle : d i ≤ h.totalDegree :=
      (monomial_le_degreeOf i hd).trans (degreeOf_le_totalDegree h i)
    omega
  exact ⟨2 + h.totalDegree, by omega, hB, (polynomialGraph_eq_zero_iff hB).not.mpr hh⟩

end CommSemiring

end MvPolynomial
