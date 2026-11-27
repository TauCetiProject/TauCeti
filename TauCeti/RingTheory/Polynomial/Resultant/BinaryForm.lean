/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import TauCeti.Algebra.Polynomial.Homogenize

import TauCeti.RingTheory.Polynomial.Resultant.Basic

/-!
# The resultant of a pair of binary forms

For binary forms `F, G ∈ R[X₀, X₁]` and formal degrees `m, n`, the resultant
`Res_{m,n}(F, G)` is Mathlib's Sylvester resultant `Polynomial.resultant f g m n` of the
dehomogenisations `f = F(X, 1)` and `g = G(X, 1)`. The formal degrees are part of the data: when
the coefficient of `X₀ᵐ` in `F` vanishes, `F` has a zero at `∞ = [1 : 0]` that `F(X, 1)` does not
see, and the resultant with formal degree `m` records it. With this orientation
`Res_{d,d}(X₀ᵈ, X₁ᵈ) = 1` and `Res_{1,1}(a X₀ + b X₁, c X₀ + e X₁) = a e - b c`.

For a pair `(F₀, F₁)` of forms of degree `d` lifting a rational self-map of `ℙ¹`, the resultant
`Res_{d,d}(F₀, F₁)` measures how far the two forms are from having a common zero. The main result
of this file makes this precise in every commutative ring: for forms `F, G` of degrees `m, n` with
`m + n ≥ 1` and for each variable `X_k` there are forms `A, B` of degrees `n - 1, m - 1` with
`A F + B G = Res_{m,n}(F, G) · X_k ^ (m + n - 1)`. Evaluating this certificate at a common zero
`x` of `F` and `G` gives `Res_{m,n}(F, G) · x_k ^ (m + n - 1) = 0`, so over a ring without zero
divisors a pair of forms with nonzero resultant has no common zero besides `0`. For two forms of
degree `d` over a field with an absolute value, upper bounds for `|A(x)|` and `|B(x)|` turn the
same identity into a lower bound for `max(|F(x)|, |G(x)|)` by a multiple of
`max(|x₀|, |x₁|) ^ d`, the estimate behind canonical heights and escape rates of rational
maps.

## Main definitions

* `MvPolynomial.binaryResultant F G m n`: the resultant `Res_{m,n}(F, G)` of two binary forms
  with formal degrees `m` and `n`.

## Main results

* `MvPolynomial.binaryResultant_homogenize`: on homogenisations it is `Polynomial.resultant`.
* `MvPolynomial.binaryResultant_smul_left`, `MvPolynomial.binaryResultant_smul_right`,
  `MvPolynomial.binaryResultant_smul_smul`: behaviour under scaling of the forms.
* `MvPolynomial.binaryResultant_comm`, `MvPolynomial.binaryResultant_map`: symmetry and base
  change.
* `MvPolynomial.binaryResultant_mul_left`, `MvPolynomial.binaryResultant_mul_right`:
  bimultiplicativity, the formal degrees adding.
* `MvPolynomial.binaryResultant_X_pow_X_pow`, `MvPolynomial.binaryResultant_C_mul_X_add_C_mul_X`,
  `MvPolynomial.binaryResultant_toTupleMvPolynomial`: the resultant of `(X₀ᵐ, X₁ⁿ)`, of two linear
  forms, and of the standard lift of a polynomial map.
* `MvPolynomial.IsHomogeneous.exists_mul_add_mul_eq_C_binaryResultant_mul_X_pow`: the
  certificate `A F + B G = Res_{m,n}(F, G) · X_k ^ (m + n - 1)`.
* `MvPolynomial.IsHomogeneous.eq_zero_of_eval_eq_zero_of_binaryResultant_ne_zero`: over a ring
  without zero divisors, forms with nonzero resultant have no common nonzero zero.

## References

* J. Milnor, *Geometry and dynamics of quadratic rational maps*, Experiment. Math. 2 (1993),
  Appendix A.
* J. H. Silverman, *Lecture Notes on Arithmetic Dynamics*, Arizona Winter School (2010),
  §4.1 and §6.1.
* R. Rumely, *The minimal resultant locus*, Acta Arith. 169 (2015), §1.
-/

public section

open Polynomial

namespace MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The resultant `Res_{m,n}(F, G)` of two binary forms `F, G ∈ R[X₀, X₁]` with formal degrees
`m` and `n`: the Sylvester resultant of the dehomogenisations `F(X, 1)` and `G(X, 1)` taken with
formal degrees `m` and `n`. For forms homogeneous of degrees `m` and `n` it is the classical
resultant of binary forms, normalised by `Res_{d,d}(X₀ᵈ, X₁ᵈ) = 1`. -/
noncomputable def binaryResultant (F G : MvPolynomial (Fin 2) R) (m n : ℕ) : R :=
  (aeval ![Polynomial.X, 1] F : R[X]).resultant (aeval ![Polynomial.X, 1] G) m n

/-- Unfolding `MvPolynomial.binaryResultant` into Mathlib's resultant of the dehomogenisations. -/
theorem binaryResultant_def (F G : MvPolynomial (Fin 2) R) (m n : ℕ) :
    F.binaryResultant G m n =
      (aeval ![Polynomial.X, 1] F : R[X]).resultant (aeval ![Polynomial.X, 1] G) m n :=
  (rfl)

/-- On homogenisations, the resultant of binary forms is Mathlib's resultant of the
polynomials. No degree bound is needed: homogenising in degree `m` keeps exactly the coefficients
of index at most `m`, which are the ones the resultant with formal degree `m` uses. -/
@[simp]
theorem binaryResultant_homogenize (p q : R[X]) (m n : ℕ) :
    (p.homogenize m).binaryResultant (q.homogenize n) m n = p.resultant q m n := by
  rw [binaryResultant_def]
  exact resultant_congr_of_coeff_eq (fun i hi ↦ coeff_aeval_homogenize_X_one p hi)
    (fun i hi ↦ coeff_aeval_homogenize_X_one q hi)

/-- Scaling the first form by `c` scales the resultant by `c ^ n`. -/
@[simp]
theorem binaryResultant_smul_left (c : R) (F G : MvPolynomial (Fin 2) R) (m n : ℕ) :
    (c • F).binaryResultant G m n = c ^ n * F.binaryResultant G m n := by
  rw [binaryResultant_def, map_smul, Polynomial.smul_eq_C_mul, resultant_C_mul_left,
    binaryResultant_def]

/-- Scaling the second form by `c` scales the resultant by `c ^ m`. -/
@[simp]
theorem binaryResultant_smul_right (c : R) (F G : MvPolynomial (Fin 2) R) (m n : ℕ) :
    F.binaryResultant (c • G) m n = c ^ m * F.binaryResultant G m n := by
  rw [binaryResultant_def, map_smul, Polynomial.smul_eq_C_mul, resultant_C_mul_right,
    binaryResultant_def]

/-- Scaling both forms by `c` scales the resultant by `c ^ (m + n)`. For the two forms of degree
`d` of a homogeneous lift of a rational map this is `c ^ (2 d)`, so the resultant of the map is
defined up to `(Rˣ) ^ (2 d)`. -/
theorem binaryResultant_smul_smul (c : R) (F G : MvPolynomial (Fin 2) R) (m n : ℕ) :
    (c • F).binaryResultant (c • G) m n = c ^ (m + n) * F.binaryResultant G m n := by
  rw [binaryResultant_smul_left, binaryResultant_smul_right, ← mul_assoc, ← pow_add, add_comm]

/-- Swapping the two forms multiplies the resultant by `(-1) ^ (m n)`. -/
theorem binaryResultant_comm (F G : MvPolynomial (Fin 2) R) (m n : ℕ) :
    F.binaryResultant G m n = (-1) ^ (m * n) * G.binaryResultant F n m := by
  rw [binaryResultant_def, resultant_comm, binaryResultant_def]

/-- The resultant of binary forms commutes with base change. -/
@[simp]
theorem binaryResultant_map (φ : R →+* S) (F G : MvPolynomial (Fin 2) R) (m n : ℕ) :
    (F.map φ).binaryResultant (G.map φ) m n = φ (F.binaryResultant G m n) := by
  rw [binaryResultant_def, aeval_X_one_map, aeval_X_one_map, resultant_map_map,
    binaryResultant_def]

/-- The resultant of the zero form with a form of positive formal degree vanishes. -/
@[simp]
theorem binaryResultant_zero_left (G : MvPolynomial (Fin 2) R) (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (0 : MvPolynomial (Fin 2) R).binaryResultant G m n = 0 := by
  rw [binaryResultant_def, map_zero, resultant_zero_left, zero_pow hn, zero_mul]

/-- The resultant of a form of positive formal degree with the zero form vanishes. -/
@[simp]
theorem binaryResultant_zero_right (F : MvPolynomial (Fin 2) R) {m : ℕ} (n : ℕ) (hm : m ≠ 0) :
    F.binaryResultant 0 m n = 0 := by
  rw [binaryResultant_def, map_zero, resultant_zero_right, zero_pow hm, zero_mul]

/-- The normalisation `Res_{m,n}(X₀ᵐ, X₁ⁿ) = 1`; in particular `Res_{d,d}(X₀ᵈ, X₁ᵈ) = 1`. -/
@[simp]
theorem binaryResultant_X_pow_X_pow (m n : ℕ) :
    (X 0 ^ m : MvPolynomial (Fin 2) R).binaryResultant (X 1 ^ n) m n = 1 := by
  have h₀ : (aeval ![Polynomial.X, 1] (X 0 ^ m : MvPolynomial (Fin 2) R) : R[X]) =
      Polynomial.X ^ m := by simp
  have h₁ : (aeval ![Polynomial.X, 1] (X 1 ^ n : MvPolynomial (Fin 2) R) : R[X]) = 1 := by simp
  rw [binaryResultant_def, h₀, h₁, resultant_one_right, coeff_X_pow_self, one_pow]

/-- `Res_{n,m}(X₁ⁿ, X₀ᵐ) = (-1) ^ (m n)`, which pins down the orientation of the resultant; in
particular `Res_{d,d}(X₁ᵈ, X₀ᵈ) = (-1) ^ (d d) = (-1) ^ d`. -/
@[simp]
theorem binaryResultant_X_pow_X_pow_swap (m n : ℕ) :
    (X 1 ^ n : MvPolynomial (Fin 2) R).binaryResultant (X 0 ^ m) n m = (-1) ^ (m * n) := by
  rw [binaryResultant_comm, binaryResultant_X_pow_X_pow, mul_one, mul_comm]

/-- The resultant of two linear forms is the determinant of their coefficient matrix:
`Res_{1,1}(a X₀ + b X₁, c X₀ + e X₁) = a e - b c`. -/
theorem binaryResultant_C_mul_X_add_C_mul_X (a b c e : R) :
    (C a * X 0 + C b * X 1 : MvPolynomial (Fin 2) R).binaryResultant (C c * X 0 + C e * X 1)
      1 1 = a * e - b * c := by
  have h₀ : (aeval ![Polynomial.X, 1] (C a * X 0 + C b * X 1 : MvPolynomial (Fin 2) R) : R[X]) =
      Polynomial.C a * Polynomial.X + Polynomial.C b := by simp
  have h₁ : (aeval ![Polynomial.X, 1] (C c * X 0 + C e * X 1 : MvPolynomial (Fin 2) R) : R[X]) =
      Polynomial.C c * Polynomial.X + Polynomial.C e := by simp
  rw [binaryResultant_def, h₀, h₁, resultant_C_mul_X_add_C_C_mul_X_add_C]

/-- The standard lift `(p.homogenize p.natDegree, X₁ ^ p.natDegree)` of a polynomial map has
resultant `p.leadingCoeff ^ p.natDegree`. -/
@[simp]
theorem binaryResultant_toTupleMvPolynomial (p : R[X]) :
    (p.toTupleMvPolynomial 0).binaryResultant (p.toTupleMvPolynomial 1) p.natDegree
      p.natDegree = p.leadingCoeff ^ p.natDegree := by
  have h₁ : (aeval ![Polynomial.X, 1] (p.toTupleMvPolynomial 1) : R[X]) = 1 := by
    simp [toTupleMvPolynomial_one_eq]
  rw [binaryResultant_def, toTupleMvPolynomial_zero_eq, aeval_homogenize_X_one _ le_rfl, h₁,
    resultant_one_right, coeff_natDegree]

/-- **Bimultiplicativity of the resultant**, in the first form: for binary forms `F₁, F₂, G`
homogeneous of degrees `m₁, m₂, n`,
`Res_{m₁+m₂,n}(F₁ F₂, G) = Res_{m₁,n}(F₁, G) · Res_{m₂,n}(F₂, G)`. -/
theorem binaryResultant_mul_left {F₁ F₂ G : MvPolynomial (Fin 2) R} {m₁ m₂ n : ℕ}
    (hF₁ : F₁.IsHomogeneous m₁) (hF₂ : F₂.IsHomogeneous m₂) (hG : G.IsHomogeneous n) :
    (F₁ * F₂).binaryResultant G (m₁ + m₂) n =
      F₁.binaryResultant G m₁ n * F₂.binaryResultant G m₂ n := by
  rw [binaryResultant_def, map_mul, resultant_mul_left_of_natDegree_le
    hF₁.natDegree_aeval_X_one_le hF₂.natDegree_aeval_X_one_le hG.natDegree_aeval_X_one_le,
    binaryResultant_def, binaryResultant_def]

/-- **Bimultiplicativity of the resultant**, in the second form: for binary forms `F, G₁, G₂`
homogeneous of degrees `m, n₁, n₂`,
`Res_{m,n₁+n₂}(F, G₁ G₂) = Res_{m,n₁}(F, G₁) · Res_{m,n₂}(F, G₂)`. -/
theorem binaryResultant_mul_right {F G₁ G₂ : MvPolynomial (Fin 2) R} {m n₁ n₂ : ℕ}
    (hF : F.IsHomogeneous m) (hG₁ : G₁.IsHomogeneous n₁) (hG₂ : G₂.IsHomogeneous n₂) :
    F.binaryResultant (G₁ * G₂) m (n₁ + n₂) =
      F.binaryResultant G₁ m n₁ * F.binaryResultant G₂ m n₂ := by
  rw [binaryResultant_comm F, binaryResultant_mul_left hG₁ hG₂ hF, binaryResultant_comm F G₁,
    binaryResultant_comm F G₂, mul_add, pow_add]
  ring

namespace IsHomogeneous

/-- **The resultant as a Nullstellensatz certificate.** Let `F` and `G` be binary forms over a
commutative ring, homogeneous of degrees `m` and `n` with `m + n ≥ 1`. For each variable `X_k`
there are binary forms `A` and `B`, homogeneous of degrees `n - 1` and `m - 1`, with
`A F + B G = Res_{m,n}(F, G) · X_k ^ (m + n - 1)`. -/
theorem exists_mul_add_mul_eq_C_binaryResultant_mul_X_pow {F G : MvPolynomial (Fin 2) R}
    {m n : ℕ} (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) (hmn : m ≠ 0 ∨ n ≠ 0)
    (k : Fin 2) :
    ∃ A B : MvPolynomial (Fin 2) R, A.IsHomogeneous (n - 1) ∧ B.IsHomogeneous (m - 1) ∧
      A * F + B * G = C (F.binaryResultant G m n) * X k ^ (m + n - 1) := by
  -- Dehomogenise: `F = f.homogenize m` and `G = g.homogenize n` with `deg f ≤ m`, `deg g ≤ n`.
  set f : R[X] := MvPolynomial.aeval ![Polynomial.X, 1] F
  set g : R[X] := MvPolynomial.aeval ![Polynomial.X, 1] G
  have hf : f.natDegree ≤ m := hF.natDegree_aeval_X_one_le
  have hg : g.natDegree ≤ n := hG.natDegree_aeval_X_one_le
  -- The polynomial `P` whose homogenisation in degree `m + n - 1` is `X_k ^ (m + n - 1)`.
  set P : R[X] := if k = 0 then Polynomial.X ^ (m + n - 1) else 1 with hP
  have hPle : P.degree ≤ (m + n - 1 : ℕ) := by
    rw [hP]
    split_ifs
    · exact degree_X_pow_le _
    · exact degree_one_le.trans (by exact_mod_cast Nat.zero_le _)
  -- `m + n - 1 < m + n` since `m + n ≥ 1`.
  have hPdeg : P.degree < ↑(m + n) := hPle.trans_lt (by exact_mod_cast Nat.sub_lt (by lia) one_pos)
  have hPh : P.homogenize (m + n - 1) = X k ^ (m + n - 1) := by
    fin_cases k <;> simp [hP]
  obtain ⟨p, q, hp, hq, key⟩ := exists_mul_add_mul_eq_C_resultant_mul hf hg hPdeg
  refine ⟨p.homogenize (n - 1), q.homogenize (m - 1),
    isHomogeneous_homogenize _, isHomogeneous_homogenize _, ?_⟩
  -- Homogenise `f p + g q = Res · P` in degree `m + n - 1`.
  have hgq := homogenize_mul_of_degree_lt g q hg hq
  rw [add_comm n m] at hgq
  have h := congr(homogenize $key (m + n - 1))
  rw [homogenize_add, homogenize_mul_of_degree_lt f p hf hp, hgq, homogenize_C_mul, hPh,
    homogenize_eq_of_isHomogeneous hF rfl, homogenize_eq_of_isHomogeneous hG rfl] at h
  rw [binaryResultant_def, ← h, mul_comm _ F, mul_comm _ G]

/-- At a common zero `x` of binary forms `F` and `G` of degrees `m` and `n` with `m + n ≥ 1`, the
resultant satisfies `Res_{m,n}(F, G) · x_k ^ (m + n - 1) = 0` for each coordinate `x_k`. -/
theorem binaryResultant_mul_pow_eq_zero_of_eval_eq_zero {F G : MvPolynomial (Fin 2) R}
    {m n : ℕ} (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) (hmn : m ≠ 0 ∨ n ≠ 0)
    {x : Fin 2 → R} (hFx : eval x F = 0) (hGx : eval x G = 0) (k : Fin 2) :
    F.binaryResultant G m n * x k ^ (m + n - 1) = 0 := by
  obtain ⟨A, B, -, -, h⟩ := hF.exists_mul_add_mul_eq_C_binaryResultant_mul_X_pow hG hmn k
  simpa [hFx, hGx] using congr(eval x $h).symm

/-- Over a ring without zero divisors, binary forms of degrees `m` and `n` with `m + n ≥ 1` and
nonzero resultant `Res_{m,n}(F, G)` have no common zero besides `0`. -/
theorem eq_zero_of_eval_eq_zero_of_binaryResultant_ne_zero [NoZeroDivisors R]
    {F G : MvPolynomial (Fin 2) R} {m n : ℕ} (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hmn : m ≠ 0 ∨ n ≠ 0) (hres : F.binaryResultant G m n ≠ 0) {x : Fin 2 → R}
    (hFx : eval x F = 0) (hGx : eval x G = 0) : x = 0 := by
  funext k
  exact eq_zero_of_pow_eq_zero <| (mul_eq_zero.mp <|
    hF.binaryResultant_mul_pow_eq_zero_of_eval_eq_zero hG hmn hFx hGx k).resolve_left hres

end IsHomogeneous

end MvPolynomial
