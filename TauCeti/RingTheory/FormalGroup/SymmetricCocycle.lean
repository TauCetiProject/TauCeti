/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
-- Proof-only: coefficients of `(X + Y)ⁿ` and of differences.
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.MvPolynomial.CommRing
-- Proof-only: substitution commutes with change of coefficients.
import Mathlib.Algebra.MvPolynomial.Monad
-- Proof-only: Bézout's identity for `Finset.gcd` over the Euclidean domain `ℤ`.
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# The Lazard symmetric 2-cocycles `C_n(X, Y)`

A two-variable polynomial `f(X, Y)` over a commutative ring `R` is an *additive 2-cocycle* if

  `f(X, Y) + f(X + Y, Z) = f(X, Y + Z) + f(Y, Z)`.

Symmetric additive 2-cocycles are the first-order deformations of the additive formal group law
`X + Y`: if `F(X, Y) ≡ X + Y + f(X, Y)` modulo terms of degree `> n` and `f` is homogeneous of
degree `n`, then commutativity and associativity of `F` modulo terms of degree `> n` say exactly
that `f` is a symmetric additive 2-cocycle. This is why they govern the degree-by-degree
construction of formal group laws and Lazard's theorem that the Lazard ring is polynomial.

For `n ≥ 2` the basic example is `(X + Y)ⁿ - Xⁿ - Yⁿ`. Its coefficients `n.choose i`,
`0 < i < n`, have greatest common divisor `d_n`, which is the prime `p` when `n` is a power of `p`
and `1` otherwise (`Choose.gcd_choose_eq_minFac_of_isPrimePow`,
`Choose.gcd_choose_eq_one_of_not_isPrimePow`). Dividing by it gives the integral polynomial

  `C_n(X, Y) = ((X + Y)ⁿ - Xⁿ - Yⁿ) / d_n`,

defined here over every commutative ring by casting its natural-number coefficients. It is a
homogeneous symmetric additive 2-cocycle of degree `n`, compatible with every change of
coefficients, and its coefficients generate the unit ideal of `ℤ`. Consequently `r • C_n = 0`
forces `r = 0` in *every* commutative ring `R`, including rings with torsion: the multiple of
`C_n` representing a cocycle is unique. The converse, existence, is the symmetric 2-cocycle lemma:
every homogeneous symmetric additive 2-cocycle of degree `n` is a multiple of `C_n`.

## Main definitions

* `MvPolynomial.IsAddCocycle`: `f(X, Y) + f(X + Y, Z) = f(X, Y + Z) + f(Y, Z)`.
* `MvPolynomial.lazardCocycle n R`: the polynomial `C_n(X, Y)` over `R`.

## Main results

* `MvPolynomial.coeff_lazardCocycle`: the coefficient of `XⁱYʲ` in `C_n` is
  `n.choose i / d_n` when `i + j = n` and `i, j ≠ 0`, and `0` otherwise.
* `MvPolynomial.gcd_choose_nsmul_lazardCocycle`: `d_n • C_n = (X + Y)ⁿ - Xⁿ - Yⁿ`.
* `MvPolynomial.map_lazardCocycle`: `C_n` is compatible with ring homomorphisms.
* `MvPolynomial.isHomogeneous_lazardCocycle`, `MvPolynomial.isSymmetric_lazardCocycle`,
  `MvPolynomial.isAddCocycle_lazardCocycle`: `C_n` is a homogeneous symmetric additive 2-cocycle
  of degree `n`.
* `MvPolynomial.smul_lazardCocycle_eq_zero_iff`: for `n ≥ 2`, `r • C_n = 0 ↔ r = 0`.

## References

* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1
  (the symmetric 2-cocycle lemma).
-/

public section

open Finset

namespace MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S]

section IsAddCocycle

/-- A two-variable polynomial `f(X, Y)` is an *additive 2-cocycle* if
`f(X, Y) + f(X + Y, Z) = f(X, Y + Z) + f(Y, Z)` in `R[X, Y, Z]`. -/
def IsAddCocycle (f : MvPolynomial (Fin 2) R) : Prop :=
  (aeval ![X 0, X 1] f + aeval ![X 0 + X 1, X 2] f : MvPolynomial (Fin 3) R) =
    aeval ![X 0, X 1 + X 2] f + aeval ![X 1, X 2] f

/-- Unfolding `MvPolynomial.IsAddCocycle`. -/
theorem isAddCocycle_iff {f : MvPolynomial (Fin 2) R} :
    f.IsAddCocycle ↔
      (aeval ![X 0, X 1] f + aeval ![X 0 + X 1, X 2] f : MvPolynomial (Fin 3) R) =
        aeval ![X 0, X 1 + X 2] f + aeval ![X 1, X 2] f :=
  Iff.rfl

namespace IsAddCocycle

variable {f g : MvPolynomial (Fin 2) R}

/-- The zero polynomial is an additive 2-cocycle. -/
@[simp]
theorem zero : (0 : MvPolynomial (Fin 2) R).IsAddCocycle := by
  simp [isAddCocycle_iff]

/-- Additive 2-cocycles are closed under addition. -/
theorem add (hf : f.IsAddCocycle) (hg : g.IsAddCocycle) : (f + g).IsAddCocycle := by
  rw [isAddCocycle_iff] at *
  rw [map_add, map_add, map_add, map_add, add_add_add_comm, hf, hg, add_add_add_comm]

/-- Additive 2-cocycles are closed under scalar multiplication. -/
theorem smul (r : R) (hf : f.IsAddCocycle) : (r • f).IsAddCocycle := by
  rw [isAddCocycle_iff] at *
  simp only [map_smul, ← smul_add, hf]

/-- Additive 2-cocycles are preserved by a change of coefficients. -/
theorem map (hf : f.IsAddCocycle) (φ : R →+* S) : (MvPolynomial.map φ f).IsAddCocycle := by
  have h := congrArg (MvPolynomial.map φ) hf
  simp only [aeval_eq_bind₁, map_add, map_bind₁] at h
  rw [isAddCocycle_iff]
  simp only [aeval_eq_bind₁]
  convert h using 4 <;> funext i <;> fin_cases i <;> simp

end IsAddCocycle

end IsAddCocycle

section lazardCocycle

/-- The **Lazard 2-cocycle** `C_n(X, Y) = ((X + Y)ⁿ - Xⁿ - Yⁿ) / d_n`, where `d_n` is the greatest
common divisor of the binomial coefficients `n.choose i` for `0 < i < n` (the prime `p` if `n` is
a power of `p`, and `1` otherwise). Its coefficients are natural numbers, cast into `R`. For
`n < 2` it is `0`. -/
noncomputable def lazardCocycle (n : ℕ) (R : Type*) [CommRing R] : MvPolynomial (Fin 2) R :=
  ∑ i ∈ Icc 1 (n - 1), monomial (Finsupp.single 0 i + Finsupp.single 1 (n - i))
    ((n.choose i / (Icc 1 (n - 1)).gcd n.choose : ℕ) : R)

/-- The coefficient of `XⁱYʲ` in `C_n` is `n.choose i / d_n` if `i + j = n` and `i, j ≠ 0`, and
`0` otherwise. -/
theorem coeff_lazardCocycle (n : ℕ) (d : Fin 2 →₀ ℕ) :
    (lazardCocycle n R).coeff d =
      if d 0 + d 1 = n ∧ d 0 ≠ 0 ∧ d 1 ≠ 0 then
        ((n.choose (d 0) / (Icc 1 (n - 1)).gcd n.choose : ℕ) : R)
      else 0 := by
  classical
  have key (i : ℕ) : Finsupp.single 0 i + Finsupp.single 1 (n - i) = d ↔
      d 0 = i ∧ d 1 = n - i := by
    simp [Finsupp.ext_iff, Fin.forall_fin_two, eq_comm]
  rw [lazardCocycle, coeff_sum]
  simp only [coeff_monomial, key]
  split_ifs with h
  · rw [Finset.sum_eq_single (d 0)]
    · rw [ite_eq_left ⟨rfl, by omega⟩]
    · intro i _ hi
      rw [ite_eq_right (by omega)]
    · intro hd
      exact absurd (mem_Icc.2 ⟨by omega, by omega⟩) hd
  · refine Finset.sum_eq_zero fun i hi => ite_eq_right ?_
    rw [mem_Icc] at hi
    omega

/-- `C_n` is compatible with every change of coefficients. -/
@[simp]
theorem map_lazardCocycle (φ : R →+* S) (n : ℕ) :
    MvPolynomial.map φ (lazardCocycle n R) = lazardCocycle n S := by
  simp [lazardCocycle, map_monomial]

/-- `C_0 = C_1 = 0`. -/
theorem lazardCocycle_of_lt_two {n : ℕ} (hn : n < 2) : lazardCocycle n R = 0 := by
  rw [lazardCocycle, Finset.Icc_eq_empty (by omega), Finset.sum_empty]

/-- `C_n(X, Y)` is `((X + Y)ⁿ - Xⁿ - Yⁿ) / d_n`. -/
theorem gcd_choose_nsmul_lazardCocycle {n : ℕ} (hn : n ≠ 0) :
    (Icc 1 (n - 1)).gcd n.choose • lazardCocycle n R = (X 0 + X 1) ^ n - X 0 ^ n - X 1 ^ n := by
  classical
  ext d
  have h0 : Finsupp.single 0 n = d ↔ d 0 = n ∧ d 1 = 0 := by
    simp [Finsupp.ext_iff, Fin.forall_fin_two, eq_comm]
  have h1 : Finsupp.single 1 n = d ↔ d 0 = 0 ∧ d 1 = n := by
    simp [Finsupp.ext_iff, Fin.forall_fin_two, eq_comm]
  rw [coeff_smul, coeff_lazardCocycle, coeff_sub, coeff_sub, coeff_add_pow, coeff_X_pow,
    coeff_X_pow]
  simp only [h0, h1, mem_antidiagonal]
  by_cases h : d 0 + d 1 = n ∧ d 0 ≠ 0 ∧ d 1 ≠ 0
  · -- At `XⁱYʲ` with `i + j = n` and `i, j ≠ 0`, both sides are `n.choose i`, as `d_n` divides it.
    obtain ⟨hd, ha, hb⟩ := h
    have hcast : (((Icc 1 (n - 1)).gcd n.choose : ℕ) : R) *
        ((n.choose (d 0) / (Icc 1 (n - 1)).gcd n.choose : ℕ) : R) = n.choose (d 0) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' (gcd_dvd (mem_Icc.2 ⟨by omega, by omega⟩))]
    simp [hd, ha, hb, nsmul_eq_mul, hcast]
  · -- At `Xⁿ` and `Yⁿ` the binomial coefficient `1` cancels; all other coefficients vanish.
    rw [ite_eq_right h, smul_zero]
    obtain ⟨ha, hb⟩ | ⟨ha, hb⟩ | hd :
        (d 0 = 0 ∧ d 1 = n) ∨ (d 0 = n ∧ d 1 = 0) ∨ d 0 + d 1 ≠ n := by omega
    · simp [ha, hb, Ne.symm hn]
    · simp [ha, hb, hn]
    · simp [hd, show ¬(d 0 = n ∧ d 1 = 0) by omega, show ¬(d 0 = 0 ∧ d 1 = n) by omega]

/-- `C_n(a, b) = ((a + b)ⁿ - aⁿ - bⁿ) / d_n` for elements `a, b` of any commutative `R`-algebra. -/
theorem gcd_choose_nsmul_aeval_lazardCocycle {A : Type*} [CommRing A] [Algebra R A] {n : ℕ}
    (hn : n ≠ 0) (a b : A) :
    (Icc 1 (n - 1)).gcd n.choose • aeval ![a, b] (lazardCocycle n R) =
      (a + b) ^ n - a ^ n - b ^ n := by
  rw [← map_nsmul, gcd_choose_nsmul_lazardCocycle hn]
  simp

/-- `C_n` is homogeneous of degree `n`. -/
theorem isHomogeneous_lazardCocycle (n : ℕ) : (lazardCocycle n R).IsHomogeneous n :=
  IsHomogeneous.sum _ _ _ fun i hi => isHomogeneous_monomial _ <| by
    rw [mem_Icc] at hi
    simp only [map_add, Finsupp.degree_single]
    omega

private theorem gcd_choose_ne_zero {n : ℕ} (hn : 2 ≤ n) : (Icc 1 (n - 1)).gcd n.choose ≠ 0 :=
  Finset.gcd_ne_zero_iff.2 ⟨1, mem_Icc.2 ⟨le_rfl, by omega⟩, by simp; omega⟩

-- Over `ℤ`, multiplication by `d_n ≠ 0` is injective, so identities for `C_n` follow from the
-- corresponding identities for `(X + Y)ⁿ - Xⁿ - Yⁿ`; they then hold over every ring by base change.
private theorem isSymmetric_lazardCocycle_int (n : ℕ) : (lazardCocycle n ℤ).IsSymmetric := by
  obtain hn | hn := lt_or_ge n 2
  · rw [lazardCocycle_of_lt_two hn]
    exact IsSymmetric.zero
  intro e
  apply smul_right_injective _ (gcd_choose_ne_zero hn)
  dsimp only
  rw [← map_nsmul, gcd_choose_nsmul_lazardCocycle (by omega)]
  have hP : (X 0 + X 1) ^ n - X 0 ^ n - X 1 ^ n =
      ((∑ i, X i) ^ n - ∑ i, X i ^ n : MvPolynomial (Fin 2) ℤ) := by
    simp only [Fin.sum_univ_two]
    ring
  rw [hP]
  simp only [map_sub, map_pow, map_sum, rename_X]
  rw [Equiv.sum_comp e (fun i => (X i : MvPolynomial (Fin 2) ℤ)),
    Equiv.sum_comp e (fun i => (X i : MvPolynomial (Fin 2) ℤ) ^ n)]

private theorem isAddCocycle_lazardCocycle_int (n : ℕ) : (lazardCocycle n ℤ).IsAddCocycle := by
  obtain hn | hn := lt_or_ge n 2
  · rw [lazardCocycle_of_lt_two hn]
    exact IsAddCocycle.zero
  rw [isAddCocycle_iff]
  apply smul_right_injective _ (gcd_choose_ne_zero hn)
  dsimp only
  simp only [smul_add, gcd_choose_nsmul_aeval_lazardCocycle (by omega : n ≠ 0)]
  ring

/-- `C_n(X, Y) = C_n(Y, X)`. -/
theorem isSymmetric_lazardCocycle (n : ℕ) : (lazardCocycle n R).IsSymmetric := by
  rw [← map_lazardCocycle (Int.castRingHom R)]
  exact (isSymmetric_lazardCocycle_int n).map _

/-- `C_n` is an additive 2-cocycle. -/
theorem isAddCocycle_lazardCocycle (n : ℕ) : (lazardCocycle n R).IsAddCocycle := by
  rw [← map_lazardCocycle (Int.castRingHom R)]
  exact (isAddCocycle_lazardCocycle_int n).map _

/-- The coefficients `n.choose i / d_n`, `0 < i < n`, of `C_n` generate the unit ideal of `ℤ`. -/
private theorem exists_sum_coeff_mul_eq_one {n : ℕ} (hn : 2 ≤ n) :
    ∃ c : ℕ → ℤ,
      ∑ i ∈ Icc 1 (n - 1), ((n.choose i / (Icc 1 (n - 1)).gcd n.choose : ℕ) : ℤ) * c i = 1 := by
  set s := Icc 1 (n - 1)
  have h1 : s.gcd (fun i => n.choose i / s.gcd n.choose) = 1 :=
    Finset.gcd_div_eq_one (i := 1) (mem_Icc.2 ⟨le_rfl, by omega⟩) (by simp; omega)
  obtain ⟨c, hc⟩ := s.gcd_eq_sum_mul fun i => ((n.choose i / s.gcd n.choose : ℕ) : ℤ)
  refine ⟨c, ?_⟩
  rw [← hc]
  have hdvd : (s.gcd fun i => ((n.choose i / s.gcd n.choose : ℕ) : ℤ)).natAbs ∣ 1 := by
    rw [← h1]
    refine Finset.dvd_gcd fun i hi => ?_
    rw [← Int.natAbs_natCast (n.choose i / s.gcd n.choose)]
    exact Int.natAbs_dvd_natAbs.2 (Finset.gcd_dvd hi)
  rw [← Int.natAbs_of_nonneg Int.finsetGcd_nonneg, Nat.dvd_one.1 hdvd, Nat.cast_one]

/-- The multiple of `C_n` is unique in every commutative ring, including rings with torsion. -/
@[simp]
theorem smul_lazardCocycle_eq_zero_iff {n : ℕ} (hn : 2 ≤ n) {r : R} :
    r • lazardCocycle n R = 0 ↔ r = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, zero_smul]⟩
  have hcoeff (i : ℕ) (hi : i ∈ Icc 1 (n - 1)) :
      r * ((n.choose i / (Icc 1 (n - 1)).gcd n.choose : ℕ) : R) = 0 := by
    have := congrArg (fun p => p.coeff (Finsupp.single 0 i + Finsupp.single 1 (n - i))) h
    rw [mem_Icc] at hi
    simpa [coeff_lazardCocycle, show i ≠ 0 by omega, show n - i ≠ 0 by omega,
      show i + (n - i) = n by omega] using this
  obtain ⟨c, hc⟩ := exists_sum_coeff_mul_eq_one hn
  calc r = r * ((1 : ℤ) : R) := by simp
    _ = 0 := by
      rw [← hc, Int.cast_sum, Finset.mul_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Int.cast_mul, Int.cast_natCast, ← mul_assoc, hcoeff i hi, zero_mul]

/-- For `n ≥ 2`, `r ↦ r • C_n` is injective. -/
theorem smul_lazardCocycle_injective {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective fun r : R => r • lazardCocycle n R := fun r s h => by
  rw [← sub_eq_zero, ← smul_lazardCocycle_eq_zero_iff hn, sub_smul]
  exact sub_eq_zero.2 h

end lazardCocycle

end MvPolynomial
