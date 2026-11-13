/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.Generators
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Tactic.LinearCombination

/-!
# The rational power-sum presentation of the symmetric functions

Newton's identities `(n + 1) e_(n + 1) = ∑_{i + j = n} (-1)ʲ eᵢ p_(j + 1)` hold in the ring `Λ_R`
of symmetric functions over every commutative ring, since they hold in every finite alphabet.
When `R` is a `ℚ`-algebra they can be solved for `e_(n + 1)`, so the power sums `p₁, p₂, …`
generate `Λ_R`; comparing with the free generation by the elementary symmetric functions shows that
they are algebraically independent as well. Over `ℤ` this fails: `p₁² - p₂ = 2 e₂`, and `e₂` is not
a polynomial in the power sums.

The inverse of the presentation is described by the polynomials `E_n` in the variables `X r`,
which stand for `p_(r + 1)`, determined by `E₀ = 1` and Newton's recursion
`E_(n + 1) = (1 / (n + 1)) ∑_{i + j = n} (-1)ʲ Eᵢ X_j`. Here `1 / (n + 1)` is the image in `R` of a
rational number, so no division is asserted in `R` itself. The polynomial `E_n` is homogeneous of
degree `n` for the weight `X r ↦ r + 1`, does not depend on the coefficient ring, and specialises in
`d` variables to Newton's expression of `e_n` through the power sums.

## Main definitions

* `TauCeti.SymmetricFunction.psumAlgHom R`: the algebra homomorphism `R[X₀, X₁, …] → Λ_R` sending
  `X r` to `p_(r + 1)`.
* `TauCeti.SymmetricFunction.esymmPsumPoly R n`: for a `ℚ`-algebra `R`, the polynomial `E_n`
  expressing `e_n` through the power sums.
* `TauCeti.SymmetricFunction.psumAlgEquiv R`: for a `ℚ`-algebra `R`, the power-sum presentation
  `R[X₀, X₁, …] ≃ₐ[R] Λ_R`.

## Main results

* `TauCeti.SymmetricFunction.mul_of_stableEsymm_eq_sum`: **Newton's identities** in `Λ_R`.
* `TauCeti.SymmetricFunction.psumAlgHom_esymmPsumPoly`: `E_n` evaluated at the power sums is `e_n`.
* `TauCeti.SymmetricFunction.psumAlgEquiv_symm_of_stableEsymm`,
  `TauCeti.SymmetricFunction.psumAlgEquiv_symm_of_stablePsum`: the inverse of the presentation
  sends `e_n` to `E_n` and `p_(r + 1)` to `X r`.
* `TauCeti.SymmetricFunction.algHom_ext_of_stablePsum`: over a `ℚ`-algebra, algebra homomorphisms
  out of `Λ_R` agree once they agree on the power sums.
* `TauCeti.SymmetricFunction.aeval_psum_esymmPsumPoly`: in `d` variables, `E_n` evaluated at the
  power sums is the elementary symmetric polynomial `e_n`.
* `TauCeti.SymmetricFunction.map_esymmPsumPoly`: `E_n` is natural in the coefficient ring.
* `TauCeti.SymmetricFunction.psumAlgHom_weightedHomogeneousComponent`,
  `TauCeti.SymmetricFunction.isWeightedHomogeneous_psumAlgEquiv_symm_of`: the presentation
  identifies the weighted grading `deg X_r = r + 1` with the grading of `Λ_R`.
* `TauCeti.SymmetricFunction.two_mul_esymmPsumPoly_two`,
  `TauCeti.SymmetricFunction.six_mul_esymmPsumPoly_three`: `2 e₂ = p₁² - p₂` and
  `6 e₃ = p₁³ - 3 p₁ p₂ + 2 p₃`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 2: Newton's identities (2.11′), the power sums as free generators of `Λ_ℚ` (2.12), and
  the expression of `e_n` through the power sums (2.14′).
-/

public section

namespace TauCeti

open MvPolynomial DirectSum Finset

namespace SymmetricFunction

section CommSemiring

variable (R : Type*) [CommSemiring R]

/-- The algebra homomorphism from polynomials in countably many variables to the symmetric functions
sending the variable `X r` to the power sum `p_(r + 1)`. There is no stable `p₀`, so the variables
are shifted by one. -/
noncomputable def psumAlgHom : MvPolynomial ℕ R →ₐ[R] SymmetricFunction R :=
  aeval fun r => DirectSum.of _ (r + 1) (stablePsum R r.succ_ne_zero)

/-- The variable `X r` is sent to the power sum `p_(r + 1)`. -/
@[simp]
theorem psumAlgHom_X (r : ℕ) :
    psumAlgHom R (X r) = DirectSum.of _ (r + 1) (stablePsum R r.succ_ne_zero) :=
  aeval_X _ _

/-- In `d` variables, `TauCeti.SymmetricFunction.psumAlgHom` substitutes the power sums
`p₁, p₂, …`. -/
theorem specialization_psumAlgHom (d : ℕ) (p : MvPolynomial ℕ R) :
    specialization R d (psumAlgHom R p) = aeval (fun r => psum (Fin d) R (r + 1)) p := by
  have h : (specialization R d).comp (psumAlgHom R) = aeval fun r => psum (Fin d) R (r + 1) :=
    MvPolynomial.algHom_ext fun r => by simp
  exact DFunLike.congr_fun h p

/-- Products of symmetric functions of degrees `i` and `j` have degree `i + j`. -/
private theorem mul_mem_range_of {x y : SymmetricFunction R} {i j k : ℕ} (hk : i + j = k)
    (hx : x ∈ Set.range (DirectSum.of _ i)) (hy : y ∈ Set.range (DirectSum.of _ j)) :
    x * y ∈ Set.range (DirectSum.of _ k) := by
  subst hk
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨_, (DirectSum.of_mul_of (A := fun n => stableSymmetricSubmodule R n) a b).symm⟩

/-- A monomial of weighted degree `k` is sent to a symmetric function of degree `k`. -/
private theorem psumAlgHom_monomial_mem_range (s : ℕ →₀ ℕ) (a : R) {k : ℕ}
    (hk : Finsupp.weight (· + 1) s = k) :
    psumAlgHom R (monomial s a) ∈ Set.range (DirectSum.of _ k) := by
  induction s using Finsupp.induction generalizing k with
  | zero =>
    rw [map_zero] at hk
    subst hk
    refine ⟨a • stableSymmetricOne R, ?_⟩
    rw [DirectSum.of_smul, of_stableSymmetricOne, monomial_zero', algHom_C,
      Algebra.algebraMap_eq_smul_one]
  | single_add r b s _ _ ih =>
    have hpow : ∀ m : ℕ, psumAlgHom R (X r ^ m) ∈ Set.range (DirectSum.of _ (m * (r + 1))) := by
      intro m
      induction m with
      | zero =>
        rw [zero_mul]
        exact ⟨stableSymmetricOne R, by rw [of_stableSymmetricOne, pow_zero, map_one]⟩
      | succ m ihm =>
        rw [pow_succ, map_mul]
        exact mul_mem_range_of R (by ring) ihm ⟨_, (psumAlgHom_X R r).symm⟩
    rw [monomial_single_add, map_mul]
    refine mul_mem_range_of R ?_ (hpow b) (ih rfl)
    rw [← hk, map_add, Finsupp.weight_single, smul_eq_mul]

/-- **The power-sum homomorphism is graded**: it sends the component of weighted degree `n`, for
the weight `X r ↦ r + 1`, to the component of degree `n`. -/
theorem psumAlgHom_weightedHomogeneousComponent (n : ℕ) (p : MvPolynomial ℕ R) :
    psumAlgHom R (weightedHomogeneousComponent (· + 1) n p) =
      DirectSum.of _ n (psumAlgHom R p n) := by
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
    have hs := isWeightedHomogeneous_monomial (· + 1) s a rfl
    obtain ⟨y, hy⟩ := psumAlgHom_monomial_mem_range R s a rfl
    rw [← hy]
    obtain rfl | hn := eq_or_ne (Finsupp.weight (· + 1) s) n
    · rw [hs.weightedHomogeneousComponent_same, ← hy, DirectSum.of_eq_same]
    · rw [hs.weightedHomogeneousComponent_ne _ (Ne.symm hn), map_zero,
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hn), map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, DirectSum.add_apply, map_add]

end CommSemiring

section CommRing

variable (R : Type*) [CommRing R]

/-- **Newton's identities** in the symmetric functions:
`(n + 1) e_(n + 1) = ∑_{i + j = n} (-1)ʲ eᵢ p_(j + 1)`. -/
theorem mul_of_stableEsymm_eq_sum (n : ℕ) :
    (n + 1 : SymmetricFunction R) * DirectSum.of _ (n + 1) (stableEsymm R (n + 1)) =
      ∑ x ∈ antidiagonal n, (-1) ^ x.2 * DirectSum.of _ x.1 (stableEsymm R x.1) *
        psumAlgHom R (X x.2) := by
  refine ext_specialization fun d => ?_
  have h := MvPolynomial.mul_esymm_eq_sum (Fin d) R (n + 1)
  rw [sum_filter, Nat.sum_antidiagonal_succ', mul_add, mul_sum] at h
  simp only [lt_irrefl, ↓reduceIte, mul_zero, zero_add] at h
  simp only [map_mul, map_add, map_natCast, map_one, specialization_of,
    coe_stableSymmetricProj_stableEsymm, map_sum, map_pow, map_neg, psumAlgHom_X,
    coe_stableSymmetricProj_stablePsum, Nat.cast_add, Nat.cast_one] at h ⊢
  rw [h]
  refine sum_congr rfl fun x hx => ?_
  rw [mem_antidiagonal] at hx
  subst hx
  simp only [show x.1 < x.1 + x.2 + 1 by omega, ↓reduceIte]
  rw [← mul_assoc, ← mul_assoc, ← pow_add,
    show x.1 + x.2 + 1 + 1 + x.1 = x.2 + 2 * (x.1 + 1) by ring, pow_add, pow_mul]
  simp

end CommRing

section Rat

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- Multiplying by `n + 1` cancels the scalar `1 / (n + 1)` coming from `ℚ`. -/
private theorem natCast_add_one_mul_algebraMap_inv_smul {A : Type*} [Semiring A] [Algebra R A]
    (n : ℕ) (a : A) : ((n : A) + 1) * (algebraMap ℚ R ((n : ℚ) + 1)⁻¹ • a) = a := by
  have h : ((n : R) + 1) * algebraMap ℚ R ((n : ℚ) + 1)⁻¹ = 1 := by
    rw [show ((n : R) + 1) = algebraMap ℚ R ((n : ℚ) + 1) by simp, ← map_mul,
      mul_inv_cancel₀ (by positivity), map_one]
  rw [Algebra.smul_def, ← mul_assoc, show ((n : A) + 1) = algebraMap R A ((n : R) + 1) by simp,
    ← map_mul, h, map_one, one_mul]

/-- The polynomial `E_n` in the variables `X r`, standing for the power sums `p_(r + 1)`, which
expresses the elementary symmetric function `e_n` over a `ℚ`-algebra: `E₀ = 1` and
`E_(n + 1) = (1 / (n + 1)) ∑_{i + j = n} (-1)ʲ Eᵢ X_j`, Newton's recursion. -/
noncomputable def esymmPsumPoly : ℕ → MvPolynomial ℕ R
  | 0 => 1
  | n + 1 => algebraMap ℚ R ((n : ℚ) + 1)⁻¹ •
      ∑ x ∈ (antidiagonal n).attach, (-1) ^ x.1.2 * esymmPsumPoly x.1.1 * X x.1.2
decreasing_by
  have := Nat.antidiagonal.fst_lt x.2
  omega

@[simp]
theorem esymmPsumPoly_zero : esymmPsumPoly R 0 = 1 := by
  rw [esymmPsumPoly]

/-- **Newton's recursion** for `TauCeti.SymmetricFunction.esymmPsumPoly`. -/
theorem esymmPsumPoly_succ (n : ℕ) :
    esymmPsumPoly R (n + 1) = algebraMap ℚ R ((n : ℚ) + 1)⁻¹ •
      ∑ x ∈ antidiagonal n, (-1) ^ x.2 * esymmPsumPoly R x.1 * X x.2 := by
  rw [esymmPsumPoly]
  congr 1
  exact sum_attach (antidiagonal n) fun x => (-1) ^ x.2 * esymmPsumPoly R x.1 * X x.2

/-- Newton's recursion for `TauCeti.SymmetricFunction.esymmPsumPoly` with the denominator cleared:
`(n + 1) E_(n + 1) = ∑_{i + j = n} (-1)ʲ Eᵢ X_j`. -/
theorem mul_esymmPsumPoly_succ (n : ℕ) :
    (n + 1 : MvPolynomial ℕ R) * esymmPsumPoly R (n + 1) =
      ∑ x ∈ antidiagonal n, (-1) ^ x.2 * esymmPsumPoly R x.1 * X x.2 := by
  rw [esymmPsumPoly_succ, natCast_add_one_mul_algebraMap_inv_smul]

@[simp]
theorem esymmPsumPoly_one : esymmPsumPoly R 1 = X 0 := by
  simp [esymmPsumPoly_succ]

/-- `2 e₂ = p₁² - p₂`. -/
theorem two_mul_esymmPsumPoly_two : 2 * esymmPsumPoly R 2 = X 0 ^ 2 - X 1 := by
  have h := mul_esymmPsumPoly_succ R 1
  norm_num [Nat.antidiagonal_succ] at h
  linear_combination h

/-- `6 e₃ = p₁³ - 3 p₁ p₂ + 2 p₃`. -/
theorem six_mul_esymmPsumPoly_three :
    6 * esymmPsumPoly R 3 = X 0 ^ 3 - 3 * X 0 * X 1 + 2 * X 2 := by
  have h := mul_esymmPsumPoly_succ R 2
  norm_num [Nat.antidiagonal_succ] at h
  linear_combination 2 * h + X 0 * two_mul_esymmPsumPoly_two R

/-- **`E_n` evaluated at the power sums is the elementary symmetric function** `e_n`. -/
@[simp]
theorem psumAlgHom_esymmPsumPoly (n : ℕ) :
    psumAlgHom R (esymmPsumPoly R n) = DirectSum.of _ n (stableEsymm R n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain _ | n := n
    · simp
    have hsum : psumAlgHom R (∑ x ∈ antidiagonal n, (-1) ^ x.2 * esymmPsumPoly R x.1 * X x.2) =
        (n + 1 : SymmetricFunction R) * DirectSum.of _ (n + 1) (stableEsymm R (n + 1)) := by
      rw [mul_of_stableEsymm_eq_sum, map_sum]
      refine sum_congr rfl fun x hx => ?_
      rw [map_mul, map_mul, map_pow, map_neg, map_one,
        ih x.1 (Nat.antidiagonal.fst_lt hx)]
    rw [esymmPsumPoly_succ, map_smul, hsum, ← mul_smul_comm,
      natCast_add_one_mul_algebraMap_inv_smul]

/-- In `d` variables, `E_n` evaluated at the power sums `p₁, p₂, …` is the elementary symmetric
polynomial `e_n`. -/
theorem aeval_psum_esymmPsumPoly (d n : ℕ) :
    aeval (fun r => psum (Fin d) R (r + 1)) (esymmPsumPoly R n) = esymm (Fin d) R n := by
  rw [← specialization_psumAlgHom, psumAlgHom_esymmPsumPoly, specialization_of,
    coe_stableSymmetricProj_stableEsymm]

/-- **`E_n` does not depend on the coefficient ring**: it is natural in ring homomorphisms between
`ℚ`-algebras. -/
theorem map_esymmPsumPoly {S : Type*} [CommRing S] [Algebra ℚ S] (f : R →+* S) (n : ℕ) :
    map f (esymmPsumPoly R n) = esymmPsumPoly S n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain _ | n := n
    · simp
    rw [esymmPsumPoly_succ, esymmPsumPoly_succ, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C,
      RingHom.map_rat_algebraMap, map_sum]
    congr 1
    refine sum_congr rfl fun x hx => ?_
    rw [map_mul, map_mul, map_pow, map_neg, map_one, map_X,
      ih x.1 (Nat.antidiagonal.fst_lt hx)]

/-- `E_n` is homogeneous of degree `n` for the weight `X r ↦ r + 1`. -/
theorem isWeightedHomogeneous_esymmPsumPoly (n : ℕ) :
    IsWeightedHomogeneous (· + 1) (esymmPsumPoly R n) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain _ | n := n
    · simpa using isWeightedHomogeneous_one R (· + 1)
    rw [esymmPsumPoly_succ, smul_eq_C_mul]
    refine IsWeightedHomogeneous.C_mul (IsWeightedHomogeneous.sum _ _ _ fun x hx => ?_) _
    have hx' := mem_antidiagonal.mp hx
    have h := (((isWeightedHomogeneous_one R (· + 1)).neg.pow x.2).mul
      (ih x.1 (Nat.antidiagonal.fst_lt hx))).mul (isWeightedHomogeneous_X R (· + 1) x.2)
    convert h using 1
    simp only [smul_zero, zero_add]
    omega

/-- The algebra homomorphism `R[X₀, X₁, …] → R[X₀, X₁, …]` sending `X r` to `E_(r + 1)`, the
inverse of the power-sum presentation read in the elementary generators. -/
private noncomputable def esymmPsumAlgHom : MvPolynomial ℕ R →ₐ[R] MvPolynomial ℕ R :=
  aeval fun r => esymmPsumPoly R (r + 1)

private theorem psumAlgHom_comp_esymmPsumAlgHom :
    (psumAlgHom R).comp (esymmPsumAlgHom R) = SymmetricFunction.esymmAlgHom R :=
  MvPolynomial.algHom_ext fun r => by simp [esymmPsumAlgHom]

/-- Each variable `X r` is a polynomial in the `E_n`: Newton's recursion at `n = r` isolates the
term `(-1)ʳ X r`, and the other terms involve only `X j` for `j < r`. -/
private theorem esymmPsumAlgHom_surjective : Function.Surjective (esymmPsumAlgHom R) := by
  have hE : ∀ n, esymmPsumPoly R n ∈ (esymmPsumAlgHom R).range := by
    rintro (_ | n)
    · simp
    · exact ⟨X n, by simp [esymmPsumAlgHom]⟩
  have hX : ∀ r, X r ∈ (esymmPsumAlgHom R).range := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      have h := mul_esymmPsumPoly_succ R r
      rw [← add_sum_erase _ _ (by simp : ((0 : ℕ), r) ∈ antidiagonal r), esymmPsumPoly_zero,
        mul_one] at h
      have hrest : ∑ x ∈ (antidiagonal r).erase (0, r),
          (-1) ^ x.2 * esymmPsumPoly R x.1 * X x.2 ∈ (esymmPsumAlgHom R).range := by
        refine sum_mem fun x hx => mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) (hE _))
          (ih _ ?_)
        obtain ⟨hne, hx⟩ := mem_erase.mp hx
        rw [mem_antidiagonal] at hx
        refine lt_of_le_of_ne (by omega) fun h2 => hne ?_
        exact Prod.ext (by omega) h2
      have hmem : (-1 : MvPolynomial ℕ R) ^ r * X r ∈ (esymmPsumAlgHom R).range := by
        rw [eq_sub_of_add_eq h.symm]
        exact sub_mem (mul_mem (add_mem (natCast_mem _ r) (one_mem _)) (hE _)) hrest
      have := mul_mem (pow_mem (neg_mem (one_mem (esymmPsumAlgHom R).range)) r) hmem
      rwa [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul] at this
  refine (AlgHom.range_eq_top _).mp (eq_top_iff.mpr ?_)
  rw [← adjoin_range_X, Algebra.adjoin_le_iff]
  rintro _ ⟨r, rfl⟩
  exact hX r

/-- **The rational power-sum presentation of the symmetric functions**: over a `ℚ`-algebra `R`,
the ring of symmetric functions is the polynomial ring over `R` on the power sums `p₁, p₂, …`, the
variable `X r` representing `p_(r + 1)`. -/
noncomputable def psumAlgEquiv : MvPolynomial ℕ R ≃ₐ[R] SymmetricFunction R :=
  AlgEquiv.ofAlgHom (psumAlgHom R) ((esymmPsumAlgHom R).comp (esymmAlgEquiv R).symm.toAlgHom)
    (by
      refine algHom_ext fun n => ?_
      simp [esymmPsumAlgHom])
    (by
      refine AlgHom.ext fun y => ?_
      obtain ⟨p, rfl⟩ := esymmPsumAlgHom_surjective R y
      have hp : psumAlgHom R (esymmPsumAlgHom R p) = esymmAlgEquiv R p := by
        rw [esymmAlgEquiv_apply, ← psumAlgHom_comp_esymmPsumAlgHom R, AlgHom.comp_apply]
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hp, AlgEquiv.coe_toAlgHom,
        AlgEquiv.symm_apply_apply, AlgHom.id_apply])

/-- The power-sum presentation is `TauCeti.SymmetricFunction.psumAlgHom`. -/
@[simp]
theorem psumAlgEquiv_apply (p : MvPolynomial ℕ R) : psumAlgEquiv R p = psumAlgHom R p :=
  (rfl)

/-- The power sum `p_(r + 1)` corresponds to the variable `X r`. -/
@[simp]
theorem psumAlgEquiv_symm_of_stablePsum (r : ℕ) :
    (psumAlgEquiv R).symm (DirectSum.of _ (r + 1) (stablePsum R r.succ_ne_zero)) = X r := by
  rw [AlgEquiv.symm_apply_eq, psumAlgEquiv_apply, psumAlgHom_X]

/-- The elementary symmetric function `e_n` corresponds to Newton's polynomial `E_n`. -/
@[simp]
theorem psumAlgEquiv_symm_of_stableEsymm (n : ℕ) :
    (psumAlgEquiv R).symm (DirectSum.of _ n (stableEsymm R n)) = esymmPsumPoly R n := by
  rw [AlgEquiv.symm_apply_eq, psumAlgEquiv_apply, psumAlgHom_esymmPsumPoly]

/-- The inverse of the power-sum presentation sends a symmetric function of degree `n` to a
polynomial of weighted degree `n`, for the weight `X r ↦ r + 1`. -/
theorem isWeightedHomogeneous_psumAlgEquiv_symm_of {n : ℕ} (f : stableSymmetricSubmodule R n) :
    IsWeightedHomogeneous (· + 1) ((psumAlgEquiv R).symm (DirectSum.of _ n f)) n := by
  set p := (psumAlgEquiv R).symm (DirectSum.of _ n f)
  have hp : psumAlgHom R p = DirectSum.of _ n f := (psumAlgEquiv R).apply_symm_apply _
  have h : weightedHomogeneousComponent (· + 1) n p = p := by
    refine (psumAlgEquiv R).injective ?_
    rw [psumAlgEquiv_apply, psumAlgEquiv_apply, psumAlgHom_weightedHomogeneousComponent, hp,
      DirectSum.of_eq_same]
  rw [← h]
  exact weightedHomogeneousComponent_isWeightedHomogeneous n p

variable {R} in
/-- **Over a `ℚ`-algebra, algebra homomorphisms out of the symmetric functions are determined by
their values on the power sums** `p₁, p₂, …`. -/
theorem algHom_ext_of_stablePsum {A : Type*} [Semiring A] [Algebra R A]
    {f g : SymmetricFunction R →ₐ[R] A}
    (h : ∀ r, f (DirectSum.of _ (r + 1) (stablePsum R r.succ_ne_zero)) =
      g (DirectSum.of _ (r + 1) (stablePsum R r.succ_ne_zero))) : f = g := by
  have hfg : f.comp (psumAlgEquiv R).toAlgHom = g.comp (psumAlgEquiv R).toAlgHom :=
    MvPolynomial.algHom_ext fun r => by simpa using h r
  refine AlgHom.ext fun x => ?_
  obtain ⟨p, rfl⟩ := (psumAlgEquiv R).surjective x
  exact DFunLike.congr_fun hfg p

end Rat

end SymmetricFunction

end TauCeti
