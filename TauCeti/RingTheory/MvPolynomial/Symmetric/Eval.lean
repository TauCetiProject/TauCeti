/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous
import TauCeti.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Evaluating symmetric polynomials at the roots of `Z ^ n - X`

By the fundamental theorem of symmetric polynomials (`MvPolynomial.esymmAlgEquiv`), every symmetric
polynomial `P` in a finite alphabet `σ` of cardinality `n` over a commutative ring `R` is uniquely a
polynomial in the elementary symmetric polynomials `e₁, …, eₙ`. If `P` is homogeneous of degree `m`,
that polynomial in `e₁, …, eₙ` is weighted homogeneous of weight `m` when the variable standing for
`eᵢ₊₁` is given weight `i + 1` (`MvPolynomial.isWeightedHomogeneous_esymmAlgEquiv_symm`).

Specialising `e₁, …, eₙ₋₁` to `0` and, when `0 < n`, `eₙ` to `(-1) ^ (n - 1) * X` defines an
`R`-algebra homomorphism
`MvPolynomial.symmetricSubalgebra.evalTopEsymm : symmetricSubalgebra σ R →ₐ[R] R[X]`
(when `n = 0`, `symmetricSubalgebra σ R` consists of constants and `evalTopEsymm` is the canonical
inclusion `R →ₐ[R] R[X]`). When `0 < n` and `Z ^ n - X = ∏_{j=1}^n (Z - ζⱼ)` splits, Vieta's
formulas give `eₖ(ζ₁, …, ζₙ) = 0` for `1 ≤ k < n` and `eₙ(ζ₁, …, ζₙ) = (-1) ^ (n - 1) * X`, so
`evalTopEsymm` is the algebraic specialisation `P(ζ₁, …, ζₙ) ∈ R[X]` defined without adjoining
`n`-th roots to `R`.

On a homogeneous symmetric polynomial of degree `m` (with `σ` nonempty), `evalTopEsymm` vanishes
unless `n ∣ m`, and in degree `k * n` it produces a scalar multiple of `X ^ k`. By Newton's
identities (`MvPolynomial.psum_eq_mul_esymm_sub_sum`), on the positive power sums `pₘ = ∑ᵢ Xᵢ ^ m`
it evaluates to `n * X ^ (m / n)` when `n ∣ m` and `0` otherwise. Passing to homogeneous components
of symmetric multivariate power series, this evaluation constructs Cartier's Frobenius operators
`fₙ` on curves of formal group laws over arbitrary commutative rings.

## Main definitions

* `MvPolynomial.symmetricSubalgebra.evalTopEsymm`: the `R`-algebra homomorphism
  `symmetricSubalgebra σ R →ₐ[R] Polynomial R` sending `eₖ` (`1 ≤ k < n`) to `0` and, when
  `0 < n`, `eₙ` to `(-1) ^ (n - 1) * X`, where `n = Fintype.card σ`.

## Main results

* `MvPolynomial.symmetricSubalgebra.coeff_evalTopEsymm_eq_zero`: for `P` homogeneous of degree `m`,
  `(evalTopEsymm σ R P).coeff k = 0` whenever `k * Fintype.card σ ≠ m`.
* `MvPolynomial.symmetricSubalgebra.evalTopEsymm_eq_zero_of_not_dvd` and
  `MvPolynomial.symmetricSubalgebra.evalTopEsymm_eq_C_mul_X_pow`: `evalTopEsymm` vanishes in
  degrees not divisible by `Fintype.card σ` and produces a monomial of degree `k` in degree
  `k * Fintype.card σ`.
* `MvPolynomial.symmetricSubalgebra.evalTopEsymm_psum`: for `m > 0`, `evalTopEsymm` maps `pₘ` to
  `n * X ^ (m / n)` if `n ∣ m` and `0` otherwise.
* `MvPolynomial.symmetricSubalgebra.map_evalTopEsymm`: `evalTopEsymm` commutes with ring
  homomorphisms.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.2.
-/

public section

open Finset

namespace MvPolynomial

namespace symmetricSubalgebra

section EvalTopEsymm

variable (σ R : Type*) [Fintype σ] [CommRing R]

/-- The `R`-algebra homomorphism `symmetricSubalgebra σ R →ₐ[R] Polynomial R` sending `eₖ` to `0`
for `1 ≤ k < Fintype.card σ` and, when `σ` is nonempty, `e_{Fintype.card σ}` to
`(-1) ^ (Fintype.card σ - 1) * X`. For nonempty `σ`, this is the algebraic evaluation of symmetric
polynomials at the roots of `Z ^ (Fintype.card σ) - X`. -/
noncomputable def evalTopEsymm : symmetricSubalgebra σ R →ₐ[R] Polynomial R :=
  (aeval fun i : Fin (Fintype.card σ) ↦
    if (i : ℕ) + 1 = Fintype.card σ then (-1 : Polynomial R) ^ (i : ℕ) * Polynomial.X else 0).comp
    (esymmAlgEquiv σ R rfl).symm

variable {σ R}

theorem evalTopEsymm_apply (p : symmetricSubalgebra σ R) :
    evalTopEsymm σ R p = aeval (fun i : Fin (Fintype.card σ) ↦
      if (i : ℕ) + 1 = Fintype.card σ then (-1 : Polynomial R) ^ (i : ℕ) * Polynomial.X else 0)
      ((esymmAlgEquiv σ R rfl).symm p) := (rfl)

/-- `evalTopEsymm` commutes with coefficient ring homomorphisms `f : R →+* S`. -/
theorem map_evalTopEsymm {S : Type*} [CommRing S] (f : R →+* S) (p : symmetricSubalgebra σ R) :
    Polynomial.map f (evalTopEsymm σ R p) = evalTopEsymm σ S ⟨MvPolynomial.map f p, p.2.map f⟩ := by
  rw [evalTopEsymm_apply, evalTopEsymm_apply, ← map_esymmAlgEquiv_symm rfl f p, aeval_def,
    aeval_def, eval₂_map, ← Polynomial.coe_mapRingHom,
    hom_eval₂ ((esymmAlgEquiv σ R rfl).symm p) (algebraMap R (Polynomial R))
      (Polynomial.mapRingHom f) _]
  exact congrFun (congrArg₂ eval₂ (RingHom.ext fun _ ↦ by simp)
    (funext fun i ↦ by split_ifs <;> simp)) _

/-- For `k > 0`, `evalTopEsymm` maps the `k`-th elementary symmetric polynomial to
`(-1) ^ (n - 1) * X` when `k = n` (`n = Fintype.card σ`) and `0` otherwise. -/
theorem evalTopEsymm_esymm_of_pos {k : ℕ} (hk : 0 < k) :
    evalTopEsymm σ R ⟨esymm σ R k, esymm_isSymmetric σ R k⟩ =
      if k = Fintype.card σ then (-1 : Polynomial R) ^ (Fintype.card σ - 1) * Polynomial.X
      else 0 := by
  rcases le_or_gt k (Fintype.card σ) with hle | hgt
  · let i : Fin (Fintype.card σ) := ⟨k - 1, by omega⟩
    have hi : (i : ℕ) + 1 = k := by simp [i]; omega
    have hsub : (⟨esymm σ R k, esymm_isSymmetric σ R k⟩ : symmetricSubalgebra σ R) =
        ⟨esymm σ R ((i : ℕ) + 1), esymm_isSymmetric σ R _⟩ := Subtype.ext (by rw [hi])
    rw [hsub, evalTopEsymm_apply, esymmAlgEquiv_symm_apply, aeval_X, hi]
    split_ifs with hk' <;> simp [i, hk']
  · have hzero : esymm σ R k = 0 := by
      rw [esymm_eq_sum_subtype]
      exact Finset.sum_eq_zero fun t _ ↦
        absurd (t.2 ▸ Finset.card_le_univ (t : Finset σ)) hgt.not_ge
    have hsub : (⟨esymm σ R k, esymm_isSymmetric σ R k⟩ : symmetricSubalgebra σ R) = 0 :=
        Subtype.ext hzero
    simp [hsub, hgt.ne']

/-- Any product in `symmetricSubalgebra σ R` containing `eₐ` with `0 < a` and `a ≠ Fintype.card σ`
is killed by `evalTopEsymm`. -/
private theorem evalTopEsymm_mul_esymm_mul_eq_zero {a : ℕ} (ha0 : 0 < a)
    (hane : a ≠ Fintype.card σ) (x y : symmetricSubalgebra σ R) :
    evalTopEsymm σ R (x * ⟨esymm σ R a, esymm_isSymmetric σ R a⟩ * y) = 0 := by
  rw [map_mul, map_mul, evalTopEsymm_esymm_of_pos ha0, ite_eq_right hane, mul_zero, zero_mul]

section Nonempty

variable [Nonempty σ]

/-- On a polynomial `φ` weighted homogeneous of weight `m` for `i ↦ i + 1`, the specialisation of
`evalTopEsymm` has zero `k`-th coefficient whenever `k * Fintype.card σ ≠ m`. -/
private theorem coeff_aeval_topEsymm_eq_zero {φ : MvPolynomial (Fin (Fintype.card σ)) R} {m k : ℕ}
    (hφ : φ.IsWeightedHomogeneous (fun i : Fin (Fintype.card σ) ↦ (i : ℕ) + 1) m)
    (hk : k * Fintype.card σ ≠ m) :
    (aeval (fun i : Fin (Fintype.card σ) ↦
      if (i : ℕ) + 1 = Fintype.card σ then
        (-1 : Polynomial R) ^ (i : ℕ) * Polynomial.X
      else 0) φ).coeff k = 0 := by
  induction hφ using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ ihp ihq => simp [ihp, ihq]
  | monomial d r hr =>
    have hn : 0 < Fintype.card σ := Fintype.card_pos
    let last : Fin (Fintype.card σ) := ⟨Fintype.card σ - 1, by omega⟩
    -- Either `d` involves some variable below `last` (which evaluates to `0`), or `d` is supported
    -- solely on `last` so its weight `d last * card σ = m` forces `k ≠ d last`.
    by_cases hsupp : ∃ i : Fin (Fintype.card σ), i ≠ last ∧ d i ≠ 0
    · obtain ⟨i, hilast, hdi⟩ := hsupp
      have hi_ne : (i : ℕ) + 1 ≠ Fintype.card σ := fun h ↦ hilast (Fin.ext (by simp [last]; omega))
      have heval : aeval (fun j : Fin (Fintype.card σ) ↦
          if (j : ℕ) + 1 = Fintype.card σ then (-1 : Polynomial R) ^ (j : ℕ) * Polynomial.X else 0)
          (monomial d r) = 0 := by
        rw [aeval_monomial, Finsupp.prod]
        refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hdi) ?_)
        rw [ite_eq_right hi_ne, zero_pow hdi]
      simp [heval]
    · push Not at hsupp
      have hd : d = Finsupp.single last (d last) := Finsupp.ext fun i ↦ by
        by_cases hi : i = last <;> simp [hi, hsupp]
      have hlast : (last : ℕ) + 1 = Fintype.card σ := Nat.sub_add_cancel hn
      have hm_eq : d last * Fintype.card σ = m := by
        rw [← hr, hd, Finsupp.weight_apply, Finsupp.sum_single_index (by simp), smul_eq_mul, hlast,
          Finsupp.single_eq_same]
      have hkd : k ≠ d last := fun h ↦ hk (h ▸ hm_eq)
      rw [hd, aeval_monomial, Finsupp.prod_single_index (by simp)]
      simp only [hlast, ↓reduceIte, mul_pow, ← pow_mul, Polynomial.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
      rw [show Polynomial.C r * ((-1 : Polynomial R) ^ ((last : ℕ) * d last) *
          Polynomial.X ^ d last) =
          Polynomial.C (r * (-1 : R) ^ ((last : ℕ) * d last)) * Polynomial.X ^ d last by
            simp [mul_assoc],
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_right hkd, mul_zero]

/-- If `p ∈ symmetricSubalgebra σ R` is homogeneous of degree `m` and `k * Fintype.card σ ≠ m`,
then the coefficient of `X ^ k` in `evalTopEsymm σ R p` vanishes. -/
theorem coeff_evalTopEsymm_eq_zero {p : symmetricSubalgebra σ R} {m k : ℕ}
    (hp : (p : MvPolynomial σ R).IsHomogeneous m) (hk : k * Fintype.card σ ≠ m) :
    (evalTopEsymm σ R p).coeff k = 0 :=
  coeff_aeval_topEsymm_eq_zero (isWeightedHomogeneous_esymmAlgEquiv_symm rfl hp) hk

/-- If `p ∈ symmetricSubalgebra σ R` is homogeneous of degree `m` and `Fintype.card σ` does not
divide `m`, then `evalTopEsymm σ R p = 0`. -/
theorem evalTopEsymm_eq_zero_of_not_dvd {p : symmetricSubalgebra σ R} {m : ℕ}
    (hp : (p : MvPolynomial σ R).IsHomogeneous m) (hm : ¬ Fintype.card σ ∣ m) :
    evalTopEsymm σ R p = 0 := by
  ext k
  rw [Polynomial.coeff_zero]
  exact coeff_evalTopEsymm_eq_zero hp fun h ↦ hm ⟨k, by rw [mul_comm, h]⟩

/-- If `p ∈ symmetricSubalgebra σ R` is homogeneous of degree `k * Fintype.card σ`, then
`evalTopEsymm σ R p` is a scalar multiple of `X ^ k`. -/
theorem evalTopEsymm_eq_C_mul_X_pow {p : symmetricSubalgebra σ R} {k : ℕ}
    (hp : (p : MvPolynomial σ R).IsHomogeneous (k * Fintype.card σ)) :
    evalTopEsymm σ R p = Polynomial.C ((evalTopEsymm σ R p).coeff k) * Polynomial.X ^ k := by
  ext j
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rcases eq_or_ne j k with rfl | hjk
  · simp
  · have hmul : j * Fintype.card σ ≠ k * Fintype.card σ := fun h ↦
      hjk (Nat.mul_right_cancel Fintype.card_pos h)
    simp [hjk, coeff_evalTopEsymm_eq_zero hp hmul]

/-- **Newton's formula for `evalTopEsymm` on power sums**: for `m > 0`, evaluating the power sum
`pₘ = ∑ᵢ Xᵢ ^ m` at the roots of `Z ^ n - X` (`n = Fintype.card σ`) yields `n * X ^ (m / n)` if
`n ∣ m` and `0` otherwise. -/
theorem evalTopEsymm_psum {m : ℕ} (hm : 0 < m) :
    evalTopEsymm σ R ⟨psum σ R m, psum_isSymmetric σ R m⟩ =
      if Fintype.card σ ∣ m then
        (Fintype.card σ : Polynomial R) * Polynomial.X ^ (m / Fintype.card σ)
      else 0 := by
  have hn : 0 < Fintype.card σ := Fintype.card_pos
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    -- Expand `pₘ` via Newton's identity
    -- `pₘ = (-1)^(m+1) m eₘ - ∑_{0 < a₁ < m} (-1)^a₁ e_{a₁} p_{a₂}`
    -- and split into the cases `m < n`, `m = n`, and `m > n` (`n = Fintype.card σ`).
    let E (k : ℕ) : symmetricSubalgebra σ R := ⟨esymm σ R k, esymm_isSymmetric σ R k⟩
    have hnewton : (⟨psum σ R m, psum_isSymmetric σ R m⟩ : symmetricSubalgebra σ R) =
        (-1) ^ (m + 1) * (m : symmetricSubalgebra σ R) * E m -
          ∑ a ∈ antidiagonal m with a.1 ∈ Set.Ioo 0 m,
            (-1) ^ a.1 * E a.1 * ⟨psum σ R a.2, psum_isSymmetric σ R a.2⟩ :=
      Subtype.ext (by simpa [E] using psum_eq_mul_esymm_sub_sum σ R m hm)
    rw [hnewton, map_sub, map_mul, map_mul, map_pow, map_neg, map_one, map_natCast, map_sum,
      evalTopEsymm_esymm_of_pos hm]
    rcases lt_trichotomy m (Fintype.card σ) with hlt | heq | hgt
    · -- Case `m < n`: both `eₘ` and every `e_{a₁}` (`0 < a₁ < m < n`) vanish under `evalTopEsymm`.
      have hndvd : ¬ Fintype.card σ ∣ m := Nat.not_dvd_of_pos_of_lt hm hlt
      rw [ite_eq_right hlt.ne, ite_eq_right hndvd, mul_zero, zero_sub, neg_eq_zero]
      refine Finset.sum_eq_zero fun a ha ↦ ?_
      rw [mem_filter, Set.mem_Ioo] at ha
      exact evalTopEsymm_mul_esymm_mul_eq_zero ha.2.1 (ha.2.2.trans hlt).ne _ _
    · -- Case `m = n`: every `e_{a₁}` (`0 < a₁ < n`) vanishes, leaving `(-1)^(n+1) n eₙ = n X`.
      subst heq
      rw [ite_eq_left rfl, ite_eq_left dvd_rfl, Nat.div_self hn, pow_one]
      have hsum : (∑ x ∈ antidiagonal (Fintype.card σ) with x.1 ∈ Set.Ioo 0 (Fintype.card σ),
          evalTopEsymm σ R
            ((-1) ^ x.1 * E x.1 * ⟨psum σ R x.2, psum_isSymmetric σ R x.2⟩)) = 0 := by
        refine Finset.sum_eq_zero fun a ha ↦ ?_
        rw [mem_filter, Set.mem_Ioo] at ha
        exact evalTopEsymm_mul_esymm_mul_eq_zero ha.2.1 ha.2.2.ne _ _
      rw [hsum, sub_zero, mul_mul_mul_comm, ← pow_add,
        Even.neg_one_pow ⟨Fintype.card σ, by omega⟩, one_mul]
    · -- Case `m > n`: `eₘ = 0` and only the `a = (n, m - n)` summand survives, reducing to
      -- `p_{m-n}` by strong induction.
      rw [ite_eq_right hgt.ne', mul_zero, zero_sub]
      have hmem : (Fintype.card σ, m - Fintype.card σ) ∈
          {a ∈ antidiagonal m | a.1 ∈ Set.Ioo 0 m} := by
        simpa [mem_filter, mem_antidiagonal, Set.mem_Ioo] using ⟨by omega, hn, hgt⟩
      rw [Finset.sum_eq_single (Fintype.card σ, m - Fintype.card σ)]
      · rw [map_mul, map_mul, map_pow, map_neg, map_one, evalTopEsymm_esymm_of_pos hn,
          ite_eq_left rfl, ih (m - Fintype.card σ) (by omega) (by omega)]
        have hdvd : Fintype.card σ ∣ m - Fintype.card σ ↔ Fintype.card σ ∣ m := by
          conv_rhs => rw [← Nat.sub_add_cancel hgt.le]
          exact Nat.dvd_add_self_right.symm
        by_cases h₁ : Fintype.card σ ∣ m - Fintype.card σ
        · rw [ite_eq_left h₁, ite_eq_left (hdvd.mp h₁)]
          have hdiv : m / Fintype.card σ = (m - Fintype.card σ) / Fintype.card σ + 1 := by
            conv_lhs => rw [← Nat.sub_add_cancel hgt.le]
            exact Nat.add_div_right (m - Fintype.card σ) hn
          rw [hdiv, pow_succ, ← mul_assoc ((-1 : Polynomial R) ^ Fintype.card σ), ← pow_add,
            Odd.neg_one_pow ⟨Fintype.card σ - 1, by omega⟩]
          ring
        · simp [h₁, mt hdvd.mpr h₁]
      · intro a ha hne
        rw [mem_filter, mem_antidiagonal, Set.mem_Ioo] at ha
        exact evalTopEsymm_mul_esymm_mul_eq_zero ha.2.1 (fun h ↦ hne (Prod.ext h (by omega))) _ _
      · exact fun hnot ↦ absurd hmem hnot

end Nonempty

end EvalTopEsymm

end symmetricSubalgebra

end MvPolynomial
