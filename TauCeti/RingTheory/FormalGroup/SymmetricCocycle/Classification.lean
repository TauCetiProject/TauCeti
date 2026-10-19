/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Basic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Finiteness.Nakayama
import TauCeti.Algebra.GCDMonoid.Finset
import TauCeti.RingTheory.Finiteness.Nakayama

/-!
# The symmetric 2-cocycle lemma

Let `R` be a commutative ring and `n ≠ 0`. This file proves **Lazard's symmetric 2-cocycle
lemma**: every homogeneous symmetric additive 2-cocycle `f(X, Y)` of degree `n` over `R` is a
multiple `r • C_n` of the Lazard cocycle `C_n = ((X + Y)ⁿ - Xⁿ - Yⁿ) / d_n`, and for `n ≥ 2` the
multiple `r` is unique. No hypothesis on `R` is needed: it may have torsion or positive
characteristic, where `(X + Y)ⁿ - Xⁿ - Yⁿ` can vanish identically and division by `d_n` is
impossible. This is the inductive step in the degree-by-degree construction of formal group laws
and in Lazard's theorem that the Lazard ring is polynomial.

## Implementation notes

Writing `f = ∑ bᵢ XⁱYⁿ⁻ⁱ`, the cocycle identity says, coefficientwise at `XⁱYʲZᵏ` with
`i, j, k ≥ 1`, that `(i + j).choose i • b_{i + j} = (j + k).choose j • bᵢ`; symmetry says
`b_{n - i} = bᵢ`. These are `ℤ`-linear conditions, so they make sense with coefficients in any
abelian group `M`, and we classify their solutions there.

* If `p • bᵢ = 0` for a prime `p`, the solution is determined by its value at one index `m`,
  depending only on `n` and `p`. When `p ∤ n` or `n = p`, one takes `m = 1`: the equations with
  `k = 1` give `(n - i) • bᵢ = (n - 1).choose i • b₁` and `i • bᵢ = (n - 1).choose (i - 1) • b₁`.
  When `p ∣ n` and `n > p`, Lucas's theorem forces `b₁ = 0` and `bᵢ = 0` for `p ∤ i`, and
  `a ↦ b_{p a}` is a solution in degree `n / p` (Frobenius descent).
* Since `C_n` is itself a solution whose coefficients have greatest common divisor `1`, it does
  not vanish at that index modulo `p`, so every `p`-torsion solution is a multiple of `C_n`.
* For a general solution `b`, choose a Bézout combination `r` of its coefficients and set
  `e = b - r • C_n`. The `ℤ`-span `N` of the `eᵢ` is finitely generated and, by the previous step
  applied to `M ⧸ p • N`, satisfies `N = p • N` for every prime `p`; hence `N = 0` by Nakayama's
  lemma.

## Main results

* `TauCeti.exists_eq_smul_lazardCocycle`: a homogeneous symmetric additive 2-cocycle of degree
  `n ≠ 0` is `r • C_n` for some `r`.
* `TauCeti.existsUnique_eq_smul_lazardCocycle`: for `n ≥ 2`, the multiple `r` is unique.

## References

* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* M. Lazard, *Commutative Formal Groups*, Lecture Notes in Mathematics 443 (1975).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
* J. Lurie, *Chromatic Homotopy Theory* (Harvard lecture notes, 2010), Lectures 2 and 3.
-/

public section

open Finset MvPolynomial

namespace TauCeti

section CoeffEquations

/-! ### The coefficient equations, with coefficients in an abelian group -/

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] {n : ℕ}

/-- The linear equations satisfied by the coefficients `bᵢ` of `XⁱYⁿ⁻ⁱ` in a symmetric additive
2-cocycle of degree `n`, with coefficients in an abelian group. -/
private structure IsCocycleCoeff (n : ℕ) (b : ℕ → M) : Prop where
  symm : ∀ i ≤ n, b (n - i) = b i
  rel : ∀ i j k : ℕ, 0 < i → 0 < j → 0 < k → i + j + k = n →
    (i + j).choose i • b (i + j) = (j + k).choose j • b i

namespace IsCocycleCoeff

variable {b b' : ℕ → M}

private theorem map (h : IsCocycleCoeff n b) (φ : M →+ N) :
    IsCocycleCoeff n fun i => φ (b i) where
  symm i hi := by rw [h.symm i hi]
  rel i j k hi hj hk hn := by rw [← map_nsmul, ← map_nsmul, h.rel i j k hi hj hk hn]

private theorem sub (h : IsCocycleCoeff n b) (h' : IsCocycleCoeff n b') :
    IsCocycleCoeff n fun i => b i - b' i where
  symm i hi := by rw [h.symm i hi, h'.symm i hi]
  rel i j k hi hj hk hn := by rw [nsmul_sub, nsmul_sub, h.rel i j k hi hj hk hn,
    h'.rel i j k hi hj hk hn]

/-- The equations with `k = 1`: `(n - i) • bᵢ = (n - 1).choose i • b_{n - 1}`. -/
private theorem sub_nsmul_eq (h : IsCocycleCoeff n b) {i : ℕ} (hi : 0 < i) (hin : i + 1 < n) :
    (n - i) • b i = (n - 1).choose i • b (n - 1) := by
  have := h.rel i (n - 1 - i) 1 hi (by omega) one_pos (by omega)
  rw [show i + (n - 1 - i) = n - 1 by omega, Nat.choose_succ_self_right,
    show n - 1 - i + 1 = n - i by omega] at this
  exact this.symm

end IsCocycleCoeff

end CoeffEquations

section Torsion

/-! ### Solutions killed by a prime -/

variable {M : Type*} [AddCommGroup M] {p : ℕ}

private theorem nsmul_eq_nsmul_of_modEq {a a' : ℕ} {x : M} (hp : p • x = 0)
    (h : a ≡ a' [MOD p]) : a • x = a' • x :=
  nsmul_eq_nsmul_iff_modEq.2 (h.of_dvd (addOrderOf_dvd_of_nsmul_eq_zero hp))

/-- `(n - 1).choose (p - 1) ≡ 1 [MOD p]` when `p ∣ n` and `n ≠ 0`, by Lucas's theorem. -/
private theorem choose_sub_one_sub_one_modEq_one (hp : p.Prime) {n : ℕ} (hpn : p ∣ n)
    (hn : n ≠ 0) : (n - 1).choose (p - 1) ≡ 1 [MOD p] := by
  have := Fact.mk hp
  have hp1 := hp.one_le
  have h₁ : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega)
  have h₂ : (p - 1) / p = 0 := Nat.div_eq_of_lt (by omega)
  have hmod : (n - 1) % p = p - 1 := by
    obtain ⟨q, rfl⟩ := hpn
    have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (right_ne_zero_of_mul hn)
    have hpq : p ≤ p * q := Nat.le_mul_of_pos_right p hq
    rw [show p * q - 1 = p - 1 + p * (q - 1) by rw [Nat.mul_sub_one]; omega,
      Nat.add_mul_mod_self_left, h₁]
  refine (Choose.choose_modEq_choose_mod_mul_choose_div_nat).trans ?_
  rw [hmod, h₁, h₂, Nat.choose_self, Nat.choose_zero_right]

/-- If `p ∤ n` or `n = p`, a `p`-torsion solution in degree `n` vanishing at `1` vanishes: the
equations with `k = 1` give `(n - i) • bᵢ = 0` and `i • bᵢ = 0`, and `p` cannot divide both
`i` and `n - i`. -/
private theorem IsCocycleCoeff.eq_zero_of_apply_one_eq_zero (hp : p.Prime) {n : ℕ}
    {b : ℕ → M} (hbc : IsCocycleCoeff n b) (hb : ∀ i, 0 < i → i < n → p • b i = 0)
    (hpn : ¬(p ∣ n ∧ p < n)) (hb1 : b 1 = 0) {i : ℕ} (hi : 0 < i) (hin : i < n) : b i = 0 := by
  have hb1' : b (n - 1) = 0 := by rw [hbc.symm 1 (by omega), hb1]
  obtain rfl | hi1 := eq_or_ne i 1
  · exact hb1
  by_cases hin' : i + 1 < n
  · have h₁ : (n - i) • b i = 0 := by rw [hbc.sub_nsmul_eq hi hin', hb1', nsmul_zero]
    have h₂ : i • b i = 0 := by
      have := hbc.sub_nsmul_eq (i := n - i) (by omega) (by omega)
      rwa [Nat.sub_sub_self hin.le, hbc.symm i hin.le, hb1', nsmul_zero] at this
    by_cases hpi : p ∣ i
    · refine (nsmul_eq_zero_iff_of_coprime (Nat.coprime_comm.1
        ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hpn ⟨?_, ?_⟩))).1 ⟨h₁, hb i hi hin⟩
      · have := Nat.dvd_add h hpi
        rwa [Nat.sub_add_cancel hin.le] at this
      · exact lt_of_le_of_lt (Nat.le_of_dvd hi hpi) hin
    · exact (nsmul_eq_zero_iff_of_coprime (Nat.coprime_comm.1
        ((Nat.Prime.coprime_iff_not_dvd hp).2 hpi))).1 ⟨h₂, hb i hi hin⟩
  · rwa [show i = n - 1 by omega]

/-- **Frobenius descent.** If `p < p * q`, a `p`-torsion solution in degree `p * q` vanishes at
the indices prime to `p`, and `a ↦ b (p * a)` is a solution in degree `q`. -/
private theorem IsCocycleCoeff.descent (hp : p.Prime) {q : ℕ} {b : ℕ → M}
    (hbc : IsCocycleCoeff (p * q) b) (hb : ∀ i, 0 < i → i < p * q → p • b i = 0)
    (hlt : p < p * q) :
    (∀ i, 0 < i → i < p * q → ¬p ∣ i → b i = 0) ∧ IsCocycleCoeff q fun a => b (p * a) := by
  have := Fact.mk hp
  have hp2 := hp.two_le
  -- The equation at `X Yᵖ⁻¹ Zⁿ⁻ᵖ` reads `p • b_p = (n - 1).choose (p - 1) • b₁`, and the
  -- binomial coefficient is `1` modulo `p`.
  have hb1 : b 1 = 0 := by
    have h := hbc.rel 1 (p - 1) (p * q - p) one_pos (by omega) (by omega) (by omega)
    rw [show 1 + (p - 1) = p by omega, Nat.choose_one_right, hb p hp.pos hlt,
      show p - 1 + (p * q - p) = p * q - 1 by omega,
      nsmul_eq_nsmul_of_modEq (hb 1 one_pos (by omega))
        (choose_sub_one_sub_one_modEq_one hp (dvd_mul_right p q) (by omega)), one_nsmul] at h
    exact h.symm
  refine ⟨fun i hi hin hpi => ?_, ⟨fun a ha => ?_, fun a a' a'' ha ha' ha'' hsum => ?_⟩⟩
  · by_cases hi' : i + 1 < p * q
    · refine (nsmul_eq_zero_iff_of_coprime (Nat.coprime_comm.1
        ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hpi ?_))).1
        ⟨by rw [hbc.sub_nsmul_eq hi hi', hbc.symm 1 (by omega), hb1, nsmul_zero], hb i hi hin⟩
      have := (Nat.dvd_sub_iff_right (by omega) (dvd_mul_right p q)).2 h
      rwa [Nat.sub_sub_self hin.le] at this
    · rw [show i = p * q - 1 by omega, hbc.symm 1 (by omega), hb1]
  · rw [Nat.mul_sub, hbc.symm (p * a) (Nat.mul_le_mul_left p ha)]
  · -- `(p * A).choose (p * B) ≡ A.choose B [MOD p]` by Lucas's theorem.
    have h := hbc.rel (p * a) (p * a') (p * a'') (by positivity) (by positivity)
      (by positivity) (by rw [← mul_add, ← mul_add, hsum])
    rw [← mul_add, ← mul_add] at h
    rwa [nsmul_eq_nsmul_of_modEq (hb _ (by positivity) (by nlinarith))
        Choose.choose_mul_mul_modEq_choose_nat,
      nsmul_eq_nsmul_of_modEq (hb _ (by positivity) (by nlinarith))
        Choose.choose_mul_mul_modEq_choose_nat] at h

/-- Over a group killed by a prime `p`, a solution of the coefficient equations in degree `n ≥ 2`
is determined by its value at a single index `m`, depending only on `n` and `p`. -/
private theorem exists_forall_eq_zero_of_eq_zero (hp : p.Prime) {n : ℕ} (hn : 2 ≤ n) :
    ∃ m, 0 < m ∧ m < n ∧ ∀ b : ℕ → M, (∀ i, 0 < i → i < n → p • b i = 0) →
      IsCocycleCoeff n b → b m = 0 → ∀ i, 0 < i → i < n → b i = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hp2 := hp.two_le
  by_cases hpn : p ∣ n ∧ p < n
  · obtain ⟨⟨q, rfl⟩, hlt⟩ := hpn
    have hq : 2 ≤ q := by
      by_contra hq
      interval_cases q <;> simp at hlt hn
    obtain ⟨m, hm0, hmq, hm⟩ := ih q (by nlinarith) hq
    refine ⟨p * m, Nat.mul_pos hp.pos hm0, Nat.mul_lt_mul_of_pos_left hmq hp.pos,
      fun b hb hbc hbm i hi hin => ?_⟩
    obtain ⟨hoff, hdesc⟩ := hbc.descent hp hb hlt
    by_cases hpi : p ∣ i
    · obtain ⟨a, rfl⟩ := hpi
      exact hm _ (fun a ha haq => hb _ (Nat.mul_pos hp.pos ha) (by nlinarith)) hdesc hbm a
        (Nat.pos_of_mul_pos_left hi) (Nat.lt_of_mul_lt_mul_left hin)
    · exact hoff i hi hin hpi
  · exact ⟨1, one_pos, by omega, fun b hb hbc hb1 i hi hin =>
      hbc.eq_zero_of_apply_one_eq_zero hp hb hpn hb1 hi hin⟩

end Torsion

section Polynomial

/-! ### The coefficients of a symmetric 2-cocycle satisfy the coefficient equations -/

variable {R : Type*} [CommRing R]

/-- The exponent `XⁱYʲ` in two variables. -/
private noncomputable abbrev expTwo (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j

/-- The coefficient of `XⁱYⁿ⁻ⁱ` in a polynomial in two variables. -/
private noncomputable def coeffDeg (n : ℕ) (f : MvPolynomial (Fin 2) R) (i : ℕ) : R :=
  f.coeff (expTwo i (n - i))

private theorem coeffDeg_lazardCocycle {n i : ℕ} (hi : 0 < i) (hin : i < n) :
    coeffDeg n (lazardCocycle n R) i = ((n.choose i / lazardGcd n : ℕ) : R) := by
  rw [coeffDeg, coeff_lazardCocycle]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  rw [ite_eq_left ⟨by simp; omega, by simp; omega, by simp; omega⟩]
  simp

/-- An exponent in three variables `a, b, c` is determined by its values at them. -/
private theorem finsupp_eq_iff_of_fin_three {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) {d d' : Fin 3 →₀ ℕ} : d = d' ↔ d a = d' a ∧ d b = d' b ∧ d c = d' c := by
  refine ⟨by rintro rfl; simp, fun ⟨h₁, h₂, h₃⟩ => Finsupp.ext fun x => ?_⟩
  rcases (by omega : x = a ∨ x = b ∨ x = c) with rfl | rfl | rfl <;> assumption

/-- The coefficients of `(X a + X b) ^ m * X c ^ k` in three variables `a, b, c`. -/
private theorem coeff_add_pow_mul_X_pow {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (m k : ℕ) (d : Fin 3 →₀ ℕ) :
    ((X a + X b) ^ m * X c ^ k : MvPolynomial (Fin 3) R).coeff d =
      if d a + d b = m ∧ d c = k then (m.choose (d a) : R) else 0 := by
  classical
  rw [add_pow, Finset.sum_mul, coeff_sum]
  have key (l : ℕ) : (X a ^ l * X b ^ (m - l) * (m.choose l : MvPolynomial (Fin 3) R) *
      X c ^ k).coeff d = if d a = l ∧ d b = m - l ∧ d c = k then (m.choose l : R) else 0 := by
    rw [← map_natCast (C : R →+* _), X_pow_eq_monomial, X_pow_eq_monomial, X_pow_eq_monomial,
      mul_right_comm _ (C _), mul_comm _ (C _), monomial_mul_monomial, monomial_mul_monomial,
      C_mul_monomial, mul_one, mul_one, mul_one, coeff_monomial]
    simp only [finsupp_eq_iff_of_fin_three hab hac hbc]
    simp [hab, hac, hbc, hab.symm, hac.symm, hbc.symm, eq_comm]
  simp only [key]
  split_ifs with h
  · rw [Finset.sum_eq_single (d a)]
    · rw [ite_eq_left ⟨rfl, by omega, h.2⟩]
    · intro l _ hl
      rw [ite_eq_right (by omega)]
    · intro hd
      simp at hd
      omega
  · refine Finset.sum_eq_zero fun l hl => ?_
    rw [mem_range] at hl
    rw [ite_eq_right (by omega)]

/-- The coefficients of `X a ^ m * X c ^ k` in three variables `a, b, c`. -/
private theorem coeff_X_pow_mul_X_pow {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (m k : ℕ) (d : Fin 3 →₀ ℕ) :
    (X a ^ m * X c ^ k : MvPolynomial (Fin 3) R).coeff d =
      if d a = m ∧ d b = 0 ∧ d c = k then 1 else 0 := by
  classical
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, mul_one, coeff_monomial]
  simp only [finsupp_eq_iff_of_fin_three hab hac hbc]
  simp [hac, hbc, hab.symm, hac.symm, eq_comm]

/-- `aeval ![P, Q]` sends the monomial `c XᵐYᵏ` to `C c * (Pᵐ * Qᵏ)`. -/
private theorem aeval_monomial_fin_two (P Q : MvPolynomial (Fin 3) R) (u : Fin 2 →₀ ℕ) (c : R) :
    aeval ![P, Q] (monomial u c) = C c * (P ^ u 0 * Q ^ u 1) := by
  rw [aeval_monomial, algebraMap_eq, Finsupp.prod_fintype _ _ fun _ => pow_zero _,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]

/-- The coefficient of `XⁱYʲZᵏ` in `g(X + Y, Z)` is `(i + j).choose i` times that of `Xⁱ⁺ʲYᵏ`
in `g`. -/
private theorem coeff_aeval_add_X (g : MvPolynomial (Fin 2) R) (d : Fin 3 →₀ ℕ) :
    (aeval ![X 0 + X 1, X 2] g).coeff d =
      (d 0 + d 1).choose (d 0) * g.coeff (expTwo (d 0 + d 1) (d 2)) := by
  induction g using MvPolynomial.induction_on' with
  | monomial u c =>
    classical
    rw [aeval_monomial_fin_two, coeff_C_mul, coeff_add_pow_mul_X_pow (by decide) (by decide)
      (by decide), coeff_monomial]
    simp only [Finsupp.ext_iff, Fin.forall_fin_two]
    split_ifs <;> simp_all [mul_comm]
  | add p q hp hq => simp [hp, hq, mul_add]

/-- The coefficient of `XⁱYʲZᵏ` in `g(X, Y + Z)` is `(j + k).choose j` times that of `XⁱYʲ⁺ᵏ`
in `g`. -/
private theorem coeff_aeval_X_add (g : MvPolynomial (Fin 2) R) (d : Fin 3 →₀ ℕ) :
    (aeval ![X 0, X 1 + X 2] g).coeff d =
      (d 1 + d 2).choose (d 1) * g.coeff (expTwo (d 0) (d 1 + d 2)) := by
  induction g using MvPolynomial.induction_on' with
  | monomial u c =>
    classical
    rw [aeval_monomial_fin_two, mul_comm (X 0 ^ _), coeff_C_mul,
      coeff_add_pow_mul_X_pow (by decide) (by decide) (by decide), coeff_monomial]
    simp only [Finsupp.ext_iff, Fin.forall_fin_two]
    split_ifs <;> simp_all [mul_comm]
  | add p q hp hq => simp [hp, hq, mul_add]

/-- The coefficient of `XⁱYʲZᵏ` in `g(X, Y)` is that of `XⁱYʲ` in `g` if `k = 0`, and `0`
otherwise. -/
private theorem coeff_aeval_X_X (g : MvPolynomial (Fin 2) R) (d : Fin 3 →₀ ℕ) :
    (aeval ![X 0, X 1] g).coeff d = if d 2 = 0 then g.coeff (expTwo (d 0) (d 1)) else 0 := by
  induction g using MvPolynomial.induction_on' with
  | monomial u c =>
    classical
    rw [aeval_monomial_fin_two, coeff_C_mul, coeff_X_pow_mul_X_pow (b := 2) (by decide)
      (by decide) (by decide), coeff_monomial]
    simp only [Finsupp.ext_iff, Fin.forall_fin_two]
    split_ifs <;> simp_all
  | add p q hp hq => simp [hp, hq, ite_add_ite]

/-- The coefficient of `XⁱYʲZᵏ` in `g(Y, Z)` is that of `XʲYᵏ` in `g` if `i = 0`, and `0`
otherwise. -/
private theorem coeff_aeval_X_X' (g : MvPolynomial (Fin 2) R) (d : Fin 3 →₀ ℕ) :
    (aeval ![X 1, X 2] g).coeff d = if d 0 = 0 then g.coeff (expTwo (d 1) (d 2)) else 0 := by
  induction g using MvPolynomial.induction_on' with
  | monomial u c =>
    classical
    rw [aeval_monomial_fin_two, coeff_C_mul, coeff_X_pow_mul_X_pow (b := 0) (by decide)
      (by decide) (by decide), coeff_monomial]
    simp only [Finsupp.ext_iff, Fin.forall_fin_two]
    split_ifs <;> simp_all
  | add p q hp hq => simp [hp, hq, ite_add_ite]

/-- The cocycle identity at the coefficient of `XⁱYʲZᵏ`. -/
private theorem _root_.MvPolynomial.IsAddCocycle₂.coeff_eq {f : MvPolynomial (Fin 2) R}
    (hf : f.IsAddCocycle₂) (i j k : ℕ) :
    (if k = 0 then f.coeff (expTwo i j) else 0) + (i + j).choose i * f.coeff (expTwo (i + j) k) =
      (j + k).choose j * f.coeff (expTwo i (j + k)) +
        if i = 0 then f.coeff (expTwo j k) else 0 := by
  have h := congrArg (fun p : MvPolynomial (Fin 3) R =>
    p.coeff (Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single 2 k)) (isAddCocycle₂_iff.1 hf)
  simpa [coeff_aeval_add_X, coeff_aeval_X_add, coeff_aeval_X_X, coeff_aeval_X_X',
    Finsupp.single_apply] using h

/-- The coefficients of a symmetric additive 2-cocycle in degree `n` satisfy the coefficient
equations. -/
private theorem isCocycleCoeff_coeffDeg {f : MvPolynomial (Fin 2) R} (hs : f.IsSymmetric)
    (hf : f.IsAddCocycle₂) (n : ℕ) : IsCocycleCoeff n (coeffDeg n f) where
  symm i hi := by
    have h := coeff_rename_mapDomain (Equiv.swap (0 : Fin 2) 1) (Equiv.injective _) f
      (expTwo i (n - i))
    rw [hs (Equiv.swap 0 1), Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      Finsupp.mapDomain_single, Equiv.swap_apply_left, Equiv.swap_apply_right, add_comm] at h
    rw [coeffDeg, coeffDeg, Nat.sub_sub_self hi, h]
  rel i j k hi hj hk hn := by
    have h := hf.coeff_eq i j k
    rw [ite_eq_right hk.ne', ite_eq_right hi.ne', zero_add, add_zero] at h
    rw [coeffDeg, coeffDeg, nsmul_eq_mul, nsmul_eq_mul, show n - (i + j) = k by omega,
      show n - i = j + k by omega]
    exact h

/-- The coefficient of `Yⁿ` in an additive 2-cocycle vanishes for `n ≠ 0`. -/
private theorem _root_.MvPolynomial.IsAddCocycle₂.coeffDeg_zero {f : MvPolynomial (Fin 2) R}
    (hf : f.IsAddCocycle₂) {n : ℕ} (hn : n ≠ 0) : coeffDeg n f 0 = 0 := by
  have h := hf.coeff_eq 0 0 n
  simp only [hn, ite_false, zero_add, Nat.choose_zero_right, Nat.cast_one, one_mul,
    ite_true] at h
  rw [coeffDeg, Nat.sub_zero]
  simpa using h

end Polynomial

section General

/-! ### Solutions with coefficients in an arbitrary abelian group -/

variable {M : Type*} [AddCommGroup M]

/-- The integral coefficient sequence of `C_n`. -/
private noncomputable abbrev lazardCoeff (n : ℕ) : ℕ → ℤ :=
  coeffDeg n (lazardCocycle n ℤ)

private theorem isCocycleCoeff_lazardCoeff (n : ℕ) : IsCocycleCoeff n (lazardCoeff n) :=
  isCocycleCoeff_coeffDeg (isSymmetric_lazardCocycle n) (isAddCocycle₂_lazardCocycle n) n

/-- Over a group killed by a prime `p`, every solution of the coefficient equations in degree
`n ≥ 2` is a multiple of the coefficients of `C_n`. -/
private theorem exists_eq_nsmul_of_torsion {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n) {b : ℕ → M}
    (hb : ∀ i, 0 < i → i < n → p • b i = 0) (hbc : IsCocycleCoeff n b) :
    ∃ s : M, ∀ i, 0 < i → i < n → b i = (n.choose i / lazardGcd n) • s := by
  have := Fact.mk hp
  -- Work in `M × ZMod p`, so that one index `m` controls solutions in `M` and in `ZMod p`.
  obtain ⟨m, hm0, hmn, hm⟩ := exists_forall_eq_zero_of_eq_zero (M := M × ZMod p) hp hn
  set c : ℕ → ℕ := fun i => n.choose i / lazardGcd n
  have hcZ : ∀ i, 0 < i → i < n → lazardCoeff n i = c i := fun i hi hin =>
    coeffDeg_lazardCocycle hi hin
  -- The coefficient `c m` of `C_n` is a unit modulo `p`, since the `c i` have no common factor.
  have hcm : ((c m : ℕ) : ZMod p) ≠ 0 := by
    intro hcm
    set φ : ℤ →+ M × ZMod p := (AddMonoidHom.inr _ _).comp (Int.castAddHom (ZMod p))
    have hzero := hm (fun i => φ (lazardCoeff n i)) (fun i _ _ => by ext <;> simp [φ])
      ((isCocycleCoeff_lazardCoeff n).map φ) (by rw [hcZ m hm0 hmn]; ext <;> simp [φ, hcm])
    have hdvd : p ∣ (Icc 1 (n - 1)).gcd c := Finset.dvd_gcd fun i hi => by
      rw [mem_Icc] at hi
      have := congrArg Prod.snd (hzero i (by omega) (by omega))
      simp only [φ, hcZ i (by omega) (by omega), AddMonoidHom.comp_apply, Int.coe_castAddHom,
        Int.cast_natCast, AddMonoidHom.inr_apply, Prod.snd_zero] at this
      exact (ZMod.natCast_eq_zero_iff _ _).1 this
    rw [gcd_choose_div_lazardGcd_eq_one hn] at hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.1 hdvd)
  set u : ℕ := (((c m : ℕ) : ZMod p)⁻¹).val
  have hu : c m * u ≡ 1 [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one,
      ZMod.coe_mul_inv_eq_one _ (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h =>
        hcm ((ZMod.natCast_eq_zero_iff _ _).2 h)))]
  refine ⟨u • b m, fun i hi hin => ?_⟩
  -- The difference `b - (u • b m) • C_n` is a `p`-torsion solution vanishing at `m`.
  have hdiff := hbc.sub ((isCocycleCoeff_lazardCoeff n).map (zmultiplesHom M (u • b m)))
  have hzero := hm (fun i => AddMonoidHom.inl M (ZMod p)
      (b i - zmultiplesHom M (u • b m) (lazardCoeff n i)))
    (fun i hi hin => by ext <;> simp [smul_sub, smul_comm p, hb i hi hin, hb m hm0 hmn])
    (hdiff.map _)
    (by
      ext
      · simp only [AddMonoidHom.inl_apply, zmultiplesHom_apply, hcZ m hm0 hmn, natCast_zsmul,
          smul_smul, nsmul_eq_nsmul_of_modEq (hb m hm0 hmn) hu, one_nsmul, sub_self,
          Prod.fst_zero]
      · simp)
  have := congrArg Prod.fst (hzero i hi hin)
  simp only [AddMonoidHom.inl_apply, zmultiplesHom_apply, hcZ i hi hin, natCast_zsmul,
    Prod.fst_zero] at this
  exact sub_eq_zero.1 this

/-- A solution `e` of the coefficient equations in degree `n ≥ 2` with `∑ lᵢ • eᵢ = 0`, for a
Bézout combination `∑ lᵢ cᵢ = 1` of the coefficients `cᵢ` of `C_n`, vanishes. Its coefficients
span a finitely generated subgroup `S` with `S = p • S` for every prime `p`, by the `p`-torsion
case applied in `M ⧸ p • S`. -/
private theorem eq_zero_of_sum_smul_eq_zero {n : ℕ} (hn : 2 ≤ n) {l : ℕ → ℤ}
    (hl : ∑ i ∈ Icc 1 (n - 1), l i * (n.choose i / lazardGcd n : ℕ) = 1) {e : ℕ → M}
    (he : IsCocycleCoeff n e) (hsum : ∑ i ∈ Icc 1 (n - 1), l i • e i = 0) {i : ℕ} (hi : 0 < i)
    (hin : i < n) : e i = 0 := by
  set S : Submodule ℤ M := Submodule.span ℤ (e '' ↑(Icc 1 (n - 1)))
  have hS : S = ⊥ := by
    refine Submodule.eq_bot_of_forall_prime_le_smul (Submodule.fg_span
      ((Icc 1 (n - 1)).finite_toSet.image e)) fun p hp => ?_
    set π := (Ideal.span {(p : ℤ)} • S).mkQ
    have htors : ∀ i, 0 < i → i < n → p • π (e i) = 0 := fun i hi hin => by
      rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← natCast_zsmul]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _)
        (Submodule.subset_span ⟨i, mem_Icc.2 ⟨hi, by omega⟩, rfl⟩)
    obtain ⟨s, hs⟩ := exists_eq_nsmul_of_torsion hp hn htors (he.map π.toAddMonoidHom)
    have hs0 : s = 0 := by
      have h₁ : ∑ i ∈ Icc 1 (n - 1), π (l i • e i) =
          ∑ i ∈ Icc 1 (n - 1), (l i * (n.choose i / lazardGcd n : ℕ)) • s :=
        Finset.sum_congr rfl fun i hi => by
          rw [mem_Icc] at hi
          rw [map_zsmul, hs i (by omega) (by omega), ← natCast_zsmul, smul_smul]
      have h := congrArg π hsum
      rwa [map_sum, map_zero, h₁, ← Finset.sum_smul, hl, one_smul] at h
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [mem_coe, mem_Icc] at hi
    have := hs i (by omega) (by omega)
    rwa [hs0, smul_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  rw [← Submodule.mem_bot ℤ, ← hS]
  exact Submodule.subset_span ⟨i, mem_Icc.2 ⟨hi, by omega⟩, rfl⟩

/-- Every solution of the coefficient equations in degree `n ≥ 2`, with coefficients in an
arbitrary abelian group, is a multiple of the coefficients of `C_n`. -/
private theorem exists_eq_nsmul {n : ℕ} (hn : 2 ≤ n) {b : ℕ → M} (hbc : IsCocycleCoeff n b) :
    ∃ r : M, ∀ i, 0 < i → i < n → b i = (n.choose i / lazardGcd n) • r := by
  have hcZ : ∀ i ∈ Icc 1 (n - 1), lazardCoeff n i = (n.choose i / lazardGcd n : ℕ) :=
    fun i hi => by
      rw [mem_Icc] at hi
      exact coeffDeg_lazardCocycle (by omega) (by omega)
  obtain ⟨l, hl⟩ :=
    Finset.exists_sum_natCast_mul_eq_one_of_gcd_eq_one (gcd_choose_div_lazardGcd_eq_one hn)
  have hl' : ∑ i ∈ Icc 1 (n - 1), l i * (n.choose i / lazardGcd n : ℕ) = 1 := by
    rw [← hl]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  -- The error `e = b - r • C_n`, for `r = ∑ lᵢ • bᵢ`, is a solution with `∑ lᵢ • eᵢ = 0`.
  set r : M := ∑ i ∈ Icc 1 (n - 1), l i • b i
  have hsum : ∑ i ∈ Icc 1 (n - 1), l i • (b i - lazardCoeff n i • r) = 0 := by
    have h₁ : ∑ i ∈ Icc 1 (n - 1), l i * lazardCoeff n i = 1 := by
      rw [← hl']
      exact Finset.sum_congr rfl fun i hi => by rw [hcZ i hi]
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul]
    rw [sub_eq_zero, ← Finset.sum_smul, h₁, one_smul]
  refine ⟨r, fun i hi hin => ?_⟩
  have := eq_zero_of_sum_smul_eq_zero hn hl'
    (hbc.sub ((isCocycleCoeff_lazardCoeff n).map (zmultiplesHom M r))) hsum hi hin
  rwa [zmultiplesHom_apply, sub_eq_zero, hcZ i (mem_Icc.2 ⟨hi, by omega⟩), natCast_zsmul] at this

end General

/-! ### The symmetric 2-cocycle lemma -/

variable {R : Type*} [CommRing R]

/-- **The symmetric 2-cocycle lemma.** Over any commutative ring `R`, a homogeneous symmetric
additive 2-cocycle `f(X, Y)` of degree `n ≠ 0` is a multiple `r • C_n` of the Lazard cocycle
`C_n = ((X + Y)ⁿ - Xⁿ - Yⁿ) / d_n`. -/
theorem exists_eq_smul_lazardCocycle {n : ℕ} (hn : n ≠ 0) {f : MvPolynomial (Fin 2) R}
    (hh : f.IsHomogeneous n) (hs : f.IsSymmetric) (hf : f.IsAddCocycle₂) :
    ∃ r : R, f = r • lazardCocycle n R := by
  obtain ⟨r, hr⟩ : ∃ r : R, ∀ i, 0 < i → i < n →
      coeffDeg n f i = (n.choose i / lazardGcd n) • r := by
    rcases lt_or_ge n 2 with h2 | h2
    · exact ⟨0, fun i hi hin => by omega⟩
    · exact exists_eq_nsmul h2 (isCocycleCoeff_coeffDeg hs hf n)
  refine ⟨r, MvPolynomial.ext _ _ fun d => ?_⟩
  rw [coeff_smul, coeff_lazardCocycle, smul_eq_mul]
  by_cases hd : d 0 + d 1 = n
  · have hd' : d = expTwo (d 0) (n - d 0) := by
      ext x
      fin_cases x <;> simp; omega
    have hfd : f.coeff d = coeffDeg n f (d 0) := by rw [coeffDeg, ← hd']
    rw [hfd]
    by_cases h0 : d 0 = 0
    · rw [ite_eq_right (by omega), mul_zero, h0]
      exact hf.coeffDeg_zero hn
    by_cases h1 : d 1 = 0
    · rw [ite_eq_right (by omega), mul_zero, show d 0 = n - 0 by omega,
        (isCocycleCoeff_coeffDeg hs hf n).symm 0 (Nat.zero_le n)]
      exact hf.coeffDeg_zero hn
    · rw [ite_eq_left ⟨hd, h0, h1⟩, hr _ (Nat.pos_of_ne_zero h0) (by omega), nsmul_eq_mul,
        mul_comm]
  · rw [ite_eq_right fun h => hd h.1, mul_zero]
    exact hh.coeff_eq_zero (by rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two])

/-- **The symmetric 2-cocycle lemma**, with uniqueness: for `n ≥ 2`, a homogeneous symmetric
additive 2-cocycle of degree `n` over any commutative ring is `r • C_n` for a unique `r`. -/
theorem existsUnique_eq_smul_lazardCocycle {n : ℕ} (hn : 2 ≤ n) {f : MvPolynomial (Fin 2) R}
    (hh : f.IsHomogeneous n) (hs : f.IsSymmetric) (hf : f.IsAddCocycle₂) :
    ∃! r : R, f = r • lazardCocycle n R := by
  obtain ⟨r, hr⟩ := exists_eq_smul_lazardCocycle (by omega) hh hs hf
  exact ⟨r, hr, fun r' hr' => smul_lazardCocycle_injective hn (hr'.symm.trans hr)⟩

end TauCeti
