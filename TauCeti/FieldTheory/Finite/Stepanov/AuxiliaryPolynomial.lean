/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Polynomial.Bivariate.Basic
import TauCeti.FieldTheory.Finite.Polynomial
import TauCeti.FieldTheory.Finite.RootsOfUnity
import TauCeti.FieldTheory.Kummer.RationalFunction
import TauCeti.RingTheory.RootsOfUnity.PolynomialNorm

/-!
# Stepanov's auxiliary polynomial is nonzero

Let `F` be a finite field with `q` elements, let `e ∣ q - 1` and `c = (q - 1) / e`, and let
`f ∈ F[X]` not be of the form `C b * hˡ` for any `ℓ > 1` dividing `e`. Stepanov's
method bounds the number of `x ∈ F` with `f(x) ^ c = 1` by the degree of an auxiliary polynomial
`R = ∑_{i < e} f ^ (i c) · Aᵢ(X, X ^ q)` that vanishes to high order at these points. The method
needs `R ≠ 0` whenever the `Aᵢ ∈ F[X][Y]` are not all zero and have small degree in `X`. This file
proves that statement (`Polynomial.sum_pow_mul_eval_X_pow_eq_zero_iff`).

## Main results

* `Polynomial.sum_pow_mul_eval_X_pow_eq_zero_iff`: if the coefficients of the `Aᵢ` have degree at
  most `D` in `X`, with `e D + (e - 1) deg f < q` and `deg_Y Aᵢ + deg f < q`, then
  `∑ᵢ f ^ (i c) · Aᵢ(X, X ^ q) = 0` if and only if every `Aᵢ` is zero.

## Implementation notes

Choose `a ∈ F` with `f(a) ≠ 0` and with `Bᵢ = Aᵢ(X, a)` not all zero
(`Polynomial.exists_eval_ne_zero_and_eval_C_ne_zero`). Modulo `(X - a) ^ q = X ^ q - a`
(`Polynomial.X_sub_C_pow_natCard`), the polynomial `X ^ q` acts as `a` and `f ^ q` as `f(a)`, so
`R = 0` gives `P(u) ≡ 0` for `P = ∑ᵢ Bᵢ Tⁱ` (Mathlib's `Polynomial.ofFn`) and `u = f ^ c`.
Kopparty squares this relation when `e = 2`. For general `e`, this file takes the norm
`N(T) = ∏_{k < e} P(ζᵏ T)` for a primitive `e`-th root of unity `ζ ∈ F`, which is `Q(Tᵉ)` with
`deg Q < e` (`Polynomial.expand_contract_prod_comp_C_mul_X`). Since `uᵉ = f ^ (q - 1)`, the
polynomial `G = f ^ (e - 1) · Q(f(a) / f)` is divisible by `(X - a) ^ q` and has degree less than
`q`, so `G = 0`. Hence `Q(f(a) / f) = 0` in the fraction field. The binomial `Tᵉ - f(a) / f` is
irreducible (`Polynomial.irreducible_X_pow_sub_C_div`, from Capelli's theorem) of degree
`e > deg P`, so `P = 0` (`Polynomial.eq_zero_of_prod_comp_C_mul_X_eq_expand`). That contradicts
the choice of `a`. For `f = 0` the hypothesis on `f` forces `e = 1`, and the sum is the one for
`f = 1`.

## References

* S. Kopparty, *The Weil bounds*, lecture notes, Topics in Finite Fields (Fall 2013), Rutgers
  University, §2.2, Lemma 3 (the case `e = 2`).
* S. A. Stepanov, *On the number of points of a hyperelliptic curve over a finite prime field*,
  Izv. Akad. Nauk SSSR Ser. Mat. 33 (1969).
* W. M. Schmidt, *Equations over Finite Fields: An Elementary Approach*, Lecture Notes in
  Mathematics 536, Springer (1976).
-/

public section

open Polynomial

namespace Polynomial

variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
/-- Modulo `(X - a) ^ q`, the sum `∑ᵢ f ^ (i c) · Aᵢ(X, X ^ q)` is `P(f ^ c)` for
`P = ∑ᵢ Aᵢ(X, a) Tⁱ`. -/
private theorem dvd_eval_sub_sum {e : ℕ} (a : F) (f : F[X]) (c : ℕ) (A : Fin e → F[X][X]) :
    (X - C a) ^ Nat.card F ∣ (∑ i : Fin e, monomial (i : ℕ) ((A i).eval (C a))).eval (f ^ c) -
      ∑ i : Fin e, f ^ ((i : ℕ) * c) * (A i).eval (X ^ Nat.card F) := by
  simp only [eval_finsetSum, eval_monomial, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun i _ ↦ ?_
  rw [pow_mul', mul_comm, ← mul_sub]
  exact dvd_mul_of_dvd_right (dvd_sub_comm.1 (X_sub_C_pow_natCard_dvd_eval_sub_eval a (A i))) _

/-- If `(X - a) ^ q` divides `Q(f ^ (q - 1))`, where `f(a) ≠ 0`, `deg Q < e` and the coefficients
of `Q` have degree at most `E` with `E + (e - 1) deg f < q`, then `Q(f(a) / f) = 0` in the
fraction field. -/
private theorem aeval_div_eq_zero_of_dvd {e E : ℕ} {f : F[X]} (hf₀ : f ≠ 0) {a : F}
    {Q : F[X][X]} (hQdeg : Q.natDegree < e) (hQcd : ∀ j, (Q.coeff j).natDegree ≤ E)
    (hE : E + (e - 1) * f.natDegree < Nat.card F)
    (hdvd : (X - C a) ^ Nat.card F ∣ Q.eval (f ^ (Nat.card F - 1))) :
    aeval (algebraMap F[X] (FractionRing F[X]) (C (f.eval a)) /
      algebraMap F[X] (FractionRing F[X]) f) Q = 0 := by
  set q := Nat.card F
  set G : F[X] := ∑ j ∈ Finset.range e, Q.coeff j * C (f.eval a) ^ j * f ^ (e - 1 - j)
  -- `f ^ q ≡ f(a)` modulo `(X - a) ^ q`, so `G ≡ f ^ (e - 1) · Q(f ^ (q - 1)) ≡ 0`.
  have hfq : (X - C a) ^ q ∣ f ^ q - C (f.eval a) :=
    X_sub_C_pow_natCard_dvd_pow_natCard_sub_C_eval a f
  have hG : (X - C a) ^ q ∣ G := by
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
    rw [← dvd_sub_right (dvd_mul_of_dvd_right hdvd (f ^ (e - 1))), eval_eq_sum_range' hQdeg,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun j hj ↦ ?_
    obtain ⟨hj', he1⟩ : j ≤ e - 1 ∧ 1 ≤ e := by
      simp only [Finset.mem_range] at hj; constructor <;> lia
    have hexp : (e - 1) + (q - 1) * j = q * j + (e - 1 - j) := by
      zify [hq1, hj', he1]
      ring
    have hpow : f ^ (e - 1) * (f ^ (q - 1)) ^ j = (f ^ q) ^ j * f ^ (e - 1 - j) := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, hexp]
    have : f ^ (e - 1) * (Q.coeff j * (f ^ (q - 1)) ^ j) - Q.coeff j * C (f.eval a) ^ j *
        f ^ (e - 1 - j) = Q.coeff j * f ^ (e - 1 - j) * ((f ^ q) ^ j - C (f.eval a) ^ j) := by
      linear_combination Q.coeff j * hpow
    rw [this]
    exact dvd_mul_of_dvd_right (hfq.trans (sub_dvd_pow_sub_pow _ _ _)) _
  have hG0 : G = 0 := by
    refine eq_zero_of_dvd_of_natDegree_lt (p := (X - C a) ^ q) hG ?_
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := E + (e - 1) * f.natDegree)
      fun j hj ↦ ?_) hE
    simp only [Finset.mem_range] at hj
    refine natDegree_mul_le.trans (add_le_add (natDegree_mul_le.trans ?_)
      (natDegree_pow_le.trans (Nat.mul_le_mul_right _ (by lia))))
    rw [← C_pow, natDegree_C, add_zero]
    exact hQcd _
  set K := FractionRing F[X]
  have hfK : algebraMap F[X] K f ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective F[X] K)).2 hf₀
  have hGK : algebraMap F[X] K G = algebraMap F[X] K f ^ (e - 1) *
      aeval (algebraMap F[X] K (C (f.eval a)) / algebraMap F[X] K f) Q := by
    rw [aeval_eq_sum_range' hQdeg, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' : e - 1 = j + (e - 1 - j) := by simp only [Finset.mem_range] at hj; lia
    have hsplit : algebraMap F[X] K f ^ (e - 1) =
        algebraMap F[X] K f ^ j * algebraMap F[X] K f ^ (e - 1 - j) := by rw [← pow_add, ← hj']
    rw [map_mul, map_mul, map_pow, map_pow, Algebra.smul_def, div_pow, hsplit]
    field_simp
  rw [hG0, map_zero, eq_comm, mul_eq_zero] at hGK
  exact hGK.resolve_left (pow_ne_zero _ hfK)

omit [Finite F] in
/-- For `P` of degree `< e` whose coefficients have degree at most `D`, the norm
`∏_{k < e} P(ζᵏ T)` is `Q(Tᵉ)` with `deg Q < e` and coefficients of degree at most `e D`. -/
private theorem exists_prod_comp_eq_expand {e D : ℕ} (he : e ≠ 0) {ζ : F}
    (hζ : IsPrimitiveRoot ζ e) {P : F[X][X]} (hPdeg : P.natDegree < e)
    (hPcd : ∀ j, (P.coeff j).natDegree ≤ D) :
    ∃ Q : F[X][X], ∏ k ∈ Finset.range e, P.comp (C (C ζ ^ k) * X) = expand F[X] e Q ∧
      Q.natDegree < e ∧ ∀ j, (Q.coeff j).natDegree ≤ e * D := by
  set N := ∏ k ∈ Finset.range e, P.comp (C (C ζ ^ k) * X)
  refine ⟨contract e N, (expand_contract_prod_comp_C_mul_X
    (hζ.map_of_injective C_injective) P).symm, ?_, fun j ↦ ?_⟩
  · have hP' : P.natDegree ≤ e - 1 := by lia
    have hNdeg : N.natDegree ≤ e * (e - 1) := by
      refine (natDegree_prod_le (Finset.range e) _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ (e - 1) fun k _ ↦ ?_).trans (by simp)
      exact natDegree_comp_le.trans ((Nat.mul_le_mul hP'
        ((natDegree_C_mul_le _ _).trans natDegree_X_le)).trans (by lia))
    suffices (contract e N).natDegree ≤ e - 1 by lia
    rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    rw [coeff_contract he]
    refine coeff_eq_zero_of_natDegree_lt (hNdeg.trans_lt ?_)
    have h1 : 1 ≤ e := by lia
    have h2 : e ≤ j := by lia
    zify [h1]
    nlinarith
  · rw [coeff_contract he]
    refine (natDegree_coeff_prod_le_of_le _ _ (a := D) (fun k _ i ↦ ?_) _).trans (by simp)
    rw [comp_C_mul_X_coeff]
    exact natDegree_mul_le.trans (by rw [← C_pow, ← C_pow, natDegree_C, add_zero]; exact hPcd _)

/-- The main case `f ≠ 0` of `Polynomial.sum_pow_mul_eval_X_pow_eq_zero_iff`. -/
private theorem forall_eq_zero_of_sum_pow_mul_eval_X_pow_eq_zero {e D : ℕ}
    (he : e ∣ Nat.card F - 1) {f : F[X]} (hf₀ : f ≠ 0)
    (hf : ∀ (b : F) (h : F[X]) (ℓ : ℕ), 1 < ℓ → ℓ ∣ e → f ≠ C b * h ^ ℓ)
    {A : Fin e → F[X][X]} (hA : ∀ i j, ((A i).coeff j).natDegree ≤ D)
    (hD : e * D + (e - 1) * f.natDegree < Nat.card F)
    (hY : ∀ i, (A i).natDegree + f.natDegree < Nat.card F)
    (hR : ∑ i : Fin e, f ^ ((i : ℕ) * ((Nat.card F - 1) / e)) * (A i).eval (X ^ Nat.card F) = 0) :
    ∀ i, A i = 0 := by
  classical
  by_contra! hne
  obtain ⟨i₀, hi₀⟩ := hne
  have he0 : e ≠ 0 := by rintro rfl; exact i₀.elim0
  set q := Nat.card F
  set c := (q - 1) / e
  obtain ⟨a, hfa, hAa⟩ := exists_eval_ne_zero_and_eval_C_ne_zero hf₀ hi₀ (hY i₀)
  set B : Fin e → F[X] := fun i ↦ (A i).eval (C a)
  have hB : ∀ i, (B i).natDegree ≤ D := fun i ↦ by
    simp only [B, eval_eq_sum_range]
    exact natDegree_sum_le_of_forall_le _ _ fun j _ ↦
      natDegree_mul_le.trans (by rw [← C_pow, natDegree_C, add_zero]; exact hA _ _)
  set P : F[X][X] := ofFn e B
  have hPdeg : P.natDegree < e := ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.2 he0) B
  have hPcd (j : ℕ) : (P.coeff j).natDegree ≤ D := by
    by_cases hj : j < e
    · rw [ofFn_coeff_eq_val_of_lt _ hj]
      exact hB _
    · rw [ofFn_coeff_eq_zero_of_ge _ (not_lt.1 hj), natDegree_zero]
      exact Nat.zero_le D
  have hPu : (X - C a) ^ q ∣ P.eval (f ^ c) := by
    have := dvd_eval_sub_sum a f c A
    rwa [hR, sub_zero, ← ofFn_eq_sum_monomial] at this
  -- `∏ₖ P(ζᵏ T) = Q(Tᵉ)` with `(X - a) ^ q ∣ Q(f ^ (q - 1))`, so `Q(f a / f) = 0`.
  obtain ⟨ζ, hζ⟩ := TauCeti.exists_isPrimitiveRoot_of_dvd_natCard_sub_one he
  obtain ⟨Q, hNQ, hQdeg, hQcd⟩ := exists_prod_comp_eq_expand he0 hζ hPdeg hPcd
  have hfc : f ^ (q - 1) = (f ^ c) ^ e := by rw [← pow_mul, Nat.div_mul_cancel he]
  have hQdvd : (X - C a) ^ q ∣ Q.eval (f ^ (q - 1)) := by
    rw [hfc]
    exact hPu.trans (eval_dvd_eval_pow_of_prod_comp_C_mul_X_eq_expand he0 hNQ _)
  have hQw := aeval_div_eq_zero_of_dvd hf₀ hQdeg hQcd hD hQdvd
  -- Map to the fraction field and apply Capelli's theorem.
  have hinj := IsFractionRing.injective F[X] (FractionRing F[X])
  set φ := algebraMap F[X] (FractionRing F[X])
  have hP0 : P.map φ = 0 := by
    refine eq_zero_of_prod_comp_C_mul_X_eq_expand (irreducible_X_pow_sub_C_div he0 hfa hf)
      (ζ := φ (C ζ)) (by rw [← map_pow, ← C_pow, hζ.pow_eq_one, C_1, map_one])
      ((natDegree_map_le).trans_lt hPdeg) (Q := Q.map φ) ?_ (by rwa [eval_map, ← aeval_def])
    rw [← map_expand, ← hNQ, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [map_comp, Polynomial.map_mul, map_C, map_X, map_pow φ]
  rw [Polynomial.map_eq_zero_iff hinj] at hP0
  have h₀ : P.coeff i₀ = B i₀ := ofFn_coeff_eq_val_of_lt _ i₀.isLt
  rw [hP0, coeff_zero] at h₀
  exact hAa h₀.symm

/-- **Stepanov's auxiliary polynomial is nonzero.** Let `F` be a finite field with `q` elements,
`e ∣ q - 1` and `c = (q - 1) / e`, and let `f` not be of the form `C b * hˡ` for any `ℓ > 1`
dividing `e`. If the coefficients of `A₀, …, A_{e-1} ∈ F[X][Y]` have degree at most `D` in `X`, with
`e D + (e - 1) deg f < q` and `deg_Y Aᵢ + deg f < q`, then
`∑ᵢ f ^ (i c) · Aᵢ(X, X ^ q) = 0` if and only if every `Aᵢ` is zero. -/
theorem sum_pow_mul_eval_X_pow_eq_zero_iff {e D : ℕ} (he : e ∣ Nat.card F - 1) {f : F[X]}
    (hf : ∀ (b : F) (h : F[X]) (ℓ : ℕ), 1 < ℓ → ℓ ∣ e → f ≠ C b * h ^ ℓ)
    {A : Fin e → F[X][X]} (hA : ∀ i j, ((A i).coeff j).natDegree ≤ D)
    (hD : e * D + (e - 1) * f.natDegree < Nat.card F)
    (hY : ∀ i, (A i).natDegree + f.natDegree < Nat.card F) :
    ∑ i : Fin e, f ^ ((i : ℕ) * ((Nat.card F - 1) / e)) * (A i).eval (X ^ Nat.card F) = 0 ↔
      ∀ i, A i = 0 := by
  refine ⟨fun hR ↦ ?_, fun h ↦ by simp [h]⟩
  rcases eq_or_ne f 0 with rfl | hf₀
  · -- For `f = 0` the hypothesis on `f` forces `e = 1`, and the sum is the one for `f = 1`.
    intro i
    have he0 : e ≠ 0 := by rintro rfl; exact i.elim0
    obtain rfl : e = 1 := by
      by_contra he1
      exact hf 0 0 e (by lia) dvd_rfl (by simp [he0])
    refine forall_eq_zero_of_sum_pow_mul_eval_X_pow_eq_zero he one_ne_zero
      (fun b h ℓ hℓ hℓ1 ↦ absurd (Nat.le_of_dvd one_pos hℓ1) (by lia)) hA (by simpa using hD)
      (by simpa using hY) (by simpa using hR) i
  · exact forall_eq_zero_of_sum_pow_mul_eval_X_pow_eq_zero he hf₀ hf hA hD hY hR

end Polynomial
