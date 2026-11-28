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
import TauCeti.Algebra.Polynomial.Bivariate.Basic
import TauCeti.Algebra.Polynomial.Degree.Operations
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
  most `D` in `X`, with `e D + (e - 1) deg f < q`, then `∑ᵢ f ^ (i c) · Aᵢ(X, X ^ q) = 0` if and
  only if every `Aᵢ` is zero.

## Implementation notes

For `e > 1` the bound on `e D + (e - 1) deg f` gives `deg f < q`, so some `a ∈ F` has
`f(a) ≠ 0`. If every `Aᵢ(X, a)` is zero, then `Aᵢ = (Y - a) A'ᵢ`, the coefficients of the `A'ᵢ`
again have degree at most `D` in `X`, and `R = (X ^ q - a) R'` for the sum `R'` of the `A'ᵢ`. So
it is enough to show that `R = 0` forces every `Bᵢ = Aᵢ(X, a)` to be zero, and an induction on
`∑ᵢ deg_Y Aᵢ` gives the claim.

Modulo `(X - a) ^ q = X ^ q - a` (`Polynomial.X_sub_C_pow_natCard`), the polynomial `X ^ q` acts
as `a` and `f ^ q` as `f(a)`, so `R = 0` gives `P(u) ≡ 0` for `P = ∑ᵢ Bᵢ Tⁱ` (Mathlib's
`Polynomial.ofFn`) and `u = f ^ c`. Kopparty squares this relation when `e = 2`. For general `e`,
this file takes the norm `N(T) = ∏_{k < e} P(ζᵏ T)` for a primitive `e`-th root of unity `ζ ∈ F`,
which is `Q(Tᵉ)` with `deg Q < e` (`Polynomial.expand_contract_prod_comp_C_mul_X`). Since
`uᵉ = f ^ (q - 1)`, the polynomial `G = f ^ (deg Q) · Q(f(a) / f)`, the value of
`Polynomial.scaleRoots Q f` at `f(a)`, is divisible by `(X - a) ^ q` and has degree less than `q`,
so `G = 0`. Hence `Q(f(a) / f) = 0` in the fraction field. The binomial `Tᵉ - f(a) / f` is
irreducible (`Polynomial.irreducible_X_pow_sub_C_div`, from Capelli's theorem) of degree
`e > deg P`, so `P = 0` (`Polynomial.eq_zero_of_prod_comp_C_mul_X_eq_expand`), and every `Bᵢ` is
zero. For `e = 1` the sum does not depend on `f`, and it is the one for `f = 1`.

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

/-- If `(X - a) ^ q` divides `Q(f ^ (q - 1))`, where `f ≠ 0`, `deg Q < e` and the coefficients
of `Q` have degree at most `E` with `E + (e - 1) deg f < q`, then `Q(f(a) / f) = 0` in the
fraction field. -/
private theorem aeval_div_eq_zero_of_dvd {e E : ℕ} {f : F[X]} (hf₀ : f ≠ 0) {a : F}
    {Q : F[X][X]} (hQdeg : Q.natDegree < e) (hQcd : ∀ j, (Q.coeff j).natDegree ≤ E)
    (hE : E + (e - 1) * f.natDegree < Nat.card F)
    (hdvd : (X - C a) ^ Nat.card F ∣ Q.eval (f ^ (Nat.card F - 1))) :
    aeval (algebraMap F[X] (FractionRing F[X]) (C (f.eval a)) /
      algebraMap F[X] (FractionRing F[X]) f) Q = 0 := by
  set q := Nat.card F
  -- `f ^ q ≡ f(a)` modulo `(X - a) ^ q`, so `G = (scaleRoots Q f)(f(a))` is congruent to
  -- `(scaleRoots Q f)(f ^ q) = f ^ deg Q · Q(f ^ (q - 1))` (`Polynomial.scaleRoots_eval_mul`).
  have hfq : (X - C a) ^ q ∣ f ^ q - C (f.eval a) :=
    X_sub_C_pow_natCard_dvd_pow_natCard_sub_C_eval a f
  have hG : (X - C a) ^ q ∣ (Q.scaleRoots f).eval (C (f.eval a)) := by
    have h1 : (X - C a) ^ q ∣ (Q.scaleRoots f).eval (f ^ q) := by
      rw [← mul_pow_sub_one Nat.card_pos.ne' f, scaleRoots_eval_mul]
      exact dvd_mul_of_dvd_right hdvd _
    exact (dvd_sub_right h1).1 (hfq.trans (sub_dvd_eval_sub _ _ _))
  have hG0 : (Q.scaleRoots f).eval (C (f.eval a)) = 0 := by
    refine eq_zero_of_dvd_of_natDegree_lt hG ?_
    rw [natDegree_pow, natDegree_X_sub_C, mul_one, eval_eq_sum_range, natDegree_scaleRoots]
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := E + (e - 1) * f.natDegree)
      fun j _ ↦ ?_) hE
    rw [coeff_scaleRoots, ← C_pow]
    refine (natDegree_mul_C_le _ _).trans (natDegree_mul_le.trans (add_le_add (hQcd _) ?_))
    exact natDegree_pow_le.trans (Nat.mul_le_mul_right _ (by lia))
  -- In the fraction field, `G = f ^ deg Q · Q(f(a) / f)` (`Polynomial.scaleRoots_eval₂_mul`).
  set φ := algebraMap F[X] (FractionRing F[X])
  have hfK : φ f ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective F[X] _)).2 hf₀
  have h := scaleRoots_eval₂_mul (p := Q) φ (φ (C (f.eval a)) / φ f) f
  rw [mul_div_cancel₀ _ hfK, eval₂_at_apply, hG0, map_zero, eq_comm, ← aeval_def] at h
  exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hfK)

omit [Finite F] in
/-- For `P` of degree `< e` whose coefficients have degree at most `D`, the norm
`∏_{k < e} P(ζᵏ T)` is `Q(Tᵉ)` with `deg Q < e` and coefficients of degree at most `e D`. -/
private theorem exists_prod_comp_eq_expand {e D : ℕ} (he : e ≠ 0) {ζ : F}
    (hζ : IsPrimitiveRoot ζ e) {P : F[X][X]} (hPdeg : P.natDegree < e)
    (hPcd : ∀ j, (P.coeff j).natDegree ≤ D) :
    ∃ Q : F[X][X], ∏ k ∈ Finset.range e, P.comp (C (C ζ ^ k) * X) = expand F[X] e Q ∧
      Q.natDegree < e ∧ ∀ j, (Q.coeff j).natDegree ≤ e * D := by
  set N := ∏ k ∈ Finset.range e, P.comp (C (C ζ ^ k) * X)
  have hN : expand F[X] e (contract e N) = N :=
    expand_contract_prod_comp_C_mul_X (hζ.map_of_injective C_injective) P
  refine ⟨contract e N, hN.symm, ?_, fun j ↦ ?_⟩
  · have hP' : P.natDegree ≤ e - 1 := by lia
    have hNdeg : N.natDegree ≤ e * (e - 1) := by
      refine (natDegree_prod_le (Finset.range e) _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ (e - 1) fun k _ ↦ ?_).trans (by simp)
      exact (natDegree_comp_C_mul_X_le _ _).trans hP'
    rw [← hN, natDegree_expand, mul_comm e] at hNdeg
    have := Nat.le_of_mul_le_mul_right hNdeg (Nat.pos_of_ne_zero he)
    lia
  · rw [coeff_contract he]
    refine (natDegree_coeff_prod_le_of_le _ _ (a := fun _ ↦ D) (fun k _ i ↦ ?_) _).trans (by simp)
    rw [comp_C_mul_X_coeff]
    exact natDegree_mul_le.trans (by rw [← C_pow, ← C_pow, natDegree_C, add_zero]; exact hPcd _)

/-- If `f ≠ 0`, `f(a) ≠ 0` and `∑ᵢ f ^ (i c) · Aᵢ(X, X ^ q) = 0` under the degree bound of
`Polynomial.sum_pow_mul_eval_X_pow_eq_zero_iff`, then every `Aᵢ` vanishes at `Y = a`. -/
private theorem eval_C_eq_zero_of_sum_pow_mul_eval_X_pow_eq_zero {e D : ℕ}
    (he : e ∣ Nat.card F - 1) {f : F[X]} (hf₀ : f ≠ 0) {a : F} (hfa : f.eval a ≠ 0)
    (hf : ∀ (b : F) (h : F[X]) (ℓ : ℕ), 1 < ℓ → ℓ ∣ e → f ≠ C b * h ^ ℓ)
    {A : Fin e → F[X][X]} (hA : ∀ i j, ((A i).coeff j).natDegree ≤ D)
    (hD : e * D + (e - 1) * f.natDegree < Nat.card F)
    (hR : ∑ i : Fin e, f ^ ((i : ℕ) * ((Nat.card F - 1) / e)) * (A i).eval (X ^ Nat.card F) = 0)
    (i₀ : Fin e) : (A i₀).eval (C a) = 0 := by
  classical
  by_contra hAa
  have he0 : e ≠ 0 := by rintro rfl; exact i₀.elim0
  set q := Nat.card F
  set c := (q - 1) / e
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
    refine eq_zero_of_prod_comp_C_mul_X_eq_expand (irreducible_X_pow_sub_C_div he0 hfa hf).prime
      (ζ := φ (C ζ)) ((map_ne_zero_iff _ hinj).2 (C_ne_zero.2 (hζ.ne_zero he0)))
      ((natDegree_map_le).trans_lt hPdeg) (Q := Q.map φ) ?_ (by rwa [eval_map, ← aeval_def])
    rw [← map_expand, ← hNQ, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [map_comp, Polynomial.map_mul, map_C, map_X, map_pow φ]
  rw [Polynomial.map_eq_zero_iff hinj] at hP0
  have h₀ : P.coeff i₀ = B i₀ := ofFn_coeff_eq_val_of_lt _ i₀.isLt
  rw [hP0, coeff_zero] at h₀
  exact hAa h₀.symm

/-- The case `f ≠ 0` of `Polynomial.sum_pow_mul_eval_X_pow_eq_zero_iff`, for `a` with `f(a) ≠ 0`.
Every `Aᵢ` vanishes at `Y = a`, so `Aᵢ = (Y - a) A'ᵢ`, and the `A'ᵢ` satisfy the same hypotheses
with a smaller sum of degrees in `Y`. -/
private theorem forall_eq_zero_of_sum_pow_mul_eval_X_pow_eq_zero {e D : ℕ}
    (he : e ∣ Nat.card F - 1) {f : F[X]} (hf₀ : f ≠ 0) {a : F} (hfa : f.eval a ≠ 0)
    (hf : ∀ (b : F) (h : F[X]) (ℓ : ℕ), 1 < ℓ → ℓ ∣ e → f ≠ C b * h ^ ℓ)
    (hD : e * D + (e - 1) * f.natDegree < Nat.card F) {A : Fin e → F[X][X]}
    (hA : ∀ i j, ((A i).coeff j).natDegree ≤ D)
    (hR : ∑ i : Fin e, f ^ ((i : ℕ) * ((Nat.card F - 1) / e)) * (A i).eval (X ^ Nat.card F) = 0) :
    ∀ i, A i = 0 := by
  induction hn : ∑ i, (A i).natDegree using Nat.strong_induction_on generalizing A with
  | _ n ih =>
  by_cases hA0 : ∀ i, A i = 0
  · exact hA0
  obtain ⟨i₀, hi₀⟩ := not_forall.1 hA0
  have h0 := eval_C_eq_zero_of_sum_pow_mul_eval_X_pow_eq_zero he hf₀ hfa hf hA hD hR
  set A' : Fin e → F[X][X] := fun i ↦ A i /ₘ (X - C (C a))
  have hAA' (i : Fin e) : A i = (X - C (C a)) * A' i :=
    (mul_divByMonic_eq_iff_isRoot.2 (h0 i)).symm
  have hA' (i : Fin e) (j : ℕ) : ((A' i).coeff j).natDegree ≤ D := by
    rw [coeff_divByMonic_X_sub_C]
    exact natDegree_sum_le_of_forall_le _ _ fun k _ ↦ by
      rw [← C_pow]
      exact (natDegree_C_mul_le _ _).trans (hA _ _)
  have hR' : ∑ i : Fin e, f ^ ((i : ℕ) * ((Nat.card F - 1) / e)) *
      (A' i).eval (X ^ Nat.card F) = 0 := by
    have hXq : (X ^ Nat.card F - C a : F[X]) ≠ 0 := X_pow_sub_C_ne_zero Nat.card_pos a
    refine (mul_eq_zero.1 (Eq.trans ?_ hR)).resolve_left hXq
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hAA' i, eval_mul, eval_sub, eval_X, eval_C]
    ring
  have hdeg (i : Fin e) (hi : A' i ≠ 0) : (A' i).natDegree < (A i).natDegree := by
    rw [hAA' i, natDegree_mul (X_sub_C_ne_zero _) hi, natDegree_X_sub_C]
    lia
  have hlt : ∑ i, (A' i).natDegree < n := by
    rw [← hn]
    refine Finset.sum_lt_sum (fun i _ ↦ ?_) ⟨i₀, Finset.mem_univ _, hdeg i₀ fun h ↦ hi₀ ?_⟩
    · by_cases hi : A' i = 0
      · rw [hi, natDegree_zero]
        exact Nat.zero_le _
      · exact (hdeg i hi).le
    · rw [hAA' i₀, h, mul_zero]
  have h' := ih _ hlt hA' hR' rfl
  intro i
  rw [hAA' i, h' i, mul_zero]

/-- **Stepanov's auxiliary polynomial is nonzero.** Let `F` be a finite field with `q` elements,
`e ∣ q - 1` and `c = (q - 1) / e`, and let `f` not be of the form `C b * hˡ` for any `ℓ > 1`
dividing `e`. If the coefficients of `A₀, …, A_{e-1} ∈ F[X][Y]` have degree at most `D` in `X`, with
`e D + (e - 1) deg f < q`, then `∑ᵢ f ^ (i c) · Aᵢ(X, X ^ q) = 0` if and only if every `Aᵢ` is
zero. -/
theorem sum_pow_mul_eval_X_pow_eq_zero_iff {e D : ℕ} (he : e ∣ Nat.card F - 1) {f : F[X]}
    (hf : ∀ (b : F) (h : F[X]) (ℓ : ℕ), 1 < ℓ → ℓ ∣ e → f ≠ C b * h ^ ℓ)
    {A : Fin e → F[X][X]} (hA : ∀ i j, ((A i).coeff j).natDegree ≤ D)
    (hD : e * D + (e - 1) * f.natDegree < Nat.card F) :
    ∑ i : Fin e, f ^ ((i : ℕ) * ((Nat.card F - 1) / e)) * (A i).eval (X ^ Nat.card F) = 0 ↔
      ∀ i, A i = 0 := by
  refine ⟨fun hR ↦ ?_, fun h ↦ by simp [h]⟩
  rcases lt_trichotomy e 1 with he1 | rfl | he1
  · intro i
    exact absurd i.isLt (by lia)
  · -- For `e = 1` the sum does not depend on `f`, and it is the one for `f = 1`.
    exact forall_eq_zero_of_sum_pow_mul_eval_X_pow_eq_zero he one_ne_zero (a := 0)
      (by rw [eval_one]; exact one_ne_zero)
      (fun b h ℓ hℓ hℓ1 ↦ absurd (Nat.le_of_dvd one_pos hℓ1) (by lia)) (by simpa using hD) hA
      (by simpa using hR)
  · -- For `e > 1` the hypothesis on `f` gives `f ≠ 0`, and `deg f < q`, so `f(a) ≠ 0` for some `a`.
    have he0 : e ≠ 0 := by lia
    have hf₀ : f ≠ 0 := by
      rintro rfl
      exact hf 0 0 e he1 dvd_rfl (by simp [he0])
    have hfq : f.natDegree < Nat.card F :=
      (Nat.le_mul_of_pos_left _ (by lia)).trans_lt ((Nat.le_add_left _ _).trans_lt hD)
    obtain ⟨a, hfa⟩ := exists_eval_ne_zero_of_natDegree_lt_card f hf₀ (by
      rw [← Nat.cast_card]
      exact_mod_cast hfq)
    exact forall_eq_zero_of_sum_pow_mul_eval_X_pow_eq_zero he hf₀ hfa hf hD hA hR

end Polynomial
