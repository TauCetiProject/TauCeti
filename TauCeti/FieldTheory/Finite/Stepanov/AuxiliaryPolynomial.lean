/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.RationalRoot
import TauCeti.FieldTheory.Finite.RootsOfUnity
import TauCeti.FieldTheory.Kummer.Capelli

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
* `Polynomial.irreducible_X_pow_sub_C_div`: over the fraction field of `F[X]`, for any field `F`,
  the binomial `Tᵉ - b / f` with `b ≠ 0` is irreducible under the same hypothesis on `f`.
* `Polynomial.coeff_prod_comp_C_mul_X_eq_zero`: for a primitive `e`-th root of unity `ζ` in a
  domain, the coefficients of `∏_{k < e} p(ζᵏ X)` vanish outside the multiples of `e`.
* `Polynomial.X_sub_C_pow_natCard`: `(X - a) ^ q = X ^ q - a` over a finite field with `q`
  elements.
* `Polynomial.exists_eval_ne_zero_and_eval_C_ne_zero`: a point `a ∈ F` where neither `f` nor
  `A(X, a)` vanishes, when the degrees are small.
* `Polynomial.natDegree_coeff_mul_le_of_le`, `Polynomial.natDegree_coeff_prod_le_of_le`: degree
  bounds for the coefficients of products in `R[X][X]`.

## Implementation notes

Choose `a ∈ F` with `f(a) ≠ 0` and with `Bᵢ = Aᵢ(X, a)` not all zero. Modulo
`(X - a) ^ q = X ^ q - a`, the polynomial `X ^ q` acts as `a` and `f ^ q` as `f(a)`, so `R = 0`
gives `P(u) ≡ 0` for `P = ∑ᵢ Bᵢ Tⁱ` and `u = f ^ c`. Kopparty squares this relation when `e = 2`.
For general `e`, this file takes the norm `N(T) = ∏_{k < e} P(ζᵏ T)` for a primitive `e`-th root
of unity `ζ ∈ F`. It is invariant under `T ↦ ζ T`, so `N(T) = Q(Tᵉ)` with `deg Q < e`. Since
`uᵉ = f ^ (q - 1)`, the polynomial `G = f ^ (e - 1) · Q(f(a) / f)` is divisible by `(X - a) ^ q`
and has degree less than `q`, so `G = 0`. Hence `Q(f(a) / f) = 0` in the fraction field, and
`P(ζᵏ t) = 0` for a root `t` of `Tᵉ - f(a) / f` and some `k`. Capelli's theorem
(`TauCeti.X_pow_sub_C_irreducible_of_forall_prime`) makes this binomial irreducible of degree `e`,
and `deg P < e`, so `P = 0`. That contradicts the choice of `a`.

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

section Bivariate

/-- If the coefficients of `P` and `Q` in `R[X][X]` have inner degree at most `a` and `b`, the
coefficients of `P * Q` have inner degree at most `a + b`. -/
theorem natDegree_coeff_mul_le_of_le {R : Type*} [Semiring R] {P Q : R[X][X]} {a b : ℕ}
    (hP : ∀ j, (P.coeff j).natDegree ≤ a) (hQ : ∀ j, (Q.coeff j).natDegree ≤ b) (n : ℕ) :
    ((P * Q).coeff n).natDegree ≤ a + b := by
  rw [coeff_mul]
  exact natDegree_sum_le_of_forall_le _ _ fun x _ ↦
    natDegree_mul_le.trans (add_le_add (hP _) (hQ _))

/-- If every coefficient of each `P i` has inner degree at most `a`, every coefficient of
`∏ i ∈ s, P i` has inner degree at most `#s * a`. -/
theorem natDegree_coeff_prod_le_of_le {R ι : Type*} [CommSemiring R] (s : Finset ι)
    (P : ι → R[X][X]) {a : ℕ}
    (hP : ∀ i ∈ s, ∀ j, ((P i).coeff j).natDegree ≤ a) (n : ℕ) :
    ((∏ i ∈ s, P i).coeff n).natDegree ≤ s.card * a := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => simp [coeff_one]; split_ifs <;> simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, add_mul, one_mul,
      add_comm (s.card * a)]
    exact natDegree_coeff_mul_le_of_le (hP i (Finset.mem_insert_self i s))
      (fun j ↦ ih (fun k hk ↦ hP k (Finset.mem_insert_of_mem hk)) j) n

end Bivariate

section Kummer

variable {F : Type*} [Field F]

/-- Over the fraction field of `F[X]`, the binomial `Tᵉ - c / f` is irreducible when `c ≠ 0` and
`f` is not of the form `C b * hˡ` for any `ℓ > 1` dividing `e`. -/
theorem irreducible_X_pow_sub_C_div {e : ℕ} (he : e ≠ 0) {f : F[X]} {c : F} (hc : c ≠ 0)
    (hf : ∀ (b : F) (h : F[X]) (ℓ : ℕ), 1 < ℓ → ℓ ∣ e → f ≠ C b * h ^ ℓ) :
    Irreducible (X ^ e - C (algebraMap F[X] (FractionRing F[X]) (C c) /
      algebraMap F[X] (FractionRing F[X]) f)) := by
  -- For `f = 0`, the hypothesis forces `e = 1`, and `T - 0` is irreducible.
  rcases eq_or_ne f 0 with rfl | hf₀
  · obtain rfl : e = 1 := by
      by_contra he1
      exact hf 0 0 e (by lia) dvd_rfl (by simp [he])
    rw [pow_one]
    exact irreducible_X_sub_C _
  set K := FractionRing F[X]
  have hinj := IsFractionRing.injective F[X] K
  have hfK : algebraMap F[X] K f ≠ 0 := (map_ne_zero_iff _ hinj).2 hf₀
  -- If `b ^ ℓ = d / f` with `d` a nonzero constant, then `b⁻¹ ^ ℓ` is the polynomial
  -- `C d⁻¹ * f`, so `b⁻¹` is a polynomial `g` since `F[X]` is integrally closed, and
  -- `f = C d * g ^ ℓ`.
  have key : ∀ (ℓ : ℕ) (d : F), 1 < ℓ → ℓ ∣ e → d ≠ 0 → ∀ b : K,
      b ^ ℓ ≠ algebraMap F[X] K (C d) / algebraMap F[X] K f := by
    intro ℓ d hℓ hℓe hd b hb
    have hCinv : algebraMap F[X] K (C d⁻¹) = (algebraMap F[X] K (C d))⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← map_mul, ← C_mul, inv_mul_cancel₀ hd, C_1, map_one])
    have hpow : b⁻¹ ^ ℓ = algebraMap F[X] K (C d⁻¹ * f) := by
      rw [inv_pow, hb, inv_div, map_mul, hCinv, div_eq_inv_mul]
    have hint : IsIntegral F[X] b⁻¹ :=
      IsIntegral.of_pow (by lia) (hpow ▸ isIntegral_algebraMap)
    obtain ⟨g, hg⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    have hgf : g ^ ℓ = C d⁻¹ * f := hinj (by rw [map_pow, hg, hpow])
    refine hf d g ℓ hℓ hℓe ?_
    rw [hgf, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hd, C_1, one_mul]
  refine TauCeti.X_pow_sub_C_irreducible_of_forall_prime he
    (fun ℓ hℓ hℓe b ↦ key ℓ c hℓ.one_lt hℓe hc b) fun h4 b hb ↦ ?_
  have h4F : (-4 : F) ≠ 0 := by
    intro h4F
    have : (-4 : K) = algebraMap F[X] K (C (-4)) := by simp only [map_neg, map_ofNat]
    rw [this, h4F, C_0, map_zero, zero_mul, eq_comm, div_eq_zero_iff] at hb
    exact hb.elim ((map_ne_zero_iff _ hinj).2 (C_ne_zero.2 hc)) hfK
  refine key 4 (c / -4) (by norm_num) h4 (div_ne_zero hc h4F) b ?_
  have h4K : (-4 : K) = algebraMap F[X] K (C (-4)) := by simp only [map_neg, map_ofNat]
  have h4K0 : (-4 : K) ≠ 0 := by
    rw [h4K]; exact (map_ne_zero_iff _ hinj).2 (C_ne_zero.2 h4F)
  have hinv : algebraMap F[X] K (C (-4)⁻¹) = (-4 : K)⁻¹ := by
    rw [h4K]; exact map_inv₀ ((algebraMap F[X] K).comp C) (-4)
  rw [div_eq_mul_inv c, C_mul, map_mul, hinv, mul_comm (algebraMap F[X] K (C c)), mul_div_assoc,
    ← hb, ← mul_assoc, inv_mul_cancel₀ h4K0, one_mul]

end Kummer

section Norm

variable {R : Type*} [CommRing R] [IsDomain R]

/-- For a primitive `e`-th root of unity `ζ` in a domain, the coefficients of the norm
`∏_{k < e} p(ζᵏ X)` vanish outside the multiples of `e`, since the norm is invariant under
`X ↦ ζ X`. -/
theorem coeff_prod_comp_C_mul_X_eq_zero {ζ : R} {e : ℕ} (hζ : IsPrimitiveRoot ζ e) (p : R[X])
    {n : ℕ} (hn : ¬e ∣ n) : (∏ k ∈ Finset.range e, p.comp (C (ζ ^ k) * X)).coeff n = 0 := by
  rcases Nat.eq_zero_or_pos e with rfl | he0
  · rw [Finset.range_zero, Finset.prod_empty, coeff_one]
    split_ifs with h
    · exact (hn (by simp [h])).elim
    · rfl
  have hstep : ∀ k, (p.comp (C (ζ ^ k) * X)).comp (C ζ * X) = p.comp (C (ζ ^ (k + 1)) * X) :=
    fun k ↦ by simp only [comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, pow_succ]
  have hcomp : (∏ k ∈ Finset.range e, p.comp (C (ζ ^ k) * X)).comp (C ζ * X) =
      ∏ k ∈ Finset.range e, p.comp (C (ζ ^ k) * X) := by
    rw [prod_comp]
    simp_rw [hstep]
    obtain ⟨e', he'⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by lia⟩
    rw [he', Finset.prod_range_succ, Finset.prod_range_succ' (fun k ↦ p.comp (C (ζ ^ k) * X))]
    congr 1
    rw [← he', hζ.pow_eq_one, pow_zero]
  have h := congrArg (fun q : R[X] ↦ q.coeff n) hcomp
  simp only [comp_C_mul_X_coeff] at h
  have hζn : ζ ^ n ≠ 1 := fun h' ↦ hn (hζ.dvd_of_pow_eq_one n h')
  have : (∏ k ∈ Finset.range e, p.comp (C (ζ ^ k) * X)).coeff n * (ζ ^ n - 1) = 0 := by
    rw [mul_sub, h, mul_one, sub_self]
  exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hζn)

end Norm

section FiniteField

variable {F : Type*} [Field F] [Finite F]

/-- If `f ≠ 0` and `A ≠ 0` in `F[X][X]` have degrees with sum less than `#F`, some `a ∈ F` has
`f a ≠ 0` and `A (C a) ≠ 0`. -/
theorem exists_eval_ne_zero_and_eval_C_ne_zero {f : F[X]} (hf : f ≠ 0) {A : F[X][X]} (hA : A ≠ 0)
    (hdeg : A.natDegree + f.natDegree < Nat.card F) :
    ∃ a : F, f.eval a ≠ 0 ∧ A.eval (C a) ≠ 0 := by
  classical
  have := Fintype.ofFinite F
  by_contra! H
  have h₁ : (Finset.univ.filter fun a ↦ f.eval a = 0).card ≤ f.natDegree :=
    calc _ ≤ f.roots.toFinset.card := Finset.card_le_card fun a ha ↦ by
            simp only [Finset.mem_filter] at ha; simp [mem_roots hf, ha.2]
      _ ≤ f.roots.card := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := card_roots' f
  have h₂ : (Finset.univ.filter fun a ↦ A.eval (C a) = 0).card ≤ A.natDegree :=
    calc _ ≤ A.roots.toFinset.card :=
          Finset.card_le_card_of_injOn C (fun a ha ↦ by
            simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at ha
            simp [mem_roots hA, ha]) C_injective.injOn
      _ ≤ A.roots.card := Multiset.toFinset_card_le _
      _ ≤ A.natDegree := card_roots' A
  have hsub : (Finset.univ : Finset F) ⊆ (Finset.univ.filter fun a ↦ f.eval a = 0) ∪
      (Finset.univ.filter fun a ↦ A.eval (C a) = 0) := by
    intro a _
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases ha : f.eval a = 0
    · exact Or.inl ha
    · exact Or.inr (H a ha)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hcard
  lia

/-- Over a finite field with `q` elements, `(X - a) ^ q = X ^ q - a`. -/
theorem X_sub_C_pow_natCard (a : F) : (X - C a) ^ Nat.card F = X ^ Nat.card F - C a := by
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, ← FiniteField.Polynomial.expand_card, map_sub, expand_X, expand_C]

/-- Modulo `(X - a) ^ q`, the sum `∑ᵢ f ^ (i c) · Aᵢ(X, X ^ q)` is `P(f ^ c)` for
`P = ∑ᵢ Aᵢ(X, a) Tⁱ`. -/
private theorem dvd_eval_sub_sum {e : ℕ} (a : F) (f : F[X]) (c : ℕ) (A : Fin e → F[X][X]) :
    (X - C a) ^ Nat.card F ∣ (∑ i : Fin e, C ((A i).eval (C a)) * X ^ (i : ℕ)).eval (f ^ c) -
      ∑ i : Fin e, f ^ ((i : ℕ) * c) * (A i).eval (X ^ Nat.card F) := by
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun i _ ↦ ?_
  rw [pow_mul', mul_comm, ← mul_sub]
  refine dvd_mul_of_dvd_right ?_ _
  rw [X_sub_C_pow_natCard]
  exact dvd_sub_comm.1 (sub_dvd_eval_sub _ _ _)

/-- If `(X - a) ^ q` divides `Q(f ^ (q - 1))`, where `f(a) ≠ 0`, `deg Q < e` and the coefficients
of `Q` have degree at most `E` with `E + (e - 1) deg f < q`, then `Q(f(a) / f) = 0` in the
fraction field. -/
private theorem aeval_div_eq_zero_of_dvd {e E : ℕ} {f : F[X]} (hf₀ : f ≠ 0) {a : F}
    {Q : F[X][X]} (hQdeg : Q.natDegree < e) (hQcd : ∀ j, (Q.coeff j).natDegree ≤ E)
    (hE : E + (e - 1) * f.natDegree < Nat.card F)
    (hdvd : (X - C a) ^ Nat.card F ∣ Q.eval (f ^ (Nat.card F - 1))) :
    aeval (algebraMap F[X] (FractionRing F[X]) (C (f.eval a)) /
      algebraMap F[X] (FractionRing F[X]) f) Q = 0 := by
  set q := Nat.card F with hq
  set G : F[X] := ∑ j ∈ Finset.range e, Q.coeff j * C (f.eval a) ^ j * f ^ (e - 1 - j)
  -- `f ^ q ≡ f(a)` modulo `(X - a) ^ q`, so `G ≡ f ^ (e - 1) · Q(f ^ (q - 1)) ≡ 0`.
  have hfq : (X - C a) ^ q ∣ f ^ q - C (f.eval a) := by
    have := Fintype.ofFinite F
    have h₁ : f ^ q = (f.map C).eval (X ^ q) := by
      rw [eval_map, hq, Nat.card_eq_fintype_card, ← FiniteField.Polynomial.expand_card,
        coe_expand]
    rw [h₁, ← eval₂_at_apply, ← eval_map, X_sub_C_pow_natCard]
    exact sub_dvd_eval_sub _ _ _
  have hG : (X - C a) ^ q ∣ G := by
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
    rw [← dvd_sub_right (dvd_mul_of_dvd_right hdvd (f ^ (e - 1))), eval_eq_sum_range' hQdeg,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun j hj ↦ ?_
    have hj' : j ≤ e - 1 := by simp only [Finset.mem_range] at hj; lia
    have hexp : (e - 1) + (q - 1) * j = q * j + (e - 1 - j) := by
      zify [hq1, hj', show 1 ≤ e by simp only [Finset.mem_range] at hj; lia]; ring
    have : f ^ (e - 1) * (Q.coeff j * (f ^ (q - 1)) ^ j) - Q.coeff j * C (f.eval a) ^ j *
        f ^ (e - 1 - j) = Q.coeff j * f ^ (e - 1 - j) * ((f ^ q) ^ j - C (f.eval a) ^ j) := by
      rw [← pow_mul, ← pow_mul, show f ^ (e - 1) * (Q.coeff j * f ^ ((q - 1) * j)) =
        Q.coeff j * f ^ ((e - 1) + (q - 1) * j) by ring, hexp]
      ring
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
    rw [map_mul, map_mul, map_pow, map_pow, Algebra.smul_def, div_pow,
      show algebraMap F[X] K f ^ (e - 1) =
        algebraMap F[X] K f ^ j * algebraMap F[X] K f ^ (e - 1 - j) by rw [← pow_add, ← hj']]
    field_simp
  rw [hG0, map_zero, eq_comm, mul_eq_zero] at hGK
  exact hGK.resolve_left (pow_ne_zero _ hfK)

/-- Over a field `K`, if `Tᵉ - w` is irreducible, `ζᵉ = 1`, `deg P < e` and
`∏_{k < e} P(ζᵏ T) = Q(Tᵉ)` with `Q(w) = 0`, then `P = 0`. -/
private theorem eq_zero_of_prod_comp_eq_expand {K : Type*} [Field K] {e : ℕ} (he : e ≠ 0)
    {w ζ : K} (hirr : Irreducible (X ^ e - C w)) (hζ : ζ ^ e = 1) {P Q : K[X]}
    (hPdeg : P.natDegree < e)
    (hNQ : ∏ k ∈ Finset.range e, P.comp (C (ζ ^ k) * X) = expand K e Q) (hQ : Q.eval w = 0) :
    P = 0 := by
  have := Fact.mk hirr
  set t : AdjoinRoot (X ^ e - C w) := AdjoinRoot.root (X ^ e - C w)
  have ht : t ^ e = algebraMap K _ w := by
    have := AdjoinRoot.aeval_eq (f := X ^ e - C w) (X ^ e - C w)
    rw [AdjoinRoot.mk_self, map_sub, aeval_X_pow, aeval_C] at this
    exact sub_eq_zero.1 this
  have hNt := congrArg (aeval t) hNQ
  rw [expand_aeval, ht, aeval_algebraMap_apply, coe_aeval_eq_eval, hQ, map_zero, map_prod] at hNt
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 hNt
  set s := algebraMap K _ (ζ ^ k) * t
  have hs : s ^ e = algebraMap K _ w := by
    rw [mul_pow, ← map_pow, ← pow_mul, pow_mul', hζ, one_pow, map_one, one_mul, ht]
  have hmin : X ^ e - C w = minpoly K s :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hs]) (monic_X_pow_sub_C _ he)
  have hPs : aeval s P = 0 := by simpa [aeval_comp, s] using hk
  have hdvd := minpoly.dvd K s hPs
  rw [← hmin] at hdvd
  exact eq_zero_of_dvd_of_natDegree_lt hdvd (by rw [natDegree_X_pow_sub_C]; exact hPdeg)

/-- A point `a` with `f a ≠ 0` (if `f ≠ 0`) and `A(X, a) ≠ 0`. -/
private theorem exists_eval_C_ne_zero {f : F[X]} {A : F[X][X]} (hA : A ≠ 0)
    (hdeg : A.natDegree + f.natDegree < Nat.card F) :
    ∃ a : F, (f ≠ 0 → f.eval a ≠ 0) ∧ A.eval (C a) ≠ 0 := by
  by_cases hf₀ : f = 0
  · obtain ⟨a, -, ha⟩ := exists_eval_ne_zero_and_eval_C_ne_zero one_ne_zero hA
      (by simpa [hf₀] using hdeg)
    exact ⟨a, fun h ↦ (h hf₀).elim, ha⟩
  · obtain ⟨a, h₁, h₂⟩ := exists_eval_ne_zero_and_eval_C_ne_zero hf₀ hA hdeg
    exact ⟨a, fun _ ↦ h₁, h₂⟩

omit [Finite F] in
/-- The polynomial `∑_{i < e} Bᵢ Tⁱ` has coefficients `Bᵢ`, degree `< e`, and coefficients of
degree at most `D` when every `Bᵢ` has. -/
private theorem sum_C_mul_X_pow_props {e D : ℕ} (he : e ≠ 0) {B : Fin e → F[X]}
    (hB : ∀ i, (B i).natDegree ≤ D) :
    (∀ i : Fin e, (∑ i : Fin e, C (B i) * X ^ (i : ℕ)).coeff i = B i) ∧
      (∑ i : Fin e, C (B i) * X ^ (i : ℕ)).natDegree < e ∧
      ∀ j, ((∑ i : Fin e, C (B i) * X ^ (i : ℕ)).coeff j).natDegree ≤ D := by
  refine ⟨fun i ↦ by simp [Fin.val_inj], lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _
    (n := e - 1) fun i _ ↦ (natDegree_C_mul_X_pow_le _ _).trans (by lia)) (by lia), fun j ↦ ?_⟩
  rw [finsetSum_coeff]
  refine natDegree_sum_le_of_forall_le _ _ fun i _ ↦ ?_
  rw [coeff_C_mul_X_pow]
  split_ifs
  · exact hB i
  · simp

omit [Finite F] in
/-- For `P` of degree `< e` whose coefficients have degree at most `D`, the norm
`∏_{k < e} P(ζᵏ T)` is `Q(Tᵉ)` with `deg Q < e` and coefficients of degree at most `e D`. -/
private theorem exists_prod_comp_eq_expand {e D : ℕ} (he : e ≠ 0) {ζ : F}
    (hζ : IsPrimitiveRoot ζ e) {P : F[X][X]} (hPdeg : P.natDegree < e)
    (hPcd : ∀ j, (P.coeff j).natDegree ≤ D) :
    ∃ Q : F[X][X], ∏ k ∈ Finset.range e, P.comp (C (C ζ ^ k) * X) = expand F[X] e Q ∧
      Q.natDegree < e ∧ ∀ j, (Q.coeff j).natDegree ≤ e * D := by
  set N := ∏ k ∈ Finset.range e, P.comp (C (C ζ ^ k) * X)
  refine ⟨contract e N, ?_, ?_, fun j ↦ ?_⟩
  · ext n : 2
    rw [coeff_expand (Nat.pos_of_ne_zero he)]
    split_ifs with h
    · rw [coeff_contract he, Nat.div_mul_cancel h]
    · exact coeff_prod_comp_C_mul_X_eq_zero (hζ.map_of_injective C_injective) P h
  · have hNdeg : N.natDegree ≤ e * (e - 1) := by
      refine (natDegree_prod_le (Finset.range e) _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ (e - 1) fun k _ ↦ ?_).trans (by simp)
      exact natDegree_comp_le.trans ((Nat.mul_le_mul (show P.natDegree ≤ e - 1 by lia)
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

omit [Finite F] in
/-- If `(X - a) ^ q ∣ P(u)` and `∏_{k < e} P(ζᵏ T) = Q(Tᵉ)`, then `(X - a) ^ q ∣ Q(uᵉ)`. -/
private theorem dvd_eval_of_prod_comp_eq_expand {e : ℕ} (he : e ≠ 0) {ζ : F} {P Q : F[X][X]}
    (hNQ : ∏ k ∈ Finset.range e, P.comp (C (C ζ ^ k) * X) = expand F[X] e Q) {u g : F[X]}
    (hPu : g ∣ P.eval u) : g ∣ Q.eval (u ^ e) := by
  rw [← expand_eval, ← hNQ, eval_prod]
  have h0 : (P.comp (C (C ζ ^ 0) * X)).eval u = P.eval u := by
    rw [pow_zero, C_1, one_mul, comp_X]
  refine hPu.trans ?_
  rw [← h0]
  exact Finset.dvd_prod_of_mem (fun k ↦ (P.comp (C (C ζ ^ k) * X)).eval u)
    (Finset.mem_range.2 (Nat.pos_of_ne_zero he))

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
  by_contra! hne
  obtain ⟨i₀, hi₀⟩ := hne
  have he0 : e ≠ 0 := by rintro rfl; exact i₀.elim0
  set q := Nat.card F
  set c := (q - 1) / e
  obtain ⟨a, hfa, hAa⟩ := exists_eval_C_ne_zero hi₀ (hY i₀)
  set B : Fin e → F[X] := fun i ↦ (A i).eval (C a)
  have hB : ∀ i, (B i).natDegree ≤ D := fun i ↦ by
    simp only [B, eval_eq_sum_range]
    exact natDegree_sum_le_of_forall_le _ _ fun j _ ↦
      natDegree_mul_le.trans (by rw [← C_pow, natDegree_C, add_zero]; exact hA _ _)
  set P : F[X][X] := ∑ i : Fin e, C (B i) * X ^ (i : ℕ)
  obtain ⟨hPcoeff, hPdeg, hPcd⟩ := sum_C_mul_X_pow_props he0 hB
  have hPu : (X - C a) ^ q ∣ P.eval (f ^ c) := by
    have := dvd_eval_sub_sum a f c A
    rwa [hR, sub_zero] at this
  -- If `f = 0`, then `e = 1` and `P = B₀` has degree `< q`, so `B₀ = 0`.
  by_cases hf₀ : f = 0
  · have he1 : e = 1 := by
      by_contra he1
      exact hf 0 0 e (by lia) dvd_rfl (by simp [hf₀, he0])
    subst he1
    have hB0 : B 0 = 0 := by
      refine eq_zero_of_dvd_of_natDegree_lt (p := (X - C a) ^ q) (by simpa [P] using hPu) ?_
      rw [natDegree_pow, natDegree_X_sub_C, mul_one]
      exact (hB 0).trans_lt (by simpa using hD)
    exact hAa (by rw [Subsingleton.elim i₀ 0]; exact hB0)
  -- Otherwise `∏ₖ P(ζᵏ T) = Q(Tᵉ)` with `(X - a) ^ q ∣ Q(f ^ (q - 1))`, so `Q(f a / f) = 0`.
  obtain ⟨ζ, hζ⟩ := TauCeti.exists_isPrimitiveRoot_of_dvd_natCard_sub_one he
  obtain ⟨Q, hNQ, hQdeg, hQcd⟩ := exists_prod_comp_eq_expand he0 hζ hPdeg hPcd
  have hQdvd : (X - C a) ^ q ∣ Q.eval (f ^ (q - 1)) := by
    rw [show f ^ (q - 1) = (f ^ c) ^ e by rw [← pow_mul, Nat.div_mul_cancel he]]
    exact dvd_eval_of_prod_comp_eq_expand he0 hNQ hPu
  have hQw := aeval_div_eq_zero_of_dvd hf₀ hQdeg hQcd hD hQdvd
  -- Map to the fraction field and apply Capelli's theorem.
  have hinj := IsFractionRing.injective F[X] (FractionRing F[X])
  set φ := algebraMap F[X] (FractionRing F[X])
  have hP0 : P.map φ = 0 := by
    refine eq_zero_of_prod_comp_eq_expand he0 (irreducible_X_pow_sub_C_div he0 (hfa hf₀) hf)
      (ζ := φ (C ζ)) (by rw [← map_pow, ← C_pow, hζ.pow_eq_one, C_1, map_one])
      ((natDegree_map_le).trans_lt hPdeg) (Q := Q.map φ) ?_ (by rwa [eval_map, ← aeval_def])
    rw [← map_expand, ← hNQ, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [map_comp, Polynomial.map_mul, map_C, map_X, map_pow φ]
  rw [Polynomial.map_eq_zero_iff hinj] at hP0
  have h₀ : P.coeff i₀ = B i₀ := hPcoeff i₀
  rw [hP0, coeff_zero] at h₀
  exact hAa h₀.symm

end FiniteField

end Polynomial
