/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.RingTheory.Ideal.Defs

import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring

/-!
# Denominators and congruences in the values of multivariate polynomials

Mathlib's `MvPolynomial.eval_mem` says that a polynomial with coefficients in a subsemiring takes
values in it at points with coordinates in it. If instead only the multiples `c xᵢ` of the
coordinates by a common denominator `c` lie in the subsemiring, then a polynomial of total degree
at most `T` has its value at `x` there after multiplication by `c ^ T`. This is the form in which
the denominators of algebraic numbers enter Liouville-type estimates: for a polynomial with
algebraic-integer coefficients evaluated at algebraic numbers with denominator `c`, the value has
denominator dividing `c ^ T`.

Over a commutative ring, evaluation also respects congruences modulo an element or an ideal: if
`xᵢ - tᵢ` lies in an ideal `I` for every variable `Xᵢ` occurring in `p`, then `p(x) - p(t) ∈ I`;
in particular, coordinatewise divisibility by `d` implies `d ∣ p(x) - p(t)`.

Over an ordered field, evaluating a polynomial at a coordinatewise rational map
`x ↦ (a ↦ N_a(x) / D_a(x))` on a domain where the denominators appearing in `p` do not vanish can
be cleared to a single polynomial `A` up to multiplication by a polynomial `B` that is strictly
positive on the domain (`MvPolynomial.exists_pos_eval_eq_mul_eval_div`).

When the coordinates of an evaluation lie in the base semiring of an algebra, applying a
base-linear functional to the resulting value is again polynomial in those coordinates.

Evaluation at a family `x` is surjective exactly when `x` generates the algebra, and its
bijectivity, which says that the `x i` are polynomial generators, is preserved by algebra
isomorphisms.

## Main results

* `MvPolynomial.exists_eval_eq_linearMap`: a base-linear image of an evaluation at base points.
* `MvPolynomial.pow_mul_eval_mem`: `c ^ T p(x)` lies in a subsemiring containing `c`, the
  coefficients of `p` and the `c xᵢ`, when `p` has total degree at most `T`.
* `MvPolynomial.eval_sub_eval_mem`, `MvPolynomial.eval_sub_eval_mem_of_vars`: values at points
  whose coordinates everywhere (or on the variables of `p`) are congruent modulo an ideal `I` are
  congruent modulo `I`.
* `MvPolynomial.dvd_eval_sub_eval`: values at points congruent modulo `d` are congruent modulo `d`.
* `MvPolynomial.aeval_surjective_iff_adjoin_range_eq_top`: `aeval x` is surjective exactly when
  the `x i` generate the algebra.
* `MvPolynomial.bijective_aeval_algEquiv_comp_iff`: an algebra isomorphism carries polynomial
  generators to polynomial generators.
* `MvPolynomial.exists_pos_eval_eq_mul_eval_div`: clears nonzero polynomial denominators in the
  value of a polynomial at a coordinatewise rational map by a strictly positive polynomial factor.
-/

public section

namespace MvPolynomial

variable {σ : Type*}

/-- A base-linear image of a polynomial evaluation at base points is again polynomial. -/
theorem exists_eval_eq_linearMap {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (f : S →ₗ[R] R) (p : MvPolynomial σ S) :
    ∃ q : MvPolynomial σ R, ∀ x : σ → R, eval x q = f (eval (algebraMap R S ∘ x) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨C (f a), fun _ ↦ by simp⟩
  | add p q hp hq =>
    obtain ⟨p', hp'⟩ := hp
    obtain ⟨q', hq'⟩ := hq
    exact ⟨p' + q', fun x ↦ by simp [hp' x, hq' x]⟩
  | mul_X p i hp =>
    obtain ⟨p', hp'⟩ := hp
    refine ⟨p' * X i, fun x ↦ ?_⟩
    simp only [map_mul, eval_X, Function.comp_apply, hp']
    rw [mul_comm (eval _ p), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

variable {S subS : Type*} [CommSemiring S] [SetLike subS S] [SubsemiringClass subS S]

/-- **Clearing denominators in a polynomial value.** If the coefficients of `p` lie in a
subsemiring `s`, `p` has total degree at most `T`, and `c ∈ s` is a common denominator of the
coordinates of `x`, that is `c xᵢ ∈ s` for all `i`, then `c ^ T p(x) ∈ s`. -/
theorem pow_mul_eval_mem {s : subS} {p : MvPolynomial σ S} (hp : ∀ m, p.coeff m ∈ s) {T : ℕ}
    (hT : p.totalDegree ≤ T) {c : S} (hc : c ∈ s) {x : σ → S} (hx : ∀ i, c * x i ∈ s) :
    c ^ T * eval x p ∈ s := by
  rw [eval_eq, Finset.mul_sum]
  refine sum_mem fun m hm ↦ ?_
  have hm' : ∑ i ∈ m.support, m i ≤ T := (le_totalDegree hm).trans hT
  -- Split `c ^ T` as `c ^ (T - |m|) c ^ |m|` and distribute `c ^ |m|` over the monomial.
  have h : c ^ T * (p.coeff m * ∏ i ∈ m.support, x i ^ m i) =
      c ^ (T - ∑ i ∈ m.support, m i) * p.coeff m * ∏ i ∈ m.support, (c * x i) ^ m i := by
    conv_lhs => rw [← Nat.sub_add_cancel hm', pow_add, ← Finset.prod_pow_eq_pow_sum]
    rw [Finset.prod_congr rfl fun i _ ↦ mul_pow c (x i) (m i), Finset.prod_mul_distrib]
    ring
  rw [h]
  exact mul_mem (mul_mem (pow_mem hc _) (hp m)) (prod_mem fun i _ ↦ pow_mem (hx i) _)

/-- The values of a polynomial at points that agree modulo an ideal `I` agree modulo `I`. -/
theorem eval_sub_eval_mem {R : Type*} [CommRing R] (p : MvPolynomial σ R) {I : Ideal R}
    {x t : σ → R} (h : ∀ i, x i - t i ∈ I) : eval x p - eval t p ∈ I := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simpa only [map_add, add_sub_add_comm] using I.add_mem hp hq
  | mul_X p i hp =>
    have hlin : eval x (p * X i) - eval t (p * X i) =
        (eval x p - eval t p) * x i + eval t p * (x i - t i) := by
      simp only [map_mul, eval_X]
      ring
    rw [hlin]
    exact I.add_mem (I.mul_mem_right _ hp) (I.mul_mem_left _ (h i))

/-- The values of a polynomial at points whose coordinates on `p.vars` agree modulo an ideal `I`
agree modulo `I`. -/
theorem eval_sub_eval_mem_of_vars {R : Type*} [CommRing R] (p : MvPolynomial σ R) {I : Ideal R}
    {x t : σ → R} (h : ∀ i ∈ p.vars, x i - t i ∈ I) : eval x p - eval t p ∈ I := by
  obtain ⟨q, hq⟩ := exists_rename_coe_vars_eq p
  rw [← hq, eval_rename, eval_rename]
  exact eval_sub_eval_mem q fun i ↦ h i i.property

/-- The values of a polynomial at points that agree modulo `d` agree modulo `d`. -/
theorem dvd_eval_sub_eval {R : Type*} [CommRing R] (p : MvPolynomial σ R) {d : R} {x t : σ → R}
    (h : ∀ i, d ∣ x i - t i) : d ∣ eval x p - eval t p := by
  rw [← Ideal.mem_span_singleton]
  exact eval_sub_eval_mem p fun i ↦ Ideal.mem_span_singleton.mpr (h i)

/-- Evaluation at a family `x` is surjective exactly when the `x i` generate the algebra. -/
theorem aeval_surjective_iff_adjoin_range_eq_top {R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] {x : σ → A} :
    Function.Surjective (aeval (R := R) x) ↔ Algebra.adjoin R (Set.range x) = ⊤ := by
  rw [← AlgHom.range_eq_top, Algebra.adjoin_range_eq_range_aeval]

/-- Composing a family with an algebra isomorphism `e` does not change whether evaluation at it is
bijective, since `aeval (e ∘ x) = e ∘ aeval x`. In particular `e` carries a family of polynomial
generators, algebraically independent and generating, to one. -/
theorem bijective_aeval_algEquiv_comp_iff {R A B : Type*} [CommSemiring R] [CommSemiring A]
    [CommSemiring B] [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) {x : σ → A} :
    Function.Bijective (aeval (R := R) (e ∘ x)) ↔ Function.Bijective (aeval (R := R) x) := by
  have h : (aeval (R := R) (e ∘ x) : MvPolynomial σ R → B) = e ∘ aeval x :=
    funext fun p ↦ (comp_aeval_apply x (e : A →ₐ[R] B) p).symm
  rw [h, e.bijective.of_comp_iff']

private theorem exists_pos_eval_eq_mul_eval_div_of_forall {α β K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {u : Set (β → K)} {N D : α → MvPolynomial β K}
    (hD : ∀ x ∈ u, ∀ a, eval x (D a) ≠ 0) (p : MvPolynomial α K) :
    ∃ A B : MvPolynomial β K, ∀ x ∈ u,
      0 < eval x B ∧ eval x A = eval x B * eval (fun a ↦ eval x (N a) / eval x (D a)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨C c, 1, fun _ _ ↦ ⟨by simp, by simp⟩⟩
  | add p q ihp ihq =>
    obtain ⟨A₁, B₁, h₁⟩ := ihp; obtain ⟨A₂, B₂, h₂⟩ := ihq
    refine ⟨A₁ * B₂ + A₂ * B₁, B₁ * B₂, fun x hx ↦ ?_⟩
    obtain ⟨hB₁, hA₁⟩ := h₁ x hx; obtain ⟨hB₂, hA₂⟩ := h₂ x hx
    exact ⟨by simp [mul_pos hB₁ hB₂], by simp only [map_add, map_mul, hA₁, hA₂]; ring⟩
  | mul_X p a ihp =>
    obtain ⟨A₁, B₁, h₁⟩ := ihp
    refine ⟨A₁ * (N a * D a), B₁ * (D a * D a), fun x hx ↦ ?_⟩
    obtain ⟨hB₁, hA₁⟩ := h₁ x hx
    have hDa : eval x (D a) ≠ 0 := hD x hx a
    have hmul : eval x (N a) * eval x (D a) =
        eval x (D a) * eval x (D a) * (eval x (N a) / eval x (D a)) := by
      rw [mul_assoc, mul_div_cancel₀ _ hDa, mul_comm]
    refine ⟨by simp [mul_pos hB₁ (mul_self_pos.2 hDa)], ?_⟩
    simp only [map_mul, eval_X, hA₁]
    rw [hmul]
    ring

/-- **Clearing polynomial denominators by a strictly positive polynomial factor.** Over an ordered
field, if the denominators `D a` for variables `a ∈ p.vars` do not vanish on `u`, then there exist
polynomials `A` and `B` with `0 < B(x)` and `A(x) = B(x) * p(N(x) / D(x))` for all `x ∈ u`. -/
theorem exists_pos_eval_eq_mul_eval_div {α β K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {u : Set (β → K)} {N D : α → MvPolynomial β K}
    (p : MvPolynomial α K) (hD : ∀ x ∈ u, ∀ a ∈ p.vars, eval x (D a) ≠ 0) :
    ∃ A B : MvPolynomial β K, ∀ x ∈ u,
      0 < eval x B ∧ eval x A = eval x B * eval (fun a ↦ eval x (N a) / eval x (D a)) p := by
  classical
  let N' (a : α) : MvPolynomial β K := if a ∈ p.vars then N a else 0
  let D' (a : α) : MvPolynomial β K := if a ∈ p.vars then D a else 1
  have hD' : ∀ x ∈ u, ∀ a, eval x (D' a) ≠ 0 := fun x hx a ↦ by
    by_cases ha : a ∈ p.vars
    · simpa [D', ha] using hD x hx a ha
    · simp [D', ha]
  obtain ⟨A, B, hAB⟩ := exists_pos_eval_eq_mul_eval_div_of_forall hD' p
  refine ⟨A, B, fun x hx ↦ ?_⟩
  have heval : eval (fun a ↦ eval x (N' a) / eval x (D' a)) p =
      eval (fun a ↦ eval x (N a) / eval x (D a)) p :=
    eval₂Hom_congr' rfl (fun a ha _ ↦ by simp [N', D', ha]) rfl
  obtain ⟨hB, hEq⟩ := hAB x hx; exact ⟨hB, heval ▸ hEq⟩

end MvPolynomial
