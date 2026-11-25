/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv

import TauCeti.Algebra.MvPolynomial.Eval
import TauCeti.Algebra.MvPolynomial.PDeriv

/-!
# Strongly and weakly divisible values of multivariate polynomials

Let `f` be a multivariate polynomial over a commutative ring `R`, let `a` be a point and let
`p, q ∈ R`. Following Poonen and Bhargava, `q` *strongly divides* `f` at `a` modulo `p`
(`MvPolynomial.StronglyDvdAt`) if `q ∣ f(a')` for every point `a'` congruent to `a` modulo `p`,
and `q` *weakly divides* `f` at `a` modulo `p` (`MvPolynomial.WeaklyDvdAt`) if `q ∣ f(a)` but
`q` does not strongly divide `f` at `a`. The case of interest is `R = ℤ`, `p` a prime and
`q = p ^ j`: for an integral invariant `f` on a lattice of coefficient vectors, such as the
discriminant of binary forms, the vectors at which `p ^ 2` strongly divides `f` form a union of
residue classes modulo `p`, which a geometric sieve controls, while the weakly divisible ones are
counted by a separate, uniformity estimate.

Strong divisibility depends only on `a` modulo `p`; weak divisibility depends only on `a`
modulo `q` when `p ∣ q`. If `q ∣ p` then strong divisibility is just `q ∣ f(a)`, so there is no
weak divisibility; in particular there are no weak multiples of `p` itself. When `p` is a
non-zero-divisor, the first-order Taylor expansion `f(a + p b) ≡ f(a) + p ∑ᵢ bᵢ ∂ᵢf(a)` modulo
`p ^ 2` gives the gradient criterion: `p ^ 2` strongly divides `f` at `a` if and only if
`p ^ 2 ∣ f(a)` and `p ∣ ∂ᵢf(a)` for every `i`. Consequently the reduction of `a` along any ring
homomorphism killing `p` (such as `ℤ → ℤ/pℤ`) lies on the common zero locus of `f` and all its
partial derivatives.

## Main definitions

* `MvPolynomial.StronglyDvdAt f p q a`: `q ∣ f(a')` for every `a'` congruent to `a` modulo `p`.
* `MvPolynomial.WeaklyDvdAt f p q a`: `q ∣ f(a)`, but `q` does not strongly divide `f` at `a`.

## Main results

* `MvPolynomial.stronglyDvdAt_iff`, `MvPolynomial.weaklyDvdAt_iff`: the defining conditions.
* `MvPolynomial.stronglyDvdAt_iff_forall_add_smul`: strong divisibility in terms of the
  translates `a + p • b`.
* `MvPolynomial.stronglyDvdAt_congr`, `MvPolynomial.weaklyDvdAt_congr`: strong divisibility
  depends only on `a` modulo `p`, and weak divisibility only on `a` modulo `q` when `p ∣ q`.
* `MvPolynomial.dvd_eval_iff_stronglyDvdAt_or_weaklyDvdAt`: `q ∣ f(a)` exactly when `q`
  divides `f` at `a` strongly or weakly (and never both).
* `MvPolynomial.stronglyDvdAt_iff_dvd_eval_of_dvd`, `MvPolynomial.not_weaklyDvdAt_of_dvd`: if
  `q ∣ p`, strong divisibility is divisibility of the value, and there is no weak divisibility.
* `MvPolynomial.stronglyDvdAt_sq_iff`: the gradient criterion for `p ^ 2`, when `p` is a
  non-zero-divisor.
* `MvPolynomial.weaklyDvdAt_sq_iff`, `MvPolynomial.weaklyDvdAt_sq_of_not_dvd_eval_pderiv`: when
  `p` is a non-zero-divisor, `p ^ 2` weakly divides `f` at `a` exactly when `p ^ 2 ∣ f(a)` and
  some partial derivative `∂ᵢf(a)` is not divisible by `p`.
* `MvPolynomial.StronglyDvdAt.eval₂_eq_zero`,
  `MvPolynomial.StronglyDvdAt.eval₂_pderiv_eq_zero`: modulo `p`, a point at which `p ^ 2`
  strongly divides `f` reduces into the zero locus of `f` and, when `p` is a non-zero-divisor,
  of every `∂ᵢf`.

## References

* B. Poonen, *Squarefree values of multivariable polynomials*, Duke Math. J. 118 (2003),
  353–373, §5.
* M. Bhargava, *The geometric sieve and the density of squarefree values of invariant
  polynomials*, arXiv:1402.0031, §3.3, (23)–(24) and Lemma 3.6.
* M. Bhargava and A. Shankar, *Binary quartic forms having bounded invariants, and the
  boundedness of the average rank of elliptic curves*, Ann. of Math. 181 (2015), 191–242, §2.6.
-/

public section

namespace MvPolynomial

variable {R S σ : Type*} [CommRing R] [CommSemiring S]

/-- `q` *strongly divides* the polynomial `f` at the point `a` modulo `p` if `q` divides the
value of `f` at every point congruent to `a` modulo `p`, coordinatewise. For `R = ℤ`, a prime `p`
and `q = p ^ j`, this says that `f` is strongly a multiple of `p ^ j` at `a`. -/
def StronglyDvdAt (f : MvPolynomial σ R) (p q : R) (a : σ → R) : Prop :=
  ∀ a' : σ → R, (∀ i, p ∣ a' i - a i) → q ∣ eval a' f

/-- `q` *weakly divides* the polynomial `f` at the point `a` modulo `p` if `q` divides the value
`f(a)` but does not strongly divide `f` at `a` modulo `p`. -/
def WeaklyDvdAt (f : MvPolynomial σ R) (p q : R) (a : σ → R) : Prop :=
  q ∣ eval a f ∧ ¬ f.StronglyDvdAt p q a

variable {f : MvPolynomial σ R} {p q : R} {a a' : σ → R}

/-- Unfolding lemma for `MvPolynomial.StronglyDvdAt`. -/
theorem stronglyDvdAt_iff :
    f.StronglyDvdAt p q a ↔ ∀ a' : σ → R, (∀ i, p ∣ a' i - a i) → q ∣ eval a' f :=
  Iff.rfl

/-- Unfolding lemma for `MvPolynomial.WeaklyDvdAt`. -/
theorem weaklyDvdAt_iff : f.WeaklyDvdAt p q a ↔ q ∣ eval a f ∧ ¬ f.StronglyDvdAt p q a :=
  Iff.rfl

/-- Strong divisibility at `a` modulo `p` is divisibility of the values at all the translates
`a + p • b`. -/
theorem stronglyDvdAt_iff_forall_add_smul :
    f.StronglyDvdAt p q a ↔ ∀ b : σ → R, q ∣ eval (a + p • b) f := by
  refine ⟨fun h b ↦ h _ fun i ↦ ⟨b i, by simp⟩, fun h a' ha' ↦ ?_⟩
  choose b hb using ha'
  have ha' : a' = a + p • b := funext fun i ↦ by simp [← hb i]
  exact ha' ▸ h b

/-- If `q` strongly divides `f` at `a`, then it divides the value `f(a)`. -/
theorem StronglyDvdAt.dvd_eval (h : f.StronglyDvdAt p q a) : q ∣ eval a f :=
  h a fun i ↦ by simp

/-- Strong divisibility depends only on the point modulo `p`. -/
theorem stronglyDvdAt_congr (h : ∀ i, p ∣ a' i - a i) :
    f.StronglyDvdAt p q a' ↔ f.StronglyDvdAt p q a :=
  ⟨fun h' x hx ↦ h' x fun i ↦ by simpa using dvd_sub (hx i) (h i),
    fun h' x hx ↦ h' x fun i ↦ by simpa using dvd_add (hx i) (h i)⟩

/-- Strong divisibility is unchanged by translating the point by `p` times a vector. -/
@[simp]
theorem stronglyDvdAt_add_smul_iff (b : σ → R) :
    f.StronglyDvdAt p q (a + p • b) ↔ f.StronglyDvdAt p q a :=
  stronglyDvdAt_congr fun i ↦ by simp

/-- If `q` weakly divides `f` at `a`, then it divides the value `f(a)`. -/
theorem WeaklyDvdAt.dvd_eval (h : f.WeaklyDvdAt p q a) : q ∣ eval a f :=
  h.1

/-- Weak divisibility excludes strong divisibility. -/
theorem WeaklyDvdAt.not_stronglyDvdAt (h : f.WeaklyDvdAt p q a) : ¬ f.StronglyDvdAt p q a :=
  h.2

/-- `q` divides the value `f(a)` exactly when it divides `f` at `a` strongly or weakly; by
`MvPolynomial.WeaklyDvdAt.not_stronglyDvdAt` the two cases are exclusive. -/
theorem dvd_eval_iff_stronglyDvdAt_or_weaklyDvdAt :
    q ∣ eval a f ↔ f.StronglyDvdAt p q a ∨ f.WeaklyDvdAt p q a :=
  ⟨fun h ↦ (em _).imp_right fun hs ↦ ⟨h, hs⟩, fun h ↦ h.elim StronglyDvdAt.dvd_eval (·.1)⟩

/-- When `p ∣ q`, weak divisibility depends only on the point modulo `q`. -/
theorem weaklyDvdAt_congr (hpq : p ∣ q) (h : ∀ i, q ∣ a' i - a i) :
    f.WeaklyDvdAt p q a' ↔ f.WeaklyDvdAt p q a := by
  rw [weaklyDvdAt_iff, weaklyDvdAt_iff, stronglyDvdAt_congr fun i ↦ hpq.trans (h i),
    dvd_iff_dvd_of_dvd_sub (dvd_eval_sub_eval f h)]

/-- If `q ∣ p`, then `q` strongly divides `f` at `a` modulo `p` exactly when it divides the
value `f(a)`, since all values at points congruent to `a` modulo `p` are congruent modulo `q`. -/
theorem stronglyDvdAt_iff_dvd_eval_of_dvd (hqp : q ∣ p) :
    f.StronglyDvdAt p q a ↔ q ∣ eval a f :=
  ⟨StronglyDvdAt.dvd_eval, fun h _ ha' ↦
    (dvd_iff_dvd_of_dvd_sub (dvd_eval_sub_eval f fun i ↦ hqp.trans (ha' i))).2 h⟩

/-- `p` strongly divides `f` at `a` modulo `p` exactly when `p ∣ f(a)`. -/
@[simp]
theorem stronglyDvdAt_self_iff : f.StronglyDvdAt p p a ↔ p ∣ eval a f :=
  stronglyDvdAt_iff_dvd_eval_of_dvd dvd_rfl

/-- If `q ∣ p`, then `q` never weakly divides `f` modulo `p`: in particular there are no weak
multiples of `p` itself. -/
theorem not_weaklyDvdAt_of_dvd (hqp : q ∣ p) : ¬ f.WeaklyDvdAt p q a :=
  fun h ↦ h.2 ((stronglyDvdAt_iff_dvd_eval_of_dvd hqp).2 h.1)

/-- **Gradient criterion, necessity.** If `p` is a non-zero-divisor and `p ^ 2` strongly divides
`f` at `a` modulo `p`, then `p` divides every partial derivative `∂ᵢf(a)`. -/
theorem StronglyDvdAt.dvd_eval_pderiv (hp : IsLeftRegular p) (h : f.StronglyDvdAt p (p ^ 2) a)
    (i : σ) : p ∣ eval a (pderiv i f) := by
  classical
  rw [stronglyDvdAt_iff_forall_add_smul] at h
  have hsum : ∑ j ∈ f.vars, eval a (pderiv j f) * (Pi.single i 1 : σ → R) j =
      eval a (pderiv i f) := by
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
    split_ifs with hi
    · rfl
    · simp [pderiv_eq_zero_of_notMem_vars hi]
  have htaylor := sq_dvd_eval_add_smul_sub_sum_pderiv f p a (Pi.single i 1 : σ → R)
  rw [hsum] at htaylor
  have hlin := dvd_sub (dvd_sub (h (Pi.single i 1 : σ → R)) (by simpa using h 0)) htaylor
  rw [sub_sub_cancel, sq] at hlin
  exact hp.dvd_cancel_left.1 hlin

/-- **Gradient criterion, sufficiency.** If `p ^ 2 ∣ f(a)` and `p` divides every partial
derivative `∂ᵢf(a)`, then `p ^ 2` strongly divides `f` at `a` modulo `p`. -/
theorem stronglyDvdAt_sq_of_forall_dvd_eval_pderiv (h0 : p ^ 2 ∣ eval a f)
    (hi : ∀ i, p ∣ eval a (pderiv i f)) : f.StronglyDvdAt p (p ^ 2) a := by
  rw [stronglyDvdAt_iff_forall_add_smul]
  intro b
  have hsum : p ^ 2 ∣ p * ∑ j ∈ f.vars, eval a (pderiv j f) * b j := by
    rw [sq]
    exact mul_dvd_mul_left p (Finset.dvd_sum fun j _ ↦ (hi j).mul_right _)
  simpa using dvd_add (dvd_add (sq_dvd_eval_add_smul_sub_sum_pderiv f p a b) hsum) h0

/-- **Gradient criterion.** If `p` is a non-zero-divisor, then `p ^ 2` strongly divides `f` at
`a` modulo `p` if and only if `p ^ 2 ∣ f(a)` and `p` divides every partial derivative
`∂ᵢf(a)`. -/
theorem stronglyDvdAt_sq_iff (hp : IsLeftRegular p) :
    f.StronglyDvdAt p (p ^ 2) a ↔ p ^ 2 ∣ eval a f ∧ ∀ i, p ∣ eval a (pderiv i f) :=
  ⟨fun h ↦ ⟨h.dvd_eval, h.dvd_eval_pderiv hp⟩,
    fun h ↦ stronglyDvdAt_sq_of_forall_dvd_eval_pderiv h.1 h.2⟩

/-- If `p` is a non-zero-divisor, then `p ^ 2` weakly divides `f` at `a` modulo `p` if and only
if `p ^ 2 ∣ f(a)` and some partial derivative `∂ᵢf(a)` is not divisible by `p`. -/
theorem weaklyDvdAt_sq_iff (hp : IsLeftRegular p) :
    f.WeaklyDvdAt p (p ^ 2) a ↔ p ^ 2 ∣ eval a f ∧ ∃ i, ¬ p ∣ eval a (pderiv i f) := by
  rw [weaklyDvdAt_iff, stronglyDvdAt_sq_iff hp, not_and, not_forall]
  exact and_congr_right fun h ↦ ⟨fun h' ↦ h' h, fun h' _ ↦ h'⟩

/-- If `p` is a non-zero-divisor, `p ^ 2 ∣ f(a)` and some partial derivative `∂ᵢf(a)` is not
divisible by `p`, then `p ^ 2` weakly divides `f` at `a` modulo `p`. -/
theorem weaklyDvdAt_sq_of_not_dvd_eval_pderiv (hp : IsLeftRegular p) (h0 : p ^ 2 ∣ eval a f)
    {i : σ} (hi : ¬ p ∣ eval a (pderiv i f)) : f.WeaklyDvdAt p (p ^ 2) a :=
  (weaklyDvdAt_sq_iff hp).2 ⟨h0, i, hi⟩

/-- If `q` strongly divides `f` at `a`, then the reduction of `a` along any ring homomorphism
`φ` killing `q` is a zero of `f`. -/
theorem StronglyDvdAt.eval₂_eq_zero (h : f.StronglyDvdAt p q a) (φ : R →+* S) (hφ : φ q = 0) :
    eval₂ φ (φ ∘ a) f = 0 := by
  obtain ⟨c, hc⟩ := h.dvd_eval
  rw [← eval₂_comp, hc, map_mul, hφ, zero_mul]

/-- If `p` is a non-zero-divisor and `p ^ 2` strongly divides `f` at `a` modulo `p`, then the
reduction of `a` along any ring homomorphism `φ` killing `p` is a zero of every partial
derivative of `f`. Together with `MvPolynomial.StronglyDvdAt.eval₂_eq_zero`, the reduction of
`a` lies on the common zero locus of `f` and its partial derivatives. -/
theorem StronglyDvdAt.eval₂_pderiv_eq_zero (hp : IsLeftRegular p)
    (h : f.StronglyDvdAt p (p ^ 2) a) (φ : R →+* S) (hφ : φ p = 0) (i : σ) :
    eval₂ φ (φ ∘ a) (pderiv i f) = 0 :=
  (stronglyDvdAt_self_iff.2 (h.dvd_eval_pderiv hp i)).eval₂_eq_zero φ hφ

end MvPolynomial
