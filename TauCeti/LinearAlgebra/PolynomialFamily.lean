/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Families of vectors and operators depending polynomially on a parameter

A family `c ↦ ∑ m < d, c ^ m • u m` of vectors of a module, or of endomorphisms of it, is the
general shape of a family depending polynomially on a scalar parameter. This file proves the two
statements such a family is used through.

*Recovering the coefficients.* Over an infinite field the functions `c ↦ c ^ m` are linearly
independent, so the coefficients of a power sum are determined by its values: a power sum that
vanishes at every point has zero coefficients
(`TauCeti.eq_zero_of_forall_sum_range_pow_smul_eq_zero`). Pairing the identity with a linear
functional turns it into a polynomial over the field with infinitely many roots, hence the zero
polynomial. The hypothesis that the field is infinite cannot be dropped: over `𝔽₂` the functions
`c ↦ c` and `c ↦ c ^ 2` agree.

*Producing the coefficients.* Conversely, a family of endomorphisms whose matrix entries against
some basis are polynomial in the parameter *is* such a power sum, with the coefficients read off
entrywise from the entry polynomials
(`TauCeti.exists_forall_eq_sum_pow_smul_of_toMatrix_eq_eval`). Truncating at one more than the
largest degree occurring keeps a single range serving every entry.

Together they are how a representation of a matrix group whose matrix entries are polynomial
functions is expanded along a one-parameter subgroup and its terms then identified.

## Main results

* `TauCeti.eq_zero_of_forall_sum_range_pow_smul_eq_zero`: the coefficients of an identically
  vanishing power sum are zero.
* `TauCeti.eq_of_forall_sum_range_pow_smul_eq`: two power sums agreeing at every point have the
  same coefficients.
* `TauCeti.exists_forall_eq_sum_pow_smul_of_toMatrix_eq_eval`: a family of endomorphisms with
  polynomial matrix entries is a finite power sum of fixed endomorphisms.
-/

public section

universe u v w

namespace TauCeti

/-! ## Recovering the coefficients from the values -/

section Coefficients

variable {K : Type u} [Field K] [Infinite K] {M : Type v} [AddCommGroup M] [Module K M]

/-- **A power sum with vector coefficients that vanishes identically has zero coefficients.** The
sum `∑ m < d, c ^ m • u m` is a polynomial in `c` with coefficients in `M`, and over an infinite
field a polynomial vanishing everywhere is the zero polynomial. -/
theorem eq_zero_of_forall_sum_range_pow_smul_eq_zero {d : ℕ} {u : ℕ → M}
    (h : ∀ c : K, ∑ m ∈ Finset.range d, c ^ m • u m = 0) {m : ℕ} (hm : m < d) : u m = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff K]
  intro psi
  set p : Polynomial K := ∑ a ∈ Finset.range d, Polynomial.monomial a (psi (u a)) with hp
  have hzero : p = 0 := by
    refine Polynomial.funext fun c ↦ ?_
    have hc := congrArg psi (h c)
    rw [map_sum, map_zero] at hc
    rw [Polynomial.eval_zero, hp, Polynomial.eval_finsetSum]
    refine Eq.trans (Finset.sum_congr rfl fun a _ ↦ ?_) hc
    rw [Polynomial.eval_monomial, map_smul, smul_eq_mul, mul_comm]
  have hcoeff : p.coeff m = psi (u m) := by
    rw [hp, Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr hm) ?_ |>.trans ?_
    · intro a _ ham
      simp [Polynomial.coeff_monomial, ham]
    · simp
  rw [← hcoeff, hzero, Polynomial.coeff_zero]

/-- **Two power sums with vector coefficients that agree at every point have the same
coefficients.** -/
theorem eq_of_forall_sum_range_pow_smul_eq {d : ℕ} {u v : ℕ → M}
    (h : ∀ c : K, ∑ m ∈ Finset.range d, c ^ m • u m = ∑ m ∈ Finset.range d, c ^ m • v m)
    {m : ℕ} (hm : m < d) : u m = v m := by
  refine sub_eq_zero.mp (eq_zero_of_forall_sum_range_pow_smul_eq_zero
    (K := K) (u := fun a ↦ u a - v a) (fun c ↦ ?_) hm)
  rw [Finset.sum_congr rfl fun a _ ↦ smul_sub (c ^ a) (u a) (v a), Finset.sum_sub_distrib, h c,
    sub_self]

end Coefficients

/-! ## Producing the coefficients from polynomial matrix entries -/

/-- **A family of endomorphisms whose matrix entries are polynomial in the parameter is a finite
power sum of fixed endomorphisms.** The `m`-th coefficient is read off entrywise from the `m`-th
coefficients of the entry polynomials. -/
theorem exists_forall_eq_sum_pow_smul_of_toMatrix_eq_eval {K : Type u} [CommRing K]
    {W : Type v} [AddCommGroup W] [Module K W] {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (f : K → Module.End K W) (Q : ι → ι → Polynomial K)
    (hQ : ∀ (c : K) (a a' : ι), LinearMap.toMatrix b b (f c) a a' = Polynomial.eval c (Q a a')) :
    ∃ (d : ℕ) (A : ℕ → Module.End K W), ∀ c : K, f c = ∑ m ∈ Finset.range d, c ^ m • A m := by
  classical
  refine ⟨(Finset.univ.sup fun q : ι × ι ↦ (Q q.1 q.2).natDegree) + 1,
    fun m ↦ (LinearMap.toMatrix b b).symm (Matrix.of fun a a' ↦ (Q a a').coeff m), fun c ↦ ?_⟩
  refine (LinearMap.toMatrix b b).injective ?_
  rw [map_sum]
  ext a a'
  have hdeg : (Q a a').natDegree
      < (Finset.univ.sup fun q : ι × ι ↦ (Q q.1 q.2).natDegree) + 1 :=
    Nat.lt_succ_of_le (Finset.le_sup (f := fun q : ι × ι ↦ (Q q.1 q.2).natDegree)
      (Finset.mem_univ (a, a')))
  rw [Matrix.sum_apply, hQ c a a', Polynomial.eval_eq_sum_range' hdeg c]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [map_smul, Matrix.smul_apply, LinearEquiv.apply_symm_apply, Matrix.of_apply, smul_eq_mul,
    mul_comm]

end TauCeti
