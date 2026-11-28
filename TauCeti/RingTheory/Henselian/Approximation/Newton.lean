/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import TauCeti.RingTheory.Henselian.Approximation.Completion
public import TauCeti.RingTheory.Henselian.Approximation.Jacobian

import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.Ring
import TauCeti.Algebra.MvPolynomial.Eval
import TauCeti.Algebra.MvPolynomial.PDeriv
import TauCeti.RingTheory.MvPolynomial.Ideal.Basic

/-!
# Newton approximation for Elkik's Jacobian ideal

For a family of multivariate polynomials `f : σ → MvPolynomial ι R` (possibly rectangular or
infinite), an element `t : R`, and an ideal `I : Ideal R`, Elkik's presentation Jacobian ideal
`MvPolynomial.elkikJacobianIdeal f` controls damped Newton approximation in the `(t, I)`-adic
filtration `filtrationIdeal t I n = (t) ^ n * I`. Unlike classical Hensel lifting for square
systems with invertible Jacobian determinant, `f` may have redundant equations and its Jacobian
minors need only divide a power `t ^ h` modulo the filtration on the smooth locus away from `t`.

When `h ≤ n`, `t ^ h` is left-regular in `R`, every `f r(a)` lies in `filtrationIdeal t I n`, and
`t ^ h` lies in `(elkikJacobianIdeal f).map (eval a) ⊔ filtrationIdeal t I (n - h)`, one damped
Newton step (`exists_approximateSolution_step`) produces `b : ι → R` modifying only finitely many
coordinates of `a`, congruent to `a` modulo `filtrationIdeal t I (n - h)`, with every `f r(b)` in
`filtrationIdeal t I (n - h) ^ 2 = filtrationIdeal t (I ^ 2) (2 * (n - h))`.

Under the strict inequality `2 * h < n`, the exponent recurrence `m ↦ 2 * (m - h)` (`newtonStepExp`)
grows exponentially, and iterating the single step yields a sequence of approximations over any
commutative ring (`exists_approximateSolution_seq`). Passing to the limit gives two exact lifting
theorems that preserve the Elkik Jacobian condition at the limit point:

* Over a `(t) * I`-adically complete ring `R`, `exists_eval_eq_zero_of_isAdicComplete` (together
  with the ideal-inclusion variant `exists_span_le_ker_eval_of_isAdicComplete`, corresponding to
  Gabber–Ramero, Lemma 5.4.8, and the principal-ideal specialisation
  `exists_eval_eq_zero_of_isAdicComplete_span_singleton`) lifts `a` to an exact zero `b : ι → R`
  congruent to `a` modulo `filtrationIdeal t I (n - h)`.
* Over an arbitrary commutative ring `R`, `exists_eval_completion_eq_zero` lifts `a` to an exact
  zero in the `(t, I)`-adic completion `completion t I` agreeing with `a` at residue level `n - h`.

Both `2 * h < n` and `IsLeftRegular (t ^ h)` are necessary; boundary counterexamples are recorded in
`TauCeti.Examples.RingTheory.Henselian.Approximation.Newton`.

## Main results

* `TauCeti.HenselianApproximation.exists_approximateSolution_step`: a single damped Newton step for
  Elkik's Jacobian ideal.
* `TauCeti.HenselianApproximation.newtonStepExp`,
  `TauCeti.HenselianApproximation.newtonStepExp_eq`,
  `TauCeti.HenselianApproximation.strictMono_newtonStepExp`: the exponent sequence `m ↦ 2 * (m - h)`
  and its closed form when `2 * h ≤ n`.
* `TauCeti.HenselianApproximation.exists_approximateSolution_seq`: universal Newton iterates over an
  arbitrary commutative ring when `2 * h < n`.
* `TauCeti.HenselianApproximation.exists_eval_eq_zero_of_isAdicComplete`,
  `TauCeti.HenselianApproximation.exists_span_le_ker_eval_of_isAdicComplete`,
  `TauCeti.HenselianApproximation.exists_eval_eq_zero_of_isAdicComplete_span_singleton`: exact
  lifting over `(t) * I`-adically and `(t)`-adically complete rings.
* `TauCeti.HenselianApproximation.exists_eval_completion_eq_zero`: exact lifting in `completion t I`
  without completeness or separatedness hypotheses on `R`.

## References

* [O. Gabber and L. Ramero, *Almost ring theory*], §5.4, Lemma 5.4.8 and Definitions 5.4.10–5.4.11.
* [R. Elkik, *Solutions d'équations à coefficients dans un anneau hensélien*], §I, Lemme 1.
-/

public section

namespace TauCeti.HenselianApproximation

section SingleStep

open scoped Matrix

variable {R σ ι : Type*} [CommRing R]

/-- Auxiliary ideal of elements `e : R` that eliminate `f(a)` modulo `t ^ h * K ^ 2` via a
finitely supported perturbation in `K := filtrationIdeal t I (n - h)`. -/
private noncomputable def newtonEliminatorIdeal (t : R) (I : Ideal R)
    (f : σ → MvPolynomial ι R) (a : ι → R) (h n : ℕ) : Ideal R where
  carrier := {e : R | ∃ v : ι →₀ R, (∀ k, v k ∈ filtrationIdeal t I (n - h)) ∧
    ∀ r : σ, e * MvPolynomial.eval a (f r) -
      t ^ h * v.sum (fun k c ↦ MvPolynomial.eval a (MvPolynomial.pderiv k (f r)) * c) ∈
        Ideal.span {t ^ h} * filtrationIdeal t I (n - h) ^ 2}
  add_mem' := by
    classical
    rintro e₁ e₂ ⟨v₁, hv₁, he₁⟩ ⟨v₂, hv₂, he₂⟩
    refine ⟨v₁ + v₂, fun k ↦ Ideal.add_mem _ (hv₁ k) (hv₂ k), fun r ↦ ?_⟩
    have hsum : (v₁ + v₂).sum (fun k c ↦ MvPolynomial.eval a (MvPolynomial.pderiv k (f r)) * c) =
        v₁.sum (fun k c ↦ MvPolynomial.eval a (MvPolynomial.pderiv k (f r)) * c) +
          v₂.sum (fun k c ↦ MvPolynomial.eval a (MvPolynomial.pderiv k (f r)) * c) :=
      Finsupp.sum_add_index' (fun _ ↦ mul_zero _) (fun _ _ _ ↦ mul_add _ _ _)
    have hlin : (e₁ + e₂) * MvPolynomial.eval a (f r) -
          t ^ h * (v₁ + v₂).sum
            (fun k c ↦ MvPolynomial.eval a (MvPolynomial.pderiv k (f r)) * c) =
        (e₁ * MvPolynomial.eval a (f r) -
          t ^ h * v₁.sum (fun k c ↦ MvPolynomial.eval a (MvPolynomial.pderiv k (f r)) * c)) +
        (e₂ * MvPolynomial.eval a (f r) -
          t ^ h * v₂.sum (fun k c ↦ MvPolynomial.eval a (MvPolynomial.pderiv k (f r)) * c)) := by
      rw [hsum]
      ring
    rw [hlin]
    exact Ideal.add_mem _ (he₁ r) (he₂ r)
  zero_mem' := ⟨0, fun _ ↦ by simp, fun _ ↦ by simp⟩
  smul_mem' := by
    classical
    rintro c e ⟨v, hv, he⟩
    refine ⟨c • v, fun k ↦ Ideal.mul_mem_left _ c (hv k), fun r ↦ ?_⟩
    have hsum : (c • v).sum (fun k d ↦ MvPolynomial.eval a (MvPolynomial.pderiv k (f r)) * d) =
        c * v.sum (fun k d ↦ MvPolynomial.eval a (MvPolynomial.pderiv k (f r)) * d) := by
      rw [Finsupp.sum_smul_index' (fun _ ↦ mul_zero _)]
      simp only [Finsupp.sum, Finset.mul_sum, smul_eq_mul]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    have hlin : (c • e) * MvPolynomial.eval a (f r) -
          t ^ h * (c • v).sum
            (fun k d ↦ MvPolynomial.eval a (MvPolynomial.pderiv k (f r)) * d) =
        c * (e * MvPolynomial.eval a (f r) -
          t ^ h * v.sum (fun k d ↦ MvPolynomial.eval a (MvPolynomial.pderiv k (f r)) * d)) := by
      rw [hsum, smul_eq_mul]
      ring
    rw [hlin]
    exact Ideal.mul_mem_left _ c (he r)

private theorem filtrationIdeal_le_newtonEliminatorIdeal (t : R) (I : Ideal R)
    (f : σ → MvPolynomial ι R) (a : ι → R) {h n : ℕ} (hhn : h ≤ n)
    (ha : ∀ r, MvPolynomial.eval a (f r) ∈ filtrationIdeal t I n) :
    filtrationIdeal t I (n - h) ≤ newtonEliminatorIdeal t I f a h n := by
  intro e he
  refine ⟨0, fun _ ↦ by simp, fun r ↦ ?_⟩
  have hprod : filtrationIdeal t I (n - h) * filtrationIdeal t I n =
      Ideal.span {t ^ h} * filtrationIdeal t I (n - h) ^ 2 := by
    have hn_eq : n = h + (n - h) := (Nat.add_sub_cancel' hhn).symm
    conv_lhs =>
      arg 2
      rw [hn_eq, filtrationIdeal_add]
    rw [mul_comm (filtrationIdeal t I (n - h)), mul_assoc, ← sq]
  simpa only [Finsupp.sum_zero_index, mul_zero, sub_zero, ← hprod] using
    Ideal.mul_mem_mul he (ha r)

/-- Differentiating a colon relation `∑ i : s, Q i * f i = g * f r` along selected columns `col`
and contracting with an adjugate solution `u` identifies the directional derivative of `f r` up to
terms quadratic in `(f(a), u)`. -/
private theorem mul_sum_pderiv_colon_eq [DecidableEq σ] {t : R} {f : σ → MvPolynomial ι R}
    {a : ι → R} {h : ℕ} {s : Finset σ} {col : s → ι} {J : Matrix s s R}
    (hJ : ∀ i j : s, J i j = MvPolynomial.eval a (MvPolynomial.pderiv (col j) (f i)))
    {g : MvPolynomial ι R} {r : σ} {Q : s → MvPolynomial ι R} (hQ : ∑ i : s, Q i * f i = g * f r)
    {w u : s → R} (htw : ∀ i : s, t ^ h * w i = MvPolynomial.eval a (f i))
    (hJu : ∀ i : s, ∑ j : s, J i j * u j = J.det * w i) :
    t ^ h * ∑ j : s, MvPolynomial.eval a (MvPolynomial.pderiv (col j) (f r)) *
        (MvPolynomial.eval a g * u j) =
      J.det * MvPolynomial.eval a g * MvPolynomial.eval a (f r) +
        t ^ h * ((∑ j : s, ∑ i : s,
            MvPolynomial.eval a (MvPolynomial.pderiv (col j) (Q i)) *
              MvPolynomial.eval a (f i) * u j) -
          ∑ j : s, MvPolynomial.eval a (MvPolynomial.pderiv (col j) g) *
            MvPolynomial.eval a (f r) * u j) := by
  have hdiff (j : s) :
      (MvPolynomial.eval a g * MvPolynomial.eval a (MvPolynomial.pderiv (col j) (f r))) * u j =
      (∑ i : s, MvPolynomial.eval a (Q i) * (J i j * u j)) +
        ((∑ i : s, MvPolynomial.eval a (MvPolynomial.pderiv (col j) (Q i)) *
            MvPolynomial.eval a (f i) * u j) -
          MvPolynomial.eval a (MvPolynomial.pderiv (col j) g) *
            MvPolynomial.eval a (f r) * u j) := by
    have hp := congrArg (fun p ↦ MvPolynomial.eval a (MvPolynomial.pderiv (col j) p) * u j) hQ.symm
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, map_sum,
      mul_comm (MvPolynomial.eval a (f _)), add_mul, Finset.sum_mul, ← hJ] at hp
    have hp' : MvPolynomial.eval a g * MvPolynomial.eval a (MvPolynomial.pderiv (col j) (f r)) *
          u j + MvPolynomial.eval a (MvPolynomial.pderiv (col j) g) *
          MvPolynomial.eval a (f r) * u j =
        ∑ x : s, (MvPolynomial.eval a (MvPolynomial.pderiv (col j) (Q x)) *
            MvPolynomial.eval a (f x) * u j +
          MvPolynomial.eval a (Q x) * J x j * u j) :=
      hp.trans (Finset.sum_congr rfl fun _ _ ↦ add_comm _ _)
    rw [eq_sub_iff_add_eq.mpr hp']
    simp only [Finset.sum_add_distrib, mul_assoc]
    ring
  have hmain : t ^ h * ∑ j : s, ∑ i : s, MvPolynomial.eval a (Q i) * (J i j * u j) =
      J.det * MvPolynomial.eval a g * MvPolynomial.eval a (f r) := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hJu]
    rw [Finset.mul_sum]
    have hterm (i : s) : t ^ h * (MvPolynomial.eval a (Q i) * (J.det * w i)) =
        J.det * (MvPolynomial.eval a (Q i) * MvPolynomial.eval a (f i)) := by
      calc
        t ^ h * (MvPolynomial.eval a (Q i) * (J.det * w i)) =
            J.det * (MvPolynomial.eval a (Q i) * (t ^ h * w i)) := by ring
        _ = J.det * (MvPolynomial.eval a (Q i) * MvPolynomial.eval a (f i)) := by rw [htw i]
    simp only [hterm, ← Finset.mul_sum]
    have hQeval := congrArg (MvPolynomial.eval a) hQ
    simp only [map_sum, map_mul] at hQeval
    rw [hQeval, mul_assoc]
  have hlhs : (∑ j : s, MvPolynomial.eval a (MvPolynomial.pderiv (col j) (f r)) *
        (MvPolynomial.eval a g * u j)) =
      ∑ j : s, (MvPolynomial.eval a g *
        MvPolynomial.eval a (MvPolynomial.pderiv (col j) (f r))) * u j :=
    Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hlhs]
  simp only [hdiff, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [mul_add, hmain]

private theorem det_mul_colon_mem_newtonEliminatorIdeal [DecidableEq σ] (t : R) (I : Ideal R)
    (f : σ → MvPolynomial ι R) (a : ι → R) {h n : ℕ} (hhn : h ≤ n)
    (ha : ∀ r, MvPolynomial.eval a (f r) ∈ filtrationIdeal t I n)
    (s : Finset σ) (col : s → ι) {g : MvPolynomial ι R}
    (hg : g ∈ (Ideal.span (f '' (s : Set σ))).colon (Ideal.span (Set.range f))) :
    MvPolynomial.eval a
        (Matrix.det (Matrix.of fun i j : s ↦ MvPolynomial.pderiv (col j) (f i)) * g) ∈
      newtonEliminatorIdeal t I f a h n := by
  classical
  set K : Ideal R := filtrationIdeal t I (n - h)
  set M : Ideal R := Ideal.span {t ^ h} * K ^ 2
  have hn_eq : h + (n - h) = n := Nat.add_sub_cancel' hhn
  have hKM : filtrationIdeal t I n * K = M := by
    rw [← hn_eq, filtrationIdeal_add, mul_assoc, ← sq]
  choose w hwK htw using fun i : s ↦ mem_filtrationIdeal_add_iff.mp (hn_eq.symm ▸ ha i)
  let J : Matrix s s R := Matrix.of fun i j : s ↦
    MvPolynomial.eval a (MvPolynomial.pderiv (col j) (f i))
  let u : s → R := J.adjugate *ᵥ w
  have huK (j : s) : u j ∈ K := K.sum_mem fun i _ ↦ K.mul_mem_left _ (hwK i)
  have hJu (i : s) : ∑ j : s, J i j * u j = J.det * w i := by
    have hmul : (J *ᵥ u) i = ((J * J.adjugate) *ᵥ w) i :=
      congrFun (Matrix.mulVec_mulVec w J J.adjugate) i
    rw [Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.smul_apply, smul_eq_mul] at hmul
    simpa only [Matrix.mulVec, dotProduct] using hmul
  let v : ι →₀ R := ∑ j : s, Finsupp.single (col j) (MvPolynomial.eval a g * u j)
  have hvK (k : ι) : v k ∈ K := by
    simp only [v, Finset.sum_apply']
    refine K.sum_mem fun j _ ↦ ?_
    by_cases hkj : col j = k
    · subst hkj; simpa using K.mul_mem_left (MvPolynomial.eval a g) (huK j)
    · simp [Finsupp.single_eq_of_ne (Ne.symm hkj)]
  have hvsum (φ : ι → R) :
      v.sum (fun k c ↦ φ k * c) = ∑ j : s, φ (col j) * (MvPolynomial.eval a g * u j) := by
    dsimp only [v]
    rw [← Finsupp.sum_finsetSum_index (fun _ ↦ mul_zero _) (fun _ _ _ ↦ mul_add _ _ _)]
    simp [Finsupp.sum_single_index]
  have hdet : MvPolynomial.eval a
      (Matrix.det (Matrix.of fun i j : s ↦ MvPolynomial.pderiv (col j) (f i))) = J.det := by
    simpa only [J, RingHom.mapMatrix_apply, Matrix.map, Matrix.of_apply] using
      RingHom.map_det (MvPolynomial.eval a)
        (Matrix.of fun i j : s ↦ MvPolynomial.pderiv (col j) (f i))
  refine ⟨v, hvK, fun r ↦ ?_⟩
  have hgfr : g * f r ∈ Ideal.span (Set.range fun i : s ↦ f i) := by
    have himg : f '' (s : Set σ) = Set.range fun i : s ↦ f i := by ext; simp
    rw [← himg]
    exact Submodule.mem_colon.mp hg (f r) (Ideal.subset_span ⟨r, rfl⟩)
  obtain ⟨Q, hQ⟩ := Ideal.mem_span_range_iff_exists_fun.mp hgfr
  have herr1 : (∑ j : s, ∑ i : s,
      MvPolynomial.eval a (MvPolynomial.pderiv (col j) (Q i)) *
        MvPolynomial.eval a (f i) * u j) ∈ M := by
    rw [← hKM]
    exact Ideal.sum_mem _ fun j _ ↦ Ideal.sum_mem _ fun i _ ↦
      Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ (ha i)) (huK j)
  have herr2 : (∑ j : s, MvPolynomial.eval a (MvPolynomial.pderiv (col j) g) *
      MvPolynomial.eval a (f r) * u j) ∈ M := by
    rw [← hKM]
    exact Ideal.sum_mem _ fun j _ ↦
      Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ (ha r)) (huK j)
  rw [map_mul, hdet, hvsum, mul_sum_pderiv_colon_eq (J := J) (fun _ _ ↦ rfl) hQ htw hJu,
    sub_add_cancel_left]
  exact M.neg_mem (M.mul_mem_left (t ^ h) (M.sub_mem herr1 herr2))

private theorem map_elkikJacobianIdeal_le_newtonEliminatorIdeal [DecidableEq σ] (t : R)
    (I : Ideal R) (f : σ → MvPolynomial ι R) (a : ι → R) {h n : ℕ} (hhn : h ≤ n)
    (ha : ∀ r, MvPolynomial.eval a (f r) ∈ filtrationIdeal t I n) :
    (MvPolynomial.elkikJacobianIdeal f).map (MvPolynomial.eval a) ≤
      newtonEliminatorIdeal t I f a h n := by
  rw [Ideal.map_le_iff_le_comap, MvPolynomial.elkikJacobianIdeal_le_iff]
  intro s
  rw [Ideal.mul_le]
  intro p hp g hg
  have hp' : p ∈ ((newtonEliminatorIdeal t I f a h n).comap (MvPolynomial.eval a)).colon {g} := by
    refine (MvPolynomial.jacobianMinorsIdeal_le_iff f s _).mpr (fun col ↦ ?_) hp
    rw [Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_comap]
    exact det_mul_colon_mem_newtonEliminatorIdeal t I f a hhn ha s col hg
  simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using hp'

/-- **Single damped Newton step for Elkik's Jacobian ideal.** If `a : ι → R` solves `f = 0` modulo
`filtrationIdeal t I n`, `t ^ h` is left-regular with `h ≤ n`, and `t ^ h` lies in the evaluated
Elkik Jacobian ideal modulo `filtrationIdeal t I (n - h)`, then there exists `b : ι → R` modifying
only finitely many coordinates of `a`, congruent to `a` modulo `filtrationIdeal t I (n - h)`, such
that every `f r(b)` lies in `filtrationIdeal t I (n - h) ^ 2`. -/
theorem exists_approximateSolution_step [DecidableEq σ] (t : R) (I : Ideal R)
    (f : σ → MvPolynomial ι R) (a : ι → R) {h n : ℕ} (hhn : h ≤ n)
    (ht : IsLeftRegular (t ^ h))
    (ha : ∀ r, MvPolynomial.eval a (f r) ∈ filtrationIdeal t I n)
    (hjac : t ^ h ∈ (MvPolynomial.elkikJacobianIdeal f).map (MvPolynomial.eval a) ⊔
      filtrationIdeal t I (n - h)) :
    ∃ b : ι → R, {i | b i ≠ a i}.Finite ∧
      (∀ i, b i - a i ∈ filtrationIdeal t I (n - h)) ∧
      ∀ r, MvPolynomial.eval b (f r) ∈ filtrationIdeal t I (n - h) ^ 2 := by
  classical
  have hmem : t ^ h ∈ newtonEliminatorIdeal t I f a h n :=
    (sup_le (map_elkikJacobianIdeal_le_newtonEliminatorIdeal t I f a hhn ha)
      (filtrationIdeal_le_newtonEliminatorIdeal t I f a hhn ha)) hjac
  obtain ⟨v, hvK, hvlin⟩ := hmem
  let b : ι → R := fun i ↦ a i - v i
  have hsupp : ∀ i, b i ≠ a i → i ∈ v.support := fun i hne ↦
    Finsupp.mem_support_iff.mpr fun hvi ↦ hne (by simp [b, hvi])
  have hfin : {i | b i ≠ a i}.Finite := v.support.finite_toSet.subset fun i hi ↦ hsupp i hi
  have hba (i : ι) : b i - a i ∈ filtrationIdeal t I (n - h) := by
    simpa only [b, sub_sub_cancel_left] using (filtrationIdeal t I (n - h)).neg_mem (hvK i)
  refine ⟨b, hfin, hba, fun r ↦ ?_⟩
  have hlin_cancel : MvPolynomial.eval a (f r) -
      v.sum (fun k c ↦ MvPolynomial.eval a (MvPolynomial.pderiv k (f r)) * c) ∈
        filtrationIdeal t I (n - h) ^ 2 := by
    have hmul : t ^ h * (MvPolynomial.eval a (f r) -
        v.sum (fun k c ↦ MvPolynomial.eval a (MvPolynomial.pderiv k (f r)) * c)) ∈
        Ideal.span {t ^ h} * filtrationIdeal t I (n - h) ^ 2 := by
      simpa only [mul_sub] using hvlin r
    obtain ⟨y, hy, hyx⟩ := Ideal.mem_span_singleton_mul.mp hmul
    exact ht hyx ▸ hy
  have htaylor := MvPolynomial.eval_sub_eval_sub_sum_pderiv_mem_sq (f r)
    (I := filtrationIdeal t I (n - h)) (a := a) (b := b) (s := v.support)
    (fun i _ hne ↦ hsupp i hne) (fun i _ ↦ hba i)
  have hsum : (∑ j ∈ v.support, MvPolynomial.eval a (MvPolynomial.pderiv j (f r)) * (b j - a j)) =
      -v.sum (fun k c ↦ MvPolynomial.eval a (MvPolynomial.pderiv k (f r)) * c) := by
    simp only [b, sub_sub_cancel_left, mul_neg, Finset.sum_neg_distrib, Finsupp.sum]
  have heq : MvPolynomial.eval b (f r) =
      (MvPolynomial.eval b (f r) - MvPolynomial.eval a (f r) -
        ∑ j ∈ v.support, MvPolynomial.eval a (MvPolynomial.pderiv j (f r)) * (b j - a j)) +
      (MvPolynomial.eval a (f r) -
        v.sum (fun k c ↦ MvPolynomial.eval a (MvPolynomial.pderiv k (f r)) * c)) := by
    rw [hsum]
    ring
  rw [heq]
  exact (filtrationIdeal t I (n - h) ^ 2).add_mem htaylor hlin_cancel

end SingleStep

section Iteration

variable {R σ ι : Type*} [CommRing R]

/-- Sequence of filtration exponents produced by repeated Newton steps: starting at `n`, each step
replaces `m` by `2 * (m - h)`. -/
def newtonStepExp (h n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => 2 * (newtonStepExp h n k - h)

/-- At step `0`, the Newton exponent sequence equals the initial precision `n`. -/
@[simp]
theorem newtonStepExp_zero (h n : ℕ) : newtonStepExp h n 0 = n := by
  simp [newtonStepExp]

/-- Each Newton step replaces the previous filtration exponent `m` by `2 * (m - h)`. -/
@[simp]
theorem newtonStepExp_succ (h n k : ℕ) :
    newtonStepExp h n (k + 1) = 2 * (newtonStepExp h n k - h) := by
  simp [newtonStepExp]

/-- Closed form for the Newton exponent sequence when `2 * h ≤ n`. -/
theorem newtonStepExp_eq {h n : ℕ} (hhn : 2 * h ≤ n) (k : ℕ) :
    newtonStepExp h n k = 2 ^ k * (n - 2 * h) + 2 * h := by
  induction k with
  | zero =>
    rw [newtonStepExp_zero]
    omega
  | succ k ih =>
    rw [newtonStepExp_succ, ih]
    have : 2 ^ (k + 1) * (n - 2 * h) = 2 * (2 ^ k * (n - 2 * h)) := by ring
    omega

/-- When `2 * h < n`, the Newton exponent sequence is strictly increasing. -/
theorem strictMono_newtonStepExp {h n : ℕ} (hhn : 2 * h < n) :
    StrictMono (newtonStepExp h n) := by
  refine strictMono_nat_of_lt_succ fun k ↦ ?_
  rw [newtonStepExp_eq (Nat.le_of_lt hhn) k, newtonStepExp_eq (Nat.le_of_lt hhn) (k + 1)]
  have hpos : 0 < 2 ^ k * (n - 2 * h) :=
    Nat.mul_pos (Nat.two_pow_pos k) (Nat.sub_pos_of_lt hhn)
  have hpow : 2 ^ (k + 1) * (n - 2 * h) = 2 * (2 ^ k * (n - 2 * h)) := by ring
  omega

/-- If `t ^ h` lies in `H(a)` modulo `filtrationIdeal t I (n - h)` with `2 * h ≤ n` and
`b ≡ a mod filtrationIdeal t I (n - h)`, then some `P ∈ H` evaluates at `b` to `t ^ h * (1 - z)`
with `z ∈ filtrationIdeal t I (n - 2 * h)`. -/
private theorem exists_eval_eq_pow_mul_one_sub {t : R} {I : Ideal R}
    {H : Ideal (MvPolynomial ι R)} {a b : ι → R} {h n : ℕ} (hhn : 2 * h ≤ n)
    (hjac : t ^ h ∈ H.map (MvPolynomial.eval a) ⊔ filtrationIdeal t I (n - h))
    (hba : ∀ i, b i - a i ∈ filtrationIdeal t I (n - h)) :
    ∃ P ∈ H, ∃ z ∈ filtrationIdeal t I (n - 2 * h),
      MvPolynomial.eval b P = t ^ h * (1 - z) := by
  obtain ⟨y, hy, r₀, hr₀, hyr⟩ := Submodule.mem_sup.mp hjac
  have hsurj : Function.Surjective (MvPolynomial.eval a) := fun c ↦
    ⟨MvPolynomial.C c, MvPolynomial.eval_C c⟩
  obtain ⟨P, hPH, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp hy
  have hdiff : t ^ h - MvPolynomial.eval b P ∈ filtrationIdeal t I (h + (n - 2 * h)) := by
    have h1 : MvPolynomial.eval b P - MvPolynomial.eval a P ∈ filtrationIdeal t I (n - h) :=
      MvPolynomial.eval_sub_eval_mem P hba
    have h2 : t ^ h - MvPolynomial.eval b P =
        r₀ - (MvPolynomial.eval b P - MvPolynomial.eval a P) := by
      rw [← hyr]
      ring
    have hn_eq : n - h = h + (n - 2 * h) := by omega
    rw [← hn_eq, h2]
    exact (filtrationIdeal t I (n - h)).sub_mem hr₀ h1
  obtain ⟨z, hz, htz⟩ := mem_filtrationIdeal_add_iff.mp hdiff
  refine ⟨P, hPH, z, hz, ?_⟩
  calc
    MvPolynomial.eval b P = t ^ h - (t ^ h - MvPolynomial.eval b P) := by ring
    _ = t ^ h - t ^ h * z := by rw [htz]
    _ = t ^ h * (1 - z) := by ring

/-- Cubic truncation `(1 + z + z ^ 2) * (1 - z) = 1 - z ^ 3` propagates the Elkik Jacobian
condition from `a` to `b` without any completeness or unit hypothesis. -/
private theorem pow_mem_map_sup_filtrationIdeal_sq {t : R} {I : Ideal R}
    {H : Ideal (MvPolynomial ι R)} {a b : ι → R} {h n : ℕ} (hhn : 2 * h ≤ n)
    (hjac : t ^ h ∈ H.map (MvPolynomial.eval a) ⊔ filtrationIdeal t I (n - h))
    (hba : ∀ i, b i - a i ∈ filtrationIdeal t I (n - h)) :
    t ^ h ∈ H.map (MvPolynomial.eval b) ⊔ filtrationIdeal t (I ^ 2) (2 * (n - h) - h) := by
  obtain ⟨P, hPH, z, hz, hPb⟩ := exists_eval_eq_pow_mul_one_sub hhn hjac hba
  let Q : MvPolynomial ι R := MvPolynomial.C (1 + z + z ^ 2) * P
  have hQH : Q ∈ H := H.mul_mem_left _ hPH
  have hQeval : MvPolynomial.eval b Q = t ^ h - t ^ h * z ^ 3 := by
    simp only [Q, map_mul, MvPolynomial.eval_C, hPb]
    ring
  have hz2 : z ^ 2 ∈ filtrationIdeal t (I ^ 2) (2 * (n - 2 * h)) := by
    rw [← filtrationIdeal_sq]
    exact Ideal.pow_mem_pow hz 2
  have hz3 : z ^ 3 ∈ filtrationIdeal t (I ^ 2) (3 * (n - 2 * h)) := by
    have hmul : z ^ 2 * z ∈ filtrationIdeal t (I ^ 2 * I) (2 * (n - 2 * h) + (n - 2 * h)) := by
      rw [← filtrationIdeal_mul_filtrationIdeal]
      exact Ideal.mul_mem_mul hz2 hz
    have hexp : 2 * (n - 2 * h) + (n - 2 * h) = 3 * (n - 2 * h) := by omega
    rw [pow_succ z 2]
    exact hexp ▸ filtrationIdeal_mono_right t Ideal.mul_le_left _ hmul
  have htz3 : t ^ h * z ^ 3 ∈ filtrationIdeal t (I ^ 2) (2 * (n - h) - h) := by
    have hmem : t ^ h * z ^ 3 ∈ filtrationIdeal t (I ^ 2) (h + 3 * (n - 2 * h)) :=
      mem_filtrationIdeal_add_iff.mpr ⟨z ^ 3, hz3, rfl⟩
    exact filtrationIdeal_antitone t (I ^ 2) (by omega) hmem
  have hsum : MvPolynomial.eval b Q + t ^ h * z ^ 3 = t ^ h := by
    rw [hQeval, sub_add_cancel]
  exact hsum ▸ Submodule.add_mem_sup (Ideal.mem_map_of_mem (MvPolynomial.eval b) hQH) htz3

/-- **Universal Newton iterates over an arbitrary commutative ring.** When `2 * h < n` and
`t ^ h` is left-regular, repeated damped Newton steps produce a sequence `u : ℕ → ι → R` starting
at `a` whose `k`-th step changes only finitely many coordinates by elements of
`filtrationIdeal t (I ^ 2 ^ k) (newtonStepExp h n k - h)` and reduces all equations modulo
`filtrationIdeal t (I ^ 2 ^ k) (newtonStepExp h n k)`. -/
theorem exists_approximateSolution_seq [DecidableEq σ] (t : R) (I : Ideal R)
    (f : σ → MvPolynomial ι R) (a : ι → R) {h n : ℕ} (hhn : 2 * h < n)
    (ht : IsLeftRegular (t ^ h))
    (ha : ∀ r, MvPolynomial.eval a (f r) ∈ filtrationIdeal t I n)
    (hjac : t ^ h ∈ (MvPolynomial.elkikJacobianIdeal f).map (MvPolynomial.eval a) ⊔
      filtrationIdeal t I (n - h)) :
    ∃ u : ℕ → ι → R, u 0 = a ∧
      (∀ k, {i | u (k + 1) i ≠ u k i}.Finite) ∧
      (∀ k i, u (k + 1) i - u k i ∈
        filtrationIdeal t (I ^ 2 ^ k) (newtonStepExp h n k - h)) ∧
      (∀ k r, MvPolynomial.eval (u k) (f r) ∈
        filtrationIdeal t (I ^ 2 ^ k) (newtonStepExp h n k)) ∧
      ∀ k, t ^ h ∈ (MvPolynomial.elkikJacobianIdeal f).map (MvPolynomial.eval (u k)) ⊔
        filtrationIdeal t (I ^ 2 ^ k) (newtonStepExp h n k - h) := by
  let State (k : ℕ) :=
    {x : ι → R // (∀ r, MvPolynomial.eval x (f r) ∈
        filtrationIdeal t (I ^ 2 ^ k) (newtonStepExp h n k)) ∧
      t ^ h ∈ (MvPolynomial.elkikJacobianIdeal f).map (MvPolynomial.eval x) ⊔
        filtrationIdeal t (I ^ 2 ^ k) (newtonStepExp h n k - h)}
  have hexp (k : ℕ) : 2 * h < newtonStepExp h n k := by
    rw [newtonStepExp_eq (Nat.le_of_lt hhn) k]
    have : 0 < 2 ^ k * (n - 2 * h) := Nat.mul_pos (Nat.two_pow_pos k) (Nat.sub_pos_of_lt hhn)
    omega
  have hstep (k : ℕ) (s : State k) :
      ∃ s' : State (k + 1), {i | s'.val i ≠ s.val i}.Finite ∧
        ∀ i, s'.val i - s.val i ∈ filtrationIdeal t (I ^ 2 ^ k) (newtonStepExp h n k - h) := by
    have hle : h ≤ newtonStepExp h n k := by
      have := hexp k
      omega
    obtain ⟨b, hfin, hba, hfb⟩ := exists_approximateSolution_step t (I ^ 2 ^ k) f s.val hle ht
      s.property.left s.property.right
    have hpow : (I ^ 2 ^ k) ^ 2 = I ^ 2 ^ (k + 1) := by rw [← pow_mul, pow_succ]
    have hfb' (r : σ) : MvPolynomial.eval b (f r) ∈
        filtrationIdeal t (I ^ 2 ^ (k + 1)) (newtonStepExp h n (k + 1)) := by
      rw [newtonStepExp_succ, ← hpow, ← filtrationIdeal_sq]
      exact hfb r
    have hjac' : t ^ h ∈ (MvPolynomial.elkikJacobianIdeal f).map (MvPolynomial.eval b) ⊔
        filtrationIdeal t (I ^ 2 ^ (k + 1)) (newtonStepExp h n (k + 1) - h) := by
      rw [newtonStepExp_succ, ← hpow]
      exact pow_mem_map_sup_filtrationIdeal_sq (Nat.le_of_lt (hexp k)) s.property.right hba
    exact ⟨⟨b, hfb', hjac'⟩, hfin, hba⟩
  choose next hnext_fin hnext_sub using hstep
  let s0 : State 0 := ⟨a, by simpa using ha, by simpa using hjac⟩
  let st : ∀ k, State k := Nat.rec s0 next
  have hst_succ (k : ℕ) : st (k + 1) = next k (st k) := rfl
  refine ⟨fun k ↦ (st k).val, rfl, fun k ↦ ?_, fun k i ↦ ?_,
    fun k r ↦ (st k).property.left r, fun k ↦ (st k).property.right⟩
  · dsimp only
    rw [hst_succ]
    exact hnext_fin k (st k)
  · dsimp only
    rw [hst_succ]
    exact hnext_sub k (st k) i

end Iteration

section Complete

variable {R σ ι : Type*} [CommRing R] [DecidableEq σ]

private theorem sub_newtonIter_mem {t : R} {I : Ideal R} {u : ℕ → ι → R} {h n : ℕ}
    (hhn : 2 * h < n)
    (hstep : ∀ k i, u (k + 1) i - u k i ∈
      filtrationIdeal t (I ^ 2 ^ k) (newtonStepExp h n k - h))
    {k m : ℕ} (hkm : k ≤ m) (i : ι) :
    u m i - u k i ∈ filtrationIdeal t (I ^ 2 ^ k) (newtonStepExp h n k - h) := by
  induction m, hkm using Nat.le_induction with
  | base => simp
  | succ m hkm ih =>
    have hle_exp : newtonStepExp h n k - h ≤ newtonStepExp h n m - h :=
      Nat.sub_le_sub_right ((strictMono_newtonStepExp hhn).monotone hkm) h
    have hle_pow : 2 ^ k ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hkm
    have hm_in_k : u (m + 1) i - u m i ∈
        filtrationIdeal t (I ^ 2 ^ k) (newtonStepExp h n k - h) :=
      (filtrationIdeal_mono_right t (Ideal.pow_le_pow_right hle_pow) _).trans
        (filtrationIdeal_antitone t (I ^ 2 ^ k) hle_exp) (hstep m i)
    rw [← sub_add_sub_cancel (u (m + 1) i) (u m i) (u k i)]
    exact Ideal.add_mem _ hm_in_k ih

/-- **Gabber–Ramero, Lemma 5.4.8 (point-evaluation form).** Over a ring `R` that is adically
complete with respect to `(t) * I`, let `f : σ → MvPolynomial ι R` be a family of polynomial
equations, `h` and `n` natural numbers with `2 * h < n`, and `t ^ h` left-regular in `R`. Every
approximate solution `a : ι → R` with `f r(a) ∈ filtrationIdeal t I n` and
`t ^ h ∈ (elkikJacobianIdeal f).map (eval a) ⊔ filtrationIdeal t I (n - h)` lifts to an exact
solution `b : ι → R` congruent to `a` modulo `filtrationIdeal t I (n - h)` satisfying
`t ^ h ∈ (elkikJacobianIdeal f).map (eval b)`. -/
theorem exists_eval_eq_zero_of_isAdicComplete (t : R) (I : Ideal R)
    [IsAdicComplete (Ideal.span {t} * I) R]
    (f : σ → MvPolynomial ι R) (a : ι → R) {h n : ℕ} (hhn : 2 * h < n)
    (ht : IsLeftRegular (t ^ h))
    (ha : ∀ r, MvPolynomial.eval a (f r) ∈ filtrationIdeal t I n)
    (hjac : t ^ h ∈ (MvPolynomial.elkikJacobianIdeal f).map (MvPolynomial.eval a) ⊔
      filtrationIdeal t I (n - h)) :
    ∃ b : ι → R, (∀ i, b i - a i ∈ filtrationIdeal t I (n - h)) ∧
      (∀ r, MvPolynomial.eval b (f r) = 0) ∧
      t ^ h ∈ (MvPolynomial.elkikJacobianIdeal f).map (MvPolynomial.eval b) := by
  let J : Ideal R := Ideal.span {t} * I
  obtain ⟨u, rfl, -, hstep, hfu, -⟩ :=
    exists_approximateSolution_seq t I f a hhn ht ha hjac
  have hexp_ge (k : ℕ) : 2 ^ k ≤ newtonStepExp h n k - h := by
    rw [newtonStepExp_eq (Nat.le_of_lt hhn) k]
    have : 2 ^ k * 1 ≤ 2 ^ k * (n - 2 * h) :=
      Nat.mul_le_mul_left (2 ^ k) (Nat.succ_le_of_lt (Nat.sub_pos_of_lt hhn))
    omega
  have hcauchy (i : ι) {k m : ℕ} (hkm : k ≤ m) :
      u k i ≡ u m i [SMOD (J ^ k • ⊤ : Ideal R)] := by
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, ← neg_sub]
    exact (J ^ k).neg_mem (filtrationIdeal_pow_le_pow_span_singleton_mul t I
      (Nat.le_of_lt Nat.lt_two_pow_self)
      ((Nat.le_of_lt Nat.lt_two_pow_self).trans (hexp_ge k))
      (sub_newtonIter_mem hhn hstep hkm i))
  choose b hb using fun i ↦
    IsPrecomplete.prec (I := J) inferInstance (f := (u · i)) fun hkm ↦ hcauchy i hkm
  have hbu (k : ℕ) (i : ι) : b i - u k i ∈ J ^ k := by
    have hmem := SModEq.sub_mem.mp (hb i k)
    rw [Ideal.smul_eq_mul, Ideal.mul_top] at hmem
    simpa only [neg_sub] using (J ^ k).neg_mem hmem
  have hba (i : ι) : b i - u 0 i ∈ filtrationIdeal t I (n - h) := by
    have hJk : J ^ (n - h) ≤ filtrationIdeal t I (n - h) := by
      rw [pow_span_singleton_mul]
      exact filtrationIdeal_mono_right t (Ideal.pow_le_self (by omega)) (n - h)
    have h2 : u (n - h) i - u 0 i ∈ filtrationIdeal t I (n - h) := by
      simpa using sub_newtonIter_mem hhn hstep (Nat.zero_le (n - h)) i
    rw [← sub_add_sub_cancel (b i) (u (n - h) i) (u 0 i)]
    exact Ideal.add_mem _ (hJk (hbu (n - h) i)) h2
  have hfb (r : σ) : MvPolynomial.eval b (f r) = 0 := by
    refine IsHausdorff.haus (I := J) inferInstance _ fun k ↦ ?_
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
    have hdiff : MvPolynomial.eval b (f r) - MvPolynomial.eval (u k) (f r) ∈ J ^ k :=
      MvPolynomial.eval_sub_eval_mem (f r) (hbu k)
    have huk : MvPolynomial.eval (u k) (f r) ∈ J ^ k := by
      refine filtrationIdeal_pow_le_pow_span_singleton_mul t I
        (Nat.le_of_lt Nat.lt_two_pow_self) ?_ (hfu k r)
      have := hexp_ge k
      have := Nat.lt_two_pow_self (n := k)
      omega
    simpa only [sub_add_cancel] using (J ^ k).add_mem hdiff huk
  have hjac_b : t ^ h ∈ (MvPolynomial.elkikJacobianIdeal f).map (MvPolynomial.eval b) := by
    obtain ⟨P, hPH, z, hz, hPb⟩ := exists_eval_eq_pow_mul_one_sub (Nat.le_of_lt hhn) hjac hba
    have hzJ : -z ∈ Ring.jacobson R := by
      refine IsAdicComplete.le_jacobson (I := J) (J.neg_mem ?_)
      have hle : filtrationIdeal t I (n - 2 * h) ≤ J := by
        simpa only [J, filtrationIdeal_def, pow_one] using
          filtrationIdeal_antitone t I (Nat.succ_le_of_lt (Nat.sub_pos_of_lt hhn))
      exact hle hz
    have hunit : IsUnit (1 - z) := by
      simpa only [sub_eq_add_neg, mul_one, add_comm] using Ring.mem_jacobson_iff.mp hzJ 1
    exact (((MvPolynomial.elkikJacobianIdeal f).map (MvPolynomial.eval b)).mul_unit_mem_iff_mem
      hunit).mp (hPb ▸ Ideal.mem_map_of_mem (MvPolynomial.eval b) hPH)
  exact ⟨b, hba, hfb, hjac_b⟩

/-- **Gabber–Ramero, Lemma 5.4.8 (ideal-inclusion form).** Over a `(t) * I`-adically complete ring
`R`, if `2 * h < n`, `t ^ h` is left-regular, `C (t ^ h) ∈ elkikJacobianIdeal f ⊔ ker (eval a)`
and `span (range f) ≤ ker (eval a) ⊔ (filtrationIdeal t I n).map C`, then there exists `b : ι → R`
congruent to `a` modulo `filtrationIdeal t I (n - h)` such that `span (range f) ≤ ker (eval b)` and
`C (t ^ h) ∈ elkikJacobianIdeal f ⊔ ker (eval b)`. -/
theorem exists_span_le_ker_eval_of_isAdicComplete (t : R) (I : Ideal R)
    [IsAdicComplete (Ideal.span {t} * I) R]
    (f : σ → MvPolynomial ι R) (a : ι → R) {h n : ℕ} (hhn : 2 * h < n)
    (ht : IsLeftRegular (t ^ h))
    (ha : Ideal.span (Set.range f) ≤
      RingHom.ker (MvPolynomial.eval a) ⊔ (filtrationIdeal t I n).map MvPolynomial.C)
    (hjac : MvPolynomial.C (t ^ h) ∈
      MvPolynomial.elkikJacobianIdeal f ⊔ RingHom.ker (MvPolynomial.eval a)) :
    ∃ b : ι → R, (∀ i, b i - a i ∈ filtrationIdeal t I (n - h)) ∧
      Ideal.span (Set.range f) ≤ RingHom.ker (MvPolynomial.eval b) ∧
      MvPolynomial.C (t ^ h) ∈
        MvPolynomial.elkikJacobianIdeal f ⊔ RingHom.ker (MvPolynomial.eval b) := by
  have ha' (r : σ) : MvPolynomial.eval a (f r) ∈ filtrationIdeal t I n :=
    (MvPolynomial.mem_ker_eval_sup_map_C_iff a (filtrationIdeal t I n) (f r)).mp
      (ha (Ideal.subset_span ⟨r, rfl⟩))
  have hjac' : t ^ h ∈ (MvPolynomial.elkikJacobianIdeal f).map (MvPolynomial.eval a) ⊔
      filtrationIdeal t I (n - h) :=
    Ideal.mem_sup_left ((MvPolynomial.C_mem_sup_ker_eval_iff a _ (t ^ h)).mp hjac)
  obtain ⟨b, hba, hfb, hjac_b⟩ := exists_eval_eq_zero_of_isAdicComplete t I f a hhn ht ha' hjac'
  refine ⟨b, hba, Ideal.span_le.mpr ?_,
    (MvPolynomial.C_mem_sup_ker_eval_iff b _ (t ^ h)).mpr hjac_b⟩
  rintro _ ⟨r, rfl⟩
  exact RingHom.mem_ker.mpr (hfb r)

/-- Principal-ideal specialisation of `exists_eval_eq_zero_of_isAdicComplete` (`I = ⊤`): over a
`(t)`-adically complete ring `R`, an approximate solution modulo `t ^ n` with `2 * h < n`,
`IsLeftRegular (t ^ h)` and `t ^ h ∈ (elkikJacobianIdeal f).map (eval a) ⊔ span {t ^ (n - h)}`
lifts to an exact zero congruent to `a` modulo `t ^ (n - h)`. -/
theorem exists_eval_eq_zero_of_isAdicComplete_span_singleton (t : R)
    [IsAdicComplete (Ideal.span {t}) R]
    (f : σ → MvPolynomial ι R) (a : ι → R) {h n : ℕ} (hhn : 2 * h < n)
    (ht : IsLeftRegular (t ^ h))
    (ha : ∀ r, t ^ n ∣ MvPolynomial.eval a (f r))
    (hjac : t ^ h ∈ (MvPolynomial.elkikJacobianIdeal f).map (MvPolynomial.eval a) ⊔
      Ideal.span {t ^ (n - h)}) :
    ∃ b : ι → R, (∀ i, t ^ (n - h) ∣ b i - a i) ∧
      (∀ r, MvPolynomial.eval b (f r) = 0) ∧
      t ^ h ∈ (MvPolynomial.elkikJacobianIdeal f).map (MvPolynomial.eval b) := by
  have : IsAdicComplete (Ideal.span {t} * (⊤ : Ideal R)) R := by
    rwa [Ideal.mul_top]
  have htop (m : ℕ) : filtrationIdeal t (⊤ : Ideal R) m = Ideal.span {t ^ m} := by
    rw [filtrationIdeal_def, Ideal.mul_top, Ideal.span_singleton_pow]
  have ha' (r : σ) : MvPolynomial.eval a (f r) ∈ filtrationIdeal t ⊤ n := by
    rw [htop, Ideal.mem_span_singleton]
    exact ha r
  have hjac' : t ^ h ∈ (MvPolynomial.elkikJacobianIdeal f).map (MvPolynomial.eval a) ⊔
      filtrationIdeal t ⊤ (n - h) := by
    rwa [htop]
  obtain ⟨b, hba, hfb, hjac_b⟩ := exists_eval_eq_zero_of_isAdicComplete t ⊤ f a hhn ht ha' hjac'
  refine ⟨b, fun i ↦ Ideal.mem_span_singleton.mp (htop (n - h) ▸ hba i), hfb, hjac_b⟩

/-- Lifts the Elkik Jacobian membership `t ^ h ∈ H(a) + filtrationIdeal t I (n - h)` along a
compatible Newton sequence `u` to the limit point `b : ι → completion t I`. -/
private theorem completionMap_pow_mem_map_elkikJacobianIdeal {t : R} {I : Ideal R}
    {f : σ → MvPolynomial ι R} {a : ι → R} {u : ℕ → ι → R} {b : ι → completion t I}
    {h n : ℕ} (hhn : 2 * h < n) (ht : IsLeftRegular (t ^ h))
    (hjac : t ^ h ∈ (MvPolynomial.elkikJacobianIdeal f).map (MvPolynomial.eval a) ⊔
      filtrationIdeal t I (n - h))
    (hua : ∀ m i, u m i - a i ∈ filtrationIdeal t I (n - h))
    (hsub : ∀ {m m' : ℕ}, m ≤ m' → ∀ i, u m' i - u m i ∈ filtrationIdeal t I (m + 1 + h))
    (heval : ∀ p m, eval t I m (MvPolynomial.eval b (MvPolynomial.map (completionMap t I) p)) =
      residueMap t I m (MvPolynomial.eval (u m) p)) :
    completionMap t I (t ^ h) ∈
      (MvPolynomial.elkikJacobianIdeal
        (fun r ↦ MvPolynomial.map (completionMap t I) (f r))).map (MvPolynomial.eval b) := by
  choose P hPH z hz hPb using fun m ↦
    exists_eval_eq_pow_mul_one_sub (Nat.le_of_lt hhn) hjac (hua m)
  -- Use a single polynomial lift `P 0 ∈ elkikJacobianIdeal f` across all levels `m`.
  have hdiff_m (m : ℕ) :
      t ^ h - MvPolynomial.eval (u m) (P 0) ∈ filtrationIdeal t I (h + (n - 2 * h)) := by
    have h0 : t ^ h - MvPolynomial.eval (u 0) (P 0) = t ^ h * z 0 := by
      rw [hPb 0]; ring
    have hm0 : MvPolynomial.eval (u m) (P 0) - MvPolynomial.eval (u 0) (P 0) ∈
        filtrationIdeal t I (n - h) := by
      refine MvPolynomial.eval_sub_eval_mem (P 0) fun i ↦ ?_
      rw [← sub_sub_sub_cancel_right (u m i) (u 0 i) (a i)]
      exact Ideal.sub_mem _ (hua m i) (hua 0 i)
    have hn_eq : n - h = h + (n - 2 * h) := by omega
    have htz0 : t ^ h * z 0 ∈ filtrationIdeal t I (n - h) :=
      hn_eq ▸ mem_filtrationIdeal_add_iff.mpr ⟨z 0, hz 0, rfl⟩
    have hlin : t ^ h - MvPolynomial.eval (u m) (P 0) =
        (t ^ h * z 0) - (MvPolynomial.eval (u m) (P 0) - MvPolynomial.eval (u 0) (P 0)) := by
      rw [← h0]
      ring
    rw [← hn_eq, hlin]
    exact Ideal.sub_mem _ htz0 hm0
  choose w hw htw using fun m ↦ mem_filtrationIdeal_add_iff.mp (hdiff_m m)
  have hw_compat (m m' : ℕ) (hmm' : m ≤ m') :
      transition t I hmm' (residueMap t I m' (w m')) = residueMap t I m (w m) := by
    rw [transition_residueMap, residueMap_eq_iff]
    have hmul : t ^ h * (w m' - w m) ∈ Ideal.span {t ^ h} * filtrationIdeal t I (m + 1) := by
      have heq : t ^ h * (w m' - w m) =
          -(MvPolynomial.eval (u m') (P 0) - MvPolynomial.eval (u m) (P 0)) := by
        calc
          t ^ h * (w m' - w m) = (t ^ h * w m') - (t ^ h * w m) := by ring
          _ = (t ^ h - MvPolynomial.eval (u m') (P 0)) -
                (t ^ h - MvPolynomial.eval (u m) (P 0)) := by rw [htw m', htw m]
          _ = -(MvPolynomial.eval (u m') (P 0) - MvPolynomial.eval (u m) (P 0)) := by ring
      rw [heq, ← filtrationIdeal_add, Nat.add_comm h (m + 1)]
      exact (filtrationIdeal t I (m + 1 + h)).neg_mem
        (MvPolynomial.eval_sub_eval_mem (P 0) (hsub hmm'))
    obtain ⟨y, hy, hyw⟩ := Ideal.mem_span_singleton_mul.mp hmul
    exact filtrationIdeal_antitone t I (Nat.le_succ m) (ht hyw ▸ hy)
  let w_comp : completion t I :=
    ⟨fun m ↦ residueMap t I m (w m), (mem_completionSubring t I _).mpr hw_compat⟩
  have hw1 : eval t I 1 w_comp = 0 := by
    simp only [w_comp, eval_apply, residueMap_eq_zero_iff]
    exact filtrationIdeal_antitone t I (Nat.succ_le_of_lt (Nat.sub_pos_of_lt hhn)) (hw 1)
  have hunit : IsUnit (1 - w_comp) := by
    have hjac_rad : -w_comp ∈ Ring.jacobson (completion t I) :=
      ker_eval_one_le_jacobson t I (by simp [RingHom.mem_ker, hw1])
    simpa only [sub_eq_add_neg, mul_one, add_comm] using Ring.mem_jacobson_iff.mp hjac_rad 1
  let P_comp := MvPolynomial.map (completionMap t I) (P 0)
  have hP_comp : P_comp ∈ MvPolynomial.elkikJacobianIdeal
      (fun r ↦ MvPolynomial.map (completionMap t I) (f r)) :=
    MvPolynomial.map_elkikJacobianIdeal_le (completionMap t I) f
      (Ideal.mem_map_of_mem _ (hPH 0))
  have hPb_comp : MvPolynomial.eval b P_comp = completionMap t I (t ^ h) * (1 - w_comp) := by
    apply completion_ext
    intro m
    have hw_eval : eval t I m w_comp = residueMap t I m (w m) := eval_apply t I m w_comp
    rw [heval (P 0) m, map_mul, map_sub, map_one, eval_completionMap, hw_eval,
      ← map_one (residueMap t I m), ← map_sub, ← map_mul]
    congr 1
    calc
      MvPolynomial.eval (u m) (P 0) = t ^ h - (t ^ h - MvPolynomial.eval (u m) (P 0)) := by ring
      _ = t ^ h - t ^ h * w m := by rw [htw m]
      _ = t ^ h * (1 - w m) := by ring
  exact (((MvPolynomial.elkikJacobianIdeal
    (fun r ↦ MvPolynomial.map (completionMap t I) (f r))).map
      (MvPolynomial.eval b)).mul_unit_mem_iff_mem hunit).mp
    (hPb_comp ▸ Ideal.mem_map_of_mem (MvPolynomial.eval b) hP_comp)

/-- **Exact lifting into the `(t, I)`-adic completion over an arbitrary commutative ring.** Without
assuming `R` complete or separated, any approximate solution `a : ι → R` with `2 * h < n`,
`IsLeftRegular (t ^ h)`, `f r(a) ∈ filtrationIdeal t I n` and
`t ^ h ∈ (elkikJacobianIdeal f).map (eval a) ⊔ filtrationIdeal t I (n - h)` lifts to an exact
solution `b : ι → completion t I` matching `a` at residue level `n - h` and preserving the Elkik
Jacobian condition over `completion t I`. -/
theorem exists_eval_completion_eq_zero (t : R) (I : Ideal R)
    (f : σ → MvPolynomial ι R) (a : ι → R) {h n : ℕ} (hhn : 2 * h < n)
    (ht : IsLeftRegular (t ^ h))
    (ha : ∀ r, MvPolynomial.eval a (f r) ∈ filtrationIdeal t I n)
    (hjac : t ^ h ∈ (MvPolynomial.elkikJacobianIdeal f).map (MvPolynomial.eval a) ⊔
      filtrationIdeal t I (n - h)) :
    ∃ b : ι → completion t I,
      (∀ i, eval t I (n - h) (b i) = residueMap t I (n - h) (a i)) ∧
      (∀ r, MvPolynomial.eval b (MvPolynomial.map (completionMap t I) (f r)) = 0) ∧
      completionMap t I (t ^ h) ∈
        (MvPolynomial.elkikJacobianIdeal
          (fun r ↦ MvPolynomial.map (completionMap t I) (f r))).map (MvPolynomial.eval b) := by
  obtain ⟨u, h0, -, hstep, hfu, -⟩ :=
    exists_approximateSolution_seq t I f a hhn ht ha hjac
  have hexp_ge (m : ℕ) : m + 1 + h ≤ newtonStepExp h n m - h := by
    rw [newtonStepExp_eq (Nat.le_of_lt hhn) m]
    have hmul : (m + 1) * 1 ≤ 2 ^ m * (n - 2 * h) :=
      Nat.mul_le_mul Nat.lt_two_pow_self (Nat.succ_le_of_lt (Nat.sub_pos_of_lt hhn))
    omega
  have hsub_I {m m' : ℕ} (hmm' : m ≤ m') (i : ι) :
      u m' i - u m i ∈ filtrationIdeal t I (m + 1 + h) :=
    (filtrationIdeal_mono_right t (Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp
      (Nat.two_pow_pos m))) _).trans (filtrationIdeal_antitone t I (hexp_ge m))
      (sub_newtonIter_mem hhn hstep hmm' i)
  have hcoord_compat (i : ι) (m m' : ℕ) (hmm' : m ≤ m') :
      transition t I hmm' (residueMap t I m' (u m' i)) = residueMap t I m (u m i) := by
    rw [transition_residueMap, residueMap_eq_iff]
    exact filtrationIdeal_antitone t I (by omega) (hsub_I hmm' i)
  let b : ι → completion t I := fun i ↦
    ⟨fun m ↦ residueMap t I m (u m i), (mem_completionSubring t I _).mpr (hcoord_compat i)⟩
  have heval_proj (p : MvPolynomial ι R) (m : ℕ) :
      eval t I m (MvPolynomial.eval b (MvPolynomial.map (completionMap t I) p)) =
        residueMap t I m (MvPolynomial.eval (u m) p) := by
    have hcomp : (eval t I m).comp
          ((MvPolynomial.eval b).comp (MvPolynomial.map (completionMap t I))) =
        (residueMap t I m).comp (MvPolynomial.eval (u m)) := by
      refine MvPolynomial.ringHom_ext' (by ext c; simp) fun i ↦ ?_
      simp [b, eval_apply]
    exact RingHom.congr_fun hcomp p
  have hba (i : ι) : eval t I (n - h) (b i) = residueMap t I (n - h) (a i) := by
    simp only [b, eval_apply, residueMap_eq_iff, ← h0]
    simpa using sub_newtonIter_mem hhn hstep (Nat.zero_le (n - h)) i
  have hfb (r : σ) : MvPolynomial.eval b (MvPolynomial.map (completionMap t I) (f r)) = 0 := by
    apply completion_ext
    intro m
    rw [heval_proj, map_zero, residueMap_eq_zero_iff]
    have hle : m ≤ newtonStepExp h n m := by
      have := hexp_ge m
      omega
    exact (filtrationIdeal_mono_right t (Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp
      (Nat.two_pow_pos m))) _).trans (filtrationIdeal_antitone t I hle) (hfu m r)
  have hua (m : ℕ) (i : ι) : u m i - a i ∈ filtrationIdeal t I (n - h) := by
    rw [← h0]
    simpa using sub_newtonIter_mem hhn hstep (Nat.zero_le m) i
  exact ⟨b, hba, hfb,
    completionMap_pow_mem_map_elkikJacobianIdeal hhn ht hjac hua hsub_I heval_proj⟩

end Complete

end TauCeti.HenselianApproximation
