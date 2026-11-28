/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import TauCeti.Analysis.Complex.PartialDeriv.Basic
import Mathlib.LinearAlgebra.Lagrange
import TauCeti.Algebra.Polynomial.Degree.CoordinateLine
import TauCeti.Algebra.Polynomial.Eval.DegreeLT
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Complex.Liouville

/-!
# Polynomial degree preservation under partial derivatives

Differentiating an entire function `f : (ι → ℂ) → ℂ` along any coordinate `i` (once or iterated
`m` times) preserves strict polynomial degree bounds `Q.degree < d` along every coordinate line `j`.
Along `j = i` this follows from polynomial differentiation, and along `j ≠ i` it follows by
differentiating the coordinate-line Lagrange interpolation identity along `i`. Moreover, vanishing
of `(partialDeriv i)^[d] f` characterizes entire functions that agree along every `zᵢ`-line with a
polynomial of degree `< d` (`TauCeti.iterate_partialDeriv_eq_zero_iff_exists_degree_lt`), so any
operator `T` sending `0` to `0` and commuting with `(partialDeriv j)^[n]` on an entire function `f`
(with `T f` entire) also preserves strict coordinate-`j` polynomial degree bounds.

## Main results

* `TauCeti.exists_degree_lt_and_partialDeriv_eq_eval`: `partialDeriv i f` preserves any strict
  coordinate polynomial degree bound `< d`.
* `TauCeti.exists_degree_lt_and_iterate_partialDeriv_eq_eval`: `(partialDeriv i)^[m] f` preserves
  any strict coordinate polynomial degree bound `< d`.
* `TauCeti.iterate_partialDeriv_eq_zero_iff_exists_degree_lt`: `(partialDeriv i)^[d] f = 0` iff
  every `zᵢ`-line agrees with a polynomial of degree `< d`.
* `TauCeti.exists_degree_lt_of_comm_iterate_partialDeriv`: any operator `T` taking an entire
  function `f` to an entire function, commuting with `(partialDeriv j)^[n]` on `f`, and sending
  `0` to `0` preserves strict coordinate-`j` polynomial degree bounds.
-/

public section

open Function Polynomial

namespace TauCeti

/-- Differentiating an entire function along coordinate `i` preserves a strict polynomial degree
bound `< d` in every coordinate `j`. -/
theorem exists_degree_lt_and_partialDeriv_eq_eval {ι : Type*} [DecidableEq ι] [Finite ι]
    {f : (ι → ℂ) → ℂ} (hf : Differentiable ℂ f) (i j : ι) {d : WithBot ℕ}
    (hdeg : ∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update y j w) = Q.eval w) (z : ι → ℂ) :
    ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, partialDeriv i f (update z j w) = Q.eval w := by
  by_cases hij : j = i
  · subst hij
    obtain ⟨Q, hQdeg, hQ⟩ := hdeg z
    refine ⟨Q.derivative, degree_derivative_le.trans_lt hQdeg, fun w ↦ ?_⟩
    rw [partialDeriv_eq_deriv_update (hf _) j, update_self]
    have hfun : (fun s ↦ f (update (update z j w) j s)) = fun s ↦ Q.eval s :=
      funext fun s ↦ by simp [hQ]
    rw [hfun, Polynomial.deriv]
  · obtain ⟨n, rfl, _⟩ := Polynomial.exists_mem_evalDegreeLT_of_exists_degree_lt (hdeg z)
    have := Fintype.ofFinite ι
    let s : Finset ℕ := Finset.range n
    let v : ℕ → ℂ := fun m ↦ (m : ℂ)
    have hv : Set.InjOn v s := Nat.cast_injective.injOn
    refine ⟨Lagrange.interpolate s v (fun m ↦ partialDeriv i f (update z j (v m))), ?_,
      fun w ↦ ?_⟩
    · simpa only [s, Finset.card_range] using
        Lagrange.degree_interpolate_lt (fun m ↦ partialDeriv i f (update z j (v m))) hv
    · have hline (w : ℂ) : (fun u ↦ f (update (update z j w) i u)) =
          fun u ↦ ∑ m ∈ s, (Lagrange.basis s v m).eval w * f (update (update z j (v m)) i u) :=
        update_update_eq_sum_lagrange_basis hij hv
          (by simpa only [s, Finset.card_range] using hdeg) z w
      have hdiff (m : ℕ) (_ : m ∈ s) : DifferentiableAt ℂ
          (fun u ↦ (Lagrange.basis s v m).eval w * f (update (update z j (v m)) i u)) (z i) :=
        (differentiable_comp_update hf (update z j (v m)) i (z i)).const_mul _
      rw [partialDeriv_eq_deriv_update (hf _) i, update_of_ne (Ne.symm hij), hline w,
        deriv_fun_sum hdiff, Lagrange.interpolate_apply, eval_finsetSum]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      have hpart (m : ℕ) :
          deriv (fun s ↦ f (update (update z j (v m)) i s)) (z i) =
            partialDeriv i f (update z j (v m)) := by
        simpa only [update_of_ne (Ne.symm hij)] using
          (partialDeriv_eq_deriv_update (hf (update z j (v m))) i).symm
      rw [deriv_const_mul _ (differentiable_comp_update hf (update z j (v m)) i (z i)), hpart m,
        eval_mul, eval_C, mul_comm]

/-- Iterated differentiation of an entire function along coordinate `i` preserves a strict
polynomial degree bound `< d` in every coordinate `j`. -/
theorem exists_degree_lt_and_iterate_partialDeriv_eq_eval {ι : Type*} [DecidableEq ι] [Finite ι]
    {f : (ι → ℂ) → ℂ} (hf : Differentiable ℂ f) (i j : ι) {d : WithBot ℕ}
    (hdeg : ∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update y j w) = Q.eval w) (m : ℕ) :
    ∀ z, ∃ Q : ℂ[X], Q.degree < d ∧
      ∀ w, (partialDeriv i)^[m] f (update z j w) = Q.eval w := by
  induction m with
  | zero => exact hdeg
  | succ m ih =>
    simp_rw [iterate_succ_apply']
    exact exists_degree_lt_and_partialDeriv_eq_eval (differentiable_iterate_partialDeriv hf i m)
      i j ih

/-- **Characterization of coordinate polynomials by iterated partial derivatives.** An entire
function `f : (ι → ℂ) → ℂ` satisfies `∂ᵢ^d f = 0` if and only if along every coordinate line in
`zᵢ`, it agrees with a polynomial of degree `< d`. -/
theorem iterate_partialDeriv_eq_zero_iff_exists_degree_lt {ι : Type*} [DecidableEq ι] [Finite ι]
    {f : (ι → ℂ) → ℂ} (hf : Differentiable ℂ f) (i : ι) (d : ℕ) :
    (partialDeriv i)^[d] f = 0 ↔
      ∀ z, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update z i w) = Q.eval w := by
  constructor
  · intro h z
    cases d with
    | zero =>
      refine ⟨0, by simp, fun w ↦ ?_⟩
      simpa using congrFun h (update z i w)
    | succ n =>
      have hline : Differentiable ℂ fun w ↦ f (update z i w) := differentiable_comp_update hf z i
      obtain ⟨Q, hQdeg, hQ⟩ :=
        hline.exists_eq_polynomial_eval_of_iteratedDeriv_eq_zero (n := n) fun k hk ↦ by
          have hk_split : k = (k - (n + 1)) + (n + 1) := by omega
          rw [iteratedDeriv_comp_update hf i z k, hk_split, iterate_add_apply, h,
            iterate_fixed (partialDeriv_zero_fun i) _]
          simp only [Pi.zero_apply]
      refine ⟨Q, (natDegree_le_iff_degree_le.mp hQdeg).trans_lt
        (by exact_mod_cast Nat.lt_succ_self n), fun w ↦ by simpa using congrFun hQ w⟩
  · intro h
    ext z
    cases d with
    | zero =>
      obtain ⟨Q, hQdeg, hQ⟩ := h z
      have hQ0 : Q = 0 := by
        by_contra hne
        exact absurd (zero_le_degree_iff.mpr hne) hQdeg.not_ge
      simpa [hQ0, update_eq_self] using hQ (z i)
    | succ n =>
      obtain ⟨Q, hQdeg, hQ⟩ := h z
      rw [Pi.zero_apply, iterate_partialDeriv_eq_iteratedDeriv_update hf i (n + 1) z]
      have hline : (fun w ↦ f (update z i w)) = Q.eval := funext hQ
      have hQnat : Q.natDegree < n + 1 := by
        rcases eq_or_ne Q 0 with rfl | hQ0
        · simp
        · rw [degree_eq_natDegree hQ0, Nat.cast_lt] at hQdeg
          exact hQdeg
      rw [hline, Polynomial.iteratedDeriv_eq_factorial_mul_eval_hasseDeriv,
        Polynomial.hasseDeriv_eq_zero_of_lt_natDegree Q (n + 1) hQnat, eval_zero, mul_zero]

/-- Any operator `T` taking an entire function `f` to an entire function `T f`, commuting with
`(partialDeriv j)^[n]` on `f` for every `n`, and satisfying `T 0 = 0`, preserves strict
coordinate-`j` polynomial degree bounds `< d`. -/
theorem exists_degree_lt_of_comm_iterate_partialDeriv {ι : Type*} [DecidableEq ι] [Finite ι]
    {f : (ι → ℂ) → ℂ} (T : ((ι → ℂ) → ℂ) → ((ι → ℂ) → ℂ)) (hf : Differentiable ℂ f)
    (hTf : Differentiable ℂ (T f)) {j : ι}
    (hcomm : ∀ n, (partialDeriv j)^[n] (T f) = T ((partialDeriv j)^[n] f))
    (hT0 : T 0 = 0) {d : WithBot ℕ}
    (hfj : ∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update y j w) = Q.eval w) (z : ι → ℂ) :
    ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, T f (update z j w) = Q.eval w := by
  obtain ⟨n, rfl, _⟩ := Polynomial.exists_mem_evalDegreeLT_of_exists_degree_lt (hfj z)
  refine (iterate_partialDeriv_eq_zero_iff_exists_degree_lt hTf j n).mp ?_ z
  rw [hcomm n, (iterate_partialDeriv_eq_zero_iff_exists_degree_lt hf j n).mpr hfj, hT0]

end TauCeti
