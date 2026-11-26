/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Analytic.ExtractZeros
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.LinearAlgebra.HermiteInterpolation

/-!
# Analytic Hermite interpolation with factored remainder

Over a characteristic-zero nontrivially normed field `𝕜`, given a function `f : 𝕜 → 𝕜` analytic on a
neighbourhood of `U`, a finite set `t ⊆ U`, and prescribed jet multiplicities `m : 𝕜 → ℕ`, algebraic
Hermite interpolation (`Polynomial.ordinaryHermiteJet_bijective`) constructs a unique polynomial `P`
of degree `< ∑ x ∈ t, m x` matching the iterated derivatives of `f` of orders `k < m a` at each
`a ∈ t`. Because `f - P` then vanishes to order at least `m a` at every `a ∈ t`, repeated divided
differences (`AnalyticOnNhd.exists_eq_prod_pow_smul`) factor the remainder globally as
`f z - P.eval z = (∏ x ∈ t, (X - C x) ^ m x).eval z * F z` for a function `F : 𝕜 → 𝕜` analytic on a
neighbourhood of `U`.

## Main results

* `AnalyticOnNhd.exists_polynomial_iteratedDeriv_eq_and_sub_eq_mul`: simultaneous finite-jet
  polynomial interpolation and analytic remainder factorization on `U`.

## References

* A. Rainer, *Advanced Complex Analysis*, proof of Theorem 11.7.
* J. L. Walsh, *Interpolation and Approximation by Rational Functions in the Complex Domain*,
  5th ed., AMS, 1969, §3.1.
-/

public section

open Polynomial Set

/-- **Analytic Hermite interpolation with factored remainder.** Let `f : 𝕜 → 𝕜` be analytic on a
neighbourhood of `U` over a complete characteristic-zero nontrivially normed field `𝕜`, let
`t : Finset 𝕜` satisfy `(t : Set 𝕜) ⊆ U`, and let `m : 𝕜 → ℕ` prescribe jet orders. There exist a
polynomial `P : 𝕜[X]` of degree `< ∑ x ∈ t, m x` and a function `F : 𝕜 → 𝕜` analytic on a
neighbourhood of `U` such that `P` matches the iterated derivatives of `f` of orders `k < m a` at
every `a ∈ t` and `f z - P.eval z = (∏ x ∈ t, (X - C x) ^ m x).eval z * F z` for all `z : 𝕜`. -/
theorem AnalyticOnNhd.exists_polynomial_iteratedDeriv_eq_and_sub_eq_mul
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜] {U : Set 𝕜} {f : 𝕜 → 𝕜}
    (hf : AnalyticOnNhd 𝕜 f U) {t : Finset 𝕜} (htU : (t : Set 𝕜) ⊆ U) (m : 𝕜 → ℕ) :
    ∃ (P : 𝕜[X]) (F : 𝕜 → 𝕜), P.degree < ↑(∑ x ∈ t, m x) ∧ AnalyticOnNhd 𝕜 F U ∧
      (∀ a ∈ t, ∀ k < m a, iteratedDeriv k (fun z ↦ P.eval z) a = iteratedDeriv k f a) ∧
      ∀ z, f z - P.eval z = (∏ x ∈ t, (X - C x) ^ m x).eval z * F z := by
  classical
  obtain ⟨P₀, hP₀⟩ := (ordinaryHermiteJet_bijective
    (Subtype.val_injective : Function.Injective ((↑) : t → 𝕜)) (fun x : t ↦ m x.val)
    fun _ k _ ↦ Ne.isUnit (Nat.cast_ne_zero.mpr k.factorial_ne_zero)).surjective
      fun (x : t) (k : Fin (m x.val)) ↦ iteratedDeriv k.val f x.val
  set P : 𝕜[X] := P₀.val
  have hP_deg : P.degree < ↑(∑ x ∈ t, m x) := by
    simpa only [P, mem_degreeLT, Finset.sum_coe_sort] using P₀.property
  have hP_jet {a : 𝕜} (ha : a ∈ t) {k : ℕ} (hk : k < m a) :
      iteratedDeriv k (fun z ↦ P.eval z) a = iteratedDeriv k f a := by
    have h1 := congr_fun (congr_fun hP₀ ⟨a, ha⟩) ⟨k, hk⟩
    rw [ordinaryHermiteJet_apply] at h1
    simpa [P, Polynomial.iteratedDeriv] using h1
  have hP_an : AnalyticOnNhd 𝕜 (fun z ↦ P.eval z) univ := AnalyticOnNhd.eval_polynomial P
  have hh_an : AnalyticOnNhd 𝕜 (fun z ↦ f z - P.eval z) U :=
    hf.sub (hP_an.mono (subset_univ U))
  have hord : ∀ a ∈ t, (m a : ℕ∞) ≤ analyticOrderAt (fun z ↦ f z - P.eval z) a := by
    intro a ha
    have haU : a ∈ U := htU ha
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hh_an a haU)]
    intro k hk
    rw [iteratedDeriv_fun_sub (hf a haU).contDiffAt (hP_an a (mem_univ a)).contDiffAt,
      hP_jet ha hk, sub_self]
  obtain ⟨F, hF, hfactor⟩ := hh_an.exists_eq_prod_pow_smul t m hord
  refine ⟨P, F, hP_deg, hF, fun _ ha _ hk ↦ hP_jet ha hk, fun z ↦ ?_⟩
  simpa [eval_prod, smul_eq_mul] using hfactor z
