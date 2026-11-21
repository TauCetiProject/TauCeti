/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Analytic.ExtractZeros
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.LinearAlgebra.HermiteInterpolation

/-!
# Analytic Hermite interpolation quotients

Given a function `f : 𝕜 → 𝕜` analytic on an open set `U` containing `K` and a finite set `S` of
interpolation nodes with multiplicities `m : 𝕜 → ℕ`, this file constructs an interpolating
polynomial `P` matching the jets `iteratedDeriv k f a` for `a ∈ S`, `k < m a`, together with an
analytic quotient `q` on an open neighbourhood `U' ⊇ K` (specifically `U \ (S \ K)`) such that
`f z - P.eval z = (∏ a ∈ S, (z - a) ^ m a) * q z` on `K`.

## Main results

* `AnalyticOnNhd.exists_hermite_quotient`: existence of the interpolating polynomial `P` and
  analytic quotient `q` on an open neighbourhood of `K`.
-/

public section

open Polynomial Set

/-- **Analytic Hermite interpolation quotient.** Let `f : 𝕜 → 𝕜` be analytic on an open set
`U ⊇ K`, and let `S : Finset 𝕜` be a finite set of nodes with multiplicities `m : 𝕜 → ℕ`. Then
there exist a polynomial `P : 𝕜[X]`, an open neighbourhood `U'` of `K`, and a function `q` analytic
on `U'` such that `P.eval` matches the jets `iteratedDeriv k f a` for `a ∈ S` and `k < m a`, and
`f z - P.eval z = (∏ a ∈ S, (z - a) ^ m a) * q z` for all `z ∈ K`. -/
theorem AnalyticOnNhd.exists_hermite_quotient {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CharZero 𝕜] [CompleteSpace 𝕜] {K U : Set 𝕜} (hU : IsOpen U) (hKU : K ⊆ U) {f : 𝕜 → 𝕜}
    (hf : AnalyticOnNhd 𝕜 f U) (S : Finset 𝕜) (m : 𝕜 → ℕ) :
    ∃ (P : 𝕜[X]) (U' : Set 𝕜) (q : 𝕜 → 𝕜), IsOpen U' ∧ K ⊆ U' ∧ AnalyticOnNhd 𝕜 q U' ∧
      (∀ z ∈ K, f z - P.eval z = (∏ a ∈ S, (z - a) ^ m a) * q z) ∧
      (∀ a ∈ S, ∀ k < m a, iteratedDeriv k (fun z ↦ P.eval z) a = iteratedDeriv k f a) := by
  classical
  have hbij := (Polynomial.eval_iterate_derivative_bijective_iff_of_charZero
    (K := 𝕜) (a := fun i : S ↦ (i : 𝕜)) (m := fun i : S ↦ m i)).mpr
    fun _ _ hij _ _ h ↦ hij (Subtype.ext h)
  obtain ⟨P₀, hP_eq⟩ := hbij.2 fun (i : S) (k : Fin (m i)) ↦ iteratedDeriv k f i
  let P : 𝕜[X] := P₀
  have hP : ∀ a ∈ S, ∀ k < m a, iteratedDeriv k (fun z ↦ P.eval z) a =
      iteratedDeriv k f a := fun a ha k hk ↦ by
    rw [Polynomial.iteratedDeriv]
    exact congrFun (congrFun hP_eq ⟨a, ha⟩) ⟨k, hk⟩
  set Sin := S.filter (· ∈ K)
  set Sout := S.filter (· ∉ K)
  set U' := U \ (Sout : Set 𝕜)
  have hU' : IsOpen U' := hU.sdiff Sout.finite_toSet.isClosed
  have hKU' : K ⊆ U' := fun z hz ↦ ⟨hKU hz, fun hz' ↦ (Finset.mem_filter.mp hz').2 hz⟩
  have hP_an : AnalyticOnNhd 𝕜 (fun z ↦ P.eval z) univ := AnalyticOnNhd.eval_polynomial P
  have hfP_an : AnalyticOnNhd 𝕜 (fun z ↦ f z - P.eval z) U' :=
    (hf.mono sdiff_subset).sub (hP_an.mono (subset_univ U'))
  have hord_in : ∀ a ∈ Sin, (m a : ℕ∞) ≤ analyticOrderAt (fun z ↦ f z - P.eval z) a := by
    intro a ha
    obtain ⟨haS, haK⟩ := Finset.mem_filter.mp ha
    have hfa := hf a (hKU haK)
    have hPa := hP_an a (mem_univ a)
    have hfPa : AnalyticAt 𝕜 (fun z ↦ f z - P.eval z) a := hfa.sub hPa
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hfPa]
    intro k hk
    rw [iteratedDeriv_fun_sub hfa.contDiffAt hPa.contDiffAt, hP a haS k hk, sub_self]
  obtain ⟨q₁, hq₁_an, hq₁_eq⟩ := hfP_an.exists_eq_prod_pow_smul Sin m hord_in
  set Qout : 𝕜 → 𝕜 := fun z ↦ ∏ b ∈ Sout, (z - b) ^ m b
  have hQout_an : AnalyticOnNhd 𝕜 Qout U' := fun z _ ↦ by
    change AnalyticAt 𝕜 (fun w ↦ ∏ b ∈ Sout, (w - b) ^ m b) z
    fun_prop
  have hQout_ne : ∀ z ∈ U', Qout z ≠ 0 := fun z hz ↦
    Finset.prod_ne_zero_iff.mpr fun b hb ↦ pow_ne_zero _ (sub_ne_zero.mpr fun hzb ↦ hz.2 (hzb ▸ hb))
  refine ⟨P, U', fun z ↦ q₁ z / Qout z, hU', hKU', hq₁_an.div hQout_an hQout_ne,
    fun z hz ↦ ?_, hP⟩
  have hsplit : (∏ a ∈ S, (z - a) ^ m a) = (∏ a ∈ Sin, (z - a) ^ m a) * Qout z :=
    (Finset.prod_filter_mul_prod_filter_not S (· ∈ K) fun a ↦ (z - a) ^ m a).symm
  have h1 := hq₁_eq z
  simp only [smul_eq_mul] at h1
  rw [h1, hsplit, mul_assoc, mul_div_cancel₀ _ (hQout_ne z (hKU' hz))]
