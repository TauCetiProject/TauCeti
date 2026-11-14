/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import TauCeti.Analysis.Calculus.Jet.Realization
import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList

/-!
# Multivariate Taylor polynomials and integral remainders

For a map `u : E → F` between normed spaces over `𝕜`, a natural order `m`, and an expansion point
`y : E`, `TauCeti.taylorPolynomial 𝕜 m u y` is the Taylor polynomial of degree `m` about `y`:

`T^m_y u (x) = ∑ j ∈ Finset.range (m + 1), (j ! : 𝕜)⁻¹ • iteratedFDeriv 𝕜 j u y (fun _ ↦ x - y)`.

It is the specialization of `TauCeti.finiteJetPolynomial` to the iterated Fréchet derivatives of
`u` at `y`. Consequently, even without differentiability assumptions on `u`, `T^m_y u` is smooth
(indeed analytic) in `x` and all of its Fréchet derivatives of order strictly above `m` vanish.
Over `ℝ` or `ℂ`, when `u` is `C^m` at `y`, its iterated Fréchet derivatives at `y` are symmetric,
so `T^m_y u` recovers every derivative of `u` at `y` up to order `m`. On the real line it agrees
with Mathlib's `taylorWithinEval u m Set.univ y`.

Over `ℝ` into a complete normed space `F`, if `u` is `C^{m + 1}` at every point of the closed
segment from `y` to `x`, Mathlib's `map_add_eq_sum_add_integral_iteratedFDeriv` gives the integral
remainder formula (`TauCeti.sub_taylorPolynomial_eq_integral`)

`u x - T^m_y u x = (m ! : ℝ)⁻¹ • ∫ t in 0..1, (1 - t) ^ m • D^{m + 1} u (y + t • (x - y)) (x - y)`.

Regularity along the whole segment is load-bearing: a step function smooth near `y` and jumping
halfway along the segment has zero Taylor polynomial at `y`, nonzero increment, and zero integral
of the derivative away from the jump. As an immediate consequence of the integral remainder, any
`C^{m + 1}` map whose `(m + 1)`-st Fréchet derivative vanishes along the segment from `y` to `x`
equals its `m`-th Taylor polynomial at `x`
(`TauCeti.taylorPolynomial_eq_self_of_iteratedFDeriv_eq_zero_segment`,
`TauCeti.taylorPolynomial_eq_self_of_iteratedFDeriv_eq_zero`).

## Main definitions

* `TauCeti.taylorPolynomial`: the Taylor polynomial of degree `m` of `u` about `y`.

## Main results

* `TauCeti.contDiff_taylorPolynomial`: `taylorPolynomial 𝕜 m u y` is smooth of every order.
* `TauCeti.iteratedFDeriv_taylorPolynomial_eq_zero_of_lt`: derivatives of order `> m` vanish.
* `TauCeti.iteratedFDeriv_taylorPolynomial_self`: over `ℝ` or `ℂ`, derivatives up to order `m` at
  `y` match those of a `C^m` germ `u`.
* `TauCeti.taylorPolynomial_real_eq_taylorWithinEval`: agreement with `taylorWithinEval` on `ℝ`.
* `TauCeti.sub_taylorPolynomial_eq_integral`: Taylor's theorem with integral remainder along the
  segment `[y, x]`.
* `TauCeti.taylorPolynomial_eq_self_of_iteratedFDeriv_eq_zero`: a `C^{m + 1}` map with vanishing
  `(m + 1)`-st derivative equals its `m`-th Taylor polynomial about any center.
-/

public section

noncomputable section

open Nat Set Filter
open scoped ContDiff Topology

namespace TauCeti

section NormedField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜) in
/-- The Taylor polynomial of degree `m` of `u : E → F` expanded at `y` and evaluated at `x`:
`∑ j ∈ Finset.range (m + 1), (j ! : 𝕜)⁻¹ • iteratedFDeriv 𝕜 j u y (fun _ ↦ x - y)`. -/
def taylorPolynomial (m : ℕ) (u : E → F) (y x : E) : F :=
  finiteJetPolynomial m (fun i ↦ iteratedFDeriv 𝕜 i.val u y) y x

/-- `taylorPolynomial` is `finiteJetPolynomial` applied to the jet of iterated Fréchet derivatives
of `u` at `y`. -/
theorem taylorPolynomial_eq_finiteJetPolynomial (m : ℕ) (u : E → F) (y : E) :
    taylorPolynomial 𝕜 m u y =
      finiteJetPolynomial m (fun i ↦ iteratedFDeriv 𝕜 i.val u y) y :=
  (rfl)

/-- Explicit sum expansion of `taylorPolynomial`. -/
theorem taylorPolynomial_apply (m : ℕ) (u : E → F) (y x : E) :
    taylorPolynomial 𝕜 m u y x =
      ∑ j ∈ Finset.range (m + 1), (j ! : 𝕜)⁻¹ • iteratedFDeriv 𝕜 j u y (fun _ ↦ x - y) := by
  rw [taylorPolynomial, finiteJetPolynomial_apply, ← Fin.sum_univ_eq_sum_range]

/-- The degree-zero Taylor polynomial at `y` is the constant map `u y`. -/
@[simp]
theorem taylorPolynomial_zero (u : E → F) (y x : E) :
    taylorPolynomial 𝕜 0 u y x = u y := by
  simp [taylorPolynomial_apply]

/-- Recurrence separating the top-degree homogeneous term of the Taylor polynomial. -/
theorem taylorPolynomial_succ (m : ℕ) (u : E → F) (y x : E) :
    taylorPolynomial 𝕜 (m + 1) u y x =
      taylorPolynomial 𝕜 m u y x +
        ((m + 1)! : 𝕜)⁻¹ • iteratedFDeriv 𝕜 (m + 1) u y (fun _ ↦ x - y) := by
  simp only [taylorPolynomial_apply, Finset.sum_range_succ]

/-- Evaluating the Taylor polynomial at its expansion center recovers `u y`. -/
@[simp]
theorem taylorPolynomial_self (m : ℕ) (u : E → F) (y : E) :
    taylorPolynomial 𝕜 m u y y = u y := by
  rw [taylorPolynomial, finiteJetPolynomial_self, Fin.val_zero, iteratedFDeriv_zero_apply]

/-- The Taylor polynomial of a constant function is that constant function. -/
@[simp]
theorem taylorPolynomial_const (m : ℕ) (c : F) (y : E) :
    taylorPolynomial 𝕜 m (fun _ : E ↦ c) y = fun _ ↦ c := by
  ext x
  rw [taylorPolynomial_apply, Finset.sum_range_succ']
  simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _)]

@[simp]
theorem taylorPolynomial_zero_fun (m : ℕ) (y : E) :
    taylorPolynomial 𝕜 m (0 : E → F) y = 0 :=
  taylorPolynomial_const m (0 : F) y

theorem taylorPolynomial_neg (m : ℕ) (u : E → F) (y : E) :
    taylorPolynomial 𝕜 m (-u) y = -taylorPolynomial 𝕜 m u y := by
  ext x
  simp [taylorPolynomial_apply, iteratedFDeriv_neg_apply, Finset.sum_neg_distrib]

/-- The Taylor polynomial at `y` depends only on the germ of `u` at `y`. -/
theorem _root_.Filter.EventuallyEq.taylorPolynomial_eq {m : ℕ} {u v : E → F} {y : E}
    (h : u =ᶠ[𝓝 y] v) :
    taylorPolynomial 𝕜 m u y = taylorPolynomial 𝕜 m v y := by
  ext x
  simp only [taylorPolynomial_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [(h.iteratedFDeriv 𝕜 j).eq_of_nhds]

theorem taylorPolynomial_add {m : ℕ} {u v : E → F} {y : E}
    (hu : ContDiffAt 𝕜 m u y) (hv : ContDiffAt 𝕜 m v y) :
    taylorPolynomial 𝕜 m (u + v) y = taylorPolynomial 𝕜 m u y + taylorPolynomial 𝕜 m v y := by
  ext x
  simp only [Pi.add_apply, taylorPolynomial_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjle : (j : ℕ∞ω) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [iteratedFDeriv_add_apply (hu.of_le hjle) (hv.of_le hjle), add_apply, smul_add]

theorem taylorPolynomial_sub {m : ℕ} {u v : E → F} {y : E}
    (hu : ContDiffAt 𝕜 m u y) (hv : ContDiffAt 𝕜 m v y) :
    taylorPolynomial 𝕜 m (u - v) y = taylorPolynomial 𝕜 m u y - taylorPolynomial 𝕜 m v y := by
  have hv' : ContDiffAt 𝕜 m (-v) y := hv.neg
  rw [sub_eq_add_neg, taylorPolynomial_add hu hv', taylorPolynomial_neg, sub_eq_add_neg]

theorem taylorPolynomial_const_smul {m : ℕ} {u : E → F} {y : E}
    (hu : ContDiffAt 𝕜 m u y) (c : 𝕜) :
    taylorPolynomial 𝕜 m (c • u) y = c • taylorPolynomial 𝕜 m u y := by
  ext x
  simp only [Pi.smul_apply, taylorPolynomial_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjle : (j : ℕ∞ω) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [iteratedFDeriv_const_smul_apply (hu.of_le hjle), smul_apply, smul_comm]

/-- The Taylor polynomial of any map is smooth (and analytic) of every order, without any
regularity hypothesis on `u`. -/
theorem contDiff_taylorPolynomial (m : ℕ) (u : E → F) (y : E) {n : ℕ∞ω} :
    ContDiff 𝕜 n (taylorPolynomial 𝕜 m u y) :=
  contDiff_finiteJetPolynomial m _ y

/-- Every iterated Fréchet derivative of `taylorPolynomial 𝕜 m u y` of order strictly above `m`
vanishes identically. -/
@[simp]
theorem iteratedFDeriv_taylorPolynomial_eq_zero_of_lt (m : ℕ) (u : E → F) (y : E)
    {k : ℕ} (hmk : m < k) :
    iteratedFDeriv 𝕜 k (taylorPolynomial 𝕜 m u y) = 0 :=
  iteratedFDeriv_finiteJetPolynomial_eq_zero_of_le m _ y k hmk

/-- Over `ℝ` or `ℂ`, if `u` is `C^m` at `y`, then for every `j ≤ m` the `j`-th Fréchet derivative
of `taylorPolynomial 𝕜 m u y` at `y` equals that of `u`. -/
theorem iteratedFDeriv_taylorPolynomial_self [IsRCLikeNormedField 𝕜] {m : ℕ} {u : E → F} {y : E}
    (hu : ContDiffAt 𝕜 m u y) {j : ℕ} (hj : j ≤ m) :
    iteratedFDeriv 𝕜 j (taylorPolynomial 𝕜 m u y) y = iteratedFDeriv 𝕜 j u y := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let i : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  exact iteratedFDeriv_finiteJetPolynomial_self m (fun r ↦ iteratedFDeriv 𝕜 r.val u y) y i
    fun v σ ↦ iteratedFDeriv_comp_perm_of_contDiffAt (hu.of_le (by exact_mod_cast hj)) v σ

end NormedField

section Real

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- On the real line, `taylorPolynomial ℝ` agrees with Mathlib's one-dimensional
`taylorWithinEval` on `Set.univ`. -/
theorem taylorPolynomial_real_eq_taylorWithinEval (m : ℕ) (u : ℝ → F) (y x : ℝ) :
    taylorPolynomial ℝ m u y x = taylorWithinEval u m univ y x := by
  rw [taylorPolynomial_apply, taylor_within_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [iteratedDerivWithin_univ, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const,
    Finset.card_fin, smul_smul]

variable [CompleteSpace F]

/-- **Taylor's theorem with integral remainder.** If `u` is `C^{m + 1}` at every point of the
closed segment from `y` to `x`, then `u x - taylorPolynomial ℝ m u y x` is the integral along the
segment of `(1 - t) ^ m / m!` times the `(m + 1)`-st Fréchet derivative applied to `x - y`. -/
theorem sub_taylorPolynomial_eq_integral {m : ℕ} {u : E → F} {y x : E}
    (hu : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (m + 1) u (y + t • (x - y))) :
    u x - taylorPolynomial ℝ m u y x =
      (m ! : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1,
        (1 - t) ^ m • iteratedFDeriv ℝ (m + 1) u (y + t • (x - y)) (fun _ ↦ x - y) := by
  have h := map_add_eq_sum_add_integral_iteratedFDeriv (n := m) (f := u) (x := y) (y := x - y) hu
  rw [add_sub_cancel, ← taylorPolynomial_apply] at h
  exact sub_eq_of_eq_add' h

/-- If `u` is `C^{m + 1}` along the closed segment from `y` to `x` and its `(m + 1)`-st Fréchet
derivative vanishes along that segment, then its `m`-th Taylor polynomial at `y` equals `u x` at
`x`. -/
theorem taylorPolynomial_eq_self_of_iteratedFDeriv_eq_zero_segment {m : ℕ} {u : E → F} {y x : E}
    (hu : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (m + 1) u (y + t • (x - y)))
    (h0 : ∀ t ∈ Icc (0 : ℝ) 1, iteratedFDeriv ℝ (m + 1) u (y + t • (x - y)) = 0) :
    taylorPolynomial ℝ m u y x = u x := by
  symm
  rw [← sub_eq_zero, sub_taylorPolynomial_eq_integral hu]
  have hint : Set.EqOn
      (fun t : ℝ ↦ (1 - t) ^ m • iteratedFDeriv ℝ (m + 1) u (y + t • (x - y)) (fun _ ↦ x - y))
      0 (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    intro t ht
    simp [h0 t ht]
  rw [intervalIntegral.integral_congr hint]
  simp

/-- A globally `C^{m + 1}` map whose `(m + 1)`-st Fréchet derivative vanishes everywhere coincides
with its `m`-th Taylor polynomial about any expansion point `y`. -/
theorem taylorPolynomial_eq_self_of_iteratedFDeriv_eq_zero {m : ℕ} {u : E → F}
    (hu : ContDiff ℝ (m + 1) u) (h0 : iteratedFDeriv ℝ (m + 1) u = 0) (y : E) :
    taylorPolynomial ℝ m u y = u := by
  ext x
  exact taylorPolynomial_eq_self_of_iteratedFDeriv_eq_zero_segment
    (fun t _ ↦ hu.contDiffAt) (fun t _ ↦ congrFun h0 _)

end Real

end TauCeti
