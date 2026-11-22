/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Conjugate
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Bounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Principal
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.ThreeFourOne
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Hadamard
import TauCeti.NumberTheory.LFunctions.Zeros.ZeroFree.RiemannZeta
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.Bounds

/-!
# The de la Vallée Poussin zero-free region for Dirichlet L-functions

We prove `TauCeti.dirichletLFunction_zeroFreeRegion`, giving one absolute constant `c` with
`0 < c ≤ Real.log 3 / 2` such that for every modulus `q ≥ 1` and every Dirichlet character `χ`
modulo `q`, any zero `ρ` of `χ.LFunction` (read through `0 < meromorphicOrderAt χ.LFunction ρ`,
which excludes the pole of principal characters at `s = 1`) in `Re ρ ≥ 1 - c / log (q (|Im ρ| + 3))`
is real and simple, forces `χ ^ 2 = 1`, and is unique in that region (the classical de la Vallée
Poussin zero-free region with at most one exceptional zero per character, distinct from the
family-wide Landau–Page theorem).

The proof reduces principal characters to `TauCeti.riemannZeta_zeroFreeRegion` and nonprincipal
characters to their primitive character `χ.primitiveCharacter` via
`DirichletCharacter.meromorphicOrderAt_LFunction_changeLevel`. For primitive nonprincipal `χ`, the
`3-4-1` inequality (`DirichletCharacter.threeFourOne_neg_re_logDeriv_LFunction_nonneg`) rules out
all zeros of complex characters and all zeros with `|Im ρ| ≥ η / 2` for quadratic characters.
Near the real axis for quadratic `χ`, pairing conjugate zeros `{ρ, star ρ}` (or distinct real
zeros `{ρ₁, ρ₂}`, or a multiple real zero) in
`DirichletCharacter.exists_sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le` contradicts the
retained-zero budget `17 / (16 * η₀)`.

## Main results

* `TauCeti.dirichletLFunction_zeroFreeRegion`: the classical de la Vallée Poussin zero-free region
  with at most one exceptional zero per character for every `DirichletCharacter.LFunction`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §14.
-/

public section

open Complex DirichletCharacter Filter Set TauCeti.LFunctions
open scoped Topology

namespace TauCeti

private theorem re_pos_of_le_one_sub_div_log {c : ℝ} (hc : c ≤ Real.log 3 / 2) {q : ℕ}
    [NeZero q] (ρ : ℂ) (hre : 1 - c / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re) : 0 < ρ.re := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog_ge : Real.log 3 ≤ Real.log (q * (|ρ.im| + 3)) :=
    Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg ρ.im])
  have hc_le : c / Real.log (q * (|ρ.im| + 3)) ≤ 1 / 2 := by
    calc
      c / Real.log (q * (|ρ.im| + 3)) ≤ (Real.log 3 / 2) / Real.log 3 := by
        rcases le_or_gt c 0 with hc0 | _
        · exact (div_nonpos_of_nonpos_of_nonneg hc0 (hlog3.trans_le hlog_ge).le).trans
            (by positivity)
        · exact div_le_div₀ (by positivity) hc hlog3 hlog_ge
      _ = 1 / 2 := by field_simp
  linarith

private theorem log_two_mul_abs_add_three_le {q : ℕ} [NeZero q] (t : ℝ) :
    Real.log (|2 * t| + 3) ≤ 2 * Real.log (q * (|t| + 3)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
  have hlog2 : Real.log 2 ≤ 1 :=
    (Real.log_le_iff_le_exp (by norm_num)).mpr (by linarith [Real.exp_one_gt_d9])
  have hL : 1 < Real.log (q * (|t| + 3)) :=
    hlog3.trans_le (Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg t]))
  calc
    Real.log (|2 * t| + 3) ≤ Real.log (2 * (|t| + 3)) :=
      Real.log_le_log (by positivity) (by rw [abs_mul, abs_two]; linarith)
    _ = Real.log 2 + Real.log (|t| + 3) := Real.log_mul (by norm_num) (by positivity)
    _ ≤ 1 + Real.log (q * (|t| + 3)) :=
        add_le_add hlog2 (Real.log_le_log (by positivity) (by nlinarith [abs_nonneg t]))
    _ ≤ 2 * Real.log (q * (|t| + 3)) := by linarith

private theorem neg_re_logDeriv_sq_add_two_mul_le {C_ne C_ζ : ℝ} (hCne : 0 < C_ne) (hCζ : 0 < C_ζ)
    (hnonprin : ∀ {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q), ψ ≠ 1 →
      ∀ {η : ℝ}, 0 < η → η ≤ 1 → ∀ u : ℝ,
      -(logDeriv ψ.LFunction (1 + η + u * I)).re ≤
        (3 / 2) * Real.log q + C_ne * Real.log (|u| + 3))
    (hζ : ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ u : ℝ,
      -(logDeriv riemannZeta (1 + η + u * I)).re ≤
        η / (η ^ 2 + u ^ 2) + C_ζ * Real.log (|u| + 3))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {η t : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hcase : χ ^ 2 ≠ 1 ∨ (χ ^ 2 = 1 ∧ η / 2 ≤ |t|)) :
    -(logDeriv (χ ^ 2).LFunction (1 + η + 2 * t * I)).re ≤
      1 / (2 * η) +
        max (3 / 2 + 2 * C_ne) (1 + 2 * C_ζ) * Real.log (q * (|t| + 3)) := by
  set L : ℝ := Real.log (q * (|t| + 3))
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hLpos : 0 < L := Real.log_pos (by nlinarith [abs_nonneg t])
  have hlogq_le : Real.log q ≤ L := Real.log_le_log (by positivity) (by nlinarith [abs_nonneg t])
  have hlog2t_le : Real.log (|2 * t| + 3) ≤ 2 * L := log_two_mul_abs_add_three_le t
  have h2t_eq : (1 : ℂ) + η + 2 * t * I = 1 + η + ((2 * t : ℝ) : ℂ) * I := by push_cast; ring
  rcases hcase with hsq | ⟨hχ2_1, ht_big⟩
  · have h0 := hnonprin (χ ^ 2) hsq hη hη1 (2 * t)
    rw [← h2t_eq] at h0
    have hneL : C_ne * Real.log (|2 * t| + 3) ≤ 2 * C_ne * L := by
      have hm := mul_le_mul_of_nonneg_left hlog2t_le hCne.le
      linarith
    have hmL : (3 / 2 + 2 * C_ne) * L ≤ max (3 / 2 + 2 * C_ne) (1 + 2 * C_ζ) * L :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    linarith [show (0 : ℝ) ≤ 1 / (2 * η) from by positivity]
  · have h2t_re : 1 ≤ ((1 : ℂ) + η + 2 * t * I).re := by simp; linarith
    have h2t_ne1 : (1 : ℂ) + η + 2 * t * I ≠ 1 := fun h ↦ by
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    have hch :=
      neg_re_logDeriv_LFunctionTrivChar_le_neg_re_logDeriv_riemannZeta_add q h2t_re h2t_ne1
    have hζ2 := hζ η hη hη1 (2 * t)
    rw [← h2t_eq] at hζ2
    have h4t : η ^ 2 ≤ (2 * t) ^ 2 := by
      have hsq := (sq_le_sq₀ (by positivity) (abs_nonneg t)).mpr ht_big
      rw [div_pow, sq_abs] at hsq
      linarith
    have hpole : η / (η ^ 2 + (2 * t) ^ 2) ≤ 1 / (2 * η) := by
      calc
        η / (η ^ 2 + (2 * t) ^ 2) ≤ η / (2 * η ^ 2) :=
          div_le_div_of_nonneg_left hη.le (by positivity) (by linarith)
        _ = 1 / (2 * η) := by field_simp
    have hζL : C_ζ * Real.log (|2 * t| + 3) ≤ 2 * C_ζ * L := by
      have hm := mul_le_mul_of_nonneg_left hlog2t_le hCζ.le
      linarith
    have hmL : (1 + 2 * C_ζ) * L ≤ max (3 / 2 + 2 * C_ne) (1 + 2 * C_ζ) * L :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
    dsimp only [LFunctionTrivChar] at hch
    rw [hχ2_1]
    linarith

private theorem threeFourOne_contradiction_of_primitive_ne_one {C_prin C_zero C_ne C_ζ K : ℝ}
    (hCp : 0 < C_prin) (hCz : 0 < C_zero) (hCne : 0 < C_ne) (hCζ : 0 < C_ζ)
    (hprin : ∀ (N : ℕ) [NeZero N] {η : ℝ}, 0 < η → η ≤ 1 →
      -(logDeriv (LFunctionTrivChar N) (1 + η)).re ≤ 1 / η + C_prin + Real.log N)
    (hsingle : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ {β u : ℝ}, 0 < β → χ.LFunction (β + u * I) = 0 → ∀ {η : ℝ}, 0 < η → η ≤ 1 →
      -(logDeriv χ.LFunction (1 + η + u * I)).re ≤
        -(1 / (1 + η - β)) + Real.log q / 2 + C_zero * Real.log (|u| + 3))
    (hnonprin : ∀ {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q), ψ ≠ 1 →
      ∀ {η : ℝ}, 0 < η → η ≤ 1 → ∀ u : ℝ,
      -(logDeriv ψ.LFunction (1 + η + u * I)).re ≤
        (3 / 2) * Real.log q + C_ne * Real.log (|u| + 3))
    (hζ : ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ u : ℝ,
      -(logDeriv riemannZeta (1 + η + u * I)).re ≤
        η / (η ^ 2 + u ^ 2) + C_ζ * Real.log (|u| + 3))
    (hK1 : 1 ≤ K)
    (hK1_le : 3 * (C_prin + 1) + 4 * (1 / 2 + C_zero) + max (3 / 2 + 2 * C_ne) (1 + 2 * C_ζ) ≤ K)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    {β t : ℝ} (hβ_pos : 0 < β) (hβ_lt : β < 1) (hzero : χ.LFunction (β + t * I) = 0)
    (hre : 1 - 1 / (160 * K) / Real.log (q * (|t| + 3)) ≤ β)
    (hcase : χ ^ 2 ≠ 1 ∨ (χ ^ 2 = 1 ∧ (1 / (16 * K * Real.log (q * (|t| + 3)))) / 2 ≤ |t|)) :
    False := by
  set L : ℝ := Real.log (q * (|t| + 3))
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
  have hL1 : 1 < L := hlog3.trans_le (Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg t]))
  have hlogq_le : Real.log q ≤ L := Real.log_le_log (by positivity) (by nlinarith [abs_nonneg t])
  have hlogt_le : Real.log (|t| + 3) ≤ L :=
    Real.log_le_log (by positivity) (by nlinarith [abs_nonneg t])
  set η : ℝ := 1 / (16 * K * L)
  have hηpos : 0 < η := by positivity
  have hη1 : η ≤ 1 := div_le_one_of_le₀ (by nlinarith) (by positivity)
  have h341 := χ.threeFourOne_neg_re_logDeriv_LFunction_nonneg (σ := 1 + η) (by linarith) t
  simp only [Complex.ofReal_add, Complex.ofReal_one, Complex.neg_re] at h341
  have hterm1 : -(logDeriv (1 : DirichletCharacter ℂ q).LFunction (1 + η)).re ≤
      1 / η + (C_prin + 1) * L := by
    have h1 := hprin q hηpos hη1
    dsimp only [LFunctionTrivChar] at h1
    have hCpL : C_prin ≤ C_prin * L := le_mul_of_one_le_right hCp.le hL1.le
    linarith
  have htermχ : -(logDeriv χ.LFunction (1 + η + t * I)).re ≤
      -(1 / (1 + η - β)) + (1 / 2 + C_zero) * L := by
    have h0 := hsingle χ hprim hne hβ_pos hzero hηpos hη1
    have hCzL : C_zero * Real.log (|t| + 3) ≤ C_zero * L :=
      mul_le_mul_of_nonneg_left hlogt_le hCz.le
    linarith
  have htermχ2 := neg_re_logDeriv_sq_add_two_mul_le hCne hCζ hnonprin hζ χ hηpos hη1 hcase
  have hKL : (3 * (C_prin + 1) + 4 * (1 / 2 + C_zero) +
      max (3 / 2 + 2 * C_ne) (1 + 2 * C_ζ)) * L ≤ K * L :=
    mul_le_mul_of_nonneg_right hK1_le (by linarith)
  have hKL_eq : K * L = 1 / (16 * η) := by dsimp [η]; field_simp
  have hcomb : 4 / (1 + η - β) ≤ 7 / (2 * η) + 1 / (16 * η) := by
    have h72 : 3 * (1 / η) + 1 / (2 * η) = 7 / (2 * η) := by field_simp; ring
    have h4div : 4 * (1 / (1 + η - β)) = 4 / (1 + η - β) := by ring
    linarith
  have h1β : 1 - β ≤ η / 10 := by
    have hscale : 1 / (160 * K) / L = η / 10 := by dsimp [η]; ring
    linarith
  have hlo : 40 / (11 * η) ≤ 4 / (1 + η - β) := by
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    linarith
  have hcon : 40 / (11 * η) ≤ 57 / (16 * η) := by
    have h57 : 7 / (2 * η) + 1 / (16 * η) = 57 / (16 * η) := by field_simp; ring
    linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hcon
  linarith

private theorem eta_budget_le {C_sum K η₀ : ℝ} {q : ℕ} [NeZero q] (hK1 : 1 ≤ K)
    (hKC : C_sum ≤ K) (hη₀ : η₀ = 1 / (16 * K * Real.log (3 * q)))
    (hsum : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ {S : Finset ℂ}, (∀ ρ ∈ S, 0 < ρ.re) → ∀ {η : ℝ}, 0 < η → η ≤ 1 →
      ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((1 + η : ℂ) - ρ)).re ≤
        1 / η + C_sum * Real.log (3 * q))
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    {S : Finset ℂ} (hS : ∀ ρ ∈ S, 0 < ρ.re) :
    0 < η₀ ∧ η₀ ≤ 1 ∧
      ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((1 + η₀ : ℂ) - ρ)).re ≤
        17 / (16 * η₀) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
  have hlog3q_ge1 : 1 ≤ Real.log (3 * q) :=
    hlog3.le.trans (Real.log_le_log (by norm_num) (by linarith))
  have hlog3q_pos : 0 < Real.log (3 * q) := zero_lt_one.trans_le hlog3q_ge1
  have hη₀_pos : 0 < η₀ := by rw [hη₀]; positivity
  have hη₀_1 : η₀ ≤ 1 := by rw [hη₀]; exact div_le_one_of_le₀ (by nlinarith) (by positivity)
  refine ⟨hη₀_pos, hη₀_1, ?_⟩
  have h0 := hsum χ hprim hne hS hη₀_pos hη₀_1
  have hK2 : C_sum * Real.log (3 * q) ≤ 1 / (16 * η₀) := by
    have hle := mul_le_mul_of_nonneg_right hKC hlog3q_pos.le
    have hEq : K * Real.log (3 * q) = 1 / (16 * η₀) := by rw [hη₀]; field_simp
    linarith
  have h17 : 1 / η₀ + 1 / (16 * η₀) = 17 / (16 * η₀) := by field_simp; ring
  linarith

private theorem re_one_div_sub_ge_of_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hne : χ ≠ 1) {η₀ : ℝ} (hη₀_pos : 0 < η₀) {ρ : ℂ} (hzero : χ.LFunction ρ = 0)
    (hgap : 1 - ρ.re ≤ η₀ / 10) (him : |ρ.im| ≤ η₀ / 2) :
    100 / (146 * η₀) ≤ (1 / ((1 + η₀ : ℂ) - ρ)).re := by
  have hβ_lt : ρ.re < 1 := by
    by_contra h
    exact χ.LFunction_ne_zero_of_one_le_re (.inl hne) (not_lt.mp h) hzero
  have hnum_pos : 0 < 1 + η₀ - ρ.re := by linarith
  have hre : (1 / ((1 + η₀ : ℂ) - ρ)).re =
      (1 + η₀ - ρ.re) / ((1 + η₀ - ρ.re) ^ 2 + ρ.im ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.ofReal_re,
      Complex.sub_im, Complex.add_im, Complex.one_im, Complex.ofReal_im, add_zero, zero_sub,
      ← sq, neg_sq]
  have hden_pos : 0 < (1 + η₀ - ρ.re) ^ 2 + ρ.im ^ 2 := by positivity
  have hden_hi : (1 + η₀ - ρ.re) ^ 2 + ρ.im ^ 2 ≤ (146 / 100) * η₀ ^ 2 := by
    have h1 : (1 + η₀ - ρ.re) ^ 2 ≤ (11 / 10 * η₀) ^ 2 := by nlinarith
    have h2 : ρ.im ^ 2 ≤ (η₀ / 2) ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg ρ.im) (by positivity)).mpr him
    nlinarith
  rw [hre]
  calc
    100 / (146 * η₀) = η₀ / ((146 / 100) * η₀ ^ 2) := by field_simp
    _ ≤ (1 + η₀ - ρ.re) / ((146 / 100) * η₀ ^ 2) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ ≤ (1 + η₀ - ρ.re) / ((1 + η₀ - ρ.re) ^ 2 + ρ.im ^ 2) :=
        div_le_div_of_nonneg_left hnum_pos.le hden_pos hden_hi

private theorem contradiction_of_retained_sum_ge {C_sum K : ℝ} (hK1 : 1 ≤ K) (hKC : C_sum ≤ K)
    (hsum : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ {S : Finset ℂ}, (∀ ρ ∈ S, 0 < ρ.re) → ∀ {η : ℝ}, 0 < η → η ≤ 1 →
      ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((1 + η : ℂ) - ρ)).re ≤
        1 / η + C_sum * Real.log (3 * q))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    {S : Finset ℂ} (hS_pos : ∀ ρ ∈ S, 0 < ρ.re) (hS_zero : ∀ ρ ∈ S, χ.LFunction ρ = 0)
    (hS_gap : ∀ ρ ∈ S, 1 - ρ.re ≤ (1 / (16 * K * Real.log (3 * q))) / 10)
    (hS_im : ∀ ρ ∈ S, |ρ.im| ≤ (1 / (16 * K * Real.log (3 * q))) / 2)
    (hm_sum : 2 ≤ ∑ ρ ∈ S, analyticOrderNatAt χ.LFunction ρ) : False := by
  set η₀ : ℝ := 1 / (16 * K * Real.log (3 * q))
  obtain ⟨hη₀_pos, -, hbudget⟩ := eta_budget_le hK1 hKC (rfl : η₀ = _) hsum χ hprim hne hS_pos
  have hterm (ρ : ℂ) (hρ : ρ ∈ S) :
      (analyticOrderNatAt χ.LFunction ρ : ℝ) * (100 / (146 * η₀)) ≤
        (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((1 + η₀ : ℂ) - ρ)).re :=
    mul_le_mul_of_nonneg_left
      (re_one_div_sub_ge_of_zero hne hη₀_pos (hS_zero ρ hρ) (hS_gap ρ hρ) (hS_im ρ hρ))
      (Nat.cast_nonneg _)
  have hsum_lo : (2 : ℝ) * (100 / (146 * η₀)) ≤
      ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((1 + η₀ : ℂ) - ρ)).re := by
    have hm_real : (2 : ℝ) ≤ ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) := by
      exact_mod_cast hm_sum
    calc
      (2 : ℝ) * (100 / (146 * η₀))
          ≤ (∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ)) * (100 / (146 * η₀)) :=
            mul_le_mul_of_nonneg_right hm_real (by positivity)
      _ = ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (100 / (146 * η₀)) :=
            Finset.sum_mul S _ _
      _ ≤ ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((1 + η₀ : ℂ) - ρ)).re :=
            Finset.sum_le_sum hterm
  have h200 : (2 : ℝ) * (100 / (146 * η₀)) = 200 / (146 * η₀) := by ring
  have hcon : 200 / (146 * η₀) ≤ 17 / (16 * η₀) := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hcon
  linarith

private theorem sq_eq_one_and_abs_im_lt_of_primitive_ne_one {K c₁ : ℝ}
    (hc₁_log : c₁ ≤ Real.log 3 / 2) (hc₁_K : c₁ ≤ 1 / (160 * K))
    (h341 : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ {β t : ℝ}, 0 < β → β < 1 → χ.LFunction (β + t * I) = 0 →
      1 - 1 / (160 * K) / Real.log (q * (|t| + 3)) ≤ β →
      χ ^ 2 ≠ 1 ∨ (χ ^ 2 = 1 ∧ (1 / (16 * K * Real.log (q * (|t| + 3)))) / 2 ≤ |t|) → False)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    {ρ : ℂ} (hre : 1 - c₁ / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re)
    (hord : 0 < meromorphicOrderAt χ.LFunction ρ) :
    χ ^ 2 = 1 ∧ |ρ.im| < (1 / (16 * K * Real.log (q * (|ρ.im| + 3)))) / 2 := by
  have hzero : χ.LFunction ρ = 0 := (χ.pos_meromorphicOrderAt_LFunction_iff hne ρ).mp hord
  have hρpos : 0 < ρ.re := re_pos_of_le_one_sub_div_log hc₁_log ρ hre
  have hβ_lt : ρ.re < 1 := by
    by_contra h
    exact χ.LFunction_ne_zero_of_one_le_re (.inl hne) (not_lt.mp h) hzero
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog_pos : 0 < Real.log (q * (|ρ.im| + 3)) := Real.log_pos (by nlinarith [abs_nonneg ρ.im])
  have hre' : 1 - 1 / (160 * K) / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re := by
    have hc_le : c₁ / Real.log (q * (|ρ.im| + 3)) ≤ 1 / (160 * K) / Real.log (q * (|ρ.im| + 3)) :=
      div_le_div_of_nonneg_right hc₁_K hlog_pos.le
    linarith
  have hzero' : χ.LFunction (ρ.re + ρ.im * I) = 0 := by rwa [Complex.re_add_im]
  have hsq : χ ^ 2 = 1 := by
    by_contra h
    exact h341 χ hprim hne hρpos hβ_lt hzero' hre' (.inl h)
  refine ⟨hsq, ?_⟩
  by_contra h
  exact h341 χ hprim hne hρpos hβ_lt hzero' hre' (.inr ⟨hsq, not_lt.mp h⟩)

private theorem log_three_mul_pos (q : ℕ) [NeZero q] : 0 < Real.log (3 * q) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  exact Real.log_pos (by linarith)

private theorem log_three_mul_le {q : ℕ} [NeZero q] (t : ℝ) :
    Real.log (3 * q) ≤ Real.log (q * (|t| + 3)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  exact Real.log_le_log (by positivity) (by nlinarith [abs_nonneg t])

private theorem gap_le_of_le_one_sub_div_log {K c₁ : ℝ} (hK1 : 1 ≤ K) (hc₁_K : c₁ ≤ 1 / (160 * K))
    {q : ℕ} [NeZero q] {ρ : ℂ} (hre : 1 - c₁ / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re) :
    1 - ρ.re ≤ (1 / (16 * K * Real.log (3 * q))) / 10 := by
  have hlog3q_pos : 0 < Real.log (3 * q) := log_three_mul_pos q
  have hL3 : Real.log (3 * q) ≤ Real.log (q * (|ρ.im| + 3)) := log_three_mul_le ρ.im
  have hc_le : c₁ / Real.log (q * (|ρ.im| + 3)) ≤ 1 / (160 * K) / Real.log (3 * q) :=
    div_le_div₀ (by positivity) hc₁_K hlog3q_pos hL3
  have hscale : 1 / (160 * K) / Real.log (3 * q) = (1 / (16 * K * Real.log (3 * q))) / 10 := by
    ring
  linarith

private theorem real_of_primitive_ne_one {C_sum K c₁ : ℝ} (hK1 : 1 ≤ K) (hKC : C_sum ≤ K)
    (hc₁_log : c₁ ≤ Real.log 3 / 2) (hc₁_K : c₁ ≤ 1 / (160 * K))
    (hsum : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ {S : Finset ℂ}, (∀ ρ ∈ S, 0 < ρ.re) → ∀ {η : ℝ}, 0 < η → η ≤ 1 →
      ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((1 + η : ℂ) - ρ)).re ≤
        1 / η + C_sum * Real.log (3 * q))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    {ρ : ℂ} (hre : 1 - c₁ / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re)
    (hord : 0 < meromorphicOrderAt χ.LFunction ρ) (hsq : χ ^ 2 = 1)
    (ht_lt : |ρ.im| < (1 / (16 * K * Real.log (q * (|ρ.im| + 3)))) / 2) : ρ.im = 0 := by
  by_contra ht0
  have hzero : χ.LFunction ρ = 0 := (χ.pos_meromorphicOrderAt_LFunction_iff hne ρ).mp hord
  have hρpos : 0 < ρ.re := re_pos_of_le_one_sub_div_log hc₁_log ρ hre
  have hlog3q_pos : 0 < Real.log (3 * q) := log_three_mul_pos q
  have hη_le :
      1 / (16 * K * Real.log (q * (|ρ.im| + 3))) ≤ 1 / (16 * K * Real.log (3 * q)) :=
    div_le_div_of_nonneg_left zero_le_one (by positivity)
      (mul_le_mul_of_nonneg_left (log_three_mul_le ρ.im) (by positivity))
  have hgap : 1 - ρ.re ≤ (1 / (16 * K * Real.log (3 * q))) / 10 :=
    gap_le_of_le_one_sub_div_log hK1 hc₁_K hre
  have him_le : |ρ.im| ≤ (1 / (16 * K * Real.log (3 * q))) / 2 := ht_lt.le.trans (by linarith)
  have hconj_zero : χ.LFunction (star ρ) = 0 :=
    (LFunction_conj_eq_zero_iff_of_isQuadratic (MulChar.isQuadratic_iff_sq_eq_one.mpr hsq) ρ).mpr
      hzero
  have hne_conj : ρ ≠ star ρ := fun h ↦ by
    have him := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at him
    exact ht0 (by linarith)
  have hm₁ := (χ.LFunction_eq_zero_iff_one_le_analyticOrderNatAt hne ρ).mp hzero
  have hm₂ := (χ.LFunction_eq_zero_iff_one_le_analyticOrderNatAt hne (star ρ)).mp hconj_zero
  refine contradiction_of_retained_sum_ge hK1 hKC hsum χ hprim hne (S := {ρ, star ρ})
    (fun z hz ↦ by
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hρpos
      · rw [Finset.mem_singleton.mp hz]; simpa [Complex.star_def] using hρpos)
    (fun z hz ↦ by
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hzero
      · rw [Finset.mem_singleton.mp hz]; exact hconj_zero)
    (fun z hz ↦ by
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hgap
      · rw [Finset.mem_singleton.mp hz]; simpa [Complex.star_def] using hgap)
    (fun z hz ↦ by
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact him_le
      · rw [Finset.mem_singleton.mp hz]; simpa [Complex.star_def] using him_le) ?_
  rw [Finset.sum_pair hne_conj]
  omega

private theorem simple_and_unique_of_real_sq {C_sum K c₁ : ℝ} (hK1 : 1 ≤ K) (hKC : C_sum ≤ K)
    (hc₁_log : c₁ ≤ Real.log 3 / 2) (hc₁_K : c₁ ≤ 1 / (160 * K))
    (hsum : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ {S : Finset ℂ}, (∀ ρ ∈ S, 0 < ρ.re) → ∀ {η : ℝ}, 0 < η → η ≤ 1 →
      ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((1 + η : ℂ) - ρ)).re ≤
        1 / η + C_sum * Real.log (3 * q))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hreal_sq : ∀ {ρ : ℂ}, 1 - c₁ / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re →
      0 < meromorphicOrderAt χ.LFunction ρ → ρ.im = 0 ∧ χ ^ 2 = 1) :
    (∀ ρ : ℂ, 1 - c₁ / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re →
      0 < meromorphicOrderAt χ.LFunction ρ →
      ρ.im = 0 ∧ χ ^ 2 = 1 ∧ meromorphicOrderAt χ.LFunction ρ = 1) ∧
    ∀ ρ₁ ρ₂ : ℂ, 1 - c₁ / Real.log (q * (|ρ₁.im| + 3)) ≤ ρ₁.re →
      1 - c₁ / Real.log (q * (|ρ₂.im| + 3)) ≤ ρ₂.re →
      0 < meromorphicOrderAt χ.LFunction ρ₁ →
      0 < meromorphicOrderAt χ.LFunction ρ₂ → ρ₁ = ρ₂ := by
  have hlog3q_pos : 0 < Real.log (3 * q) := log_three_mul_pos q
  refine ⟨fun ρ hre hord ↦ ?_, fun ρ₁ ρ₂ hre₁ hre₂ hord₁ hord₂ ↦ ?_⟩
  · obtain ⟨him, hsq⟩ := hreal_sq hre hord
    refine ⟨him, hsq, ?_⟩
    rw [χ.meromorphicOrderAt_LFunction_eq_one_iff hne ρ]
    by_contra hm_ne
    have hzero := (χ.pos_meromorphicOrderAt_LFunction_iff hne ρ).mp hord
    have hm1 := (χ.LFunction_eq_zero_iff_one_le_analyticOrderNatAt hne ρ).mp hzero
    refine contradiction_of_retained_sum_ge hK1 hKC hsum χ hprim hne (S := {ρ})
      (fun z hz ↦ by
        rw [Finset.mem_singleton.mp hz]; exact re_pos_of_le_one_sub_div_log hc₁_log ρ hre)
      (fun z hz ↦ by rw [Finset.mem_singleton.mp hz]; exact hzero)
      (fun z hz ↦ by
        rw [Finset.mem_singleton.mp hz]; exact gap_le_of_le_one_sub_div_log hK1 hc₁_K hre)
      (fun z hz ↦ by rw [Finset.mem_singleton.mp hz, him, abs_zero]; positivity) ?_
    rw [Finset.sum_singleton]
    omega
  · by_contra hne12
    obtain ⟨him₁, -⟩ := hreal_sq hre₁ hord₁
    obtain ⟨him₂, -⟩ := hreal_sq hre₂ hord₂
    have hzero₁ := (χ.pos_meromorphicOrderAt_LFunction_iff hne ρ₁).mp hord₁
    have hzero₂ := (χ.pos_meromorphicOrderAt_LFunction_iff hne ρ₂).mp hord₂
    have hm₁ := (χ.LFunction_eq_zero_iff_one_le_analyticOrderNatAt hne ρ₁).mp hzero₁
    have hm₂ := (χ.LFunction_eq_zero_iff_one_le_analyticOrderNatAt hne ρ₂).mp hzero₂
    refine contradiction_of_retained_sum_ge hK1 hKC hsum χ hprim hne (S := {ρ₁, ρ₂})
      (fun z hz ↦ by
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact re_pos_of_le_one_sub_div_log hc₁_log z hre₁
        · rw [Finset.mem_singleton.mp hz]; exact re_pos_of_le_one_sub_div_log hc₁_log _ hre₂)
      (fun z hz ↦ by
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hzero₁
        · rw [Finset.mem_singleton.mp hz]; exact hzero₂)
      (fun z hz ↦ by
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact gap_le_of_le_one_sub_div_log hK1 hc₁_K hre₁
        · rw [Finset.mem_singleton.mp hz]; exact gap_le_of_le_one_sub_div_log hK1 hc₁_K hre₂)
      (fun z hz ↦ by
        rcases Finset.mem_insert.mp hz with rfl | hz
        · rw [him₁, abs_zero]; positivity
        · rw [Finset.mem_singleton.mp hz, him₂, abs_zero]; positivity) ?_
    rw [Finset.sum_pair hne12]
    omega

private theorem primitive_nonprincipal_zeroFreeRegion :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ Real.log 3 / 2 ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
        (∀ ρ : ℂ, 1 - c₁ / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re →
          0 < meromorphicOrderAt χ.LFunction ρ →
          ρ.im = 0 ∧ χ ^ 2 = 1 ∧ meromorphicOrderAt χ.LFunction ρ = 1) ∧
        ∀ ρ₁ ρ₂ : ℂ, 1 - c₁ / Real.log (q * (|ρ₁.im| + 3)) ≤ ρ₁.re →
          1 - c₁ / Real.log (q * (|ρ₂.im| + 3)) ≤ ρ₂.re →
          0 < meromorphicOrderAt χ.LFunction ρ₁ →
          0 < meromorphicOrderAt χ.LFunction ρ₂ → ρ₁ = ρ₂ := by
  obtain ⟨C_prin, hCp, hprin⟩ := exists_neg_re_logDeriv_LFunctionTrivChar_one_add_le
  obtain ⟨C_zero, hCz, hsingle⟩ := exists_neg_re_logDeriv_LFunction_one_add_zero_le
  obtain ⟨C_ne, hCne, hnonprin⟩ := exists_neg_re_logDeriv_LFunction_one_add_le_of_ne_one
  obtain ⟨C_ζ, hCζ, hζ_raw⟩ := exists_neg_re_logDeriv_riemannZeta_one_add_mul_I_le
  obtain ⟨C_sum, _, hsum⟩ := exists_sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le
  let K₁ : ℝ := 3 * (C_prin + 1) + 4 * (1 / 2 + C_zero) + max (3 / 2 + 2 * C_ne) (1 + 2 * C_ζ)
  let K : ℝ := max 1 (max K₁ C_sum)
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK1_le : K₁ ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKC : C_sum ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  let c₁ : ℝ := min (Real.log 3 / 2) (1 / (160 * K))
  have hc₁_pos : 0 < c₁ := lt_min (half_pos (Real.log_pos (by norm_num))) (by positivity)
  have hc₁_log : c₁ ≤ Real.log 3 / 2 := min_le_left _ _
  have hc₁_K : c₁ ≤ 1 / (160 * K) := min_le_right _ _
  have h341 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
      {β t : ℝ} (hb0 : 0 < β) (hb1 : β < 1) (hz : χ.LFunction (β + t * I) = 0)
      (hre : 1 - 1 / (160 * K) / Real.log (q * (|t| + 3)) ≤ β)
      (hcase : χ ^ 2 ≠ 1 ∨ (χ ^ 2 = 1 ∧ (1 / (16 * K * Real.log (q * (|t| + 3)))) / 2 ≤ |t|)) :
      False :=
    threeFourOne_contradiction_of_primitive_ne_one hCp hCz hCne hCζ hprin hsingle hnonprin
      (fun η hη hη1 u ↦ (hζ_raw η hη hη1 u).1) hK1 hK1_le χ hp hn hb0 hb1 hz hre hcase
  refine ⟨c₁, hc₁_pos, hc₁_log, fun q _ χ hprim hne ↦ ?_⟩
  refine simple_and_unique_of_real_sq hK1 hKC hc₁_log hc₁_K hsum χ hprim hne fun {ρ} hre hord ↦ ?_
  obtain ⟨hsq, ht_lt⟩ :=
    sq_eq_one_and_abs_im_lt_of_primitive_ne_one hc₁_log hc₁_K h341 χ hprim hne hre hord
  exact ⟨real_of_primitive_ne_one hK1 hKC hc₁_log hc₁_K hsum χ hprim hne hre hord hsq ht_lt, hsq⟩

private theorem principal_meromorphicOrderAt_not_pos {c c_ζ : ℝ} (hc_ζ : 0 < c_ζ)
    (hc_le_ζ : c ≤ c_ζ) (hc_log : c ≤ Real.log 3 / 2)
    (hζ_zfr : ∀ s : ℂ, 1 - c_ζ / Real.log (|s.im| + 3) ≤ s.re → riemannZeta s ≠ 0)
    (q : ℕ) [NeZero q] (ρ : ℂ) (hre : 1 - c / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re)
    (hord : 0 < meromorphicOrderAt (1 : DirichletCharacter ℂ q).LFunction ρ) : False := by
  rcases eq_or_ne ρ 1 with rfl | hρ1
  · rw [meromorphicOrderAt_LFunction_one_at_one q] at hord
    exact absurd hord (by decide)
  · have hpos := re_pos_of_le_one_sub_div_log hc_log ρ hre
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    rw [← changeLevel_one (q.one_dvd),
      meromorphicOrderAt_LFunction_changeLevel (1 : DirichletCharacter ℂ 1) q.one_dvd hpos,
      LFunction_modOne_eq, (analyticOn_riemannZeta ρ hρ1).meromorphicOrderAt_eq] at hord
    have hζ0 : riemannZeta ρ = 0 := by
      by_contra hne
      rw [(analyticOn_riemannZeta ρ hρ1).analyticOrderAt_eq_zero.mpr hne] at hord
      simp at hord
    have hlog_ge : Real.log (|ρ.im| + 3) ≤ Real.log (q * (|ρ.im| + 3)) :=
      Real.log_le_log (by linarith [abs_nonneg ρ.im]) (by nlinarith [abs_nonneg ρ.im])
    have hc_le : c / Real.log (q * (|ρ.im| + 3)) ≤ c_ζ / Real.log (|ρ.im| + 3) :=
      div_le_div₀ hc_ζ.le hc_le_ζ (Real.log_pos (by linarith [abs_nonneg ρ.im])) hlog_ge
    exact hζ_zfr ρ (by linarith) hζ0

/-- **The de la Vallée Poussin zero-free region for Dirichlet L-functions.** There is one absolute
constant `c`, with `0 < c ≤ log 3 / 2`, such that for every modulus `q ≥ 1` and every Dirichlet
character `χ` modulo `q`, primitive or not, a zero `ρ` of `L(·, χ)` with
`Re ρ ≥ 1 − c / log (q (|Im ρ| + 3))` is real, simple, and occurs only for a real character
(`χ² = 1`), and there is at most one such zero (Davenport §14). -/
theorem dirichletLFunction_zeroFreeRegion :
    ∃ c : ℝ, 0 < c ∧ c ≤ Real.log 3 / 2 ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (∀ ρ : ℂ, 1 - c / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re →
          0 < meromorphicOrderAt (DirichletCharacter.LFunction χ) ρ →
          ρ.im = 0 ∧ χ ^ 2 = 1 ∧ meromorphicOrderAt (DirichletCharacter.LFunction χ) ρ = 1) ∧
        ∀ ρ₁ ρ₂ : ℂ, 1 - c / Real.log (q * (|ρ₁.im| + 3)) ≤ ρ₁.re →
          1 - c / Real.log (q * (|ρ₂.im| + 3)) ≤ ρ₂.re →
          0 < meromorphicOrderAt (DirichletCharacter.LFunction χ) ρ₁ →
          0 < meromorphicOrderAt (DirichletCharacter.LFunction χ) ρ₂ → ρ₁ = ρ₂ := by
  obtain ⟨c_ζ, hc_ζ, hζ_zfr⟩ := riemannZeta_zeroFreeRegion
  obtain ⟨c₁, hc₁, hc₁_log, hprim_zfr⟩ := primitive_nonprincipal_zeroFreeRegion
  let c : ℝ := min c_ζ c₁
  have hc_pos : 0 < c := lt_min hc_ζ hc₁
  have hc_log : c ≤ Real.log 3 / 2 := (min_le_right _ _).trans hc₁_log
  refine ⟨c, hc_pos, hc_log, fun q _ χ ↦ ?_⟩
  by_cases hχ1 : χ = 1
  · subst hχ1
    have no_zero := principal_meromorphicOrderAt_not_pos hc_ζ (min_le_left _ _) hc_log hζ_zfr q
    exact ⟨fun ρ hre hord ↦ (no_zero ρ hre hord).elim,
      fun ρ₁ _ hre₁ _ hord₁ _ ↦ (no_zero ρ₁ hre₁ hord₁).elim⟩
  · let q₀ : ℕ := χ.conductor
    have : NeZero q₀ := ⟨Nat.ne_of_gt (Nat.pos_of_dvd_of_pos χ.conductor_dvd_level (NeZero.pos q))⟩
    let χ₀ : DirichletCharacter ℂ q₀ := χ.primitiveCharacter
    have hχ₀_ne : χ₀ ≠ 1 := mt χ.primitiveCharacter_eq_one_iff.mp hχ1
    obtain ⟨hsingle, huniq⟩ := hprim_zfr q₀ χ₀ χ.primitiveCharacter_isPrimitive hχ₀_ne
    have htransfer (ρ : ℂ) (hre : 1 - c / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re) :
        1 - c₁ / Real.log (q₀ * (|ρ.im| + 3)) ≤ ρ.re ∧
          meromorphicOrderAt χ.LFunction ρ = meromorphicOrderAt χ₀.LFunction ρ := by
      have hpos := re_pos_of_le_one_sub_div_log hc_log ρ hre
      have hq₀ : (q₀ : ℝ) ≤ q := by
        exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
      have hq₀1 : (1 : ℝ) ≤ q₀ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₀)
      have hlog_ge : Real.log (q₀ * (|ρ.im| + 3)) ≤ Real.log (q * (|ρ.im| + 3)) :=
        Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right hq₀ (by positivity))
      have hc_le : c / Real.log (q * (|ρ.im| + 3)) ≤ c₁ / Real.log (q₀ * (|ρ.im| + 3)) :=
        div_le_div₀ hc₁.le (min_le_right _ _) (Real.log_pos (by nlinarith [abs_nonneg ρ.im]))
          hlog_ge
      rw [← χ.changeLevel_primitiveCharacter]
      exact ⟨by linarith, meromorphicOrderAt_LFunction_changeLevel χ₀ χ.conductor_dvd_level hpos⟩
    refine ⟨fun ρ hre hord ↦ ?_, fun ρ₁ ρ₂ hre₁ hre₂ hord₁ hord₂ ↦ ?_⟩
    · obtain ⟨hre', hord_eq⟩ := htransfer ρ hre
      rw [hord_eq] at hord ⊢
      obtain ⟨him, hsq, h1⟩ := hsingle ρ hre' hord
      exact ⟨him, by rw [← χ.changeLevel_primitiveCharacter, ← map_pow, hsq, map_one], h1⟩
    · obtain ⟨hre₁', hord_eq₁⟩ := htransfer ρ₁ hre₁
      obtain ⟨hre₂', hord_eq₂⟩ := htransfer ρ₂ hre₂
      rw [hord_eq₁] at hord₁
      rw [hord_eq₂] at hord₂
      exact huniq ρ₁ ρ₂ hre₁' hre₂' hord₁ hord₂

end TauCeti
