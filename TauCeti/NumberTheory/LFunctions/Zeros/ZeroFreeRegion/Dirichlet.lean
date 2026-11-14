/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.MulChar.Basic
import TauCeti.Analysis.Complex.LocalLogDeriv
import TauCeti.Analysis.Meromorphic.Divisor
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Conjugate
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv
import TauCeti.NumberTheory.LFunctions.Zeros.ZeroFreeRegion.RiemannZeta
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta
import TauCeti.NumberTheory.LSeries.DirichletEulerLog
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDerivNearOne

/-!
# The classical zero-free region for Dirichlet L-functions

For a modulus `q ≥ 1` and a Dirichlet character `χ` modulo `q`, de la Vallée Poussin's method
combined with Landau's local logarithmic-derivative bound shows that `L(s, χ)` has no zeros in a
region `Re s ≥ 1 - c / log (q (|Im s| + 3))`, with at most one exception: when `χ` is real
(`χ ^ 2 = 1`), there may be at most one zero in the region, and any such zero is real and simple.

Zeros are formulated via `0 < meromorphicOrderAt χ.LFunction ρ`, which excludes the simple pole of
the principal character at `s = 1` without a separate side condition and transfers cleanly from the
level-one character (`riemannZeta`) to any principal character modulo `q` on `Re s > 0`. Taking
`c ≤ log 3 / 2` places the entire region inside `Re s ≥ 1 / 2`.

For nonprincipal `χ`, partial summation bounds `‖L(w, χ)‖` by `O(q (|t| + 3))` on the disc of
radius `1 / 2` centred at `9 / 8 + i t`, so Landau's lemma bounds `-Re (L′/L)` up to
`O(log (q (|t| + 3)))` while retaining nearby zeros with positive weight (and the Dirichlet series
at `9 / 8` extends the zero-free bound across `Re s > 9 / 8`):
* When `χ ^ 2 ≠ 1`, or when `χ ^ 2 = 1` and `|Im ρ| ≥ 6 (1 - Re ρ)`, the `3–4–1` inequality at
  `σ = 1 + 4 (1 - Re ρ)` rules out any zero in the region (using the `(4 |γ|)⁻¹` bound for the
  pole of `L′/L(σ + 2 i γ, 1_q)` when `χ ^ 2 = 1`).
* When `χ ^ 2 = 1` and `0 < |Im ρ| < 6 (1 - Re ρ)`, conjugate symmetry gives a distinct zero
  `conj ρ`, and retaining the pair `{ρ, conj ρ}` in `-Re (ζ′/ζ(σ) + L′/L(σ, χ)) ≥ 0` at
  `σ = 1 + 12 (1 - Re ρ)` outweighs the pole `1 / (σ - 1)`.
* Bounding the sum of divisor multiplicities over any finite set of real zeros in the region by `1`
  via the same `1 + χ` inequality yields both simplicity and uniqueness of the possible Siegel zero.

## Main results

* `TauCeti.LFunctions.exists_neg_re_logDeriv_LFunction_le`:
  `-Re (L′/L(s, χ)) ≪ log (q (|Im s| + 3))` uniformly for nonprincipal `χ` modulo `q` and
  `1 < Re s`.
* `TauCeti.LFunctions.dirichletLFunction_zeroFreeRegion`: the classical zero-free region for
  `DirichletCharacter.LFunction`, including reality, simplicity, and uniqueness of the possible
  Siegel zero when `χ ^ 2 = 1`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §14.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Theorem 11.3.
-/

public section

open Complex DirichletCharacter Metric Set
open scoped ComplexConjugate

namespace TauCeti.LFunctions

private theorem norm_LFunction_on_closedBall {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {t : ℝ} {w : ℂ} (hw : w ∈ closedBall ((9 / 8 : ℝ) + t * I) (1 / 2)) :
    5 / 8 ≤ w.re ∧ ‖χ.LFunction w‖ ≤ 2 * ((q : ℝ) * (|t| + 3)) := by
  set z₀ : ℂ := (9 / 8 : ℝ) + t * I
  have hw_norm : ‖w - z₀‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using hw
  have hre_diff : |(w - z₀).re| ≤ 1 / 2 := (abs_re_le_norm _).trans hw_norm
  have hw_re : 5 / 8 ≤ w.re := by
    have hz₀_re : z₀.re = 9 / 8 := by simp [z₀]
    rw [sub_re, hz₀_re] at hre_diff
    linarith [(abs_le.mp hre_diff).1]
  have hwn : ‖w‖ ≤ |t| + 3 := by
    have hz₀n : ‖z₀‖ ≤ 9 / 8 + |t| :=
      (norm_add_le _ _).trans (by norm_num [norm_mul, norm_real])
    calc ‖w‖ = ‖w - z₀ + z₀‖ := by ring_nf
      _ ≤ ‖w - z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ ≤ 1 / 2 + (9 / 8 + |t|) := add_le_add hw_norm hz₀n
      _ ≤ |t| + 3 := by linarith
  refine ⟨hw_re, ?_⟩
  calc ‖χ.LFunction w‖ ≤ (q : ℝ) * ‖w‖ / w.re :=
      χ.norm_LFunction_le_level_mul_norm_div_re hχ (by linarith)
    _ ≤ (q : ℝ) * (|t| + 3) / (5 / 8) := by gcongr
    _ ≤ 2 * ((q : ℝ) * (|t| + 3)) := by
      have hq0 : 0 ≤ (q : ℝ) * (|t| + 3) := by positivity
      linarith

private theorem exists_neg_re_logDeriv_LFunction_add_sum_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {σ t : ℝ}, 1 < σ → σ ≤ 9 / 8 → ∀ S : Finset ℂ,
        -(logDeriv χ.LFunction (σ + t * I)).re +
            ∑ ρ ∈ S, (MeromorphicOn.divisor χ.LFunction
              (closedBall ((9 / 8 : ℝ) + t * I) ((1 / 2 : ℝ) / 2)) ρ : ℝ) *
              ((((σ : ℂ) + t * I) - ρ)⁻¹).re ≤
          A * Real.log (q * (|t| + 3)) := by
  obtain ⟨A, hA, hLandau⟩ := TauCeti.exists_neg_re_logDeriv_add_sum_divisor_half_le
    (σ₀ := 9 / 8) (σ₁ := 1) (R := 1 / 2) (b := Real.exp (-(riemannZeta (9 / 8 : ℝ)).re))
    (c := 2) (K₀ := 3) (by norm_num) (Real.exp_pos _) (by norm_num)
  refine ⟨A, hA, fun {q} _ χ hχ {σ t} hσ1 hσ2 S ↦ ?_⟩
  have hf : AnalyticOnNhd ℂ χ.LFunction (closedBall ((9 / 8 : ℝ) + t * I) (1 / 2)) :=
    fun z _ ↦ (differentiable_LFunction hχ).analyticAt z
  have hb₀ : Real.exp (-(riemannZeta (9 / 8 : ℝ)).re) ≤ ‖χ.LFunction ((9 / 8 : ℝ) + t * I)‖ := by
    simpa using χ.exp_neg_re_riemannZeta_le_norm_LFunction
      (s := (9 / 8 : ℝ) + t * I) (by simp; norm_num)
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  exact hLandau hf hb₀
    (fun w hw ↦ (norm_LFunction_on_closedBall hχ (sphere_subset_closedBall hw)).2)
    (fun _ _ hw ↦ LFunction_ne_zero_of_one_le_re χ (.inl hχ) hw) hσ1
    (abs_le.mpr ⟨by linarith, by linarith⟩) (by nlinarith [abs_nonneg t]) S

/-- **Upper bound for `-Re (L′/L)` of a nonprincipal character across `1 < Re s`.** There is an
absolute constant `A > 0` such that
`-(logDeriv χ.LFunction s).re ≤ A * Real.log (q * (|s.im| + 3))` for every modulus `q ≥ 1`, every
`χ ≠ 1` modulo `q`, and every `s : ℂ` with `1 < s.re`. -/
theorem exists_neg_re_logDeriv_LFunction_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {s : ℂ}, 1 < s.re →
        -(logDeriv χ.LFunction s).re ≤ A * Real.log (q * (|s.im| + 3)) := by
  obtain ⟨A₀, hA₀, h⟩ := exists_neg_re_logDeriv_LFunction_add_sum_le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set C₉ : ℝ := max 0 (-(logDeriv riemannZeta (9 / 8 : ℝ)).re)
  set A : ℝ := max A₀ (C₉ / Real.log 3)
  refine ⟨A, lt_max_of_lt_left hA₀, fun {q} _ χ hχ {s} hs ↦ ?_⟩
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  have hL_ge : Real.log 3 ≤ Real.log (q * (|s.im| + 3)) :=
    Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg s.im])
  have hL_pos : 0 < Real.log (q * (|s.im| + 3)) := hlog3.trans_le hL_ge
  rcases le_or_gt s.re (9 / 8) with hs9 | hs9
  · have h0 := h χ hχ (t := s.im) hs hs9 ∅
    rw [Finset.sum_empty, add_zero, re_add_im s] at h0
    exact h0.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hL_pos.le)
  · have hnorm : -(logDeriv χ.LFunction s).re ≤ C₉ :=
      ((neg_le_abs _).trans ((abs_re_le_norm _).trans
        (χ.norm_logDeriv_LFunction_le_of_le_re (σ := 9 / 8) (by norm_num) hs9.le))).trans
        (le_max_right _ _)
    calc -(logDeriv χ.LFunction s).re ≤ C₉ := hnorm
      _ = C₉ / Real.log 3 * Real.log 3 := (div_mul_cancel₀ _ hlog3.ne').symm
      _ ≤ A * Real.log (q * (|s.im| + 3)) :=
        mul_le_mul (le_max_right _ _) hL_ge hlog3.le (hA₀.le.trans (le_max_left _ _))

private theorem coe_divisor_LFunction_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t : ℝ) {ρ : ℂ}
    (hρ : ρ ∈ closedBall ((9 / 8 : ℝ) + t * I) ((1 / 2 : ℝ) / 2)) :
    (MeromorphicOn.divisor χ.LFunction
      (closedBall ((9 / 8 : ℝ) + t * I) ((1 / 2 : ℝ) / 2)) ρ : WithTop ℤ) =
      meromorphicOrderAt χ.LFunction ρ :=
  AnalyticOnNhd.coe_divisor_eq_meromorphicOrderAt
    (fun z _ ↦ (differentiable_LFunction hχ).analyticAt z) (convex_closedBall _ _).isPreconnected
    ⟨(9 / 8 : ℝ) + t * I, mem_closedBall_self (by norm_num),
      LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simp; norm_num)⟩ hρ

private theorem one_le_divisor_LFunction_of_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t : ℝ) {ρ : ℂ}
    (hρ : ρ ∈ closedBall ((9 / 8 : ℝ) + t * I) ((1 / 2 : ℝ) / 2)) (hL0 : χ.LFunction ρ = 0) :
    1 ≤ MeromorphicOn.divisor χ.LFunction
      (closedBall ((9 / 8 : ℝ) + t * I) ((1 / 2 : ℝ) / 2)) ρ :=
  Int.add_one_le_iff.2 <|
    (AnalyticOnNhd.zero_lt_divisor_iff
      (fun z _ ↦ (differentiable_LFunction hχ).analyticAt z)
      (convex_closedBall _ _).isPreconnected
      ⟨(9 / 8 : ℝ) + t * I, mem_closedBall_self (by norm_num),
        LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simp; norm_num)⟩ hρ).2 hL0

private theorem mem_closedBall_of_seven_div_eight_le_re {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {ρ : ℂ} (h7 : 7 / 8 ≤ ρ.re)
    (hL0 : χ.LFunction ρ = 0) :
    ρ ∈ closedBall ((9 / 8 : ℝ) + ρ.im * I) ((1 / 2 : ℝ) / 2) := by
  have hlt1 : ρ.re < 1 :=
    by_contra fun h ↦ LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hL0
  rw [mem_closedBall, dist_eq_norm,
    show ρ - ((9 / 8 : ℝ) + ρ.im * I) = ((ρ.re - 9 / 8 : ℝ) : ℂ) from
      Complex.ext (by simp) (by simp),
    norm_real, Real.norm_eq_abs, abs_le]
  exact ⟨by linarith, by linarith⟩

private theorem le_div_log_three_mul {C L : ℝ} (hC : 0 ≤ C) (hL : Real.log 3 ≤ L) :
    C ≤ C / Real.log 3 * L := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  exact (div_mul_cancel₀ C hlog3.ne').symm.trans_le
    (mul_le_mul_of_nonneg_left hL (div_nonneg hC hlog3.le))

private theorem exists_neg_re_logDeriv_sq_two_mul_le :
    ∃ B : ℝ, 0 < B ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ γ δ : ℝ},
      1 < σ → 0 < δ → (χ ^ 2 ≠ 1 ∨ 6 * δ ≤ |γ|) →
        -(logDeriv (χ ^ 2).LFunction (σ + 2 * γ * I)).re ≤
          (24 * δ)⁻¹ + B * Real.log (q * (|γ| + 3)) := by
  obtain ⟨A, hA, hLandau⟩ := exists_neg_re_logDeriv_LFunction_le
  obtain ⟨B₀, hB₀, hζ⟩ := exists_neg_re_logDeriv_riemannZeta_le_of_im_ne_zero
  refine ⟨2 * A + 2 * B₀ + 1, by positivity, fun {q} _ χ {σ γ δ} hσ1 hδ0 hcase ↦ ?_⟩
  set s : ℂ := σ + 2 * γ * I
  set L : ℝ := Real.log (q * (|γ| + 3))
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  have hL_pos : 0 < L :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 3)).trans_le
      (Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg γ]))
  have hs_re : s.re = σ := by simp [s]
  have hs_im : s.im = 2 * γ := by simp [s]
  have hlog2 : Real.log (q * (|2 * γ| + 3)) ≤ 2 * L := by
    calc Real.log (q * (|2 * γ| + 3)) ≤ Real.log ((q * (|γ| + 3)) ^ 2) :=
        Real.log_le_log (by positivity) (by
          have hsq : |2 * γ| + 3 ≤ (|γ| + 3) ^ 2 := by
            rw [abs_mul]; norm_num; nlinarith [abs_nonneg γ]
          calc (q : ℝ) * (|2 * γ| + 3) ≤ (q : ℝ) * (|γ| + 3) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
            _ ≤ (q : ℝ) ^ 2 * (|γ| + 3) ^ 2 :=
              mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
            _ = ((q : ℝ) * (|γ| + 3)) ^ 2 := (mul_pow _ _ _).symm)
      _ = 2 * L := by rw [Real.log_pow]; push_cast; rfl
  rcases eq_or_ne (χ ^ 2) 1 with hsq1 | hsq_ne
  · have hγ6 : 6 * δ ≤ |γ| := hcase.resolve_left (not_not.2 hsq1)
    have hγ_ne : γ ≠ 0 := fun h0 ↦ by simp [h0] at hγ6; linarith
    have htriv : -(logDeriv (1 : DirichletCharacter ℂ q).LFunction s -
        logDeriv riemannZeta s).re ≤ Real.log q :=
      (neg_le_abs _).trans <| (abs_re_le_norm _).trans <|
        norm_logDeriv_LFunctionTrivChar_sub_logDeriv_riemannZeta_le (N := q) (s := s)
          (by linarith)
    have hlogq : Real.log q ≤ L := Real.log_le_log (by positivity) (by nlinarith [abs_nonneg γ])
    have hζs := hζ (s := s) (by linarith) (by rw [hs_im]; exact mul_ne_zero two_ne_zero hγ_ne)
    have him2 : (2 * |s.im|)⁻¹ ≤ (24 * δ)⁻¹ := by
      rw [hs_im, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact inv_anti₀ (by positivity) (by linarith)
    have hlog_ζ : Real.log (|s.im| + 3) ≤ 2 * L :=
      (Real.log_le_log (by positivity) (by rw [hs_im]; nlinarith [abs_nonneg (2 * γ)])).trans hlog2
    rw [hsq1]
    rw [sub_re] at htriv
    nlinarith [mul_nonneg hA.le hL_pos.le]
  · have h2 := hLandau (χ ^ 2) hsq_ne (s := s) (by linarith)
    rw [hs_im] at h2
    have hinv0 : 0 ≤ (24 * δ)⁻¹ := by positivity
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * B₀ + 1) hL_pos.le]

private theorem exists_neg_re_logDeriv_LFunction_retained :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {σ : ℝ} {ρ : ℂ}, 1 < σ → σ ≤ 9 / 8 → 7 / 8 ≤ ρ.re → χ.LFunction ρ = 0 →
        -(logDeriv χ.LFunction (σ + ρ.im * I)).re + (σ - ρ.re)⁻¹ ≤
          A * Real.log (q * (|ρ.im| + 3)) := by
  obtain ⟨A, hA, hLandau⟩ := exists_neg_re_logDeriv_LFunction_add_sum_le
  refine ⟨A, hA, fun {q} _ χ hχ {σ ρ} hσ1 hσ2 h7 hL0 ↦ ?_⟩
  have hρ_lt1 : ρ.re < 1 :=
    by_contra fun h ↦ LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hL0
  have hρ_mem := mem_closedBall_of_seven_div_eight_le_re hχ h7 hL0
  have h1 := hLandau χ hχ (σ := σ) (t := ρ.im) hσ1 hσ2 {ρ}
  have hD : (1 : ℝ) ≤ (MeromorphicOn.divisor χ.LFunction
      (closedBall ((9 / 8 : ℝ) + ρ.im * I) ((1 / 2 : ℝ) / 2)) ρ : ℝ) :=
    mod_cast one_le_divisor_LFunction_of_eq_zero hχ ρ.im hρ_mem hL0
  have hdiff : (σ : ℂ) + ρ.im * I - ρ = ((σ - ρ.re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp)
  rw [Finset.sum_singleton, hdiff, ← ofReal_inv, ofReal_re] at h1
  linarith [le_mul_of_one_le_left (inv_nonneg.2 (by linarith : (0 : ℝ) ≤ σ - ρ.re)) hD]

private theorem exists_not_pos_meromorphicOrderAt_of_sq_ne_one_or_im_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ ρ : ℂ, (χ ^ 2 ≠ 1 ∨ 6 * (1 - ρ.re) ≤ |ρ.im|) →
        1 - c / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re →
        ¬ 0 < meromorphicOrderAt χ.LFunction ρ := by
  obtain ⟨A, hA, hret⟩ := exists_neg_re_logDeriv_LFunction_retained
  obtain ⟨C₁, hC₁0, hpole0⟩ := TauCeti.exists_neg_re_logDeriv_riemannZeta_one_add_le
  obtain ⟨B₂, hB₂, hsq2⟩ := exists_neg_re_logDeriv_sq_two_mul_le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set M : ℝ := 3 * C₁ / Real.log 3 + 4 * A + B₂
  have hM : 0 < M := by positivity
  set c : ℝ := min (1 / 32 * Real.log 3) (1 / (240 * M))
  refine ⟨c, by positivity, fun {q} _ χ hχ ρ hcase hρre hord ↦ ?_⟩
  have hL0 : χ.LFunction ρ = 0 := (χ.meromorphicOrderAt_LFunction_pos_iff.1 hord).1
  have hρ_lt1 : ρ.re < 1 :=
    by_contra fun h ↦ LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hL0
  set γ : ℝ := ρ.im
  set δ : ℝ := 1 - ρ.re
  set L : ℝ := Real.log (q * (|γ| + 3))
  have hδ0 : 0 < δ := sub_pos.2 hρ_lt1
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  have hlog_ge : Real.log 3 ≤ L := Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg γ])
  have hL_pos : 0 < L := hlog3.trans_le hlog_ge
  have hδ_le : δ ≤ c / L := by linarith
  have hδ_32 : δ ≤ 1 / 32 := by
    have hc_le : c ≤ 1 / 32 * Real.log 3 := min_le_left _ _
    exact (hδ_le.trans (by gcongr)).trans_eq (mul_div_cancel_right₀ _ hlog3.ne')
  set η : ℝ := 4 * δ
  set σ : ℝ := 1 + η
  have hpole : -(logDeriv riemannZeta σ).re ≤ η⁻¹ + C₁ / Real.log 3 * L :=
    le_trans (by simpa [σ] using hpole0 (η := η) (by positivity) (by linarith))
      (add_le_add_right (le_div_log_three_mul hC₁0 hlog_ge) _)
  have hzero_γ : -(logDeriv χ.LFunction (σ + γ * I)).re + (5 * δ)⁻¹ ≤ A * L := by
    simpa [show σ - ρ.re = 5 * δ by simp [σ, η, δ]; ring] using
      hret χ hχ (σ := σ) (by linarith) (by linarith) (by linarith) hL0
  have hzero_2γ := hsq2 χ (σ := σ) (γ := γ) (δ := δ) (by linarith) hδ0 hcase
  have h341 := χ.threeFourOne_re_logDeriv_riemannZeta_LFunction_nonpos (σ := σ) (by linarith) γ
  have hcomb : (120 * δ)⁻¹ ≤ M * L := by
    have halg : 4 * (5 * δ)⁻¹ - 3 * η⁻¹ - (24 * δ)⁻¹ = (120 * δ)⁻¹ := by
      simp only [η]; field_simp [hδ0.ne']; ring
    have hMeq : M * L = 3 * (C₁ / Real.log 3 * L) + 4 * (A * L) + B₂ * L := by simp only [M]; ring
    linarith
  rw [inv_le_iff_one_le_mul₀ (by positivity)] at hcomb
  have hδM : δ * L ≤ 1 / (240 * M) :=
    (le_div_iff₀ hL_pos).mp (hδ_le.trans (div_le_div_of_nonneg_right (min_le_right _ _) hL_pos.le))
  have hupper : 120 * δ * (M * L) ≤ 1 / 2 :=
    ((by ring : 120 * δ * (M * L) = 120 * M * (δ * L)) ▸
      mul_le_mul_of_nonneg_left hδM (by positivity : (0 : ℝ) ≤ 120 * M)).trans_eq
      (by field_simp [hM.ne']; ring)
  linarith

private theorem mem_closedBall_zero_of_im_lt {z : ℂ} (hδ : 1 - z.re ≤ 1 / 96)
    (him : |z.im| < 6 * (1 - z.re)) :
    z ∈ closedBall ((9 / 8 : ℝ) + (0 : ℝ) * I) ((1 / 2 : ℝ) / 2) := by
  have hz1 : z.re < 1 := by linarith [abs_nonneg z.im]
  rw [mem_closedBall, dist_eq_norm,
    show z - ((9 / 8 : ℝ) + (0 : ℝ) * I) = ((z.re - 9 / 8 : ℝ) : ℂ) + z.im * I from
      Complex.ext (by simp) (by simp)]
  calc ‖((z.re - 9 / 8 : ℝ) : ℂ) + z.im * I‖
      ≤ ‖((z.re - 9 / 8 : ℝ) : ℂ)‖ + ‖(z.im : ℂ) * I‖ := norm_add_le _ _
    _ = |z.re - 9 / 8| + |z.im| := by
        rw [norm_real, Real.norm_eq_abs, norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one]
    _ = 1 / 8 + (1 - z.re) + |z.im| := by rw [abs_of_neg (by linarith)]; ring
    _ ≤ (1 / 2 : ℝ) / 2 := by linarith

private theorem exists_neg_re_logDeriv_LFunction_conj_pair_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      ∀ {ρ : ℂ}, ρ.im ≠ 0 → |ρ.im| < 6 * (1 - ρ.re) → 1 - ρ.re ≤ 1 / 96 → χ.LFunction ρ = 0 →
        -(logDeriv χ.LFunction ((1 + 12 * (1 - ρ.re) : ℝ) : ℂ)).re +
          2 * (13 / 205 * (1 - ρ.re)⁻¹) ≤ A * Real.log (q * (|ρ.im| + 3)) := by
  obtain ⟨A, hA, hLandau⟩ := exists_neg_re_logDeriv_LFunction_add_sum_le
  refine ⟨A, hA, fun {q} _ χ hχ hsq {ρ} hγ0 hγ_lt hδ_96 hL0 ↦ ?_⟩
  have hLconj : χ.LFunction (conj ρ) = 0 :=
    (LFunction_conj_eq_zero_iff_of_isQuadratic (MulChar.isQuadratic_iff_sq_eq_one.2 hsq) ρ).2 hL0
  set γ : ℝ := ρ.im
  set δ : ℝ := 1 - ρ.re
  have hδ0 : 0 < δ := by linarith [abs_nonneg γ]
  set σ : ℝ := 1 + 12 * δ
  have hne_conj : ρ ≠ conj ρ := fun h ↦ hγ0 (conj_eq_iff_im.1 h.symm)
  have h1 := hLandau χ hχ (σ := σ) (t := 0) (by linarith) (by linarith) {ρ, conj ρ}
  rw [Finset.sum_pair hne_conj] at h1
  set w : ℂ := ((σ : ℂ) + (0 : ℝ) * I) - ρ
  have hw_re_bound : 13 / 205 * δ⁻¹ ≤ (w⁻¹).re := by
    have hw_re : w.re = 13 * δ := by simp [w, σ, δ]; ring
    have hw_im : w.im = -γ := by simp [w, γ]
    have hnsq_eq : normSq w = 169 * δ ^ 2 + γ ^ 2 := by rw [normSq_apply, hw_re, hw_im]; ring
    have hnsq_le : normSq w ≤ 205 * δ ^ 2 := by
      have hγsq : γ ^ 2 ≤ 36 * δ ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg γ]
      linarith
    rw [inv_re, hw_re]
    calc 13 / 205 * δ⁻¹ = 13 * δ / (205 * δ ^ 2) := by field_simp [hδ0.ne']
      _ ≤ 13 * δ / normSq w := div_le_div_of_nonneg_left (by positivity) (by nlinarith) hnsq_le
  have hconj_eq : ((((σ : ℂ) + (0 : ℝ) * I) - conj ρ)⁻¹).re = (w⁻¹).re := by
    rw [show ((σ : ℂ) + (0 : ℝ) * I) - conj ρ = conj w from Complex.ext (by simp [w]) (by simp [w]),
      ← map_inv₀, conj_re]
  set U0 : Set ℂ := closedBall ((9 / 8 : ℝ) + (0 : ℝ) * I) ((1 / 2 : ℝ) / 2)
  have hD₁ : (1 : ℝ) ≤ (MeromorphicOn.divisor χ.LFunction U0 ρ : ℝ) :=
    mod_cast one_le_divisor_LFunction_of_eq_zero hχ 0 (mem_closedBall_zero_of_im_lt hδ_96 hγ_lt) hL0
  have hD₂ : (1 : ℝ) ≤ (MeromorphicOn.divisor χ.LFunction U0 (conj ρ) : ℝ) :=
    mod_cast one_le_divisor_LFunction_of_eq_zero hχ 0
      (mem_closedBall_zero_of_im_lt (by simp; linarith) (by simp; linarith)) hLconj
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  have hlog0 : Real.log (q * 3) ≤ Real.log (q * (|γ| + 3)) :=
    Real.log_le_log (by positivity) (by nlinarith [abs_nonneg γ])
  have h0nonneg : 0 ≤ (w⁻¹).re := (by positivity : 0 ≤ 13 / 205 * δ⁻¹).trans hw_re_bound
  have hle₁ := hw_re_bound.trans (le_mul_of_one_le_left h0nonneg hD₁)
  have hle₂ := (hconj_eq ▸ hw_re_bound).trans (le_mul_of_one_le_left (hconj_eq ▸ h0nonneg) hD₂)
  have hsum : -(logDeriv χ.LFunction ((σ : ℂ) + (0 : ℝ) * I)).re + 2 * (13 / 205 * δ⁻¹) ≤
      A * Real.log (q * (|(0 : ℝ)| + 3)) := by linarith
  simp only [ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at hsum
  nlinarith

private theorem exists_not_pos_meromorphicOrderAt_of_im_lt :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      ∀ ρ : ℂ, ρ.im ≠ 0 → |ρ.im| < 6 * (1 - ρ.re) →
        1 - c / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re →
        ¬ 0 < meromorphicOrderAt χ.LFunction ρ := by
  obtain ⟨A, hA, hpair0⟩ := exists_neg_re_logDeriv_LFunction_conj_pair_le
  obtain ⟨C₁, hC₁0, hpole0⟩ := TauCeti.exists_neg_re_logDeriv_riemannZeta_one_add_le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set M : ℝ := C₁ / Real.log 3 + A
  have hM : 0 < M := by positivity
  set c : ℝ := min (1 / 96 * Real.log 3) (107 / (4920 * M))
  refine ⟨c, by positivity, fun {q} _ χ hχ hsq ρ hγ0 hγ_lt hρre hord ↦ ?_⟩
  have hL0 : χ.LFunction ρ = 0 := (χ.meromorphicOrderAt_LFunction_pos_iff.1 hord).1
  set δ : ℝ := 1 - ρ.re
  set L : ℝ := Real.log (q * (|ρ.im| + 3))
  have hδ0 : 0 < δ := by linarith [abs_nonneg ρ.im]
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  have hlog_ge : Real.log 3 ≤ L := Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg ρ.im])
  have hL_pos : 0 < L := hlog3.trans_le hlog_ge
  have hδ_le : δ ≤ c / L := by linarith
  have hδ_96 : δ ≤ 1 / 96 := by
    have hc_le : c ≤ 1 / 96 * Real.log 3 := min_le_left _ _
    exact (hδ_le.trans (by gcongr)).trans_eq (mul_div_cancel_right₀ _ hlog3.ne')
  set η : ℝ := 12 * δ
  set σ : ℝ := 1 + η
  have hpair : -(logDeriv χ.LFunction σ).re + 2 * (13 / 205 * δ⁻¹) ≤ A * L :=
    hpair0 χ hχ hsq hγ0 hγ_lt hδ_96 hL0
  have hpole : -(logDeriv riemannZeta σ).re ≤ η⁻¹ + C₁ / Real.log 3 * L :=
    le_trans (by simpa [σ] using hpole0 (η := η) (by positivity) (by linarith))
      (add_le_add_right (le_div_log_three_mul hC₁0 hlog_ge) _)
  have h1χ := χ.re_logDeriv_riemannZeta_add_re_logDeriv_LFunction_nonpos
    (s := σ) (by simp [σ]; linarith)
  simp only [ofReal_re] at h1χ
  have hcomb : 2 * (13 / 205 * δ⁻¹) - η⁻¹ ≤ M * L := by
    have _ : M * L = C₁ / Real.log 3 * L + A * L := by simp only [M]; ring
    linarith
  have halg : 2 * (13 / 205 * δ⁻¹) - η⁻¹ = 107 / 2460 * δ⁻¹ := by
    simp only [η]; field_simp [hδ0.ne']; ring
  rw [halg, mul_inv_le_iff₀ hδ0] at hcomb
  have hδM : δ * L ≤ 107 / (4920 * M) :=
    (le_div_iff₀ hL_pos).mp (hδ_le.trans (div_le_div_of_nonneg_right (min_le_right _ _) hL_pos.le))
  have hupper : M * L * δ ≤ 107 / 4920 :=
    ((by ring : M * L * δ = M * (δ * L)) ▸ mul_le_mul_of_nonneg_left hδM hM.le).trans_eq
      (by field_simp [hM.ne'])
  linarith

private theorem sum_divisor_mul_re_inv_ge {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ16 : δ ≤ 1 / 16) {S : Finset ℂ}
    (hS : ∀ ρ ∈ S, ρ.im = 0 ∧ 1 - ρ.re ≤ δ ∧ χ.LFunction ρ = 0) :
    (∑ ρ ∈ S, (MeromorphicOn.divisor χ.LFunction
        (closedBall ((9 / 8 : ℝ) + (0 : ℝ) * I) ((1 / 2 : ℝ) / 2)) ρ : ℝ)) * (3 * δ)⁻¹ ≤
      ∑ ρ ∈ S, (MeromorphicOn.divisor χ.LFunction
        (closedBall ((9 / 8 : ℝ) + (0 : ℝ) * I) ((1 / 2 : ℝ) / 2)) ρ : ℝ) *
        (((((1 + 2 * δ : ℝ) : ℂ) + (0 : ℝ) * I) - ρ)⁻¹).re := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun ρ hρ ↦ ?_
  obtain ⟨him, hle, hL0⟩ := hS ρ hρ
  have hlt1 : ρ.re < 1 :=
    by_contra fun h ↦ LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hL0
  have hmem : ρ ∈ closedBall ((9 / 8 : ℝ) + (0 : ℝ) * I) ((1 / 2 : ℝ) / 2) := by
    simpa [him] using mem_closedBall_of_seven_div_eight_le_re hχ (by linarith) hL0
  have hD0 : (0 : ℝ) ≤ (MeromorphicOn.divisor χ.LFunction
      (closedBall ((9 / 8 : ℝ) + (0 : ℝ) * I) ((1 / 2 : ℝ) / 2)) ρ : ℝ) :=
    zero_le_one.trans (mod_cast one_le_divisor_LFunction_of_eq_zero hχ 0 hmem hL0)
  rw [show (((1 + 2 * δ : ℝ) : ℂ) + (0 : ℝ) * I) - ρ = ((1 + 2 * δ - ρ.re : ℝ) : ℂ) from
    Complex.ext (by simp) (by simp [him]), ← ofReal_inv, ofReal_re]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ (by linarith) (by linarith)) hD0

private theorem exists_sum_divisor_le_one_of_im_eq_zero :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 16 * Real.log 3 ∧
      ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ S : Finset ℂ,
        (∀ ρ ∈ S, ρ.im = 0 ∧ 1 - c / Real.log (q * 3) ≤ ρ.re ∧ χ.LFunction ρ = 0) →
        ∑ ρ ∈ S, MeromorphicOn.divisor χ.LFunction
          (closedBall ((9 / 8 : ℝ) + (0 : ℝ) * I) ((1 / 2 : ℝ) / 2)) ρ ≤ 1 := by
  obtain ⟨A, hA, hLandau⟩ := exists_neg_re_logDeriv_LFunction_add_sum_le
  obtain ⟨C₁, hC₁0, hpole0⟩ := TauCeti.exists_neg_re_logDeriv_riemannZeta_one_add_le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set M : ℝ := C₁ / Real.log 3 + A
  have hM : 0 < M := by positivity
  set c : ℝ := min (1 / 16 * Real.log 3) (1 / (12 * M))
  refine ⟨c, by positivity, min_le_left _ _, fun {q} _ χ hχ S hS ↦ ?_⟩
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · simp
  by_contra! hgt
  set δ : ℝ := S.sup' hSne fun ρ ↦ 1 - ρ.re
  set L : ℝ := Real.log (q * 3)
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  have hlog_ge : Real.log 3 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hL_pos : 0 < L := hlog3.trans_le hlog_ge
  have ⟨ρ₀, hρ₀S⟩ := hSne
  have hδ0 : 0 < δ := (sub_pos.2 <| by_contra fun h ↦
    LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) (hS ρ₀ hρ₀S).2.2).trans_le
    (Finset.le_sup' (fun z : ℂ ↦ 1 - z.re) hρ₀S)
  have hδ_le : δ ≤ c / L := Finset.sup'_le hSne _ fun ρ hρ ↦ by linarith [(hS ρ hρ).2.1]
  have hδ_16 : δ ≤ 1 / 16 := by
    have hc_le : c ≤ 1 / 16 * Real.log 3 := min_le_left _ _
    exact (hδ_le.trans (by gcongr)).trans_eq (mul_div_cancel_right₀ _ hlog3.ne')
  set σ : ℝ := 1 + 2 * δ
  let U0 : Set ℂ := closedBall ((9 / 8 : ℝ) + (0 : ℝ) * I) ((1 / 2 : ℝ) / 2)
  have hD2 : (2 : ℝ) ≤ ∑ ρ ∈ S, (MeromorphicOn.divisor χ.LFunction U0 ρ : ℝ) := by
    rw [← Int.cast_sum]
    exact_mod_cast Int.add_one_le_iff.2 hgt
  have hsum_ge : 2 * (3 * δ)⁻¹ ≤
      ∑ ρ ∈ S, (MeromorphicOn.divisor χ.LFunction U0 ρ : ℝ) *
        ((((σ : ℂ) + (0 : ℝ) * I) - ρ)⁻¹).re :=
    (mul_le_mul_of_nonneg_right hD2 (by positivity)).trans
      (sum_divisor_mul_re_inv_ge hχ hδ0 hδ_16 fun ρ hρ ↦
        ⟨(hS ρ hρ).1, Finset.le_sup' (fun z : ℂ ↦ 1 - z.re) hρ, (hS ρ hρ).2.2⟩)
  have h1 := hLandau χ hχ (σ := σ) (t := 0) (by linarith) (by linarith) S
  have h1' : -(logDeriv χ.LFunction ((σ : ℂ) + (0 : ℝ) * I)).re + 2 * (3 * δ)⁻¹ ≤
      A * Real.log (q * (|(0 : ℝ)| + 3)) := by linarith
  simp only [ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at h1'
  have hpole : -(logDeriv riemannZeta σ).re ≤ (2 * δ)⁻¹ + C₁ / Real.log 3 * L :=
    le_trans (by simpa [σ] using hpole0 (η := 2 * δ) (by positivity) (by linarith))
      (add_le_add_right (le_div_log_three_mul hC₁0 hlog_ge) _)
  have h1χ := χ.re_logDeriv_riemannZeta_add_re_logDeriv_LFunction_nonpos
    (s := σ) (by simp [σ]; linarith)
  simp only [ofReal_re] at h1χ
  have hcomb : (6 * δ)⁻¹ ≤ M * L := by
    have halg : 2 * (3 * δ)⁻¹ - (2 * δ)⁻¹ = (6 * δ)⁻¹ := by field_simp [hδ0.ne']; ring
    have _ : M * L = C₁ / Real.log 3 * L + A * L := by simp only [M]; ring
    linarith
  rw [inv_le_iff_one_le_mul₀ (by positivity)] at hcomb
  have hδM : δ * L ≤ 1 / (12 * M) :=
    (le_div_iff₀ hL_pos).mp (hδ_le.trans (div_le_div_of_nonneg_right (min_le_right _ _) hL_pos.le))
  have hupper : 6 * δ * (M * L) ≤ 1 / 2 :=
    ((by ring : 6 * δ * (M * L) = 6 * M * (δ * L)) ▸
      mul_le_mul_of_nonneg_left hδM (by positivity : (0 : ℝ) ≤ 6 * M)).trans_eq
      (by field_simp [hM.ne']; ring)
  linarith

private theorem exists_meromorphicOrderAt_eq_one_and_eq_of_im_eq_zero :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      (∀ ρ : ℂ, ρ.im = 0 → 1 - c / Real.log (q * 3) ≤ ρ.re →
        0 < meromorphicOrderAt χ.LFunction ρ → meromorphicOrderAt χ.LFunction ρ = 1) ∧
      ∀ ρ₁ ρ₂ : ℂ, ρ₁.im = 0 → ρ₂.im = 0 →
        1 - c / Real.log (q * 3) ≤ ρ₁.re → 1 - c / Real.log (q * 3) ≤ ρ₂.re →
        0 < meromorphicOrderAt χ.LFunction ρ₁ → 0 < meromorphicOrderAt χ.LFunction ρ₂ →
        ρ₁ = ρ₂ := by
  obtain ⟨c, hc, hc16, hsum⟩ := exists_sum_divisor_le_one_of_im_eq_zero
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨c, hc, fun {q} _ χ hχ ↦ ?_⟩
  let U0 : Set ℂ := closedBall ((9 / 8 : ℝ) + (0 : ℝ) * I) ((1 / 2 : ℝ) / 2)
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  have hlog_ge : Real.log 3 ≤ Real.log (q * 3) := Real.log_le_log (by norm_num) (by linarith)
  have hmem (ρ : ℂ) (him : ρ.im = 0) (hre : 1 - c / Real.log (q * 3) ≤ ρ.re)
      (hL0 : χ.LFunction ρ = 0) : ρ ∈ U0 := by
    have hdiv : c / Real.log (q * 3) ≤ 1 / 16 * Real.log 3 / Real.log 3 := by gcongr
    rw [mul_div_cancel_right₀ _ hlog3.ne'] at hdiv
    simpa [U0, him] using mem_closedBall_of_seven_div_eight_le_re hχ (by linarith) hL0
  refine ⟨fun ρ him hre hord ↦ ?_, fun ρ₁ ρ₂ him₁ him₂ hre₁ hre₂ hord₁ hord₂ ↦ ?_⟩
  · have hL0 := (χ.meromorphicOrderAt_LFunction_pos_iff.1 hord).1
    have hm := hmem ρ him hre hL0
    have hle1 : MeromorphicOn.divisor χ.LFunction U0 ρ ≤ 1 := by
      simpa [U0] using hsum χ hχ {ρ} fun z hz ↦ Finset.mem_singleton.mp hz ▸ ⟨him, hre, hL0⟩
    rw [← coe_divisor_LFunction_eq hχ 0 hm]
    exact_mod_cast le_antisymm hle1 (one_le_divisor_LFunction_of_eq_zero hχ 0 hm hL0)
  · by_contra hne
    have hL₁ := (χ.meromorphicOrderAt_LFunction_pos_iff.1 hord₁).1
    have hL₂ := (χ.meromorphicOrderAt_LFunction_pos_iff.1 hord₂).1
    have hle1 := hsum χ hχ {ρ₁, ρ₂} (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro z (rfl | rfl)
      · exact ⟨him₁, hre₁, hL₁⟩
      · exact ⟨him₂, hre₂, hL₂⟩)
    rw [Finset.sum_pair hne] at hle1
    have hge₁ := one_le_divisor_LFunction_of_eq_zero hχ 0 (hmem ρ₁ him₁ hre₁ hL₁) hL₁
    have hge₂ := one_le_divisor_LFunction_of_eq_zero hχ 0 (hmem ρ₂ him₂ hre₂ hL₂) hL₂
    omega

/-- **The classical zero-free region for Dirichlet `L`-functions.** There is an absolute constant
`c` with `0 < c ≤ log 3 / 2` such that for every modulus `q ≥ 1` and every Dirichlet character `χ`
modulo `q`, any zero `ρ` of `L(·, χ)` (in the sense `0 < meromorphicOrderAt χ.LFunction ρ`) with
`1 - c / log (q (|Im ρ| + 3)) ≤ Re ρ` is real, simple, and occurs only for a real character
(`χ ^ 2 = 1`), and there is at most one such zero. -/
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
  obtain ⟨cζ, hcζ, hζ⟩ := riemannZeta_zeroFreeRegion
  obtain ⟨c₁, hc₁, hno_high⟩ := exists_not_pos_meromorphicOrderAt_of_sq_ne_one_or_im_ge
  obtain ⟨c₂, hc₂, hno_low⟩ := exists_not_pos_meromorphicOrderAt_of_im_lt
  obtain ⟨c₃, hc₃, hreal_zero⟩ := exists_meromorphicOrderAt_eq_one_and_eq_of_im_eq_zero
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set c : ℝ := min (Real.log 3 / 2) (min cζ (min c₁ (min c₂ c₃)))
  have hc_half : c ≤ Real.log 3 / 2 := min_le_left _ _
  have hc_r : c ≤ min cζ (min c₁ (min c₂ c₃)) := min_le_right _ _
  have hc_ζ : c ≤ cζ := hc_r.trans (min_le_left _ _)
  have hc_1 : c ≤ c₁ := hc_r.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc_2 : c ≤ c₂ :=
    hc_r.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hc_3 : c ≤ c₃ :=
    hc_r.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨c, by positivity, hc_half, fun q _ χ ↦ ?_⟩
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  have hreal (ρ : ℂ) (hρre : 1 - c / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re)
      (hord : 0 < meromorphicOrderAt χ.LFunction ρ) :
      ρ.im = 0 ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧ 1 - c₃ / Real.log (q * 3) ≤ ρ.re := by
    set L : ℝ := Real.log (q * (|ρ.im| + 3))
    have hlog_ge : Real.log 3 ≤ L := Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg ρ.im])
    have hlog_pos : 0 < L := hlog3.trans_le hlog_ge
    have hlift {c' : ℝ} (hc' : c ≤ c') : 1 - c' / L ≤ ρ.re :=
      (sub_le_sub_left (div_le_div_of_nonneg_right hc' hlog_pos.le) 1).trans hρre
    have hhalf : (1 / 2 : ℝ) ≤ ρ.re := by
      have hdiv : c / L ≤ (Real.log 3 / 2) / Real.log 3 := by gcongr
      have hval : (Real.log 3 / 2) / Real.log 3 = 1 / 2 := by field_simp [hlog3.ne']
      linarith
    have hχ : χ ≠ 1 := by
      rintro rfl
      rw [show meromorphicOrderAt (1 : DirichletCharacter ℂ q).LFunction ρ =
            meromorphicOrderAt riemannZeta ρ from
          meromorphicOrderAt_LFunctionTrivChar_eq_riemannZeta (by linarith),
        TauCeti.meromorphicOrderAt_riemannZeta_pos_iff] at hord
      have hlog_q : Real.log (|ρ.im| + 3) ≤ L :=
        Real.log_le_log (by positivity) (by nlinarith [abs_nonneg ρ.im])
      have hlog_pos' : 0 < Real.log (|ρ.im| + 3) :=
        hlog3.trans_le (Real.log_le_log (by norm_num) (by linarith [abs_nonneg ρ.im]))
      have hdiv : c / L ≤ cζ / Real.log (|ρ.im| + 3) := by gcongr
      exact hζ ρ hord.2 (by linarith) hord.1
    have hsq : χ ^ 2 = 1 := by_contra fun hsq ↦ hno_high χ hχ ρ (.inl hsq) (hlift hc_1) hord
    have him : ρ.im = 0 := by_contra fun him0 ↦
      (le_or_gt (6 * (1 - ρ.re)) |ρ.im|).elim
        (fun hge ↦ hno_high χ hχ ρ (.inr hge) (hlift hc_1) hord)
        (fun hlt ↦ hno_low χ hχ hsq ρ him0 hlt (hlift hc_2) hord)
    exact ⟨him, hsq, hχ, by simpa [L, him] using hlift hc_3⟩
  refine ⟨fun ρ hre hord ↦ ?_, fun ρ₁ ρ₂ hre₁ hre₂ hord₁ hord₂ ↦ ?_⟩
  · obtain ⟨him, hsq, hχ, hc3⟩ := hreal ρ hre hord
    exact ⟨him, hsq, (hreal_zero χ hχ).1 ρ him hc3 hord⟩
  · obtain ⟨him₁, -, hχ, hc3₁⟩ := hreal ρ₁ hre₁ hord₁
    obtain ⟨him₂, -, -, hc3₂⟩ := hreal ρ₂ hre₂ hord₂
    exact (hreal_zero χ hχ).2 ρ₁ ρ₂ him₁ him₂ hc3₁ hc3₂ hord₁ hord₂

/-! ### Example -/

example : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ ^ 2 ≠ 1 → ∀ ρ : ℂ, 1 - c / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re → χ.LFunction ρ ≠ 0 := by
  obtain ⟨c, hc, -, hreg⟩ := dirichletLFunction_zeroFreeRegion
  refine ⟨c, hc, fun q _ χ hsq ρ hre hL0 ↦ ?_⟩
  have hχ : χ ≠ 1 := fun h1 ↦ hsq (by simp [h1])
  exact hsq ((hreg q χ).1 ρ hre (χ.meromorphicOrderAt_LFunction_pos_iff.2 ⟨hL0, .inr hχ⟩)).2.1

end TauCeti.LFunctions
