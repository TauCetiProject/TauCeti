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
`O(log (q (|t| + 3)))` while retaining nearby zeros with positive weight:
* When `χ ^ 2 ≠ 1`, or when `χ ^ 2 = 1` and `|Im ρ| ≥ 6 (1 - Re ρ)`, the `3–4–1` inequality at
  `σ = 1 + 4 (1 - Re ρ)` rules out any zero in the region (using the `(4 |γ|)⁻¹` bound for the
  pole of `L′/L(σ + 2 i γ, 1)` when `χ ^ 2 = 1`).
* When `χ ^ 2 = 1` and `0 < |Im ρ| < 6 (1 - Re ρ)`, conjugate symmetry gives a distinct zero
  `conj ρ`, and retaining the pair `{ρ, conj ρ}` in `-Re (ζ′/ζ(σ) + L′/L(σ, χ)) ≥ 0` at
  `σ = 1 + 12 (1 - Re ρ)` outweighs the pole `1 / (σ - 1)`.
* The same `1 + χ` inequality on the real axis shows that any real zero in the region is simple and
  unique.

## Main results

* `TauCeti.LFunctions.exists_neg_re_logDeriv_LFunction_le`:
  `-Re (L′/L(σ + i t, χ)) ≪ log (q (|t| + 3))` uniformly for nonprincipal `χ` modulo `q` and
  `1 < σ ≤ 9 / 8`.
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
    (hχ : χ ≠ 1) {t : ℝ} {w : ℂ} (hw : w ∈ closedBall ((9 / 8 : ℂ) + t * I) (1 / 2)) :
    5 / 8 ≤ w.re ∧ ‖χ.LFunction w‖ ≤ 2 * ((q : ℝ) * (|t| + 3)) := by
  set z₀ : ℂ := 9 / 8 + t * I
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
              (closedBall ((9 / 8 : ℂ) + t * I) ((1 / 2 : ℝ) / 2)) ρ : ℝ) *
              ((((σ : ℂ) + t * I) - ρ)⁻¹).re ≤
          A * Real.log (q * (|t| + 3)) := by
  set C₀ : ℝ := 2 * Real.exp (riemannZeta (9 / 8 : ℝ)).re
  have hC₀ : 0 < C₀ := by positivity
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨96 * (max 0 (Real.log C₀) / Real.log 3 + 1), by positivity,
    fun {q} _ χ hχ {σ t} hσ1 hσ2 S ↦ ?_⟩
  set z₀ : ℂ := 9 / 8 + t * I
  have hf : AnalyticOnNhd ℂ χ.LFunction (closedBall z₀ (1 / 2)) :=
    ((differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
  have h1le : 1 ≤ Real.exp (riemannZeta (9 / 8 : ℝ)).re * ‖χ.LFunction z₀‖ := by
    have hz₀_lo : Real.exp (-(riemannZeta (9 / 8 : ℝ)).re) ≤ ‖χ.LFunction z₀‖ := by
      simpa [z₀] using χ.exp_neg_re_riemannZeta_le_norm_LFunction (s := z₀) (by simp [z₀]; norm_num)
    set a : ℝ := (riemannZeta (9 / 8 : ℝ)).re
    calc (1 : ℝ) = Real.exp (a + -a) := by simp
      _ = Real.exp a * Real.exp (-a) := Real.exp_add _ _
      _ ≤ Real.exp a * ‖χ.LFunction z₀‖ := by gcongr
  have hM (w : ℂ) (hw : w ∈ sphere z₀ (1 / 2)) :
      ‖χ.LFunction w‖ ≤ C₀ * ((q : ℝ) * (|t| + 3)) * ‖χ.LFunction z₀‖ := by
    calc ‖χ.LFunction w‖ ≤ 2 * ((q : ℝ) * (|t| + 3)) :=
        (norm_LFunction_on_closedBall hχ (sphere_subset_closedBall hw)).2
      _ ≤ 2 * ((q : ℝ) * (|t| + 3)) *
          (Real.exp (riemannZeta (9 / 8 : ℝ)).re * ‖χ.LFunction z₀‖) :=
        le_mul_of_one_le_right (by positivity) h1le
      _ = C₀ * ((q : ℝ) * (|t| + 3)) * ‖χ.LFunction z₀‖ := by simp only [C₀]; ring
  have hz : ‖(σ : ℂ) + t * I - z₀‖ ≤ (1 / 2 : ℝ) / 4 := by
    have heq : (σ : ℂ) + t * I - z₀ = ((σ - 9 / 8 : ℝ) : ℂ) :=
      Complex.ext (by simp [z₀]) (by simp [z₀])
    rw [heq, norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith
  have hfz : χ.LFunction ((σ : ℂ) + t * I) ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simp; linarith)
  have hre (ρ : ℂ) (_ : ρ ∈ closedBall z₀ ((1 / 2 : ℝ) / 2)) (hρ0 : χ.LFunction ρ = 0) :
      ρ.re ≤ ((σ : ℂ) + t * I).re := by
    have hρ1 : ρ.re < 1 :=
      by_contra fun h ↦ LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hρ0
    simp; linarith
  have hmain := hf.neg_re_logDeriv_add_sum_divisor_half_le (by norm_num) hM hz hfz hre S
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  have hqt : 0 < (q : ℝ) * (|t| + 3) := by positivity
  have hlog_ge : Real.log 3 ≤ Real.log (q * (|t| + 3)) :=
    Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg t])
  have hmax : Real.log C₀ ≤ max 0 (Real.log C₀) / Real.log 3 * Real.log (q * (|t| + 3)) := by
    calc Real.log C₀ ≤ max 0 (Real.log C₀) := le_max_right _ _
      _ = max 0 (Real.log C₀) / Real.log 3 * Real.log 3 := (div_mul_cancel₀ _ hlog3.ne').symm
      _ ≤ max 0 (Real.log C₀) / Real.log 3 * Real.log (q * (|t| + 3)) :=
        mul_le_mul_of_nonneg_left hlog_ge (div_nonneg (le_max_left _ _) hlog3.le)
  rw [Real.log_mul hC₀.ne' hqt.ne'] at hmain
  linarith

/-- **Landau upper bound for `-Re (L′/L)` of a nonprincipal character.** There is an absolute
constant `A > 0` such that `-(logDeriv χ.LFunction (σ + t * I)).re ≤ A * Real.log (q * (|t| + 3))`
for every modulus `q ≥ 1`, every `χ ≠ 1` modulo `q`, every `1 < σ ≤ 9 / 8`, and every `t : ℝ`. -/
theorem exists_neg_re_logDeriv_LFunction_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {σ t : ℝ}, 1 < σ → σ ≤ 9 / 8 →
        -(logDeriv χ.LFunction (σ + t * I)).re ≤ A * Real.log (q * (|t| + 3)) := by
  obtain ⟨A, hA, h⟩ := exists_neg_re_logDeriv_LFunction_add_sum_le
  exact ⟨A, hA, fun {_} _ χ hχ {_ _} hσ1 hσ2 ↦ by simpa using h χ hχ hσ1 hσ2 ∅⟩

private theorem LFunction_eq_zero_of_pos_meromorphicOrderAt {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {ρ : ℂ}
    (hord : 0 < meromorphicOrderAt χ.LFunction ρ) : χ.LFunction ρ = 0 := by
  by_contra hne
  have ha : AnalyticAt ℂ χ.LFunction ρ :=
    ((differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ) ρ (mem_univ ρ)
  rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.2 hne] at hord
  exact lt_irrefl 0 hord

private theorem coe_divisor_LFunction_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t : ℝ) {ρ : ℂ}
    (hρ : ρ ∈ closedBall ((9 / 8 : ℂ) + t * I) ((1 / 2 : ℝ) / 2)) :
    (MeromorphicOn.divisor χ.LFunction
      (closedBall ((9 / 8 : ℂ) + t * I) ((1 / 2 : ℝ) / 2)) ρ : WithTop ℤ) =
      meromorphicOrderAt χ.LFunction ρ := by
  have hf : AnalyticOnNhd ℂ χ.LFunction (closedBall ((9 / 8 : ℂ) + t * I) (1 / 2)) :=
    ((differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
  have hz₀ : χ.LFunction ((9 / 8 : ℂ) + t * I) ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simp; norm_num)
  exact hf.coe_divisor_half_eq_meromorphicOrderAt hz₀ hρ

private theorem one_le_divisor_LFunction_of_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t : ℝ) {ρ : ℂ}
    (hρ : ρ ∈ closedBall ((9 / 8 : ℂ) + t * I) ((1 / 2 : ℝ) / 2)) (hL0 : χ.LFunction ρ = 0) :
    1 ≤ MeromorphicOn.divisor χ.LFunction
      (closedBall ((9 / 8 : ℂ) + t * I) ((1 / 2 : ℝ) / 2)) ρ := by
  have ha : AnalyticAt ℂ χ.LFunction ρ :=
    ((differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ) ρ (mem_univ ρ)
  have hpos : (0 : WithTop ℤ) <
      (MeromorphicOn.divisor χ.LFunction
        (closedBall ((9 / 8 : ℂ) + t * I) ((1 / 2 : ℝ) / 2)) ρ : WithTop ℤ) := by
    rw [coe_divisor_LFunction_eq hχ t hρ, ha.meromorphicOrderAt_eq]
    cases ho : analyticOrderAt χ.LFunction ρ with
    | top => simp
    | coe n =>
      have hn : n ≠ 0 := by simpa [ho] using ha.analyticOrderAt_ne_zero.2 hL0
      simpa using Nat.pos_of_ne_zero hn
  have h0 := WithTop.coe_lt_coe.1 hpos
  omega

private theorem mem_closedBall_of_seven_div_eight_le_re {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {ρ : ℂ} (h7 : 7 / 8 ≤ ρ.re)
    (hL0 : χ.LFunction ρ = 0) :
    ρ ∈ closedBall ((9 / 8 : ℂ) + ρ.im * I) ((1 / 2 : ℝ) / 2) := by
  have hlt1 : ρ.re < 1 :=
    by_contra fun h ↦ LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hL0
  rw [mem_closedBall, dist_eq_norm]
  have heq : ρ - ((9 / 8 : ℂ) + ρ.im * I) = ((ρ.re - 9 / 8 : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp)
  rw [heq, norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith

private theorem exists_neg_re_logDeriv_riemannZeta_pole_le :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ {η : ℝ}, 0 < η → η ≤ 1 →
      -(logDeriv riemannZeta ((1 + η : ℝ) : ℂ)).re ≤ η⁻¹ + C₁ := by
  obtain ⟨C, hC⟩ := TauCeti.exists_norm_neg_logDeriv_riemannZeta_one_add_sub_inv_le
  refine ⟨max 0 C, le_max_left _ _, fun {η} hη0 hη1 ↦ ?_⟩
  have h := (abs_re_le_norm _).trans ((hC η hη0 hη1).trans (le_max_right 0 C))
  have hre : (-logDeriv riemannZeta (1 + (η : ℂ)) - (η : ℂ)⁻¹).re =
      -(logDeriv riemannZeta ((1 + η : ℝ) : ℂ)).re - η⁻¹ := by simp [← ofReal_inv]
  linarith [(abs_le.mp h).2]

private theorem re_inv_add_two_mul_I_le {η γ : ℝ} (hη0 : 0 < η) (hγ : γ ≠ 0) :
    (((η : ℂ) + (2 * γ : ℝ) * I)⁻¹).re ≤ (4 * |γ|)⁻¹ := by
  have _ : 0 < |γ| := abs_pos.2 hγ
  rw [inv_re]
  have hnsq : normSq ((η : ℂ) + (2 * γ : ℝ) * I) = η ^ 2 + 4 * γ ^ 2 := by
    rw [normSq_apply]; simp; ring
  rw [show ((η : ℂ) + (2 * γ : ℝ) * I).re = η by simp, hnsq,
    le_inv_comm₀ (by positivity) (by positivity), inv_div, le_div_iff₀ hη0]
  nlinarith [sq_nonneg (η - 2 * |γ|), sq_abs γ]

private theorem exists_neg_re_logDeriv_riemannZeta_two_mul_le :
    ∃ B : ℝ, 0 < B ∧ ∀ (q : ℕ) [NeZero q] {σ γ : ℝ}, 1 < σ → σ ≤ 9 / 8 → γ ≠ 0 →
      -(logDeriv riemannZeta (σ + 2 * γ * I)).re ≤
        (4 * |γ|)⁻¹ + B * Real.log (q * (|γ| + 3)) := by
  obtain ⟨Aζ, hAζ, hζhigh⟩ := exists_neg_re_logDeriv_riemannZeta_le
  have hK : IsCompact (Icc (1 : ℝ) (9 / 8) ×ℂ Icc (-1 : ℝ) 1) :=
    isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨CK, hCK⟩ := hK.exists_norm_logDeriv_riemannZeta_add_inv_sub_one_le fun z hz ↦ hz.1.1
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set CK' : ℝ := max 0 CK
  refine ⟨2 * Aζ + CK' / Real.log 3, by positivity, fun q _ {σ γ} hσ1 hσ2 hγ ↦ ?_⟩
  set s : ℂ := σ + 2 * γ * I
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  have hlog_ge : Real.log 3 ≤ Real.log (q * (|γ| + 3)) :=
    Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg γ])
  have hlog_pos : 0 < Real.log (q * (|γ| + 3)) := hlog3.trans_le hlog_ge
  rcases le_or_gt 1 |2 * γ| with h2γ | h2γ
  · have hhigh := hζhigh hσ1 hσ2 h2γ
    simp only [ofReal_mul, ofReal_ofNat] at hhigh
    have hlog2 : Real.log (|2 * γ| + 3) ≤ 2 * Real.log (q * (|γ| + 3)) := by
      calc Real.log (|2 * γ| + 3) ≤ Real.log ((q * (|γ| + 3)) ^ 2) :=
          Real.log_le_log (by positivity) (by
            have hsq : |2 * γ| + 3 ≤ (|γ| + 3) ^ 2 := by
              rw [abs_mul]; norm_num; nlinarith [abs_nonneg γ]
            have hqsq : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
            nlinarith [sq_nonneg (|γ| + 3)])
        _ = 2 * Real.log (q * (|γ| + 3)) := by rw [Real.log_pow]; norm_num
    have hinv0 : 0 ≤ (4 * |γ|)⁻¹ := by positivity
    have hCK0 : 0 ≤ CK' / Real.log 3 * Real.log (q * (|γ| + 3)) :=
      mul_nonneg (div_nonneg (le_max_left _ _) hlog3.le) hlog_pos.le
    nlinarith
  · have hsK : s ∈ Icc (1 : ℝ) (9 / 8) ×ℂ Icc (-1 : ℝ) 1 :=
      ⟨⟨by simp [s]; linarith, by simp [s]; linarith⟩, by simpa [s] using abs_le.mp h2γ.le⟩
    have hs1 : s ≠ 1 := fun h ↦ hγ (by simpa [s] using congrArg im h)
    have hb := (abs_re_le_norm _).trans ((hCK s hsK hs1).trans (le_max_right 0 CK))
    have hs_re : ((s - 1)⁻¹).re ≤ (4 * |γ|)⁻¹ := by
      rw [show s - 1 = ((σ - 1 : ℝ) : ℂ) + (2 * γ : ℝ) * I from
        Complex.ext (by simp [s]) (by simp [s])]
      exact re_inv_add_two_mul_I_le (sub_pos.2 hσ1) hγ
    have hCK_log : CK' ≤ CK' / Real.log 3 * Real.log (q * (|γ| + 3)) := by
      calc CK' = CK' / Real.log 3 * Real.log 3 := (div_mul_cancel₀ _ hlog3.ne').symm
        _ ≤ CK' / Real.log 3 * Real.log (q * (|γ| + 3)) :=
          mul_le_mul_of_nonneg_left hlog_ge (div_nonneg (le_max_left _ _) hlog3.le)
    have hA0 : 0 ≤ 2 * Aζ * Real.log (q * (|γ| + 3)) :=
      mul_nonneg (by positivity) hlog_pos.le
    have hadd_re : (logDeriv riemannZeta s + (s - 1)⁻¹).re =
        (logDeriv riemannZeta s).re + ((s - 1)⁻¹).re := add_re _ _
    linarith [(abs_le.mp hb).1]

private theorem exists_neg_re_logDeriv_sq_two_mul_le :
    ∃ B : ℝ, 0 < B ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ γ δ : ℝ},
      1 < σ → σ ≤ 9 / 8 → 0 < δ → (χ ^ 2 ≠ 1 ∨ 6 * δ ≤ |γ|) →
        -(logDeriv (χ ^ 2).LFunction (σ + 2 * γ * I)).re ≤
          (24 * δ)⁻¹ + B * Real.log (q * (|γ| + 3)) := by
  obtain ⟨A, hA, hLandau⟩ := exists_neg_re_logDeriv_LFunction_le
  obtain ⟨B₀, hB₀, hζ2⟩ := exists_neg_re_logDeriv_riemannZeta_two_mul_le
  refine ⟨2 * A + B₀ + 1, by positivity, fun {q} _ χ {σ γ δ} hσ1 hσ2 hδ0 hcase ↦ ?_⟩
  set L : ℝ := Real.log (q * (|γ| + 3))
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  have hL_pos : 0 < L :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 3)).trans_le
      (Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg γ]))
  rcases eq_or_ne (χ ^ 2) 1 with hsq1 | hsq_ne
  · have hγ6 : 6 * δ ≤ |γ| := hcase.resolve_left (not_not.2 hsq1)
    have hγ_ne : γ ≠ 0 := fun h0 ↦ by simp [h0] at hγ6; linarith
    set s : ℂ := σ + 2 * γ * I
    have htriv := (abs_re_le_norm _).trans
      (norm_logDeriv_trivChar_sub_logDeriv_riemannZeta_le (N := q) (s := s) (by simp [s]; linarith))
    have hlogq : Real.log q ≤ L := Real.log_le_log (by positivity) (by nlinarith [abs_nonneg γ])
    have hsub : (logDeriv (1 : DirichletCharacter ℂ q).LFunction s - logDeriv riemannZeta s).re =
        (logDeriv (1 : DirichletCharacter ℂ q).LFunction s).re - (logDeriv riemannZeta s).re :=
      sub_re _ _
    have hζ := hζ2 q hσ1 hσ2 hγ_ne
    have hinv24 : (4 * |γ|)⁻¹ ≤ (24 * δ)⁻¹ := inv_anti₀ (by positivity) (by linarith)
    rw [hsq1]
    linarith [(abs_le.mp htriv).1, mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * A) hL_pos.le]
  · have h2 := hLandau (χ ^ 2) hsq_ne (σ := σ) (t := 2 * γ) hσ1 hσ2
    simp only [ofReal_mul, ofReal_ofNat] at h2
    have hlog2 : Real.log (q * (|2 * γ| + 3)) ≤ 2 * L := by
      calc Real.log (q * (|2 * γ| + 3)) ≤ Real.log ((q * (|γ| + 3)) ^ 2) :=
          Real.log_le_log (by positivity) (by
            have hsq : |2 * γ| + 3 ≤ (|γ| + 3) ^ 2 := by
              rw [abs_mul]; norm_num; nlinarith [abs_nonneg γ]
            have hqsq : (q : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
            nlinarith [sq_nonneg (|γ| + 3)])
        _ = 2 * L := by rw [Real.log_pow]; push_cast; rfl
    have hinv0 : 0 ≤ (24 * δ)⁻¹ := by positivity
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ B₀ + 1) hL_pos.le]

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
      (closedBall ((9 / 8 : ℂ) + ρ.im * I) ((1 / 2 : ℝ) / 2)) ρ : ℝ) :=
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
  obtain ⟨C₁, hC₁0, hpole0⟩ := exists_neg_re_logDeriv_riemannZeta_pole_le
  obtain ⟨B₂, hB₂, hsq2⟩ := exists_neg_re_logDeriv_sq_two_mul_le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set M : ℝ := 3 * C₁ / Real.log 3 + 4 * A + B₂
  have hM : 0 < M := by positivity
  set c : ℝ := min (1 / 32 * Real.log 3) (1 / (240 * M))
  refine ⟨c, by positivity, fun {q} _ χ hχ ρ hcase hρre hord ↦ ?_⟩
  have hL0 : χ.LFunction ρ = 0 := LFunction_eq_zero_of_pos_meromorphicOrderAt hχ hord
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
    calc δ ≤ c / L := hδ_le
      _ ≤ (1 / 32 * Real.log 3) / Real.log 3 := by gcongr
      _ = 1 / 32 := mul_div_cancel_right₀ _ hlog3.ne'
  set η : ℝ := 4 * δ
  set σ : ℝ := 1 + η
  have hpole : -(logDeriv riemannZeta σ).re ≤ η⁻¹ + C₁ := hpole0 (by positivity) (by linarith)
  have hzero_γ : -(logDeriv χ.LFunction (σ + γ * I)).re + (5 * δ)⁻¹ ≤ A * L := by
    simpa [show σ - ρ.re = 5 * δ by simp [σ, η, δ]; ring] using
      hret χ hχ (σ := σ) (by linarith) (by linarith) (by linarith) hL0
  have hzero_2γ := hsq2 χ (σ := σ) (γ := γ) (δ := δ) (by linarith) (by linarith) hδ0 hcase
  have h341 := χ.three_mul_re_logDeriv_riemannZeta_add_four_add_nonpos (σ := σ) (by linarith) γ
  have hC_log : C₁ ≤ C₁ / Real.log 3 * L := by
    calc C₁ = C₁ / Real.log 3 * Real.log 3 := (div_mul_cancel₀ _ hlog3.ne').symm
      _ ≤ C₁ / Real.log 3 * L := mul_le_mul_of_nonneg_left hlog_ge (div_nonneg hC₁0 hlog3.le)
  have hcomb : (120 * δ)⁻¹ ≤ M * L := by
    have halg : 4 * (5 * δ)⁻¹ - 3 * η⁻¹ - (24 * δ)⁻¹ = (120 * δ)⁻¹ := by
      simp only [η]; field_simp [hδ0.ne']; ring
    have hMeq : M * L = 3 * (C₁ / Real.log 3 * L) + 4 * (A * L) + B₂ * L := by simp only [M]; ring
    linarith
  rw [inv_le_iff_one_le_mul₀ (by positivity)] at hcomb
  have hδM : δ * L ≤ 1 / (240 * M) :=
    (le_div_iff₀ hL_pos).mp (hδ_le.trans (div_le_div_of_nonneg_right (min_le_right _ _) hL_pos.le))
  have hupper : 120 * δ * (M * L) ≤ 1 / 2 := by
    calc 120 * δ * (M * L) = 120 * M * (δ * L) := by ring
      _ ≤ 120 * M * (1 / (240 * M)) := mul_le_mul_of_nonneg_left hδM (by positivity)
      _ = 1 / 2 := by field_simp [hM.ne']; ring
  linarith

private theorem mem_closedBall_zero_of_im_lt {z : ℂ} (hz1 : z.re < 1) (hδ : 1 - z.re ≤ 1 / 96)
    (him : |z.im| < 6 * (1 - z.re)) :
    z ∈ closedBall ((9 / 8 : ℂ) + (0 : ℝ) * I) ((1 / 2 : ℝ) / 2) := by
  rw [mem_closedBall, dist_eq_norm]
  have heq : z - ((9 / 8 : ℂ) + (0 : ℝ) * I) = ((z.re - 9 / 8 : ℝ) : ℂ) + z.im * I :=
    Complex.ext (by simp) (by simp)
  rw [heq]
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
  have hρ_lt1 : ρ.re < 1 :=
    by_contra fun h ↦ LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hL0
  set γ : ℝ := ρ.im
  set δ : ℝ := 1 - ρ.re
  have hδ0 : 0 < δ := sub_pos.2 hρ_lt1
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
  set U0 : Set ℂ := closedBall ((9 / 8 : ℂ) + (0 : ℝ) * I) ((1 / 2 : ℝ) / 2)
  have hD₁ : (1 : ℝ) ≤ (MeromorphicOn.divisor χ.LFunction U0 ρ : ℝ) := mod_cast
    one_le_divisor_LFunction_of_eq_zero hχ 0 (mem_closedBall_zero_of_im_lt hρ_lt1 hδ_96 hγ_lt) hL0
  have hD₂ : (1 : ℝ) ≤ (MeromorphicOn.divisor χ.LFunction U0 (conj ρ) : ℝ) := mod_cast
    one_le_divisor_LFunction_of_eq_zero hχ 0
      (mem_closedBall_zero_of_im_lt (by simp; linarith) (by simp; linarith)
        (by simp; linarith)) hLconj
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
  obtain ⟨C₁, hC₁0, hpole0⟩ := exists_neg_re_logDeriv_riemannZeta_pole_le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set M : ℝ := C₁ / Real.log 3 + A
  have hM : 0 < M := by positivity
  set c : ℝ := min (1 / 96 * Real.log 3) (107 / (4920 * M))
  refine ⟨c, by positivity, fun {q} _ χ hχ hsq ρ hγ0 hγ_lt hρre hord ↦ ?_⟩
  have hL0 : χ.LFunction ρ = 0 := LFunction_eq_zero_of_pos_meromorphicOrderAt hχ hord
  have hρ_lt1 : ρ.re < 1 :=
    by_contra fun h ↦ LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hL0
  set δ : ℝ := 1 - ρ.re
  set L : ℝ := Real.log (q * (|ρ.im| + 3))
  have hδ0 : 0 < δ := sub_pos.2 hρ_lt1
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  have hlog_ge : Real.log 3 ≤ L := Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg ρ.im])
  have hL_pos : 0 < L := hlog3.trans_le hlog_ge
  have hδ_le : δ ≤ c / L := by linarith
  have hδ_96 : δ ≤ 1 / 96 := by
    have hc_le : c ≤ 1 / 96 * Real.log 3 := min_le_left _ _
    calc δ ≤ c / L := hδ_le
      _ ≤ (1 / 96 * Real.log 3) / Real.log 3 := by gcongr
      _ = 1 / 96 := mul_div_cancel_right₀ _ hlog3.ne'
  set η : ℝ := 12 * δ
  set σ : ℝ := 1 + η
  have hpair : -(logDeriv χ.LFunction σ).re + 2 * (13 / 205 * δ⁻¹) ≤ A * L :=
    hpair0 χ hχ hsq hγ0 hγ_lt hδ_96 hL0
  have hpole : -(logDeriv riemannZeta σ).re ≤ η⁻¹ + C₁ := hpole0 (by positivity) (by linarith)
  have h1χ := χ.re_logDeriv_riemannZeta_add_re_logDeriv_LFunction_nonpos (σ := σ) (by linarith)
  have hC_log : C₁ ≤ C₁ / Real.log 3 * L := by
    calc C₁ = C₁ / Real.log 3 * Real.log 3 := (div_mul_cancel₀ _ hlog3.ne').symm
      _ ≤ C₁ / Real.log 3 * L := mul_le_mul_of_nonneg_left hlog_ge (div_nonneg hC₁0 hlog3.le)
  have hcomb : 2 * (13 / 205 * δ⁻¹) - η⁻¹ ≤ M * L := by
    have _ : M * L = C₁ / Real.log 3 * L + A * L := by simp only [M]; ring
    linarith
  have halg : 2 * (13 / 205 * δ⁻¹) - η⁻¹ = 107 / 2460 * δ⁻¹ := by
    simp only [η]; field_simp [hδ0.ne']; ring
  rw [halg, mul_inv_le_iff₀ hδ0] at hcomb
  have hδM : δ * L ≤ 107 / (4920 * M) :=
    (le_div_iff₀ hL_pos).mp (hδ_le.trans (div_le_div_of_nonneg_right (min_le_right _ _) hL_pos.le))
  have hupper : M * L * δ ≤ 107 / 4920 := by
    calc M * L * δ = M * (δ * L) := by ring
      _ ≤ M * (107 / (4920 * M)) := mul_le_mul_of_nonneg_left hδM hM.le
      _ = 107 / 4920 := by field_simp [hM.ne']
  linarith

private theorem real_axis_two_weight_contradiction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {A C₁ δ : ℝ} (hC₁0 : 0 ≤ C₁) (hδ0 : 0 < δ) (hδ_16 : δ ≤ 1 / 16)
    (hδM : δ * Real.log (q * 3) ≤ 1 / (12 * (C₁ / Real.log 3 + A))) (hM : 0 < C₁ / Real.log 3 + A)
    (hpole0 : ∀ {η : ℝ}, 0 < η → η ≤ 1 → -(logDeriv riemannZeta ((1 + η : ℝ) : ℂ)).re ≤ η⁻¹ + C₁)
    (hret : -(logDeriv χ.LFunction ((1 + 2 * δ : ℝ) : ℂ)).re + 2 * (3 * δ)⁻¹ ≤
      A * Real.log (q * 3)) : False := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  set L : ℝ := Real.log (q * 3)
  have hlog_ge : Real.log 3 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  set η : ℝ := 2 * δ
  set σ : ℝ := 1 + η
  set M : ℝ := C₁ / Real.log 3 + A
  have hpole : -(logDeriv riemannZeta σ).re ≤ η⁻¹ + C₁ := hpole0 (by positivity) (by linarith)
  have h1χ := χ.re_logDeriv_riemannZeta_add_re_logDeriv_LFunction_nonpos (σ := σ) (by linarith)
  have hC_log : C₁ ≤ C₁ / Real.log 3 * L := by
    calc C₁ = C₁ / Real.log 3 * Real.log 3 := (div_mul_cancel₀ _ hlog3.ne').symm
      _ ≤ C₁ / Real.log 3 * L := mul_le_mul_of_nonneg_left hlog_ge (div_nonneg hC₁0 hlog3.le)
  have hcomb : 2 * (3 * δ)⁻¹ - η⁻¹ ≤ M * L := by
    have _ : M * L = C₁ / Real.log 3 * L + A * L := by simp only [M]; ring
    linarith
  have halg : 2 * (3 * δ)⁻¹ - η⁻¹ = (6 * δ)⁻¹ := by simp only [η]; field_simp [hδ0.ne']; ring
  rw [halg, inv_le_iff_one_le_mul₀ (by positivity)] at hcomb
  have hupper : 6 * δ * (M * L) ≤ 1 / 2 := by
    calc 6 * δ * (M * L) = 6 * M * (δ * L) := by ring
      _ ≤ 6 * M * (1 / (12 * M)) := mul_le_mul_of_nonneg_left hδM (by positivity)
      _ = 1 / 2 := by field_simp [hM.ne']; ring
  linarith

private theorem exists_meromorphicOrderAt_eq_one_of_im_eq_zero :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ ρ : ℂ, ρ.im = 0 → 1 - c / Real.log (q * 3) ≤ ρ.re →
        0 < meromorphicOrderAt χ.LFunction ρ → meromorphicOrderAt χ.LFunction ρ = 1 := by
  obtain ⟨A, hA, hLandau⟩ := exists_neg_re_logDeriv_LFunction_add_sum_le
  obtain ⟨C₁, hC₁0, hpole0⟩ := exists_neg_re_logDeriv_riemannZeta_pole_le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set M : ℝ := C₁ / Real.log 3 + A
  have hM : 0 < M := by positivity
  set c : ℝ := min (1 / 16 * Real.log 3) (1 / (12 * M))
  refine ⟨c, by positivity, fun {q} _ χ hχ ρ him hρre hord ↦ ?_⟩
  have hL0 : χ.LFunction ρ = 0 := LFunction_eq_zero_of_pos_meromorphicOrderAt hχ hord
  have hρ_lt1 : ρ.re < 1 :=
    by_contra fun h ↦ LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hL0
  set δ : ℝ := 1 - ρ.re
  set L : ℝ := Real.log (q * 3)
  have hδ0 : 0 < δ := sub_pos.2 hρ_lt1
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  have hlog_ge : Real.log 3 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hL_pos : 0 < L := hlog3.trans_le hlog_ge
  have hδ_le : δ ≤ c / L := by linarith
  have hδ_16 : δ ≤ 1 / 16 := by
    have hc_le : c ≤ 1 / 16 * Real.log 3 := min_le_left _ _
    calc δ ≤ c / L := hδ_le
      _ ≤ (1 / 16 * Real.log 3) / Real.log 3 := by gcongr
      _ = 1 / 16 := mul_div_cancel_right₀ _ hlog3.ne'
  set U0 : Set ℂ := closedBall ((9 / 8 : ℂ) + (0 : ℝ) * I) ((1 / 2 : ℝ) / 2)
  have hρ_mem : ρ ∈ U0 := by
    simpa [U0, him] using mem_closedBall_of_seven_div_eight_le_re hχ (by linarith) hL0
  have hDeq := coe_divisor_LFunction_eq hχ 0 hρ_mem
  have hD1 : 1 ≤ MeromorphicOn.divisor χ.LFunction U0 ρ :=
    one_le_divisor_LFunction_of_eq_zero hχ 0 hρ_mem hL0
  by_contra hne1
  have hD2 : 2 ≤ MeromorphicOn.divisor χ.LFunction U0 ρ := by
    have hneD : MeromorphicOn.divisor χ.LFunction U0 ρ ≠ 1 := fun h ↦ hne1 (by rw [← hDeq, h]; rfl)
    omega
  have h1 := hLandau χ hχ (σ := 1 + 2 * δ) (t := 0) (by linarith) (by linarith) {ρ}
  have hdiff : (((1 + 2 * δ : ℝ) : ℂ) + (0 : ℝ) * I) - ρ = ((3 * δ : ℝ) : ℂ) :=
    Complex.ext (by simp [δ]; ring) (by simp [him])
  rw [Finset.sum_singleton, hdiff, ← ofReal_inv, ofReal_re] at h1
  have hD2r : 2 * (3 * δ)⁻¹ ≤ (MeromorphicOn.divisor χ.LFunction U0 ρ : ℝ) * (3 * δ)⁻¹ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hD2) (by positivity)
  have hsum : -(logDeriv χ.LFunction (((1 + 2 * δ : ℝ) : ℂ) + (0 : ℝ) * I)).re + 2 * (3 * δ)⁻¹ ≤
      A * Real.log (q * (|(0 : ℝ)| + 3)) := by linarith
  simp only [ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at hsum
  have hδM : δ * L ≤ 1 / (12 * M) :=
    (le_div_iff₀ hL_pos).mp (hδ_le.trans (div_le_div_of_nonneg_right (min_le_right _ _) hL_pos.le))
  exact real_axis_two_weight_contradiction χ hC₁0 hδ0 hδ_16 hδM hM hpole0 hsum

private theorem exists_eq_of_im_eq_zero :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ ρ₁ ρ₂ : ℂ, ρ₁.im = 0 → ρ₂.im = 0 →
        1 - c / Real.log (q * 3) ≤ ρ₁.re → 1 - c / Real.log (q * 3) ≤ ρ₂.re →
        0 < meromorphicOrderAt χ.LFunction ρ₁ → 0 < meromorphicOrderAt χ.LFunction ρ₂ →
        ρ₁ = ρ₂ := by
  obtain ⟨A, hA, hLandau⟩ := exists_neg_re_logDeriv_LFunction_add_sum_le
  obtain ⟨C₁, hC₁0, hpole0⟩ := exists_neg_re_logDeriv_riemannZeta_pole_le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set M : ℝ := C₁ / Real.log 3 + A
  have hM : 0 < M := by positivity
  set c : ℝ := min (1 / 16 * Real.log 3) (1 / (12 * M))
  refine ⟨c, by positivity, fun {q} _ χ hχ ρ₁ ρ₂ him₁ him₂ hre₁ hre₂ hord₁ hord₂ ↦ ?_⟩
  by_contra hne
  have hL₁ : χ.LFunction ρ₁ = 0 := LFunction_eq_zero_of_pos_meromorphicOrderAt hχ hord₁
  have hL₂ : χ.LFunction ρ₂ = 0 := LFunction_eq_zero_of_pos_meromorphicOrderAt hχ hord₂
  have hlt₁ : ρ₁.re < 1 :=
    by_contra fun h ↦ LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hL₁
  set δ : ℝ := max (1 - ρ₁.re) (1 - ρ₂.re)
  set L : ℝ := Real.log (q * 3)
  have hδ0 : 0 < δ := lt_max_of_lt_left (sub_pos.2 hlt₁)
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  have hlog_ge : Real.log 3 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hL_pos : 0 < L := hlog3.trans_le hlog_ge
  have hδ_le : δ ≤ c / L := max_le (by linarith) (by linarith)
  have hδ_16 : δ ≤ 1 / 16 := by
    have hc_le : c ≤ 1 / 16 * Real.log 3 := min_le_left _ _
    calc δ ≤ c / L := hδ_le
      _ ≤ (1 / 16 * Real.log 3) / Real.log 3 := by gcongr
      _ = 1 / 16 := mul_div_cancel_right₀ _ hlog3.ne'
  set σ : ℝ := 1 + 2 * δ
  have hterm (ρ : ℂ) (him : ρ.im = 0) (hL0 : χ.LFunction ρ = 0) (hle : 1 - ρ.re ≤ δ) :
      (3 * δ)⁻¹ ≤ (MeromorphicOn.divisor χ.LFunction
        (closedBall ((9 / 8 : ℂ) + (0 : ℝ) * I) ((1 / 2 : ℝ) / 2)) ρ : ℝ) *
        ((((σ : ℂ) + (0 : ℝ) * I) - ρ)⁻¹).re := by
    have hlt : ρ.re < 1 :=
      by_contra fun h ↦ LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hL0
    have hmem : ρ ∈ closedBall ((9 / 8 : ℂ) + (0 : ℝ) * I) ((1 / 2 : ℝ) / 2) := by
      simpa [him] using mem_closedBall_of_seven_div_eight_le_re hχ (by linarith) hL0
    have hD1 := one_le_divisor_LFunction_of_eq_zero hχ 0 hmem hL0
    rw [show ((σ : ℂ) + (0 : ℝ) * I) - ρ = ((σ - ρ.re : ℝ) : ℂ) from
      Complex.ext (by simp) (by simp [him]), ← ofReal_inv, ofReal_re]
    have hinv : (3 * δ)⁻¹ ≤ (σ - ρ.re)⁻¹ := inv_anti₀ (by linarith) (by simp [σ]; linarith)
    exact hinv.trans
      (le_mul_of_one_le_left (inv_nonneg.2 (by simp [σ]; linarith)) (by exact_mod_cast hD1))
  have h1 := hLandau χ hχ (σ := σ) (t := 0) (by linarith) (by linarith) {ρ₁, ρ₂}
  rw [Finset.sum_pair hne] at h1
  have ht₁ := hterm ρ₁ him₁ hL₁ (le_max_left _ _)
  have ht₂ := hterm ρ₂ him₂ hL₂ (le_max_right _ _)
  have hsum : -(logDeriv χ.LFunction ((σ : ℂ) + (0 : ℝ) * I)).re + 2 * (3 * δ)⁻¹ ≤
      A * Real.log (q * (|(0 : ℝ)| + 3)) := by linarith
  simp only [ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at hsum
  have hδM : δ * L ≤ 1 / (12 * M) :=
    (le_div_iff₀ hL_pos).mp (hδ_le.trans (div_le_div_of_nonneg_right (min_le_right _ _) hL_pos.le))
  exact real_axis_two_weight_contradiction χ hC₁0 hδ0 hδ_16 hδM hM hpole0 hsum

private theorem not_pos_meromorphicOrderAt_trivChar {q : ℕ} [NeZero q] {ρ : ℂ} (hρ : 0 < ρ.re)
    (hζ : ρ ≠ 1 → riemannZeta ρ ≠ 0) :
    ¬ 0 < meromorphicOrderAt (1 : DirichletCharacter ℂ q).LFunction ρ := by
  intro hord
  have h1 : (1 : DirichletCharacter ℂ q) = changeLevel q.one_dvd (1 : DirichletCharacter ℂ 1) :=
    (changeLevel_one q.one_dvd).symm
  rw [h1, meromorphicOrderAt_LFunction_changeLevel _ q.one_dvd hρ, LFunction_modOne_eq] at hord
  rcases eq_or_ne ρ 1 with rfl | hρ1
  · rw [TauCeti.meromorphicOrderAt_riemannZeta_one] at hord
    exact absurd (WithTop.coe_lt_coe.1 hord) (by omega)
  · have ha : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ1
    rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.2 (hζ hρ1)] at hord
    exact lt_irrefl 0 hord

private theorem exists_dirichlet_zero_properties :
    ∃ c : ℝ, 0 < c ∧ c ≤ Real.log 3 / 2 ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ),
        1 - c / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re →
        0 < meromorphicOrderAt χ.LFunction ρ →
        ρ.im = 0 ∧ χ ^ 2 = 1 ∧ meromorphicOrderAt χ.LFunction ρ = 1 ∧ χ ≠ 1 := by
  obtain ⟨cζ, hcζ, hζ⟩ := riemannZeta_zeroFreeRegion
  obtain ⟨c₁, hc₁, hno_high⟩ := exists_not_pos_meromorphicOrderAt_of_sq_ne_one_or_im_ge
  obtain ⟨c₂, hc₂, hno_low⟩ := exists_not_pos_meromorphicOrderAt_of_im_lt
  obtain ⟨c₃, hc₃, hsimple⟩ := exists_meromorphicOrderAt_eq_one_of_im_eq_zero
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
  refine ⟨c, by positivity, hc_half, fun q _ χ ρ hρre hord ↦ ?_⟩
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  set L : ℝ := Real.log (q * (|ρ.im| + 3))
  have hlog_ge : Real.log 3 ≤ L := Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg ρ.im])
  have hlog_pos : 0 < L := hlog3.trans_le hlog_ge
  have hlift {c' : ℝ} (hc' : c ≤ c') : 1 - c' / L ≤ ρ.re := by
    have : c / L ≤ c' / L := by gcongr
    linarith
  have hρ_pos : 0 < ρ.re := by
    have hdiv : c / L ≤ (Real.log 3 / 2) / Real.log 3 := by gcongr
    have hval : (Real.log 3 / 2) / Real.log 3 = 1 / 2 := by field_simp [hlog3.ne']
    linarith
  have hχ : χ ≠ 1 := by
    rintro rfl
    refine not_pos_meromorphicOrderAt_trivChar hρ_pos (fun hρ1 ↦ hζ ρ hρ1 ?_) hord
    have hlog_q : Real.log (|ρ.im| + 3) ≤ L :=
      Real.log_le_log (by positivity) (by nlinarith [abs_nonneg ρ.im])
    have hlog_pos' : 0 < Real.log (|ρ.im| + 3) :=
      hlog3.trans_le (Real.log_le_log (by norm_num) (by linarith [abs_nonneg ρ.im]))
    have hdiv : c / L ≤ cζ / Real.log (|ρ.im| + 3) := by gcongr
    linarith
  have hsq : χ ^ 2 = 1 := by_contra fun hsq ↦ hno_high χ hχ ρ (.inl hsq) (hlift hc_1) hord
  have him : ρ.im = 0 := by
    by_contra him0
    exact (le_or_gt (6 * (1 - ρ.re)) |ρ.im|).elim
      (fun hge ↦ hno_high χ hχ ρ (.inr hge) (hlift hc_1) hord)
      (fun hlt ↦ hno_low χ hχ hsq ρ him0 hlt (hlift hc_2) hord)
  have hre3 : 1 - c₃ / Real.log (q * 3) ≤ ρ.re := by simpa [L, him] using hlift hc_3
  exact ⟨him, hsq, hsimple χ hχ ρ him hre3 hord, hχ⟩

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
  obtain ⟨c₀, hc₀, hc₀_half, hprops⟩ := exists_dirichlet_zero_properties
  obtain ⟨c₄, hc₄, huniq⟩ := exists_eq_of_im_eq_zero
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set c : ℝ := min c₀ c₄
  have hc_0 : c ≤ c₀ := min_le_left _ _
  have hc_4 : c ≤ c₄ := min_le_right _ _
  refine ⟨c, by positivity, hc_0.trans hc₀_half, fun q _ χ ↦ ?_⟩
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  have hlift (ρ : ℂ) (hre : 1 - c / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re) :
      1 - c₀ / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re := by
    have hlog_pos : 0 < Real.log (q * (|ρ.im| + 3)) :=
      hlog3.trans_le (Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg ρ.im]))
    have : c / Real.log (q * (|ρ.im| + 3)) ≤ c₀ / Real.log (q * (|ρ.im| + 3)) := by gcongr
    linarith
  refine ⟨fun ρ hre hord ↦ ?_, fun ρ₁ ρ₂ hre₁ hre₂ hord₁ hord₂ ↦ ?_⟩
  · obtain ⟨him, hsq, h1, -⟩ := hprops q χ ρ (hlift ρ hre) hord
    exact ⟨him, hsq, h1⟩
  · obtain ⟨him₁, -, -, hχ⟩ := hprops q χ ρ₁ (hlift ρ₁ hre₁) hord₁
    obtain ⟨him₂, -, -, -⟩ := hprops q χ ρ₂ (hlift ρ₂ hre₂) hord₂
    have hlog_q3 : 0 < Real.log (q * 3) :=
      hlog3.trans_le (Real.log_le_log (by norm_num) (by linarith))
    have hre₁' : 1 - c₄ / Real.log (q * 3) ≤ ρ₁.re := by
      rw [him₁, abs_zero, zero_add] at hre₁
      have : c / Real.log (q * 3) ≤ c₄ / Real.log (q * 3) := by gcongr
      linarith
    have hre₂' : 1 - c₄ / Real.log (q * 3) ≤ ρ₂.re := by
      rw [him₂, abs_zero, zero_add] at hre₂
      have : c / Real.log (q * 3) ≤ c₄ / Real.log (q * 3) := by gcongr
      linarith
    exact huniq χ hχ ρ₁ ρ₂ him₁ him₂ hre₁' hre₂' hord₁ hord₂

/-! ### Example -/

example : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ ^ 2 ≠ 1 → ∀ ρ : ℂ, 1 - c / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re → χ.LFunction ρ ≠ 0 := by
  obtain ⟨c, hc, -, hreg⟩ := dirichletLFunction_zeroFreeRegion
  refine ⟨c, hc, fun q _ χ hsq ρ hre hL0 ↦ ?_⟩
  have hχ : χ ≠ 1 := fun h1 ↦ hsq (by simp [h1])
  have ha : AnalyticAt ℂ χ.LFunction ρ :=
    ((differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ) ρ (mem_univ ρ)
  have hord : 0 < meromorphicOrderAt χ.LFunction ρ := by
    rw [ha.meromorphicOrderAt_eq]
    cases ho : analyticOrderAt χ.LFunction ρ with
    | top => simp
    | coe n =>
      have hn : n ≠ 0 := by simpa [ho] using ha.analyticOrderAt_ne_zero.2 hL0
      simpa using Nat.pos_of_ne_zero hn
  exact hsq ((hreg q χ).1 ρ hre hord).2.1

end TauCeti.LFunctions
