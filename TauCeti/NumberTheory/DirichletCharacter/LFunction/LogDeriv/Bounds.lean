/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import TauCeti.Analysis.Complex.LocalLogDeriv
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic
import TauCeti.NumberTheory.LSeries.DirichletEulerLog

/-!
# Landau upper bounds for the logarithmic derivative of Dirichlet `L`-functions

For a modulus `q ≥ 1` and a nonprincipal Dirichlet character `χ ≠ 1` modulo `q`, Landau's local
logarithmic-derivative lemma applied on the disc of radius `1 / 2` centred at `9 / 8 + i t` gives
the uniform signed upper bound `-(logDeriv χ.LFunction s).re ≤ A * log (q * (|Im s| + 3))` with an
absolute constant `A > 0`:

* For `1 ≤ σ ≤ 9 / 8`, `TauCeti.exists_neg_re_logDeriv_LFunction_add_sum_le` bounds
  `-(logDeriv χ.LFunction (σ + t * I)).re` while retaining the divisor-weighted zero terms over
  any finite set `S` (only zeros in `S ∩ closedBall ((9 / 8 : ℝ) + t * I) (1 / 4)` contribute).
* Extending across `Re s > 9 / 8` via the Dirichlet series at `9 / 8` drops the retained-zero sum
  and yields the half-plane bound `TauCeti.exists_neg_re_logDeriv_LFunction_le` across
  all `1 ≤ Re s`.
* Combining the local single-zero term on `1 ≤ σ ≤ 9 / 8` with `7 / 8 ≤ ρ.re` and absorbing the
  bounded term `(σ - ρ.re)⁻¹ ≤ 8` into the half-plane bound outside that range yields
  `TauCeti.exists_neg_re_logDeriv_LFunction_add_sub_inv_le` for all `σ ≥ 1` and all
  zeros `ρ` of `χ.LFunction`.

## Main results

* `TauCeti.exists_neg_re_logDeriv_LFunction_add_sum_le`: local retained-zero bound on
  `1 ≤ σ ≤ 9 / 8` for `S ∩ closedBall ((9 / 8 : ℝ) + t * I) (1 / 4)`.
* `TauCeti.exists_neg_re_logDeriv_LFunction_le`: half-plane bound on `1 ≤ Re s`
  without retained zero terms.
* `TauCeti.exists_neg_re_logDeriv_LFunction_add_sub_inv_le`: uniform single-zero bound
  for all `1 ≤ σ` and every zero `ρ` of `χ.LFunction`.

## References

* Michael Stoll, David Loeffler, and Terence Tao,
  `DirichletCharacter.LFunction_ne_zero_of_one_le_re` in
  `Mathlib.NumberTheory.LSeries.Nonvanishing`.
-/

public section

open DirichletCharacter

namespace TauCeti

/-- **Retained-zero Landau upper bound for `-Re (L′/L)` of a nonprincipal character.** There is an
absolute constant `A > 0` such that for `χ ≠ 1` modulo `q ≥ 1`, `1 ≤ σ ≤ 9 / 8`, and any finite
set `S : Finset ℂ`, retaining the divisor-weighted zero terms over `S` (where only zeros in
`S ∩ closedBall ((9 / 8 : ℝ) + t * I) (1 / 4)` contribute) gives an
`A * Real.log (q * (|t| + 3))` upper bound. -/
theorem exists_neg_re_logDeriv_LFunction_add_sum_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {σ t : ℝ}, 1 ≤ σ → σ ≤ 9 / 8 → ∀ S : Finset ℂ,
        -(logDeriv χ.LFunction (σ + t * Complex.I)).re +
            ∑ ρ ∈ S, (MeromorphicOn.divisor χ.LFunction
              (Metric.closedBall ((9 / 8 : ℝ) + t * Complex.I) ((1 / 2 : ℝ) / 2)) ρ : ℝ) *
              ((((σ : ℂ) + t * Complex.I) - ρ)⁻¹).re ≤
          A * Real.log (q * (|t| + 3)) := by
  obtain ⟨A, hA, hLandau⟩ :=
    TauCeti.exists_neg_re_logDeriv_add_sum_divisor_half_le_ofReal_add_mul_I
      (x₀ := 9 / 8) (R := 1 / 2) (b := Real.exp (-(riemannZeta (9 / 8 : ℝ)).re))
      (c := 2) (K₀ := 3) (a := 3) (by norm_num) (Real.exp_pos _) (by norm_num) (by norm_num)
  refine ⟨A, hA, fun {q} _ χ hχ {σ t} hσ1 hσ2 S ↦ ?_⟩
  have hf : AnalyticOnNhd ℂ χ.LFunction
      (Metric.closedBall ((9 / 8 : ℝ) + t * Complex.I) (1 / 2)) :=
    fun z _ ↦ (differentiable_LFunction hχ).analyticAt z
  have hb₀ : Real.exp (-(riemannZeta (9 / 8 : ℝ)).re) ≤
      ‖χ.LFunction ((9 / 8 : ℝ) + t * Complex.I)‖ := by
    simpa using χ.exp_neg_re_riemannZeta_le_norm_LFunction
      (s := (9 / 8 : ℝ) + t * Complex.I) (by simp; norm_num)
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  refine hLandau hf hb₀ (fun w _ hwre hwn ↦ ?_) (by linarith) hσ2
    (LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simp [hσ1])) S
    (fun ρ _ _ h0 ↦ (χ.re_lt_one_of_LFunction_eq_zero (.inr hχ) h0).le.trans (by simp [hσ1]))
    (by nlinarith [abs_nonneg t])
  norm_num at hwre
  calc ‖χ.LFunction w‖ ≤ (q : ℝ) * ‖w‖ / w.re :=
      χ.norm_LFunction_le_level_mul_norm_div_re hχ (by linarith)
    _ ≤ (q : ℝ) * (|t| + 3) / (5 / 8) := by gcongr
    _ ≤ 2 * ((q : ℝ) * (|t| + 3)) := by
      have hq0 : 0 ≤ (q : ℝ) * (|t| + 3) := by positivity
      linarith

/-- **Upper bound for `-Re (L′/L)` of a nonprincipal character across `1 ≤ Re s`.** There is an
absolute constant `A > 0` such that
`-(logDeriv χ.LFunction s).re ≤ A * Real.log (q * (|s.im| + 3))` for every modulus `q ≥ 1`, every
`χ ≠ 1` modulo `q`, and every `s : ℂ` with `1 ≤ s.re` (with no retained-zero sum). -/
theorem exists_neg_re_logDeriv_LFunction_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {s : ℂ}, 1 ≤ s.re →
        -(logDeriv χ.LFunction s).re ≤ A * Real.log (q * (|s.im| + 3)) := by
  obtain ⟨A₀, hA₀, h⟩ := exists_neg_re_logDeriv_LFunction_add_sum_le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let σ₀ : ℝ := 9 / 8
  refine ⟨max A₀ (-(logDeriv riemannZeta σ₀).re / Real.log 3), lt_max_of_lt_left hA₀,
    fun {q} _ χ hχ {s} hs ↦ ?_⟩
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  exact χ.neg_re_logDeriv_LFunction_le_max_mul_of_bound_on_left (σ₀ := σ₀) (by norm_num [σ₀]) hlog3
    (Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg s.im])) fun hs9 ↦ by
      simpa [Complex.re_add_im s] using h χ hχ (t := s.im) hs hs9 ∅

/-- **Single-zero Landau upper bound for `-Re (L′/L)` of a nonprincipal character.** There is an
absolute constant `A > 0` such that for every modulus `q ≥ 1`, every nonprincipal character
`χ ≠ 1` modulo `q`, every `σ ≥ 1`, and every zero `ρ` of `χ.LFunction`,
`-(logDeriv χ.LFunction (σ + ρ.im * I)).re + (σ - ρ.re)⁻¹ ≤ A * Real.log (q * (|ρ.im| + 3))`. -/
theorem exists_neg_re_logDeriv_LFunction_add_sub_inv_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {σ : ℝ} {ρ : ℂ}, 1 ≤ σ → χ.LFunction ρ = 0 →
        -(logDeriv χ.LFunction (σ + ρ.im * Complex.I)).re + (σ - ρ.re)⁻¹ ≤
          A * Real.log (q * (|ρ.im| + 3)) := by
  obtain ⟨A₁, hA₁, hsum⟩ := exists_neg_re_logDeriv_LFunction_add_sum_le
  obtain ⟨A₂, _, hle⟩ := exists_neg_re_logDeriv_LFunction_le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨max A₁ (A₂ + (1 / 8)⁻¹ / Real.log 3), lt_max_of_lt_left hA₁,
    fun {q} _ χ hχ {σ ρ} hσ1 hL0 ↦ ?_⟩
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
  have hρ_lt1 : ρ.re < 1 := χ.re_lt_one_of_LFunction_eq_zero (.inr hχ) hL0
  exact TauCeti.neg_re_logDeriv_add_sub_inv_le_max_mul
    (f := χ.LFunction) (ρ := ρ) (σ₁ := 1) (σ₀ := 9 / 8) (σ := σ) (r := (1 / 2 : ℝ) / 2)
    (d := 1 / 8) (A₁ := A₁) (A₂ := A₂) (L₀ := Real.log 3) (L := Real.log (q * (|ρ.im| + 3)))
    hσ1 (by norm_num) (by norm_num) (by norm_num) hlog3
    (Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg ρ.im]))
    (fun z _ ↦ (differentiable_LFunction hχ).analyticAt z)
    (LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simp; norm_num)) hL0 hρ_lt1.le
    (fun hσ9 ↦ hsum χ hχ hσ1 hσ9 {ρ})
    (by simpa using hle χ hχ (s := σ + ρ.im * Complex.I) (by simp [hσ1]))

end TauCeti
