/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.LFunctions.Zeros.ZeroFreeRegion.Dirichlet

/-!
# Separating an exceptional Dirichlet zero at every height

In the character prime number theorem (Iwaniec–Kowalski, *Analytic Number Theory*,
Theorem 5.27), the exceptional main term must not depend on the truncation height of
the explicit formula. We select the possible simple real zero using a window scaled
by the logarithm of the modulus alone. Every other zero up to height `T` satisfies
a uniform real-part bound scaled by `log (q * (T + 2))`.
-/

public section

open Complex

namespace TauCeti.LFunctions

-- The loss of a factor of two covers the change from `+ 3` in the zero-free region
-- to `+ 2` in the height estimates for the explicit formula.
private theorem mem_classical_region_of_height {q c T : ℝ} {ρ : ℂ} (hq : 1 ≤ q) (hc : 0 ≤ c)
    (hT : |ρ.im| ≤ T) (hre : 1 - c / Real.log (q * (T + 2)) ≤ ρ.re) :
    1 - (2 * c) / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re := by
  have hT₀ : 0 ≤ T := (abs_nonneg _).trans hT
  have h : q * (|ρ.im| + 3) ≤ (q * (T + 2)) * (q * (T + 2)) := by
    calc
      _ ≤ q * (T + 3) := by gcongr
      _ ≤ q * ((T + 2) * (T + 2)) := by gcongr; nlinarith
      _ = (q * (T + 2)) * (T + 2) := by ring
      _ ≤ _ := by gcongr; nlinarith
  have hp : 1 < q * (|ρ.im| + 3) := by nlinarith [abs_nonneg ρ.im]
  have hb : 1 < q * (T + 2) := by nlinarith
  have hb₀ : q * (T + 2) ≠ 0 := ne_of_gt (zero_lt_one.trans hb)
  have hlog : Real.log (q * (|ρ.im| + 3)) ≤ 2 * Real.log (q * (T + 2)) := by
    simpa only [Real.log_mul hb₀ hb₀, two_mul] using Real.log_le_log (zero_lt_one.trans hp) h
  have hdiv : c / Real.log (q * (T + 2)) ≤ (2 * c) / Real.log (q * (|ρ.im| + 3)) := by
    rw [div_le_div_iff₀ (Real.log_pos hb) (Real.log_pos hp)]
    nlinarith [mul_le_mul_of_nonneg_left hlog hc]
  linarith

private theorem mem_classical_region_of_exceptional_window {q c β : ℝ} (hq : 3 ≤ q)
    (hc : 0 ≤ c) (hβ : 1 - c / Real.log q < β) :
    1 - (2 * c) / Real.log (q * 3) ≤ β := by
  have hq₀ : 0 < q := by linarith
  have hlog : 0 < Real.log (q * 3) := Real.log_pos (by linarith)
  have hcomp : Real.log (q * 3) ≤ 2 * Real.log q := by
    have h := Real.log_le_log (by positivity : 0 < q * 3)
      (mul_le_mul_of_nonneg_left hq hq₀.le)
    simpa only [Real.log_mul hq₀.ne' hq₀.ne', two_mul] using h
  have hdiv : c / Real.log q ≤ (2 * c) / Real.log (q * 3) := by
    rw [div_le_div_iff₀ (Real.log_pos (by linarith)) hlog]
    nlinarith [mul_le_mul_of_nonneg_left hcomp hc]
  linarith

/-- The possible exceptional zero of a nonprincipal Dirichlet character is determined by the
real window `(1 - c / log q, 1)`, independently of any height cutoff. It is simple, belongs to a
real character, and exceeds `1/2`. Every other zero through height `T` has real part at most
`1 - c / log (q * (T + 2))`. The same `c` works for all moduli, including imprimitive
characters. -/
theorem exists_exceptionalZero_split :
    ∃ c : ℝ, 0 < c ∧ c ≤ Real.log 3 / 2 ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ∃ e : Option ℝ,
          (∀ β : ℝ, e = some β ↔ 1 - c / Real.log q < β ∧ χ.LFunction β = 0) ∧
          (∀ β : ℝ, e = some β → χ ^ 2 = 1 ∧ 1 / 2 < β ∧ β < 1 ∧
            analyticOrderNatAt χ.LFunction β = 1) ∧
          ∀ (T : ℝ) (ρ : ℂ), |ρ.im| ≤ T → χ.LFunction ρ = 0 →
            e.map Complex.ofReal ≠ some ρ → ρ.re ≤ 1 - c / Real.log (q * (T + 2)) := by
  obtain ⟨a, ha, ha₃, hreg⟩ := dirichletLFunction_zeroFreeRegion
  let c := a / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hca : 2 * c = a := by dsimp [c]; ring
  refine ⟨c, hc, by linarith, fun q _ χ hχ ↦ ?_⟩
  have hq : (3 : ℝ) ≤ q := by exact_mod_cast DirichletCharacter.three_le_level_of_ne_one hχ
  have hq₀ : (0 : ℝ) < q := by linarith
  have hqlog : 0 < Real.log q := Real.log_pos (by linarith)
  let P (β : ℝ) : Prop := 1 - c / Real.log q < β ∧ χ.LFunction β = 0
  have hord {ρ : ℂ} (hz : χ.LFunction ρ = 0) : 0 < meromorphicOrderAt χ.LFunction ρ :=
    (DirichletCharacter.meromorphicOrderAt_LFunction_pos_iff χ).mpr ⟨hz, Or.inr hχ⟩
  have hmem {β : ℝ} (hβ : P β) :
      1 - a / Real.log (q * (|(β : ℂ).im| + 3)) ≤ (β : ℂ).re := by
    simpa [← hca] using mem_classical_region_of_exceptional_window hq hc.le hβ.1
  have huniq {β γ : ℝ} (hβ : P β) (hγ : P γ) : β = γ :=
    Complex.ofReal_injective ((hreg q χ).2 _ _ (hmem hβ) (hmem hγ) (hord hβ.2) (hord hγ.2))
  classical
  have hex : ∃ e : Option ℝ, ∀ β : ℝ, e = some β ↔ P β := by
    by_cases h : ∃ β, P β
    · obtain ⟨β, hβ⟩ := h
      exact ⟨some β, fun γ ↦ ⟨fun he ↦ (Option.some.inj he) ▸ hβ,
        fun hγ ↦ congrArg some (huniq hβ hγ)⟩⟩
    · exact ⟨none, fun β ↦ ⟨by simp, fun hβ ↦ (h ⟨β, hβ⟩).elim⟩⟩
  obtain ⟨e, he⟩ := hex
  refine ⟨e, he, ?_, ?_⟩
  · intro β hb
    have hβ := (he β).mp hb
    obtain ⟨-, hsq, hm⟩ := (hreg q χ).1 _ (hmem hβ) (hord hβ.2)
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hq
    have hhalf : c / Real.log q ≤ 1 / 2 := by rw [div_le_iff₀ hqlog]; linarith
    refine ⟨hsq, by linarith [hβ.1], lt_of_not_ge fun hre ↦ ?_, ?_⟩
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simpa using hre) hβ.2
    · exact (DirichletCharacter.meromorphicOrderAt_LFunction_eq_natCast_iff χ (n := 1)
        one_ne_zero).mp (by simpa using hm)
  · intro T ρ hT hz hexcl
    by_contra! hr
    have hregion := mem_classical_region_of_height (le_trans (by norm_num) hq) hc.le hT hr.le
    rw [hca] at hregion
    have him := ((hreg q χ).1 ρ hregion (hord hz)).1
    have hT₀ : 0 ≤ T := (abs_nonneg _).trans hT
    have hρ : (ρ.re : ℂ) = ρ := Complex.ext (by simp) (by simp [him])
    have hlog : Real.log (q : ℝ) ≤ Real.log (q * (T + 2)) :=
      Real.log_le_log hq₀ (by nlinarith)
    have hdiv := div_le_div_of_nonneg_left hc.le hqlog hlog
    have hb : P ρ.re := ⟨by linarith, by rwa [hρ]⟩
    exact hexcl (by rw [(he _).mpr hb, Option.map_some, hρ])

end TauCeti.LFunctions
