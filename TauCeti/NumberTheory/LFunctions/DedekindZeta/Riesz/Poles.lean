/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.RemainderMellin
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed
import TauCeti.NumberTheory.LFunctions.DedekindZeta.Nonvanishing

/-!
# Poles of the Dedekind zeta Riesz remainder Mellin expression

The first Riesz kernel changes a zero of `ζ_K` of multiplicity `m`, away from the origin,
into a simple pole with residue `m / (ρ * (1 - ρ))`. The main-term subtraction removes the
pole at `1`. On the open right half-plane the poles thus lie in the open critical strip,
and at real poles the residues are positive. This is the sign needed when combining
smoothed prime sums with nonnegative weights.
-/

public section

open Complex

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- Away from the origin, the poles of the Riesz remainder Mellin expression for `ζ_K`
are precisely the points where the continued zeta function has positive order. -/
@[simp] theorem meromorphicOrderAt_rieszRemainderMellin_dedekindZetaC_neg_iff {ρ : ℂ}
    (h₀ : ρ ≠ 0) :
    meromorphicOrderAt (rieszRemainderMellin (dedekindZetaC K)) ρ < 0 ↔
      0 < meromorphicOrderAt (dedekindZetaC K) ρ := by
  rcases eq_or_ne ρ 1 with rfl | h₁
  · have ha := (meromorphic_dedekindZetaC K).analyticAt_rieszRemainderMellin_one
    simp [ha.meromorphicOrderAt_nonneg.not_gt, meromorphicOrderAt_dedekindZetaC_one]
  · rw [(meromorphic_dedekindZetaC K).meromorphicOrderAt_rieszRemainderMellin_neg_iff h₀ h₁
      (meromorphicOrderAt_dedekindZetaC_ne_top K ρ),
      lt_iff_le_and_ne]
    exact ⟨fun h ↦ ⟨(analyticAt_dedekindZetaC K h₁).meromorphicOrderAt_nonneg, h.symm⟩,
      fun h ↦ h.2.symm⟩

/-- At a nonzero zero `ρ` of `ζ_K`, the Riesz remainder Mellin expression has a simple pole
whose residue is the zero multiplicity divided by `ρ * (1 - ρ)`. -/
theorem rieszRemainderMellin_dedekindZetaC_simplePole {ρ : ℂ} (h₀ : ρ ≠ 0)
    (hρ : 0 < meromorphicOrderAt (dedekindZetaC K) ρ) :
    meromorphicOrderAt (rieszRemainderMellin (dedekindZetaC K)) ρ = -1 ∧
      meromorphicTrailingCoeffAt (rieszRemainderMellin (dedekindZetaC K)) ρ =
        ((meromorphicOrderAt (dedekindZetaC K) ρ).untop₀ : ℂ) / (ρ * (1 - ρ)) := by
  have h₁ : ρ ≠ 1 := by
    rintro rfl
    rw [meromorphicOrderAt_dedekindZetaC_one] at hρ
    exact (WithTop.coe_lt_coe.mp hρ).not_ge (by decide)
  lift meromorphicOrderAt (dedekindZetaC K) ρ to ℤ using
    meromorphicOrderAt_dedekindZetaC_ne_top K ρ with m hm
  exact (meromorphic_dedekindZetaC K).rieszRemainderMellin_simplePole h₀ h₁ hm.symm
    (WithTop.coe_lt_coe.mp hρ).ne'

/-- The Riesz remainder Mellin expression for `ζ_K` is holomorphic on `Re s ≥ 1`,
including the removed singularity at `1`. -/
theorem analyticAt_rieszRemainderMellin_dedekindZetaC_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (rieszRemainderMellin (dedekindZetaC K)) s := by
  rcases eq_or_ne s 1 with rfl | h₁
  · exact (meromorphic_dedekindZetaC K).analyticAt_rieszRemainderMellin_one
  · have h₀ : s ≠ 0 := by rintro rfl; norm_num at hs
    exact ((meromorphic_dedekindZetaC K).rieszRemainderMellin_eq_and_analyticAt h₀ h₁
      (analyticAt_dedekindZetaC K h₁) (dedekindZetaC_ne_zero_of_one_le_re K hs h₁)).2

/-- Every real pole of the Dedekind zeta Riesz remainder Mellin expression in the open right
half-plane has positive real residue. -/
theorem exists_pos_meromorphicTrailingCoeffAt_rieszRemainderMellin_dedekindZetaC {β : ℝ}
    (hβ : 0 < β) (hpole : meromorphicOrderAt (rieszRemainderMellin (dedekindZetaC K)) β < 0) :
    ∃ c : ℝ, 0 < c ∧
      meromorphicTrailingCoeffAt (rieszRemainderMellin (dedekindZetaC K)) β = (c : ℂ) := by
  have h₀ : (β : ℂ) ≠ 0 := ofReal_ne_zero.mpr hβ.ne'
  have hβ₁ : β < 1 := lt_of_not_ge fun h ↦
    hpole.not_ge (analyticAt_rieszRemainderMellin_dedekindZetaC_of_one_le_re K
      (by simpa using h)).meromorphicOrderAt_nonneg
  have hzero := (meromorphicOrderAt_rieszRemainderMellin_dedekindZetaC_neg_iff K h₀).mp hpole
  rw [(rieszRemainderMellin_dedekindZetaC_simplePole K h₀ hzero).2]
  lift meromorphicOrderAt (dedekindZetaC K) (β : ℂ) to ℤ using
    meromorphicOrderAt_dedekindZetaC_ne_top K β with m
  have hm : 0 < m := WithTop.coe_lt_coe.mp hzero
  exact ⟨(m : ℝ) / (β * (1 - β)), by positivity, by push_cast; rfl⟩

end TauCeti.LFunctions
