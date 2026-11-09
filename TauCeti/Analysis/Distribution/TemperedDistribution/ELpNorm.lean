/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# The `Lᵖ` norm of a tempered distribution

For `1 ≤ p ≤ ∞`, the extended `Lᵖ` norm of a tempered distribution `u` is `‖g‖_p` when `u` is the
tempered distribution of a function `g ∈ Lᵖ`, and `∞` otherwise. The function `g` is unique when it
exists (`MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot`), so this extends the norm of
`Lᵖ` to all of `𝓢'(E, F)`. It is an extended norm: it vanishes exactly at `0`, is subadditive and
is homogeneous, and it is finite exactly on the image of `Lᵖ`.

This lets `Lᵖ` bounds be stated for distributions that are not known in advance to be functions,
as in the definition of Besov spaces, where the `Lᵖ` norms of the Littlewood–Paley blocks of an
arbitrary tempered distribution are measured.

## Main declarations

* `TemperedDistribution.eLpNorm`: the extended `Lᵖ` norm of a tempered distribution.
* `TemperedDistribution.eLpNorm_coe`: on the image of `Lᵖ`, it is the norm of `Lᵖ`.
* `TemperedDistribution.eLpNorm_lt_top_iff`: it is finite exactly on the image of `Lᵖ`.
* `TemperedDistribution.eLpNorm_eq_zero_iff`, `TemperedDistribution.eLpNorm_add_le`,
  `TemperedDistribution.eLpNorm_sum_le`, `TemperedDistribution.eLpNorm_smul`: it is an extended
  norm.
-/

public section

noncomputable section

open MeasureTheory hiding eLpNorm
open scoped ENNReal SchwartzMap

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The **extended `Lᵖ` norm of a tempered distribution**: `‖g‖_p` if `u` is the tempered
distribution of `g ∈ Lᵖ`, and `∞` if `u` is not given by an `Lᵖ` function. -/
def eLpNorm (u : 𝓢'(E, F)) (p : ℝ≥0∞) [Fact (1 ≤ p)] : ℝ≥0∞ :=
  ⨅ (g : Lp F p (volume : Measure E)) (_ : (g : 𝓢'(E, F)) = u), ‖g‖ₑ

/-- The tempered distribution of an `Lᵖ` function determines the function. -/
private theorem coe_injective :
    Function.Injective fun g : Lp F p (volume : Measure E) ↦ (g : 𝓢'(E, F)) :=
  LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := F) (μ := volume))

/-- The tempered distribution of a sum of `Lᵖ` functions is the sum of their distributions. -/
private theorem coe_add (g h : Lp F p (volume : Measure E)) :
    ((g + h : Lp F p (volume : Measure E)) : 𝓢'(E, F)) = g + h :=
  map_add (Lp.toTemperedDistributionCLM F volume p) g h

/-- The tempered distribution of a multiple of an `Lᵖ` function is the multiple of its
distribution. -/
private theorem coe_smul (c : ℂ) (g : Lp F p (volume : Measure E)) :
    ((c • g : Lp F p (volume : Measure E)) : 𝓢'(E, F)) = c • (g : 𝓢'(E, F)) :=
  map_smul (Lp.toTemperedDistributionCLM F volume p) c g

/-- On the tempered distribution of an `Lᵖ` function, the extended `Lᵖ` norm is the norm of the
function. -/
@[simp]
theorem eLpNorm_coe (g : Lp F p (volume : Measure E)) : eLpNorm (g : 𝓢'(E, F)) p = ‖g‖ₑ :=
  le_antisymm (iInf_le_of_le g (iInf_le _ rfl))
    (le_iInf₂ fun _ h ↦ (congrArg _ (coe_injective h)).ge)

/-- The extended `Lᵖ` norm of a tempered distribution is finite exactly when the distribution is
given by an `Lᵖ` function. -/
theorem eLpNorm_lt_top_iff {u : 𝓢'(E, F)} :
    eLpNorm u p < ∞ ↔ ∃ g : Lp F p (volume : Measure E), u = g := by
  refine ⟨fun hu ↦ ?_, fun ⟨g, hg⟩ ↦ hg ▸ (eLpNorm_coe g).trans_lt enorm_lt_top⟩
  by_contra! h
  refine hu.ne (iInf₂_eq_top.2 fun g hg ↦ (h g hg.symm).elim)

/-- A tempered distribution that is not given by an `Lᵖ` function has infinite `Lᵖ` norm. -/
theorem eLpNorm_eq_top {u : 𝓢'(E, F)} (hu : ∀ g : Lp F p (volume : Measure E), u ≠ g) :
    eLpNorm u p = ∞ :=
  not_lt_top_iff.1 fun h ↦ (eLpNorm_lt_top_iff.1 h).elim fun g hg ↦ hu g hg

@[simp]
theorem eLpNorm_zero : eLpNorm (0 : 𝓢'(E, F)) p = 0 := by
  have h := eLpNorm_coe (F := F) (0 : Lp F p (volume : Measure E))
  rwa [enorm_zero, ← Lp.toTemperedDistributionCLM_apply, map_zero] at h

/-- The extended `Lᵖ` norm of a tempered distribution vanishes only at `0`. -/
@[simp]
theorem eLpNorm_eq_zero_iff {u : 𝓢'(E, F)} : eLpNorm u p = 0 ↔ u = 0 := by
  refine ⟨fun hu ↦ ?_, by rintro rfl; exact eLpNorm_zero⟩
  obtain ⟨g, rfl⟩ := eLpNorm_lt_top_iff.1 (hu.trans_lt ENNReal.zero_lt_top)
  rw [eLpNorm_coe, enorm_eq_zero] at hu
  rw [hu, ← Lp.toTemperedDistributionCLM_apply, map_zero]

/-- The extended `Lᵖ` norm of a tempered distribution is subadditive. -/
theorem eLpNorm_add_le (u v : 𝓢'(E, F)) : eLpNorm (u + v) p ≤ eLpNorm u p + eLpNorm v p := by
  by_cases hu : eLpNorm u p = ∞
  · simp [hu]
  by_cases hv : eLpNorm v p = ∞
  · simp [hv]
  obtain ⟨g, rfl⟩ := eLpNorm_lt_top_iff.1 (lt_top_iff_ne_top.2 hu)
  obtain ⟨h, rfl⟩ := eLpNorm_lt_top_iff.1 (lt_top_iff_ne_top.2 hv)
  rw [← coe_add, eLpNorm_coe, eLpNorm_coe, eLpNorm_coe]
  exact enorm_add_le g h

/-- The extended `Lᵖ` norm of a finite sum of tempered distributions is at most the sum of their
extended `Lᵖ` norms. -/
theorem eLpNorm_sum_le {ι : Type*} (s : Finset ι) (u : ι → 𝓢'(E, F)) :
    eLpNorm (∑ i ∈ s, u i) p ≤ ∑ i ∈ s, eLpNorm (u i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (eLpNorm_add_le _ _).trans (by gcongr)

/-- The extended `Lᵖ` norm of a tempered distribution is homogeneous. -/
theorem eLpNorm_smul (c : ℂ) (u : 𝓢'(E, F)) : eLpNorm (c • u) p = ‖c‖ₑ * eLpNorm u p := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  by_cases hu : ∃ g : Lp F p (volume : Measure E), u = g
  · obtain ⟨g, rfl⟩ := hu
    rw [← coe_smul, eLpNorm_coe, eLpNorm_coe, enorm_smul]
  · push Not at hu
    rw [eLpNorm_eq_top hu, ENNReal.mul_top (enorm_ne_zero.2 hc)]
    refine eLpNorm_eq_top fun g hg ↦ hu (c⁻¹ • g) ?_
    rw [coe_smul, ← hg, smul_smul, inv_mul_cancel₀ hc, one_smul]

@[simp]
theorem eLpNorm_neg (u : 𝓢'(E, F)) : eLpNorm (-u) p = eLpNorm u p := by
  simpa using eLpNorm_smul (p := p) (-1 : ℂ) u

end TemperedDistribution
