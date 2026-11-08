/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.ExitExhaustion
public import TauCeti.Probability.BrownianMotion.Geometric

/-!
# Expanding spot-domain exits

`TauCeti.Probability.spotExitTime S n` is the first exit of the asset process `S` from
`(1 / (n + 1), n + 1)`. These times increase with `n` and tend to infinity along every
strictly positive continuous path. In particular, they exhaust every finite horizon almost
surely for geometric Brownian motion with positive initial spot, including zero volatility.

The result supplies the pathwise exhaustion needed when removing bounded-spot localization
from pricing identities. No stochastic integral or stopped pricing identity is asserted.
The stopping-time property requires separate hypotheses on path versions and adaptation;
almost-sure continuity alone is not used to claim literal stopping on a raw filtration.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §6.4, for localization in the Black–Scholes pricing argument.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal ENNReal

namespace TauCeti.Probability

variable {Ω : Type*} {S : ℝ≥0 → Ω → ℝ} {ω : Ω}

/-- The first exit of a spot process from `(1 / (n + 1), n + 1)`, with infinity when there
is no exit. The index shift avoids a zero denominator. -/
def spotExitTime (S : ℝ≥0 → Ω → ℝ) (n : ℕ) : Ω → WithTop ℝ≥0 :=
  hittingAfter S (Ioo ((n + 1 : ℝ)⁻¹) (n + 1))ᶜ 0

/-- `spotExitTime` is the native first hitting time of the complement of the spot domain. -/
theorem spotExitTime_def (S : ℝ≥0 → Ω → ℝ) (n : ℕ) :
    spotExitTime S n = hittingAfter S (Ioo ((n + 1 : ℝ)⁻¹) (n + 1))ᶜ 0 := (rfl)

/-- Exit strictly before a finite horizon means that the path leaves the open spot domain
at some time strictly before that horizon. This characterization needs no continuity. -/
@[simp]
theorem spotExitTime_lt_iff {n : ℕ} {T : ℝ≥0} :
    spotExitTime S n ω < (T : ℝ≥0∞) ↔
      ∃ t ∈ Ico (0 : ℝ≥0) T, S t ω ≤ (n + 1 : ℝ)⁻¹ ∨ (n + 1 : ℝ) ≤ S t ω := by
  rw [spotExitTime_def, ← ENNReal.some_eq_coe' T, hittingAfter_lt_iff (i := T)]
  simp only [mem_compl_iff, mem_Ioo, not_and_or, not_lt]

/-- There is no exit exactly when the whole path stays in the open spot domain. -/
@[simp]
theorem spotExitTime_eq_top_iff {n : ℕ} :
    spotExitTime S n ω = ⊤ ↔ ∀ t, S t ω ∈ Ioo ((n + 1 : ℝ)⁻¹) (n + 1) := by
  simp [spotExitTime_def, hittingAfter_eq_top_iff]

/-- The first domain is empty, so its exit occurs at time zero on every path. -/
@[simp]
theorem spotExitTime_zero (S : ℝ≥0 → Ω → ℝ) : spotExitTime S 0 = 0 := by
  ext ω
  simp [spotExitTime_def, hittingAfter_univ]

private theorem monotone_spotDomain :
    Monotone (fun n : ℕ ↦ Ioo ((n + 1 : ℝ)⁻¹) (n + 1)) := by
  intro m n hmn
  apply Ioo_subset_Ioo
  · exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
  · exact_mod_cast Nat.add_le_add_right hmn 1

/-- Expanding the spot domain can only delay the first exit, on every path. -/
theorem monotone_spotExitTime (S : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    Monotone (fun n ↦ spotExitTime S n ω) := by
  intro m n hmn
  exact hittingAfter_apply_anti S 0 ω (compl_subset_compl.mpr (monotone_spotDomain hmn))

/-- On a strictly positive continuous path, spot-domain exits eventually exceed any fixed
finite horizon. In particular, capping the exits at that horizon eventually gives the horizon. -/
theorem eventually_lt_spotExitTime (hS : Continuous (S · ω)) (hpos : ∀ t, 0 < S t ω)
    (T : ℝ≥0) :
    ∀ᶠ n in atTop, (T : WithTop ℝ≥0) < spotExitTime S n ω := by
  simp_rw [spotExitTime_def]
  apply hS.eventually_lt_hittingAfter_compl (fun _ ↦ isOpen_Ioo) monotone_spotDomain
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (max (S t ω) (S t ω)⁻¹)
  refine ⟨n, ?_, ?_⟩
  · apply (inv_lt_comm₀ (by positivity) (hpos t)).mpr
    exact (le_max_right _ _).trans_lt (hn.trans (lt_add_one _))
  · exact (le_max_left _ _).trans_lt (hn.trans (lt_add_one _))

/-- The spot-domain exits of a strictly positive continuous path tend to infinity. -/
theorem tendsto_spotExitTime (hS : Continuous (S · ω)) (hpos : ∀ t, 0 < S t ω) :
    Tendsto (fun n ↦ spotExitTime S n ω) atTop (𝓝 ⊤) := by
  exact (WithTop.tendsto_nhds_top_iff _).mpr fun T ↦
    eventually_lt_spotExitTime hS hpos T

end TauCeti.Probability

namespace ProbabilityTheory.IsBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-- Geometric Brownian motion with positive initial spot almost surely has spot-domain exits
beyond each finite horizon. The null set is independent of the horizon; volatility may vanish. -/
theorem ae_eventually_lt_spotExitTime_geometricBrownianMotion (hW : IsBrownianReal W P)
    {s : ℝ} (hs : 0 < s) (μ σ : ℝ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ᶠ n in atTop,
      (T : WithTop ℝ≥0) < spotExitTime (geometricBrownianMotion s μ σ W) n ω := by
  filter_upwards [hW.cont] with ω hω
  have hS : Continuous (geometricBrownianMotion s μ σ W · ω) := by
    simp_rw [geometricBrownianMotion_def]
    fun_prop
  exact eventually_lt_spotExitTime hS (fun t ↦ geometricBrownianMotion_pos hs μ σ W t ω)

end ProbabilityTheory.IsBrownianReal
