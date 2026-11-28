/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Topology.MetricSpace.Arclength.Basic

/-!
# Checks for the arclength factorization: a curve with a pause

The curve `γ : [0, 3] → ℝ` equal to `t` on `[0, 1]`, to `1` on `[1, 2]` and to `t − 1` on `[2, 3]`
(`TauCeti.Examples.Arclength.pauseCurve`, written `min t 1 + max (t − 2) 0`) is nondecreasing, so
its length is `γ(3) − γ(0) = 2` (`TauCeti.Examples.Arclength.eVariationOn_pauseCurve`) and its
cumulative arclength `s(t) = variationOnFromTo γ [0, 3] 0 t` is `γ` itself
(`TauCeti.Examples.Arclength.variationOnFromTo_pauseCurve`). The natural parameterization `c` is
then the identity on the length interval `[0, 2]`
(`TauCeti.Examples.Arclength.eqOn_naturalParameterization_pauseCurve`), and `γ = c ∘ s` on
`[0, 3]`.

The arclength is constant on `[1, 2]`, so it is not injective
(`TauCeti.Examples.Arclength.not_injOn_variationOnFromTo_pauseCurve`) and the arclength
parametrization cannot be defined as `γ ∘ s⁻¹`; on `(1, 2)`, `γ' = 0`
(`TauCeti.Examples.Arclength.deriv_pauseCurve_eq_zero_of_mem_Ioo`) and `s' = 0`
(`TauCeti.Examples.Arclength.deriv_variationOnFromTo_pauseCurve_eq_zero_of_mem_Ioo`), and the
factorization identities say nothing about `c'` there.
-/

public section

open Set

namespace TauCeti.Examples.Arclength

/-- The curve with a pause: `t` on `[0, 1]`, `1` on `[1, 2]` and `t − 1` on `[2, 3]`. -/
def pauseCurve (t : ℝ) : ℝ :=
  min t 1 + max (t - 2) 0

/-- Unfolding lemma for `TauCeti.Examples.Arclength.pauseCurve`. -/
theorem pauseCurve_def (t : ℝ) : pauseCurve t = min t 1 + max (t - 2) 0 :=
  (rfl)

/-- The curve with a pause is nondecreasing. -/
theorem monotone_pauseCurve : Monotone pauseCurve := fun a b h ↦ by
  simp only [pauseCurve_def]
  exact add_le_add (min_le_min_right 1 h) (max_le_max_right 0 (by linarith))

/-- The curve with a pause is continuous. -/
theorem continuous_pauseCurve : Continuous pauseCurve := by
  simp only [funext pauseCurve_def]
  fun_prop

/-- The curve is constant equal to `1` on `[1, 2]`. -/
theorem pauseCurve_eq_one_of_mem_Icc {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 2) : pauseCurve t = 1 := by
  rw [pauseCurve_def, min_eq_right ht.1, max_eq_right (by linarith [ht.2])]
  ring

/-- **The length of the curve with a pause is `2`.** -/
theorem eVariationOn_pauseCurve : eVariationOn pauseCurve (Icc 0 3) = 2 := by
  have h := (monotone_pauseCurve.monotoneOn univ).eVariationOn_eq (mem_univ 0) (mem_univ 3)
  rw [univ_inter] at h
  rw [h, pauseCurve_def, pauseCurve_def]
  norm_num

/-- The curve with a pause has bounded variation on `[0, 3]`. -/
theorem boundedVariationOn_pauseCurve : BoundedVariationOn pauseCurve (Icc 0 3) := by
  rw [BoundedVariationOn, eVariationOn_pauseCurve]
  exact ENNReal.ofNat_ne_top

/-- **The arclength of the curve with a pause is the curve itself**, since it is nondecreasing and
starts at `0`. -/
theorem variationOnFromTo_pauseCurve {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 3) :
    variationOnFromTo pauseCurve (Icc 0 3) 0 t = pauseCurve t := by
  have h0 : pauseCurve 0 = 0 := by norm_num [pauseCurve_def]
  rw [variationOnFromTo.eq_of_le _ _ ht.1,
    (monotone_pauseCurve.monotoneOn (Icc 0 3)).eVariationOn_eq (left_mem_Icc.2 (by norm_num)) ht,
    ENNReal.toReal_ofReal (sub_nonneg.2 (monotone_pauseCurve ht.1)), h0, sub_zero]

/-- **The natural parameterization is the identity on the length interval `[0, 2]`.** -/
theorem eqOn_naturalParameterization_pauseCurve :
    EqOn (naturalParameterization pauseCurve (Icc 0 3) 0) id (Icc 0 2) := by
  have h := boundedVariationOn_pauseCurve.eqOn_naturalParameterization
    continuous_pauseCurve.continuousOn (by norm_num) (g := id)
    fun t ht ↦ by simp [variationOnFromTo_pauseCurve ht]
  rw [eVariationOn_pauseCurve, ENNReal.toReal_ofNat] at h
  exact h.symm

/-- The arclength is constant on `[1, 2]`, so it is not injective on `[0, 3]`. -/
theorem not_injOn_variationOnFromTo_pauseCurve :
    ¬InjOn (variationOnFromTo pauseCurve (Icc 0 3) 0) (Icc 0 3) := fun h ↦ by
  have h₁ : (1 : ℝ) ∈ Icc (0 : ℝ) 3 := ⟨by norm_num, by norm_num⟩
  have h₂ : (2 : ℝ) ∈ Icc (0 : ℝ) 3 := ⟨by norm_num, by norm_num⟩
  have := h h₁ h₂ (by rw [variationOnFromTo_pauseCurve h₁, variationOnFromTo_pauseCurve h₂,
    pauseCurve_eq_one_of_mem_Icc ⟨le_rfl, by norm_num⟩,
    pauseCurve_eq_one_of_mem_Icc ⟨by norm_num, le_rfl⟩])
  norm_num at this

/-- On `(1, 2)` the curve has derivative `0`. -/
theorem deriv_pauseCurve_eq_zero_of_mem_Ioo {t : ℝ} (ht : t ∈ Ioo (1 : ℝ) 2) :
    deriv pauseCurve t = 0 := by
  have h : pauseCurve =ᶠ[nhds t] fun _ ↦ 1 :=
    Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun u hu ↦
      pauseCurve_eq_one_of_mem_Icc (Ioo_subset_Icc_self hu)
  rw [h.deriv_eq, deriv_const]

/-- On `(1, 2)` the derivative of the arclength is `0`, like that of the curve. -/
theorem deriv_variationOnFromTo_pauseCurve_eq_zero_of_mem_Ioo {t : ℝ} (ht : t ∈ Ioo (1 : ℝ) 2) :
    deriv (variationOnFromTo pauseCurve (Icc 0 3) 0) t = 0 := by
  have h : variationOnFromTo pauseCurve (Icc 0 3) 0 =ᶠ[nhds t] pauseCurve :=
    Filter.eventually_of_mem (Ioo_mem_nhds (by linarith [ht.1] : (0 : ℝ) < t)
      (by linarith [ht.2] : t < 3)) fun u hu ↦ variationOnFromTo_pauseCurve (Ioo_subset_Icc_self hu)
  rw [h.deriv_eq, deriv_pauseCurve_eq_zero_of_mem_Ioo ht]

end TauCeti.Examples.Arclength
