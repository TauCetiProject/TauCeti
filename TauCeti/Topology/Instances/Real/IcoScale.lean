/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Scaling the unit half-open interval

For `ε > 0`, multiplication by `ε` is a homeomorphism `[0, 1) ≃ₜ [0, ε)` with inverse `s ↦ s / ε`
(`TauCeti.icoScale`). It rescales a depth parameter in `[0, 1)`, as for collars, to an interval
`[0, ε)` and back.

A continuous map on `[0, δ)` is controlled near `0` by its value there: it stays in any
neighbourhood of that value on a shorter interval `[0, ε)`, and if it sends every positive point
into a set `P`, its value at `0` lies in the closure of `P`.

## Main definitions

* `TauCeti.icoScale`: the homeomorphism `[0, 1) ≃ₜ [0, ε)`, `t ↦ ε t`.

## Main statements

* `TauCeti.exists_pos_forall_lt_mem`: a continuous map on `[0, δ)` stays in any neighbourhood of
  its value at `0` on a shorter interval `[0, ε)`.
* `TauCeti.mem_closure_of_forall_ne_zero`: a continuous map on `[0, δ)` sending every positive
  point into `P` sends `0` into the closure of `P`.
-/

public section

open Set Topology

namespace TauCeti

variable {ε : ℝ}

/-- The scaling `t ↦ ε t` of half-open intervals, `[0, 1) ≃ₜ [0, ε)`, for `ε > 0`. -/
noncomputable def icoScale (hε : 0 < ε) : ↥(Ico (0 : ℝ) 1) ≃ₜ ↥(Ico (0 : ℝ) ε) where
  toFun t := ⟨ε * t, mul_nonneg hε.le t.property.1, mul_lt_of_lt_one_right hε t.property.2⟩
  invFun s := ⟨s / ε, div_nonneg s.property.1 hε.le, (div_lt_one hε).2 s.property.2⟩
  left_inv t := Subtype.ext (mul_div_cancel_left₀ _ hε.ne')
  right_inv s := Subtype.ext (mul_div_cancel₀ _ hε.ne')
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The scaling of `[0, 1)` onto `[0, ε)` is multiplication by `ε`. -/
@[simp]
theorem coe_icoScale (hε : 0 < ε) (t : ↥(Ico (0 : ℝ) 1)) : (icoScale hε t : ℝ) = ε * t :=
  (rfl)

/-- The inverse of the scaling of `[0, 1)` onto `[0, ε)` is division by `ε`. -/
@[simp]
theorem coe_icoScale_symm (hε : 0 < ε) (s : ↥(Ico (0 : ℝ) ε)) :
    ((icoScale hε).symm s : ℝ) = s / ε :=
  (rfl)

/-- A continuous map on `[0, δ)` stays in any neighbourhood of its value at `0` on a shorter
interval `[0, ε)`. -/
theorem exists_pos_forall_lt_mem {Y : Type*} [TopologicalSpace Y] {U : Set Y} {δ : ℝ}
    (hδ : 0 < δ) {g : Ico (0 : ℝ) δ → Y} (hg : Continuous g)
    (hU : U ∈ 𝓝 (g ⟨0, left_mem_Ico.2 hδ⟩)) :
    ∃ ε > 0, ∀ s : Ico (0 : ℝ) δ, (s : ℝ) < ε → g s ∈ U := by
  obtain ⟨V, hV, hVU⟩ := (mem_nhds_subtype _ _ _).1 (hg.continuousAt.preimage_mem_nhds hU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨ε, hε, fun s hs ↦ @hVU s (hball ?_)⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg s.property.1]
  exact hs

/-- If a continuous map on `[0, δ)` sends every positive point into `P`, it sends `0` into the
closure of `P`. -/
theorem mem_closure_of_forall_ne_zero {Z : Type*} [TopologicalSpace Z] {P : Set Z}
    {δ : ℝ} (hδ : 0 < δ) {g : Ico (0 : ℝ) δ → Z} (hg : Continuous g)
    (hP : ∀ s : Ico (0 : ℝ) δ, (s : ℝ) ≠ 0 → g s ∈ P) : g ⟨0, left_mem_Ico.2 hδ⟩ ∈ closure P := by
  -- `g 0` is the limit of the points `g (δ / (n + 2))`.
  let u : ℕ → Ico (0 : ℝ) δ := fun n ↦ ⟨δ / ((n + 2 : ℕ) : ℝ), by positivity, by
    rw [div_lt_iff₀ (by positivity)]
    push_cast
    nlinarith⟩
  have hu : Filter.Tendsto u Filter.atTop (𝓝 ⟨0, left_mem_Ico.2 hδ⟩) :=
    tendsto_subtype_rng.2 ((tendsto_const_div_atTop_nhds_zero_nat δ).comp
      (Filter.tendsto_add_atTop_nat 2))
  exact mem_closure_of_tendsto ((hg.tendsto _).comp hu) (.of_forall fun n ↦ hP _ (by positivity))

end TauCeti
