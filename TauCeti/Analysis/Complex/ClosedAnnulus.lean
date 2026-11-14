/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Topology.MetricSpace.ProperSpace
public import TauCeti.Analysis.Complex.Circle

/-!
# The closed annulus in the complex plane

The closed annulus `r₁ ≤ ‖z‖ ≤ r₂` centred at the origin of `ℂ`, with its membership criterion,
its compactness, and polar coordinates on it.

## Main declarations

* `Complex.closedAnnulus`: the closed annulus `r₁ ≤ ‖z‖ ≤ r₂`.
* `Complex.closedAnnulus.le_norm_coe` and `Complex.closedAnnulus.norm_coe_le`: the norm bounds of
  a point of the closed annulus.
* `Complex.isCompact_closedAnnulus`: the closed annulus is compact.
* `Complex.closedAnnulusHomeomorph`: for `0 < r₁`, polar coordinates identify the closed annulus
  with `Circle × [r₁, r₂]`.
-/

public section

open Metric

namespace Complex

/-- The closed annulus `r₁ ≤ ‖z‖ ≤ r₂` in `ℂ`. -/
noncomputable def closedAnnulus (r₁ r₂ : ℝ) : Set ℂ :=
  closedBall 0 r₂ \ ball 0 r₁

@[simp]
theorem mem_closedAnnulus {r₁ r₂ : ℝ} {z : ℂ} :
    z ∈ closedAnnulus r₁ r₂ ↔ r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ := by
  simp [closedAnnulus, and_comm]

/-- A point of the closed annulus has norm at least `r₁`. -/
theorem closedAnnulus.le_norm_coe {r₁ r₂ : ℝ} (z : closedAnnulus r₁ r₂) : r₁ ≤ ‖(z : ℂ)‖ :=
  (mem_closedAnnulus.1 z.2).1

/-- A point of the closed annulus has norm at most `r₂`. -/
theorem closedAnnulus.norm_coe_le {r₁ r₂ : ℝ} (z : closedAnnulus r₁ r₂) : ‖(z : ℂ)‖ ≤ r₂ :=
  (mem_closedAnnulus.1 z.2).2

theorem isCompact_closedAnnulus (r₁ r₂ : ℝ) : IsCompact (closedAnnulus r₁ r₂) :=
  (isCompact_closedBall 0 r₂).diff isOpen_ball

instance instCompactSpaceClosedAnnulus (r₁ r₂ : ℝ) : CompactSpace (closedAnnulus r₁ r₂) :=
  isCompact_iff_compactSpace.1 (isCompact_closedAnnulus r₁ r₂)

variable {r₁ r₂ : ℝ}

/-- Polar coordinates on the closed annulus `r₁ ≤ ‖z‖ ≤ r₂` with `0 < r₁`: the direction
`z / ‖z‖` and the modulus `‖z‖`. The direction is that of Mathlib's `homeomorphUnitSphereProd`. -/
noncomputable def closedAnnulusHomeomorph (h₀ : 0 < r₁) :
    closedAnnulus r₁ r₂ ≃ₜ Circle × Set.Icc r₁ r₂ where
  toFun z :=
    have hz : (z : ℂ) ≠ 0 := norm_pos_iff.1 (h₀.trans_le (mem_closedAnnulus.1 z.2).1)
    (Circle.homeomorphSphere.symm (homeomorphUnitSphereProd ℂ ⟨z, hz⟩).1,
      ⟨‖(z : ℂ)‖, mem_closedAnnulus.1 z.2⟩)
  invFun p := ⟨(p.2 : ℝ) • (p.1 : ℂ), by
    have h2 := p.2.2
    rw [mem_closedAnnulus, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg
      (h₀.le.trans h2.1)]
    exact h2⟩
  left_inv z := by
    have hz : (z : ℂ) ≠ 0 := norm_pos_iff.1 (h₀.trans_le (mem_closedAnnulus.1 z.2).1)
    ext1
    simp [hz]
  right_inv p := by
    have ht : 0 < (p.2 : ℝ) := h₀.trans_le p.2.2.1
    ext
    · simp [abs_of_pos ht, ht.ne']
    · simp [abs_of_pos ht]
  continuous_toFun := by
    refine .prodMk (Circle.homeomorphSphere.symm.continuous.comp (continuous_fst.comp
      ((homeomorphUnitSphereProd ℂ).continuous.comp (continuous_subtype_val.subtype_mk _))))
      (continuous_subtype_val.norm.subtype_mk _)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop

@[simp]
theorem coe_closedAnnulusHomeomorph_apply_fst (h₀ : 0 < r₁) (z : closedAnnulus r₁ r₂) :
    ((closedAnnulusHomeomorph h₀ z).1 : ℂ) = ‖(z : ℂ)‖⁻¹ • (z : ℂ) := by
  simp [closedAnnulusHomeomorph]

@[simp]
theorem coe_closedAnnulusHomeomorph_apply_snd (h₀ : 0 < r₁) (z : closedAnnulus r₁ r₂) :
    ((closedAnnulusHomeomorph h₀ z).2 : ℝ) = ‖(z : ℂ)‖ :=
  (rfl)

@[simp]
theorem coe_closedAnnulusHomeomorph_symm_apply (h₀ : 0 < r₁) (p : Circle × Set.Icc r₁ r₂) :
    ((closedAnnulusHomeomorph h₀).symm p : ℂ) = (p.2 : ℝ) • (p.1 : ℂ) :=
  (rfl)

end Complex
