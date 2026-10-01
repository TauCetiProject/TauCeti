/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.Anharmonic

/-!
# Standard punctured neighborhoods of the three punctures

This file fixes pairwise disjoint standard neighborhoods of the punctures `0`, `1`, and `∞` in
the thrice-punctured sphere. In the affine coordinate they are

* `puncturedNeighborhoodZero = {z | ‖z‖ < 1 / 2}`;
* `puncturedNeighborhoodOne = {z | ‖z - 1‖ < 1 / 2}`;
* `puncturedNeighborhoodInf = {z | 2 < ‖z‖}`.

The missing center of each finite disc is already excluded from `ThricePuncturedSphere`. The
anharmonic maps `z ↦ 1 - z` and `z ↦ 1 / z` identify the neighborhoods at `1` and `∞` with the
one at `0`. Thus all three are copies of the same punctured disc, expressed in the standard
local coordinates at the three punctures.

These neighborhoods are the local geometric input for extending a finite cover across the three
punctures: their pairwise disjointness lets the three fillings be performed independently.

## Main definitions

* `puncturedHalfDisc`: the punctured complex disc of radius `1 / 2`.
* `puncturedNeighborhoodZero`, `puncturedNeighborhoodOne`, `puncturedNeighborhoodInf`: the
  three standard neighborhoods.
* `puncturedNeighborhoodZeroEquivPuncturedHalfDisc`,
  `puncturedNeighborhoodOneEquivPuncturedHalfDisc`, and
  `puncturedNeighborhoodInfEquivPuncturedHalfDisc`: their standard local coordinates.
-/

public section

open Set

namespace TauCeti

namespace ThricePuncturedSphere

/-! ### The three neighborhoods -/

/-- The complex punctured disc of radius `1 / 2`, used as the common coordinate model for the
three standard punctured neighborhoods. -/
def puncturedHalfDisc : Set ℂ :=
  {z | 0 < ‖z‖ ∧ ‖z‖ < 1 / 2}

/-- The standard punctured half-disc about `0` in the thrice-punctured sphere. The center is
absent because points of `ThricePuncturedSphere` are nonzero. -/
def puncturedNeighborhoodZero : Set ThricePuncturedSphere :=
  {z | ‖(z : ℂ)‖ < 1 / 2}

/-- The standard punctured half-disc about `1` in the thrice-punctured sphere. The center is
absent because points of `ThricePuncturedSphere` are not equal to `1`. -/
def puncturedNeighborhoodOne : Set ThricePuncturedSphere :=
  {z | ‖(z : ℂ) - 1‖ < 1 / 2}

/-- The standard punctured neighborhood of `∞`, represented in the affine coordinate by the
exterior of the closed disc of radius `2`. -/
def puncturedNeighborhoodInf : Set ThricePuncturedSphere :=
  {z | 2 < ‖(z : ℂ)‖}

@[simp]
theorem mem_puncturedNeighborhoodZero {z : ThricePuncturedSphere} :
    z ∈ puncturedNeighborhoodZero ↔ ‖(z : ℂ)‖ < 1 / 2 :=
  Iff.rfl

@[simp]
theorem mem_puncturedNeighborhoodOne {z : ThricePuncturedSphere} :
    z ∈ puncturedNeighborhoodOne ↔ ‖(z : ℂ) - 1‖ < 1 / 2 :=
  Iff.rfl

@[simp]
theorem mem_puncturedNeighborhoodInf {z : ThricePuncturedSphere} :
    z ∈ puncturedNeighborhoodInf ↔ 2 < ‖(z : ℂ)‖ :=
  Iff.rfl

@[simp]
theorem mem_puncturedHalfDisc {z : ℂ} :
    z ∈ puncturedHalfDisc ↔ 0 < ‖z‖ ∧ ‖z‖ < 1 / 2 :=
  Iff.rfl

/-- The standard punctured neighborhood of `0` is open. -/
theorem isOpen_puncturedNeighborhoodZero : IsOpen puncturedNeighborhoodZero :=
  isOpen_lt continuous_subtype_val.norm continuous_const

/-- The standard punctured neighborhood of `1` is open. -/
theorem isOpen_puncturedNeighborhoodOne : IsOpen puncturedNeighborhoodOne :=
  isOpen_lt (continuous_subtype_val.sub continuous_const).norm continuous_const

/-- The standard punctured neighborhood of `∞` is open. -/
theorem isOpen_puncturedNeighborhoodInf : IsOpen puncturedNeighborhoodInf :=
  isOpen_lt continuous_const continuous_subtype_val.norm

/-! ### Disjointness -/

/-- The standard punctured neighborhoods of `0` and `1` are disjoint. -/
theorem disjoint_puncturedNeighborhoodZero_puncturedNeighborhoodOne :
    Disjoint puncturedNeighborhoodZero puncturedNeighborhoodOne := by
  rw [Set.disjoint_left]
  intro z hz hOne
  have hle : (1 : ℝ) ≤ ‖(z : ℂ)‖ + ‖(z : ℂ) - 1‖ := calc
    (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
    _ = ‖(z : ℂ) - ((z : ℂ) - 1)‖ := by ring_nf
    _ ≤ ‖(z : ℂ)‖ + ‖(z : ℂ) - 1‖ := norm_sub_le _ _
  rw [mem_puncturedNeighborhoodZero] at hz
  rw [mem_puncturedNeighborhoodOne] at hOne
  linarith

/-- The standard punctured neighborhoods of `0` and `∞` are disjoint. -/
theorem disjoint_puncturedNeighborhoodZero_puncturedNeighborhoodInf :
    Disjoint puncturedNeighborhoodZero puncturedNeighborhoodInf := by
  rw [Set.disjoint_left]
  intro z hz hInf
  rw [mem_puncturedNeighborhoodZero] at hz
  rw [mem_puncturedNeighborhoodInf] at hInf
  linarith

/-- The standard punctured neighborhoods of `1` and `∞` are disjoint. -/
theorem disjoint_puncturedNeighborhoodOne_puncturedNeighborhoodInf :
    Disjoint puncturedNeighborhoodOne puncturedNeighborhoodInf := by
  rw [Set.disjoint_left]
  intro z hOne hInf
  have hle : ‖(z : ℂ)‖ ≤ ‖(z : ℂ) - 1‖ + 1 := calc
    ‖(z : ℂ)‖ = ‖((z : ℂ) - 1) + 1‖ := by ring_nf
    _ ≤ ‖(z : ℂ) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ = ‖(z : ℂ) - 1‖ + 1 := by norm_num
  rw [mem_puncturedNeighborhoodOne] at hOne
  rw [mem_puncturedNeighborhoodInf] at hInf
  linarith

/-! ### Standard local coordinates -/

/-- The affine coordinate identifies the standard neighborhood of `0` with the complex
punctured disc of radius `1 / 2`. -/
noncomputable def puncturedNeighborhoodZeroEquivPuncturedHalfDisc :
    ↥puncturedNeighborhoodZero ≃ₜ ↥puncturedHalfDisc where
  toFun z := ⟨(z : ThricePuncturedSphere), norm_pos_iff.mpr z.1.ne_zero, z.2⟩
  invFun z := by
    have hne : (z : ℂ) ≠ 1 := by
      intro h
      have hz := z.2.2
      rw [h, norm_one] at hz
      norm_num at hz
    exact ⟨⟨z, norm_pos_iff.mp z.2.1, hne⟩, z.2.2⟩
  left_inv z := by ext; rfl
  right_inv z := by ext; rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp]
theorem coe_puncturedNeighborhoodZeroEquivPuncturedHalfDisc
    (z : ↥puncturedNeighborhoodZero) :
    (puncturedNeighborhoodZeroEquivPuncturedHalfDisc z : ℂ) =
      (z : ThricePuncturedSphere) :=
  by
    change ((z.1 : ThricePuncturedSphere) : ℂ) = ((z : ThricePuncturedSphere) : ℂ)
    rfl

/-- The local coordinate `z ↦ 1 - z` identifies the punctured neighborhood of `1` with the
punctured neighborhood of `0`. -/
private noncomputable def puncturedNeighborhoodOneEquivZero :
    ↥puncturedNeighborhoodOne ≃ₜ ↥puncturedNeighborhoodZero :=
  mob01.subtype fun z ↦ by
    rw [mem_puncturedNeighborhoodOne, mem_puncturedNeighborhoodZero, coe_mob01]
    rw [show 1 - (z : ℂ) = -((z : ℂ) - 1) by ring, norm_neg]

/-- The coordinate `z ↦ 1 - z` identifies the standard neighborhood of `1` with the complex
punctured disc of radius `1 / 2`. -/
noncomputable def puncturedNeighborhoodOneEquivPuncturedHalfDisc :
    ↥puncturedNeighborhoodOne ≃ₜ ↥puncturedHalfDisc :=
  puncturedNeighborhoodOneEquivZero.trans
    puncturedNeighborhoodZeroEquivPuncturedHalfDisc

@[simp]
theorem coe_puncturedNeighborhoodOneEquivPuncturedHalfDisc
    (z : ↥puncturedNeighborhoodOne) :
    (puncturedNeighborhoodOneEquivPuncturedHalfDisc z : ℂ) =
      1 - (z : ThricePuncturedSphere) :=
  coe_mob01 (z : ThricePuncturedSphere)

/-- The local coordinate `z ↦ 1 / z` identifies the punctured neighborhood of `∞` with the
punctured neighborhood of `0`. -/
private noncomputable def puncturedNeighborhoodInfEquivZero :
    ↥puncturedNeighborhoodInf ≃ₜ ↥puncturedNeighborhoodZero :=
  mob0Inf.subtype fun z ↦ by
    rw [mem_puncturedNeighborhoodInf, mem_puncturedNeighborhoodZero, coe_mob0Inf,
      norm_div, norm_one]
    have hz : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
    constructor
    · intro h
      rw [div_lt_iff₀ hz]
      nlinarith
    · intro h
      rw [div_lt_iff₀ hz] at h
      nlinarith

/-- The coordinate `z ↦ 1 / z` identifies the standard neighborhood of `∞` with the complex
punctured disc of radius `1 / 2`. This is the standard chart at `∞`. -/
noncomputable def puncturedNeighborhoodInfEquivPuncturedHalfDisc :
    ↥puncturedNeighborhoodInf ≃ₜ ↥puncturedHalfDisc :=
  puncturedNeighborhoodInfEquivZero.trans
    puncturedNeighborhoodZeroEquivPuncturedHalfDisc

@[simp]
theorem coe_puncturedNeighborhoodInfEquivPuncturedHalfDisc
    (z : ↥puncturedNeighborhoodInf) :
    (puncturedNeighborhoodInfEquivPuncturedHalfDisc z : ℂ) =
      1 / (z : ThricePuncturedSphere) :=
  coe_mob0Inf (z : ThricePuncturedSphere)

end ThricePuncturedSphere

end TauCeti
