/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Prod

/-!
# Difference and midpoint coordinates on the plane

The linear map taking a difference and midpoint to the corresponding pair of real coordinates
preserves Lebesgue measure. It is useful for separating translation-invariant pair interactions
from quadratic energies.
-/

public section
noncomputable section

open MeasureTheory

namespace TauCeti.MeasureTheory

/-- Convert a difference and midpoint to the corresponding pair of real coordinates. -/
def differenceMidpointEquiv : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun p := (p.2 + p.1 / 2, p.2 - p.1 / 2)
  invFun p := (p.1 - p.2, p.2 + (p.1 - p.2) / 2)
  left_inv p := by
    ext <;> dsimp <;> ring
  right_inv p := by
    ext <;> dsimp <;> ring
  measurable_toFun := by
    -- Expose the coordinate map so `fun_prop` can see its measurable components.
    change Measurable (fun p : ℝ × ℝ => (p.2 + p.1 / 2, p.2 - p.1 / 2))
    fun_prop
  measurable_invFun := by
    -- Expose the inverse coordinate map for `fun_prop`.
    change Measurable (fun p : ℝ × ℝ => (p.1 - p.2, p.2 + (p.1 - p.2) / 2))
    fun_prop

@[simp]
theorem differenceMidpointEquiv_apply (p : ℝ × ℝ) :
    differenceMidpointEquiv p = (p.2 + p.1 / 2, p.2 - p.1 / 2) := by
  rw [differenceMidpointEquiv]
  rfl

@[simp]
theorem differenceMidpointEquiv_symm_apply (p : ℝ × ℝ) :
    differenceMidpointEquiv.symm p = (p.1 - p.2, p.2 + (p.1 - p.2) / 2) := by
  rw [differenceMidpointEquiv]
  rfl

/-- The difference-midpoint change of coordinates preserves Lebesgue measure on `ℝ × ℝ`. -/
theorem measurePreserving_differenceMidpointEquiv :
    MeasurePreserving differenceMidpointEquiv volume volume := by
  rw [Measure.volume_eq_prod]
  let shift : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, p.2 + -(p.1 / 2))
  have hshift : MeasurePreserving shift (volume.prod volume) (volume.prod volume) := by
    refine MeasurePreserving.skew_product
      (μa := (volume : Measure ℝ)) (μb := (volume : Measure ℝ))
      (μc := (volume : Measure ℝ)) (μd := (volume : Measure ℝ))
      (f := id) (g := fun d z : ℝ => z + -(d / 2))
      (MeasurePreserving.id (volume : Measure ℝ)) ?_ ?_
    · fun_prop
    · filter_upwards with d
      have hd : MeasurePreserving (fun z : ℝ => z + -(d / 2)) volume volume :=
        measurePreserving_add_right (G := ℝ) (μ := (volume : Measure ℝ)) (-(d / 2))
      exact hd.map_eq
  have hadd : MeasurePreserving (fun p : ℝ × ℝ => (p.1 + p.2, p.2))
      (volume.prod volume) (volume.prod volume) :=
    measurePreserving_add_prod volume volume
  have heq : (differenceMidpointEquiv : ℝ × ℝ → ℝ × ℝ) =
      fun p => ((shift p).1 + (shift p).2, (shift p).2) := by
    funext p
    apply Prod.ext <;> simp only [differenceMidpointEquiv_apply] <;> dsimp [shift] <;> ring
  rw [heq]
  exact hadd.comp hshift

end TauCeti.MeasureTheory
