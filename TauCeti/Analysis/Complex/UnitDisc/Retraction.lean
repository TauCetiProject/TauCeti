/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UnitDisc.Basic
public import TauCeti.Analysis.Normed.Module.Ball.Retraction
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# The radial retraction of the plane into the open unit disc

For `0 ≤ r < 1`, the radial retraction of `ℂ` onto the closed disc of radius `r` about `0`
(`TauCeti.radialRetraction`) takes its values in the open unit disc `𝔻`. This file packages it as
a continuous map `ℂ → 𝔻` (`TauCeti.Complex.UnitDisc.radialRetractionToUnitDisc`). It fixes the
closed disc of radius `r` and sends every other point to the point of the circle of radius `r` on
the same ray.

Restricted to `𝔻`, it retracts `𝔻` onto the closed disc of radius `r`
(`TauCeti.Complex.UnitDisc.discRetraction`). Precomposing a disc map `σ : 𝔻 → Y` with this
retraction keeps `σ` on that closed disc and replaces it outside by its values on the circle of
radius `r`. The new disc has compact image, and nothing of `σ` near the boundary of `𝔻` survives
in it; this is how zero charges of discs are localized to a closed subdisc. Every compact subset of
`𝔻` lies in such a subdisc, of some radius less than `1`
(`Complex.UnitDisc.exists_forall_norm_lt_of_isCompact`), where the retraction does not move it.
-/

public section

noncomputable section

open Metric Set
open scoped Complex.UnitDisc

namespace TauCeti.Complex.UnitDisc

open _root_.Complex.UnitDisc

variable {r : ℝ} {hr : 0 ≤ r} {hr₁ : r < 1}

/-- The **radial retraction of `ℂ` into the open unit disc**: for `0 ≤ r < 1`, the radial
retraction of `ℂ` onto the closed disc of radius `r` about `0`, which takes its values in `𝔻`. -/
def radialRetractionToUnitDisc (r : ℝ) (hr : 0 ≤ r) (hr₁ : r < 1) : C(ℂ, 𝔻) where
  toFun w := mk (TauCeti.radialRetraction r w) <| by
    rw [norm_radialRetraction hr]
    exact (min_le_right _ _).trans_lt hr₁
  continuous_toFun :=
    isEmbedding_coe.continuous_iff.2 (lipschitzWith_radialRetraction hr).continuous

@[simp]
theorem coe_radialRetractionToUnitDisc_apply (w : ℂ) :
    (radialRetractionToUnitDisc r hr hr₁ w : ℂ) = TauCeti.radialRetraction r w :=
  (rfl)

/-- The radial retraction of radius `r` has norm `min ‖w‖ r`. -/
theorem norm_coe_radialRetractionToUnitDisc_apply (w : ℂ) :
    ‖(radialRetractionToUnitDisc r hr hr₁ w : ℂ)‖ = min ‖w‖ r := by
  rw [coe_radialRetractionToUnitDisc_apply, norm_radialRetraction hr]

/-- The radial retraction of radius `r` fixes the closed disc of radius `r`. -/
theorem coe_radialRetractionToUnitDisc_apply_of_norm_le {w : ℂ} (h : ‖w‖ ≤ r) :
    (radialRetractionToUnitDisc r hr hr₁ w : ℂ) = w := by
  rw [coe_radialRetractionToUnitDisc_apply, TauCeti.radialRetraction_of_norm_le h]

/-- A point whose radial retraction of radius `r` has norm less than `r` has norm less than `r`;
the retraction moves only points of norm greater than `r`, onto the circle of radius `r`. -/
theorem norm_lt_of_norm_coe_radialRetractionToUnitDisc_apply_lt {w : ℂ} {s : ℝ}
    (h : ‖(radialRetractionToUnitDisc r hr hr₁ w : ℂ)‖ < s) (hs : s ≤ r) : ‖w‖ < s := by
  rw [norm_coe_radialRetractionToUnitDisc_apply] at h
  rcases min_choice ‖w‖ r with h' | h' <;> rw [h'] at h
  · exact h
  · exact absurd hs (not_le.2 h)

/-- The **radial retraction of the open unit disc** onto its closed subdisc of radius `r`, for
`0 ≤ r < 1`: the restriction of `TauCeti.Complex.UnitDisc.radialRetractionToUnitDisc` to `𝔻`. -/
def discRetraction (r : ℝ) (hr : 0 ≤ r) (hr₁ : r < 1) : C(𝔻, 𝔻) :=
  (radialRetractionToUnitDisc r hr hr₁).comp ⟨(↑), continuous_coe⟩

@[simp]
theorem discRetraction_apply (z : 𝔻) :
    discRetraction r hr hr₁ z = radialRetractionToUnitDisc r hr hr₁ z :=
  (rfl)

/-- The radial retraction of `𝔻` onto its closed subdisc of radius `r` fixes the points of norm at
most `r`. -/
theorem discRetraction_apply_of_norm_le {z : 𝔻} (h : ‖(z : ℂ)‖ ≤ r) :
    discRetraction r hr hr₁ z = z :=
  coe_injective (coe_radialRetractionToUnitDisc_apply_of_norm_le (hr := hr) (hr₁ := hr₁) h)

/-- The radial retraction of `𝔻` onto its closed subdisc of radius `r` takes values of norm at most
`r`. -/
theorem norm_coe_discRetraction_apply_le (z : 𝔻) : ‖(discRetraction r hr hr₁ z : ℂ)‖ ≤ r := by
  rw [discRetraction_apply, norm_coe_radialRetractionToUnitDisc_apply]
  exact min_le_right _ _

/-- A point of `𝔻` whose radial retraction onto the closed subdisc of radius `r` has norm less than
`s ≤ r` is fixed by the retraction and has norm less than `s`. -/
theorem discRetraction_apply_eq_and_norm_lt {z : 𝔻} {s : ℝ}
    (h : ‖(discRetraction r hr hr₁ z : ℂ)‖ < s) (hs : s ≤ r) :
    discRetraction r hr hr₁ z = z ∧ ‖(z : ℂ)‖ < s := by
  have hz :=
    norm_lt_of_norm_coe_radialRetractionToUnitDisc_apply_lt (hr := hr) (hr₁ := hr₁) h hs
  exact ⟨discRetraction_apply_of_norm_le (hz.le.trans hs), hz⟩

end TauCeti.Complex.UnitDisc
