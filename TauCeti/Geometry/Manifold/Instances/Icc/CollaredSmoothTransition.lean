/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Icc
import Mathlib.Analysis.Convex.Basic

/-!
# The collared smooth transition

`TauCeti.collaredSmoothTransition t = Real.smoothTransition (2 * t - 1 / 2)` is a smooth map of
the line into `[0, 1]` which is `0` up to `1 / 4` and `1` from `3 / 4` on, so it is constant near
both ends of the unit interval. Reparametrizing time by it makes a family constant near its two
ends: it is the time reparametrization of the traces of diffeotopies, and precomposing a map of the
plane with it in both coordinates flattens the map near the boundary of the unit square.

The straight-line homotopy `TauCeti.collaredSmoothTransitionLineMap c s = s + c (ρ s - s)` runs
from the identity, at `c = 0`, to the collared smooth transition `ρ`, at `c = 1`. It fixes `0` and
`1` and keeps the unit interval inside itself, so it is a homotopy relative to the endpoints from
the identity of the unit interval to `ρ`.

## Main declarations

* `TauCeti.collaredSmoothTransition`: the collared smooth transition, as a real function.
* `TauCeti.collaredSmoothTransitionLineMap`: the straight-line homotopy from the identity to the
  collared smooth transition.
* `TauCeti.collaredSmoothTransitionLineMapUnit`: the straight-line homotopy as a homotopy of maps of
  the unit interval.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {n : ℕ∞ω}

/-- The collared smooth transition `Real.smoothTransition (2 * t - 1 / 2)`: a smooth transition
from `0` to `1` which is constant on neighborhoods of both ends of the unit interval. -/
def collaredSmoothTransition (t : ℝ) : ℝ :=
  Real.smoothTransition (2 * t - 1 / 2)

/-- The defining formula of the collared smooth transition. -/
theorem collaredSmoothTransition_def (t : ℝ) :
    collaredSmoothTransition t = Real.smoothTransition (2 * t - 1 / 2) :=
  (rfl)

/-- The collared smooth transition takes values in the unit interval. -/
theorem collaredSmoothTransition_mem (t : ℝ) : collaredSmoothTransition t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The collared smooth transition is `0` up to `1 / 4`. -/
theorem collaredSmoothTransition_eq_zero_of_le {t : ℝ} (ht : t ≤ 1 / 4) :
    collaredSmoothTransition t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- The collared smooth transition is `1` from `3 / 4` on. -/
theorem collaredSmoothTransition_eq_one_of_ge {t : ℝ} (ht : 3 / 4 ≤ t) :
    collaredSmoothTransition t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The collared smooth transition is `C^n` for every `n ≤ ∞`. -/
theorem contDiff_collaredSmoothTransition (hn : n ≤ ∞) :
    ContDiff ℝ n collaredSmoothTransition :=
  ((Real.smoothTransition.contDiff (n := ⊤)).of_le hn).comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)

/-- The collared smooth transition is continuous. -/
@[continuity, fun_prop]
theorem continuous_collaredSmoothTransition : Continuous collaredSmoothTransition :=
  (contDiff_collaredSmoothTransition (n := 0) (by simp)).continuous

/-- The collared smooth transition into the unit interval (`TauCeti.collaredSmoothTransitionUnit`)
is the collared smooth transition. -/
theorem coe_collaredSmoothTransitionUnit_eq (t : ℝ) :
    (collaredSmoothTransitionUnit t : ℝ) = collaredSmoothTransition t :=
  coe_collaredSmoothTransitionUnit t

/-- The straight-line homotopy `s + c (ρ s - s)` from the identity, at `c = 0`, to the collared
smooth transition `ρ`, at `c = 1`. -/
def collaredSmoothTransitionLineMap (c s : ℝ) : ℝ :=
  s + c * (collaredSmoothTransition s - s)

/-- The defining formula of the straight-line homotopy. -/
theorem collaredSmoothTransitionLineMap_def (c s : ℝ) :
    collaredSmoothTransitionLineMap c s = s + c * (collaredSmoothTransition s - s) :=
  (rfl)

/-- At time `0` the straight-line homotopy is the identity. -/
@[simp]
theorem collaredSmoothTransitionLineMap_zero_left (s : ℝ) :
    collaredSmoothTransitionLineMap 0 s = s := by
  simp [collaredSmoothTransitionLineMap]

/-- At time `1` the straight-line homotopy is the collared smooth transition. -/
@[simp]
theorem collaredSmoothTransitionLineMap_one_left (s : ℝ) :
    collaredSmoothTransitionLineMap 1 s = collaredSmoothTransition s := by
  simp [collaredSmoothTransitionLineMap]

/-- The straight-line homotopy fixes `0`. -/
@[simp]
theorem collaredSmoothTransitionLineMap_zero_right (c : ℝ) :
    collaredSmoothTransitionLineMap c 0 = 0 := by
  simp [collaredSmoothTransitionLineMap,
    collaredSmoothTransition_eq_zero_of_le (by norm_num : (0 : ℝ) ≤ 1 / 4)]

/-- The straight-line homotopy fixes `1`. -/
@[simp]
theorem collaredSmoothTransitionLineMap_one_right (c : ℝ) :
    collaredSmoothTransitionLineMap c 1 = 1 := by
  simp [collaredSmoothTransitionLineMap,
    collaredSmoothTransition_eq_one_of_ge (by norm_num : (3 / 4 : ℝ) ≤ 1)]

/-- The straight-line homotopy keeps `[0, 1]` inside `[0, 1]`. -/
theorem collaredSmoothTransitionLineMap_mem {c s : ℝ} (hc : c ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1) : collaredSmoothTransitionLineMap c s ∈ Icc (0 : ℝ) 1 := by
  convert convex_Icc (0 : ℝ) 1 hs (collaredSmoothTransition_mem s) (sub_nonneg.2 hc.2) hc.1
    (by ring) using 1
  simp only [collaredSmoothTransitionLineMap, smul_eq_mul]
  ring

/-- Near `0`, the straight-line homotopy commutes with the translation by `1`. -/
theorem collaredSmoothTransitionLineMap_add_one (c : ℝ) {s : ℝ} (hs₀ : -1 / 4 ≤ s)
    (hs₁ : s ≤ 1 / 4) :
    collaredSmoothTransitionLineMap c (s + 1) = collaredSmoothTransitionLineMap c s + 1 := by
  rw [collaredSmoothTransitionLineMap_def, collaredSmoothTransitionLineMap_def,
    collaredSmoothTransition_eq_one_of_ge (by linarith), collaredSmoothTransition_eq_zero_of_le hs₁]
  ring

/-- The straight-line homotopy is jointly `C^n` for every `n ≤ ∞`. -/
theorem contDiff_collaredSmoothTransitionLineMap (hn : n ≤ ∞) :
    ContDiff ℝ n fun q : ℝ × ℝ ↦ collaredSmoothTransitionLineMap q.1 q.2 :=
  contDiff_snd.add (contDiff_fst.mul
    (((contDiff_collaredSmoothTransition hn).comp contDiff_snd).sub contDiff_snd))

/-- The straight-line homotopy is jointly continuous. -/
@[continuity, fun_prop]
theorem continuous_collaredSmoothTransitionLineMap :
    Continuous fun q : ℝ × ℝ ↦ collaredSmoothTransitionLineMap q.1 q.2 :=
  (contDiff_collaredSmoothTransitionLineMap (n := 0) (by simp)).continuous

/-- The straight-line homotopy from the identity to the collared smooth transition, as a map of the
unit interval at each time `c ∈ [0, 1]`. -/
def collaredSmoothTransitionLineMapUnit (c s : unitInterval) : unitInterval :=
  ⟨collaredSmoothTransitionLineMap c s, collaredSmoothTransitionLineMap_mem c.property s.property⟩

/-- The straight-line homotopy of the unit interval is the straight-line homotopy. -/
@[simp]
theorem coe_collaredSmoothTransitionLineMapUnit (c s : unitInterval) :
    (collaredSmoothTransitionLineMapUnit c s : ℝ) = collaredSmoothTransitionLineMap c s :=
  (rfl)

/-- The straight-line homotopy of the unit interval is jointly continuous. -/
@[continuity, fun_prop]
theorem continuous_collaredSmoothTransitionLineMapUnit :
    Continuous fun q : unitInterval × unitInterval ↦ collaredSmoothTransitionLineMapUnit q.1 q.2 :=
  (continuous_collaredSmoothTransitionLineMap.comp
    (continuous_subtypeVal.prodMap continuous_subtypeVal)).subtype_mk _

/-- At time `0` the straight-line homotopy of the unit interval is the identity. -/
@[simp]
theorem collaredSmoothTransitionLineMapUnit_zero_left (s : unitInterval) :
    collaredSmoothTransitionLineMapUnit 0 s = s :=
  Subtype.ext (collaredSmoothTransitionLineMap_zero_left s)

/-- At time `1` the straight-line homotopy of the unit interval is the collared smooth
transition. -/
@[simp]
theorem collaredSmoothTransitionLineMapUnit_one_left (s : unitInterval) :
    collaredSmoothTransitionLineMapUnit 1 s = collaredSmoothTransitionUnit s :=
  Subtype.ext ((collaredSmoothTransitionLineMap_one_left s).trans
    (coe_collaredSmoothTransitionUnit_eq s).symm)

/-- The straight-line homotopy of the unit interval fixes `0`. -/
@[simp]
theorem collaredSmoothTransitionLineMapUnit_zero_right (c : unitInterval) :
    collaredSmoothTransitionLineMapUnit c 0 = 0 :=
  Subtype.ext (collaredSmoothTransitionLineMap_zero_right c)

/-- The straight-line homotopy of the unit interval fixes `1`. -/
@[simp]
theorem collaredSmoothTransitionLineMapUnit_one_right (c : unitInterval) :
    collaredSmoothTransitionLineMapUnit c 1 = 1 :=
  Subtype.ext (collaredSmoothTransitionLineMap_one_right c)

end TauCeti
