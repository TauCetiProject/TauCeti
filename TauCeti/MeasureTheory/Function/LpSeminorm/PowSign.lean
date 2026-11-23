/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Pow.PowSign
public import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# `Lᵖ` seminorms of Thorin's analytic family

For a simple function `u` with values in a complex normed space, the member
`u.map (TauCeti.powSign w) = sgn(u) |u| ^ w` of Thorin's analytic family through `u` has pointwise
norm at most `|u| ^ re w`. If `u` lies in the unit ball of `Lˢ`, it therefore lies in the unit
ball of `Lᵗ` for `1 / t = re w / s` (`MeasureTheory.SimpleFunc.eLpNorm_map_powSign_le_one`). This
is the boundary estimate of the analytic family in the Riesz–Thorin theorem.
-/

public section

open scoped ENNReal

namespace MeasureTheory.SimpleFunc

variable {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {mα : MeasurableSpace α}
  {μ : Measure α}

/-- The member `u_w = sgn(u) |u| ^ w` of the analytic family through `u` has `Lᵗ` norm at most
one, where `1 / t = re w / s`, whenever `u` has `Lˢ` norm at most one. -/
theorem eLpNorm_map_powSign_le_one (u : SimpleFunc α E) {s t : ℝ≥0∞} {w : ℂ} (hw : 0 ≤ w.re)
    (ht : t⁻¹ = ENNReal.ofReal w.re * s⁻¹) (hu : eLpNorm u s μ ≤ 1) :
    eLpNorm (u.map (TauCeti.powSign w)) t μ ≤ 1 :=
  (TauCeti.eLpNorm_le_eLpNorm_rpow hw (u.map _).aestronglyMeasurable ht
    (ae_of_all _ fun x => by simpa using TauCeti.norm_powSign_le w (u x))).trans
    (ENNReal.rpow_le_one hu hw)

end MeasureTheory.SimpleFunc
