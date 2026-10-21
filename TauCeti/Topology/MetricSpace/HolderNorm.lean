/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.HolderNorm

/-!
# Bounds for Hölder seminorms

Transporting every Hölder bound gives a comparison of extended Hölder seminorms.
A strict upper bound on the seminorm gives a Hölder constant for pseudo extended metric spaces.
-/

public section

noncomputable section

namespace TauCeti

open scoped NNReal ENNReal

/-- Transport of Hölder estimates with unchanged constants bounds the target seminorm by
the source seminorm, even when the latter is infinite. -/
theorem eHolderNorm_le_of_holderWith {X Y X' Y' : Type*}
    [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    [PseudoEMetricSpace X'] [PseudoEMetricSpace Y']
    {r s : ℝ≥0} {f : X → Y} {g : X' → Y'}
    (h : ∀ C, HolderWith C r f → HolderWith C s g) :
    eHolderNorm s g ≤ eHolderNorm r f :=
  le_iInf₂ fun C hC ↦ (h C hC).eHolderNorm_le

/-- A strict upper bound for the extended Hölder seminorm is a Hölder constant. -/
theorem holderWith_of_eHolderNorm_lt {X Y : Type*}
    [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {r C : ℝ≥0} {f : X → Y} (h : eHolderNorm r f < C) : HolderWith C r f := by
  simp only [eHolderNorm, iInf_lt_iff] at h
  obtain ⟨D, hD, hDC⟩ := h
  exact hD.mono (ENNReal.coe_le_coe.mp hDC.le)

end TauCeti
