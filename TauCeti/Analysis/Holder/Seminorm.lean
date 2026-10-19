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
A finite upper bound on the seminorm of a map between metric spaces gives a Hölder constant.
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

/-- A finite upper bound for the extended Hölder seminorm is a Hölder constant. -/
theorem HolderWith.of_eHolderNorm_le {X Y : Type*} [MetricSpace X] [EMetricSpace Y]
    {r : ℝ≥0} {f : X → Y} {A : ℝ≥0∞} (hA : A ≠ ∞) (h : eHolderNorm r f ≤ A) :
    HolderWith A.toNNReal r f := by
  have hf : MemHolder r f := eHolderNorm_ne_top.mp (ne_top_of_le_ne_top hA h)
  exact hf.holderWith.mono (by
    rw [← ENNReal.coe_le_coe, hf.coe_nnHolderNorm_eq_eHolderNorm, ENNReal.coe_toNNReal hA]
    exact h)

end TauCeti
