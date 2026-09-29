/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Bilinear operations on bounded Hölder functions

A continuous bilinear map sends two bounded Hölder functions of the same exponent to a Hölder
function. The estimate keeps the uniform bounds separate from the Hölder constants, so it also
applies to restrictions and yields the product estimate for the supremum-plus-Hölder norm.

The argument is adapted from `holderWith_bilinear_of_norm_le` in
[DifferentialGeometry, Holder/Bilinear.lean](https://github.com/qinz1yang/differential-geometry/blob/7a48598d35109aa99d1cc678e2724c213cdf4ff3/DifferentialGeometry/Analysis/Schauder/Holder/Bilinear.lean).
Here the scalar field is arbitrary and the operator norm is explicit.
-/

public section

open Set
open scoped NNReal

namespace ContinuousLinearMap

variable {𝕜 X E F G : Type*} [NontriviallyNormedField 𝕜] [PseudoMetricSpace X]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A bilinear map preserves Hölder continuity on a set when both input functions are bounded
there. The constant is `‖B‖ * (Mf * Kg + Mg * Kf)`. -/
theorem holderOnWith_comp₂ (B : E →L[𝕜] F →L[𝕜] G)
    {α Kf Kg Mf Mg : ℝ≥0} {f : X → E} {g : X → F} {s : Set X}
    (hf : HolderOnWith Kf α f s) (hg : HolderOnWith Kg α g s)
    (hfnorm : ∀ x ∈ s, ‖f x‖ ≤ Mf) (hgnorm : ∀ x ∈ s, ‖g x‖ ≤ Mg) :
    HolderOnWith (‖B‖₊ * (Mf * Kg + Mg * Kf)) α (fun x ↦ B (f x) (g x)) s := by
  intro x hx y hy
  have hsplit : B (f x) (g x) - B (f y) (g y) =
      B (f x) (g x - g y) + B (f x - f y) (g y) := by
    simp only [map_sub, sub_apply]
    abel
  have hbound : dist (B (f x) (g x)) (B (f y) (g y)) ≤
      (‖B‖ * ((Mf : ℝ) * Kg + Mg * Kf)) * dist x y ^ (α : ℝ) := by
    rw [dist_eq_norm, hsplit]
    calc
      ‖B (f x) (g x - g y) + B (f x - f y) (g y)‖ ≤
          ‖B‖ * ‖f x‖ * ‖g x - g y‖ + ‖B‖ * ‖f x - f y‖ * ‖g y‖ :=
        (norm_add_le _ _).trans (add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _))
      _ ≤ ‖B‖ * Mf * (Kg * dist x y ^ (α : ℝ)) +
          ‖B‖ * (Kf * dist x y ^ (α : ℝ)) * Mg := by
        gcongr
        · exact hfnorm x hx
        · simpa only [dist_eq_norm] using hg.dist_le hx hy
        · simpa only [dist_eq_norm] using hf.dist_le hx hy
        · exact hgnorm y hy
      _ = _ := by ring
  rw [edist_nndist, edist_nndist,
    ← ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg, ← ENNReal.coe_mul,
    ENNReal.coe_le_coe]
  exact_mod_cast hbound

/-- A bilinear map preserves global Hölder continuity for uniformly bounded functions. -/
theorem holderWith_comp₂ (B : E →L[𝕜] F →L[𝕜] G)
    {α Kf Kg Mf Mg : ℝ≥0} {f : X → E} {g : X → F}
    (hf : HolderWith Kf α f) (hg : HolderWith Kg α g)
    (hfnorm : ∀ x, ‖f x‖ ≤ Mf) (hgnorm : ∀ x, ‖g x‖ ≤ Mg) :
    HolderWith (‖B‖₊ * (Mf * Kg + Mg * Kf)) α (fun x ↦ B (f x) (g x)) :=
  holderOnWith_univ.mp (B.holderOnWith_comp₂ (hf.holderOnWith univ)
    (hg.holderOnWith univ) (fun x _ ↦ hfnorm x) (fun x _ ↦ hgnorm x))

end ContinuousLinearMap
