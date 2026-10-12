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
Here the map may be semilinear over arbitrary nontrivially normed fields, the spaces are
seminormed, the domain is a pseudo-emetric space, and the operator norm is explicit.
-/

public section

open Set
open scoped NNReal ENNReal

namespace ContinuousLinearMap

variable {𝕜 𝕜₂ 𝕜₃ X E F G : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [NontriviallyNormedField 𝕜₃] [PseudoEMetricSpace X]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜₃ G]
  {σ₁₃ : 𝕜 →+* 𝕜₃} {σ₂₃ : 𝕜₂ →+* 𝕜₃} [RingHomIsometric σ₁₃] [RingHomIsometric σ₂₃]

/-- A bilinear map preserves Hölder continuity on a set when both input functions are bounded
there. The constant is `‖B‖ * (Mf * Kg + Mg * Kf)`. -/
theorem holderOnWith_comp₂ (B : E →SL[σ₁₃] F →SL[σ₂₃] G)
    {α Kf Kg Mf Mg : ℝ≥0} {f : X → E} {g : X → F} {s : Set X}
    (hf : HolderOnWith Kf α f s) (hg : HolderOnWith Kg α g s)
    (hfnorm : ∀ x ∈ s, ‖f x‖ ≤ Mf) (hgnorm : ∀ x ∈ s, ‖g x‖ ≤ Mg) :
    HolderOnWith (‖B‖₊ * (Mf * Kg + Mg * Kf)) α (fun x ↦ B (f x) (g x)) s := by
  intro x hx y hy
  have hsplit : B (f x) (g x) - B (f y) (g y) =
      B (f x) (g x - g y) + B (f x - f y) (g y) := by
    simp only [map_sub, sub_apply]
    abel
  have hle : ‖B (f x) (g x) - B (f y) (g y)‖ ≤
      ‖B‖ * ‖f x‖ * ‖g x - g y‖ + ‖B‖ * ‖f x - f y‖ * ‖g y‖ := by
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _))
  calc
    edist (B (f x) (g x)) (B (f y) (g y)) ≤
        ‖B‖₊ * ‖f x‖₊ * edist (g x) (g y) + ‖B‖₊ * edist (f x) (f y) * ‖g y‖₊ := by
      simp only [edist_nndist, nndist_eq_nnnorm]
      exact_mod_cast hle
    _ ≤ ‖B‖₊ * Mf * (Kg * edist x y ^ (α : ℝ)) + ‖B‖₊ * (Kf * edist x y ^ (α : ℝ)) * Mg := by
      gcongr
      · exact_mod_cast hfnorm x hx
      · exact hg.edist_le hx hy
      · exact hf.edist_le hx hy
      · exact_mod_cast hgnorm y hy
    _ = _ := by
      push_cast
      ring

/-- A bilinear map preserves global Hölder continuity for uniformly bounded functions. -/
theorem holderWith_comp₂ (B : E →SL[σ₁₃] F →SL[σ₂₃] G)
    {α Kf Kg Mf Mg : ℝ≥0} {f : X → E} {g : X → F}
    (hf : HolderWith Kf α f) (hg : HolderWith Kg α g)
    (hfnorm : ∀ x, ‖f x‖ ≤ Mf) (hgnorm : ∀ x, ‖g x‖ ≤ Mg) :
    HolderWith (‖B‖₊ * (Mf * Kg + Mg * Kf)) α (fun x ↦ B (f x) (g x)) :=
  holderOnWith_univ.mp (B.holderOnWith_comp₂ (hf.holderOnWith univ)
    (hg.holderOnWith univ) (fun x _ ↦ hfnorm x) (fun x _ ↦ hgnorm x))

end ContinuousLinearMap
