/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Bilinear operations on bounded Hölder functions

A continuous bilinear map sends two bounded Hölder functions of the same exponent to a Hölder
function. The estimate keeps the uniform bounds separate from the Hölder constants, so it also
applies to restrictions and yields the product estimate for the supremum-plus-Hölder norm.

For scalar multiplication by a factor vanishing off a set `s`, the second function need only be
Hölder and bounded on `s` (`HolderWith.smul_of_eq_zero`): this is how a cutoff extends a function
given on `s` to the whole space.

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

namespace HolderWith

variable {𝕜 X G : Type*} [NontriviallyNormedField 𝕜] [PseudoEMetricSpace X]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A scalar factor that is Hölder on the whole space and vanishes off a set `s` turns a function
that is Hölder and bounded only on `s` into a function that is Hölder on the whole space. Nothing
is assumed about `f` off `s`: there the product vanishes, and across the boundary of `s` only the
bound on `f` and the Hölder bound on `c` enter. This is how a cutoff `c` extends a function given
on `s`. -/
theorem smul_of_eq_zero {α Kc Kf Mc Mf : ℝ≥0} {c : X → 𝕜} {f : X → G} {s : Set X}
    (hc : HolderWith Kc α c) (hf : HolderOnWith Kf α f s) (hcnorm : ∀ x, ‖c x‖ ≤ Mc)
    (hfnorm : ∀ x ∈ s, ‖f x‖ ≤ Mf) (hc0 : ∀ x ∉ s, c x = 0) :
    HolderWith (Mc * Kf + Mf * Kc) α (fun x ↦ c x • f x) := by
  -- Across the boundary of `s`, the product at `x ∈ s` is `(c x - c y) • f x`.
  have hcross : ∀ x ∈ s, ∀ y ∉ s, edist (c x • f x) (c y • f y) ≤
      (Mc * Kf + Mf * Kc) * edist x y ^ (α : ℝ) := by
    intro x hx y hy
    calc
      edist (c x • f x) (c y • f y) = ‖c x - c y‖₊ * ‖f x‖₊ := by
        rw [hc0 y hy, sub_zero, zero_smul, edist_zero_right, enorm_eq_nnnorm, nnnorm_smul,
          ENNReal.coe_mul]
      _ ≤ (Kc * edist x y ^ (α : ℝ)) * Mf := by
        gcongr
        · rw [← nndist_eq_nnnorm, ← edist_nndist]
          exact hc.edist_le x y
        · exact_mod_cast hfnorm x hx
      _ ≤ (Mc * Kf + Mf * Kc) * edist x y ^ (α : ℝ) := by
        rw [mul_comm _ (Mf : ℝ≥0∞), ← mul_assoc]
        gcongr
        exact_mod_cast le_add_self
  let B : 𝕜 →L[𝕜] G →L[𝕜] G := ContinuousLinearMap.lsmul 𝕜 𝕜
  have hconst : ‖B‖₊ * (Mc * Kf + Mf * Kc) ≤ Mc * Kf + Mf * Kc := by
    calc
      _ ≤ 1 * (Mc * Kf + Mf * Kc) :=
        by
          gcongr
          exact ContinuousLinearMap.opNNNorm_lsmul_le
      _ = _ := one_mul _
  have hboth := (B.holderOnWith_comp₂ (hc.holderOnWith s) hf
    (fun x _ ↦ hcnorm x) hfnorm).mono_const hconst
  intro x y
  by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
  · simpa only [B, ContinuousLinearMap.lsmul_apply] using hboth.edist_le hx hy
  · exact hcross x hx y hy
  · rw [edist_comm, edist_comm x]
    exact hcross y hy x hx
  · simp [hc0 x hx, hc0 y hy]

end HolderWith
