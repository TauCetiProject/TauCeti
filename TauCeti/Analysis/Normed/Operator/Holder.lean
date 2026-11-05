/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Bilinear operations on bounded Hölder functions

A continuous bilinear map sends two bounded Hölder functions of the same exponent to a Hölder
function. The estimate keeps the uniform bounds separate from the Hölder constants, so it also
applies to restrictions and yields the product estimate for the supremum-plus-Hölder norm.

If one argument vanishes off a set `s`, the other need only be Hölder and bounded on `s`
(`ContinuousLinearMap.holderWith_comp₂_of_eq_zero`, and `HolderWith.smul_of_eq_zero` for scalar
multiplication): this is how a cutoff extends a function given on `s` to the whole space, and how
freezing a coefficient on the support of a localized function is estimated.

For a scalar-valued continuous multilinear map `L`, the map `L.smulRight (g x - g y)` has norm at
most `‖L‖` times the Hölder bound on the increment of `g` (`HolderWith.norm_smulRight_sub_le`).

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

/-- A bilinear map preserves global Hölder continuity when its second argument vanishes off a set
`s` on which both arguments are bounded and the first one is Hölder. Nothing is assumed about `f`
off `s`: there the product vanishes, and across the boundary of `s` only the bound on `f` and the
Hölder bound on `g` enter. -/
theorem holderWith_comp₂_of_eq_zero (B : E →SL[σ₁₃] F →SL[σ₂₃] G)
    {α Kf Kg Mf Mg : ℝ≥0} {f : X → E} {g : X → F} {s : Set X}
    (hf : HolderOnWith Kf α f s) (hg : HolderWith Kg α g)
    (hfnorm : ∀ x ∈ s, ‖f x‖ ≤ Mf) (hgnorm : ∀ x ∈ s, ‖g x‖ ≤ Mg) (hg0 : ∀ x ∉ s, g x = 0) :
    HolderWith (‖B‖₊ * (Mf * Kg + Mg * Kf)) α (fun x ↦ B (f x) (g x)) := by
  -- Across the boundary of `s`, the product at `x ∈ s` is `B (f x) (g x - g y)`.
  have hcross : ∀ x ∈ s, ∀ y ∉ s, edist (B (f x) (g x)) (B (f y) (g y)) ≤
      (‖B‖₊ * (Mf * Kg + Mg * Kf)) * edist x y ^ (α : ℝ) := by
    intro x hx y hy
    have hle : ‖B (f x) (g x) - B (f y) (g y)‖ ≤ ‖B‖ * ‖f x‖ * ‖g x - g y‖ := by
      rw [hg0 y hy, map_zero, sub_zero, sub_zero]
      exact B.le_opNorm₂ _ _
    calc
      edist (B (f x) (g x)) (B (f y) (g y)) ≤ ‖B‖₊ * ‖f x‖₊ * edist (g x) (g y) := by
        simp only [edist_nndist, nndist_eq_nnnorm]
        exact_mod_cast hle
      _ ≤ ‖B‖₊ * Mf * (Kg * edist x y ^ (α : ℝ)) := by
        gcongr
        · exact_mod_cast hfnorm x hx
        · exact hg.edist_le x y
      _ ≤ (‖B‖₊ * (Mf * Kg + Mg * Kf)) * edist x y ^ (α : ℝ) := by
        rw [← mul_assoc, mul_assoc (‖B‖₊ : ℝ≥0∞)]
        gcongr
        exact_mod_cast le_self_add
  have hboth := B.holderOnWith_comp₂ hf (hg.holderOnWith s) hfnorm hgnorm
  intro x y
  by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
  · exact hboth.edist_le hx hy
  · exact hcross x hx y hy
  · rw [edist_comm, edist_comm x]
    exact hcross y hy x hx
  · simp [hg0 x hx, hg0 y hy]

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
  have h := (ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] G →L[𝕜] G).flip.holderWith_comp₂_of_eq_zero
    hf hc hfnorm (fun x _ ↦ hcnorm x) hc0
  refine h.mono ?_
  rw [ContinuousLinearMap.opNNNorm_flip, add_comm]
  exact mul_le_of_le_one_left zero_le ContinuousLinearMap.opNNNorm_lsmul_le

/-- For a scalar-valued continuous multilinear map `L` and an `α`-Hölder function `g` with
constant `H`, `‖L.smulRight (g x - g y)‖ ≤ H (‖L‖ dist(x, y)^α)`. -/
theorem norm_smulRight_sub_le {ι Y : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [PseudoMetricSpace Y]
    {H α : ℝ≥0} {g : Y → G} (hg : HolderWith H α g) (L : ContinuousMultilinearMap 𝕜 E 𝕜)
    (x y : Y) : ‖L.smulRight (g x - g y)‖ ≤ H * (‖L‖ * dist x y ^ (α : ℝ)) := by
  rw [ContinuousMultilinearMap.norm_smulRight, mul_left_comm, ← dist_eq_norm]
  exact mul_le_mul_of_nonneg_left (hg.dist_le x y) (norm_nonneg _)

end HolderWith
