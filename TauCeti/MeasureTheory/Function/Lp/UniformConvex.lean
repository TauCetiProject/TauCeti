/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.Convex.Uniform.Rpow
import TauCeti.Analysis.InnerProductSpace.Clarkson
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Uniform convexity of `Lᵖ` spaces for `1 < p < ∞`

Let `E` be a uniformly convex real normed space and `1 < p < ∞`. For every `η > 0` there is
`δ > 0` such that

`‖f + g‖ ^ p + δ * ‖f - g‖ ^ p ≤ (2 ^ (p - 1) + δ * η) * (‖f‖ ^ p + ‖g‖ ^ p)`

for all `f g : Lp E p μ`. This is the integral of the pointwise inequality
`TauCeti.exists_forall_norm_add_rpow_add_mul_norm_sub_rpow_le`. On the unit sphere, taking `η`
small compared with `‖f - g‖ ^ p` bounds `‖f + g‖` away from `2`, so the Lebesgue–Bochner space
`Lp E p μ` is uniformly convex. By the Milman–Pettis theorem it is then reflexive when `E` is
complete. The scalar spaces `Lp ℝ p μ` and `Lp ℂ p μ` are the main examples, and so is
`Lp E p μ` for a Hilbert space `E`.

When the norm of `E` satisfies the parallelogram identity and `2 ≤ p < ∞`, integrating the
pointwise Clarkson inequality `TauCeti.norm_add_rpow_add_norm_sub_rpow_le` gives the sharper
**Clarkson inequality**

`‖f + g‖ ^ p + ‖f - g‖ ^ p ≤ 2 ^ (p - 1) * (‖f‖ ^ p + ‖g‖ ^ p)`,

which yields an explicit modulus of convexity.

## Main statements

* `MeasureTheory.Lp.norm_add_rpow_add_norm_sub_rpow_le`: Clarkson's inequality for `Lᵖ`,
  `2 ≤ p < ∞`.
* `MeasureTheory.Lp.exists_forall_norm_add_rpow_add_mul_norm_sub_rpow_le`: the uniform convexity
  estimate for `Lᵖ`, `1 < p < ∞`, with values in a uniformly convex space.
* `MeasureTheory.Lp.uniformConvexSpace`: `Lp E p μ` is uniformly convex for `1 < p < ∞`.
* `MeasureTheory.Lp.surjective_inclusionInDoubleDual`: for complete uniformly convex `E`,
  `Lp E p μ` is reflexive for `1 < p < ∞`.

## References

* J. A. Clarkson, *Uniformly convex spaces*, Trans. Amer. Math. Soc. 40 (1936), 396–414.
* M. M. Day, *Some more uniformly convex spaces*, Bull. Amer. Math. Soc. 47 (1941), 504–507.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 4.10.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  {p : ℝ≥0∞}

section Clarkson

variable [InnerProductSpaceable E]

/-- **Clarkson's inequality.** For `2 ≤ p < ∞` and `f g : Lp E p μ`, where the norm of `E`
satisfies the parallelogram identity,
`‖f + g‖ ^ p + ‖f - g‖ ^ p ≤ 2 ^ (p - 1) * (‖f‖ ^ p + ‖g‖ ^ p)`. -/
theorem norm_add_rpow_add_norm_sub_rpow_le (hp : 2 ≤ p) (hp_top : p ≠ ∞) (f g : Lp E p μ) :
    ‖f + g‖ ^ p.toReal + ‖f - g‖ ^ p.toReal ≤
      2 ^ (p.toReal - 1) * (‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le (by norm_num) hp).ne'
  have hq : 2 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp_top hp
  have hint (h : Lp E p μ) : Integrable (fun x ↦ ‖h x‖ ^ p.toReal) μ :=
    (Lp.memLp h).integrable_norm_rpow hp0 hp_top
  rw [← Lp.integral_norm_rpow_eq_norm_rpow hp0 hp_top, ← Lp.integral_norm_rpow_eq_norm_rpow hp0
    hp_top, ← Lp.integral_norm_rpow_eq_norm_rpow hp0 hp_top f,
    ← Lp.integral_norm_rpow_eq_norm_rpow hp0 hp_top g, ← integral_add (hint _) (hint _),
    ← integral_add (hint _) (hint _), ← integral_const_mul]
  refine integral_mono_ae ((hint _).add (hint _)) (((hint _).add (hint _)).const_mul _) ?_
  filter_upwards [Lp.coeFn_add f g, Lp.coeFn_sub f g] with x hadd hsub
  simpa only [hadd, hsub, Pi.add_apply, Pi.sub_apply] using
    TauCeti.norm_add_rpow_add_norm_sub_rpow_le hq (f x) (g x)

end Clarkson

section UniformConvex

variable [NormedSpace ℝ E] [UniformConvexSpace E]

/-- **The uniform convexity estimate for `Lᵖ`.** Let `E` be a uniformly convex real normed
space and `1 < p < ∞`. For every `η > 0` there is `δ > 0` such that for all `f g : Lp E p μ`,
`‖f + g‖ ^ p + δ * ‖f - g‖ ^ p ≤ (2 ^ (p - 1) + δ * η) * (‖f‖ ^ p + ‖g‖ ^ p)`.
The constant `δ` depends only on `E`, `p` and `η`. -/
theorem exists_forall_norm_add_rpow_add_mul_norm_sub_rpow_le (hp : 1 < p) (hp_top : p ≠ ∞)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ, 0 < δ ∧ ∀ f g : Lp E p μ, ‖f + g‖ ^ p.toReal + δ * ‖f - g‖ ^ p.toReal ≤
      (2 ^ (p.toReal - 1) + δ * η) * (‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hq : 1 < p.toReal := by simpa using ENNReal.toReal_strict_mono hp_top hp
  obtain ⟨δ, hδ, h⟩ := TauCeti.exists_forall_norm_add_rpow_add_mul_norm_sub_rpow_le (E := E) hq hη
  refine ⟨δ, hδ, fun f g ↦ ?_⟩
  have hint (h : Lp E p μ) : Integrable (fun x ↦ ‖h x‖ ^ p.toReal) μ :=
    (Lp.memLp h).integrable_norm_rpow hp0 hp_top
  have hnorm (h : Lp E p μ) : ‖h‖ ^ p.toReal = ∫ x, ‖h x‖ ^ p.toReal ∂μ :=
    (Lp.integral_norm_rpow_eq_norm_rpow hp0 hp_top h).symm
  rw [hnorm (f + g), hnorm (f - g), hnorm f, hnorm g, ← integral_const_mul,
    ← integral_add (hint _) ((hint _).const_mul _), ← integral_add (hint _) (hint _),
    ← integral_const_mul]
  refine integral_mono_ae ((hint _).add ((hint _).const_mul _))
    (((hint _).add (hint _)).const_mul _) ?_
  filter_upwards [Lp.coeFn_add f g, Lp.coeFn_sub f g] with x hadd hsub
  simpa only [hadd, hsub, Pi.add_apply, Pi.sub_apply] using h (f x) (g x)

/-- **`Lᵖ` is uniformly convex for `1 < p < ∞`** when `E` is a uniformly convex real normed
space. -/
theorem uniformConvexSpace [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ∞) :
    UniformConvexSpace (Lp E p μ) := by
  refine ⟨fun ε hε ↦ ?_⟩
  have hq : 1 < p.toReal := by simpa using ENNReal.toReal_strict_mono hp_top hp
  set q := p.toReal
  have hq0 : 0 < q := by linarith
  have hεq : 0 < ε ^ q := Real.rpow_pos_of_pos hε q
  -- Apply the estimate with `η = ε ^ q / 4`; on the unit sphere it bounds `‖f + g‖ ^ q`
  -- by `2 ^ q - δ * ε ^ q / 2`.
  obtain ⟨δ, hδ, h⟩ := exists_forall_norm_add_rpow_add_mul_norm_sub_rpow_le (E := E) (μ := μ)
    hp hp_top (div_pos hεq four_pos)
  set A := max (2 ^ q - δ * ε ^ q / 2) 0
  have hA : A < 2 ^ q := max_lt (by linarith [mul_pos hδ hεq]) (by positivity)
  have hroot : A ^ q⁻¹ < 2 := by
    calc A ^ q⁻¹ < ((2 : ℝ) ^ q) ^ q⁻¹ :=
          Real.rpow_lt_rpow (le_max_right _ _) hA (inv_pos.2 hq0)
      _ = 2 := Real.rpow_rpow_inv zero_le_two hq0.ne'
  refine ⟨2 - A ^ q⁻¹, sub_pos.2 hroot, fun f hf g hg hfg ↦ ?_⟩
  rw [sub_sub_cancel]
  have hfg' := h f g
  rw [hf, hg, Real.one_rpow] at hfg'
  have hsub : ε ^ q ≤ ‖f - g‖ ^ q := Real.rpow_le_rpow hε.le hfg hq0.le
  have h2 : (2 : ℝ) ^ (q - 1) * (1 + 1) = 2 ^ q := by
    rw [Real.rpow_sub_one two_ne_zero]
    ring
  have hadd : ‖f + g‖ ^ q ≤ A := le_max_of_le_left (by nlinarith)
  calc ‖f + g‖ = (‖f + g‖ ^ q) ^ q⁻¹ := (Real.rpow_rpow_inv (norm_nonneg _) hq0.ne').symm
    _ ≤ A ^ q⁻¹ := Real.rpow_le_rpow (by positivity) hadd (inv_nonneg.2 hq0.le)

end UniformConvex

/-- **`Lᵖ` is reflexive for `1 < p < ∞`** when `E` is a real or complex Banach space that is
uniformly convex, such as `ℝ`, `ℂ` or a Hilbert space. This is the Milman–Pettis theorem applied
to `MeasureTheory.Lp.uniformConvexSpace`. -/
theorem surjective_inclusionInDoubleDual {𝕜 : Type*} [RCLike 𝕜] [Fact (1 ≤ p)]
    [NormedSpace 𝕜 E] [CompleteSpace E] [UniformConvexSpace E] (hp : 1 < p) (hp_top : p ≠ ∞) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 (Lp E p μ)) :=
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have := uniformConvexSpace (E := E) (μ := μ) hp hp_top
  TauCeti.surjective_inclusionInDoubleDual_of_uniformConvexSpace

end MeasureTheory.Lp
