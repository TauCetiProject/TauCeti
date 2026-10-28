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
import TauCeti.Analysis.Convex.Uniform
import TauCeti.Analysis.InnerProductSpace.Clarkson
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Uniform convexity of `Lᵖ` spaces for `2 ≤ p < ∞`

Let `E` be a normed group whose norm satisfies the parallelogram identity
(`InnerProductSpaceable`), for instance a real or complex inner product space. For `2 ≤ p < ∞`,
integrating the pointwise Clarkson inequality `TauCeti.norm_add_rpow_add_norm_sub_rpow_le` gives
**Clarkson's inequality**

`‖f + g‖ ^ p + ‖f - g‖ ^ p ≤ 2 ^ (p - 1) * (‖f‖ ^ p + ‖g‖ ^ p)`

for `f g : Lp E p μ`. On the unit sphere it says `‖f + g‖ ^ p ≤ 2 ^ p - ‖f - g‖ ^ p`, so
`Lp E p μ` is uniformly convex. By the Milman–Pettis theorem it is then reflexive when `E` is
complete.

## Main statements

* `MeasureTheory.Lp.norm_add_rpow_add_norm_sub_rpow_le`: Clarkson's inequality for `Lᵖ`,
  `2 ≤ p < ∞`.
* `MeasureTheory.Lp.uniformConvexSpace`: `Lp E p μ` is uniformly convex for `2 ≤ p < ∞`.
* `MeasureTheory.Lp.surjective_inclusionInDoubleDual`: for complete `E`, `Lp E p μ` is
  reflexive for `2 ≤ p < ∞`.

## References

* J. A. Clarkson, *Uniformly convex spaces*, Trans. Amer. Math. Soc. 40 (1936), 396–414.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 4.10.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpaceable E] {p : ℝ≥0∞}

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

/-- **`Lᵖ` is uniformly convex for `2 ≤ p < ∞`** when the norm of `E` satisfies the
parallelogram identity. -/
theorem uniformConvexSpace [Fact (1 ≤ p)] (hp : 2 ≤ p) (hp_top : p ≠ ∞) :
    UniformConvexSpace (Lp E p μ) := by
  refine ⟨fun ε hε ↦ ?_⟩
  set q := p.toReal with hq_def
  have hq : 2 ≤ q := by simpa using ENNReal.toReal_mono hp_top hp
  have hq0 : 0 < q := by linarith
  -- Work with `e = min ε 2`, so that `2 ^ q - e ^ q` is nonnegative.
  set e := min ε 2
  have he : 0 < e := lt_min hε two_pos
  have hepow : e ^ q ≤ 2 ^ q := Real.rpow_le_rpow he.le (min_le_right ε 2) hq0.le
  have hroot : (2 ^ q - e ^ q) ^ q⁻¹ < 2 := by
    calc (2 ^ q - e ^ q) ^ q⁻¹ < ((2 : ℝ) ^ q) ^ q⁻¹ :=
          Real.rpow_lt_rpow (sub_nonneg.2 hepow) (sub_lt_self _ (Real.rpow_pos_of_pos he q))
            (inv_pos.2 hq0)
      _ = 2 := Real.rpow_rpow_inv zero_le_two hq0.ne'
  refine ⟨2 - (2 ^ q - e ^ q) ^ q⁻¹, sub_pos.2 hroot, fun f hf g hg hfg ↦ ?_⟩
  rw [sub_sub_cancel]
  -- Clarkson's inequality on the unit sphere bounds `‖f + g‖ ^ q` by `2 ^ q - e ^ q`.
  have hclarkson := norm_add_rpow_add_norm_sub_rpow_le hp hp_top f g
  rw [hf, hg, Real.one_rpow, ← hq_def, one_add_one_eq_two,
    Real.rpow_sub_one two_ne_zero, div_mul_cancel₀ _ two_ne_zero] at hclarkson
  have hsub : e ^ q ≤ ‖f - g‖ ^ q :=
    Real.rpow_le_rpow he.le ((min_le_left ε 2).trans hfg) hq0.le
  have hadd : ‖f + g‖ ^ q ≤ 2 ^ q - e ^ q := by linarith
  calc ‖f + g‖ = (‖f + g‖ ^ q) ^ q⁻¹ := (Real.rpow_rpow_inv (norm_nonneg _) hq0.ne').symm
    _ ≤ (2 ^ q - e ^ q) ^ q⁻¹ :=
      Real.rpow_le_rpow (by positivity) hadd (inv_nonneg.2 hq0.le)

/-- **`Lᵖ` is reflexive for `2 ≤ p < ∞`** when `E` is a real Banach space whose norm satisfies
the parallelogram identity, such as a real or complex Hilbert space. This is the Milman–Pettis
theorem applied to `MeasureTheory.Lp.uniformConvexSpace`. -/
theorem surjective_inclusionInDoubleDual [Fact (1 ≤ p)] [NormedSpace ℝ E] [CompleteSpace E]
    (hp : 2 ≤ p) (hp_top : p ≠ ∞) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ (Lp E p μ)) :=
  have := uniformConvexSpace (E := E) (μ := μ) hp hp_top
  TauCeti.surjective_inclusionInDoubleDual_of_uniformConvexSpace

end MeasureTheory.Lp
