/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LipschitzSmooth.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Operations preserving Lipschitz smoothness

`LipschitzSmoothWith 𝕜 K f` says that `f` is differentiable with first-order Taylor remainder at
most `K / 2 * dist x y ^ 2`. The remainder bound with respect to any field of continuous linear
maps already implies differentiability, which gives a constructor with no derivative hypothesis.

This file also records how the constant behaves under the basic operations: it may be enlarged,
constants and continuous linear maps are `0`-smooth, adding a constant does not change it, a sum
is smooth with the sum of the constants, and a scalar multiple `c • f` is smooth with the constant
multiplied by `‖c‖₊`.

## Main results

* `LipschitzSmoothWith.of_norm_sub_sub_le`: smoothness from the remainder bound alone.
* `LipschitzSmoothWith.weaken`: monotonicity in the constant.
* `LipschitzSmoothWith.const`, `ContinuousLinearMap.lipschitzSmoothWith`: constants and continuous
  linear maps are `0`-smooth.
* `LipschitzSmoothWith.const_add`, `LipschitzSmoothWith.add_const`, `LipschitzSmoothWith.add`,
  `LipschitzSmoothWith.const_smul`: translates, sums and scalar multiples.
-/

public section

open scoped NNReal

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {K K' : ℝ≥0} {f g : E → F}

namespace LipschitzSmoothWith

/-- A function whose first-order remainder with respect to a field `f'` of continuous linear maps
is at most `K / 2 * dist x y ^ 2` is `K`-smooth. The bound alone makes `f' x` the derivative of
`f` at `x`, so no differentiability has to be supplied. -/
theorem of_norm_sub_sub_le {f' : E → E →L[𝕜] F}
    (hbound : ∀ x y, ‖f y - f x - f' x (y - x)‖ ≤ K / 2 * dist x y ^ 2) :
    LipschitzSmoothWith 𝕜 K f := by
  refine .of_hasFDerivAt (fun x ↦ .of_isLittleO ?_) hbound
  refine (Asymptotics.IsBigO.of_bound (K / 2) (.of_forall fun y ↦ ?_)).trans_isLittleO
    (Asymptotics.isLittleO_pow_sub_sub x one_lt_two)
  simpa [dist_eq_norm'] using hbound x y

/-- A `K`-smooth function is `K'`-smooth for every `K' ≥ K`. -/
theorem weaken (hf : LipschitzSmoothWith 𝕜 K f) (hK : K ≤ K') : LipschitzSmoothWith 𝕜 K' f :=
  ⟨hf.differentiable, fun x y ↦ (hf.fderiv_norm_le x y).trans <| by gcongr⟩

variable (𝕜 E) in
/-- A constant function is `0`-smooth. -/
protected theorem const (c : F) : LipschitzSmoothWith 𝕜 0 fun _ : E ↦ c :=
  .of_hasFDerivAt (fun x ↦ hasFDerivAt_const c x) fun x y ↦ by simp

/-- Adding a constant to a `K`-smooth function gives a `K`-smooth function. -/
theorem const_add (hf : LipschitzSmoothWith 𝕜 K f) (c : F) :
    LipschitzSmoothWith 𝕜 K fun x ↦ c + f x :=
  .of_hasFDerivAt (fun x ↦ (hf.differentiable x).hasFDerivAt.const_add c) fun x y ↦ by
    simpa only [add_sub_add_left_eq_sub] using hf.fderiv_norm_le x y

/-- Adding a constant on the right to a `K`-smooth function gives a `K`-smooth function. -/
theorem add_const (hf : LipschitzSmoothWith 𝕜 K f) (c : F) :
    LipschitzSmoothWith 𝕜 K fun x ↦ f x + c :=
  .of_hasFDerivAt (fun x ↦ (hf.differentiable x).hasFDerivAt.add_const c) fun x y ↦ by
    simpa only [add_sub_add_right_eq_sub] using hf.fderiv_norm_le x y

/-- The sum of a `K`-smooth and a `K'`-smooth function is `(K + K')`-smooth. -/
theorem add (hf : LipschitzSmoothWith 𝕜 K f) (hg : LipschitzSmoothWith 𝕜 K' g) :
    LipschitzSmoothWith 𝕜 (K + K') (f + g) := by
  refine .of_hasFDerivAt
    (fun x ↦ (hf.differentiable x).hasFDerivAt.add (hg.differentiable x).hasFDerivAt) fun x y ↦ ?_
  calc ‖(f + g) y - (f + g) x - (fderiv 𝕜 f x + fderiv 𝕜 g x) (y - x)‖
      = ‖(f y - f x - fderiv 𝕜 f x (y - x)) + (g y - g x - fderiv 𝕜 g x (y - x))‖ := by
        simp only [Pi.add_apply, add_apply]
        congr 1
        abel
    _ ≤ K / 2 * dist x y ^ 2 + K' / 2 * dist x y ^ 2 :=
        (norm_add_le _ _).trans (add_le_add (hf.fderiv_norm_le x y) (hg.fderiv_norm_le x y))
    _ = (K + K' : ℝ≥0) / 2 * dist x y ^ 2 := by
        push_cast
        ring

/-- A scalar multiple `c • f` of a `K`-smooth function is `(‖c‖₊ * K)`-smooth. -/
theorem const_smul (hf : LipschitzSmoothWith 𝕜 K f) (c : 𝕜) :
    LipschitzSmoothWith 𝕜 (‖c‖₊ * K) (c • f) := by
  refine .of_hasFDerivAt (fun x ↦ (hf.differentiable x).hasFDerivAt.const_smul c) fun x y ↦ ?_
  calc ‖(c • f) y - (c • f) x - (c • fderiv 𝕜 f x) (y - x)‖
      = ‖c‖ * ‖f y - f x - fderiv 𝕜 f x (y - x)‖ := by
        rw [← norm_smul]
        simp only [Pi.smul_apply, smul_apply, smul_sub]
    _ ≤ ‖c‖ * (K / 2 * dist x y ^ 2) :=
        mul_le_mul_of_nonneg_left (hf.fderiv_norm_le x y) (norm_nonneg c)
    _ = (‖c‖₊ * K : ℝ≥0) / 2 * dist x y ^ 2 := by
        push_cast
        ring

end LipschitzSmoothWith

/-- A continuous linear map is `0`-smooth. -/
protected theorem ContinuousLinearMap.lipschitzSmoothWith (ℓ : E →L[𝕜] F) :
    LipschitzSmoothWith 𝕜 0 ℓ :=
  .of_hasFDerivAt (fun _ ↦ ℓ.hasFDerivAt) fun x y ↦ by simp
