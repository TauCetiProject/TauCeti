/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Pairing with a real square-integrable function

A real datum `f ∈ L²(ν)` and a continuous linear map `T : W → L²(ν)` give the bounded functional
`v ↦ ∫ f · T v dν` on `W`. This is how data enter the weak form of a boundary value problem: an
interior datum is paired through the value map of a Sobolev space, and a boundary datum through a
trace.

## Main declarations

* `MeasureTheory.Lp.pairingL`: the functional `v ↦ ∫ f · T v dν`, with its evaluation
  `MeasureTheory.Lp.pairingL_apply` and the bound `MeasureTheory.Lp.norm_pairingL_le` by
  `‖f‖ ‖T‖`.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace MeasureTheory.Lp

variable {X W : Type*} [MeasurableSpace X] {ν : Measure X} [SeminormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- The pairing `v ↦ ∫ f · T v dν` of a space `W` with a real datum `f ∈ L²(ν)`, through a
continuous linear map `T : W → L²(ν)`: the `L²` inner product with `f` composed with `T`. -/
def pairingL (f : Lp ℝ 2 ν) (T : W →L[ℝ] Lp ℝ 2 ν) : StrongDual ℝ W :=
  (innerSL ℝ f).comp T

/-- The pairing of `W` with `f ∈ L²(ν)` through `T` evaluates to `∫ f · T v dν`. -/
@[simp]
theorem pairingL_apply (f : Lp ℝ 2 ν) (T : W →L[ℝ] Lp ℝ 2 ν) (v : W) :
    pairingL f T v = ∫ x, f x * T v x ∂ν := by
  simp only [pairingL, ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def,
    RCLike.inner_apply, conj_trivial]
  exact integral_congr_ae (ae_of_all _ fun _ => mul_comm _ _)

/-- The pairing of `W` with `f ∈ L²(ν)` through `T` has norm at most `‖f‖ ‖T‖`. -/
theorem norm_pairingL_le (f : Lp ℝ 2 ν) (T : W →L[ℝ] Lp ℝ 2 ν) :
    ‖pairingL f T‖ ≤ ‖f‖ * ‖T‖ :=
  ((innerSL ℝ f).opNorm_comp_le T).trans_eq (by rw [innerSL_apply_norm])

end MeasureTheory.Lp
