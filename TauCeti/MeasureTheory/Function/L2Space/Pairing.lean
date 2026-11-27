/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Norm

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
* `MeasureTheory.Lp.integral_norm_sq_eq_and_integrable_of_ae_eq`: a covector field almost
  everywhere equal to the pairing `⟪h, ·⟫` with `h ∈ L²(ν, V)` is square integrable, with the
  squared norm of `h` as the integral of its squared norm.
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

/-- A covector field almost everywhere equal to `⟪h, ·⟫` for `h ∈ L²(ν, V)` is square integrable
with the norm of `h`. -/
theorem integral_norm_sq_eq_and_integrable_of_ae_eq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {h : Lp V 2 ν} {η : X → V →L[ℝ] ℝ}
    (hae : (fun x ↦ innerSL ℝ (h x)) =ᵐ[ν] η) :
    ∫ x, ‖η x‖ ^ 2 ∂ν = ‖h‖ ^ 2 ∧ Integrable (fun x ↦ ‖η x‖ ^ 2) ν := by
  have hn : (fun x ↦ ‖η x‖ ^ 2) =ᵐ[ν] fun x ↦ ‖h x‖ ^ 2 :=
    hae.mono fun x hx ↦ by
      simp only at hx ⊢
      rw [← hx, innerSL_apply_norm]
  have hm : MemLp (⇑h) ((2 : ℕ) : ENNReal) ν := by simpa using Lp.memLp h
  refine ⟨?_, (hm.integrable_norm_pow two_ne_zero).congr hn.symm⟩
  rw [integral_congr_ae hn, Lp.integral_norm_sq_eq_norm_sq]

end MeasureTheory.Lp
