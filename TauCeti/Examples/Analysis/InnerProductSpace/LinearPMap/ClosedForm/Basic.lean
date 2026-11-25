/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ClosedForm.Basic

/-!
# Examples of represented operators of scalar forms

`ContinuousLinearMap.closedFormOperator_smul_id_smul_innerSL` computes the operator represented by
the scalar form `q(u, v) = b ⟪u, v⟫` along `j = a • id` as `(b / a ^ 2) • id`. Three worked
examples:

* `V = H = ℂ`, `j = id`, `q(u, v) = 2 conj(u) v` represents `A = 2 I`, at `u = 1`, `v = i` both
  sides of `q(u, v) = ⟪A u, v⟫` are `2 i`, and `q` is coercive with `α = 0` and `c = 2`;
* `q = 0` with `j = id` represents the zero operator; the shifted forms with `α = 1` and with
  `α = 2` are both coercive with `c = 1`;
* `j = 2 id` on `ℂ` and `q(u, v) = conj(u) v` represent `A = (1 / 4) I`, and
  `⟪A (2u), 2v⟫ = conj(u) v`, while `A = I` would multiply the pairing by `4`.
-/

public section

open ContinuousLinearMap

open scoped InnerProductSpace ComplexConjugate

namespace TauCeti.Examples.ClosedForm

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- On `ℂ` with `j = id`, the form `q(u, v) = 2 conj(u) v` represents `A = 2 I`. -/
theorem closedFormOperator_id_two_smul_innerSL
    (hj : Function.Injective (ContinuousLinearMap.id ℂ ℂ))
    (hd : DenseRange (ContinuousLinearMap.id ℂ ℂ)) :
    closedFormOperator (ContinuousLinearMap.id ℂ ℂ) hj hd ((2 : ℂ) • innerSL ℂ) =
      ((2 : ℂ) • LinearMap.id).toPMap ⊤ := by
  have := closedFormOperator_smul_id_smul_innerSL (𝕜 := ℂ) (H := ℂ) (a := 1) one_ne_zero 2
    (by simpa using hj) (by simpa using hd)
  norm_num at this ⊢
  exact this

/-- At `u = 1` and `v = i`, both sides of `q(u, v) = ⟪2 u, v⟫` are `2 i`. -/
theorem two_innerSL_one_I :
    ((2 : ℂ) • innerSL ℂ) (1 : ℂ) Complex.I = 2 * Complex.I ∧
      ⟪(2 : ℂ) • (1 : ℂ), Complex.I⟫_ℂ = 2 * Complex.I := by
  refine ⟨by simp, ?_⟩
  simp [RCLike.inner_apply, mul_comm, Complex.conj_ofNat]

/-- With `j = id`, the form `q(u, v) = 2 ⟪u, v⟫` is coercive with shift `α = 0` and `c = 2`. -/
theorem two_mul_norm_sq_le_re_shiftedForm_id_two_smul_innerSL_self (u : H) :
    2 * ‖u‖ ^ 2 ≤
      RCLike.re (shiftedForm (ContinuousLinearMap.id 𝕜 H) ((2 : 𝕜) • innerSL 𝕜) 0 u u) :=
  mul_norm_sq_le_re_shiftedForm_self (ω := 0) _ le_rfl (fun u => by simp) u

/-- With `j = id`, the zero form represents the zero operator. -/
theorem closedFormOperator_id_zero (hj : Function.Injective (ContinuousLinearMap.id 𝕜 H))
    (hd : DenseRange (ContinuousLinearMap.id 𝕜 H)) :
    closedFormOperator (ContinuousLinearMap.id 𝕜 H) hj hd 0 = (0 : H →ₗ[𝕜] H).toPMap ⊤ := by
  have := closedFormOperator_smul_id_smul_innerSL (𝕜 := 𝕜) (H := H) (a := 1) one_ne_zero 0
    (by simpa using hj) (by simpa using hd)
  simp only [RCLike.ofReal_one, one_smul, RCLike.ofReal_zero, zero_smul, zero_div] at this
  convert this using 2
  ext u v
  simp

/-- With `j = id` and `q = 0`, the shifts `α = 1` and `α = 2` both satisfy the coercivity bound
with `c = 1`. -/
theorem one_mul_norm_sq_le_re_shiftedForm_id_zero_self (u : H) :
    1 * ‖u‖ ^ 2 ≤ RCLike.re (shiftedForm (ContinuousLinearMap.id 𝕜 H) 0 1 u u) ∧
      1 * ‖u‖ ^ 2 ≤ RCLike.re (shiftedForm (ContinuousLinearMap.id 𝕜 H) 0 2 u u) := by
  refine ⟨mul_norm_sq_le_re_shiftedForm_self (ω := 1) _ le_rfl (fun u => ?_) u,
    mul_norm_sq_le_re_shiftedForm_self (ω := 1) _ one_le_two (fun u => ?_) u⟩ <;> simp

/-- On `ℂ` with `j = 2 id`, the form `q(u, v) = conj(u) v` represents `A = (1 / 4) I`. -/
theorem closedFormOperator_two_smul_id_innerSL
    (hj : Function.Injective ((2 : ℂ) • ContinuousLinearMap.id ℂ ℂ))
    (hd : DenseRange ((2 : ℂ) • ContinuousLinearMap.id ℂ ℂ)) :
    closedFormOperator ((2 : ℂ) • ContinuousLinearMap.id ℂ ℂ) hj hd (innerSL ℂ) =
      ((1 / 4 : ℂ) • LinearMap.id).toPMap ⊤ := by
  have := closedFormOperator_smul_id_smul_innerSL (𝕜 := ℂ) (H := ℂ) (a := 2) two_ne_zero 1
    (by simpa using hj) (by simpa using hd)
  norm_num at this ⊢
  exact this

/-- With `A = (1 / 4) I` and `j = 2 id`, `⟪A (2 u), 2 v⟫ = conj(u) v`; with `A = I` the pairing
would be `4 conj(u) v`. -/
theorem inner_quarter_two_two (u v : ℂ) :
    ⟪(1 / 4 : ℂ) • ((2 : ℂ) • u), (2 : ℂ) • v⟫_ℂ = conj u * v ∧
      ⟪(2 : ℂ) • u, (2 : ℂ) • v⟫_ℂ = 4 * (conj u * v) := by
  simp only [smul_eq_mul, RCLike.inner_apply, map_mul, map_div₀, map_one, map_ofNat]
  constructor <;> ring

end TauCeti.Examples.ClosedForm
