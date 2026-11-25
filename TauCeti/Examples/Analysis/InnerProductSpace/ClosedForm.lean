/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ClosedForm.Basic

/-!
# Represented operators of scalar forms

On an inner product space `H` over `𝕜`, take the inclusion `j = a • id` for a real `a ≠ 0` and the
form `q(u, v) = b ⟪u, v⟫` for a real `b`. The operator represented by `q` along `j`,
`ContinuousLinearMap.closedFormOperator`, is the everywhere defined multiple `(b / a ^ 2) • id`:
for `x = a u` the representative `h` must satisfy `b ⟪u, v⟫ = ⟪h, a v⟫` for all `v`, so
`h = (b / a) u = (b / a ^ 2) x`.

The three cases below are the first Checks of UO-D06 (§4.7) of the
OperatorTheory/UnboundedOperators roadmap:

* `V = H = ℂ`, `j = id`, `q(u, v) = 2 conj(u) v` represents `A = 2 I`, and at `u = 1`, `v = i`
  both sides of `q(u, v) = ⟪A u, v⟫` are `2 i`;
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

/-- `x ↦ a • x` is injective for `a ≠ 0`. -/
theorem injective_smul_id {a : ℝ} (ha : a ≠ 0) :
    Function.Injective ((a : 𝕜) • ContinuousLinearMap.id 𝕜 H) := fun x y hxy => by
  simpa [smul_right_inj (RCLike.ofReal_ne_zero.2 ha)] using hxy

/-- `x ↦ a • x` has dense range for `a ≠ 0`. -/
theorem denseRange_smul_id {a : ℝ} (ha : a ≠ 0) :
    DenseRange ((a : 𝕜) • ContinuousLinearMap.id 𝕜 H) :=
  Function.Surjective.denseRange fun x =>
    ⟨(a : 𝕜)⁻¹ • x, by simp [smul_smul, RCLike.ofReal_ne_zero.2 ha]⟩

/-- **The represented operator of a scalar form.** Along `j = a • id` with real `a ≠ 0`, the form
`q(u, v) = b ⟪u, v⟫` with real `b` represents the everywhere defined operator
`(b / a ^ 2) • id`. -/
theorem closedFormOperator_smul_id_smul_innerSL {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    closedFormOperator ((a : 𝕜) • ContinuousLinearMap.id 𝕜 H) (injective_smul_id ha)
        (denseRange_smul_id ha) ((b : 𝕜) • innerSL 𝕜) =
      (((b / a ^ 2 : ℝ) : 𝕜) • LinearMap.id).toPMap ⊤ := by
  have ha' : (a : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 ha
  symm
  refine eq_closedFormOperator_of_mem_graph_iff _ _ _ _ fun x h => ?_
  simp only [LinearPMap.mem_graph_iff, LinearMap.toPMap_domain, LinearMap.toPMap_apply,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq, Subtype.exists, Submodule.mem_top,
    exists_true_left, exists_eq_left, coe_id', smul_apply, innerSL_apply_apply]
  constructor
  · rintro rfl
    refine ⟨(a : 𝕜)⁻¹ • x, by simp [smul_smul, ha'], fun v => ?_⟩
    simp only [inner_smul_left, inner_smul_right, map_inv₀, RCLike.conj_ofReal, smul_eq_mul]
    push_cast
    field_simp
  · rintro ⟨u, rfl, hu⟩
    refine ext_inner_right 𝕜 fun v => ?_
    have := hu v
    simp only [inner_smul_left, inner_smul_right, RCLike.conj_ofReal, smul_eq_mul] at this ⊢
    push_cast
    field_simp
    linear_combination this

/-- **First Check.** On `ℂ` with `j = id`, the form `q(u, v) = 2 conj(u) v` represents `A = 2 I`. -/
theorem closedFormOperator_two_innerSL (hj : Function.Injective (ContinuousLinearMap.id ℂ ℂ))
    (hd : DenseRange (ContinuousLinearMap.id ℂ ℂ)) :
    closedFormOperator (ContinuousLinearMap.id ℂ ℂ) hj hd ((2 : ℂ) • innerSL ℂ) =
      ((2 : ℂ) • LinearMap.id).toPMap ⊤ := by
  have := closedFormOperator_smul_id_smul_innerSL (𝕜 := ℂ) (H := ℂ) (a := 1) one_ne_zero 2
  norm_num at this
  exact this

/-- At `u = 1` and `v = i`, both sides of `q(u, v) = ⟪2 u, v⟫` are `2 i`. -/
theorem two_innerSL_one_I :
    ((2 : ℂ) • innerSL ℂ) (1 : ℂ) Complex.I = 2 * Complex.I ∧
      ⟪(2 : ℂ) • (1 : ℂ), Complex.I⟫_ℂ = 2 * Complex.I := by
  refine ⟨by simp, ?_⟩
  simp [RCLike.inner_apply, mul_comm, Complex.conj_ofNat]

/-- **Second Check.** With `j = id`, the zero form represents the zero operator. -/
theorem closedFormOperator_zero (hj : Function.Injective (ContinuousLinearMap.id 𝕜 H))
    (hd : DenseRange (ContinuousLinearMap.id 𝕜 H)) :
    closedFormOperator (ContinuousLinearMap.id 𝕜 H) hj hd 0 = (0 : H →ₗ[𝕜] H).toPMap ⊤ := by
  have := closedFormOperator_smul_id_smul_innerSL (𝕜 := 𝕜) (H := H) (a := 1) one_ne_zero 0
  simp only [RCLike.ofReal_one, one_smul, RCLike.ofReal_zero, zero_smul, zero_div] at this
  convert this using 2
  ext u v
  simp

/-- With `j = id` and `q = 0`, the shifts `α = 1` and `α = 2` both satisfy the coercivity bound
with `c = 1`. -/
theorem one_mul_norm_sq_le_re_shiftedForm_zero (u : H) :
    1 * ‖u‖ ^ 2 ≤ RCLike.re (shiftedForm (ContinuousLinearMap.id 𝕜 H) 0 1 u u) ∧
      1 * ‖u‖ ^ 2 ≤ RCLike.re (shiftedForm (ContinuousLinearMap.id 𝕜 H) 0 2 u u) := by
  refine ⟨mul_norm_sq_le_re_shiftedForm_self (ω := 1) _ le_rfl (fun u => ?_) u,
    mul_norm_sq_le_re_shiftedForm_self (ω := 1) _ one_le_two (fun u => ?_) u⟩ <;> simp

/-- **Third Check.** On `ℂ` with `j = 2 id`, the form `q(u, v) = conj(u) v` represents
`A = (1 / 4) I`. -/
theorem closedFormOperator_two_smul_innerSL
    (hj : Function.Injective ((2 : ℂ) • ContinuousLinearMap.id ℂ ℂ))
    (hd : DenseRange ((2 : ℂ) • ContinuousLinearMap.id ℂ ℂ)) :
    closedFormOperator ((2 : ℂ) • ContinuousLinearMap.id ℂ ℂ) hj hd (innerSL ℂ) =
      ((1 / 4 : ℂ) • LinearMap.id).toPMap ⊤ := by
  have := closedFormOperator_smul_id_smul_innerSL (𝕜 := ℂ) (H := ℂ) (a := 2) two_ne_zero 1
  norm_num at this
  exact this

/-- With `A = (1 / 4) I` and `j = 2 id`, `⟪A (2 u), 2 v⟫ = conj(u) v`; with `A = I` the pairing
would be `4 conj(u) v`. -/
theorem inner_quarter_two_two (u v : ℂ) :
    ⟪(1 / 4 : ℂ) • ((2 : ℂ) • u), (2 : ℂ) • v⟫_ℂ = conj u * v ∧
      ⟪(2 : ℂ) • u, (2 : ℂ) • v⟫_ℂ = 4 * (conj u * v) := by
  simp only [smul_eq_mul, RCLike.inner_apply, map_mul, map_div₀, map_one, map_ofNat]
  constructor <;> ring

end TauCeti.Examples.ClosedForm
