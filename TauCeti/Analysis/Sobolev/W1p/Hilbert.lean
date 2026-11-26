/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic

/-!
# The inner product of `W^{1,2}(Ω)`

At exponent two the first-order Sobolev space `W^{1,2}(Ω) = H¹(Ω)` is a closed subspace of the
`L²` space of value-gradient jets, so it is a real inner product space, and so is every closed
subspace of it, such as `H¹₀(Ω)`. Its inner product is the sum of the `L²` inner products of the
values and of the weak gradients,

`⟪u, v⟫_{H¹(Ω)} = ⟪u, v⟫_{L²(Ω)} + ⟪∇u, ∇v⟫_{L²(Ω; E)}`

(`TauCeti.W1p.inner_eq_inner_value_add_inner_gradient`): it is the polarization of the norm
identity `‖u‖² = ‖u‖²_{L²} + ‖∇u‖²_{L²}`
(`TauCeti.W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq`). This is what computing in
orthonormal bases of `H¹(Ω)` or `H¹₀(Ω)` needs, for instance in expansions in eigenfunctions.
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [OpensMeasurableSpace E] {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E}

/-- **The inner product of `H¹(Ω)`** is the sum of the `L²` inner products of the values and of the
weak gradients: `⟪u, v⟫ = ⟪u, v⟫_{L²(Ω)} + ⟪∇u, ∇v⟫_{L²(Ω; E)}`. -/
theorem W1p.inner_eq_inner_value_add_inner_gradient (u v : W1p mu Omega 2) :
    ⟪u, v⟫_ℝ = ⟪W1p.value u, W1p.value v⟫_ℝ + ⟪W1p.gradient u, W1p.gradient v⟫_ℝ := by
  have h (w : W1p mu Omega 2) := W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq w
  simp only [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    ← sq, h, W1p.value_add, W1p.gradient_add]
  ring

end TauCeti
