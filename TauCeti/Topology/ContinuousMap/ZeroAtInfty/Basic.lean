/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Bounded scalar actions and pointwise norms on `C₀(α, β)`

Mathlib equips the space `C₀(α, β)` of continuous functions vanishing at infinity with the sup
distance and, for normed fields, with a normed-space structure. This file supplies the structure
needed when the scalars form a normed ring rather than a field:

* `ZeroAtInftyContinuousMap.instIsBoundedSMul`: a bounded scalar action on `β` induces one on
  `C₀(α, β)`, so for instance `C₀(α, R)` is a module with contractive action over a seminormed
  ring `R`;
* `ZeroAtInftyContinuousMap.norm_le` and `ZeroAtInftyContinuousMap.norm_eq_iSup_norm`: the norm
  on `C₀(α, β)` is the supremum of the pointwise norms;
* `ZeroAtInftyContinuousMap.evalCLM`: evaluation at a point as a continuous linear map over an
  arbitrary semiring of scalars.

With `α` discrete these are the basic structures of the model space `C₀(I, R)` of
nonarchimedean functional analysis over normed rings; its coordinate structure is developed in
`TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete`.
-/

public section

open scoped ZeroAtInfty BoundedContinuousFunction

namespace ZeroAtInftyContinuousMap

variable {α β : Type*} [TopologicalSpace α]

section PseudoMetric

variable [PseudoMetricSpace β] [Zero β]

/-- A bounded scalar action on `β` induces a bounded scalar action on `C₀(α, β)`. In particular
`C₀(α, R)` has a contractive scalar action of a seminormed ring `R`. -/
instance instIsBoundedSMul {𝕜 : Type*} [PseudoMetricSpace 𝕜] [Zero 𝕜] [SMulZeroClass 𝕜 β]
    [IsBoundedSMul 𝕜 β] : IsBoundedSMul 𝕜 C₀(α, β) where
  dist_smul_pair' c f g := dist_smul_pair c f.toBCF g.toBCF
  dist_pair_smul' c₁ c₂ f := dist_pair_smul c₁ c₂ f.toBCF

end PseudoMetric

/-- The coercion to functions commutes with finite sums. -/
@[simp, norm_cast]
theorem coe_sum [TopologicalSpace β] [AddCommMonoid β] [ContinuousAdd β] {ι : Type*}
    (s : Finset ι) (f : ι → C₀(α, β)) : ⇑(∑ i ∈ s, f i) = ∑ i ∈ s, ⇑(f i) :=
  map_sum (⟨⟨DFunLike.coe, coe_zero⟩, coe_add⟩ : C₀(α, β) →+ α → β) f s

section Normed

variable [SeminormedAddCommGroup β]

/-- The norm of a function vanishing at infinity bounds the norm of each of its values. -/
theorem norm_coe_le_norm (f : C₀(α, β)) (x : α) : ‖f x‖ ≤ ‖f‖ :=
  f.toBCF.norm_coe_le_norm x

/-- The norm of a function vanishing at infinity is bounded by `C ≥ 0` exactly when each of its
values is. -/
theorem norm_le {f : C₀(α, β)} {C : ℝ} (hC : 0 ≤ C) : ‖f‖ ≤ C ↔ ∀ x, ‖f x‖ ≤ C :=
  f.toBCF.norm_le hC

/-- The norm of a function vanishing at infinity is the supremum of the norms of its values. -/
theorem norm_eq_iSup_norm (f : C₀(α, β)) : ‖f‖ = ⨆ x, ‖f x‖ :=
  f.toBCF.norm_eq_iSup_norm

variable (𝕜 : Type*) [Semiring 𝕜] [Module 𝕜 β] [ContinuousConstSMul 𝕜 β]

/-- Evaluation at a point, as a continuous linear map `C₀(α, β) →L[𝕜] β`. -/
def evalCLM (x : α) : C₀(α, β) →L[𝕜] β where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuous_eval_const (F := α →ᵇ β) x).comp isometry_toBCF.continuous

/-- `evalCLM 𝕜 x` evaluates at `x`. -/
@[simp]
theorem evalCLM_apply (x : α) (f : C₀(α, β)) : evalCLM 𝕜 x f = f x := (rfl)

end Normed

end ZeroAtInftyContinuousMap
