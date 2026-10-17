/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Scalar actions, norms and evaluation on continuous functions vanishing at infinity

Mathlib equips `C₀(α, β)` with the sup norm and with a normed-space structure over a normed
field. This file supplies the corresponding structure over an arbitrary metric scalar type: if
the action of `𝕜` on `β` is bounded (`IsBoundedSMul 𝕜 β`), then so is the pointwise action of
`𝕜` on `C₀(α, β)`. In particular, for a seminormed ring `R` and a module `E` with contractive
action `‖r • x‖ ≤ ‖r‖ * ‖x‖`, the action of `R` on `C₀(α, E)` is again contractive. This is the
setting of Banach modules over Banach rings, where the scalars need not form a field.

We also record finite sums, the pointwise description of the sup norm of `C₀(α, β)`,
transported from bounded continuous functions, and evaluation at a point as a continuous linear
map of norm at most one over any ring of scalars.
-/

public section

open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

variable {α β : Type*} [TopologicalSpace α]

/-- The function underlying a finite sum of continuous functions vanishing at infinity is the
finite sum of the underlying functions. -/
@[simp, norm_cast]
theorem coe_sum [TopologicalSpace β] [AddCommMonoid β] [ContinuousAdd β] {ι : Type*}
    (s : Finset ι) (f : ι → C₀(α, β)) : ⇑(∑ i ∈ s, f i) = ∑ i ∈ s, ⇑(f i) :=
  map_sum (⟨⟨DFunLike.coe, coe_zero⟩, coe_add⟩ : C₀(α, β) →+ α → β) f s

section IsBoundedSMul

/-- The bounded continuous function underlying the zero function is zero. -/
@[simp]
theorem toBCF_zero [PseudoMetricSpace β] [Zero β] : (0 : C₀(α, β)).toBCF = 0 := (rfl)

variable {𝕜 : Type*} [PseudoMetricSpace 𝕜] [Zero 𝕜] [PseudoMetricSpace β] [Zero β]
  [SMulZeroClass 𝕜 β] [IsBoundedSMul 𝕜 β]

/-- The bounded continuous function underlying a scalar multiple is the scalar multiple of the
underlying bounded continuous function. -/
@[simp]
theorem toBCF_smul (c : 𝕜) (f : C₀(α, β)) : (c • f).toBCF = c • f.toBCF := (rfl)

/-- A bounded scalar action on the values gives a bounded pointwise scalar action on continuous
functions vanishing at infinity. -/
instance instIsBoundedSMul : IsBoundedSMul 𝕜 C₀(α, β) where
  dist_smul_pair' c f g := by
    simpa only [← dist_toBCF_eq_dist, toBCF_smul] using dist_smul_pair c f.toBCF g.toBCF
  dist_pair_smul' c₁ c₂ f := by
    simpa only [← dist_toBCF_eq_dist, toBCF_smul, toBCF_zero] using dist_pair_smul c₁ c₂ f.toBCF

end IsBoundedSMul

section Norm

variable [SeminormedAddCommGroup β]

/-- Each value of a continuous function vanishing at infinity has norm at most its sup norm. -/
theorem norm_apply_le (f : C₀(α, β)) (x : α) : ‖f x‖ ≤ ‖f‖ :=
  f.toBCF.norm_coe_le_norm x

/-- The sup norm of a continuous function vanishing at infinity is at most a nonnegative constant
exactly when every value has norm at most that constant. -/
theorem norm_le {f : C₀(α, β)} {C : ℝ} (hC : 0 ≤ C) : ‖f‖ ≤ C ↔ ∀ x, ‖f x‖ ≤ C := by
  simpa only [← norm_toBCF_eq_norm, toBCF_apply] using
    BoundedContinuousFunction.norm_le (f := f.toBCF) hC

/-- The sup norm of a continuous function vanishing at infinity is the supremum of the norms of
its values. -/
theorem norm_eq_iSup_norm (f : C₀(α, β)) : ‖f‖ = ⨆ x, ‖f x‖ :=
  f.toBCF.norm_eq_iSup_norm

end Norm

section Eval

variable [SeminormedAddCommGroup β] (R : Type*) [Ring R] [Module R β] [ContinuousConstSMul R β]

/-- Evaluation at a point, as a continuous linear map `C₀(α, β) →L[R] β` over any ring of
scalars. Its norm bound is `ZeroAtInftyContinuousMap.norm_apply_le`. -/
noncomputable def evalCLM (x : α) : C₀(α, β) →L[R] β :=
  LinearMap.mkContinuous
    { toFun f := f x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    1 fun f ↦ by simpa using f.norm_apply_le x

/-- Evaluation at a point sends a function to its value there. -/
@[simp]
theorem evalCLM_apply (x : α) (f : C₀(α, β)) : evalCLM R x f = f x := (rfl)

end Eval

end ZeroAtInftyContinuousMap
