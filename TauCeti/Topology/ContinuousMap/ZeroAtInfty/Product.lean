/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# Elementary tensors on `C₀(α × β, E)`

For arbitrary topological spaces `α` and `β`, a seminormed ring `R`, and a seminormed `R`-module
`E` with a bounded scalar action, `a ∈ C₀(α, R)` and `b ∈ C₀(β, E)` form the elementary tensor
`ZeroAtInftyContinuousMap.prodSMul a b ∈ C₀(α × β, E)` sending `(x, y)` to `a x • b y`. Because the
cocompact filter on `α × β` is the coproduct of the cocompact filters on `α` and `β`, boundedness
of one factor against vanishing at infinity of the other ensures that `prodSMul a b` vanishes at
infinity without any locally compact or discrete hypothesis on `α` or `β`.

This provides two-variable test functions on product spaces directly inside `C₀` without auxiliary
topological tensor products, and feeds the discrete currying and two-variable functional API in
`TauCeti.Topology.ContinuousMap.ZeroAtInfty.Bilinear`:

* `ZeroAtInftyContinuousMap.prodSMul`: the elementary tensor `(x, y) ↦ a x • b y` in
  `C₀(α × β, E)`, together with its additivity and scalar-multiplication laws in each variable;
* `ZeroAtInftyContinuousMap.norm_prodSMul_le` and `ZeroAtInftyContinuousMap.norm_prodSMul`: the
  sup-norm inequality `‖prodSMul a b‖ ≤ ‖a‖ * ‖b‖`, upgraded to equality when scalar multiplication
  preserves norms (`NormSMulClass R E`);
* `ZeroAtInftyContinuousMap.congrLeft_prodAssoc_prodSMul` and
  `ZeroAtInftyContinuousMap.congrLeft_prodComm_prodSMul`: associativity of iterated elementary
  tensors under `Homeomorph.prodAssoc` and symmetry under `Homeomorph.prodComm` over a commutative
  seminormed ring.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

section BoundedSMul

variable {R E : Type*} [SeminormedRing R] [SeminormedAddCommGroup E] [Module R E]
  [IsBoundedSMul R E]

private theorem tendsto_cocompact_prodSMul (a : C₀(α, R)) (b : C₀(β, E)) :
    Tendsto (fun p : α × β ↦ a p.1 • b p.2) (cocompact (α × β)) (𝓝 0) := by
  rw [← Filter.coprod_cocompact, Filter.coprod, tendsto_sup]
  exact ⟨squeeze_zero_norm (fun p ↦ (norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_coe_le_norm b p.2) (norm_nonneg _)))
      (by simpa using ((zero_at_infty a).norm.comp tendsto_comap).mul_const ‖b‖),
    squeeze_zero_norm (fun p ↦ (norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_coe_le_norm a p.1) (norm_nonneg _)))
      (by simpa using ((zero_at_infty b).norm.comp tendsto_comap).const_mul ‖a‖)⟩

/-- **Elementary tensor on a product space.** Given `a ∈ C₀(α, R)` and `b ∈ C₀(β, E)`, the
two-variable map `(x, y) ↦ a x • b y` is continuous and vanishes at infinity on `α × β`. -/
def prodSMul (a : C₀(α, R)) (b : C₀(β, E)) : C₀(α × β, E) where
  toFun p := a p.1 • b p.2
  continuous_toFun := (a.continuous.comp continuous_fst).smul (b.continuous.comp continuous_snd)
  zero_at_infty' := tendsto_cocompact_prodSMul a b

/-- `prodSMul a b` evaluates at `(x, y)` to `a x • b y`. -/
@[simp]
theorem prodSMul_apply (a : C₀(α, R)) (b : C₀(β, E)) (p : α × β) :
    prodSMul a b p = a p.1 • b p.2 := (rfl)

/-- The sup norm of `prodSMul a b` is at most `‖a‖ * ‖b‖`. -/
theorem norm_prodSMul_le (a : C₀(α, R)) (b : C₀(β, E)) :
    ‖prodSMul a b‖ ≤ ‖a‖ * ‖b‖ :=
  (norm_le (by positivity)).2 fun p ↦ (norm_smul_le (a p.1) (b p.2)).trans
    (mul_le_mul (norm_coe_le_norm a p.1) (norm_coe_le_norm b p.2)
      (norm_nonneg _) (norm_nonneg _))

/-- An elementary tensor with `0` on the left is `0`. -/
@[simp]
theorem prodSMul_zero_left (b : C₀(β, E)) : prodSMul (0 : C₀(α, R)) b = 0 := by
  ext; simp

/-- An elementary tensor with `0` on the right is `0`. -/
@[simp]
theorem prodSMul_zero_right (a : C₀(α, R)) : prodSMul a (0 : C₀(β, E)) = 0 := by
  ext; simp

/-- `prodSMul` is additive in its first argument. -/
theorem prodSMul_add_left (a₁ a₂ : C₀(α, R)) (b : C₀(β, E)) :
    prodSMul (a₁ + a₂) b = prodSMul a₁ b + prodSMul a₂ b := by
  ext; simp [add_smul]

/-- `prodSMul` is additive in its second argument. -/
theorem prodSMul_add_right (a : C₀(α, R)) (b₁ b₂ : C₀(β, E)) :
    prodSMul a (b₁ + b₂) = prodSMul a b₁ + prodSMul a b₂ := by
  ext; simp

/-- `prodSMul` associates with compatible scalar multiplication in its first argument. -/
theorem prodSMul_smul_left {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S E] [ContinuousConstSMul S E] [IsScalarTower S R E]
    (s : S) (a : C₀(α, R)) (b : C₀(β, E)) :
    prodSMul (s • a) b = s • prodSMul a b := by
  ext; simp [smul_assoc]

/-- `prodSMul` commutes with compatible scalar multiplication in its second argument. -/
theorem prodSMul_smul_right {S : Type*} [SMulZeroClass S E] [ContinuousConstSMul S E]
    [SMulCommClass R S E] (s : S) (a : C₀(α, R)) (b : C₀(β, E)) :
    prodSMul a (s • b) = s • prodSMul a b := by
  ext; simp [smul_comm]

/-- Reassociating `(α × β) × γ` to `α × (β × γ)` reassociates iterated elementary tensors. -/
theorem congrLeft_prodAssoc_prodSMul {S : Type*} [Semiring S] [Module S E] [ContinuousConstSMul S E]
    (a : C₀(α, R)) (b : C₀(β, R)) (c : C₀(γ, E)) :
    congrLeft S E (Homeomorph.prodAssoc α β γ) (prodSMul (prodSMul a b) c) =
      prodSMul a (prodSMul b c) := by
  ext ⟨x, y, z⟩; simp [Homeomorph.prodAssoc, mul_smul]

end BoundedSMul

/-- When scalar multiplication preserves norms, `‖prodSMul a b‖ = ‖a‖ * ‖b‖`. -/
@[simp]
theorem norm_prodSMul {R E : Type*} [SeminormedRing R] [SeminormedAddCommGroup E] [Module R E]
    [NormSMulClass R E] (a : C₀(α, R)) (b : C₀(β, E)) :
    ‖prodSMul a b‖ = ‖a‖ * ‖b‖ := by
  refine le_antisymm (norm_prodSMul_le a b) ?_
  rcases (norm_nonneg b).eq_or_lt with hb | hb
  · rw [← hb, mul_zero]
    exact norm_nonneg _
  · rw [← le_div_iff₀ hb]
    refine (norm_le (by positivity)).2 fun x ↦ ?_
    rw [le_div_iff₀ hb]
    rcases (norm_nonneg (a x)).eq_or_lt with hax | hax
    · rw [← hax, zero_mul]
      exact norm_nonneg _
    · rw [← le_div_iff₀' hax]
      refine (norm_le (by positivity)).2 fun y ↦ ?_
      rw [le_div_iff₀' hax, ← norm_smul]
      exact norm_coe_le_norm (prodSMul a b) (x, y)

/-- Over a commutative seminormed ring, swapping `α × β` swaps elementary tensor factors. -/
@[simp]
theorem congrLeft_prodComm_prodSMul {R : Type*} [SeminormedCommRing R]
    (a : C₀(α, R)) (b : C₀(β, R)) :
    congrLeft R R (Homeomorph.prodComm α β) (prodSMul a b) = prodSMul b a := by
  ext ⟨y, x⟩; simp [mul_comm]

end ZeroAtInftyContinuousMap
