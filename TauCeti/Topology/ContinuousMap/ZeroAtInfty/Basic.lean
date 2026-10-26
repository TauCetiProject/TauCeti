/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Scalar actions and pointwise norms on `C₀(α, β)`

Mathlib equips the space `C₀(α, β)` of continuous functions vanishing at infinity with the sup
distance and, for normed fields, with a normed-space structure. This file supplies the structure
needed for scalar actions beyond normed fields:

* `ZeroAtInftyContinuousMap.instIsBoundedSMul`: a bounded scalar action on `β` induces one on
  `C₀(α, β)`, so for instance `C₀(α, R)` is a module with contractive action over a seminormed
  ring `R`;
* `ZeroAtInftyContinuousMap.instContinuousConstSMul`: a continuous distributive scalar action
  on an additive uniform group `β` induces continuous fixed-scalar multiplication on `C₀(α, β)`;
* `ZeroAtInftyContinuousMap.norm_le` and `ZeroAtInftyContinuousMap.norm_eq_iSup_norm`: the norm
  on `C₀(α, β)` is the supremum of the pointwise norms;
* `ZeroAtInftyContinuousMap.evalCLM`: evaluation at a point as a continuous linear map over an
  arbitrary semiring of scalars;
* `ZeroAtInftyContinuousMap.compLeft`: a continuous linear map `u : E →L[R] F` with a uniform
  bound `‖u x‖ ≤ C * ‖x‖` acts pointwise as a continuous linear map `C₀(α, E) →L[R] C₀(α, F)`;
* `ZeroAtInftyContinuousMap.congrLeft`: a homeomorphism `α ≃ₜ β` induces a linear isometry
  equivalence `C₀(α, E) ≃ₗᵢ[R] C₀(β, E)`.

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

/-- A continuous distributive scalar action on an additive uniform group induces continuous
fixed-scalar multiplication on functions vanishing at infinity, with their sup metric. -/
-- Prefer the existing continuity instances obtained from bounded scalar actions.
instance (priority := 90) instContinuousConstSMul
    [PseudoMetricSpace β] [AddGroup β] [IsUniformAddGroup β]
    {R : Type*} [DistribSMul R β] [ContinuousConstSMul R β] : ContinuousConstSMul R C₀(α, β) where
  continuous_const_smul r := by
    let := uniformContinuousConstSMul_of_continuousConstSMul R β
    exact continuous_iff_continuousAt.2 fun f ↦ tendsto_iff_tendstoUniformly.2 <|
      (uniformContinuous_const_smul r).comp_tendstoUniformly <|
        tendsto_iff_tendstoUniformly.1 Filter.tendsto_id

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

section Comparison

variable {β R E F : Type*} [TopologicalSpace β] [SeminormedAddCommGroup E]

/-- Precomposition with a homeomorphism preserves the norm of a function vanishing at infinity. -/
@[simp]
theorem norm_comp_toCocompactMap (f : C₀(β, E)) (e : α ≃ₜ β) :
    ‖f.comp e.toCocompactMap‖ = ‖f‖ :=
  le_antisymm ((norm_le (norm_nonneg f)).2 fun _ ↦ norm_coe_le_norm f _)
    ((norm_le (norm_nonneg _)).2 fun y ↦ by
      simpa using norm_coe_le_norm (f.comp e.toCocompactMap) (e.symm y))

variable [Semiring R] [Module R E] [ContinuousConstSMul R E]
  [SeminormedAddCommGroup F] [Module R F] [ContinuousConstSMul R F]

/-- **Pointwise action of a bounded coefficient map.** A continuous linear map
`u : E →L[R] F` with a uniform bound `‖u x‖ ≤ C * ‖x‖` acts on `C₀(α, E)` by postcomposition,
giving a continuous linear map `C₀(α, E) →L[R] C₀(α, F)`. -/
def compLeft (u : E →L[R] F) (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖) : C₀(α, E) →L[R] C₀(α, F) :=
  let L : C₀(α, E) →ₗ[R] C₀(α, F) :=
    { toFun f :=
        { toFun := u ∘ f
          continuous_toFun := u.continuous.comp (map_continuous f)
          zero_at_infty' := (u.continuous.tendsto' 0 0 (map_zero u)).comp (zero_at_infty f) }
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  { L with
    cont := by
      obtain ⟨C, hC⟩ := hu
      refine AddMonoidHomClass.continuous_of_bound L (max C 0) fun f ↦
        (norm_le (by positivity)).2 fun x ↦ (hC (f x)).trans ?_
      exact mul_le_mul (le_max_left C 0) (norm_coe_le_norm f x) (norm_nonneg _)
        (le_max_right C 0) }

/-- `compLeft u hu` applies `u` pointwise. -/
@[simp]
theorem compLeft_apply (u : E →L[R] F) (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖) (f : C₀(α, E)) (x : α) :
    compLeft u hu f x = u (f x) := (rfl)

/-- The coordinatewise action of a composite is the composite of the coordinatewise actions. -/
theorem compLeft_comp {G : Type*} [SeminormedAddCommGroup G] [Module R G] [ContinuousConstSMul R G]
    (v : F →L[R] G) (u : E →L[R] F) (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖)
    (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖) (hvu : ∃ C, ∀ x, ‖v.comp u x‖ ≤ C * ‖x‖) :
    compLeft (α := α) (v.comp u) hvu = (compLeft v hv).comp (compLeft u hu) := (rfl)

/-- A uniform bound `C ≥ 0` for `u` is also a uniform bound for its coordinatewise action. -/
theorem norm_compLeft_apply_le (u : E →L[R] F) {C : ℝ} (hC₀ : 0 ≤ C)
    (hC : ∀ x, ‖u x‖ ≤ C * ‖x‖) (f : C₀(α, E)) : ‖compLeft u ⟨C, hC⟩ f‖ ≤ C * ‖f‖ :=
  (norm_le (by positivity)).2 fun x ↦
    (hC (f x)).trans (mul_le_mul_of_nonneg_left (norm_coe_le_norm f x) hC₀)

/-- The coordinatewise action of a bounded coefficient map is itself uniformly bounded. -/
theorem exists_norm_compLeft_apply_le (u : E →L[R] F) (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖) :
    ∃ C, ∀ f : C₀(α, E), ‖compLeft u hu f‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ := hu
  refine ⟨max C 0, norm_compLeft_apply_le u (le_max_right C 0) fun x ↦ ?_⟩
  exact (hC x).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg x))

variable (R E) in
/-- **Reindexing along a homeomorphism.** A homeomorphism `e : α ≃ₜ β` identifies `C₀(α, E)` with
`C₀(β, E)` isometrically, by `f ↦ f ∘ e.symm`. For discrete index types, any equivalence `e` gives
such a homeomorphism `e.toHomeomorphOfDiscrete`. -/
def congrLeft (e : α ≃ₜ β) : C₀(α, E) ≃ₗᵢ[R] C₀(β, E) where
  toFun f := f.comp e.symm.toCocompactMap
  invFun f := f.comp e.toCocompactMap
  left_inv f := by ext; simp
  right_inv f := by ext; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := norm_comp_toCocompactMap f e.symm

/-- `congrLeft R E e f` is `f ∘ e.symm`. -/
@[simp]
theorem congrLeft_apply (e : α ≃ₜ β) (f : C₀(α, E)) (y : β) :
    congrLeft R E e f y = f (e.symm y) := (rfl)

/-- The inverse of reindexing along `e` is reindexing along `e.symm`. -/
@[simp]
theorem congrLeft_symm (e : α ≃ₜ β) : (congrLeft R E e).symm = congrLeft R E e.symm := (rfl)

/-- Reindexing along the identity is the identity. -/
@[simp]
theorem congrLeft_refl : congrLeft R E (Homeomorph.refl α) = LinearIsometryEquiv.refl R _ := (rfl)

/-- Reindexing along a composite is the composite of the reindexings. -/
theorem congrLeft_trans {γ : Type*} [TopologicalSpace γ] (e : α ≃ₜ β) (e' : β ≃ₜ γ) :
    congrLeft R E (e.trans e') = (congrLeft R E e).trans (congrLeft R E e') := (rfl)

/-- Reindexing commutes with the coordinatewise action of a bounded coefficient map. -/
theorem congrLeft_compLeft (e : α ≃ₜ β) (u : E →L[R] F) (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖)
    (f : C₀(α, E)) : congrLeft R F e (compLeft u hu f) = compLeft u hu (congrLeft R E e f) := (rfl)

end Comparison

end ZeroAtInftyContinuousMap
