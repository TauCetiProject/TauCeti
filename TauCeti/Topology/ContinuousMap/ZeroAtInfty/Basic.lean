/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import TauCeti.Analysis.Normed.Operator.Basic

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
* `ZeroAtInftyContinuousMap.compLeftFamily`: a strongly continuous family `u : α → E →L[R] F` of
  continuous linear maps with a uniform bound `‖u x e‖ ≤ C * ‖e‖` acts pointwise as a continuous
  linear map `C₀(α, E) →L[R] C₀(α, F)`, by `f ↦ (x ↦ u x (f x))`;
* `ZeroAtInftyContinuousMap.compLeft`: its constant case, the postcomposition with one continuous
  linear map `u : E →L[R] F` with a uniform bound `‖u e‖ ≤ C * ‖e‖`;
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
  map_sum (⟨⟨DFunLike.coe, FunLike.coe_zero⟩, FunLike.coe_add⟩ : C₀(α, β) →+ α → β) f s

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

/-- Pointwise scalar multiplication of a function vanishing at infinity by a bounded continuous
scalar function `c : α → R`. -/
def smulBounded {R : Type*} [SeminormedRing R] [Module R β] [IsBoundedSMul R β]
    (c : α → R) (hc : Continuous c) (hK : ∃ K, ∀ x, ‖c x‖ ≤ K) (f : C₀(α, β)) : C₀(α, β) where
  toFun x := c x • f x
  continuous_toFun := hc.smul (map_continuous f)
  zero_at_infty' := by
    obtain ⟨K, hK⟩ := hK
    refine squeeze_zero_norm (fun x ↦ (norm_smul_le (c x) (f x)).trans
      (mul_le_mul_of_nonneg_right (hK x) (norm_nonneg _))) ?_
    simpa using (zero_at_infty f).norm.const_mul K

/-- `smulBounded c hc hK f` multiplies `f` pointwise by `c`. -/
@[simp]
theorem smulBounded_apply {R : Type*} [SeminormedRing R] [Module R β] [IsBoundedSMul R β]
    (c : α → R) (hc : Continuous c) (hK : ∃ K, ∀ x, ‖c x‖ ≤ K) (f : C₀(α, β)) (x : α) :
    smulBounded c hc hK f x = c x • f x :=
  (rfl)

/-- A function in `C₀(ℝ, β)` has norm at most `δ > 0` outside some bounded interval `[-T, T]`. -/
theorem exists_abs_ge_norm_le (f : C₀(ℝ, β)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T > 0, ∀ s : ℝ, T ≤ |s| → ‖f s‖ ≤ δ := by
  obtain ⟨K, hK, hKsub⟩ := Filter.mem_cocompact.1
    ((tendsto_zero_iff_norm_tendsto_zero.1 (zero_at_infty f)).eventually
      (Metric.ball_mem_nhds 0 hδ))
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨max R 0 + 1, by positivity, fun s hs ↦ ?_⟩
  by_contra! hgt
  have hsK : s ∈ K := by
    by_contra hs_not
    have hball : ‖f s‖ < δ := by
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hKsub hs_not
    exact hgt.not_gt hball
  have hle : |s| ≤ R := by simpa [Real.dist_eq] using Metric.mem_closedBall.1 (hR hsK)
  exact absurd ((hs.trans hle).trans (le_max_left R 0)) (not_le_of_gt (lt_add_one _))

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

/-- **Pointwise action of a strongly continuous family.** A family `u : α → E →L[R] F` of
continuous linear maps that is strongly continuous (`x ↦ u x e` is continuous for every `e`) and
uniformly bounded by `‖u x e‖ ≤ C * ‖e‖` acts on `C₀(α, E)` by `f ↦ (x ↦ u x (f x))`, giving a
continuous linear map `C₀(α, E) →L[R] C₀(α, F)`. Its constant case is `compLeft`. -/
def compLeftFamily (u : α → E →L[R] F) (hu : ∀ e, Continuous fun x => u x e)
    (hC : ∃ C, ∀ x e, ‖u x e‖ ≤ C * ‖e‖) : C₀(α, E) →L[R] C₀(α, F) :=
  let L : C₀(α, E) →ₗ[R] C₀(α, F) :=
    { toFun f :=
        { toFun x := u x (f x)
          continuous_toFun := by
            obtain ⟨C, hC⟩ := hC
            exact AddMonoidHomClass.continuous_apply_of_bound hu hC (map_continuous f)
          zero_at_infty' := by
            obtain ⟨C, hC⟩ := hC
            refine squeeze_zero_norm (fun x => hC x (f x)) ?_
            simpa using (zero_at_infty f).norm.const_mul C }
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  { L with
    cont := by
      obtain ⟨C, hC⟩ := hC
      refine AddMonoidHomClass.continuous_of_bound L (max C 0) fun f ↦
        (norm_le (by positivity)).2 fun x ↦ (hC x (f x)).trans ?_
      exact mul_le_mul (le_max_left C 0) (norm_coe_le_norm f x) (norm_nonneg _)
        (le_max_right C 0) }

/-- `compLeftFamily u hu hC` applies `u x` at each point `x`. -/
@[simp]
theorem compLeftFamily_apply (u : α → E →L[R] F) (hu : ∀ e, Continuous fun x => u x e)
    (hC : ∃ C, ∀ x e, ‖u x e‖ ≤ C * ‖e‖) (f : C₀(α, E)) (x : α) :
    compLeftFamily u hu hC f x = u x (f x) := (rfl)

/-- A uniform bound `C` for the family `u` is also a bound for its pointwise action. -/
theorem norm_compLeftFamily_apply_le (u : α → E →L[R] F) (hu : ∀ e, Continuous fun x => u x e)
    (hC : ∃ C, ∀ x e, ‖u x e‖ ≤ C * ‖e‖) {C : ℝ} (hCu : ∀ x e, ‖u x e‖ ≤ C * ‖e‖)
    (f : C₀(α, E)) : ‖compLeftFamily u hu hC f‖ ≤ C * ‖f‖ := by
  rcases le_or_gt 0 C with hC₀ | hC₀
  · exact (norm_le (by positivity)).2 fun x ↦
      (hCu x (f x)).trans (mul_le_mul_of_nonneg_left (norm_coe_le_norm f x) hC₀)
  · have hf : ∀ x, ‖f x‖ = 0 := fun x ↦ by
      have h1 := (norm_nonneg (u x (f x))).trans (hCu x (f x))
      nlinarith [norm_nonneg (f x)]
    have h0 : ‖f‖ = 0 := le_antisymm ((norm_le le_rfl).2 fun x ↦ (hf x).le) (norm_nonneg _)
    rw [h0, mul_zero]
    exact (norm_le le_rfl).2 fun x ↦ by simpa [hf x] using (hCu x (f x))

/-- **Pointwise action of a bounded coefficient map.** A continuous linear map
`u : E →L[R] F` with a uniform bound `‖u x‖ ≤ C * ‖x‖` acts on `C₀(α, E)` by postcomposition,
giving a continuous linear map `C₀(α, E) →L[R] C₀(α, F)`: the constant case of
`compLeftFamily`. -/
def compLeft (u : E →L[R] F) (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖) : C₀(α, E) →L[R] C₀(α, F) :=
  compLeftFamily (fun _ => u) (fun _ => continuous_const) (hu.imp fun _ hC _ => hC)

/-- `compLeft u hu` applies `u` pointwise. -/
@[simp]
theorem compLeft_apply (u : E →L[R] F) (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖) (f : C₀(α, E)) (x : α) :
    compLeft u hu f x = u (f x) := (rfl)

/-- The coordinatewise action of a composite is the composite of the coordinatewise actions. -/
theorem compLeft_comp {G : Type*} [SeminormedAddCommGroup G] [Module R G] [ContinuousConstSMul R G]
    (v : F →L[R] G) (u : E →L[R] F) (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖)
    (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖) (hvu : ∃ C, ∀ x, ‖v.comp u x‖ ≤ C * ‖x‖) :
    compLeft (α := α) (v.comp u) hvu = (compLeft v hv).comp (compLeft u hu) := (rfl)

/-- A uniform bound `C` for `u` is also a uniform bound for its coordinatewise action. -/
theorem norm_compLeft_apply_le (u : E →L[R] F) {C : ℝ}
    (hC : ∀ x, ‖u x‖ ≤ C * ‖x‖) (f : C₀(α, E)) : ‖compLeft u ⟨C, hC⟩ f‖ ≤ C * ‖f‖ :=
  norm_compLeftFamily_apply_le _ _ _ (fun _ => hC) f

/-- The coordinatewise action of a bounded coefficient map is itself uniformly bounded. -/
theorem exists_norm_compLeft_apply_le (u : E →L[R] F) (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖) :
    ∃ C, ∀ f : C₀(α, E), ‖compLeft u hu f‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ := hu
  refine ⟨max C 0, norm_compLeft_apply_le u fun x ↦ ?_⟩
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
