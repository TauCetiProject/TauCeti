/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Norm bounds and pointwise operators on bounded continuous functions

This file records norm estimates for operations on bounded continuous functions, and the operator
of pointwise application of a bounded continuous family of continuous linear maps.

The main estimate, `TauCeti.norm_boundedContinuousFunction_comp_le`, bounds the sup norm of the
postcomposition `N ∘ f` of a bounded continuous function `f` by an `ε`-Lipschitz map `N` by
`‖N 0‖ + ε * ‖f‖`. Thus a globally Lipschitz nonlinearity maps bounded continuous functions to
bounded ones with an explicit affine norm bound. In `TauCeti.Analysis.ODE.LyapunovPerron.Basic` it
supplies the uniform bound on the forcing term `s ↦ N (γ s)` that makes the Lyapunov–Perron
integral converge and defines the Lyapunov–Perron operator on bounded continuous curves.

`BoundedContinuousFunction.applyCLM` applies a bounded continuous family `φ` of continuous linear
maps pointwise, `(φ, h) ↦ (t ↦ φ t (h t))`, as a continuous bilinear map, and
`BoundedContinuousFunction.norm_applyCLM_apply_le` bounds the operator norm of `applyCLM φ`
by `‖φ‖`.
The derivative of a superposition operator `f ↦ G ∘ f` at `f` is `applyCLM` of the family
`t ↦ G' (f t)` of derivatives of `G`; see
`TauCeti.Analysis.Calculus.FDeriv.BoundedContinuousFunction`.

`BoundedContinuousFunction.continuousAt_of_forall_apply_eq` says that an operator that is given
near `f₀` by `Θ f t = G (f t)`, with `G` uniformly continuous on a set containing a tube around the
range of `f₀`, is continuous at `f₀` (`BoundedContinuousFunction.apply_mem_of_mem_ball` and
`BoundedContinuousFunction.ball_half_subset_of_mem_ball` are the facts about the tube).

`BoundedContinuousFunction.compContinuousₗᵢ` is precomposition with a homeomorphism, as a linear
isometry equivalence of a submodule of `α →ᵇ β` that it preserves, and
`ContinuousLinearMap.compLeftContinuousBounded_compContinuous` says that postcomposition with a
continuous linear map commutes with precomposition.
-/

public section

open Metric
open scoped NNReal BoundedContinuousFunction

namespace TauCeti

variable {T X Y : Type*} [TopologicalSpace T] [SeminormedAddCommGroup X]
  [SeminormedAddCommGroup Y]
  {N : X → Y} {ε : ℝ≥0}

/-- Postcomposition by an `ε`-Lipschitz map `N` has norm at most
`‖N 0‖ + ε * ‖f‖`. -/
theorem norm_boundedContinuousFunction_comp_le (hN : LipschitzWith ε N) (f : T →ᵇ X) :
    ‖f.comp N hN‖ ≤ ‖N 0‖ + ε * ‖f‖ := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun t ↦ ?_
  have h := hN.dist_le_mul (f t) 0
  rw [dist_eq_norm, dist_zero_right] at h
  have ht := f.norm_coe_le_norm t
  have := norm_sub_norm_le (N (f t)) (N 0)
  simp only [BoundedContinuousFunction.comp_apply]
  nlinarith [ε.coe_nonneg]

end TauCeti

namespace BoundedContinuousFunction

variable {α 𝕜 X Y : Type*} [TopologicalSpace α] [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Pointwise application `(φ, h) ↦ (t ↦ φ t (h t))` of a bounded continuous family `φ` of
continuous linear maps to a bounded continuous function `h`, as a continuous bilinear map. -/
noncomputable def applyCLM : (α →ᵇ (X →L[𝕜] Y)) →L[𝕜] (α →ᵇ X) →L[𝕜] α →ᵇ Y :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜
      (fun (φ : α →ᵇ (X →L[𝕜] Y)) (h : α →ᵇ X) ↦
        ofNormedAddCommGroup (fun t ↦ φ t (h t)) (φ.continuous.clm_apply h.continuous)
        (‖φ‖ * ‖h‖) fun t ↦
          (φ t).le_of_opNorm_le_of_le (φ.norm_coe_le_norm t) (h.norm_coe_le_norm t))
      (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp)
      (fun _ _ _ ↦ by ext; simp))
    1 fun φ h ↦ by
      rw [LinearMap.mk₂_apply, one_mul]
      exact norm_ofNormedAddCommGroup_le _ (by positivity) _

@[simp]
theorem applyCLM_apply (φ : α →ᵇ (X →L[𝕜] Y)) (h : α →ᵇ X) (t : α) :
    applyCLM φ h t = φ t (h t) :=
  (rfl)

/-- Pointwise application of `φ` has operator norm at most the sup norm of `φ`. -/
theorem norm_applyCLM_apply_le (φ : α →ᵇ (X →L[𝕜] Y)) : ‖applyCLM φ‖ ≤ ‖φ‖ :=
  (applyCLM φ).opNorm_le_bound (norm_nonneg φ) fun h ↦ (norm_le (by positivity)).2 fun t ↦
    (φ t).le_of_opNorm_le_of_le (φ.norm_coe_le_norm t) (h.norm_coe_le_norm t)


section PseudoMetricSpace

variable {α X Y : Type*} [TopologicalSpace α] [PseudoMetricSpace X] [PseudoMetricSpace Y]
  {s : Set X} {f₀ : α →ᵇ X} {δ : ℝ} {G : X → Y} {Θ : (α →ᵇ X) → α →ᵇ Y}

/-- If the values of `f₀` stay `δ > 0` inside `s`, then every function in the `δ`-ball about `f₀`
has its values in `s`. -/
theorem apply_mem_of_mem_ball {f : α →ᵇ X} (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s)
    (hf : f ∈ ball f₀ δ) (t : α) : f t ∈ s :=
  hf₀ t (mem_ball.2 ((dist_coe_le_dist t).trans_lt (mem_ball.1 hf)))

/-- If the values of `f₀` stay `δ > 0` inside `s`, then so do the values of every function
uniformly within `δ / 2` of `f₀`, with the margin `δ / 2`. -/
theorem ball_half_subset_of_mem_ball {f : α →ᵇ X} (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s)
    (hf : f ∈ ball f₀ (δ / 2)) (t : α) : ball (f t) (δ / 2) ⊆ s :=
  (ball_subset_ball' (by linarith [dist_coe_le_dist (f := f) (g := f₀) t, mem_ball.1 hf])).trans
    (hf₀ t)

/-- If `G` is uniformly continuous on `s`, the values of `f₀` stay a distance `δ > 0` inside `s`,
and `Θ f t = G (f t)` on the ball of radius `δ` about `f₀`, then `Θ` is continuous at `f₀`. -/
theorem continuousAt_of_forall_apply_eq (hG : UniformContinuousOn G s) (hδ : 0 < δ)
    (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s) (hΘ : ∀ f ∈ ball f₀ δ, ∀ t, Θ f t = G (f t)) :
    ContinuousAt Θ f₀ := by
  refine Metric.continuousAt_iff.2 fun ε hε ↦ ?_
  obtain ⟨η, hη, hGη⟩ := Metric.uniformContinuousOn_iff_le.1 hG (ε / 2) (half_pos hε)
  refine ⟨min δ η, lt_min hδ hη, fun f hf ↦ ?_⟩
  have hfδ : f ∈ ball f₀ δ := mem_ball.2 (hf.trans_le (min_le_left _ _))
  refine lt_of_le_of_lt ((dist_le (half_pos hε).le).2 fun t ↦ ?_) (half_lt_self hε)
  rw [hΘ f hfδ, hΘ f₀ (mem_ball_self hδ)]
  exact hGη _ (apply_mem_of_mem_ball hf₀ hfδ t) _
    (hf₀ t (mem_ball_self hδ)) ((dist_coe_le_dist t).trans (hf.le.trans (min_le_right _ _)))

end PseudoMetricSpace

end BoundedContinuousFunction

/-- Postcomposition with a continuous linear map commutes with precomposition with a continuous
map. -/
theorem ContinuousLinearMap.compLeftContinuousBounded_compContinuous {α δ 𝕜 β γ : Type*}
    [TopologicalSpace α] [TopologicalSpace δ] [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup β] [NormedSpace 𝕜 β] [SeminormedAddCommGroup γ] [NormedSpace 𝕜 γ]
    (g : β →L[𝕜] γ) (f : α →ᵇ β) (a : C(δ, α)) :
    g.compLeftContinuousBounded δ (f.compContinuous a) =
      (g.compLeftContinuousBounded α f).compContinuous a :=
  (rfl)

namespace BoundedContinuousFunction

variable {α 𝕜 β S : Type*} [TopologicalSpace α] [NormedField 𝕜] [SeminormedAddCommGroup β]
  [NormedSpace 𝕜 β] [SetLike S (α →ᵇ β)] [AddSubgroupClass S (α →ᵇ β)]
  [SMulMemClass S 𝕜 (α →ᵇ β)]

/-- Precomposition with a continuous map `a` of `α` that has a continuous inverse `b`, as a linear
isometry equivalence of a submodule `s` of `α →ᵇ β`, such as a `Submodule` or a `Subalgebra`,
preserved by both `a` and `b`. -/
def compContinuousₗᵢ (s : S) (a b : C(α, α)) (hab : ∀ x, a (b x) = x) (hba : ∀ x, b (a x) = x)
    (ha : ∀ f ∈ s, f.compContinuous a ∈ s) (hb : ∀ f ∈ s, f.compContinuous b ∈ s) :
    s ≃ₗᵢ[𝕜] s where
  toFun f := ⟨(f : α →ᵇ β).compContinuous a, ha _ f.2⟩
  invFun f := ⟨(f : α →ᵇ β).compContinuous b, hb _ f.2⟩
  map_add' _ _ := Subtype.ext <| ext fun _ => by simp
  map_smul' _ _ := Subtype.ext <| ext fun _ => by simp
  left_inv f := Subtype.ext <| ext fun x => congrArg (f : α →ᵇ β) (hab x)
  right_inv f := Subtype.ext <| ext fun x => congrArg (f : α →ᵇ β) (hba x)
  norm_map' f := by
    rw [AddSubgroupClass.coe_norm, AddSubgroupClass.coe_norm]
    refine le_antisymm ((f : α →ᵇ β).norm_compContinuous_le a) ?_
    calc ‖(f : α →ᵇ β)‖ = ‖((f : α →ᵇ β).compContinuous a).compContinuous b‖ := by
          congr 1
          ext x
          exact congrArg (f : α →ᵇ β) (hab x).symm
      _ ≤ ‖(f : α →ᵇ β).compContinuous a‖ := norm_compContinuous_le _ _

/-- `compContinuousₗᵢ s a b … f` is the precomposition of `f` with `a`. -/
@[simp]
theorem compContinuousₗᵢ_apply (s : S) (a b : C(α, α)) (hab : ∀ x, a (b x) = x)
    (hba : ∀ x, b (a x) = x) (ha : ∀ f ∈ s, f.compContinuous a ∈ s)
    (hb : ∀ f ∈ s, f.compContinuous b ∈ s) (f : s) :
    (compContinuousₗᵢ (𝕜 := 𝕜) s a b hab hba ha hb f : α →ᵇ β) =
      (f : α →ᵇ β).compContinuous a :=
  (rfl)

/-- The inverse of `compContinuousₗᵢ s a b …` is precomposition with `b`. -/
@[simp]
theorem compContinuousₗᵢ_symm_apply (s : S) (a b : C(α, α)) (hab : ∀ x, a (b x) = x)
    (hba : ∀ x, b (a x) = x) (ha : ∀ f ∈ s, f.compContinuous a ∈ s)
    (hb : ∀ f ∈ s, f.compContinuous b ∈ s) (f : s) :
    ((compContinuousₗᵢ (𝕜 := 𝕜) s a b hab hba ha hb).symm f : α →ᵇ β) =
      (f : α →ᵇ β).compContinuous b :=
  (rfl)

end BoundedContinuousFunction
