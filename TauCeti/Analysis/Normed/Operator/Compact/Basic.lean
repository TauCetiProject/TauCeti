/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Tactic.NoncommRing

/-!
# Compact operators on quotients and bounded sequences

This file records sequential consequences of compactness for bounded sequences in seminormed
spaces. These give the subsequence and separation arguments used in Riesz theory for compact
perturbations of the identity. It also shows that the compact operators form a two-sided ideal of
the algebra of bounded operators, that a compact operator descends to a compact operator on the
quotient by a submodule of its kernel, and characterizes compact operators into complete spaces by
total boundedness of the image of a closed ball.

The ideal property also controls perturbations that are compact only relative to an operator `T`:
if `K T` is compact, then replacing `F` by `F + K` keeps `(F² - 1) T` compact, provided `[F, T]`
is compact, and keeps `[F, T]` compact when `T K` is compact as well. These are the rules behind
the compact perturbations of Fredholm modules.

## Main declarations

* `IsCompactOperator.mul_left`, `IsCompactOperator.mul_right`: products of a compact operator
  with a bounded operator, on either side, are compact.
* `ContinuousLinearMap.isCompactOperator_add_commutator`,
  `ContinuousLinearMap.isCompactOperator_add_mul_self_sub_one_mul`: the conditions `[F, T]` and
  `(F² - 1) T` compact survive perturbing `F` by an operator `K` compact relative to `T`.
* `IsCompactOperator.exists_subseq_tendsto`: a compact operator sends a bounded sequence
  to a sequence with a convergent subsequence.
* `IsCompactOperator.exists_dist_lt_of_norm_le`: a compact operator cannot keep the
  images of a bounded sequence pairwise separated.
* `IsCompactOperator.liftQL`: the operator induced by a compact operator on a quotient by a
  submodule of its kernel is compact.
* `IsCompactOperator.totallyBounded_image_closedBall`: a compact operator maps closed balls to
  totally bounded sets.
* `isCompactOperator_of_totallyBounded_image_closedBall`: conversely, a linear map into a complete
  Hausdorff space that maps a closed ball of positive radius to a totally bounded set is compact.
-/

public section

namespace IsCompactOperator

open Filter
open scoped Topology

section Mul

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]

/-- A bounded operator times a compact operator is compact. -/
theorem mul_left {T : M →L[R] M} (hT : IsCompactOperator T) (S : M →L[R] M) :
    IsCompactOperator (S * T) := by
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.coe_comp]
  exact hT.clm_comp S

/-- A compact operator times a bounded operator is compact. -/
theorem mul_right {T : M →L[R] M} (hT : IsCompactOperator T) (S : M →L[R] M) :
    IsCompactOperator (T * S) := by
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.coe_comp]
  exact hT.comp_clm S

end Mul

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {K : X →ₗ[𝕜] Y}
variable {R : ℝ} {u : ℕ → X}

/-- A compact operator sends a bounded sequence to a sequence with a convergent subsequence. -/
theorem exists_subseq_tendsto (hK : IsCompactOperator K) (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ (y : Y) (ψ : ℕ → ℕ), StrictMono ψ ∧ Tendsto (fun k => K (u (ψ k))) atTop (𝓝 y) := by
  obtain ⟨S, hS, hSsub⟩ := hK.image_closedBall_subset_compact R
  obtain ⟨y, -, ψ, hψ, hψy⟩ :=
    hS.tendsto_subseq fun n => hSsub ⟨u n, by simpa using hu n, rfl⟩
  exact ⟨y, ψ, hψ, hψy⟩

/-- A compact operator cannot keep the images of a bounded sequence pairwise separated: two
distinct indices always have images within any prescribed positive distance. -/
theorem exists_dist_lt_of_norm_le (hK : IsCompactOperator K) (hu : ∀ n, ‖u n‖ ≤ R) {ε : ℝ}
    (hε : 0 < ε) : ∃ m n, m ≠ n ∧ dist (K (u m)) (K (u n)) < ε := by
  obtain ⟨y, ψ, hψ, hψy⟩ := hK.exists_subseq_tendsto hu
  have hcauchy := hψy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy ε hε
  exact ⟨ψ (N + 1), ψ N, by simp [hψ.injective.eq_iff], hN (N + 1) (Nat.le_succ N)⟩

section Quotient

variable {R₁ R₂ M N : Type*} [Ring R₁] [Ring R₂] {σ : R₁ →+* R₂} [AddCommGroup M] [Module R₁ M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [AddCommGroup N] [Module R₂ N]
  [TopologicalSpace N]

/-- A compact operator descends to a compact operator on the quotient by a submodule of its
kernel. -/
theorem liftQL {S : Submodule R₁ M} {f : M →SL[σ] N} (hf : IsCompactOperator f)
    (h : S ≤ f.ker) : IsCompactOperator (S.liftQL f h) := by
  -- The quotient map is open, so it carries a neighbourhood of `0` that `f` maps into a compact
  -- set `C` to a neighbourhood of `0` that the induced map sends into `C`.
  obtain ⟨C, hC, hfC⟩ := hf
  refine ⟨C, hC, Filter.mem_of_superset (x := S.mkQ '' (f ⁻¹' C)) ?_ ?_⟩
  · simpa using S.isOpenMap_mkQ.image_mem_nhds hfC
  · rintro _ ⟨m, hm, rfl⟩
    simpa using hm

end Quotient

end IsCompactOperator

namespace ContinuousLinearMap

section Perturbation

variable {R : Type*} [Ring R] {M : Type*} [TopologicalSpace M] [AddCommGroup M]
  [IsTopologicalAddGroup M] [Module R M]

/-- If `[F, T]` is compact and so are `K T` and `T K`, then `[F + K, T]` is compact. -/
theorem isCompactOperator_add_commutator {F K T : M →L[R] M}
    (hc : IsCompactOperator ⇑(F * T - T * F)) (hK : IsCompactOperator ⇑(K * T))
    (hK' : IsCompactOperator ⇑(T * K)) : IsCompactOperator ⇑((F + K) * T - T * (F + K)) := by
  have e : (F + K) * T - T * (F + K) = (F * T - T * F) + K * T - T * K := by
    noncomm_ring
  rw [e, FunLike.coe_sub, FunLike.coe_add]
  exact (hc.add hK).sub hK'

/-- If `[F, T]`, `(F² - 1) T` and `K T` are compact, then `((F + K)² - 1) T` is compact. -/
theorem isCompactOperator_add_mul_self_sub_one_mul {F K T : M →L[R] M}
    (hc : IsCompactOperator ⇑(F * T - T * F)) (hs : IsCompactOperator ⇑((F * F - 1) * T))
    (hK : IsCompactOperator ⇑(K * T)) : IsCompactOperator ⇑(((F + K) * (F + K) - 1) * T) := by
  have e : ((F + K) * (F + K) - 1) * T = (F * F - 1) * T + F * (K * T) + (K * T) * F +
      K * (F * T - T * F) + K * (K * T) := by
    noncomm_ring
  simp only [e, FunLike.coe_add]
  exact ((((hs.add (hK.mul_left F)).add (hK.mul_right F)).add (hc.mul_left K)).add
    (hK.mul_left K))

end Perturbation

end ContinuousLinearMap

section TotallyBounded

variable {𝕜₁ 𝕜₂ M₁ M₂ : Type*} [NontriviallyNormedField 𝕜₁] [SeminormedRing 𝕜₂]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} [SeminormedAddCommGroup M₁] [NormedSpace 𝕜₁ M₁]
  [UniformSpace M₂] [AddCommMonoid M₂] [Module 𝕜₂ M₂] [ContinuousConstSMul 𝕜₂ M₂]
  {f : M₁ →ₛₗ[σ₁₂] M₂}

/-- A compact operator maps every closed ball to a totally bounded set. -/
theorem IsCompactOperator.totallyBounded_image_closedBall (hf : IsCompactOperator f) (r : ℝ) :
    TotallyBounded (f '' Metric.closedBall 0 r) := by
  obtain ⟨K, hK, hfK⟩ := hf.image_closedBall_subset_compact r
  exact hK.totallyBounded.subset hfK

/-- A linear map into a complete Hausdorff space that maps a closed ball of positive radius to a
totally bounded set is a compact operator. -/
theorem isCompactOperator_of_totallyBounded_image_closedBall [T2Space M₂] [CompleteSpace M₂]
    {r : ℝ} (hr : 0 < r) (hf : TotallyBounded (f '' Metric.closedBall 0 r)) :
    IsCompactOperator f :=
  (isCompactOperator_iff_isCompact_closure_image_closedBall f hr).mpr <|
    hf.closure.isCompact_of_isClosed isClosed_closure

end TotallyBounded

end
