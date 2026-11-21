/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import TauCeti.Analysis.Normed.Module.Dual.Submodule
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# A strongly null net of rank-one operators with unbounded norms

On a normed space `E` over `ℝ` or `ℂ` (more generally, over a field with
`IsRCLikeNormedField`) that is not finite-dimensional, every finite-dimensional
subspace is closed and proper. For a closed proper subspace `S`, the Hahn–Banach theorem gives a
continuous linear functional `f` vanishing on `S` and taking the value `1` at a vector `x ∉ S`.
The rank-one operator `f.smulRight (c • x)` then vanishes on `S` and has operator norm at least
`‖c‖`, which can be made as large as we like
(`Submodule.exists_dual_forall_mem_eq_zero_lt_norm_smulRight`); such an operator has rank at
most one (`LinearMap.rank_smulRight_le_one`).

Indexing these choices by pairs `(F, n)` of a finite set `F ⊆ E` and a natural number `n`, with
the product order (inclusion of finite sets and the usual order on `ℕ`) and its `atTop` filter,
gives the net `TauCeti.unboundedRankOneNet` of rank-one operators which converges to `0` in
Mathlib's topology of pointwise convergence `PointwiseConvergenceCLM` (the strong operator
topology, `TauCeti.tendsto_toPointwiseConvergenceCLM_unboundedRankOneNet`), while its operator
norms tend to infinity (`TauCeti.tendsto_norm_unboundedRankOneNet_atTop`). All properties are
collected in `TauCeti.exists_tendsto_toPointwiseConvergenceCLM_zero_tendsto_norm_atTop`.

For a Banach space `E` this contrasts with
`ContinuousLinearMap.exists_norm_le_of_tendsto_pointwise`: by the Banach–Steinhaus theorem a
strongly convergent *sequence* of operators is norm bounded, but a strongly convergent net need
not be, not even eventually.
-/

public section

open Filter Topology

namespace LinearMap

variable {R M N : Type*} [Semiring R] [StrongRankCondition R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- A map `b ↦ f b • x` built from a linear functional `f` has rank at most one. -/
theorem rank_smulRight_le_one (f : M →ₗ[R] R) (x : N) : (f.smulRight x).rank ≤ 1 := by
  refine (Submodule.rank_mono ?_).trans ((rank_span_le {x}).trans (by simp))
  rintro _ ⟨b, rfl⟩
  exact Submodule.mem_span_singleton.2 ⟨f b, rfl⟩

end LinearMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]

namespace Submodule

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A closed proper subspace `S` is annihilated by rank-one operators `x ↦ f x • v` of arbitrarily
large operator norm. -/
theorem exists_dual_forall_mem_eq_zero_lt_norm_smulRight {S : Submodule 𝕜 E}
    (hS : IsClosed (S : Set E)) (hS_ne : S ≠ ⊤) (r : ℝ) :
    ∃ (f : StrongDual 𝕜 E) (v : E), (∀ y ∈ S, f y = 0) ∧ r < ‖f.smulRight v‖ := by
  obtain ⟨x, hx⟩ := SetLike.exists_notMem_of_ne_top S hS_ne
  obtain ⟨f, hfS, hfx⟩ := exists_dual_forall_mem_eq_zero_eq_one hS hx
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 r
  refine ⟨f, c • x, hfS, hc.trans_le ?_⟩
  -- `‖f.smulRight (c • x)‖ = ‖c‖ * (‖f‖ * ‖x‖)` and `1 = ‖f x‖ ≤ ‖f‖ * ‖x‖`.
  have h₁ := f.le_opNorm x
  rw [hfx, norm_one] at h₁
  rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, mul_left_comm]
  exact le_mul_of_one_le_right (norm_nonneg c) h₁

end Submodule

namespace TauCeti

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- In a normed space that is not finite-dimensional, the span of a finite set is annihilated by
rank-one operators `x ↦ f x • v` of arbitrarily large operator norm. -/
theorem exists_dual_forall_mem_span_eq_zero_lt_norm_smulRight (hE : ¬ FiniteDimensional 𝕜 E)
    (F : Finset E) (r : ℝ) :
    ∃ (f : StrongDual 𝕜 E) (v : E),
      (∀ y ∈ Submodule.span 𝕜 (F : Set E), f y = 0) ∧ r < ‖f.smulRight v‖ := by
  -- Completeness of `𝕜` makes finite-dimensional subspaces closed; they are proper as `E` is
  -- not finite-dimensional.
  have : CompleteSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
  exact Submodule.exists_dual_forall_mem_eq_zero_lt_norm_smulRight
    (Submodule.span 𝕜 (F : Set E)).isClosed_of_finiteDimensional
    (fun h ↦ hE (Module.Finite.equiv (LinearEquiv.ofTop _ h))) r

/-- A net of rank-one operators on a normed space `E` which is not finite-dimensional, indexed by
pairs `(F, n)` of a finite set `F ⊆ E` and a natural number `n`: the operator at `(F, n)` is a
chosen rank-one operator `x ↦ f x • v` vanishing on the span of `F` with norm greater than `n`.
It tends to `0` pointwise while its norms tend to infinity. -/
noncomputable def unboundedRankOneNet (hE : ¬ FiniteDimensional 𝕜 E) (i : Finset E × ℕ) :
    E →L[𝕜] E :=
  (exists_dual_forall_mem_span_eq_zero_lt_norm_smulRight hE i.1 i.2).choose.smulRight
    (exists_dual_forall_mem_span_eq_zero_lt_norm_smulRight hE i.1 i.2).choose_spec.choose

variable (hE : ¬ FiniteDimensional 𝕜 E)

/-- Each operator of `unboundedRankOneNet` has rank at most one. -/
theorem rank_unboundedRankOneNet_le_one (i : Finset E × ℕ) :
    (unboundedRankOneNet hE i : E →ₗ[𝕜] E).rank ≤ 1 :=
  LinearMap.rank_smulRight_le_one _ _

/-- The operator of `unboundedRankOneNet` at `(F, n)` vanishes on the span of `F`. -/
theorem unboundedRankOneNet_apply_eq_zero {i : Finset E × ℕ} {y : E}
    (hy : y ∈ Submodule.span 𝕜 (i.1 : Set E)) : unboundedRankOneNet hE i y = 0 := by
  rw [unboundedRankOneNet, ContinuousLinearMap.smulRight_apply,
    (exists_dual_forall_mem_span_eq_zero_lt_norm_smulRight hE i.1 i.2).choose_spec.choose_spec.1
      y hy, zero_smul]

/-- The operator of `unboundedRankOneNet` at `(F, n)` has norm greater than `n`. -/
theorem lt_norm_unboundedRankOneNet (i : Finset E × ℕ) : (i.2 : ℝ) < ‖unboundedRankOneNet hE i‖ :=
  (exists_dual_forall_mem_span_eq_zero_lt_norm_smulRight hE i.1 i.2).choose_spec.choose_spec.2

/-- `unboundedRankOneNet` tends to `0` in the topology of pointwise convergence (the strong
operator topology): each vector eventually lies in the finite set of the index. -/
theorem tendsto_toPointwiseConvergenceCLM_unboundedRankOneNet :
    Tendsto (fun i ↦ ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E E
      (unboundedRankOneNet hE i)) atTop (𝓝 0) := by
  refine PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.2 fun x ↦ ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (({x}, 0) : Finset E × ℕ)] with i hi
  exact (unboundedRankOneNet_apply_eq_zero hE
    (Submodule.subset_span (hi.1 (Finset.mem_singleton_self x)))).symm

/-- The operator norms of `unboundedRankOneNet` tend to infinity. -/
theorem tendsto_norm_unboundedRankOneNet_atTop :
    Tendsto (fun i ↦ ‖unboundedRankOneNet hE i‖) atTop atTop := by
  refine tendsto_atTop.2 fun b ↦ ?_
  filter_upwards [eventually_ge_atTop ((∅, ⌈b⌉₊) : Finset E × ℕ)] with i hi
  exact (Nat.le_ceil b).trans ((Nat.cast_le.2 hi.2).trans (lt_norm_unboundedRankOneNet hE i).le)

include hE in
/-- **A strongly null net with unbounded norms.** On a normed space `E` which is not
finite-dimensional, there is a net of operators indexed by pairs `(F, n)` of a finite set
`F ⊆ E` and a natural number `n`, directed by inclusion and the usual order, such that the
operator at `(F, n)` has rank at most one, vanishes on the span of `F` and has norm at least
`n`. Along the `atTop` filter of this directed set the net tends to `0` in the topology of
pointwise convergence (the strong operator topology), while the operator norms tend to
infinity. So the Banach–Steinhaus bound for strongly convergent sequences fails for nets. -/
theorem exists_tendsto_toPointwiseConvergenceCLM_zero_tendsto_norm_atTop :
    ∃ T : Finset E × ℕ → E →L[𝕜] E,
      (∀ i, (T i : E →ₗ[𝕜] E).rank ≤ 1) ∧
      (∀ i, ∀ y ∈ Submodule.span 𝕜 (i.1 : Set E), T i y = 0) ∧
      (∀ i, (i.2 : ℝ) ≤ ‖T i‖) ∧
      Tendsto (fun i ↦ ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E E (T i))
        atTop (𝓝 0) ∧
      Tendsto (fun i ↦ ‖T i‖) atTop atTop :=
  ⟨unboundedRankOneNet hE, rank_unboundedRankOneNet_le_one hE,
    fun _ _ ↦ unboundedRankOneNet_apply_eq_zero hE, fun i ↦ (lt_norm_unboundedRankOneNet hE i).le,
    tendsto_toPointwiseConvergenceCLM_unboundedRankOneNet hE,
    tendsto_norm_unboundedRankOneNet_atTop hE⟩

end TauCeti
