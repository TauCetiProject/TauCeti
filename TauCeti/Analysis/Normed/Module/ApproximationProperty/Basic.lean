/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.FiniteRange
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
import TauCeti.Analysis.Convex.TotallyBounded
import TauCeti.Analysis.Normed.Module.Convex

/-!
# Approximation properties of normed spaces

The approximation property asks for finite-rank bounded operators approximating the identity
uniformly on each norm-compact set. The bounded approximation property imposes a common operator
norm bound; the metric approximation property uses bound one. These definitions do not require
completeness.

A uniformly bounded net of finite-rank operators converging pointwise to the identity gives the
bounded approximation property. The compact-uniform convergence needed here follows from
Mathlib's equicontinuity criterion for bounded families of operators and its Ascoli theorem.
This criterion applies to finite projections of Schauder bases.

Evaluating bounded operators along a null sequence `x` gives a linear map
`TauCeti.evalNullSeq` into `C₀(ℕ, F)`. If the identity lies in the closure of the evaluations of a
family of operators, then members of the family approximate the identity uniformly along `x`
(`TauCeti.exists_mem_forall_norm_sub_lt_of_mem_closure`).

Over `ℝ` or `ℂ`, the finite-rank operators of norm at most `r` form a real-convex set
(`TauCeti.convex_setOf_hasFiniteRange_norm_le`). By Grothendieck's compactness lemma, every totally
bounded set lies in the closed convex hull of a null sequence, so approximating the identity
uniformly along null sequences by operators from any family approximates it on totally bounded
sets (`TauCeti.exists_mem_forall_norm_sub_lt_of_forall_tendsto_zero`).

Finite rank is Mathlib's `LinearMap.HasFiniteRange`, meaning finitely generated range, which
over a field is equivalent to finite-dimensional range.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, Section 3.4.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1.
-/

public section

open Filter Set
open scoped NNReal Topology ZeroAtInfty

namespace TauCeti

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- The identity can be approximated uniformly on every norm-compact set by bounded operators
with finite-dimensional range. -/
def HasApproximationProperty : Prop :=
  ∀ K : Set E, IsCompact K → ∀ ε > (0 : ℝ), ∃ T : E →L[𝕜] E,
    T.toLinearMap.HasFiniteRange ∧ ∀ x ∈ K, ‖T x - x‖ < ε

/-- The approximation property with the common operator norm bound `C`. -/
def HasBoundedApproximationPropertyWith (C : ℝ≥0) : Prop :=
  ∀ K : Set E, IsCompact K → ∀ ε > (0 : ℝ), ∃ T : E →L[𝕜] E,
    T.toLinearMap.HasFiniteRange ∧ ‖T‖ ≤ C ∧ ∀ x ∈ K, ‖T x - x‖ < ε

/-- The identity has finite-rank approximations on compact sets with some common finite norm
bound. The bound is independent of both the compact set and the error tolerance. -/
def HasBoundedApproximationProperty : Prop :=
  ∃ C : ℝ≥0, HasBoundedApproximationPropertyWith 𝕜 E C

/-- The identity can be approximated uniformly on compact sets by finite-rank contractions. -/
def HasMetricApproximationProperty : Prop :=
  HasBoundedApproximationPropertyWith 𝕜 E 1

variable {𝕜 E}

/-- Characterization of the approximation property by compact-set approximations. -/
theorem hasApproximationProperty_iff : HasApproximationProperty 𝕜 E ↔
    ∀ K : Set E, IsCompact K → ∀ ε > (0 : ℝ), ∃ T : E →L[𝕜] E,
      T.toLinearMap.HasFiniteRange ∧ ∀ x ∈ K, ‖T x - x‖ < ε := Iff.rfl

/-- Characterization of the approximation property with a prescribed norm bound. -/
theorem hasBoundedApproximationPropertyWith_iff {C : ℝ≥0} :
    HasBoundedApproximationPropertyWith 𝕜 E C ↔
      ∀ K : Set E, IsCompact K → ∀ ε > (0 : ℝ), ∃ T : E →L[𝕜] E,
        T.toLinearMap.HasFiniteRange ∧ ‖T‖ ≤ C ∧ ∀ x ∈ K, ‖T x - x‖ < ε := Iff.rfl

/-- A larger norm bound preserves the bounded approximation property. -/
theorem HasBoundedApproximationPropertyWith.mono {C D : ℝ≥0}
    (h : HasBoundedApproximationPropertyWith 𝕜 E C) (hCD : C ≤ D) :
    HasBoundedApproximationPropertyWith 𝕜 E D := by
  intro K hK ε hε
  obtain ⟨T, hT, hnorm, herr⟩ := h K hK ε hε
  exact ⟨T, hT, hnorm.trans (by exact_mod_cast hCD), herr⟩

/-- Forgetting a prescribed norm bound gives the approximation property. -/
theorem HasBoundedApproximationPropertyWith.hasApproximationProperty {C : ℝ≥0}
    (h : HasBoundedApproximationPropertyWith 𝕜 E C) : HasApproximationProperty 𝕜 E := by
  intro K hK ε hε
  obtain ⟨T, hT, _, herr⟩ := h K hK ε hε
  exact ⟨T, hT, herr⟩

/-- A prescribed finite bound witnesses the bounded approximation property. -/
theorem HasBoundedApproximationPropertyWith.hasBoundedApproximationProperty {C : ℝ≥0}
    (h : HasBoundedApproximationPropertyWith 𝕜 E C) :
    HasBoundedApproximationProperty 𝕜 E := ⟨C, h⟩

/-- The bounded approximation property implies the approximation property. -/
theorem HasBoundedApproximationProperty.hasApproximationProperty
    (h : HasBoundedApproximationProperty 𝕜 E) : HasApproximationProperty 𝕜 E := by
  obtain ⟨C, hC⟩ := h
  exact hC.hasApproximationProperty

/-- Characterization of the bounded approximation property by a common finite bound. -/
theorem hasBoundedApproximationProperty_iff : HasBoundedApproximationProperty 𝕜 E ↔
    ∃ C : ℝ≥0, HasBoundedApproximationPropertyWith 𝕜 E C := Iff.rfl

/-- The metric approximation property is the case of norm bound one. -/
theorem hasMetricApproximationProperty_iff : HasMetricApproximationProperty 𝕜 E ↔
    HasBoundedApproximationPropertyWith 𝕜 E 1 := Iff.rfl

/-- The metric approximation property implies the bounded approximation property. -/
theorem HasMetricApproximationProperty.hasBoundedApproximationProperty
    (h : HasMetricApproximationProperty 𝕜 E) : HasBoundedApproximationProperty 𝕜 E :=
  HasBoundedApproximationPropertyWith.hasBoundedApproximationProperty h

/-- A uniformly bounded net of finite-rank operators converging pointwise to the identity
gives the bounded approximation property with the same bound. -/
theorem HasBoundedApproximationPropertyWith.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {C : ℝ≥0} (T : ι → E →L[𝕜] E) (hfinite : ∀ i, (T i).toLinearMap.HasFiniteRange)
    (hbound : ∀ i, ‖T i‖ ≤ C) (hlim : ∀ x, Tendsto (fun i => T i x) l (𝓝 x)) :
    HasBoundedApproximationPropertyWith 𝕜 E C := by
  have hbounded : ∃ D : ℝ, ∀ i, ‖T i‖ ≤ D := ⟨C, hbound⟩
  have heq : Equicontinuous (fun i x => T i x) :=
    ((NormedSpace.equicontinuous_tfae T).out 6 2).mp hbounded
  intro K hK ε hε
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hpoint : Tendsto (fun i (x : K) => T i x) l (𝓝 fun x : K => (x : E)) :=
    tendsto_pi_nhds.mpr fun x => hlim x
  have hunif : TendstoUniformly (fun i (x : K) => T i x) (fun x => (x : E)) l := by
    apply UniformFun.tendsto_iff_tendstoUniformly.mp
    exact ((equicontinuous_restrict_iff _).mpr (heq.equicontinuousOn K)).tendsto_uniformFun_iff_pi
      l _ |>.mpr hpoint
  obtain ⟨i, hi⟩ := (Metric.tendstoUniformly_iff.mp hunif ε hε).exists
  refine ⟨T i, hfinite i, hbound i, fun x hx => ?_⟩
  simpa only [dist_eq_norm, norm_sub_rev] using hi ⟨x, hx⟩

/-- Finite-dimensional normed spaces have the metric approximation property. -/
theorem hasMetricApproximationProperty_of_finiteDimensional [FiniteDimensional 𝕜 E] :
    HasMetricApproximationProperty 𝕜 E := by
  intro K _ ε hε
  exact ⟨ContinuousLinearMap.id 𝕜 E, .of_finite_dom, ContinuousLinearMap.norm_id_le,
    fun x _ => by simpa using hε⟩

section NullSequence

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {x : ℕ → E}

variable (𝕜 F) in
/-- Evaluation of bounded operators `E →L[𝕜] F` along a null sequence `x`, as a linear map
`(E →L[𝕜] F) →ₗ[𝕜] C₀(ℕ, F)`. -/
noncomputable def evalNullSeq (hx : Tendsto x atTop (𝓝 0)) : (E →L[𝕜] F) →ₗ[𝕜] C₀(ℕ, F) where
  toFun T := ZeroAtInftyContinuousMap.mkOfDiscrete (fun n ↦ T (x n)) <| by
    rw [Nat.cofinite_eq_atTop, ← map_zero T]
    exact (T.continuous.tendsto 0).comp hx
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem evalNullSeq_apply (hx : Tendsto x atTop (𝓝 0)) (T : E →L[𝕜] F) (n : ℕ) :
    evalNullSeq 𝕜 F hx T n = T (x n) := by
  simp [evalNullSeq]

/-- If the identity, evaluated along a null sequence `x`, lies in the closure of the evaluations
of a set `P` of operators, then for every `δ > 0` some `R ∈ P` is within `δ` of the identity
uniformly along `x`. -/
theorem exists_mem_forall_norm_sub_lt_of_mem_closure (hx : Tendsto x atTop (𝓝 0))
    {P : Set (E →L[𝕜] E)}
    (h : evalNullSeq 𝕜 E hx (ContinuousLinearMap.id 𝕜 E) ∈ closure (evalNullSeq 𝕜 E hx '' P))
    {δ : ℝ} (hδ : 0 < δ) : ∃ R ∈ P, ∀ n, ‖R (x n) - x n‖ < δ := by
  obtain ⟨_, ⟨R, hR, rfl⟩, hdist⟩ := Metric.mem_closure_iff.1 h δ hδ
  refine ⟨R, hR, fun n ↦ ?_⟩
  rw [dist_comm, dist_eq_norm, ← map_sub] at hdist
  simpa using
    (ZeroAtInftyContinuousMap.norm_coe_le_norm
      (evalNullSeq 𝕜 E hx (R - ContinuousLinearMap.id 𝕜 E)) n).trans_lt hdist

end NullSequence

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The finite-rank operators of norm at most `r` form a real-convex set. -/
theorem convex_setOf_hasFiniteRange_norm_le [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] (r : ℝ) :
    Convex ℝ {T : E →L[𝕜] F | T.toLinearMap.HasFiniteRange ∧ ‖T‖ ≤ r} := by
  rintro T ⟨hT, hTr⟩ S ⟨hS, hSr⟩ a b ha hb hab
  refine ⟨?_, ?_⟩
  · rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) a T, RCLike.real_smul_eq_coe_smul (K := 𝕜) b S,
      ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
      ContinuousLinearMap.toLinearMap_smul]
    exact (hT.smul _).add (hS.smul _)
  · calc ‖a • T + b • S‖ ≤ a * ‖T‖ + b * ‖S‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * r + b * r := by gcongr
      _ = r := by rw [← add_mul, hab, one_mul]

/-- If every null sequence `x` admits, for each `δ > 0`, an operator `R ∈ P` within `δ` of the
identity uniformly along `x`, then for every totally bounded set `K` and `ε > 0` some `R ∈ P` is
within `ε` of the identity uniformly on `K`. By Grothendieck's compactness lemma, `K` lies in the
closed convex hull of a null sequence. -/
theorem exists_mem_forall_norm_sub_lt_of_forall_tendsto_zero {P : Set (E →L[𝕜] E)}
    (h : ∀ x : ℕ → E, Tendsto x atTop (𝓝 0) → ∀ δ > (0 : ℝ),
      ∃ R ∈ P, ∀ n, ‖R (x n) - x n‖ < δ)
    {K : Set E} (hK : TotallyBounded K) {ε : ℝ} (hε : 0 < ε) :
    ∃ R ∈ P, ∀ z ∈ K, ‖R z - z‖ < ε := by
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  have : IsScalarTower ℝ 𝕜 E := .restrictScalars ℝ 𝕜 E
  obtain ⟨x, hx, hKx⟩ := hK.exists_tendsto_zero_subset_closure_convexHull
  obtain ⟨R, hR, hRx⟩ := h x hx _ (half_pos hε)
  refine ⟨R, hR, fun z hz ↦ ?_⟩
  have hle : ‖(R - ContinuousLinearMap.id 𝕜 E) z‖ ≤ ε / 2 :=
    (R - ContinuousLinearMap.id 𝕜 E).norm_le_of_mem_closure_convexHull
      (by rintro _ ⟨n, rfl⟩; exact (hRx n).le) (hKx hz)
  simpa using hle.trans_lt (half_lt_self hε)

end RCLike

end TauCeti
