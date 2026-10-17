/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import TauCeti.Analysis.Normed.Group.NullFamily
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic
public import TauCeti.Topology.MetricSpace.Ultra.ContinuousMaps

/-!
# Null families on a discrete index type

On a discrete index type `I` every function is continuous and the cocompact filter is the
cofinite filter, so `C₀(I, E)` is the space of families `I → E` tending to zero along the
cofinite filter, with the sup norm. Over a complete ultrametric normed ring `R`, the spaces
`C₀(I, R)` are the model spaces of nonarchimedean functional analysis: a Banach module is
orthonormalisable when it is linearly isometric to one of them.

This file develops the coordinate description of these spaces.

* `ZeroAtInftyContinuousMap.ofTendstoCofinite` builds an element of `C₀(I, E)` from a family
  tending to zero along the cofinite filter.
* `ZeroAtInftyContinuousMap.single i x` is the coordinate vector with value `x` at `i` and zero
  elsewhere; it has norm `‖x‖`.
* `ZeroAtInftyContinuousMap.exists_norm_apply_eq_norm`: the sup norm of an element of `C₀(I, E)`
  is attained at some index when `I` is nonempty.
* `ZeroAtInftyContinuousMap.hasSum_single`: every `f : C₀(I, E)` is the unconditional sum of its
  coordinate vectors `single i (f i)`. Consequently finitely supported families are dense, and
  over a ring `R` the span of the unit coordinate vectors `single i 1` is dense in `C₀(I, R)`.
* `ZeroAtInftyContinuousMap.ext_continuousLinearMap`: continuous linear maps out of `C₀(I, E)`
  are determined by their values on coordinate vectors.
* `ZeroAtInftyContinuousMap.lift`: a bounded family `e : I → M` in a complete ultrametric
  module `M` with contractive scalar action extends to the continuous linear map
  `C₀(I, R) →L[R] M`, `a ↦ ∑' i, a i • e i`, with `‖lift e he a‖ ≤ (⨆ i, ‖e i‖) * ‖a‖`. It sends
  `single i r` to `r • e i`, and it is the unique continuous linear map with `single i 1 ↦ e i`.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), §1.
* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §10.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

variable {I E : Type*} [TopologicalSpace I] [DiscreteTopology I]

section Cofinite

variable [TopologicalSpace E] [Zero E]

/-- An element of `C₀(I, E)` on a discrete index type tends to zero along the cofinite filter. -/
theorem tendsto_cofinite_zero (f : C₀(I, E)) : Tendsto f cofinite (𝓝 0) := by
  simpa only [cocompact_eq_cofinite] using zero_at_infty f

/-- A family on a discrete index type tending to zero along the cofinite filter, as an element
of `C₀(I, E)`. -/
def ofTendstoCofinite (f : I → E) (hf : Tendsto f cofinite (𝓝 0)) : C₀(I, E) where
  toFun := f
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by rwa [cocompact_eq_cofinite]

/-- The family underlying `ofTendstoCofinite f hf` is `f`. -/
@[simp]
theorem coe_ofTendstoCofinite (f : I → E) (hf : Tendsto f cofinite (𝓝 0)) :
    ⇑(ofTendstoCofinite f hf) = f := (rfl)

/-- Rebuilding an element of `C₀(I, E)` from its underlying family gives it back. -/
@[simp]
theorem ofTendstoCofinite_coe (f : C₀(I, E)) :
    ofTendstoCofinite f f.tendsto_cofinite_zero = f := (rfl)

end Cofinite

section Single

variable [DecidableEq I]

section Zero

variable [TopologicalSpace E] [Zero E]

/-- The coordinate vector `single i x : C₀(I, E)`, with value `x` at `i` and `0` elsewhere. -/
def single (i : I) (x : E) : C₀(I, E) :=
  ofTendstoCofinite (Pi.single i x : I → E) <| tendsto_const_nhds.congr' <|
    (eventually_cofinite_ne i).mono fun _ hj ↦ by simp [hj]

/-- The family underlying a coordinate vector is `Pi.single i x`. -/
@[simp]
theorem coe_single (i : I) (x : E) : ⇑(single i x) = (Pi.single i x : I → E) := (rfl)

/-- The value of a coordinate vector at an index. -/
theorem single_apply (i j : I) (x : E) : single i x j = (Pi.single i x : I → E) j := (rfl)

/-- A coordinate vector takes the value `x` at its own index. -/
theorem single_apply_self (i : I) (x : E) : single i x i = x := by
  simp

/-- A coordinate vector vanishes away from its own index. -/
theorem single_apply_of_ne {i j : I} (h : j ≠ i) (x : E) : single i x j = 0 := by
  simp [h]

/-- The coordinate vector with entry zero is zero. -/
@[simp]
theorem single_zero (i : I) : single i (0 : E) = 0 := by
  ext j
  simp

/-- The coordinate vector at a fixed index is injective in its entry. -/
theorem single_injective (i : I) : Function.Injective (single i : E → C₀(I, E)) :=
  fun x y h ↦ by simpa using congr($h i)

/-- A coordinate vector vanishes exactly when its entry does. -/
@[simp]
theorem single_eq_zero_iff {i : I} {x : E} : single i x = 0 ↔ x = 0 :=
  (single_injective i).eq_iff' (single_zero i)

end Zero

/-- Coordinate vectors are additive in their entry. -/
@[simp]
theorem single_add [TopologicalSpace E] [AddZeroClass E] [ContinuousAdd E] (i : I) (x y : E) :
    single i (x + y) = single i x + single i y := by
  ext j
  simp [Pi.single_add]

/-- The coordinate vector of a negation is the negated coordinate vector. -/
@[simp]
theorem single_neg [TopologicalSpace E] [AddGroup E] [IsTopologicalAddGroup E] (i : I) (x : E) :
    single i (-x) = -single i x := by
  ext j
  simp [Pi.single_neg]

/-- The coordinate vector of a difference is the difference of coordinate vectors. -/
@[simp]
theorem single_sub [TopologicalSpace E] [AddGroup E] [IsTopologicalAddGroup E] (i : I)
    (x y : E) : single i (x - y) = single i x - single i y := by
  ext j
  simp [Pi.single_sub]

/-- Coordinate vectors commute with scalar multiplication of their entry. -/
@[simp]
theorem single_smul [TopologicalSpace E] [Zero E] {R : Type*} [SMulZeroClass R E]
    [ContinuousConstSMul R E] (i : I) (r : R) (x : E) :
    single i (r • x) = r • single i x := by
  ext j
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [hj]

/-- Over a ring, the coordinate vector with entry `r` is `r` times the unit coordinate vector. -/
theorem smul_single_one {R : Type*} [Semiring R] [TopologicalSpace R] [IsTopologicalSemiring R]
    (i : I) (r : R) : r • single i (1 : R) = single i r := by
  rw [← single_smul, smul_eq_mul, mul_one]

/-- A coordinate vector has the norm of its entry. -/
@[simp]
theorem norm_single [SeminormedAddCommGroup E] (i : I) (x : E) : ‖single i x‖ = ‖x‖ := by
  refine le_antisymm ((norm_le (norm_nonneg x)).2 fun j ↦ ?_) ?_
  · rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [hj]
  · simpa using (single i x).norm_apply_le i

end Single

section Norm

variable [SeminormedAddCommGroup E]

/-- **The sup norm is attained**: on a nonempty discrete index type, some value of an element of
`C₀(I, E)` has norm equal to the sup norm. -/
theorem exists_norm_apply_eq_norm [Nonempty I] (f : C₀(I, E)) : ∃ i, ‖f i‖ = ‖f‖ := by
  by_cases hf : ∃ i, ‖f i‖ ≠ 0
  · obtain ⟨i, hi⟩ :=
      TauCeti.exists_norm_eq_ciSup_of_tendsto_cofinite_zero f.tendsto_cofinite_zero hf
    exact ⟨i, hi.trans f.norm_eq_iSup_norm.symm⟩
  · push Not at hf
    obtain ⟨i⟩ := ‹Nonempty I›
    have hf0 : ‖f‖ = 0 := le_antisymm ((norm_le le_rfl).2 fun j ↦ (hf j).le) (norm_nonneg _)
    exact ⟨i, (hf i).trans hf0.symm⟩

variable [DecidableEq I]

/-- **Coefficient expansion**: every element of `C₀(I, E)` is the unconditional sum of its
coordinate vectors. -/
theorem hasSum_single (f : C₀(I, E)) : HasSum (fun i ↦ single i (f i)) f := by
  rw [HasSum, Metric.tendsto_nhds]
  intro ε hε
  -- Outside the finite set of indices where `‖f i‖ ≥ ε / 2`, every value is small.
  have hfin : {i | ε / 2 ≤ ‖f i‖}.Finite := by
    simpa only [eventually_cofinite, not_lt] using
      (tendsto_zero_iff_norm_tendsto_zero.1 f.tendsto_cofinite_zero).eventually_lt_const
        (half_pos hε)
  filter_upwards [eventually_ge_atTop hfin.toFinset] with s hs
  rw [dist_eq_norm]
  refine ((norm_le (half_pos hε).le).2 fun j ↦ ?_).trans_lt (half_lt_self hε)
  by_cases hj : j ∈ s
  · simp [hj, (half_pos hε).le]
  · have hlt : ‖f j‖ < ε / 2 := not_le.1 fun h ↦ hj (hs (by simpa using h))
    simpa [hj] using hlt.le

omit [DecidableEq I] in
/-- Finitely supported families are dense in `C₀(I, E)`. -/
theorem dense_setOf_finite_support : Dense {f : C₀(I, E) | (Function.support f).Finite} := by
  classical
  refine fun f ↦ mem_closure_of_tendsto (hasSum_single f) (Eventually.of_forall fun s ↦ ?_)
  refine s.finite_toSet.subset fun j hj ↦ ?_
  by_contra h
  rw [Finset.mem_coe] at h
  simp [h] at hj

/-- Over a ring `R`, the span of the unit coordinate vectors `single i 1` is dense in
`C₀(I, R)`. -/
theorem dense_span_range_single_one {R : Type*} [SeminormedRing R] :
    Dense (Submodule.span R (Set.range fun i : I ↦ single i (1 : R)) : Set C₀(I, R)) := by
  refine fun f ↦ mem_closure_of_tendsto (hasSum_single f) (Eventually.of_forall fun s ↦ ?_)
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [← smul_single_one]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Two continuous linear maps out of `C₀(I, E)` that agree on all coordinate vectors are
equal. -/
theorem ext_continuousLinearMap {R M : Type*} [Semiring R] [Module R E]
    [ContinuousConstSMul R E] [AddCommMonoid M] [Module R M] [TopologicalSpace M] [T2Space M]
    {u v : C₀(I, E) →L[R] M} (h : ∀ i x, u (single i x) = v (single i x)) : u = v := by
  ext f
  have hu := u.hasSum (hasSum_single f)
  simp only [h] at hu
  exact hu.unique (v.hasSum (hasSum_single f))

/-- Two continuous linear maps out of `C₀(I, R)` that agree on the unit coordinate vectors
`single i 1` are equal. -/
theorem ext_continuousLinearMap_single_one {R M : Type*} [SeminormedRing R] [AddCommMonoid M]
    [Module R M] [TopologicalSpace M] [T2Space M] {u v : C₀(I, R) →L[R] M}
    (h : ∀ i, u (single i 1) = v (single i 1)) : u = v :=
  ext_continuousLinearMap fun i r ↦ by rw [← smul_single_one, map_smul, map_smul, h]

end Norm

section Lift

/-! ### Extension of bounded families -/

variable {R M : Type*} [SeminormedRing R] [NormedAddCommGroup M] [Module R M]
  [IsBoundedSMul R M] [IsUltrametricDist M] [CompleteSpace M]
  {e : I → M} (he : BddAbove (Set.range fun i ↦ ‖e i‖))
include he

private theorem summable_smul_of_bddAbove (a : C₀(I, R)) : Summable fun i ↦ a i • e i := by
  obtain ⟨C, hC⟩ := he
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun i ↦ (norm_smul_le (a i) (e i)).trans (mul_le_mul_of_nonneg_left
      (hC ⟨i, rfl⟩) (norm_nonneg _))) ?_
  simpa using (tendsto_zero_iff_norm_tendsto_zero.1 a.tendsto_cofinite_zero).mul_const C

omit [DiscreteTopology I] [CompleteSpace M] in
private theorem norm_tsum_smul_le (a : C₀(I, R)) : ‖∑' i, a i • e i‖ ≤ (⨆ i, ‖e i‖) * ‖a‖ := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg (Real.iSup_nonneg fun _ ↦ norm_nonneg _) (norm_nonneg _)) fun i ↦ ?_
  calc ‖a i • e i‖ ≤ ‖a i‖ * ‖e i‖ := norm_smul_le _ _
    _ ≤ ‖a‖ * ⨆ i, ‖e i‖ := by
        gcongr
        · exact a.norm_apply_le i
        · exact le_ciSup he i
    _ = (⨆ i, ‖e i‖) * ‖a‖ := mul_comm _ _

omit he in
variable (e) in
/-- **Extension of a bounded family**: a bounded family `e : I → M` in a complete ultrametric
module with contractive scalar action defines the continuous linear map
`C₀(I, R) →L[R] M`, `a ↦ ∑' i, a i • e i`. Its norm bound is `norm_lift_apply_le`. -/
noncomputable def lift (he : BddAbove (Set.range fun i ↦ ‖e i‖)) : C₀(I, R) →L[R] M :=
  LinearMap.mkContinuous
    { toFun a := ∑' i, a i • e i
      map_add' a b := by
        simp only [coe_add, Pi.add_apply, add_smul]
        exact (summable_smul_of_bddAbove he a).tsum_add (summable_smul_of_bddAbove he b)
      map_smul' r a := by
        simp only [coe_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact (summable_smul_of_bddAbove he a).tsum_const_smul r }
    (⨆ i, ‖e i‖) (norm_tsum_smul_le he)

/-- The extension of a bounded family sends `a` to `∑' i, a i • e i`. -/
theorem lift_apply (a : C₀(I, R)) : lift e he a = ∑' i, a i • e i := (rfl)

/-- The series `∑ i, a i • e i` converges unconditionally to the extension of `e` at `a`. -/
theorem hasSum_lift (a : C₀(I, R)) : HasSum (fun i ↦ a i • e i) (lift e he a) :=
  (summable_smul_of_bddAbove he a).hasSum

/-- The extension of a bounded family has norm at most the supremum of the norms of the family. -/
theorem norm_lift_apply_le (a : C₀(I, R)) : ‖lift e he a‖ ≤ (⨆ i, ‖e i‖) * ‖a‖ :=
  norm_tsum_smul_le he a

variable [DecidableEq I]

/-- The extension of a bounded family sends the coordinate vector `single i r` to `r • e i`. -/
@[simp]
theorem lift_single (i : I) (r : R) : lift e he (single i r) = r • e i := by
  rw [lift_apply, tsum_eq_single i fun j hj ↦ by simp [hj]]
  simp

/-- The extension of a bounded family is the unique continuous linear map sending each unit
coordinate vector `single i 1` to `e i`. -/
theorem eq_lift_iff {u : C₀(I, R) →L[R] M} : u = lift e he ↔ ∀ i, u (single i 1) = e i :=
  ⟨by rintro rfl i; simp, fun h ↦ ext_continuousLinearMap_single_one fun i ↦ by simp [h]⟩

end Lift

end ZeroAtInftyContinuousMap
