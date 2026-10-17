/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic
public import TauCeti.Analysis.Normed.Group.NullFamily
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# The model space `C₀(I, E)` on a discrete index

For a discrete space `I`, the cocompact filter on `I` is the cofinite filter, so `C₀(I, E)` is
the space of families `I → E` tending to zero along the cofinite filter, with the sup norm. Over
a complete ultrametric normed ring `R`, the spaces `C₀(I, R)` are the model spaces of
nonarchimedean functional analysis: orthonormalisable Banach modules are those linearly isometric
to some `C₀(I, R)`.

This file develops the coordinate structure of `C₀(I, E)`:

* `ZeroAtInftyContinuousMap.mkOfDiscrete`: a family tending to zero along the cofinite filter as
  an element of `C₀(I, E)`;
* `ZeroAtInftyContinuousMap.single i x`: the coordinate vector supported at `i` with value `x`,
  of norm `‖x‖` (`ZeroAtInftyContinuousMap.norm_single`);
* `ZeroAtInftyContinuousMap.exists_norm_coe_eq_norm`: the sup norm is attained at some
  coordinate when `I` is nonempty;
* `ZeroAtInftyContinuousMap.hasSum_single`: every `f` is the unconditional sum of its coordinate
  vectors `single i (f i)`, and for scalar families `f = ∑ i, f i • single i 1`
  (`ZeroAtInftyContinuousMap.hasSum_smul_single_one`);
* `ZeroAtInftyContinuousMap.dense_setOf_finite_support` and
  `ZeroAtInftyContinuousMap.dense_span_single_one`: finitely supported families are dense, and
  the coordinate vectors `single i 1` span a dense submodule of `C₀(I, R)`;
* `ZeroAtInftyContinuousMap.continuousLinearMap_ext`: continuous linear maps out of `C₀(I, E)`
  are determined by their values on coordinate vectors;
* `ZeroAtInftyContinuousMap.lift`: a bounded family `e : I → M` in a complete ultrametric
  module `M` with contractive scalar action extends to the continuous linear map
  `C₀(I, R) →L[R] M`, `a ↦ ∑' i, a i • e i`, with `‖lift e he a‖ ≤ (⨆ i, ‖e i‖) * ‖a‖`. It sends
  `single i r` to `r • e i`, and it is the unique continuous linear map with `single i 1 ↦ e i`.

Apart from `lift`, none of these statements needs completeness or the ultrametric inequality.

## References

* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §10.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), 69–85.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

variable {I β : Type*} [TopologicalSpace I] [DiscreteTopology I]

section Zero

variable [TopologicalSpace β] [Zero β]

/-- A function vanishing at infinity on a discrete space tends to zero along the cofinite
filter. -/
theorem tendsto_cofinite (f : C₀(I, β)) : Tendsto f cofinite (𝓝 0) := by
  simpa [cocompact_eq_cofinite] using zero_at_infty f

/-- A family on a discrete space tending to zero along the cofinite filter, as a continuous
function vanishing at infinity. -/
def mkOfDiscrete (f : I → β) (hf : Tendsto f cofinite (𝓝 0)) : C₀(I, β) where
  toFun := f
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by rwa [cocompact_eq_cofinite]

/-- `mkOfDiscrete f hf` has underlying family `f`. -/
@[simp]
theorem coe_mkOfDiscrete (f : I → β) (hf : Tendsto f cofinite (𝓝 0)) :
    ⇑(mkOfDiscrete f hf) = f := (rfl)

/-- `mkOfDiscrete` recovers every function vanishing at infinity on a discrete space. -/
@[simp]
theorem mkOfDiscrete_coe (f : C₀(I, β)) : mkOfDiscrete f f.tendsto_cofinite = f := (rfl)

variable [DecidableEq I]

/-- The coordinate vector `single i b` of `C₀(I, β)`: the family with value `b` at `i` and zero
elsewhere. -/
def single (i : I) (b : β) : C₀(I, β) :=
  mkOfDiscrete (Pi.single i b) <| tendsto_const_nhds.congr' <|
    (eventually_cofinite_ne i).mono fun _ hj ↦ by simp [hj]

/-- `single i b` has underlying family `Pi.single i b`. -/
@[simp]
theorem coe_single (i : I) (b : β) : ⇑(single i b) = Pi.single i b := (rfl)

/-- The coordinates of `single i b`. -/
theorem single_apply (i j : I) (b : β) : single i b j = if j = i then b else 0 :=
  Pi.single_apply i b j

/-- `single i b` takes the value `b` at `i`. -/
theorem single_eq_same (i : I) (b : β) : single i b i = b := by simp

/-- `single i b` vanishes away from `i`. -/
theorem single_eq_of_ne {i j : I} (h : j ≠ i) (b : β) : single i b j = 0 := by simp [h]

/-- The coordinate vector with value zero is zero. -/
@[simp]
theorem single_zero (i : I) : single i (0 : β) = 0 := by ext; simp

/-- The coordinate vector at a fixed index is injective in its entry. -/
theorem single_injective (i : I) : Function.Injective (single i : β → C₀(I, β)) :=
  fun x y h ↦ by simpa using congr($h i)

/-- A coordinate vector vanishes exactly when its entry does. -/
@[simp]
theorem single_eq_zero_iff {i : I} {b : β} : single i b = 0 ↔ b = 0 :=
  (single_injective i).eq_iff' (single_zero i)

end Zero

section Algebra

variable [DecidableEq I] [TopologicalSpace β]

/-- `single i` is additive. -/
theorem single_add [AddZeroClass β] [ContinuousAdd β] (i : I) (b c : β) :
    single i (b + c) = single i b + single i c := by
  ext; simp [Pi.single_add]

/-- The coordinate vector of a negation is the negated coordinate vector. -/
theorem single_neg [AddGroup β] [IsTopologicalAddGroup β] (i : I) (b : β) :
    single i (-b) = -single i b := by
  ext; simp [Pi.single_neg]

/-- The coordinate vector of a difference is the difference of coordinate vectors. -/
theorem single_sub [AddGroup β] [IsTopologicalAddGroup β] (i : I) (b c : β) :
    single i (b - c) = single i b - single i c := by
  ext; simp [Pi.single_sub]

/-- `single i` commutes with scalar multiplication. -/
theorem single_smul {R : Type*} [Zero β] [SMulZeroClass R β] [ContinuousConstSMul R β] (i : I)
    (r : R) (b : β) : single i (r • b) = r • single i b := by
  ext j; by_cases h : j = i <;> simp [h]

/-- In `C₀(I, R)`, the coordinate vector `single i r` is `r` times the unit vector
`single i 1`. -/
theorem smul_single_one {R : Type*} [TopologicalSpace R] [MulZeroOneClass R] [ContinuousMul R]
    (i : I) (r : R) :
    r • single i (1 : R) = single i r := by
  ext j; by_cases h : j = i <;> simp [h]

end Algebra

section Normed

variable [SeminormedAddCommGroup β]

/-- A coordinate vector has the norm of its nonzero entry. -/
@[simp]
theorem norm_single [DecidableEq I] (i : I) (b : β) : ‖single i b‖ = ‖b‖ := by
  refine le_antisymm ((norm_le (norm_nonneg b)).2 fun j ↦ ?_) ?_
  · by_cases h : j = i <;> simp [h]
  · simpa using norm_coe_le_norm (single i b) i

/-- **The sup norm is attained**: on a nonempty discrete index, some coordinate of `f ∈ C₀(I, β)`
has norm `‖f‖`. This covers every nonzero `f`, whose index type is necessarily nonempty. -/
theorem exists_norm_coe_eq_norm [Nonempty I] (f : C₀(I, β)) : ∃ i, ‖f i‖ = ‖f‖ := by
  by_cases hf : ∃ i, ‖f i‖ ≠ 0
  · obtain ⟨i, hi⟩ := TauCeti.exists_forall_norm_le_of_tendsto_cofinite_zero f.tendsto_cofinite hf
    exact ⟨i, le_antisymm (norm_coe_le_norm f i) ((norm_le (norm_nonneg _)).2 hi)⟩
  · push Not at hf
    obtain ⟨i⟩ := ‹Nonempty I›
    refine ⟨i, ?_⟩
    rw [hf i]
    exact (le_antisymm ((norm_le le_rfl).2 fun j ↦ (hf j).le) (norm_nonneg f)).symm

section

variable [DecidableEq I]

/-- The partial sum of the coordinate expansion of `f` over a finite set `s` is the restriction of
`f` to `s`. -/
theorem sum_single_apply (f : C₀(I, β)) (s : Finset I) (j : I) :
    (∑ i ∈ s, single i (f i)) j = if j ∈ s then f j else 0 := by
  simp [Finset.sum_apply, Pi.single_apply]

/-- **Coordinate expansion**: every `f ∈ C₀(I, β)` is the unconditional sum of its coordinate
vectors `single i (f i)`. -/
theorem hasSum_single (f : C₀(I, β)) : HasSum (fun i ↦ single i (f i)) f := by
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  have hfin : {j | ¬‖f j‖ < ε / 2}.Finite := eventually_cofinite.1 <|
    (by simpa using f.tendsto_cofinite.norm : Tendsto (fun j ↦ ‖f j‖) cofinite (𝓝 0))
      |>.eventually_lt_const (half_pos hε)
  refine ⟨hfin.toFinset, fun s hs ↦ ?_⟩
  rw [dist_eq_norm]
  refine ((norm_le (half_pos hε).le).2 fun j ↦ ?_).trans_lt (half_lt_self hε)
  by_cases hj : j ∈ s
  · simpa [sum_single_apply, hj] using (half_pos hε).le
  · have : ‖f j‖ < ε / 2 := not_not.1 fun h ↦ hj (hs (by simpa using h))
    simpa [sum_single_apply, hj] using this.le

/-- Continuous linear maps out of `C₀(I, β)` agreeing on all coordinate vectors are equal. -/
theorem continuousLinearMap_ext {R M : Type*} [Semiring R] [Module R β] [ContinuousConstSMul R β]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M] [T2Space M]
    {φ ψ : C₀(I, β) →L[R] M} (h : ∀ i b, φ (single i b) = ψ (single i b)) : φ = ψ := by
  ext f
  exact ((hasSum_single f).mapL φ).unique (by simpa only [h] using (hasSum_single f).mapL ψ)

end

/-- **Finite-support density**: the finitely supported families are dense in `C₀(I, β)`. -/
theorem dense_setOf_finite_support : Dense {f : C₀(I, β) | (Function.support f).Finite} := by
  classical
  exact fun f ↦ mem_closure_of_tendsto (hasSum_single f) <| Eventually.of_forall fun s ↦
    s.finite_toSet.subset fun j hj ↦ by
      by_contra h
      exact hj (by simp only [sum_single_apply]; simp [Finset.mem_coe.not.1 h])

end Normed

section Ring

variable {R : Type*} [SeminormedRing R] [DecidableEq I]

/-- **Coordinate expansion in the unit vectors**: every `f ∈ C₀(I, R)` is the unconditional sum
`∑ i, f i • single i 1`. -/
theorem hasSum_smul_single_one (f : C₀(I, R)) : HasSum (fun i ↦ f i • single i (1 : R)) f := by
  simpa only [smul_single_one] using hasSum_single f

/-- The unit vectors `single i 1` span a dense submodule of `C₀(I, R)`. -/
theorem dense_span_single_one :
    Dense (Submodule.span R (Set.range fun i : I ↦ single i (1 : R)) : Set C₀(I, R)) :=
  fun f ↦ mem_closure_of_tendsto (hasSum_smul_single_one f) <| Eventually.of_forall fun _ ↦
    Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Continuous linear maps out of `C₀(I, R)` agreeing on the unit vectors `single i 1` are
equal. -/
theorem continuousLinearMap_ext_single_one {M : Type*} [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [T2Space M] {φ ψ : C₀(I, R) →L[R] M}
    (h : ∀ i, φ (single i 1) = ψ (single i 1)) : φ = ψ :=
  continuousLinearMap_ext fun i r ↦ by rw [← smul_single_one, map_smul, map_smul, h]

end Ring

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
  simpa using (tendsto_zero_iff_norm_tendsto_zero.1 a.tendsto_cofinite).mul_const C

omit [DiscreteTopology I] [CompleteSpace M] in
private theorem norm_tsum_smul_le (a : C₀(I, R)) : ‖∑' i, a i • e i‖ ≤ (⨆ i, ‖e i‖) * ‖a‖ := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg (Real.iSup_nonneg fun _ ↦ norm_nonneg _) (norm_nonneg _)) fun i ↦ ?_
  calc ‖a i • e i‖ ≤ ‖a i‖ * ‖e i‖ := norm_smul_le _ _
    _ ≤ ‖a‖ * ⨆ i, ‖e i‖ := by
        gcongr
        · exact a.norm_coe_le_norm i
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
  ⟨by rintro rfl i; simp, fun h ↦ continuousLinearMap_ext_single_one fun i ↦ by simp [h]⟩

end Lift

end ZeroAtInftyContinuousMap
