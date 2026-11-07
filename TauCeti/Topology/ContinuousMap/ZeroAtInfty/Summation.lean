/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# Summation of ultrametric null families

In a complete ultrametric normed group, a family vanishing at infinity on a discrete index
is unconditionally summable. Summation is a norm-decreasing continuous linear map
`tsumCLM R : C₀(I, E) →L[R] E`, for any continuous scalar action. It is characterised by
sending `single i x` to `x`, commutes with bounded coefficient maps, and is invariant under
reindexing.

For a null family on a product, `curryEquiv` and summation in the inner variable produce a
null family in the outer variable. Summing that family gives the original double sum.
The sup-norm decay in this statement is essential: pointwise decay of a family of null
families does not imply summability in `C₀`.

The construction uses Mathlib's nonarchimedean summability criterion and ultrametric sum
estimate, and the native `C₀` coefficient expansion `hasSum_single`. The bundled map
parallels Mathlib's `lp.tsumCLM`, using null families rather than absolutely summable families.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

variable {I J R E F : Type*} [TopologicalSpace I] [DiscreteTopology I]
  [NormedAddCommGroup E] [IsUltrametricDist E] [CompleteSpace E]

/-- A null family with values in a complete ultrametric normed group is unconditionally
summable. -/
theorem summable (f : C₀(I, E)) : Summable f :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero f.tendsto_cofinite

omit [DiscreteTopology I] [CompleteSpace E] in
/-- The unconditional sum of an ultrametric null family is bounded by its sup norm. -/
theorem norm_tsum_le (f : C₀(I, E)) : ‖∑' i, f i‖ ≤ ‖f‖ :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg f)
    (norm_coe_le_norm f)

variable (R) [Semiring R] [Module R E] [ContinuousConstSMul R E]

/-- Summation of null families in a complete ultrametric normed module, as a continuous
linear map. The scalar ring need not be normed. -/
noncomputable def tsumCLM : C₀(I, E) →L[R] E :=
  let L : C₀(I, E) →ₗ[R] E :=
    { toFun := fun f ↦ ∑' i, f i
      map_add' f g := by
        simp only [FunLike.coe_add, Pi.add_apply]
        exact f.summable.tsum_add g.summable
      map_smul' r f := by
        simp only [FunLike.coe_smul, Pi.smul_apply, RingHom.id_apply]
        exact f.summable.tsum_const_smul r }
  { L with
    cont := AddMonoidHomClass.continuous_of_bound L 1 fun f ↦ by
      simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, one_mul] using norm_tsum_le f }

variable {R}

/-- `tsumCLM` is unconditional summation. -/
theorem tsumCLM_apply (f : C₀(I, E)) : tsumCLM R f = ∑' i, f i := (rfl)

/-- Summation is norm-decreasing, also for empty indices and the zero module. -/
theorem norm_tsumCLM_apply_le (f : C₀(I, E)) : ‖tsumCLM R f‖ ≤ ‖f‖ := by
  simpa only [tsumCLM_apply] using norm_tsum_le f

/-- A uniform bound for summation, suitable for coefficientwise composition via `compLeft`. -/
theorem tsumCLM_bound : ∃ C, ∀ f : C₀(I, E), ‖tsumCLM R f‖ ≤ C * ‖f‖ :=
  ⟨1, fun f ↦ by simpa only [one_mul] using norm_tsumCLM_apply_le (R := R) f⟩

/-- The terms of a null family sum to its image under `tsumCLM`. -/
theorem hasSum_tsumCLM (f : C₀(I, E)) : HasSum (fun i ↦ f i) (tsumCLM R f) := by
  simpa only [tsumCLM_apply] using f.summable.hasSum

/-- Summation sends a coordinate vector to its value. -/
@[simp]
theorem tsumCLM_single [DecidableEq I] (i : I) (x : E) :
    tsumCLM R (single i x) = x := by
  simp [tsumCLM_apply, coe_single]

/-- The summation map is the unique continuous linear map sending each coordinate vector
to its value. -/
theorem eq_tsumCLM_iff [DecidableEq I] (u : C₀(I, E) →L[R] E) :
    u = tsumCLM R ↔ ∀ i x, u (single i x) = x := by
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  exact continuousLinearMap_ext fun i x ↦ by simp [h]

/-- A sum over a finite coordinate truncation is the corresponding finite partial sum. -/
@[simp]
theorem tsumCLM_indicatorCLM (s : Finset I) (f : C₀(I, E)) :
    tsumCLM R (indicatorCLM R (s : Set I) f) = ∑ i ∈ s, f i := by
  classical
  rw [indicatorCLM_finset_apply, map_sum]
  simp

/-- The error of a finite partial sum is bounded by the sup norm of the omitted tail. -/
theorem norm_sum_sub_tsumCLM_le (s : Finset I) (f : C₀(I, E)) :
    ‖(∑ i ∈ s, f i) - tsumCLM R f‖ ≤ ‖indicatorCLM R (s : Set I) f - f‖ := by
  simpa using norm_tsumCLM_apply_le (R := R) (indicatorCLM R (s : Set I) f - f)

variable [NormedAddCommGroup F] [IsUltrametricDist F] [CompleteSpace F]
  [Module R F] [ContinuousConstSMul R F]

/-- Summation commutes with any bounded continuous linear coefficient map. -/
theorem tsumCLM_compLeft (u : E →L[R] F) (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖)
    (f : C₀(I, E)) :
    tsumCLM R (compLeft u hu f) = u (tsumCLM R f) := by
  simpa only [tsumCLM_apply, compLeft_apply] using
    ((hasSum_tsumCLM (R := R) f).mapL u).tsum_eq

section Reindex

variable [TopologicalSpace J] [DiscreteTopology J]

/-- Summation is invariant under reindexing a discrete family by a homeomorphism. -/
@[simp]
theorem tsumCLM_congrLeft (e : I ≃ₜ J) (f : C₀(I, E)) :
    tsumCLM R (congrLeft R E e f) = tsumCLM R f := by
  simpa only [tsumCLM_apply, congrLeft_apply, Homeomorph.coe_toEquiv] using
    e.symm.toEquiv.tsum_eq f

/-- Summing the inner variable of a product null family gives a null family in the outer
variable. The hypothesis controls both indices jointly. -/
theorem tendsto_tsum_cofinite (f : C₀(I × J, E)) :
    Tendsto (fun i ↦ ∑' j, f (i, j)) cofinite (𝓝 0) := by
  simpa only [Function.comp_def, tsumCLM_apply, curryEquiv_apply_apply] using
    ((tsumCLM ℕ).continuous.tendsto' 0 0 (map_zero _)).comp
      (curryEquiv ℕ E f).tendsto_cofinite

/-- Fubini's identity for a null family on a product, expressed using the native model-space
isometry and coefficientwise summation. -/
theorem tsumCLM_curryEquiv (f : C₀(I × J, E)) :
    tsumCLM R (compLeft (tsumCLM R) (tsumCLM_bound (R := R)) (curryEquiv R E f)) =
      tsumCLM R f := by
  simpa only [tsumCLM_apply, compLeft_apply, curryEquiv_apply_apply] using f.summable.tsum_prod.symm

end Reindex

end ZeroAtInftyContinuousMap
