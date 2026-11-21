/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import TauCeti.Analysis.Holder.UniformContinuous
public import TauCeti.Analysis.PDE.Parabolic.Holder.PositiveTime
public import TauCeti.Analysis.PDE.Parabolic.Holder.Solvability
import TauCeti.Analysis.Normed.Group.Submodule
import TauCeti.Analysis.PDE.HeatKernel.UniformContinuous

/-!
# The parabolic Cauchy problem with bounded uniformly continuous initial data

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `Q = ℝⁿ × [0, T]`, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have coefficients in `C_b^{α,α/2}(Q)`, `0 < α < 1`, with `a` uniformly elliptic. For a forcing
`f ∈ C_b^{α,α/2}(Q)` and an initial datum `g ∈ C_b^{2,α}(ℝⁿ)` the Cauchy problem `P u = f`,
`u(·, 0) = g` has a unique solution in `C_b^{2+α,1+α/2}(Q)`
(`TauCeti.ParabolicC2HolderSpace.euclideanInitialDataCLE`). By the maximum principle this solution
is bounded in the supremum norm by the supremum norms of the data,
`|u(x, t)| ≤ exp (γ t) (sup |g| + t sup |f|)` whenever `c ≤ γ`, `0 ≤ γ`. So the solution map
`(f, g) ↦ u`, viewed as a map into the bounded continuous functions on `Q`, is continuous for the
supremum norm of the initial datum, and it extends by continuity to the closure of `C_b^{2,α}` in
that norm. This closure is the space `BUC(ℝⁿ)` of bounded uniformly continuous functions
(`TauCeti.CkHolderSpace.denseRange_toBUC`).

This file constructs the extended solution operator
`euclideanCauchySolutionBUC : C_b^{α,α/2}(Q) × BUC(ℝⁿ) →L[ℝ] C_b(Q)` and proves the properties
that pass to the limit from smooth data:

* it agrees with the classical solution on `C_b^{2,α}` initial data, and it is the only continuous
  linear map that does;
* the one-sided maximum principle bound `u ≤ exp (γ t) (M + t K)` for `f ≤ K`, `g ≤ M`, hence the
  two-sided bound and the comparison principle;
* `u(·, 0) = g`, and `u(·, t) → g` uniformly as `t → 0⁺`.

The uniform attainment of the initial datum is where uniform continuity is needed: for merely
bounded continuous data the heat flow does not converge uniformly at `t = 0`.

Away from the initial time the extended solution is a classical solution. The Schauder estimate at
positive times (`exists_rpow_mul_norm_restrictL_le_euclideanParabolicOperatorL`) bounds the
order-two norm of a classical solution on `ℝⁿ × [δ, T]` by `‖f‖_{α,par}` and the supremum of its
initial values only, so for `0 < δ < T` the restrictions of the classical solutions to
`ℝⁿ × [δ, T]` extend by continuity as well, to a continuous linear map
`euclideanCauchySolutionBUCRestrictL : C_b^{α,α/2}(Q) × BUC(ℝⁿ) →L[ℝ] C_b^{2+α,1+α/2}(ℝⁿ × [δ, T])`.
It agrees with the restriction of `euclideanCauchySolutionBUC`, solves `P u = f` on
`ℝⁿ × [δ, T]`, and satisfies `δ^(1 + α/2) ‖u‖_{2+α,par;[δ,T]} ≤ C (‖f‖_{α,par} + sup |g|)` with
`C` uniform in `δ`, in the coefficients within given bounds and in the horizon. Composed with the
spatial trace `spatialTraceL` at a time `t ∈ [δ, T]`, it gives `g ↦ u(·, t)` as a bounded map from
`BUC(ℝⁿ)` to `C_b^{2,α}(ℝⁿ)`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4
  (solutions with continuous initial data as limits of solutions with smooth data, and their
  regularity at positive times).
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2, Section 4 (the
  maximum principle behind the supremum bounds).
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set Filter Metric ParabolicSpaceTime BoundedContinuousFunction
open CkHolderSpace (toBUC toBUC_apply denseRange_toBUC)
open scoped NNReal Topology

variable {α : ℝ≥0} {ι : Type*} [Fintype ι] {T : ℝ≥0}

/-! ### The extended solution operator -/

section Extension

/-- The data map `(f, g) ↦ (f, g)` from `C_b^{α,α/2} × C_b^{2,α}` to `C_b^{α,α/2} × BUC`. -/
private def dataMap : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ →ₗ[ℝ]
    HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ :=
  LinearMap.prodMap LinearMap.id toBUC.toLinearMap

@[simp]
private theorem dataMap_apply (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
    CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) : dataMap d = (d.1, toBUC d.2) :=
  rfl

private theorem denseRange_dataMap (hα : α ≤ 1) :
    DenseRange (dataMap (α := α) (ι := ι) (T := T)) := by
  rw [dataMap, LinearMap.coe_prodMap, LinearMap.id_coe, ContinuousLinearMap.coe_coe]
  exact denseRange_id.prodMap (denseRange_toBUC hα)

variable [DecidableEq ι] (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
  (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
  (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
  (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
  (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)

/-- The classical solution `(f, g) ↦ u` of the Cauchy problem with `C_b^{2,α}` initial datum, as a
bounded continuous function on the slab. -/
private def solutionValue :
    HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ →ₗ[ℝ]
        (slab (E := EuclideanSpace ℝ ι) 0 T →ᵇ ℝ) :=
  (valueL.comp
    (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm.toContinuousLinearMap).toLinearMap

variable {a b c}

/-- The degenerate ellipticity required by the maximum principle. -/
private theorem nonneg_quadraticForm (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) (p)
    (ξ : EuclideanSpace ℝ ι) : 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ := by
  obtain ⟨lam, hlam, h⟩ := ha
  exact (mul_nonneg hlam.le (sq_nonneg _)).trans (h p ξ)

/-- The classical solution is bounded at time `0` by the supremum of its initial datum. -/
private theorem abs_euclideanInitialDataCLE_symm_apply_slabMk_zero_le
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) (x : EuclideanSpace ℝ ι) :
    |(euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm d (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩)| ≤
      ‖toBUC d.2‖ := by
  rw [euclideanInitialDataCLE_symm_apply_slabMk_zero, ← toBUC_apply, ← Real.norm_eq_abs,
    ← ClosedSubmodule.norm_coe]
  exact norm_coe_le_norm _ x

/-- The supremum bound for the classical solution: `‖u‖_∞ ≤ exp (‖c‖ T) (1 + T) ‖(f, g)‖`, where
`g` is measured in the supremum norm. -/
private theorem norm_solutionValue_le
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    ‖solutionValue hα₀ hα₁ hT a b c ha d‖ ≤
      Real.exp (‖c‖ * T) * (1 + T) * ‖dataMap d‖ := by
  set u := (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm d
  have hK : ‖d.1‖ ≤ ‖dataMap d‖ := by simp
  have hM : ‖toBUC d.2‖ ≤ ‖dataMap d‖ := by simp
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun p ↦ ?_
  have hp := abs_le_exp_mul_mul_add_mul_of_abs_euclideanParabolicOperatorL_le hα₁.le
    (nonneg_quadraticForm ha)
    (fun p ↦ (Real.le_norm_self _).trans (HolderSpace.norm_apply_le c p))
    (norm_nonneg c) u (K := ‖d.1‖) (M := ‖toBUC d.2‖)
    (fun q ↦ by
      rw [euclideanParabolicOperatorL_euclideanInitialDataCLE_symm_apply]
      exact (Real.norm_eq_abs _).symm.trans_le (HolderSpace.norm_apply_le d.1 q))
    (abs_euclideanInitialDataCLE_symm_apply_slabMk_zero_le hα₀ hα₁ hT ha d) p
  have ht0 : (0 : ℝ) ≤ slabTime p := (slabTime p).property.1
  have htT : (slabTime p : ℝ) ≤ T := (slabTime p).property.2
  have hexp : Real.exp (‖c‖ * (slabTime p - 0)) ≤ Real.exp (‖c‖ * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg c))
  calc ‖solutionValue hα₀ hα₁ hT a b c ha d p‖ = |u p| := Real.norm_eq_abs _
    _ ≤ Real.exp (‖c‖ * (slabTime p - 0)) * (‖toBUC d.2‖ + (slabTime p - 0) * ‖d.1‖) := hp
    _ ≤ Real.exp (‖c‖ * T) * (‖dataMap d‖ + T * ‖dataMap d‖) := by
      refine mul_le_mul hexp ?_
        (add_nonneg (norm_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))) (by positivity)
      have := mul_le_mul (a := (slabTime p : ℝ) - 0) (by linarith) hK (norm_nonneg _) T.coe_nonneg
      linarith
    _ = Real.exp (‖c‖ * T) * (1 + T) * ‖dataMap d‖ := by ring

variable (a b c)

/-- **The solution operator for bounded uniformly continuous initial data.** For `0 < α < 1`,
coefficients `aⁱʲ`, `bⁱ`, `c` in `C_b^{α,α/2}(ℝⁿ × [0, T])` with `a` uniformly elliptic, this is
the continuous linear map `(f, g) ↦ u` from `C_b^{α,α/2}(ℝⁿ × [0, T]) × BUC(ℝⁿ)` to the bounded
continuous functions on the slab that extends the solution operator of the Cauchy problem
`P u = f`, `u(·, 0) = g` from initial data in `C_b^{2,α}(ℝⁿ)`
(`euclideanCauchySolutionBUC_apply_of_ckHolderSpace`). -/
def euclideanCauchySolutionBUC :
    HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ →L[ℝ]
        (slab (E := EuclideanSpace ℝ ι) 0 T →ᵇ ℝ) :=
  (solutionValue hα₀ hα₁ hT a b c ha).extendOfNorm dataMap

variable {a b c}

private theorem euclideanCauchySolutionBUC_dataMap
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (dataMap d) =
      valueL ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm d) :=
  LinearMap.extendOfNorm_eq (denseRange_dataMap hα₁.le)
    ⟨_, norm_solutionValue_le hα₀ hα₁ hT ha⟩ d

/-- **Agreement with the classical solution.** On an initial datum `w` that is a bounded
`C^{2,α}` function `g`, the extended solution is the solution in `C_b^{2+α,1+α/2}` of `P u = f`,
`u(·, 0) = g`. -/
theorem euclideanCauchySolutionBUC_apply_of_ckHolderSpace
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ)
    (g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ)
    (hw : ∀ x, (w : EuclideanSpace ℝ ι →ᵇ ℝ) x = g x) :
    euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, w) =
      valueL ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g)) := by
  have hd : (f, w) = dataMap (f, g) :=
    Prod.ext rfl (Subtype.ext <| BoundedContinuousFunction.ext fun x ↦ by
      rw [hw, dataMap_apply, toBUC_apply])
  rw [hd, euclideanCauchySolutionBUC_dataMap]

/-- The extension agrees with the classical solution on the image `toBUC g` of a bounded `C^{2,α}`
initial datum `g`. -/
@[simp]
theorem euclideanCauchySolutionBUC_toBUC
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, toBUC g) =
      valueL ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g)) :=
  euclideanCauchySolutionBUC_dataMap hα₀ hα₁ hT ha (f, g)

/-- **Uniqueness of the extension.** A continuous linear map on `C_b^{α,α/2} × BUC` that agrees
with the classical solution operator on `C_b^{2,α}` initial data is `euclideanCauchySolutionBUC`. -/
theorem eq_euclideanCauchySolutionBUC
    (L : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ →L[ℝ]
        (slab (E := EuclideanSpace ℝ ι) 0 T →ᵇ ℝ))
    (hL : ∀ (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
      (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ)
      (g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ),
      (∀ x, (w : EuclideanSpace ℝ ι →ᵇ ℝ) x = g x) →
        L (f, w) = valueL ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g))) :
    L = euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha :=
  (LinearMap.extendOfNorm_unique (denseRange_dataMap hα₁.le) _
    (norm_solutionValue_le hα₀ hα₁ hT ha) L <| LinearMap.ext fun d ↦
      hL d.1 (toBUC d.2) d.2 (toBUC_apply d.2)).symm

/-- **The supremum bound for the extended solution.** The extended solution operator has operator
norm at most `exp (‖c‖ T) (1 + T)`. -/
theorem norm_euclideanCauchySolutionBUC_le :
    ‖euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha‖ ≤ Real.exp (‖c‖ * T) * (1 + T) :=
  LinearMap.opNorm_extendOfNorm_le (denseRange_dataMap hα₁.le) (by positivity)
    (norm_solutionValue_le hα₀ hα₁ hT ha)

/-- **The supremum bound for the extended solution.**
`‖u‖_∞ ≤ exp (‖c‖ T) (1 + T) max (‖f‖, ‖g‖_∞)`. -/
theorem norm_euclideanCauchySolutionBUC_apply_le
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) :
    ‖euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha d‖ ≤
      Real.exp (‖c‖ * T) * (1 + T) * ‖d‖ :=
  LinearMap.norm_extendOfNorm_apply_le (denseRange_dataMap hα₁.le) _
    (norm_solutionValue_le hα₀ hα₁ hT ha) d

/-- Every initial datum in `BUC` is approximated, within any `δ > 0`, by a bounded `C^{2,α}`
function, and the extended solutions are then within `exp (‖c‖ T) (1 + T) δ` of each other. -/
private theorem exists_ckHolderSpace_approx
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ,
      (∀ x, |(w : EuclideanSpace ℝ ι →ᵇ ℝ) x - g x| < δ) ∧
      ∀ p, |euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, w) p -
          (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g) p| ≤
        Real.exp (‖c‖ * T) * (1 + T) * δ := by
  obtain ⟨_, ⟨g, rfl⟩, hg⟩ := Metric.mem_closure_iff.1 (denseRange_toBUC hα₁.le w) δ hδ
  rw [dist_eq_norm] at hg
  refine ⟨g, fun x ↦ ?_, fun p ↦ ?_⟩
  · rw [← toBUC_apply, ← Real.norm_eq_abs, ← _root_.sub_apply]
    exact (norm_coe_le_norm _ x).trans_lt hg
  · have hsub : euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, w) -
        valueL ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g)) =
          euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (0, w - toBUC g) := by
      rw [← euclideanCauchySolutionBUC_toBUC, ← map_sub, Prod.mk_sub_mk, sub_self]
    have hn := norm_euclideanCauchySolutionBUC_apply_le hα₀ hα₁ hT (b := b) (c := c) ha
      (0, w - toBUC g)
    rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] at hn
    calc _ = ‖(euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, w) -
          valueL ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g))) p‖ := by
          rw [Real.norm_eq_abs, _root_.sub_apply, valueL_apply]
      _ ≤ _ := by
        rw [hsub]
        exact (norm_coe_le_norm _ p).trans
          (hn.trans (mul_le_mul_of_nonneg_left hg.le (by positivity)))

/-- **The maximum principle for the extended solution.** Let `c ≤ γ` with `0 ≤ γ`. If the forcing
satisfies `f ≤ K` and the initial datum `g ≤ M`, where `0 ≤ M` and `0 ≤ K`, then the extended
solution satisfies `u(x, t) ≤ exp (γ t) (M + t K)`. -/
theorem euclideanCauchySolutionBUC_apply_le {γ M K : ℝ} (hc : ∀ p, c p ≤ γ) (hγ : 0 ≤ γ)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) (hf : ∀ p, f p ≤ K)
    (hw : ∀ x, (w : EuclideanSpace ℝ ι →ᵇ ℝ) x ≤ M) (p : slab (E := EuclideanSpace ℝ ι) 0 T) :
    euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, w) p ≤
      Real.exp (γ * slabTime p) * (M + slabTime p * K) := by
  obtain ⟨A, hA, hAdef⟩ : ∃ A, 0 ≤ A ∧ A = Real.exp (‖c‖ * T) * (1 + T) := ⟨_, by positivity, rfl⟩
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  -- Approximate `w` within `δ` by a `C^{2,α}` datum `g` and compare with its classical solution.
  obtain ⟨δ, hδ, hεδ⟩ : ∃ δ, 0 < δ ∧ (Real.exp (γ * slabTime p) + A) * δ = ε :=
    ⟨ε / (Real.exp (γ * slabTime p) + A), by positivity, mul_div_cancel₀ ε (by positivity)⟩
  obtain ⟨g, hg, hu⟩ := exists_ckHolderSpace_approx hα₀ hα₁ hT ha f w hδ
  rw [← hAdef] at hu
  have hcl := le_exp_mul_mul_add_mul_of_euclideanParabolicOperatorL_le hα₁.le
    (nonneg_quadraticForm ha) hc hγ (M := M + δ) (K := K) (by positivity) hK
    ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g))
    (fun q ↦ by rw [euclideanParabolicOperatorL_euclideanInitialDataCLE_symm_apply]; exact hf q)
    (fun x ↦ by
      rw [euclideanInitialDataCLE_symm_apply_slabMk_zero]
      linarith [hw x, (abs_lt.1 (hg x)).1]) p
  rw [sub_zero] at hcl
  have hup := (abs_le.1 (hu p)).2
  calc _ ≤ (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g) p + A * δ := by
        rw [valueL_apply] at hup; exact sub_le_iff_le_add'.1 hup
    _ ≤ Real.exp (γ * slabTime p) * (M + δ + slabTime p * K) + A * δ := by gcongr
    _ = _ := by linear_combination hεδ

/-- **The two-sided maximum principle bound.** If `c ≤ γ` with `0 ≤ γ`, `|f| ≤ K` and `|g| ≤ M`,
then the extended solution satisfies `|u(x, t)| ≤ exp (γ t) (M + t K)`. -/
theorem abs_euclideanCauchySolutionBUC_apply_le {γ M K : ℝ} (hc : ∀ p, c p ≤ γ) (hγ : 0 ≤ γ)
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) (hf : ∀ p, |f p| ≤ K)
    (hw : ∀ x, |(w : EuclideanSpace ℝ ι →ᵇ ℝ) x| ≤ M) (p : slab (E := EuclideanSpace ℝ ι) 0 T) :
    |euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, w) p| ≤
      Real.exp (γ * slabTime p) * (M + slabTime p * K) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hw 0)
  have hK : 0 ≤ K := (abs_nonneg _).trans (hf p)
  have hneg := euclideanCauchySolutionBUC_apply_le hα₀ hα₁ hT (b := b) ha hc hγ hM hK (-f) (-w)
    (fun q ↦ by rw [HolderSpace.neg_apply]; exact neg_le.1 (abs_le.1 (hf q)).1)
    (fun x ↦ by simpa using neg_le.1 (abs_le.1 (hw x)).1) p
  rw [← Prod.neg_mk, map_neg, FunLike.coe_neg, Pi.neg_apply] at hneg
  exact abs_le.2 ⟨neg_le.1 hneg, euclideanCauchySolutionBUC_apply_le hα₀ hα₁ hT ha hc hγ hM hK
    f w (fun q ↦ (abs_le.1 (hf q)).2) (fun x ↦ (abs_le.1 (hw x)).2) p⟩

/-- **The comparison principle for the extended solution.** Ordered forcings and ordered initial
data give ordered extended solutions. -/
theorem euclideanCauchySolutionBUC_apply_le_apply
    {f f' : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    {w w' : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ} (hf : ∀ p, f p ≤ f' p)
    (hw : ∀ x, (w : EuclideanSpace ℝ ι →ᵇ ℝ) x ≤ (w' : EuclideanSpace ℝ ι →ᵇ ℝ) x)
    (p : slab (E := EuclideanSpace ℝ ι) 0 T) :
    euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, w) p ≤
      euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f', w') p := by
  have h := euclideanCauchySolutionBUC_apply_le hα₀ hα₁ hT (b := b) ha
    (fun q ↦ (Real.le_norm_self _).trans (HolderSpace.norm_apply_le c q))
    (norm_nonneg c) le_rfl le_rfl (f - f') (w - w')
    (fun q ↦ by rw [HolderSpace.sub_apply]; linarith [hf q])
    (fun x ↦ by simpa using hw x) p
  rw [← Prod.mk_sub_mk, map_sub, _root_.sub_apply] at h
  linarith

/-- **The initial condition.** The extended solution takes the initial datum at `t = 0`. -/
@[simp]
theorem euclideanCauchySolutionBUC_apply_slabMk_zero
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) (x : EuclideanSpace ℝ ι) :
    euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, w) (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩) =
      (w : EuclideanSpace ℝ ι →ᵇ ℝ) x := by
  refine (denseRange_dataMap hα₁.le).induction_on
    (p := fun d ↦ euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha d
      (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩) = (d.2 : EuclideanSpace ℝ ι →ᵇ ℝ) x) (f, w) ?_
    fun d ↦ ?_
  · exact isClosed_eq ((continuous_eval_const _).comp
      (euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha).continuous)
      ((continuous_eval_const x).comp (continuous_subtypeVal.comp continuous_snd))
  · simp

/-- **Uniform attainment of the initial datum.** As `t → 0⁺`, the extended solution converges to
the initial datum uniformly on `ℝⁿ`: `sup_x |u(x, t) - g(x)| → 0`. -/
theorem tendstoUniformly_euclideanCauchySolutionBUC
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) :
    TendstoUniformly (fun (t : Icc (0 : ℝ) T) (x : EuclideanSpace ℝ ι) ↦
      euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, w) (slabMk x t))
      (fun x ↦ (w : EuclideanSpace ℝ ι →ᵇ ℝ) x) (𝓝 ⟨0, left_mem_Icc.2 hT.le⟩) := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨A, hA, hAdef⟩ : ∃ A, 0 ≤ A ∧ A = Real.exp (‖c‖ * T) * (1 + T) := ⟨_, by positivity, rfl⟩
  -- Approximate `w` within `δ` by a `C^{2,α}` datum `g`; the classical solution `u` with datum `g`
  -- is Lipschitz in time, uniformly in space, with the `C^{α,α/2}` norm of `∂ₜu` as constant.
  obtain ⟨δ, hδ, hAδ⟩ : ∃ δ, 0 < δ ∧ (A + 1) * δ = ε / 2 :=
    ⟨ε / (2 * (A + 1)), by positivity, by field_simp⟩
  obtain ⟨g, hg, hu⟩ := exists_ckHolderSpace_approx hα₀ hα₁ hT ha f w hδ
  rw [← hAdef] at hu
  set u := (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g)
  obtain ⟨τ, hτ, hDτ⟩ : ∃ τ, 0 < τ ∧ ‖timeDerivL u‖ * τ ≤ ε / 2 :=
    ⟨ε / (2 * (‖timeDerivL u‖ + 1)), by positivity, by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
      nlinarith [norm_nonneg (timeDerivL u)]⟩
  have hev : ∀ᶠ t : Icc (0 : ℝ) T in 𝓝 ⟨0, left_mem_Icc.2 hT.le⟩, (t : ℝ) < τ :=
    (continuous_subtypeVal.tendsto _).eventually (gt_mem_nhds hτ)
  filter_upwards [hev] with t ht x
  have h1 := abs_le.1 (hu (slabMk x t))
  have h2 := abs_lt.1 (hg x)
  have h3 := u.norm_apply_slabMk_sub_le x t ⟨0, left_mem_Icc.2 hT.le⟩
  rw [euclideanInitialDataCLE_symm_apply_slabMk_zero, Real.norm_eq_abs, sub_zero,
    abs_of_nonneg t.property.1] at h3
  have hDt : ‖timeDerivL u‖ * t ≤ ε / 2 :=
    (mul_le_mul_of_nonneg_left ht.le (norm_nonneg _)).trans hDτ
  have h3' := abs_le.1 (h3.trans hDt)
  rw [dist_eq_norm, Real.norm_eq_abs, abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3'.1, h3'.2]

end Extension

/-! ### Regularity at positive times -/

section PositiveTime

variable [DecidableEq ι]

/-- The positive-time estimate for the classical solution in terms of its data: with `u` the
solution of `P u = f`, `u(·, 0) = g` for `g ∈ C_b^{2,α}`,
`δ^(1 + α/2) ‖u‖_{2+α,par;[δ,T]} ≤ C (‖f‖_{α,par} + sup |g|)`, uniformly over coefficients with
ellipticity constant `λ` and Hölder norms at most `K`, and horizons at most `T₀`. -/
private theorem exists_rpow_mul_norm_restrictL_euclideanInitialDataCLE_symm_le (hα₀ : 0 < α)
    (hα₁ : α < 1) {lam : ℝ} (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (hl : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
          CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) {δ : ℝ} (hδ : 0 < δ) (hδT : δ < T),
          δ ^ (1 + (α : ℝ) / 2) * ‖restrictL hδ.le le_rfl hδT
            ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ⟨lam, hlam, hl⟩).symm d)‖ ≤
            C * (‖d.1‖ + ‖toBUC d.2‖) := by
  obtain ⟨C, hC, hest⟩ := exists_rpow_mul_norm_restrictL_le_euclideanParabolicOperatorL (ι := ι)
    hα₀ hα₁ (Lam := ∑ _i : ι, ∑ _j : ι, (K : ℝ)) hlam K T₀
  refine ⟨C, hC, ?_⟩
  intro T hT hTT₀ a b c hl hak hbk hck d δ hδ hδT
  have h := hest T hT hTT₀ a b c hl (toQuadraticForm'_le_of_forall_norm_le hak) hak hbk hck
    ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ⟨lam, hlam, hl⟩).symm d) (M := ‖toBUC d.2‖)
    (abs_euclideanInitialDataCLE_symm_apply_slabMk_zero_le hα₀ hα₁ hT ⟨lam, hlam, hl⟩ d) hδ hδT
  -- Name the restriction, so that unification does not unfold the order-two norm.
  obtain ⟨r, hr⟩ : ∃ r, restrictL hδ.le le_rfl hδT
      ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ⟨lam, hlam, hl⟩).symm d) = r := ⟨_, rfl⟩
  rw [hr, euclideanParabolicOperatorL_euclideanInitialDataCLE_symm_apply] at h
  rwa [hr]

variable (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
  (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
  (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
  (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
  (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
  {δ : ℝ} (hδ : 0 < δ) (hδT : δ < T)

/-- The classical solution `(f, g) ↦ u` with `C_b^{2,α}` initial datum, restricted to
`ℝⁿ × [δ, T]`. -/
private def solutionRestrict :
    HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ →ₗ[ℝ]
        ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hδT :=
  ((restrictL hδ.le le_rfl hδT).comp
    (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm.toContinuousLinearMap).toLinearMap

variable {a b c}

private theorem solutionRestrict_apply
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    solutionRestrict hα₀ hα₁ hT a b c ha hδ hδT d =
      restrictL hδ.le le_rfl hδT ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm d) :=
  (rfl)

/-- The restricted classical solution is bounded by the supremum norm of the initial datum, with a
constant that blows up as `δ → 0`. -/
private theorem exists_norm_solutionRestrict_le :
    ∃ C, ∀ d, ‖solutionRestrict hα₀ hα₁ hT a b c ha hδ hδT d‖ ≤ C * ‖dataMap d‖ := by
  obtain ⟨lam, hlam, hl⟩ := ha
  obtain ⟨K, hak, hbk, hck⟩ := exists_coeff_norm_le a b c
  obtain ⟨C, hC, hest⟩ := exists_rpow_mul_norm_restrictL_euclideanInitialDataCLE_symm_le
    (ι := ι) hα₀ hα₁ hlam K T
  have hδ' : 0 < δ ^ (1 + (α : ℝ) / 2) := Real.rpow_pos_of_pos hδ _
  refine ⟨2 * C / δ ^ (1 + (α : ℝ) / 2), fun d ↦ ?_⟩
  have h := hest T hT le_rfl a b c hl hak hbk hck d hδ hδT
  have h₁ : ‖d.1‖ ≤ ‖dataMap d‖ := by simp
  have h₂ : ‖toBUC d.2‖ ≤ ‖dataMap d‖ := by simp
  rw [solutionRestrict_apply, div_mul_eq_mul_div, le_div_iff₀ hδ', mul_comm]
  nlinarith

variable (a b c)

/-- **The solution for uniformly continuous initial data at positive times.** For `0 < α < 1`,
coefficients `aⁱʲ`, `bⁱ`, `c` in `C_b^{α,α/2}(ℝⁿ × [0, T])` with `a` uniformly elliptic, and
`0 < δ < T`, this is the continuous linear map `(f, g) ↦ u|_{[δ, T]}` from
`C_b^{α,α/2}(ℝⁿ × [0, T]) × BUC(ℝⁿ)` to the order-two space `C_b^{2+α,1+α/2}(ℝⁿ × [δ, T])`,
where `u = euclideanCauchySolutionBUC (f, g)` solves `P u = f`, `u(·, 0) = g`
(`euclideanCauchySolutionBUCRestrictL_apply`). So the restriction of `u` to `ℝⁿ × [δ, T]` is an
order-two parabolic Hölder map, and `u` is a classical solution at positive times
(`euclideanParabolicOperatorL_euclideanCauchySolutionBUCRestrictL`). -/
def euclideanCauchySolutionBUCRestrictL :
    HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ →L[ℝ]
        ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hδT :=
  (solutionRestrict hα₀ hα₁ hT a b c ha hδ hδT).extendOfNorm dataMap

variable {a b c}

private theorem euclideanCauchySolutionBUCRestrictL_dataMap
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    euclideanCauchySolutionBUCRestrictL hα₀ hα₁ hT a b c ha hδ hδT (dataMap d) =
      restrictL hδ.le le_rfl hδT ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm d) :=
  LinearMap.extendOfNorm_eq (denseRange_dataMap hα₁.le)
    (exists_norm_solutionRestrict_le hα₀ hα₁ hT ha hδ hδT) d

/-- **Agreement with the classical solution.** On a bounded `C^{2,α}` initial datum `g`, the
solution at positive times is the restriction to `ℝⁿ × [δ, T]` of the solution in
`C_b^{2+α,1+α/2}(ℝⁿ × [0, T])` of `P u = f`, `u(·, 0) = g`. -/
@[simp]
theorem euclideanCauchySolutionBUCRestrictL_toBUC
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    euclideanCauchySolutionBUCRestrictL hα₀ hα₁ hT a b c ha hδ hδT (f, toBUC g) =
      restrictL hδ.le le_rfl hδT ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g)) :=
  euclideanCauchySolutionBUCRestrictL_dataMap hα₀ hα₁ hT ha hδ hδT (f, g)

/-- **The solution at positive times is the restriction of the extended solution.** At every point
of `ℝⁿ × [δ, T]`, `euclideanCauchySolutionBUCRestrictL` takes the value of
`euclideanCauchySolutionBUC`. -/
@[simp]
theorem euclideanCauchySolutionBUCRestrictL_apply
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ)
    (p : slab (E := EuclideanSpace ℝ ι) δ T) :
    euclideanCauchySolutionBUCRestrictL hα₀ hα₁ hT a b c ha hδ hδT d p =
      euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha d
        (inclusion (slab_subset_slab hδ.le le_rfl) p) := by
  refine (denseRange_dataMap hα₁.le).induction_on d ?_ fun d ↦ ?_
  · exact isClosed_eq ((continuous_eval_const p).comp (valueL.continuous.comp
      (euclideanCauchySolutionBUCRestrictL hα₀ hα₁ hT a b c ha hδ hδT).continuous))
      ((continuous_eval_const _).comp (euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha).continuous)
  · rw [euclideanCauchySolutionBUCRestrictL_dataMap, euclideanCauchySolutionBUC_dataMap,
      restrictL_apply, valueL_apply]

/-- **The equation at positive times.** On `ℝⁿ × [δ, T]` the solution is a classical solution of
`P u = f`: the operator with the coefficients restricted to `ℝⁿ × [δ, T]` maps it to the
restriction of the forcing. -/
theorem euclideanParabolicOperatorL_euclideanCauchySolutionBUCRestrictL
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) :
    euclideanParabolicOperatorL hα₁.le
        (fun i j ↦ HolderSpace.compLipschitzL _
          (LipschitzWith.inclusion (slab_subset_slab hδ.le le_rfl)) (a i j))
        (fun i ↦ HolderSpace.compLipschitzL _
          (LipschitzWith.inclusion (slab_subset_slab hδ.le le_rfl)) (b i))
        (HolderSpace.compLipschitzL _ (LipschitzWith.inclusion (slab_subset_slab hδ.le le_rfl)) c)
        (euclideanCauchySolutionBUCRestrictL hα₀ hα₁ hT a b c ha hδ hδT d) =
      HolderSpace.compLipschitzL _ (LipschitzWith.inclusion (slab_subset_slab hδ.le le_rfl))
        d.1 := by
  refine (denseRange_dataMap hα₁.le).induction_on d ?_ fun d ↦ ?_
  · exact isClosed_eq ((ContinuousLinearMap.continuous _).comp
      (euclideanCauchySolutionBUCRestrictL hα₀ hα₁ hT a b c ha hδ hδT).continuous)
      ((ContinuousLinearMap.continuous _).comp continuous_fst)
  · rw [euclideanCauchySolutionBUCRestrictL_dataMap, euclideanParabolicOperatorL_restrictL,
      euclideanParabolicOperatorL_euclideanInitialDataCLE_symm_apply, dataMap_apply]

/-- **The interior estimate at positive times.** For `0 < α < 1`, an ellipticity constant `λ > 0`,
a bound `K` on the Hölder norms of the coefficients and a bound `T₀` on the horizon, there is a
constant `C` such that on `ℝⁿ × [0, T]`, `T ≤ T₀`, the solution `u` of `P u = f`, `u(·, 0) = g`
for `g ∈ BUC(ℝⁿ)` satisfies, for every `0 < δ < T`,

`δ^(1 + α/2) ‖u‖_{2+α,par;[δ,T]} ≤ C (‖f‖_{α,par} + sup |g|)`.

The weight `δ^(1 + α/2)` is the parabolic scaling of the top-order Hölder seminorms; only the
supremum of the initial datum enters. -/
theorem exists_rpow_mul_norm_euclideanCauchySolutionBUCRestrictL_le {lam : ℝ} (hlam : 0 < lam)
    (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (hl : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
          (g : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) {δ : ℝ} (hδ : 0 < δ)
          (hδT : δ < T),
          δ ^ (1 + (α : ℝ) / 2) *
              ‖euclideanCauchySolutionBUCRestrictL hα₀ hα₁ hT a b c ⟨lam, hlam, hl⟩ hδ hδT
                (f, g)‖ ≤ C * (‖f‖ + ‖g‖) := by
  obtain ⟨C, hC, hest⟩ := exists_rpow_mul_norm_restrictL_euclideanInitialDataCLE_symm_le
    (ι := ι) hα₀ hα₁ hlam K T₀
  refine ⟨C, hC, ?_⟩
  intro T hT hTT₀ a b c hl hak hbk hck f g δ hδ hδT
  -- The estimate holds on the dense set of smooth data, and both sides are continuous.
  refine (denseRange_dataMap hα₁.le).induction_on (p := fun d ↦ δ ^ (1 + (α : ℝ) / 2) *
      ‖euclideanCauchySolutionBUCRestrictL hα₀ hα₁ hT a b c ⟨lam, hlam, hl⟩ hδ hδT d‖ ≤
        C * (‖d.1‖ + ‖d.2‖)) (f, g) ?_ fun d ↦ ?_
  · exact isClosed_le (continuous_const.mul (continuous_norm.comp
      (euclideanCauchySolutionBUCRestrictL hα₀ hα₁ hT a b c _ hδ hδT).continuous))
      (continuous_const.mul ((continuous_norm.comp continuous_fst).add
        (continuous_norm.comp continuous_snd)))
  · rw [euclideanCauchySolutionBUCRestrictL_dataMap, dataMap_apply]
    exact hest T hT hTT₀ a b c hl hak hbk hck d hδ hδT

end PositiveTime

end TauCeti.ParabolicC2HolderSpace
