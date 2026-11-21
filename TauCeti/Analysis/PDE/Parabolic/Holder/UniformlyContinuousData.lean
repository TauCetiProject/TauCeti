/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import TauCeti.Analysis.Holder.UniformContinuous
public import TauCeti.Analysis.PDE.Parabolic.Holder.Solvability
import TauCeti.Analysis.Normed.Group.Submodule
import TauCeti.Analysis.PDE.HeatKernel.UniformContinuous
import TauCeti.Analysis.PDE.Parabolic.Holder.InitialTrace

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
* `u(·, 0) = g`, and `u(·, t) → g` uniformly as `t → 0⁺`;
* the rate of this convergence depends on `g` only through its modulus of continuity and its
  supremum: if `g` moves by at most `η` over distances at most `√t`, then
  `|u(x, t) - g(x)| ≤ C (η + t (‖g‖_∞ + ‖f‖_∞))`, with `C` depending only on the dimension, `T`
  and bounds for the coefficients (`exists_abs_euclideanCauchySolutionBUC_sub_le`). So a bounded,
  uniformly equicontinuous family of initial data is attained uniformly in the family
  (`tendstoUniformly_euclideanCauchySolutionBUC_of_uniformEquicontinuous`).

The uniform attainment of the initial datum is where uniform continuity is needed: for merely
bounded continuous data the heat flow does not converge uniformly at `t = 0`. The rate passes to
the limit from the classical rate for `C_b^{2,α}` data
(`exists_abs_sub_le_of_abs_euclideanParabolicOperatorL_le`), since an approximant within `δ` of
`g` moves by at most `η + 2 δ` over the same distances. The interior
regularity of the extended solution for `t > 0`, where it is a classical solution, needs Schauder
estimates at positive times that do not involve the Hölder norm of the datum; it is not proved
here.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4
  (solutions with continuous initial data as limits of solutions with smooth data).
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
    (fun x ↦ by
      rw [euclideanInitialDataCLE_symm_apply_slabMk_zero, ← toBUC_apply, ← Real.norm_eq_abs,
        ← ClosedSubmodule.norm_coe]
      exact norm_coe_le_norm _ x) p
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

/-! ### The rate of attainment of the initial datum -/

section Modulus

variable [DecidableEq ι] (hT : (0 : ℝ) < T)

/-- **The rate of attainment of a uniformly continuous initial datum.** There is a constant `C`,
depending only on the dimension, `T`, `Λ`, `β` and `γ`, with the following property. Let
`0 < α < 1`, let the coefficients `aⁱʲ`, `bⁱ`, `c` lie in `C_b^{α,α/2}(ℝⁿ × [0, T])` with `a`
uniformly elliptic, `|aⁱʲ| ≤ Λ`, `|bⁱ| ≤ β` and `|c| ≤ γ`, and let `u` be the extended solution
of `P u = f`, `u(·, 0) = g` for `|f| ≤ K` and `g ∈ BUC` with `|g| ≤ M`. If `g` moves by at most `η`
over distances at most `√t`, then

`|u(x, t) - g(x)| ≤ C (η + t (M + K))`.

For a nondecreasing modulus of continuity `ω` of `g` this is
`‖u(·, t) - g‖_∞ ≤ C (ω(√t) + t (‖g‖_∞ + ‖f‖_∞))`: the rate depends on `g` only through `ω` and
its supremum, so it is uniform over a bounded family of data with a common modulus. -/
theorem exists_abs_euclideanCauchySolutionBUC_sub_le (Λ β γ : ℝ) :
    ∃ C ≥ 0, ∀ {α : ℝ≥0} (hα₀ : 0 < α) (hα₁ : α < 1)
      {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
      {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
      {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
      (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
        lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) {K M η : ℝ}
      (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
      (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ),
      (∀ p i j, |a i j p| ≤ Λ) → (∀ p i, |b i p| ≤ β) → (∀ p, |c p| ≤ γ) →
      (∀ p, |f p| ≤ K) → (∀ x, |(w : EuclideanSpace ℝ ι →ᵇ ℝ) x| ≤ M) →
      ∀ (x : EuclideanSpace ℝ ι) (t : Icc (0 : ℝ) T), (∀ y z, dist y z ≤ √(t : ℝ) →
        |(w : EuclideanSpace ℝ ι →ᵇ ℝ) y - (w : EuclideanSpace ℝ ι →ᵇ ℝ) z| ≤ η) →
        |euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, w) (slabMk x t) -
          (w : EuclideanSpace ℝ ι →ᵇ ℝ) x| ≤ C * (η + t * (M + K)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_sub_le_of_abs_euclideanParabolicOperatorL_le (ι := ι)
    (ht := hT) Λ β γ
  refine ⟨C, hC0, fun {α} hα₀ hα₁ {a b c} ha {K M η} f w hΛ hβ hγ hf hw x t hη ↦ ?_⟩
  -- Approximate `w` within `δ` by a `C^{2,α}` datum `g`, whose classical solution `U` obeys the
  -- classical rate with `η + 2 δ` and `M + δ`, and let `δ → 0`.
  set A := Real.exp (‖c‖ * T) * (1 + T)
  have hpos : 0 < A + C * (2 + t) + 1 :=
    add_pos_of_nonneg_of_pos (add_nonneg (by positivity)
      (mul_nonneg hC0 (by linarith [t.property.1]))) one_pos
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ > 0, (A + C * (2 + t) + 1) * δ = ε :=
    ⟨ε / (A + C * (2 + t) + 1), div_pos hε hpos, mul_div_cancel₀ ε hpos.ne'⟩
  obtain ⟨g, hg, hu⟩ := exists_ckHolderSpace_approx hα₀ hα₁ hT ha f w hδ
  set U := (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g)
  have hU := hC hα₁.le (K := K) (M := M + δ) (η := η + 2 * δ) U (nonneg_quadraticForm ha) hΛ hβ
    hγ (fun p ↦ by rw [euclideanParabolicOperatorL_euclideanInitialDataCLE_symm_apply]; exact hf p)
    (fun y ↦ by
      rw [euclideanInitialDataCLE_symm_apply_slabMk_zero]
      linarith [abs_sub_abs_le_abs_sub (g y) ((w : EuclideanSpace ℝ ι →ᵇ ℝ) y), hw y,
        abs_sub_comm (g y) ((w : EuclideanSpace ℝ ι →ᵇ ℝ) y), hg y])
    (slabMk x t) (fun y z hyz ↦ by
      rw [euclideanInitialDataCLE_symm_apply_slabMk_zero,
        euclideanInitialDataCLE_symm_apply_slabMk_zero]
      rw [slabTime_slabMk, sub_zero] at hyz
      have h₁ := abs_lt.1 (hg y)
      have h₂ := abs_lt.1 (hg z)
      have h₃ := abs_le.1 (hη y z hyz)
      exact abs_le.2 ⟨by linarith, by linarith⟩)
  rw [space_slabMk, euclideanInitialDataCLE_symm_apply_slabMk_zero, slabTime_slabMk,
    sub_zero] at hU
  calc _ ≤ |euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, w) (slabMk x t) - U (slabMk x t)| +
        |U (slabMk x t) - g x| + |g x - (w : EuclideanSpace ℝ ι →ᵇ ℝ) x| := by
        linarith [abs_sub_le (euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, w) (slabMk x t))
          (U (slabMk x t)) ((w : EuclideanSpace ℝ ι →ᵇ ℝ) x),
          abs_sub_le (U (slabMk x t)) (g x) ((w : EuclideanSpace ℝ ι →ᵇ ℝ) x)]
    _ ≤ A * δ + C * (η + 2 * δ + t * (M + δ + K)) + δ := by
        rw [abs_sub_comm (g x)]
        gcongr
        · exact hu _
        · exact (hg x).le
    _ = C * (η + t * (M + K)) + ε := by rw [← hδε]; ring

/-- **Uniform attainment for an equicontinuous family of initial data.** If the initial data
`gₖ ∈ BUC` are uniformly bounded and uniformly equicontinuous, the extended solutions `uₖ` of
`P uₖ = f`, `uₖ(·, 0) = gₖ` attain them uniformly in the family:
`sup_{k, x} |uₖ(x, t) - gₖ(x)| → 0` as `t → 0⁺`. -/
theorem tendstoUniformly_euclideanCauchySolutionBUC_of_uniformEquicontinuous (hα₀ : 0 < α)
    (hα₁ : α < 1) (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) {κ : Type*}
    (w : κ → uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ)
    (hw : UniformEquicontinuous fun k ↦ ⇑(w k : EuclideanSpace ℝ ι →ᵇ ℝ)) {M : ℝ}
    (hM : ∀ k x, |(w k : EuclideanSpace ℝ ι →ᵇ ℝ) x| ≤ M) :
    TendstoUniformly (fun (t : Icc (0 : ℝ) T) (q : κ × EuclideanSpace ℝ ι) ↦
      euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, w q.1) (slabMk q.2 t))
      (fun q ↦ (w q.1 : EuclideanSpace ℝ ι →ᵇ ℝ) q.2) (𝓝 ⟨0, left_mem_Icc.2 hT.le⟩) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_euclideanCauchySolutionBUC_sub_le (ι := ι) hT
    (∑ i, ∑ j, ‖a i j‖) (∑ i, ‖b i‖) ‖c‖
  -- The Hölder norms of the coefficients and of the forcing bound them pointwise.
  have hΛ : ∀ p i j, |a i j p| ≤ ∑ i, ∑ j, ‖a i j‖ := fun p i j ↦
    ((Real.norm_eq_abs _).symm.trans_le (HolderSpace.norm_apply_le (a i j) p)).trans
      ((Finset.single_le_sum (fun j _ ↦ norm_nonneg (a i j)) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun i ↦ ∑ j, ‖a i j‖) (fun i _ ↦ by positivity)
          (Finset.mem_univ i)))
  have hβ : ∀ p i, |b i p| ≤ ∑ i, ‖b i‖ := fun p i ↦
    ((Real.norm_eq_abs _).symm.trans_le (HolderSpace.norm_apply_le (b i) p)).trans
      (Finset.single_le_sum (fun i _ ↦ norm_nonneg (b i)) (Finset.mem_univ i))
  have hnorm (h : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) (p) : |h p| ≤ ‖h‖ :=
    (Real.norm_eq_abs _).symm.trans_le (HolderSpace.norm_apply_le h p)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  -- Take `η` with `C η < ε / 2`, the scale `δ₁` of the oscillation `η`, and times `t < τ`.
  set R := C * |M + ‖f‖|
  obtain ⟨η, hη, hηε⟩ : ∃ η > 0, C * η < ε / 2 :=
    ⟨ε / (2 * (C + 1)), by positivity, by
      rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) two_pos]
      nlinarith⟩
  obtain ⟨δ₁, hδ₁, hδ₁η⟩ := Metric.uniformEquicontinuous_iff.1 hw η hη
  obtain ⟨τ, hτ, hτδ, hτR⟩ : ∃ τ > 0, τ ≤ δ₁ ^ 2 ∧ R * τ < ε / 2 :=
    ⟨min (δ₁ ^ 2) (ε / (2 * (R + 1))), by positivity, min_le_left _ _,
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)).trans_lt (by
        rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) two_pos]
        nlinarith [abs_nonneg (M + ‖f‖)])⟩
  have hev : ∀ᶠ t : Icc (0 : ℝ) T in 𝓝 ⟨0, left_mem_Icc.2 hT.le⟩, (t : ℝ) < τ :=
    (continuous_subtypeVal.tendsto _).eventually (gt_mem_nhds hτ)
  filter_upwards [hev] with t ht q
  have ht₀ : (0 : ℝ) ≤ t := t.property.1
  have hsδ : √(t : ℝ) < δ₁ := by
    rw [← Real.sqrt_sq hδ₁.le]
    exact Real.sqrt_lt_sqrt ht₀ (ht.trans_le hτδ)
  have key := hC hα₀ hα₁ ha f (w q.1) hΛ hβ (hnorm c) (hnorm f) (hM q.1) q.2 t
    fun y z hyz ↦ by simpa [Real.dist_eq] using (hδ₁η y z (hyz.trans_lt hsδ) q.1).le
  have hR : C * (t * (M + ‖f‖)) ≤ R * τ :=
    calc _ ≤ C * (t * |M + ‖f‖|) := by gcongr; exact le_abs_self _
      _ = R * t := by ring
      _ ≤ R * τ := by gcongr
  rw [Real.dist_eq, abs_sub_comm]
  calc _ ≤ C * (η + t * (M + ‖f‖)) := key
    _ < ε := by linarith

end Modulus

end TauCeti.ParabolicC2HolderSpace
