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

/-!
# Parabolic Cauchy and terminal-value problems with bounded uniformly continuous data

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
* it is within `exp (‖c‖ T) (1 + T) δ` of the classical solution whose `C_b^{2,α}` datum is
  uniformly within `δ` of `g`;
* the one-sided maximum principle bound `u ≤ exp (γ t) (M + t K)` for `f ≤ K`, `g ≤ M`, hence the
  two-sided bound and the comparison principle;
* `u(·, 0) = g`, and `u(·, t) → g` uniformly as `t → 0⁺`;
* any bounded solution that is classical for `0 < t < T` is the extended solution: a bounded
  function `v` on `[0, T] × ℝⁿ`, continuous there, `C²` in space and differentiable in time for
  `0 < t < T`, with `P v = f` there and `v(·, 0) = g`, is the extended solution
  (`eq_euclideanCauchySolutionBUC_apply_of_deriv_sub_eq`). More precisely, bounded classical
  subsolutions lie below it and supersolutions above it
  (`le_euclideanCauchySolutionBUC_apply_of_deriv_sub_le`,
  `euclideanCauchySolutionBUC_apply_le_of_le_deriv_sub`).

The uniform attainment of the initial datum is where uniform continuity is needed: for merely
bounded continuous data the heat flow does not converge uniformly at `t = 0`.

Time reversal `R (x, t) = (x, T - t)` transports all of this to the terminal-value problem
`∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u = f`, `u(·, T) = g` with `g ∈ BUC(ℝⁿ)`. The operator
`euclideanTerminalSolutionBUC : C_b^{α,α/2}(Q) × BUC(ℝⁿ) →L[ℝ] C_b(Q)` sends `(f, g)` to `v ∘ R`,
where `v` is the extended solution of the Cauchy problem with the reversed coefficients `a ∘ R`,
`b ∘ R`, `c ∘ R` and data `(-f ∘ R, g)`, since `u ↦ u ∘ R` turns `∂ₜu + L u = f` into
`∂ₜv - L_R v = -f ∘ R`. It agrees with every classical solution in `C_b^{2+α,1+α/2}` of the
terminal-value problem and is the only continuous linear map that does; it satisfies the maximum
principle `u(x, t) ≤ exp (γ (T - t)) (M + (T - t) K)` for `c ≤ γ`, `f ≥ -K`, `g ≤ M`, and the
comparison principle; and `u(·, T) = g`, with `u(·, t) → g` uniformly as `t → T⁻`. The interior
regularity of the extended solution for `t > 0`, where it is a classical solution, needs Schauder
estimates at positive times that do not involve the Hölder norm of the datum. It is proved in
`TauCeti.Analysis.PDE.Parabolic.Holder.PositiveTime`
(`euclideanCauchySolutionBUCRestrictL`, `euclideanCauchySolutionBUCRestrictL_apply` and
`exists_rpow_mul_norm_euclideanCauchySolutionBUCRestrictL_apply_le`). Uniqueness needs no such
estimate. If `g` is approximated within `δ` by a `C_b^{2,α}` datum,
the whole-space maximum principle bounds `v` minus the classical solution with that datum by
`exp (‖c‖ t) δ`. That classical solution is within a multiple of `δ` of the extended solution, and
`δ` is arbitrary.

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

/-- The data map `(f, g) ↦ (f, g)` from `C_b^{α,α/2} × C_b^{2,α}` to `C_b^{α,α/2} × BUC`, along
which `euclideanCauchySolutionBUC` extends the classical solution operator. -/
def euclideanCauchyDataToBUC : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ →ₗ[ℝ]
    HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ :=
  LinearMap.prodMap LinearMap.id toBUC.toLinearMap

@[simp]
theorem euclideanCauchyDataToBUC_apply
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    euclideanCauchyDataToBUC d = (d.1, toBUC d.2) :=
  (rfl)

/-- The data map has dense range, since `C_b^{2,α}` is dense in `BUC`. -/
theorem denseRange_euclideanCauchyDataToBUC (hα : α ≤ 1) :
    DenseRange (euclideanCauchyDataToBUC (α := α) (ι := ι) (T := T)) := by
  rw [euclideanCauchyDataToBUC, LinearMap.coe_prodMap, LinearMap.id_coe,
    ContinuousLinearMap.coe_coe]
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
      Real.exp (‖c‖ * T) * (1 + T) * ‖euclideanCauchyDataToBUC d‖ := by
  set u := (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm d
  have hK : ‖d.1‖ ≤ ‖euclideanCauchyDataToBUC d‖ := by simp
  have hM : ‖toBUC d.2‖ ≤ ‖euclideanCauchyDataToBUC d‖ := by simp
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
    _ ≤ Real.exp (‖c‖ * T) * (‖euclideanCauchyDataToBUC d‖ + T * ‖euclideanCauchyDataToBUC d‖) := by
      refine mul_le_mul hexp ?_
        (add_nonneg (norm_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))) (by positivity)
      have := mul_le_mul (a := (slabTime p : ℝ) - 0) (by linarith) hK (norm_nonneg _) T.coe_nonneg
      linarith
    _ = Real.exp (‖c‖ * T) * (1 + T) * ‖euclideanCauchyDataToBUC d‖ := by ring

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
  (solutionValue hα₀ hα₁ hT a b c ha).extendOfNorm euclideanCauchyDataToBUC

variable {a b c}

private theorem euclideanCauchySolutionBUC_euclideanCauchyDataToBUC
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (euclideanCauchyDataToBUC d) =
      valueL ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm d) :=
  LinearMap.extendOfNorm_eq (denseRange_euclideanCauchyDataToBUC hα₁.le)
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
  have hd : (f, w) = euclideanCauchyDataToBUC (f, g) :=
    Prod.ext rfl (Subtype.ext <| BoundedContinuousFunction.ext fun x ↦ by
      rw [hw, euclideanCauchyDataToBUC_apply, toBUC_apply])
  rw [hd, euclideanCauchySolutionBUC_euclideanCauchyDataToBUC]

/-- The extension agrees with the classical solution on the image `toBUC g` of a bounded `C^{2,α}`
initial datum `g`. -/
@[simp]
theorem euclideanCauchySolutionBUC_toBUC
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, toBUC g) =
      valueL ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g)) :=
  euclideanCauchySolutionBUC_euclideanCauchyDataToBUC hα₀ hα₁ hT ha (f, g)

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
  (LinearMap.extendOfNorm_unique (denseRange_euclideanCauchyDataToBUC hα₁.le) _
    (norm_solutionValue_le hα₀ hα₁ hT ha) L <| LinearMap.ext fun d ↦
      hL d.1 (toBUC d.2) d.2 (toBUC_apply d.2)).symm

/-- **The supremum bound for the extended solution.** The extended solution operator has operator
norm at most `exp (‖c‖ T) (1 + T)`. -/
theorem norm_euclideanCauchySolutionBUC_le :
    ‖euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha‖ ≤ Real.exp (‖c‖ * T) * (1 + T) :=
  LinearMap.opNorm_extendOfNorm_le (denseRange_euclideanCauchyDataToBUC hα₁.le) (by positivity)
    (norm_solutionValue_le hα₀ hα₁ hT ha)

/-- **The supremum bound for the extended solution.**
`‖u‖_∞ ≤ exp (‖c‖ T) (1 + T) max (‖f‖, ‖g‖_∞)`. -/
theorem norm_euclideanCauchySolutionBUC_apply_le
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) :
    ‖euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha d‖ ≤
      Real.exp (‖c‖ * T) * (1 + T) * ‖d‖ :=
  LinearMap.norm_extendOfNorm_apply_le (denseRange_euclideanCauchyDataToBUC hα₁.le) _
    (norm_solutionValue_le hα₀ hα₁ hT ha) d

/-- **Comparison with a classical solution.** If the bounded `C^{2,α}` function `g` is uniformly
within `δ` of the initial datum `w`, then the extended solution with data `(f, w)` is uniformly
within `exp (‖c‖ T) (1 + T) δ` of the classical solution with data `(f, g)`. -/
theorem abs_euclideanCauchySolutionBUC_apply_sub_le
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ)
    (g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) {δ : ℝ}
    (hg : ∀ x, |(w : EuclideanSpace ℝ ι →ᵇ ℝ) x - g x| ≤ δ)
    (p : slab (E := EuclideanSpace ℝ ι) 0 T) :
    |euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, w) p -
        (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g) p| ≤
      Real.exp (‖c‖ * T) * (1 + T) * δ := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hg 0)
  have hnorm : ‖w - toBUC g‖ ≤ δ := by
    rw [← ClosedSubmodule.norm_coe]
    refine (norm_le hδ).2 fun x ↦ ?_
    have hx := hg x
    rwa [← toBUC_apply, ← Real.norm_eq_abs, ← _root_.sub_apply] at hx
  -- By linearity, the difference is the extended solution with data `(0, w - g)`.
  have hsub : euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, w) -
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
        (hn.trans (mul_le_mul_of_nonneg_left hnorm (by positivity)))

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
  have hgw (x) : |(w : EuclideanSpace ℝ ι →ᵇ ℝ) x - g x| < δ := by
    rw [← toBUC_apply, ← Real.norm_eq_abs, ← _root_.sub_apply]
    exact (norm_coe_le_norm _ x).trans_lt hg
  exact ⟨g, hgw, abs_euclideanCauchySolutionBUC_apply_sub_le hα₀ hα₁ hT ha f w g
    fun x ↦ (hgw x).le⟩

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
  refine (denseRange_euclideanCauchyDataToBUC hα₁.le).induction_on
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

/-! ### Bounded classical solutions -/

/-- Let `u ∈ C_b^{2+α,1+α/2}` solve `P u = f`, read as a function of time and space extended
constantly in time outside `[0, T]`. If `v` satisfies `P v ≤ f` at an interior point `(x, t)`,
then `w = v - u` satisfies the homogeneous inequality `∂ₜw ≤ aⁱʲ ∂ᵢ∂ⱼw + bⁱ ∂ᵢw + c w` there, in
the coordinate form of the whole-space maximum principle. -/
private theorem hasDerivAt_sub_and_le_of_deriv_sub_le
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT)
    (hu : euclideanParabolicOperatorL hα₁.le a b c u = f) {v : ℝ → EuclideanSpace ℝ ι → ℝ}
    {t : ℝ} (ht : t ∈ Ioo 0 (T : ℝ)) (x : EuclideanSpace ℝ ι) (hcd : ContDiffAt ℝ 2 (v t) x)
    (hdiff : DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hP : deriv (fun s ↦ v s x) t - (∑ i, ∑ j, a i j (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩) *
          fderiv ℝ (fderiv ℝ (v t)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        ∑ i, b i (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩) *
          fderiv ℝ (v t) x (EuclideanSpace.single i 1) +
        c (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩) * v t x) ≤
        f (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩)) :
    HasDerivAt (fun s ↦ (v s + (-1 : ℝ) • fun y ↦ u (slabMk y (projIcc (0 : ℝ) T hT.le s))) x)
        (deriv (fun s ↦ v s x) t - timeDerivL u (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩)) t ∧
      deriv (fun s ↦ v s x) t - timeDerivL u (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩) ≤
        ∑ i, ∑ j, (Matrix.of fun i j ↦ a i j (slabMk x (projIcc (0 : ℝ) T hT.le t))) i j *
            fderiv ℝ (fderiv ℝ (v t + (-1 : ℝ) • fun y ↦
              u (slabMk y (projIcc (0 : ℝ) T hT.le t)))) x
              (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
          fderiv ℝ (v t + (-1 : ℝ) • fun y ↦ u (slabMk y (projIcc (0 : ℝ) T hT.le t))) x
            (∑ i, b i (slabMk x (projIcc (0 : ℝ) T hT.le t)) • EuclideanSpace.single i 1) +
          c (slabMk x (projIcc (0 : ℝ) T hT.le t)) *
            (v t + (-1 : ℝ) • fun y ↦ u (slabMk y (projIcc (0 : ℝ) T hT.le t))) x + 0 := by
  have ht' : t ∈ Ioo 0 ((T : ℝ) - 0) := by rwa [sub_zero]
  have hp : projIcc (0 : ℝ) T hT.le t = ⟨t, Ioo_subset_Icc_self ht⟩ := projIcc_of_mem _ _
  have hd : HasDerivAt (fun s ↦ u (slabMk x (projIcc (0 : ℝ) T hT.le s)))
      (timeDerivL u (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩)) t := by
    simpa only [add_zero, hp] using hasDerivAt_slabMk_projIcc_add u x ht'
  have hU := deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_eq_euclideanParabolicOperatorL
    hα₁.le (a := a) (b := b) (c := c) u ht' x
  simp only [add_zero, hu] at hU
  rw [hd.deriv] at hU
  refine ⟨(hdiff.hasDerivAt.add (hd.const_smul (-1 : ℝ))).congr_deriv
    (by simp [sub_eq_add_neg]), ?_⟩
  rw [add_zero, PDE.sum_mul_fderiv_fderiv_add_fderiv_add_smul hcd
    (u.contDiff_spatialSlice _).contDiffAt]
  simp only [hp, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_smul]
    at hU ⊢
  linarith only [hP, hU]

/-- A bounded classical subsolution that starts at most `δ` above a `C^{2,α}` datum `g` stays at
most `exp (‖c‖ t) δ` above the classical solution `u` with data `(f, g)`: if `v` is continuous on
`[0, T] × ℝⁿ` and bounded above there, `C²` in space and differentiable in time for `0 < t < T`,
with `P v ≤ f` there and `v(·, 0) ≤ g + δ`, then `v(t, x) - u(x, t) ≤ exp (‖c‖ t) δ`. -/
private theorem sub_le_exp_mul_of_deriv_sub_le
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) {v : ℝ → EuclideanSpace ℝ ι → ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hcont : ContinuousOn (Function.uncurry v) (Icc 0 (T : ℝ) ×ˢ univ))
    (hbdd : BddAbove (Function.uncurry v '' Icc 0 (T : ℝ) ×ˢ univ))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 (T : ℝ) → ∀ x, ContDiffAt ℝ 2 (v t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 (T : ℝ) → ∀ x, DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hP : ∀ ⦃t⦄ (ht : t ∈ Ioo 0 (T : ℝ)) x,
      deriv (fun s ↦ v s x) t - (∑ i, ∑ j, a i j (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩) *
          fderiv ℝ (fderiv ℝ (v t)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        ∑ i, b i (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩) *
          fderiv ℝ (v t) x (EuclideanSpace.single i 1) +
        c (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩) * v t x) ≤
        f (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩))
    (hinit : ∀ x, v 0 x ≤ g x + δ) {t : ℝ} (ht : t ∈ Icc 0 (T : ℝ)) (x : EuclideanSpace ℝ ι) :
    v t x - (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g) (slabMk x ⟨t, ht⟩) ≤
      Real.exp (‖c‖ * t) * δ := by
  set u := (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g)
  have hu : euclideanParabolicOperatorL hα₁.le a b c u = f :=
    euclideanParabolicOperatorL_euclideanInitialDataCLE_symm_apply (f, g)
  have hUle : ∀ p, -u p ≤ ‖valueL u‖ := fun p ↦
    neg_le.1 (neg_le_of_abs_le (by simpa using (valueL u).norm_coe_le_norm p))
  have hUcont : Continuous fun z : ℝ × EuclideanSpace ℝ ι ↦
      u (slabMk z.2 (projIcc (0 : ℝ) T hT.le z.1)) :=
    (valueL u).continuous.comp (continuous_slabMk.comp (continuous_snd.prodMk
      ((continuous_projIcc (h := hT.le)).comp continuous_fst)))
  obtain ⟨Mv, hMv⟩ := hbdd
  have key := PDE.le_exp_mul_mul_add_mul_of_deriv_le_sum_mul_fderiv_fderiv_add_fderiv_add_mul_add
    (u := fun s ↦ v s + (-1 : ℝ) • fun y ↦ u (slabMk y (projIcc (0 : ℝ) T hT.le s)))
    (a := fun s y ↦ Matrix.of fun i j ↦ a i j (slabMk y (projIcc (0 : ℝ) T hT.le s)))
    (b := fun s y ↦ ∑ i, b i (slabMk y (projIcc (0 : ℝ) T hT.le s)) • EuclideanSpace.single i 1)
    (c := fun s y ↦ c (slabMk y (projIcc (0 : ℝ) T hT.le s)))
    (Lam := ∑ i, ‖a i i‖) (β := ∑ i, ‖b i‖) (M := δ) (F := 0)
    (fun s _ y ξ ↦ nonneg_quadraticForm ha _ ξ)
    (fun s _ y ↦ (HolderSpace.trace_le_sum_norm a _).trans (le_mul_of_one_le_right (by positivity)
      (le_add_of_nonneg_right (by positivity))))
    (fun s _ y ↦ (HolderSpace.norm_sum_apply_smul_single_le_sum_norm b _).trans
      (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (norm_nonneg y))))
    (fun s _ y ↦ (le_abs_self _).trans (HolderSpace.norm_apply_le c _)) (norm_nonneg c) hδ le_rfl
    ((hcont.add (hUcont.continuousOn.const_smul (-1 : ℝ))).congr fun _ _ ↦ rfl)
    ⟨Mv + ‖valueL u‖, by
      rintro _ ⟨⟨s, y⟩, hsy, rfl⟩
      have h1 : v s y ≤ Mv := hMv ⟨(s, y), hsy, rfl⟩
      simp only [Function.uncurry_apply_pair, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith only [h1, hUle (slabMk y (projIcc (0 : ℝ) T hT.le s))]⟩
    (fun s hs y ↦ (hcd hs y).add ((u.contDiff_spatialSlice _).contDiffAt.const_smul (-1 : ℝ)))
    (fun s hs y ↦ (hasDerivAt_sub_and_le_of_deriv_sub_le hα₁ hT f u hu hs y (hcd hs y)
      (hdiff hs y) (hP hs y)).1.differentiableAt)
    (fun s hs y ↦ by
      obtain ⟨hd, hle⟩ := hasDerivAt_sub_and_le_of_deriv_sub_le hα₁ hT f u hu hs y (hcd hs y)
        (hdiff hs y) (hP hs y)
      rw [hd.deriv]; exact hle)
    (fun y ↦ by
      have h0 : projIcc (0 : ℝ) T hT.le 0 = ⟨0, left_mem_Icc.2 hT.le⟩ := projIcc_of_mem _ _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0]
      rw [euclideanInitialDataCLE_symm_apply_slabMk_zero]
      linarith only [hinit y])
  have hpt : projIcc (0 : ℝ) T hT.le t = ⟨t, ht⟩ := projIcc_of_mem _ _
  have h := key ht x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hpt, mul_zero, add_zero] at h
  linarith only [h]

/-- **Bounded classical subsolutions lie below the extended solution.** Let `v : ℝ → ℝⁿ → ℝ`,
with time as its first argument, be continuous on `[0, T] × ℝⁿ` and bounded above there, `C²` in
space and differentiable in time for `0 < t < T`, with
`∂ₜv - (aⁱʲ ∂ᵢ∂ⱼv + bⁱ ∂ᵢv + c v) ≤ f` there and `v(·, 0) ≤ g`. Then `v` lies below the extended
solution `euclideanCauchySolutionBUC (f, g)` on `[0, T] × ℝⁿ`. No regularity of `v` at `t = 0`
beyond continuity is needed. -/
theorem le_euclideanCauchySolutionBUC_apply_of_deriv_sub_le
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) {v : ℝ → EuclideanSpace ℝ ι → ℝ}
    (hcont : ContinuousOn (Function.uncurry v) (Icc 0 (T : ℝ) ×ˢ univ))
    (hbdd : BddAbove (Function.uncurry v '' Icc 0 (T : ℝ) ×ˢ univ))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 (T : ℝ) → ∀ x, ContDiffAt ℝ 2 (v t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 (T : ℝ) → ∀ x, DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hP : ∀ ⦃t⦄ (ht : t ∈ Ioo 0 (T : ℝ)) x,
      deriv (fun s ↦ v s x) t - (∑ i, ∑ j, a i j (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩) *
          fderiv ℝ (fderiv ℝ (v t)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        ∑ i, b i (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩) *
          fderiv ℝ (v t) x (EuclideanSpace.single i 1) +
        c (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩) * v t x) ≤
        f (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩))
    (hinit : ∀ x, v 0 x ≤ (w : EuclideanSpace ℝ ι →ᵇ ℝ) x) {t : ℝ} (ht : t ∈ Icc 0 (T : ℝ))
    (x : EuclideanSpace ℝ ι) :
    v t x ≤ euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, w) (slabMk x ⟨t, ht⟩) := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  -- Approximate `w` within `δ` by a `C^{2,α}` datum `g`; compare `v` with its classical solution.
  obtain ⟨A, hA, hAdef⟩ : ∃ A, 0 ≤ A ∧ A = Real.exp (‖c‖ * T) * (1 + T) := ⟨_, by positivity, rfl⟩
  obtain ⟨δ, hδ, hεδ⟩ : ∃ δ, 0 < δ ∧ (Real.exp (‖c‖ * T) + A) * δ = ε :=
    ⟨ε / (Real.exp (‖c‖ * T) + A), by positivity, mul_div_cancel₀ ε (by positivity)⟩
  obtain ⟨g, hg, hu⟩ := exists_ckHolderSpace_approx hα₀ hα₁ hT ha f w hδ
  rw [← hAdef] at hu
  have hv := sub_le_exp_mul_of_deriv_sub_le hα₀ hα₁ hT ha f g hδ.le hcont hbdd hcd hdiff hP
    (fun y ↦ (hinit y).trans (sub_lt_iff_lt_add'.1 (abs_lt.1 (hg y)).2).le) ht x
  have hexp : Real.exp (‖c‖ * t) * δ ≤ Real.exp (‖c‖ * T) * δ :=
    mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 (norm_nonneg c))) hδ.le
  calc v t x ≤ (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g) (slabMk x ⟨t, ht⟩) +
        Real.exp (‖c‖ * t) * δ := sub_le_iff_le_add'.1 hv
    _ ≤ (euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, w) (slabMk x ⟨t, ht⟩) + A * δ) +
        Real.exp (‖c‖ * T) * δ :=
      add_le_add (neg_le_sub_iff_le_add.1 (abs_le.1 (hu (slabMk x ⟨t, ht⟩))).1) hexp
    _ = _ := by rw [← hεδ]; ring

/-- **Bounded classical supersolutions lie above the extended solution.** Let `v : ℝ → ℝⁿ → ℝ`,
with time as its first argument, be continuous on `[0, T] × ℝⁿ` and bounded below there, `C²` in
space and differentiable in time for `0 < t < T`, with
`f ≤ ∂ₜv - (aⁱʲ ∂ᵢ∂ⱼv + bⁱ ∂ᵢv + c v)` there and `g ≤ v(·, 0)`. Then `v` lies above the extended
solution `euclideanCauchySolutionBUC (f, g)` on `[0, T] × ℝⁿ`. -/
theorem euclideanCauchySolutionBUC_apply_le_of_le_deriv_sub
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) {v : ℝ → EuclideanSpace ℝ ι → ℝ}
    (hcont : ContinuousOn (Function.uncurry v) (Icc 0 (T : ℝ) ×ˢ univ))
    (hbdd : BddBelow (Function.uncurry v '' Icc 0 (T : ℝ) ×ˢ univ))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 (T : ℝ) → ∀ x, ContDiffAt ℝ 2 (v t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 (T : ℝ) → ∀ x, DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hP : ∀ ⦃t⦄ (ht : t ∈ Ioo 0 (T : ℝ)) x, f (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩) ≤
      deriv (fun s ↦ v s x) t - (∑ i, ∑ j, a i j (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩) *
          fderiv ℝ (fderiv ℝ (v t)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        ∑ i, b i (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩) *
          fderiv ℝ (v t) x (EuclideanSpace.single i 1) +
        c (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩) * v t x))
    (hinit : ∀ x, (w : EuclideanSpace ℝ ι →ᵇ ℝ) x ≤ v 0 x) {t : ℝ} (ht : t ∈ Icc 0 (T : ℝ))
    (x : EuclideanSpace ℝ ι) :
    euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, w) (slabMk x ⟨t, ht⟩) ≤ v t x := by
  -- `-v` is a subsolution with data `(-f, -w)`.
  have h := le_euclideanCauchySolutionBUC_apply_of_deriv_sub_le hα₀ hα₁ hT (b := b) (c := c) ha
    (-f) (-w) (v := -v) (hcont.neg.congr fun _ _ ↦ rfl)
    (by
      obtain ⟨m, hm⟩ := hbdd
      refine ⟨-m, ?_⟩
      rintro _ ⟨⟨s, y⟩, hsy, rfl⟩
      have h1 : m ≤ v s y := hm ⟨(s, y), hsy, rfl⟩
      simp only [Function.uncurry_apply_pair, Pi.neg_apply]
      linarith)
    (fun s hs y ↦ (hcd hs y).neg) (fun s hs y ↦ (hdiff hs y).neg)
    (fun s hs y ↦ by
      have h1 : fderiv ℝ (-v s) = -fderiv ℝ (v s) := funext fun _ ↦ fderiv_neg
      have h2 : fderiv ℝ (-fderiv ℝ (v s)) y = -fderiv ℝ (fderiv ℝ (v s)) y := fderiv_neg
      simp only [Pi.neg_apply, deriv.fun_neg, h1, h2, HolderSpace.neg_apply,
        _root_.neg_apply, mul_neg, Finset.sum_neg_distrib]
      linarith [hP hs y])
    (fun y ↦ by simpa using neg_le_neg (hinit y)) ht x
  rw [← Prod.neg_mk, map_neg, FunLike.coe_neg, Pi.neg_apply, Pi.neg_apply, Pi.neg_apply] at h
  linarith

/-- **Uniqueness among bounded classical solutions.** Let `v : ℝ → ℝⁿ → ℝ`, with time as its
first argument, be bounded and continuous on `[0, T] × ℝⁿ`, `C²` in space and differentiable in
time for `0 < t < T`, with `∂ₜv - (aⁱʲ ∂ᵢ∂ⱼv + bⁱ ∂ᵢv + c v) = f` there and `v(·, 0) = g`. Then
`v` is the extended solution `euclideanCauchySolutionBUC (f, g)` on `[0, T] × ℝⁿ`. In particular
the Cauchy problem with data in `C_b^{α,α/2} × BUC` has at most one solution among bounded
functions that are continuous on `[0, T] × ℝⁿ` and classical for `t > 0`. -/
theorem eq_euclideanCauchySolutionBUC_apply_of_deriv_sub_eq
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) {v : ℝ → EuclideanSpace ℝ ι → ℝ}
    (hcont : ContinuousOn (Function.uncurry v) (Icc 0 (T : ℝ) ×ˢ univ))
    (hbdd : Bornology.IsBounded (Function.uncurry v '' Icc 0 (T : ℝ) ×ˢ univ))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 (T : ℝ) → ∀ x, ContDiffAt ℝ 2 (v t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 (T : ℝ) → ∀ x, DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hP : ∀ ⦃t⦄ (ht : t ∈ Ioo 0 (T : ℝ)) x,
      deriv (fun s ↦ v s x) t - (∑ i, ∑ j, a i j (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩) *
          fderiv ℝ (fderiv ℝ (v t)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        ∑ i, b i (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩) *
          fderiv ℝ (v t) x (EuclideanSpace.single i 1) +
        c (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩) * v t x) =
        f (slabMk x ⟨t, Ioo_subset_Icc_self ht⟩))
    (hinit : ∀ x, v 0 x = (w : EuclideanSpace ℝ ι →ᵇ ℝ) x) {t : ℝ} (ht : t ∈ Icc 0 (T : ℝ))
    (x : EuclideanSpace ℝ ι) :
    v t x = euclideanCauchySolutionBUC hα₀ hα₁ hT a b c ha (f, w) (slabMk x ⟨t, ht⟩) := by
  rw [isBounded_iff_bddBelow_bddAbove] at hbdd
  exact le_antisymm
    (le_euclideanCauchySolutionBUC_apply_of_deriv_sub_le hα₀ hα₁ hT ha f w hcont hbdd.2 hcd hdiff
      (fun s hs y ↦ (hP hs y).le) (fun y ↦ (hinit y).le) ht x)
    (euclideanCauchySolutionBUC_apply_le_of_le_deriv_sub hα₀ hα₁ hT ha f w hcont hbdd.1 hcd hdiff
      (fun s hs y ↦ (hP hs y).ge) (fun y ↦ (hinit y).ge) ht x)

end Extension

/-! ### The terminal-value problem -/

section Terminal

/-- Time reversal `(x, t) ↦ (x, T - t)`, mapping the slab `ℝⁿ × [0, T]` onto itself. -/
private def slabReverse (T : ℝ≥0) :
    slab (E := EuclideanSpace ℝ ι) 0 T ≃ᵢ slab (E := EuclideanSpace ℝ ι) 0 T :=
  slabTimeReverse (T : ℝ) (sub_self _).symm (sub_zero _).symm

private theorem slabReverse_slabMk (x : EuclideanSpace ℝ ι) (t : Icc (0 : ℝ) T) :
    slabReverse T (slabMk x t) =
      slabMk x (iccTimeReverse (T : ℝ) (sub_self _).symm (sub_zero _).symm t) :=
  slabTimeReverse_slabMk _ _ _ x t

private theorem coe_slabTime_slabReverse (p : slab (E := EuclideanSpace ℝ ι) 0 T) :
    (slabTime (slabReverse T p) : ℝ) = T - slabTime p :=
  coe_slabTime_slabTimeReverse ..

/-- Reversing a coefficient or forcing field in time, `f ↦ f ∘ R`. -/
private def reverseL : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ →L[ℝ]
    HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ :=
  HolderSpace.compLipschitzL _ (slabReverse T).isometry.lipschitzWith

private theorem reverseL_apply (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (p : slab (E := EuclideanSpace ℝ ι) 0 T) : reverseL f p = f (slabReverse T p) :=
  HolderSpace.compLipschitzL_apply _ f p

private theorem norm_reverseL_apply_le (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) :
    ‖reverseL f‖ ≤ ‖f‖ := by
  simpa using (reverseL (α := α) (T := T)).le_of_opNorm_le
    (HolderSpace.norm_compLipschitzL_le_one _) f

/-- The data `(f, g)` of the terminal-value problem become the data `(-f ∘ R, g)` of the reversed
Cauchy problem. -/
private def reverseDataL : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ →L[ℝ]
    HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ :=
  (-reverseL).prodMap (ContinuousLinearMap.id ℝ _)

private theorem reverseDataL_apply (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) :
    reverseDataL (f, w) = (-reverseL f, w) :=
  (rfl)

variable [DecidableEq ι]

/-- Reversing the coefficients in time keeps them uniformly elliptic. -/
private theorem reverse_ellipticity
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ reverseL (a i j) p).toQuadraticForm' ξ :=
  ha.imp fun _ h ↦ ⟨h.1, fun p ξ ↦ by simpa only [reverseL_apply] using h.2 (slabReverse T p) ξ⟩

variable (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
  (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
  (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
  (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
  (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)

/-- **The solution operator for bounded uniformly continuous terminal data.** For `0 < α < 1`,
coefficients `aⁱʲ`, `bⁱ`, `c` in `C_b^{α,α/2}(ℝⁿ × [0, T])` with `a` uniformly elliptic, this is
the continuous linear map `(f, g) ↦ u` from `C_b^{α,α/2}(ℝⁿ × [0, T]) × BUC(ℝⁿ)` to the bounded
continuous functions on the slab that extends the solution operator of the terminal-value problem
`∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u = f`, `u(·, T) = g` from terminal data in `C_b^{2,α}(ℝⁿ)`
(`euclideanTerminalSolutionBUC_eq_valueL`). It is the time reversal of
`euclideanCauchySolutionBUC`. -/
def euclideanTerminalSolutionBUC :
    HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ →L[ℝ]
        (slab (E := EuclideanSpace ℝ ι) 0 T →ᵇ ℝ) :=
  (compContinuousCLM ℝ ℝ ⟨slabReverse T, (slabReverse T).continuous⟩).comp
    ((euclideanCauchySolutionBUC hα₀ hα₁ hT (fun i j ↦ reverseL (a i j)) (fun i ↦ reverseL (b i))
      (reverseL c) (reverse_ellipticity ha)).comp reverseDataL)

variable {a b c}

/-- The terminal-value solution at `p` is the solution of the reversed Cauchy problem with data
`(-f ∘ R, g)` at `R p`, `R (x, t) = (x, T - t)`. -/
private theorem euclideanTerminalSolutionBUC_apply
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ)
    (p : slab (E := EuclideanSpace ℝ ι) 0 T) :
    euclideanTerminalSolutionBUC hα₀ hα₁ hT a b c ha (f, w) p =
      euclideanCauchySolutionBUC hα₀ hα₁ hT (fun i j ↦ reverseL (a i j)) (fun i ↦ reverseL (b i))
        (reverseL c) (reverse_ellipticity ha) (-reverseL f, w) (slabReverse T p) :=
  (rfl)

/-- **Agreement with the classical solution.** If `u ∈ C_b^{2+α,1+α/2}` solves the terminal-value
problem `∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u = f` with terminal trace `u(·, T) = w`, then it is the
extended solution with data `(f, w)`. -/
theorem euclideanTerminalSolutionBUC_eq_valueL
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ)
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT)
    (hu : euclideanBackwardParabolicOperatorL hα₁.le a b c u = f)
    (hw : ∀ x, (w : EuclideanSpace ℝ ι →ᵇ ℝ) x = u (slabMk x ⟨T, right_mem_Icc.2 hT.le⟩)) :
    euclideanTerminalSolutionBUC hα₀ hα₁ hT a b c ha (f, w) = valueL u := by
  -- The time reversal `v = u ∘ R` solves the reversed Cauchy problem with data `(-f ∘ R, u(·, T))`.
  obtain ⟨v, hv⟩ : ∃ v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
      v = timeReverseLIE (T : ℝ) (sub_self _).symm (sub_zero _).symm u := ⟨_, rfl⟩
  have hPv : euclideanParabolicOperatorL hα₁.le (fun i j ↦ reverseL (a i j))
      (fun i ↦ reverseL (b i)) (reverseL c) v = -reverseL f := by
    rw [hv, ← hu]
    exact euclideanParabolicOperatorL_timeReverseLIE hα₁.le u
  have hv₀ : (euclideanInitialDataCLE hα₀ hα₁ hT (fun i j ↦ reverseL (a i j))
      (fun i ↦ reverseL (b i)) (reverseL c) (reverse_ellipticity ha)).symm
        (-reverseL f, v.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩) = v := by
    rw [ContinuousLinearEquiv.symm_apply_eq, euclideanInitialDataCLE_apply, hPv]
  have hcl := euclideanCauchySolutionBUC_apply_of_ckHolderSpace hα₀ hα₁ hT
    (b := fun i ↦ reverseL (b i)) (c := reverseL c) (reverse_ellipticity ha) (-reverseL f) w
    (v.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩) fun x ↦ by
      rw [hw, spatialTrace_apply, hv, timeReverseLIE_apply, slabTimeReverse_slabMk,
        iccTimeReverse_left _ _ _ hT.le]
  rw [hv₀] at hcl
  ext p
  rw [euclideanTerminalSolutionBUC_apply, hcl, valueL_apply, valueL_apply, hv,
    timeReverseLIE_apply]
  exact congrArg (valueL u) (slabTimeReverse_slabTimeReverse _ _ _ _ _ p)

/-- **Uniqueness of the extension.** A continuous linear map on `C_b^{α,α/2} × BUC` that agrees
with the classical solution operator of the terminal-value problem on `C_b^{2,α}` terminal data
is `euclideanTerminalSolutionBUC`. -/
theorem eq_euclideanTerminalSolutionBUC
    (L : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ →L[ℝ]
        (slab (E := EuclideanSpace ℝ ι) 0 T →ᵇ ℝ))
    (hL : ∀ (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
      (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ)
      (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT),
      euclideanBackwardParabolicOperatorL hα₁.le a b c u = f →
      (∀ x, (w : EuclideanSpace ℝ ι →ᵇ ℝ) x = u (slabMk x ⟨T, right_mem_Icc.2 hT.le⟩)) →
        L (f, w) = valueL u) :
    L = euclideanTerminalSolutionBUC hα₀ hα₁ hT a b c ha := by
  obtain ⟨lam, hlam, ha'⟩ := ha
  -- Both maps agree on the dense set of data with a `C_b^{2,α}` terminal datum.
  have hdense : DenseRange (Prod.map id toBUC :
      HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
        CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ →
      HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
        uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) :=
    denseRange_id.prodMap (denseRange_toBUC hα₁.le)
  refine DFunLike.coe_injective (hdense.equalizer L.continuous
    (euclideanTerminalSolutionBUC hα₀ hα₁ hT a b c ⟨lam, hlam, ha'⟩).continuous ?_)
  refine funext fun ⟨f, g⟩ ↦ ?_
  obtain ⟨u, hu⟩ := (bijective_euclideanBackwardParabolicOperatorL_prod_spatialTraceL hα₀ hα₁ hT
    b c hlam ha').2 (f, g)
  simp only [ContinuousLinearMap.prod_apply, Prod.mk.injEq] at hu
  have hw (x : EuclideanSpace ℝ ι) : ((toBUC g : uniformContinuousSubmodule ℝ _ ℝ) :
      EuclideanSpace ℝ ι →ᵇ ℝ) x = u (slabMk x ⟨T, right_mem_Icc.2 hT.le⟩) := by
    rw [toBUC_apply, ← hu.2, spatialTraceL_apply, spatialTrace_apply]
  simp only [Function.comp_apply, Prod.map_apply, id_eq]
  rw [hL f (toBUC g) u hu.1 hw,
    euclideanTerminalSolutionBUC_eq_valueL hα₀ hα₁ hT _ f (toBUC g) u hu.1 hw]

/-- **The supremum bound for the terminal-value solution.** The solution operator has operator
norm at most `exp (‖c‖ T) (1 + T)`. -/
theorem norm_euclideanTerminalSolutionBUC_le :
    ‖euclideanTerminalSolutionBUC hα₀ hα₁ hT a b c ha‖ ≤ Real.exp (‖c‖ * T) * (1 + T) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ⟨f, w⟩ ↦ ?_
  have hd : ‖reverseDataL (f, w)‖ ≤ ‖(f, w)‖ := by
    rw [reverseDataL_apply, Prod.norm_def, Prod.norm_def, norm_neg]
    exact max_le_max (norm_reverseL_apply_le f) le_rfl
  calc ‖euclideanTerminalSolutionBUC hα₀ hα₁ hT a b c ha (f, w)‖ ≤
        ‖euclideanCauchySolutionBUC hα₀ hα₁ hT (fun i j ↦ reverseL (a i j))
          (fun i ↦ reverseL (b i)) (reverseL c) (reverse_ellipticity ha) (reverseDataL (f, w))‖ :=
        norm_compContinuous_le _ _
    _ ≤ Real.exp (‖reverseL c‖ * T) * (1 + T) * ‖reverseDataL (f, w)‖ :=
        norm_euclideanCauchySolutionBUC_apply_le hα₀ hα₁ hT (a := fun i j ↦ reverseL (a i j))
          (b := fun i ↦ reverseL (b i)) (c := reverseL c) (reverse_ellipticity ha) _
    _ ≤ Real.exp (‖c‖ * T) * (1 + T) * ‖(f, w)‖ := by
        gcongr
        exact norm_reverseL_apply_le c

/-- **The supremum bound for the terminal-value solution.**
`‖u‖_∞ ≤ exp (‖c‖ T) (1 + T) max (‖f‖, ‖g‖_∞)`. -/
theorem norm_euclideanTerminalSolutionBUC_apply_le
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) :
    ‖euclideanTerminalSolutionBUC hα₀ hα₁ hT a b c ha d‖ ≤
      Real.exp (‖c‖ * T) * (1 + T) * ‖d‖ :=
  (euclideanTerminalSolutionBUC hα₀ hα₁ hT a b c ha).le_of_opNorm_le
    (norm_euclideanTerminalSolutionBUC_le hα₀ hα₁ hT ha) d

/-- **The maximum principle for the terminal-value solution.** Let `c ≤ γ` with `0 ≤ γ`. If the
forcing satisfies `f ≥ -K` and the terminal datum `g ≤ M`, where `0 ≤ M` and `0 ≤ K`, then the
solution satisfies `u(x, t) ≤ exp (γ (T - t)) (M + (T - t) K)`. -/
theorem euclideanTerminalSolutionBUC_apply_le {γ M K : ℝ} (hc : ∀ p, c p ≤ γ) (hγ : 0 ≤ γ)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) (hf : ∀ p, -K ≤ f p)
    (hw : ∀ x, (w : EuclideanSpace ℝ ι →ᵇ ℝ) x ≤ M) (p : slab (E := EuclideanSpace ℝ ι) 0 T) :
    euclideanTerminalSolutionBUC hα₀ hα₁ hT a b c ha (f, w) p ≤
      Real.exp (γ * (T - slabTime p)) * (M + (T - slabTime p) * K) := by
  rw [euclideanTerminalSolutionBUC_apply, ← coe_slabTime_slabReverse]
  exact euclideanCauchySolutionBUC_apply_le hα₀ hα₁ hT (a := fun i j ↦ reverseL (a i j))
    (b := fun i ↦ reverseL (b i)) (c := reverseL c) (reverse_ellipticity ha)
    (fun q ↦ by rw [reverseL_apply]; exact hc _) hγ hM hK (-reverseL f) w
    (fun q ↦ by rw [HolderSpace.neg_apply, reverseL_apply]; exact neg_le.1 (hf _)) hw _

/-- **The two-sided maximum principle bound.** If `c ≤ γ` with `0 ≤ γ`, `|f| ≤ K` and `|g| ≤ M`,
then the terminal-value solution satisfies `|u(x, t)| ≤ exp (γ (T - t)) (M + (T - t) K)`. -/
theorem abs_euclideanTerminalSolutionBUC_apply_le {γ M K : ℝ} (hc : ∀ p, c p ≤ γ) (hγ : 0 ≤ γ)
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) (hf : ∀ p, |f p| ≤ K)
    (hw : ∀ x, |(w : EuclideanSpace ℝ ι →ᵇ ℝ) x| ≤ M) (p : slab (E := EuclideanSpace ℝ ι) 0 T) :
    |euclideanTerminalSolutionBUC hα₀ hα₁ hT a b c ha (f, w) p| ≤
      Real.exp (γ * (T - slabTime p)) * (M + (T - slabTime p) * K) := by
  rw [euclideanTerminalSolutionBUC_apply, ← coe_slabTime_slabReverse]
  exact abs_euclideanCauchySolutionBUC_apply_le hα₀ hα₁ hT (a := fun i j ↦ reverseL (a i j))
    (b := fun i ↦ reverseL (b i)) (c := reverseL c) (reverse_ellipticity ha)
    (fun q ↦ by rw [reverseL_apply]; exact hc _) hγ (-reverseL f) w
    (fun q ↦ by rw [HolderSpace.neg_apply, reverseL_apply, abs_neg]; exact hf _) hw _

/-- **The comparison principle for the terminal-value solution.** If `f' ≤ f` and `g ≤ g'`, then
the solution with data `(f, g)` lies below the solution with data `(f', g')`. -/
theorem euclideanTerminalSolutionBUC_apply_le_apply
    {f f' : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    {w w' : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ} (hf : ∀ p, f' p ≤ f p)
    (hw : ∀ x, (w : EuclideanSpace ℝ ι →ᵇ ℝ) x ≤ (w' : EuclideanSpace ℝ ι →ᵇ ℝ) x)
    (p : slab (E := EuclideanSpace ℝ ι) 0 T) :
    euclideanTerminalSolutionBUC hα₀ hα₁ hT a b c ha (f, w) p ≤
      euclideanTerminalSolutionBUC hα₀ hα₁ hT a b c ha (f', w') p := by
  rw [euclideanTerminalSolutionBUC_apply, euclideanTerminalSolutionBUC_apply]
  exact euclideanCauchySolutionBUC_apply_le_apply hα₀ hα₁ hT (a := fun i j ↦ reverseL (a i j))
    (b := fun i ↦ reverseL (b i)) (c := reverseL c) (reverse_ellipticity ha)
    (fun q ↦ by simp only [HolderSpace.neg_apply, reverseL_apply, neg_le_neg_iff]; exact hf _) hw _

/-- **The terminal condition.** The terminal-value solution takes the terminal datum at `t = T`. -/
@[simp]
theorem euclideanTerminalSolutionBUC_apply_slabMk_right
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) (x : EuclideanSpace ℝ ι) :
    euclideanTerminalSolutionBUC hα₀ hα₁ hT a b c ha (f, w)
        (slabMk x ⟨T, right_mem_Icc.2 hT.le⟩) = (w : EuclideanSpace ℝ ι →ᵇ ℝ) x := by
  rw [euclideanTerminalSolutionBUC_apply, slabReverse_slabMk, iccTimeReverse_right _ _ _ hT.le,
    euclideanCauchySolutionBUC_apply_slabMk_zero]

/-- **Uniform attainment of the terminal datum.** As `t → T⁻`, the terminal-value solution
converges to the terminal datum uniformly on `ℝⁿ`: `sup_x |u(x, t) - g(x)| → 0`. -/
theorem tendstoUniformly_euclideanTerminalSolutionBUC
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) :
    TendstoUniformly (fun (t : Icc (0 : ℝ) T) (x : EuclideanSpace ℝ ι) ↦
      euclideanTerminalSolutionBUC hα₀ hα₁ hT a b c ha (f, w) (slabMk x t))
      (fun x ↦ (w : EuclideanSpace ℝ ι →ᵇ ℝ) x) (𝓝 ⟨T, right_mem_Icc.2 hT.le⟩) := by
  -- Time reversal `t ↦ T - t` is continuous and sends `T` to `0`, where the reversed Cauchy
  -- solution attains its initial datum uniformly.
  have hσ := (iccTimeReverse (T : ℝ) (sub_self _).symm (sub_zero _).symm).continuous.tendsto
    ⟨(T : ℝ), right_mem_Icc.2 hT.le⟩
  rw [iccTimeReverse_right _ _ _ hT.le] at hσ
  have h := tendstoUniformly_euclideanCauchySolutionBUC hα₀ hα₁ hT (b := fun i ↦ reverseL (b i))
    (c := reverseL c) (reverse_ellipticity ha) (-reverseL f) w
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  filter_upwards [hσ.eventually (h ε hε)] with t ht x
  rw [euclideanTerminalSolutionBUC_apply, slabReverse_slabMk]
  exact ht x

end Terminal

end TauCeti.ParabolicC2HolderSpace
