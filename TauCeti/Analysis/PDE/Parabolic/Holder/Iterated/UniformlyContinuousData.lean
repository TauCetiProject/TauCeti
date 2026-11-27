/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.PositiveTime
public import TauCeti.Analysis.PDE.Parabolic.Holder.UniformlyContinuousData
import TauCeti.Analysis.Holder.Inclusion
import TauCeti.Analysis.PDE.HeatKernel.UniformContinuous

/-!
# Uniformly continuous initial data at every order

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `ℝⁿ × [0, T]`, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have scalar coefficients in the parabolic Hölder space `C_{par,b}^{k+α}`, `0 < α < 1`, with `a`
uniformly elliptic. For a forcing `f ∈ C_{par,b}^{k+α}` and an initial datum `g` that is only
bounded and uniformly continuous, the Cauchy problem `P u = f`, `u(·, 0) = g` has the solution
`TauCeti.ParabolicC2HolderSpace.euclideanCauchySolutionBUC`, a bounded continuous function on the
slab obtained from the classical solutions by continuity in the supremum norm of `g`. That solution
lies in `C_b^{2+α,1+α/2}` on every slab `ℝⁿ × [δ, T]`, `0 < δ < T`. This file shows that it is as
regular there as the coefficients and the forcing allow: it lies in `C_{par,b}^{k+2+α}` on
`ℝⁿ × [δ, T]`, with

`‖u‖_{k+2+α;[δ,T]} ≤ C max (‖f‖_{k+α}, sup |g|)`,

where `C` depends only on `n`, `k`, `α`, `δ`, the ellipticity constant, a bound on the norms of
the coefficients in `C_{par,b}^{k+α}` and a bound on the horizon. Only the supremum of the initial
datum enters: no derivative of `g` is needed at positive times.

* `TauCeti.ParabolicCkHolderSpace.euclideanCauchySolutionBUCRestrictL`: the solution on
  `ℝⁿ × [δ, T]`, as a continuous linear map
  `C_{par,b}^{k+α}(ℝⁿ × [0, T]) × BUC(ℝⁿ) →L[ℝ] C_{par,b}^{k+2+α}(ℝⁿ × [δ, T])`.
* `TauCeti.ParabolicCkHolderSpace.euclideanCauchySolutionBUCRestrictL_toBUC`: on initial data in
  `C_b^{k+2,α}` it is the restriction of the solution of order `k + 2` on the whole slab
  (`TauCeti.ParabolicCkHolderSpace.euclideanInitialDataCLE`).
* `TauCeti.ParabolicCkHolderSpace.euclideanCauchySolutionBUCRestrictL_apply`: its values are those
  of `TauCeti.ParabolicC2HolderSpace.euclideanCauchySolutionBUC`, with the coefficients and the
  forcing read in `C_b^{α,α/2}`. So the maximum principle, the uniform attainment of the initial
  datum and the uniqueness among bounded classical solutions proved there apply to it.
* `TauCeti.ParabolicCkHolderSpace.parabolicOperatorL_euclideanCauchySolutionBUCRestrictL`: it
  solves `P u = f` on `ℝⁿ × [δ, T]`.
* `TauCeti.ParabolicCkHolderSpace.exists_norm_euclideanCauchySolutionBUCRestrictL_le`: the
  estimate above, uniformly in the coefficients and in the horizon.

## The argument

On data `(f, g)` with `g ∈ C_b^{k+2,α}` the solution of order `k + 2` exists on the whole slab,
and the Schauder estimate of order `k` at positive times
(`TauCeti.ParabolicCkHolderSpace.exists_norm_restrictL_le_parabolicOperatorL`) bounds its
restriction to `ℝⁿ × [δ, T]` by `‖f‖_{k+α}` and `sup |g|`. The data `C_{par,b}^{k+α} × C_b^{k+2,α}`
are dense in `C_{par,b}^{k+α} × BUC` (`TauCeti.CkHolderSpace.denseRange_toBUC`), so the restricted
solution map extends by continuity, and the identities that hold on the dense data, the equation
and the agreement of values with the extended solution of order two, pass to the limit. The values
agree on the dense data because the solution of order `k + 2` has the values of the solution in
`C_b^{2+α,1+α/2}`
(`TauCeti.ParabolicCkHolderSpace.coe_euclideanInitialDataCLE_symm_eq_parabolicC2HolderSpace`).

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4
  (solutions with continuous initial data as limits of solutions with smooth data).
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Prentice-Hall, 1964, Chapter 3
  (Schauder estimates away from the initial time).
-/

public section
noncomputable section

namespace TauCeti.ParabolicCkHolderSpace

open Set ParabolicSpaceTime BoundedContinuousFunction
open CkHolderSpace (toBUC toBUC_apply denseRange_toBUC)
open scoped NNReal

attribute [local instance] instNormedAddCommGroupContinuousLinearMapRealId
  instNormedSpaceRealContinuousLinearMapId instNormedAddCommGroupEuclideanCovector
  instNormedSpaceEuclideanCovector instNormedAddCommGroupEuclideanHessian
  instNormedSpaceEuclideanHessian

variable {ι : Type*} [Fintype ι] {k : ℕ} {α T : ℝ≥0} {hT : (0 : ℝ) < T}

/-! ### The data map -/

/-- The data map `(f, g) ↦ (f, g)` from `C_{par,b}^{k+α} × C_b^{k+2,α}` to
`C_{par,b}^{k+α} × BUC`, along which the solution operator extends. -/
private def cauchyDataToBUC :
    ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT ×
      CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ →ₗ[ℝ]
    ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ :=
  LinearMap.prodMap LinearMap.id toBUC.toLinearMap

private theorem cauchyDataToBUC_apply
    (d : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT ×
      CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ) :
    cauchyDataToBUC d = (d.1, toBUC d.2) :=
  (rfl)

/-- The data map has dense range, since `C_b^{k+2,α}` is dense in `BUC`. -/
private theorem denseRange_cauchyDataToBUC (hα : α ≤ 1) :
    DenseRange (cauchyDataToBUC (k := k) (α := α) (ι := ι) (hT := hT)) := by
  rw [cauchyDataToBUC, LinearMap.coe_prodMap, LinearMap.id_coe, ContinuousLinearMap.coe_coe]
  exact denseRange_id.prodMap (denseRange_toBUC hα)

/-! ### The solution at positive times -/

section PositiveTime

variable [DecidableEq ι] (hα₀ : 0 < α) (hα₁ : α < 1)

/-- The classical solution `(f, g) ↦ u` of the Cauchy problem with initial datum in
`C_b^{k+2,α}`, restricted to `ℝⁿ × [δ, T]`. -/
private def restrictedSolution
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {δ : ℝ} (hδ : 0 < δ) (hδT : δ < T) :
    ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT ×
      CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ →ₗ[ℝ]
        ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hδT :=
  ((restrictL hδ.le le_rfl hδT).comp
    (euclideanInitialDataCLE hα₀ hα₁ a b c ha).symm.toContinuousLinearMap).toLinearMap

/-- The Schauder estimate at positive times for the classical solutions, in the norm of the data
space `C_{par,b}^{k+α} × BUC`: `‖u‖_{k+2+α;[δ,T]} ≤ C max (‖f‖_{k+α}, sup |g|)`, uniformly over the
coefficients and horizons in the given bounds. -/
private theorem exists_norm_restrictedSolution_le {lam : ℝ} (hlam : 0 < lam) (k : ℕ)
    (K T₀ : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ → ∀ hδT : δ < T,
      ∀ (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ d : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT ×
            CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ,
          ‖restrictedSolution hα₀ hα₁ a b c ⟨lam, hlam, ha⟩ hδ hδT d‖ ≤
            C * ‖cauchyDataToBUC d‖ := by
  obtain ⟨C, hC, hest⟩ :=
    exists_norm_restrictL_le_parabolicOperatorL (ι := ι) hα₀ hα₁ hlam k K T₀ hδ
  refine ⟨2 * C, by positivity, fun T hT hTT₀ hδT a b c ha hak hbk hck d ↦ ?_⟩
  set u := (euclideanInitialDataCLE hα₀ hα₁ a b c ⟨lam, hlam, ha⟩).symm d
  -- The initial values of the classical solution are bounded by the supremum norm of the datum.
  have hM (x : EuclideanSpace ℝ ι) : |u (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩)| ≤ ‖toBUC d.2‖ := by
    rw [euclideanInitialDataCLE_symm_apply_slabMk_zero, ← toBUC_apply, ← Real.norm_eq_abs,
      ← ClosedSubmodule.norm_coe]
    exact BoundedContinuousFunction.norm_coe_le_norm _ x
  have h := hest T hT hTT₀ hδT a b c ha hak hbk hck u hM
  rw [parabolicOperatorL_euclideanInitialDataCLE_symm_apply] at h
  rw [cauchyDataToBUC_apply]
  have hf := norm_fst_le (d.1, toBUC d.2)
  have hg := norm_snd_le (d.1, toBUC d.2)
  calc ‖restrictedSolution hα₀ hα₁ a b c ⟨lam, hlam, ha⟩ hδ hδT d‖
      ≤ C * (‖d.1‖ + ‖toBUC d.2‖) := h
    _ ≤ 2 * C * ‖(d.1, toBUC d.2)‖ := by nlinarith

variable (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
  (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
  (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
  (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
  {δ : ℝ} (hδ : 0 < δ) (hδT : δ < T)

/-- **The solution with uniformly continuous initial data at positive times, at every order.**
For `0 < α < 1`, coefficients `aⁱʲ`, `bⁱ`, `c` in `C_{par,b}^{k+α}(ℝⁿ × [0, T])` with `a`
uniformly elliptic, and `0 < δ < T`, the restriction to `ℝⁿ × [δ, T]` of the solution of the
Cauchy problem `P u = f`, `u(·, 0) = g` with bounded uniformly continuous initial datum `g`, as a
continuous linear map `C_{par,b}^{k+α}(ℝⁿ × [0, T]) × BUC(ℝⁿ) →L[ℝ] C_{par,b}^{k+2+α}(ℝⁿ × [δ, T])`.
Its values are those of `TauCeti.ParabolicC2HolderSpace.euclideanCauchySolutionBUC`
(`euclideanCauchySolutionBUCRestrictL_apply`), and it solves `P u = f`
(`parabolicOperatorL_euclideanCauchySolutionBUCRestrictL`). -/
def euclideanCauchySolutionBUCRestrictL :
    ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ →L[ℝ]
        ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hδT :=
  (restrictedSolution hα₀ hα₁ a b c ha hδ hδT).extendOfNorm cauchyDataToBUC

variable {a b c}

private theorem euclideanCauchySolutionBUCRestrictL_cauchyDataToBUC
    (d : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT ×
      CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ) :
    euclideanCauchySolutionBUCRestrictL hα₀ hα₁ a b c ha hδ hδT (cauchyDataToBUC d) =
      restrictL hδ.le le_rfl hδT ((euclideanInitialDataCLE hα₀ hα₁ a b c ha).symm d) :=
  LinearMap.extendOfNorm_eq (denseRange_cauchyDataToBUC hα₁.le) (by
    obtain ⟨lam, hlam, hlam'⟩ := ha
    obtain ⟨C, -, hC⟩ :=
      exists_norm_restrictedSolution_le (ι := ι) hα₀ hα₁ hlam k (‖a‖₊ ⊔ ‖b‖₊ ⊔ ‖c‖₊) T hδ
    -- The norms of the coefficients are bounded by the supremum norms of the families.
    exact ⟨C, hC T hT le_rfl hδT a b c hlam'
      (fun i j ↦ ((norm_le_pi_norm (a i) j).trans (norm_le_pi_norm a i)).trans
        (le_sup_left.trans le_sup_left : ‖a‖₊ ≤ _))
      (fun i ↦ (norm_le_pi_norm b i).trans (le_sup_right.trans le_sup_left : ‖b‖₊ ≤ _))
      (le_sup_right : ‖c‖₊ ≤ _)⟩) d

/-- **Agreement with the classical solution.** On an initial datum `g ∈ C_b^{k+2,α}`, the solution
at positive times is the restriction to `ℝⁿ × [δ, T]` of the solution in `C_{par,b}^{k+2+α}` of
`P u = f`, `u(·, 0) = g`. -/
@[simp]
theorem euclideanCauchySolutionBUCRestrictL_toBUC
    (f : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (g : CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ) :
    euclideanCauchySolutionBUCRestrictL hα₀ hα₁ a b c ha hδ hδT (f, toBUC g) =
      restrictL hδ.le le_rfl hδT ((euclideanInitialDataCLE hα₀ hα₁ a b c ha).symm (f, g)) :=
  euclideanCauchySolutionBUCRestrictL_cauchyDataToBUC hα₀ hα₁ ha hδ hδT (f, g)

/-- **The values are those of the extended solution.** On `ℝⁿ × [δ, T]`, the values of
`euclideanCauchySolutionBUCRestrictL` are those of the solution
`TauCeti.ParabolicC2HolderSpace.euclideanCauchySolutionBUC` with bounded uniformly continuous
initial datum, for coefficients `a'`, `b'`, `c'` and a forcing `f'` in `C_b^{α,α/2}` with the
values of `a`, `b`, `c` and `f`. -/
theorem euclideanCauchySolutionBUCRestrictL_apply
    {a' : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    {b' : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    {c' : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (ha' : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a' i j p).toQuadraticForm' ξ)
    (haa' : ∀ i j, ⇑(a' i j) = ⇑(a i j)) (hbb' : ∀ i, ⇑(b' i) = ⇑(b i)) (hcc' : ⇑c' = ⇑c)
    {f : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT}
    {f' : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ} (hff' : ⇑f' = ⇑f)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ)
    (p : slab (E := EuclideanSpace ℝ ι) δ T) :
    euclideanCauchySolutionBUCRestrictL hα₀ hα₁ a b c ha hδ hδT (f, w) p =
      ParabolicC2HolderSpace.euclideanCauchySolutionBUC hα₀ hα₁ hT a' b' c' ha' (f', w)
        (inclusion (slab_subset_slab hδ.le le_rfl) p) := by
  refine (denseRange_toBUC (k := k + 1) hα₁.le).induction_on
    (p := fun w ↦ euclideanCauchySolutionBUCRestrictL hα₀ hα₁ a b c ha hδ hδT (f, w) p =
      ParabolicC2HolderSpace.euclideanCauchySolutionBUC hα₀ hα₁ hT a' b' c' ha' (f', w)
        (inclusion (slab_subset_slab hδ.le le_rfl) p)) w ?_ fun g ↦ ?_
  · refine isClosed_eq ?_ ?_
    · simp_rw [← valueL_apply]
      exact (continuous_eval_const p).comp (valueL.continuous.comp
        ((euclideanCauchySolutionBUCRestrictL hα₀ hα₁ a b c ha hδ hδT).continuous.comp
          (continuous_const.prodMk continuous_id)))
    · exact (continuous_eval_const _).comp
        ((ParabolicC2HolderSpace.euclideanCauchySolutionBUC hα₀ hα₁ hT a' b' c' ha').continuous.comp
          (continuous_const.prodMk continuous_id))
  · obtain ⟨g', hg'⟩ := CkHolderSpace.exists_coe_eq_of_le hα₁.le (Nat.le_add_left 2 k) g
    rw [euclideanCauchySolutionBUCRestrictL_toBUC, restrictL_apply,
      ParabolicC2HolderSpace.euclideanCauchySolutionBUC_apply_of_ckHolderSpace hα₀ hα₁ hT ha' f'
        (toBUC g) g' fun x ↦ by rw [toBUC_apply, hg'],
      ParabolicC2HolderSpace.valueL_apply]
    exact congrFun (coe_euclideanInitialDataCLE_symm_eq_parabolicC2HolderSpace hα₀ hα₁ a b c ha ha'
      haa' hbb' hcc' hff' hg') _

/-- **The solution is a classical solution at positive times.** On `ℝⁿ × [δ, T]`,
`euclideanCauchySolutionBUCRestrictL` solves `P u = f`, where `P` has the coefficients `aⁱʲ`, `bⁱ`,
`c` restricted to `ℝⁿ × [δ, T]`. -/
theorem parabolicOperatorL_euclideanCauchySolutionBUCRestrictL
    (f : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) :
    parabolicOperatorL hα₁.le
        (euclideanSecondOrderCoeff fun i j ↦ restrictL hδ.le le_rfl hδT (a i j))
        (euclideanFirstOrderCoeff fun i ↦ restrictL hδ.le le_rfl hδT (b i))
        (euclideanZerothOrderCoeff (restrictL hδ.le le_rfl hδT c))
        (euclideanCauchySolutionBUCRestrictL hα₀ hα₁ a b c ha hδ hδT (f, w)) =
      restrictL hδ.le le_rfl hδT f := by
  refine (denseRange_toBUC (k := k + 1) hα₁.le).induction_on
    (p := fun w ↦ parabolicOperatorL hα₁.le
        (euclideanSecondOrderCoeff fun i j ↦ restrictL hδ.le le_rfl hδT (a i j))
        (euclideanFirstOrderCoeff fun i ↦ restrictL hδ.le le_rfl hδT (b i))
        (euclideanZerothOrderCoeff (restrictL hδ.le le_rfl hδT c))
        (euclideanCauchySolutionBUCRestrictL hα₀ hα₁ a b c ha hδ hδT (f, w)) =
      restrictL hδ.le le_rfl hδT f) w
    (isClosed_eq ((ContinuousLinearMap.continuous _).comp
      ((euclideanCauchySolutionBUCRestrictL hα₀ hα₁ a b c ha hδ hδT).continuous.comp
        (continuous_const.prodMk continuous_id))) continuous_const) fun g ↦ ?_
  rw [euclideanCauchySolutionBUCRestrictL_toBUC, ← restrictL_euclideanSecondOrderCoeff,
    ← restrictL_euclideanFirstOrderCoeff, ← restrictL_euclideanZerothOrderCoeff,
    parabolicOperatorL_restrictL, parabolicOperatorL_euclideanInitialDataCLE_symm_apply]

/-- **Schauder estimate at positive times for uniformly continuous initial data, at every
order.** For `0 < α < 1`, an ellipticity constant `λ > 0`, `k : ℕ`, a bound `K` on the norms of the
coefficients in `C_{par,b}^{k+α}`, a bound `T₀` on the horizon and a time `δ > 0`, there is a
constant `C` such that the solution `u` of `P u = f`, `u(·, 0) = g` on `ℝⁿ × [0, T]`,
`δ < T ≤ T₀`, with `f ∈ C_{par,b}^{k+α}` and `g ∈ BUC(ℝⁿ)` satisfies

`‖u‖_{k+2+α;[δ,T]} ≤ C max (‖f‖_{k+α}, sup |g|)`,

where `‖u‖_{k+2+α;[δ,T]}` is the norm of `u` in `C_{par,b}^{k+2+α}(ℝⁿ × [δ, T])`. -/
theorem exists_norm_euclideanCauchySolutionBUCRestrictL_le {lam : ℝ} (hlam : 0 < lam) (k : ℕ)
    (K T₀ : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ → ∀ hδT : δ < T,
      ∀ (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ d : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT ×
            uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ,
          ‖euclideanCauchySolutionBUCRestrictL hα₀ hα₁ a b c ⟨lam, hlam, ha⟩ hδ hδT d‖ ≤
            C * ‖d‖ := by
  obtain ⟨C, hC, hest⟩ := exists_norm_restrictedSolution_le (ι := ι) hα₀ hα₁ hlam k K T₀ hδ
  exact ⟨C, hC, fun T hT hTT₀ hδT a b c ha hak hbk hck d ↦
    LinearMap.norm_extendOfNorm_apply_le (denseRange_cauchyDataToBUC hα₁.le) C
      (hest T hT hTT₀ hδT a b c ha hak hbk hck) d⟩

end PositiveTime

end TauCeti.ParabolicCkHolderSpace
