/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.UniformlyContinuousData

/-!
# Terminal-value problems with uniformly continuous data before the terminal time

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `Q = ℝⁿ × [0, T]`, let

`P_back u = ∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u`

have coefficients in `C_b^{α,α/2}(Q)`, `0 < α < 1`, with `a` uniformly elliptic. For a forcing
`f ∈ C_b^{α,α/2}(Q)` and a terminal datum `g` that is only bounded and uniformly continuous, the
terminal-value problem `P_back u = f`, `u(·, T) = g` is solved by the extended solution operator
`TauCeti.ParabolicC2HolderSpace.euclideanTerminalSolutionBUC`, a continuous linear map into the
bounded continuous functions on `Q`. This file shows that before the terminal time this solution is
a classical one, with the Schauder estimate weighted by the distance to the terminal time.

For `0 < δ < T`, the solution restricted to `ℝⁿ × [0, T - δ]` is given by a continuous linear map
`euclideanTerminalSolutionBUCRestrictL` from `C_b^{α,α/2}(Q) × BUC(ℝⁿ)` to
`C_b^{2+α,1+α/2}(ℝⁿ × [0, T - δ])`, whose values are those of `euclideanTerminalSolutionBUC`
(`euclideanTerminalSolutionBUCRestrictL_apply`), which solves `P_back u = f` there
(`euclideanBackwardParabolicOperatorL_euclideanTerminalSolutionBUCRestrictL`), and which satisfies

`δ^(1 + α/2) ‖u‖_{2+α,par;[0,T-δ]} ≤ C max (‖f‖_{α,par}, sup |g|)`

uniformly in `0 < δ < T`, in the coefficients with given ellipticity and Hölder bounds, and in
horizons `T ≤ T₀` (`exists_rpow_mul_norm_euclideanTerminalSolutionBUCRestrictL_le`). These are the
time reversals of the corresponding statements for the Cauchy problem at positive times
(`TauCeti.ParabolicC2HolderSpace.euclideanCauchySolutionBUCRestrictL`).

## The argument

On a bounded `C^{2,α}` terminal datum the classical solution of the terminal-value problem exists
(`TauCeti.ParabolicC2HolderSpace.euclideanTerminalDataCLE`), and the Schauder estimate before the
terminal time (in the `TauCeti.ParabolicC2HolderSpace` namespace,
`exists_rpow_mul_norm_restrictL_le_euclideanBackwardParabolicOperatorL`) bounds its restriction
to `ℝⁿ × [0, T - δ]` by `C δ^(-(1 + α/2)) (‖f‖_{α,par} + sup |g|)`, with only the supremum of the
terminal datum on the right. So the restricted classical solution map
extends by continuity from `C_b^{2,α}` to its closure `BUC` in the supremum norm. The value at a
point and the backward operator are continuous on `C_b^{2+α,1+α/2}`, so the identification with
`euclideanTerminalSolutionBUC` and the equation pass to the limit from smooth terminal data.

## Main declarations

All declarations are in the `TauCeti.ParabolicC2HolderSpace` namespace.

* `euclideanTerminalSolutionBUCRestrictL`: the solution on `ℝⁿ × [0, T - δ]` as a
  `C_b^{2+α,1+α/2}` map.
* `euclideanTerminalSolutionBUCRestrictL_toBUC`: on `C_b^{2,α}` terminal data it is the restricted
  classical solution.
* `euclideanTerminalSolutionBUCRestrictL_apply`: it is the extended solution.
* `euclideanBackwardParabolicOperatorL_euclideanTerminalSolutionBUCRestrictL`: it solves the
  backward equation.
* `exists_rpow_mul_norm_euclideanTerminalSolutionBUCRestrictL_le`: the Schauder estimate before
  the terminal time for bounded uniformly continuous terminal data.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4
  (solutions with continuous data as limits of solutions with smooth data).
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2, Section 4 (backward
  equations and time reversal).
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime BoundedContinuousFunction
open CkHolderSpace (toBUC toBUC_apply)
open scoped NNReal

variable {α : ℝ≥0} {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0} (hα₀ : 0 < α) (hα₁ : α < 1)

/-- The classical solution `(f, g) ↦ u` of the terminal-value problem with `C_b^{2,α}` terminal
datum, restricted to `ℝⁿ × [0, T - δ]`. -/
private def restrictedTerminalSolution (hT : (0 : ℝ) < T)
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {δ : ℝ} (hδ : 0 < δ) (hδT : δ < T) :
    HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ →ₗ[ℝ]
        ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ (sub_pos.2 hδT) :=
  ((restrictL le_rfl (sub_le_self (T : ℝ) hδ.le) (sub_pos.2 hδT)).comp
    (euclideanTerminalDataCLE hα₀ hα₁ hT a b c ha).symm.toContinuousLinearMap).toLinearMap

private theorem restrictedTerminalSolution_apply (hT : (0 : ℝ) < T)
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {δ : ℝ} (hδ : 0 < δ) (hδT : δ < T)
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    restrictedTerminalSolution hα₀ hα₁ hT a b c ha hδ hδT d =
      restrictL le_rfl (sub_le_self (T : ℝ) hδ.le) (sub_pos.2 hδT)
        ((euclideanTerminalDataCLE hα₀ hα₁ hT a b c ha).symm d) :=
  (rfl)

/-- The weighted Schauder estimate before the terminal time for the classical solutions, in the
norm of the data space `C_b^{α,α/2} × BUC`:
`‖u‖_{2+α,par;[0,T-δ]} ≤ C / δ^(1 + α/2) * max (‖f‖, ‖g‖_∞)`, uniformly over the coefficients and
horizons in the given bounds. -/
private theorem exists_norm_restrictedTerminalSolution_le_div {lam : ℝ} (hlam : 0 < lam)
    (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ {δ : ℝ} (hδ : 0 < δ) (hδT : δ < T)
          (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
            CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ),
          ‖restrictedTerminalSolution hα₀ hα₁ hT a b c ⟨lam, hlam, ha⟩ hδ hδT d‖ ≤
            C / δ ^ (1 + (α : ℝ) / 2) * ‖euclideanCauchyDataToBUC d‖ := by
  obtain ⟨C, hC, hest⟩ :=
    exists_rpow_mul_norm_restrictL_le_euclideanBackwardParabolicOperatorL (ι := ι) hα₀ hα₁
      (Lam := ∑ _i : ι, ∑ _j : ι, (K : ℝ)) hlam K T₀
  refine ⟨2 * C, by positivity, fun T hT hTT₀ a b c ha hak hbk hck δ hδ hδT d ↦ ?_⟩
  -- The terminal values of the classical solution are bounded by the supremum norm of the datum.
  have hterm (x : EuclideanSpace ℝ ι) :
      |(euclideanTerminalDataCLE hα₀ hα₁ hT a b c ⟨lam, hlam, ha⟩).symm d
        (slabMk x ⟨T, right_mem_Icc.2 hT.le⟩)| ≤ ‖toBUC d.2‖ := by
    rw [euclideanTerminalDataCLE_symm_apply_slabMk_right, ← toBUC_apply, ← Real.norm_eq_abs,
      ← ClosedSubmodule.norm_coe]
    exact norm_coe_le_norm _ x
  have h := hest T hT hTT₀ a b c ha (toQuadraticForm'_le_of_norm_coeff_le hak) hak hbk hck _
    hterm hδ hδT
  rw [euclideanBackwardParabolicOperatorL_euclideanTerminalDataCLE_symm_apply] at h
  have hf : ‖d.1‖ ≤ ‖euclideanCauchyDataToBUC d‖ := by simp
  have hg : ‖toBUC d.2‖ ≤ ‖euclideanCauchyDataToBUC d‖ := by simp
  rw [restrictedTerminalSolution_apply, div_mul_eq_mul_div,
    le_div_iff₀' (Real.rpow_pos_of_pos hδ _)]
  nlinarith

variable (hT : (0 : ℝ) < T) (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
  (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
  (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
  (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
  {δ : ℝ} (hδ : 0 < δ) (hδT : δ < T)

/-- **The terminal-value solution before the terminal time.** For `0 < δ < T`, the restriction to
`ℝⁿ × [0, T - δ]` of the solution of the terminal-value problem `P_back u = f`, `u(·, T) = g` with
bounded uniformly continuous terminal datum `g`, as a continuous linear map
`C_b^{α,α/2}(ℝⁿ × [0, T]) × BUC(ℝⁿ) →L[ℝ] C_b^{2+α,1+α/2}(ℝⁿ × [0, T - δ])`. Its values are those
of `euclideanTerminalSolutionBUC` (`euclideanTerminalSolutionBUCRestrictL_apply`), so the extended
solution is a classical solution before the terminal time
(`euclideanBackwardParabolicOperatorL_euclideanTerminalSolutionBUCRestrictL`). -/
def euclideanTerminalSolutionBUCRestrictL :
    HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ →L[ℝ]
        ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ (sub_pos.2 hδT) :=
  (restrictedTerminalSolution hα₀ hα₁ hT a b c ha hδ hδT).extendOfNorm euclideanCauchyDataToBUC

variable {a b c}

private theorem euclideanTerminalSolutionBUCRestrictL_euclideanCauchyDataToBUC
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    euclideanTerminalSolutionBUCRestrictL hα₀ hα₁ hT a b c ha hδ hδT
        (euclideanCauchyDataToBUC d) =
      restrictL le_rfl (sub_le_self (T : ℝ) hδ.le) (sub_pos.2 hδT)
        ((euclideanTerminalDataCLE hα₀ hα₁ hT a b c ha).symm d) :=
  LinearMap.extendOfNorm_eq (denseRange_euclideanCauchyDataToBUC hα₁.le) (by
    obtain ⟨lam, hlam, hlam'⟩ := ha
    obtain ⟨K, hak, hbk, hck⟩ := exists_norm_coeff_le a b c
    obtain ⟨C, -, hC⟩ :=
      exists_norm_restrictedTerminalSolution_le_div (ι := ι) hα₀ hα₁ hlam K T
    -- `convert` matches the instance arguments of the coercion of `restrictedTerminalSolution`
    -- with those in the statement of `extendOfNorm_eq`; `exact` would instead unfold the norm of
    -- the order-two space, whose carrier is not exposed here.
    exact ⟨C / δ ^ (1 + (α : ℝ) / 2), fun d ↦ by
      convert hC T hT le_rfl a b c hlam' hak hbk hck hδ hδT d using 2⟩) d

/-- **Agreement with the classical solution.** On a bounded `C^{2,α}` terminal datum `g`, the
solution before the terminal time is the restriction to `ℝⁿ × [0, T - δ]` of the solution in
`C_b^{2+α,1+α/2}(ℝⁿ × [0, T])` of `P_back u = f`, `u(·, T) = g`. -/
@[simp]
theorem euclideanTerminalSolutionBUCRestrictL_toBUC
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    euclideanTerminalSolutionBUCRestrictL hα₀ hα₁ hT a b c ha hδ hδT (f, toBUC g) =
      restrictL le_rfl (sub_le_self (T : ℝ) hδ.le) (sub_pos.2 hδT)
        ((euclideanTerminalDataCLE hα₀ hα₁ hT a b c ha).symm (f, g)) := by
  have h := euclideanTerminalSolutionBUCRestrictL_euclideanCauchyDataToBUC hα₀ hα₁ hT (b := b)
    (c := c) ha hδ hδT (f, g)
  rwa [euclideanCauchyDataToBUC_apply] at h

/-- **The extended solution is `C^{2+α,1+α/2}` before the terminal time.** On
`ℝⁿ × [0, T - δ]`, the values of `euclideanTerminalSolutionBUCRestrictL` are those of the extended
solution `euclideanTerminalSolutionBUC`. -/
@[simp]
theorem euclideanTerminalSolutionBUCRestrictL_apply
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ)
    (p : slab (E := EuclideanSpace ℝ ι) 0 (T - δ)) :
    euclideanTerminalSolutionBUCRestrictL hα₀ hα₁ hT a b c ha hδ hδT d p =
      euclideanTerminalSolutionBUC hα₀ hα₁ hT a b c ha d
        (inclusion (slab_subset_slab le_rfl (sub_le_self (T : ℝ) hδ.le)) p) := by
  refine (denseRange_euclideanCauchyDataToBUC hα₁.le).induction_on
    (p := fun d ↦ euclideanTerminalSolutionBUCRestrictL hα₀ hα₁ hT a b c ha hδ hδT d p =
      euclideanTerminalSolutionBUC hα₀ hα₁ hT a b c ha d
        (inclusion (slab_subset_slab le_rfl (sub_le_self (T : ℝ) hδ.le)) p)) d ?_ fun d ↦ ?_
  · refine isClosed_eq ?_ ?_
    · simp_rw [← valueL_apply]
      exact (continuous_eval_const p).comp (valueL.continuous.comp
        (euclideanTerminalSolutionBUCRestrictL hα₀ hα₁ hT a b c ha hδ hδT).continuous)
    · exact (continuous_eval_const _).comp
        (euclideanTerminalSolutionBUC hα₀ hα₁ hT a b c ha).continuous
  · obtain ⟨f, g⟩ := d
    rw [euclideanTerminalSolutionBUCRestrictL_euclideanCauchyDataToBUC,
      euclideanCauchyDataToBUC_apply, euclideanTerminalSolutionBUC_toBUC, restrictL_apply,
      valueL_apply]

/-- **The extended solution is a classical solution before the terminal time.** On
`ℝⁿ × [0, T - δ]`, `euclideanTerminalSolutionBUCRestrictL` solves `P_back u = f`, where `P_back`
has the coefficients `aⁱʲ`, `bⁱ`, `c` restricted to `ℝⁿ × [0, T - δ]`. -/
theorem euclideanBackwardParabolicOperatorL_euclideanTerminalSolutionBUCRestrictL
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (w : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) :
    euclideanBackwardParabolicOperatorL hα₁.le
        (fun i j ↦ HolderSpace.compLipschitzL _
          (LipschitzWith.inclusion (slab_subset_slab le_rfl (sub_le_self (T : ℝ) hδ.le))) (a i j))
        (fun i ↦ HolderSpace.compLipschitzL _
          (LipschitzWith.inclusion (slab_subset_slab le_rfl (sub_le_self (T : ℝ) hδ.le))) (b i))
        (HolderSpace.compLipschitzL _
          (LipschitzWith.inclusion (slab_subset_slab le_rfl (sub_le_self (T : ℝ) hδ.le))) c)
        (euclideanTerminalSolutionBUCRestrictL hα₀ hα₁ hT a b c ha hδ hδT (f, w)) =
      HolderSpace.compLipschitzL _
        (LipschitzWith.inclusion (slab_subset_slab le_rfl (sub_le_self (T : ℝ) hδ.le))) f := by
  set R := HolderSpace.compLipschitzL (α := α) (Y := ℝ) _
    (LipschitzWith.inclusion (slab_subset_slab (E := EuclideanSpace ℝ ι) le_rfl
      (sub_le_self (T : ℝ) hδ.le)))
  -- Both sides are continuous linear in the data, and they agree on `C_b^{2,α}` terminal data.
  have h : euclideanBackwardParabolicOperatorL hα₁.le (fun i j ↦ R (a i j)) (fun i ↦ R (b i))
      (R c) ∘L euclideanTerminalSolutionBUCRestrictL hα₀ hα₁ hT a b c ha hδ hδT =
        R ∘L ContinuousLinearMap.fst ℝ _ _ := by
    refine ContinuousLinearMap.ext fun d ↦
      (denseRange_euclideanCauchyDataToBUC hα₁.le).induction_on
      (p := fun d ↦ (euclideanBackwardParabolicOperatorL hα₁.le (fun i j ↦ R (a i j))
        (fun i ↦ R (b i)) (R c) ∘L
          euclideanTerminalSolutionBUCRestrictL hα₀ hα₁ hT a b c ha hδ hδT) d =
        (R ∘L ContinuousLinearMap.fst ℝ _ _) d) d
      (isClosed_eq (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _))
      fun d ↦ ?_
    rw [ContinuousLinearMap.comp_apply,
      euclideanTerminalSolutionBUCRestrictL_euclideanCauchyDataToBUC,
      euclideanBackwardParabolicOperatorL_restrictL,
      euclideanBackwardParabolicOperatorL_euclideanTerminalDataCLE_symm_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', euclideanCauchyDataToBUC_apply]
  exact congrArg (fun L ↦ L (f, w)) h

/-- **Schauder estimate before the terminal time for bounded uniformly continuous data.** For
`0 < α < 1`, an ellipticity constant `λ > 0`, a bound `K` on the Hölder norms of the coefficients
and a bound `T₀` on the horizon, there is a constant `C` such that the extended solution `u` of
`P_back u = f`, `u(·, T) = g` on `ℝⁿ × [0, T]`, `T ≤ T₀`, satisfies for every `0 < δ < T`

`δ^(1 + α/2) ‖u‖_{2+α,par;[0,T-δ]} ≤ C max (‖f‖_{α,par}, ‖g‖_∞)`,

where `‖u‖_{2+α,par;[0,T-δ]}` is the `C_b^{2+α,1+α/2}` norm of `u` on `ℝⁿ × [0, T - δ]`. -/
theorem exists_rpow_mul_norm_euclideanTerminalSolutionBUCRestrictL_le {lam : ℝ} (hlam : 0 < lam)
    (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ {δ : ℝ} (hδ : 0 < δ) (hδT : δ < T)
          (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
            uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ),
          δ ^ (1 + (α : ℝ) / 2) *
              ‖euclideanTerminalSolutionBUCRestrictL hα₀ hα₁ hT a b c ⟨lam, hlam, ha⟩ hδ hδT d‖ ≤
            C * ‖d‖ := by
  obtain ⟨C, hC, hest⟩ :=
    exists_norm_restrictedTerminalSolution_le_div (ι := ι) hα₀ hα₁ hlam K T₀
  refine ⟨C, hC, fun T hT hTT₀ a b c ha hak hbk hck δ hδ hδT d ↦ ?_⟩
  have hδα : 0 < δ ^ (1 + (α : ℝ) / 2) := Real.rpow_pos_of_pos hδ _
  -- As in `euclideanTerminalSolutionBUCRestrictL_euclideanCauchyDataToBUC`, `convert` matches the
  -- instance arguments of the coercions in the statement of `norm_extendOfNorm_apply_le` with ours.
  have h := LinearMap.norm_extendOfNorm_apply_le (denseRange_euclideanCauchyDataToBUC hα₁.le)
    (C / δ ^ (1 + (α : ℝ) / 2)) (fun d' ↦ by
      convert hest T hT hTT₀ a b c ha hak hbk hck hδ hδT d' using 2) d
  rw [euclideanTerminalSolutionBUCRestrictL]
  convert (le_div_iff₀' hδα).1 (h.trans_eq (div_mul_eq_mul_div _ _ _)) using 2

end TauCeti.ParabolicC2HolderSpace
