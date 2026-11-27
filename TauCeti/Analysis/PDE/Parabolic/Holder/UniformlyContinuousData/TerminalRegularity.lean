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

Time reversal `R (x, s) = (x, T - s)` turns `P_back` into a forward operator with the reversed
coefficients (`TauCeti.ParabolicC2HolderSpace.euclideanParabolicOperatorL_timeReverseLIE`), the
terminal-value problem into a Cauchy problem, and `ℝⁿ × [0, T - δ]` into `ℝⁿ × [δ, T]`; this is how
`euclideanTerminalSolutionBUC` is built from `euclideanCauchySolutionBUC`. So
`euclideanTerminalSolutionBUCRestrictL` is the time reversal of
`TauCeti.ParabolicC2HolderSpace.euclideanCauchySolutionBUCRestrictL` with the reversed coefficients
and data, and its properties are those of the forward operator. The weighted estimate keeps its
constant because time reversal is an isometry and does not increase the norm of the data.

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
open CkHolderSpace (toBUC)
open scoped NNReal

variable {α : ℝ≥0} {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0} (hα₀ : 0 < α) (hα₁ : α < 1)
  (hT : (0 : ℝ) < T) (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
  (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
  (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
  (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
  {δ : ℝ} (hδ : 0 < δ) (hδT : δ < T)

/-- **The terminal-value solution before the terminal time.** For `0 < δ < T`, the restriction to
`ℝⁿ × [0, T - δ]` of the solution of the terminal-value problem `P_back u = f`, `u(·, T) = g` with
bounded uniformly continuous terminal datum `g`, as a continuous linear map
`C_b^{α,α/2}(ℝⁿ × [0, T]) × BUC(ℝⁿ) →L[ℝ] C_b^{2+α,1+α/2}(ℝⁿ × [0, T - δ])`. It is the time
reversal `R (x, s) = (x, T - s)` of `euclideanCauchySolutionBUCRestrictL` with the coefficients
`aⁱʲ ∘ R`, `bⁱ ∘ R`, `c ∘ R` and data `(-f ∘ R, g)`. Its values are those of
`euclideanTerminalSolutionBUC` (`euclideanTerminalSolutionBUCRestrictL_apply`), so the extended
solution is a classical solution before the terminal time
(`euclideanBackwardParabolicOperatorL_euclideanTerminalSolutionBUCRestrictL`). -/
def euclideanTerminalSolutionBUCRestrictL :
    HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ →L[ℝ]
        ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ (sub_pos.2 hδT) :=
  (timeReverseLIE (E := EuclideanSpace ℝ ι) (F := ℝ) (α := α) (hab := hδT) (T : ℝ)
      (sub_self (T : ℝ)).symm rfl).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((euclideanCauchySolutionBUCRestrictL hα₀ hα₁ hT
      (fun i j ↦ HolderSpace.compLipschitzL _
        (slabTimeReverse (T : ℝ) (sub_self _).symm (sub_zero _).symm).isometry.lipschitzWith
          (a i j))
      (fun i ↦ HolderSpace.compLipschitzL _
        (slabTimeReverse (T : ℝ) (sub_self _).symm (sub_zero _).symm).isometry.lipschitzWith (b i))
      (HolderSpace.compLipschitzL _
        (slabTimeReverse (T : ℝ) (sub_self _).symm (sub_zero _).symm).isometry.lipschitzWith c)
      (ha.imp fun _ h ↦ ⟨h.1, mul_norm_sq_le_toQuadraticForm'_compLipschitzL _ h.2⟩) hδ hδT).comp
      (ContinuousLinearMap.prodMap (-HolderSpace.compLipschitzL _
        (slabTimeReverse (T : ℝ) (sub_self _).symm (sub_zero _).symm).isometry.lipschitzWith)
        (ContinuousLinearMap.id ℝ _)))

variable {a b c}

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
  obtain ⟨f, w⟩ := d
  rw [euclideanTerminalSolutionBUC_apply_eq_euclideanCauchySolutionBUC hα₀ hα₁ hT ha
    (ha.imp fun _ h ↦ ⟨h.1, mul_norm_sq_le_toQuadraticForm'_compLipschitzL _ h.2⟩)]
  simp only [euclideanTerminalSolutionBUCRestrictL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply, ContinuousLinearMap.id_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    timeReverseLIE_apply, euclideanCauchySolutionBUCRestrictL_apply]
  congr 1
  ext <;> simp

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
  ext p
  rw [euclideanTerminalSolutionBUCRestrictL_apply, euclideanTerminalSolutionBUC_toBUC,
    restrictL_apply, valueL_apply]

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
  set R := slabTimeReverse (E := EuclideanSpace ℝ ι) (T : ℝ) (sub_self (T : ℝ)).symm
    (sub_zero (T : ℝ)).symm
  set S := slabTimeReverse (E := EuclideanSpace ℝ ι) (T : ℝ) (sub_self (T : ℝ)).symm
    (rfl : (T : ℝ) - δ = T - δ)
  ext p
  -- The forward equation of the reversed problem at `S p` is the backward equation at `p`.
  have h := congrArg (fun g ↦ g (S p))
    (euclideanParabolicOperatorL_euclideanCauchySolutionBUCRestrictL hα₀ hα₁ hT
      (a := fun i j ↦ HolderSpace.compLipschitzL _ R.isometry.lipschitzWith (a i j))
      (b := fun i ↦ HolderSpace.compLipschitzL _ R.isometry.lipschitzWith (b i))
      (c := HolderSpace.compLipschitzL _ R.isometry.lipschitzWith c)
      (ha.imp fun _ h ↦ ⟨h.1, mul_norm_sq_le_toQuadraticForm'_compLipschitzL _ h.2⟩) hδ hδT
      (-HolderSpace.compLipschitzL _ R.isometry.lipschitzWith f) w)
  have hp : R (inclusion (slab_subset_slab hδ.le le_rfl) (S p)) =
      inclusion (slab_subset_slab le_rfl (sub_le_self (T : ℝ) hδ.le)) p := by
    ext <;> simp [R, S]
  simp only [euclideanParabolicOperatorL_apply, HolderSpace.compLipschitzL_apply,
    HolderSpace.neg_apply, hp] at h
  simp only [euclideanTerminalSolutionBUCRestrictL, euclideanBackwardParabolicOperatorL_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_prodMap', Prod.map_apply,
    ContinuousLinearMap.id_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, timeReverseLIE_apply, timeDerivL_timeReverseLIE,
    spatialFDerivL_timeReverseLIE, spatialSecondFDerivL_timeReverseLIE,
    HolderSpace.compLipschitzL_apply, _root_.neg_apply]
  simp only [R, S] at h
  linarith

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
    exists_rpow_mul_norm_euclideanCauchySolutionBUCRestrictL_le (ι := ι) hα₀ hα₁ hlam K T₀
  refine ⟨C, hC, fun T hT hTT₀ a b c ha hak hbk hck δ hδ hδT ⟨f, w⟩ ↦ ?_⟩
  set R := slabTimeReverse (E := EuclideanSpace ℝ ι) (T : ℝ) (sub_self (T : ℝ)).symm
    (sub_zero (T : ℝ)).symm
  have hR (g : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) :
      ‖HolderSpace.compLipschitzL _ R.isometry.lipschitzWith g‖ ≤ ‖g‖ :=
    HolderSpace.norm_compLipschitzL_apply_le _ g
  -- The forward estimate for the reversed coefficients and data; reversing the data does not
  -- increase its norm, and reversing the solution keeps it.
  have h := hest T hT hTT₀ _ _ _ (mul_norm_sq_le_toQuadraticForm'_compLipschitzL _ ha)
    (fun i j ↦ (hR _).trans (hak i j)) (fun i ↦ (hR _).trans (hbk i)) ((hR c).trans hck) hδ hδT
    (-HolderSpace.compLipschitzL _ R.isometry.lipschitzWith f, w)
  have hd : ‖(-HolderSpace.compLipschitzL _ R.isometry.lipschitzWith f, w)‖ ≤ ‖(f, w)‖ := by
    simp only [Prod.norm_def, norm_neg]
    exact max_le_max (hR f) le_rfl
  refine le_trans (le_of_eq ?_) (h.trans (mul_le_mul_of_nonneg_left hd hC))
  simp only [euclideanTerminalSolutionBUCRestrictL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply, ContinuousLinearMap.id_apply,
    _root_.neg_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.norm_map, R]

end TauCeti.ParabolicC2HolderSpace
