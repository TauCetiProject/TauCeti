/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.ConstantCoefficient.CauchyPotential
public import TauCeti.Analysis.PDE.Parabolic.Holder.DuhamelPotential.Basic
import TauCeti.Analysis.Normed.Operator.Prod

/-!
# The inhomogeneous constant-coefficient parabolic Cauchy problem

Let `A` be a constant matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `0 < λ`, and write
`P_A u = ∂ₜu - ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` on the slab `ℝⁿ × [0, T]`. For `0 < α < 1`, forcing
`f ∈ C_b^{α,α/2}` and initial datum `g ∈ C_b^{2,α}`, the Cauchy problem

`P_A u = f`,  `u(·, 0) = g`

has a unique solution `u` in the bounded order-two parabolic Hölder space `C_b^{2+α,1+α/2}`. The
solution depends linearly on `(f, g)`, with operator norm at most `C (1 + T)`, where `C` depends
only on `λ`, `Λ`, `α` and the dimension. Equivalently, `u ↦ (P_A u, u(·, 0))` is a bijection
`C_b^{2+α,1+α/2} → C_b^{α,α/2} × C_b^{2,α}`, and every `u` satisfies the a priori estimate

`‖u‖_{2+α,par} ≤ C (1 + T) (‖P_A u‖_{α,par} + ‖u(·, 0)‖_{2,α})`.

No symmetry of `A` is needed. This constant-coefficient estimate is the model that the Schauder
theory for variable coefficients perturbs by freezing the coefficients, and the heat operator
`A = 1` is the starting point of the method of continuity.

The solution is the sum of the solution of the homogeneous problem with datum `g`
(`TauCeti.ParabolicC2HolderSpace.exists_solutionOperator_euclideanParabolicOperatorL_const`) and
the Duhamel heat potential of `f` (`TauCeti.heatDuhamelPotentialL`), transported through the
linear change of spatial variables that turns `P_A` into the heat operator
(`exists_continuousLinearEquiv_euclideanParabolicOperatorL_compSpatialL_eq`, in the namespace
`TauCeti.ParabolicC2HolderSpace`).
Uniqueness is that of the homogeneous problem.

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.exists_solutionOperator_euclideanParabolicOperatorL_const_prod`:
  the bounded solution operator `(f, g) ↦ u`, uniform over the ellipticity class.
* `TauCeti.ParabolicC2HolderSpace.bijective_euclideanParabolicOperatorL_const_prod_spatialTraceL`:
  `u ↦ (P_A u, u(·, 0))` is bijective.
* `TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL_const`: the a priori
  estimate.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.1 (linear reduction of a constant elliptic principal part).
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime
open scoped NNReal

variable {α : ℝ≥0} {ι : Type*} [Fintype ι] {T : ℝ≥0}

/-- The Duhamel heat potential transported by a linear change of spatial variables `e`:
`f ↦ D(f ∘ (e × id)) ∘ (e⁻¹ × id)`. -/
private def transportedDuhamelL (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) :
    HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ →L[ℝ]
      ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT :=
  (compSpatialL α ℝ hT e.symm.toContinuousLinearMap).comp
    ((heatDuhamelPotentialL hα₀ hα₁ hT).comp
      (HolderSpace.compLipschitzL _
        (lipschitzWith_slabSpaceMap e.toContinuousLinearMap.lipschitzWith)))

private theorem spatialTrace_transportedDuhamelL (hα₀ : 0 < α) (hα₁ : α < 1)
    (hT : (0 : ℝ) < T) (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) (f) :
    (transportedDuhamelL hα₀ hα₁ hT e f).spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ = 0 := by
  simp [transportedDuhamelL]

private theorem operator_transportedDuhamelL [DecidableEq ι] (hα₀ : 0 < α) (hα₁ : α < 1)
    (hT : (0 : ℝ) < T) (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) (A : Matrix ι ι ℝ)
    (he : ∀ u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
      euclideanParabolicOperatorL hα₁.le
          (fun i j ↦ HolderSpace.const ((1 : Matrix ι ι ℝ) i j)) 0 0
          (compSpatialL α ℝ hT e.toContinuousLinearMap u) =
        HolderSpace.compLipschitzL _
          (lipschitzWith_slabSpaceMap e.toContinuousLinearMap.lipschitzWith)
          (euclideanParabolicOperatorL hα₁.le (fun i j ↦ HolderSpace.const (A i j)) 0 0 u))
    (f) :
    euclideanParabolicOperatorL hα₁.le (fun i j ↦ HolderSpace.const (A i j)) 0 0
      (transportedDuhamelL hα₀ hα₁ hT e f) = f := by
  rw [transportedDuhamelL, ContinuousLinearMap.comp_apply,
    euclideanParabolicOperatorL_compSpatialL_symm_eq hα₁.le e he, ContinuousLinearMap.comp_apply,
    euclideanParabolicOperatorL_heatDuhamelPotentialL]
  ext p
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  simp only [HolderSpace.compLipschitzL_apply, slabSpaceMap_slabMk,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

private theorem norm_transportedDuhamelL_le (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) {K : ℝ} (hK : 1 ≤ K)
    (he : ‖e.toContinuousLinearMap‖ ≤ K) (hei : ‖e.symm.toContinuousLinearMap‖ ≤ K) :
    ‖transportedDuhamelL hα₀ hα₁ hT e‖ ≤
      (K ^ 2 * K ^ (α : ℝ)) * ‖heatDuhamelPotentialL (E := EuclideanSpace ℝ ι) (F := ℝ)
        hα₀ hα₁ hT‖ * K ^ (α : ℝ) := by
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hR := norm_compSpatialL_le_of_norm_le α ℝ hT hK hei
  have hJ : ‖HolderSpace.compLipschitzL (α := α) (Y := ℝ) _
      (lipschitzWith_slabSpaceMap (a := 0) (b := T)
        e.toContinuousLinearMap.lipschitzWith)‖ ≤ K ^ (α : ℝ) := by
    refine (HolderSpace.norm_compLipschitzL_le _).trans
      (max_le (Real.one_le_rpow hK (by positivity)) ?_)
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    rw [NNReal.coe_max, coe_nnnorm, NNReal.coe_one]
    exact max_le he hK
  calc ‖transportedDuhamelL hα₀ hα₁ hT e‖
      ≤ ‖compSpatialL α ℝ hT e.symm.toContinuousLinearMap‖ *
          (‖heatDuhamelPotentialL (E := EuclideanSpace ℝ ι) (F := ℝ) hα₀ hα₁ hT‖ *
            ‖HolderSpace.compLipschitzL (α := α) (Y := ℝ) _
              (lipschitzWith_slabSpaceMap (a := 0) (b := T)
                e.toContinuousLinearMap.lipschitzWith)‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (K ^ 2 * K ^ (α : ℝ)) * (‖heatDuhamelPotentialL (E := EuclideanSpace ℝ ι) (F := ℝ)
          hα₀ hα₁ hT‖ * K ^ (α : ℝ)) := by gcongr
    _ = _ := by ring

/-- **The bounded solution operator of the constant-coefficient Cauchy problem.** For
`0 < α < 1` and fixed ellipticity bounds `0 < lam` and `Lam`, there is a constant `C` such that for
every matrix `A` with `lam ‖ξ‖² ≤ ξᵀ A ξ ≤ Lam ‖ξ‖²` and every horizon `T > 0` the problem
`∂ₜu - ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = f`, `u(·, 0) = g` on `ℝⁿ × [0, T]` has, for all forcing
`f ∈ C_b^{α,α/2}` and initial data `g ∈ C_b^{2,α}`, exactly one solution
`u ∈ C_b^{2+α,1+α/2}`, namely `L (f, g)` for a continuous linear map `L` of norm at most
`C (1 + T)`. No symmetry of the matrix is needed: only its symmetric part enters the operator. -/
theorem exists_solutionOperator_euclideanParabolicOperatorL_const_prod [DecidableEq ι]
    (hα₀ : 0 < α) (hα₁ : α < 1) {lam Lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : Matrix ι ι ℝ,
      (∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      (∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T),
      ∃ L : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
            CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ →L[ℝ]
          ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
        ‖L‖ ≤ C * (1 + T) ∧ ∀ f g u,
          (euclideanParabolicOperatorL hα₁.le (fun i j ↦ HolderSpace.const (A i j)) 0 0 u = f ∧
            u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ = g) ↔ u = L (f, g) := by
  -- `L (f, g) = D f + L₀ g`, where `L₀` solves the homogeneous problem and `D` is the Duhamel
  -- potential transported by the coordinate change `e` reducing `P_A` to the heat operator.
  obtain ⟨C₀, hC₀, hhom⟩ :=
    exists_solutionOperator_euclideanParabolicOperatorL_const (ι := ι) hα₁.le (Lam := Lam) hlam
  obtain ⟨CD, hCD⟩ :=
    exists_norm_heatDuhamelPotentialL_le (α := α) (E := EuclideanSpace ℝ ι) (F := ℝ) hα₀ hα₁
  let K := max 1 (max (Real.sqrt Lam) (Real.sqrt lam)⁻¹)
  have hK : 1 ≤ K := le_max_left _ _
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  -- The Duhamel constant is nonnegative, as it bounds a norm at the horizon `T = 1`.
  have hCD₀ : 0 ≤ CD := by
    have h := (norm_nonneg _).trans (hCD 1 one_pos)
    norm_num at h
    linarith
  refine ⟨C₀ + K ^ 2 * K ^ (α : ℝ) * CD * K ^ (α : ℝ), by positivity,
    fun A hA hA' T hT ↦ ?_⟩
  obtain ⟨L₀, hL₀, hL₀u⟩ := hhom A hA hA' T hT
  obtain ⟨e, hen, hein, he⟩ :=
    exists_continuousLinearEquiv_norm_le_euclideanParabolicOperatorL_compSpatialL_eq
      (hab := hT) hα₁.le hlam hA hA'
  set D := transportedDuhamelL hα₀ hα₁ hT e
  set P := euclideanParabolicOperatorL hα₁.le (fun i j ↦ HolderSpace.const (A i j)) 0 0
  set t₀ : Icc (0 : ℝ) T := ⟨0, left_mem_Icc.2 hT.le⟩
  have hPD : ∀ f, P (D f) = f := operator_transportedDuhamelL hα₀ hα₁ hT e A he
  have htrD : ∀ f, (D f).spatialTrace t₀ = 0 := spatialTrace_transportedDuhamelL hα₀ hα₁ hT e
  refine ⟨D.coprod L₀, ?_, fun f g u ↦ ?_⟩
  · have hT1 : (1 : ℝ) ≤ 1 + T := le_add_of_nonneg_right T.coe_nonneg
    have hD : ‖D‖ ≤ K ^ 2 * K ^ (α : ℝ) * CD * K ^ (α : ℝ) * (1 + T) := by
      refine (norm_transportedDuhamelL_le hα₀ hα₁ hT e hK hen hein).trans ?_
      have := hCD T hT
      calc K ^ 2 * K ^ (α : ℝ) * ‖heatDuhamelPotentialL (E := EuclideanSpace ℝ ι) (F := ℝ)
            hα₀ hα₁ hT‖ * K ^ (α : ℝ)
          ≤ K ^ 2 * K ^ (α : ℝ) * (CD * (1 + T)) * K ^ (α : ℝ) := by gcongr
        _ = _ := by ring
    refine (D.opNorm_coprod_le L₀).trans ?_
    calc ‖D‖ + ‖L₀‖ ≤ K ^ 2 * K ^ (α : ℝ) * CD * K ^ (α : ℝ) * (1 + T) + C₀ * (1 + T) :=
          add_le_add hD (hL₀.trans (le_mul_of_one_le_right hC₀ hT1))
      _ = _ := by ring
  · simp only [ContinuousLinearMap.coprod_apply]
    constructor
    · -- Subtracting the Duhamel part leaves a solution of the homogeneous problem.
      rintro ⟨hPu, htru⟩
      have h := (hL₀u g (u - D f)).1 ⟨by rw [map_sub, hPu, hPD, sub_self], by
        simp [htru, htrD]⟩
      rw [← h, add_sub_cancel]
    · rintro rfl
      have h := (hL₀u g (L₀ g)).2 rfl
      exact ⟨by rw [map_add, h.1, hPD, add_zero], by simp [h.2, htrD]⟩

/-- **The constant-coefficient Cauchy problem is well posed.** For `0 < α < 1`, a matrix `A`
with `lam ‖ξ‖² ≤ ξᵀ A ξ`, `0 < lam`, and a horizon `T > 0`, the map
`u ↦ (∂ₜu - ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu, u(·, 0))` from `C_b^{2+α,1+α/2}(ℝⁿ × [0, T])` to
`C_b^{α,α/2}(ℝⁿ × [0, T]) × C_b^{2,α}(ℝⁿ)` is bijective. -/
theorem bijective_euclideanParabolicOperatorL_const_prod_spatialTraceL [DecidableEq ι]
    (hα₀ : 0 < α) (hα₁ : α < 1) {A : Matrix ι ι ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hT : (0 : ℝ) < T) :
    Function.Bijective
      ((euclideanParabolicOperatorL hα₁.le (fun i j ↦ HolderSpace.const (A i j)) 0 0).prod
        (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩)) := by
  -- Every fixed matrix satisfies an upper ellipticity bound, so the uniform theorem applies.
  obtain ⟨_, _, hC⟩ :=
    exists_solutionOperator_euclideanParabolicOperatorL_const_prod (ι := ι) hα₀ hα₁
      (Lam := ‖PDE.matrixBilinearForm A‖) hlam
  obtain ⟨L, -, hL⟩ :=
    hC A hA (PDE.toQuadraticForm'_le_norm_matrixBilinearForm_mul_sq A) T hT
  refine ⟨fun u v huv ↦ ?_, fun fg ↦ ⟨L fg, ?_⟩⟩
  · simp only [ContinuousLinearMap.prod_apply, spatialTraceL_apply, Prod.mk.injEq] at huv
    exact ((hL _ _ u).1 ⟨rfl, rfl⟩).trans ((hL _ _ v).1 ⟨huv.1.symm, huv.2.symm⟩).symm
  · obtain ⟨h₁, h₂⟩ := (hL fg.1 fg.2 (L fg)).2 rfl
    simp only [ContinuousLinearMap.prod_apply, spatialTraceL_apply, h₁, h₂]

/-- **The constant-coefficient Schauder estimate.** For `0 < α < 1` and fixed ellipticity bounds
`0 < lam` and `Lam`, there is a constant `C` such that for every matrix `A` with
`lam ‖ξ‖² ≤ ξᵀ A ξ ≤ Lam ‖ξ‖²`, every horizon `T > 0` and every `u ∈ C_b^{2+α,1+α/2}` on
`ℝⁿ × [0, T]`,
`‖u‖ ≤ C (1 + T) (‖∂ₜu - ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu‖ + ‖u(·, 0)‖)`. -/
theorem exists_norm_le_euclideanParabolicOperatorL_const [DecidableEq ι]
    (hα₀ : 0 < α) (hα₁ : α < 1) {lam Lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : Matrix ι ι ℝ,
      (∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      (∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T) (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT),
        ‖u‖ ≤ C * (1 + T) *
          (‖euclideanParabolicOperatorL hα₁.le (fun i j ↦ HolderSpace.const (A i j)) 0 0 u‖ +
            ‖u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖) := by
  obtain ⟨C, hC₀, hC⟩ :=
    exists_solutionOperator_euclideanParabolicOperatorL_const_prod (ι := ι) hα₀ hα₁
      (Lam := Lam) hlam
  refine ⟨C, hC₀, fun A hA hA' T hT u ↦ ?_⟩
  obtain ⟨L, hL, hLu⟩ := hC A hA hA' T hT
  have hu := (hLu _ _ u).1 ⟨rfl, rfl⟩
  have h := L.le_opNorm
    (euclideanParabolicOperatorL hα₁.le (fun i j ↦ HolderSpace.const (A i j)) 0 0 u,
      u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩)
  rw [← hu, Prod.norm_mk] at h
  refine h.trans (mul_le_mul hL (max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _))
    (le_max_of_le_left (norm_nonneg _)) (by positivity))

end TauCeti.ParabolicC2HolderSpace
