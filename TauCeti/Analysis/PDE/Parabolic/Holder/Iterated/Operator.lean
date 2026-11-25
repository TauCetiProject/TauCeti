/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Bilinear
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.CompLeft
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Differentiation
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Inclusion
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.LowOrder
public import TauCeti.Analysis.PDE.Parabolic.Holder.Operator
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Second-order parabolic operators on the parabolic Hölder spaces of every order

For coefficient fields `A`, `B`, `C` in the bounded parabolic Hölder space `C_{par,b}^{k+α}` of
order `k` on the slab `E × [a, b]` (`TauCeti.ParabolicCkHolderSpace`), with values in the
continuous linear maps on Hessians, gradients and values, this file defines the spatial operator
`L u = A·D_x²u + B·D_xu + C·u` and the parabolic operator `P u = ∂ₜu - L u` as bounded linear maps

`C_{par,b}^{k+2+α} → C_{par,b}^{k+α}`,

for `α ≤ 1`, together with the initial-data operator `u ↦ (P u, u(·, a))` into
`C_{par,b}^{k+α} × C_b^{k+2,α}`. Each term is a pointwise product of a coefficient with a
derivative of `u`, so the operators are bounded by the product estimate
`ContinuousLinearMap.norm_compParabolicCkHolder₂_le` and the inclusions between consecutive
orders. They are linear in the coefficients, with explicit operator bounds depending only on `k`,
so `P` depends Lipschitz continuously on its coefficients in operator norm. These are the
operators of the Schauder theory of parabolic equations at every order of differentiability: the
statement that the initial-data operator is an isomorphism for uniformly elliptic coefficients of
order `k` is the order-`k` form of the Cauchy problem.

At order `k = 0` the parabolic operator is the operator
`TauCeti.ParabolicC2HolderSpace.parabolicOperatorL` on `C_b^{2+α,1+α/2}`, under the
identifications `TauCeti.ParabolicCkHolderSpace.equivHolderSpace` and
`TauCeti.ParabolicCkHolderSpace.equivParabolicC2HolderSpace`
(`TauCeti.ParabolicCkHolderSpace.equivHolderSpace_parabolicOperatorL`); the initial-data operator
is the order-`k` form of `TauCeti.ParabolicC2HolderSpace.initialDataL`.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.spatialOperatorL` and
  `TauCeti.ParabolicCkHolderSpace.parabolicOperatorL`: the operators `L` and `P = ∂ₜ - L`, with
  their values in terms of the fields of `u`
  (`TauCeti.ParabolicCkHolderSpace.parabolicOperatorL_apply`) and in terms of the derivatives of
  its time slices (`TauCeti.ParabolicCkHolderSpace.parabolicOperatorL_slabMk`).
* `TauCeti.ParabolicCkHolderSpace.initialDataL`: the operator `u ↦ (P u, u(·, a))`.
* `TauCeti.ParabolicCkHolderSpace.norm_parabolicOperatorL_le`,
  `TauCeti.ParabolicCkHolderSpace.norm_parabolicOperatorL_sub_le`,
  `TauCeti.ParabolicCkHolderSpace.norm_initialDataL_le` and
  `TauCeti.ParabolicCkHolderSpace.norm_initialDataL_sub_le`: the operator bounds and the
  Lipschitz dependence on the coefficients.
* `TauCeti.ParabolicCkHolderSpace.equivHolderSpace_parabolicOperatorL`: agreement with the
  operator on `C_b^{2+α,1+α/2}` at order zero.
* `TauCeti.ParabolicCkHolderSpace.continuous_initialDataL` and
  `TauCeti.ParabolicCkHolderSpace.continuousAt_inverse_initialDataL`: continuity of the
  initial-data operator, and of the inverse of an invertible one, in the coefficients.
* `TauCeti.ParabolicCkHolderSpace.inclusionOfLEL_parabolicOperatorL`: the operator commutes with
  the inclusions between orders, as do its parts
  (`TauCeti.ParabolicCkHolderSpace.inclusionOfLEL_timeDerivL` and
  `TauCeti.ParabolicCkHolderSpace.inclusionOfLEL_spatialOperatorL`) and the initial data
  (`TauCeti.ParabolicCkHolderSpace.initialDataL_inclusionOfLEL_fst` and
  `TauCeti.ParabolicCkHolderSpace.coe_initialDataL_inclusionOfLEL_snd`).
* `TauCeti.ParabolicCkHolderSpace.euclideanSecondOrderCoeff`, `euclideanFirstOrderCoeff` and
  `euclideanZerothOrderCoeff`: the coefficient fields on `ℝⁿ` assembled from scalar coefficients,
  the order-`k` forms of `TauCeti.ParabolicC2HolderSpace.euclideanSecondOrderCoeff`,
  `euclideanFirstOrderCoeff` and `euclideanZerothOrderCoeff`, with which they agree at order zero
  (`TauCeti.ParabolicCkHolderSpace.equivHolderSpace_euclideanParabolicOperatorL`).

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section

noncomputable section

namespace TauCeti

open Set ParabolicSpaceTime
open scoped NNReal

namespace ParabolicCkHolderSpace

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/- The shortcut instances of `TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Differentiation` for
operator-valued fields. The spatial derivative takes values in spaces built with them, and the
gradient, the Hessian and the coefficient fields of this file must carry the same instances:
otherwise the kernel has to unfold the norm structures of operator spaces to identify them. -/
attribute [local instance] instNormedAddCommGroupContinuousLinearMapRealId
  instNormedSpaceRealContinuousLinearMapId

/-! ### The spatial operator -/

section Spatial

variable (hα : α ≤ 1) (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
  (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
  (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab)

/-- The spatial operator `L u = A·D_x²u + B·D_xu + C·u` as a function: the Hessian, the gradient
and the value of `u` are brought to the order `k` of the coefficients and multiplied pointwise. -/
private def spatialOperator (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    ParabolicCkHolderSpace k α E F hab :=
  (ContinuousLinearMap.id ℝ _).compParabolicCkHolder₂ hα A
      (spatialFDerivL k α E (E →L[ℝ] F) hab (spatialFDerivL (k + 1) α E F hab u)) +
    (ContinuousLinearMap.id ℝ _).compParabolicCkHolder₂ hα B
      (inclusionL hα (spatialFDerivL (k + 1) α E F hab u)) +
    (ContinuousLinearMap.id ℝ _).compParabolicCkHolder₂ hα C (inclusionL hα (inclusionL hα u))

private theorem spatialOperator_apply (u : ParabolicCkHolderSpace (k + 2) α E F hab)
    (p : slab (E := E) a b) :
    spatialOperator hα A B C u p =
      A p (continuousMultilinearCurryFin2 ℝ E F (mixedDerivL 0 2 u p)) +
        B p (spatialFDerivBCF u p) + C p (u p) := by
  simp only [spatialOperator, coe_add, Pi.add_apply,
    ContinuousLinearMap.compParabolicCkHolder₂_apply, ContinuousLinearMap.id_apply,
    inclusionL_apply]
  rw [spatialFDerivL_spatialFDerivL_apply, spatialFDerivL_apply_eq_spatialFDerivBCF]

/-- The spatial operator as a function, at a point `(x, t)`: the coefficients applied to the
second and first Fréchet derivatives and to the value of `u` on its time slice. -/
private theorem spatialOperator_slabMk (u : ParabolicCkHolderSpace (k + 2) α E F hab) (x : E)
    (t : Icc a b) :
    spatialOperator hα A B C u (slabMk x t) =
      A (slabMk x t) (fderiv ℝ (fderiv ℝ fun y ↦ u (slabMk y t)) x) +
        B (slabMk x t) (fderiv ℝ (fun y ↦ u (slabMk y t)) x) + C (slabMk x t) (u (slabMk x t)) := by
  have h : (fun y ↦ spatialFDerivL (k + 1) α E F hab u (slabMk y t)) =
      fderiv ℝ fun y ↦ u (slabMk y t) :=
    funext fun y ↦ spatialFDerivL_slabMk u y t
  simp only [spatialOperator, coe_add, Pi.add_apply,
    ContinuousLinearMap.compParabolicCkHolder₂_apply, ContinuousLinearMap.id_apply,
    inclusionL_apply]
  rw [spatialFDerivL_slabMk, h, spatialFDerivL_slabMk]

/-- The norm of a pointwise product with a coefficient of order `k` is at most
`21 (k + 1)² 2ᵏ ‖D‖ ‖v‖`. -/
private theorem norm_id_compParabolicCkHolder₂_apply_le {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (D : ParabolicCkHolderSpace k α E (G →L[ℝ] F) hab)
    (v : ParabolicCkHolderSpace k α E G hab) :
    ‖(ContinuousLinearMap.id ℝ _).compParabolicCkHolder₂ hα D v‖ ≤
      21 * (k + 1) ^ 2 * 2 ^ k * ‖D‖ * ‖v‖ := by
  refine (ContinuousLinearMap.norm_compParabolicCkHolder₂_apply_le _ hα D v).trans ?_
  have h₁ := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := G →L[ℝ] F)
  calc 21 * (k + 1) ^ 2 * 2 ^ k * ‖ContinuousLinearMap.id ℝ (G →L[ℝ] F)‖ * ‖D‖ * ‖v‖
      ≤ 21 * (k + 1) ^ 2 * 2 ^ k * 1 * ‖D‖ * ‖v‖ := by gcongr
    _ = _ := by ring

/-- The bound on the spatial operator. -/
private theorem norm_spatialOperator_le (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    ‖spatialOperator hα A B C u‖ ≤ 21 * (k + 1) ^ 2 * 2 ^ k *
      (‖A‖ + 8 * (k + 1) ^ 2 * ‖B‖ + 64 * (k + 1) ^ 2 * (k + 2) ^ 2 * ‖C‖) * ‖u‖ := by
  set K : ℝ := 21 * (k + 1) ^ 2 * 2 ^ k
  have hK : 0 ≤ K := by positivity
  have hA := norm_id_compParabolicCkHolder₂_apply_le hα A
    (spatialFDerivL k α E (E →L[ℝ] F) hab (spatialFDerivL (k + 1) α E F hab u))
  have hB := norm_id_compParabolicCkHolder₂_apply_le hα B
    (inclusionL hα (spatialFDerivL (k + 1) α E F hab u))
  have hC := norm_id_compParabolicCkHolder₂_apply_le hα C (inclusionL hα (inclusionL hα u))
  have h₂ : ‖spatialFDerivL k α E (E →L[ℝ] F) hab (spatialFDerivL (k + 1) α E F hab u)‖ ≤ ‖u‖ :=
    (norm_spatialFDerivL_le _).trans (norm_spatialFDerivL_le u)
  have h₁ : ‖inclusionL hα (spatialFDerivL (k + 1) α E F hab u)‖ ≤ 8 * (k + 1) ^ 2 * ‖u‖ :=
    ((inclusionL hα).le_opNorm _).trans
      (mul_le_mul (norm_inclusionL_le_mul_sq hα) (norm_spatialFDerivL_le u) (norm_nonneg _)
        (by positivity))
  have h₀ : ‖inclusionL hα (inclusionL hα u)‖ ≤
      8 * (k + 1) ^ 2 * (8 * ((k + 1 : ℕ) + 1) ^ 2 * ‖u‖) := by
    refine ((inclusionL hα).le_opNorm _).trans
      (mul_le_mul (norm_inclusionL_le_mul_sq hα) (((inclusionL hα).le_opNorm _).trans ?_)
        (norm_nonneg _) (by positivity))
    exact mul_le_mul_of_nonneg_right (norm_inclusionL_le_mul_sq (k := k + 1) hα) (norm_nonneg _)
  have hL : ‖spatialOperator hα A B C u‖ ≤
      ‖(ContinuousLinearMap.id ℝ _).compParabolicCkHolder₂ hα A
          (spatialFDerivL k α E (E →L[ℝ] F) hab (spatialFDerivL (k + 1) α E F hab u))‖ +
        ‖(ContinuousLinearMap.id ℝ _).compParabolicCkHolder₂ hα B
          (inclusionL hα (spatialFDerivL (k + 1) α E F hab u))‖ +
        ‖(ContinuousLinearMap.id ℝ _).compParabolicCkHolder₂ hα C
          (inclusionL hα (inclusionL hα u))‖ :=
    norm_add₃_le
  have hAu := mul_le_mul_of_nonneg_left h₂ (mul_nonneg hK (norm_nonneg A))
  have hBu := mul_le_mul_of_nonneg_left h₁ (mul_nonneg hK (norm_nonneg B))
  have hCu := mul_le_mul_of_nonneg_left h₀ (mul_nonneg hK (norm_nonneg C))
  push_cast at hCu
  calc ‖spatialOperator hα A B C u‖
      ≤ K * ‖A‖ * ‖u‖ + K * ‖B‖ * (8 * (k + 1) ^ 2 * ‖u‖) +
          K * ‖C‖ * (8 * (k + 1) ^ 2 * (8 * (k + 1 + 1) ^ 2 * ‖u‖)) := by linarith
    _ = _ := by ring

/-- **The spatial operator** `L u = A·D_x²u + B·D_xu + C·u` with coefficient fields in
`C_{par,b}^{k+α}`, as a continuous linear map from `C_{par,b}^{(k+2)+α}` to `C_{par,b}^{k+α}`. Its
values are given by `ParabolicCkHolderSpace.spatialOperatorL_apply` in terms of the fields of `u`
and by `ParabolicCkHolderSpace.spatialOperatorL_slabMk` in terms of the derivatives of its time
slices. -/
def spatialOperatorL :
    ParabolicCkHolderSpace (k + 2) α E F hab →L[ℝ] ParabolicCkHolderSpace k α E F hab :=
  LinearMap.mkContinuous
    { toFun := spatialOperator hα A B C
      map_add' u v := ext fun p ↦ by
        simp only [spatialOperator_apply, coe_add, Pi.add_apply, map_add,
          FunLike.coe_add]
        abel
      map_smul' c u := ext fun p ↦ by
        simp only [spatialOperator_apply, coe_smul, Pi.smul_apply, map_smul,
          FunLike.coe_smul, RingHom.id_apply, smul_add] }
    _ (norm_spatialOperator_le hα A B C)

/-- The values of the spatial operator, in terms of the fields `D_t^0 D_x^2 u` and `D_t^0 D_x^1 u`
of `u`. -/
@[simp]
theorem spatialOperatorL_apply (u : ParabolicCkHolderSpace (k + 2) α E F hab)
    (p : slab (E := E) a b) :
    spatialOperatorL hα A B C u p =
      A p (continuousMultilinearCurryFin2 ℝ E F (mixedDerivL 0 2 u p)) +
        B p (spatialFDerivBCF u p) + C p (u p) := by
  rw [spatialOperatorL, LinearMap.mkContinuous_apply]
  exact spatialOperator_apply hα A B C u p

/-- The values of the spatial operator at `(x, t)`, in terms of the first and second Fréchet
derivatives of the time slice `y ↦ u (y, t)`. -/
theorem spatialOperatorL_slabMk (u : ParabolicCkHolderSpace (k + 2) α E F hab) (x : E)
    (t : Icc a b) :
    spatialOperatorL hα A B C u (slabMk x t) =
      A (slabMk x t) (fderiv ℝ (fderiv ℝ fun y ↦ u (slabMk y t)) x) +
        B (slabMk x t) (fderiv ℝ (fun y ↦ u (slabMk y t)) x) + C (slabMk x t) (u (slabMk x t)) := by
  rw [spatialOperatorL, LinearMap.mkContinuous_apply]
  exact spatialOperator_slabMk hα A B C u x t

/-- **The operator bound for the spatial operator.**
`‖L‖ ≤ 21 (k + 1)² 2ᵏ (‖A‖ + 8 (k + 1)² ‖B‖ + 64 (k + 1)² (k + 2)² ‖C‖)`, uniformly over the
spaces and the slab. The factors `8 (k + 1)²` and `64 (k + 1)² (k + 2)²` bound the inclusions
through which the gradient and the value of `u` enter. -/
theorem norm_spatialOperatorL_le :
    ‖spatialOperatorL hα A B C‖ ≤ 21 * (k + 1) ^ 2 * 2 ^ k *
      (‖A‖ + 8 * (k + 1) ^ 2 * ‖B‖ + 64 * (k + 1) ^ 2 * (k + 2) ^ 2 * ‖C‖) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- **The parabolic operator** `P u = ∂ₜu - A·D_x²u - B·D_xu - C·u` with coefficient fields in
`C_{par,b}^{k+α}`, as a continuous linear map from `C_{par,b}^{(k+2)+α}` to `C_{par,b}^{k+α}`. The
time derivative is taken within `[a, b]`, so one-sided at the endpoints. -/
def parabolicOperatorL :
    ParabolicCkHolderSpace (k + 2) α E F hab →L[ℝ] ParabolicCkHolderSpace k α E F hab :=
  timeDerivL k α E F hab - spatialOperatorL hα A B C

theorem parabolicOperatorL_def :
    parabolicOperatorL hα A B C = timeDerivL k α E F hab - spatialOperatorL hα A B C := (rfl)

/-- The values of the parabolic operator, in terms of the fields of `u`. -/
@[simp]
theorem parabolicOperatorL_apply (u : ParabolicCkHolderSpace (k + 2) α E F hab)
    (p : slab (E := E) a b) :
    parabolicOperatorL hα A B C u p =
      mixedDerivL 1 0 u p 0 - (A p (continuousMultilinearCurryFin2 ℝ E F (mixedDerivL 0 2 u p)) +
        B p (spatialFDerivBCF u p) + C p (u p)) := by
  rw [parabolicOperatorL_def, _root_.sub_apply, coe_sub, Pi.sub_apply,
    timeDerivL_apply, spatialOperatorL_apply]

/-- The values of the parabolic operator at `(x, t)`, in terms of the time derivative within
`[a, b]` and the spatial Fréchet derivatives of `u`: this is the equation
`∂ₜu - A·D_x²u - B·D_xu - C·u` read classically. -/
theorem parabolicOperatorL_slabMk (u : ParabolicCkHolderSpace (k + 2) α E F hab) (x : E)
    (t : Icc a b) :
    parabolicOperatorL hα A B C u (slabMk x t) =
      derivWithin (ParabolicC2HolderSpace.timeExtension hab.le u x) (Icc a b) t -
        (A (slabMk x t) (fderiv ℝ (fderiv ℝ fun y ↦ u (slabMk y t)) x) +
          B (slabMk x t) (fderiv ℝ (fun y ↦ u (slabMk y t)) x) +
          C (slabMk x t) (u (slabMk x t))) := by
  rw [parabolicOperatorL_def, _root_.sub_apply, coe_sub, Pi.sub_apply,
    timeDerivL_slabMk, spatialOperatorL_slabMk]

/-- **The operator bound for the parabolic operator.**
`‖P‖ ≤ 1 + 21 (k + 1)² 2ᵏ (‖A‖ + 8 (k + 1)² ‖B‖ + 64 (k + 1)² (k + 2)² ‖C‖)`, uniformly over the
spaces and the slab. -/
theorem norm_parabolicOperatorL_le :
    ‖parabolicOperatorL hα A B C‖ ≤ 1 + 21 * (k + 1) ^ 2 * 2 ^ k *
      (‖A‖ + 8 * (k + 1) ^ 2 * ‖B‖ + 64 * (k + 1) ^ 2 * (k + 2) ^ 2 * ‖C‖) :=
  (norm_sub_le _ _).trans (add_le_add norm_timeDerivL_le_one (norm_spatialOperatorL_le hα A B C))

/-- The initial-data operator `u ↦ (P u, u(·, a))` from `C_{par,b}^{(k+2)+α}` to
`C_{par,b}^{k+α} × C_b^{k+2,α}`: the forcing and the initial spatial trace of `u`. -/
def initialDataL :
    ParabolicCkHolderSpace (k + 2) α E F hab →L[ℝ]
      ParabolicCkHolderSpace k α E F hab × CkHolderSpace (k + 2) α E F :=
  (parabolicOperatorL hα A B C).prod (spatialTraceL ⟨a, left_mem_Icc.2 hab.le⟩)

theorem initialDataL_def :
    initialDataL hα A B C =
      (parabolicOperatorL hα A B C).prod (spatialTraceL ⟨a, left_mem_Icc.2 hab.le⟩) := (rfl)

/-- The data of a function consist of its forcing and its initial spatial trace. -/
theorem initialDataL_apply (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    initialDataL hα A B C u =
      (parabolicOperatorL hα A B C u, u.spatialTrace ⟨a, left_mem_Icc.2 hab.le⟩) := by
  simp [initialDataL_def]

/-- The first data component is the parabolic operator. -/
@[simp]
theorem initialDataL_fst (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    (initialDataL hα A B C u).1 = parabolicOperatorL hα A B C u := by
  simp [initialDataL_def]

/-- The second data component is the initial spatial trace. -/
@[simp]
theorem initialDataL_snd (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    (initialDataL hα A B C u).2 = u.spatialTrace ⟨a, left_mem_Icc.2 hab.le⟩ := by
  simp [initialDataL_def]

/-- The data operator has the same coefficient bound as its parabolic component. -/
theorem norm_initialDataL_le :
    ‖initialDataL hα A B C‖ ≤ 1 + 21 * (k + 1) ^ 2 * 2 ^ k *
      (‖A‖ + 8 * (k + 1) ^ 2 * ‖B‖ + 64 * (k + 1) ^ 2 * (k + 2) ^ 2 * ‖C‖) := by
  rw [initialDataL_def, ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  exact max_le (norm_parabolicOperatorL_le hα A B C)
    ((norm_spatialTraceL_le_one _).trans (le_add_of_nonneg_right (by positivity)))

end Spatial

/-! ### Dependence on the coefficients -/

section Coefficients

variable (hα : α ≤ 1)
  {A A' : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab}
  {B B' : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab}
  {C C' : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab}

/-- The spatial operator is linear in its coefficients. -/
theorem spatialOperatorL_sub :
    spatialOperatorL hα (A - A') (B - B') (C - C') =
      spatialOperatorL hα A B C - spatialOperatorL hα A' B' C' := by
  ext u p
  simp only [spatialOperatorL_apply, _root_.sub_apply, coe_sub, Pi.sub_apply]
  abel

/-- The difference of two parabolic operators is the spatial operator of the difference of their
coefficients. -/
theorem parabolicOperatorL_sub_parabolicOperatorL :
    parabolicOperatorL hα A B C - parabolicOperatorL hα A' B' C' =
      spatialOperatorL hα (A' - A) (B' - B) (C' - C) := by
  rw [spatialOperatorL_sub, parabolicOperatorL_def, parabolicOperatorL_def]
  abel

/-- **Lipschitz dependence on the coefficients.** In operator norm,
`‖P_{A,B,C} - P_{A',B',C'}‖ ≤
  21 (k + 1)² 2ᵏ (‖A - A'‖ + 8 (k + 1)² ‖B - B'‖ + 64 (k + 1)² (k + 2)² ‖C - C'‖)`. -/
theorem norm_parabolicOperatorL_sub_le :
    ‖parabolicOperatorL hα A B C - parabolicOperatorL hα A' B' C'‖ ≤
      21 * (k + 1) ^ 2 * 2 ^ k *
        (‖A - A'‖ + 8 * (k + 1) ^ 2 * ‖B - B'‖ + 64 * (k + 1) ^ 2 * (k + 2) ^ 2 * ‖C - C'‖) := by
  rw [parabolicOperatorL_sub_parabolicOperatorL, norm_sub_rev A, norm_sub_rev B, norm_sub_rev C]
  exact norm_spatialOperatorL_le hα _ _ _

/-- Initial traces cancel in the difference of two data operators. -/
theorem initialDataL_sub_initialDataL :
    initialDataL hα A B C - initialDataL hα A' B' C' =
      (parabolicOperatorL hα A B C - parabolicOperatorL hα A' B' C').prod 0 := by
  ext u <;> simp

/-- Initial traces cancel in a difference of initial-data operators, so the perturbation norm is
that of the parabolic operators. -/
theorem norm_initialDataL_sub :
    ‖initialDataL hα A B C - initialDataL hα A' B' C'‖ =
      ‖parabolicOperatorL hα A B C - parabolicOperatorL hα A' B' C'‖ := by
  rw [initialDataL_sub_initialDataL, ContinuousLinearMap.opNorm_prod, Prod.norm_def, norm_zero,
    max_eq_left (norm_nonneg _)]

/-- A coefficient perturbation has the same explicit bound for the full initial-data operator as
for its parabolic component. -/
theorem norm_initialDataL_sub_le :
    ‖initialDataL hα A B C - initialDataL hα A' B' C'‖ ≤
      21 * (k + 1) ^ 2 * 2 ^ k *
        (‖A - A'‖ + 8 * (k + 1) ^ 2 * ‖B - B'‖ + 64 * (k + 1) ^ 2 * (k + 2) ^ 2 * ‖C - C'‖) := by
  rw [norm_initialDataL_sub]
  exact norm_parabolicOperatorL_sub_le hα

/-- The initial-data operator depends continuously on the coefficients, in operator norm. -/
theorem continuous_initialDataL :
    Continuous fun abc : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab ×
        ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab ×
        ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab ↦
      initialDataL hα abc.1 abc.2.1 abc.2.2 := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_initialDataL_sub_le hα)
    (Continuous.tendsto' (by fun_prop) x 0 (by simp))

/-- **The solution operator depends continuously on the coefficients.** If the initial-data
operator with coefficients `(A, B, C)` is invertible, its inverse is continuous in operator norm
as a function of the coefficients at `(A, B, C)`. -/
theorem continuousAt_inverse_initialDataL [CompleteSpace F]
    (h : (initialDataL hα A B C).IsInvertible) :
    ContinuousAt (fun abc : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab ×
        ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab ×
        ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab ↦
      (initialDataL hα abc.1 abc.2.1 abc.2.2).inverse) (A, B, C) :=
  ContinuousAt.comp (g := ContinuousLinearMap.inverse)
    (h.contDiffAt_map_inverse (n := 0)).continuousAt (continuous_initialDataL hα).continuousAt

end Coefficients

/-! ### Order zero -/

/-- **Agreement at order zero.** For coefficients of order zero and `u` of order two, the
parabolic operator is the operator `TauCeti.ParabolicC2HolderSpace.parabolicOperatorL` on
`C_b^{2+α,1+α/2}`, under the identifications of `C_{par,b}^{0+α}` with `C_b^{α,α/2}` and of
`C_{par,b}^{2+α}` with `C_b^{2+α,1+α/2}`. -/
theorem equivHolderSpace_parabolicOperatorL (hα : α ≤ 1)
    (A : ParabolicCkHolderSpace 0 α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace 0 α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace 0 α E (F →L[ℝ] F) hab) (u : ParabolicCkHolderSpace 2 α E F hab) :
    equivHolderSpace (parabolicOperatorL hα A B C u) =
      ParabolicC2HolderSpace.parabolicOperatorL hα (equivHolderSpace A) (equivHolderSpace B)
        (equivHolderSpace C) (equivParabolicC2HolderSpace u) := by
  refine HolderSpace.ext fun p ↦ ?_
  simp [ParabolicC2HolderSpace.parabolicOperatorL_apply]

/-! ### Reading the operator at a lower order -/

/-- The time derivative commutes with the inclusions between orders: reading `∂ₜu` at a lower
order `m` is differentiating `u` read at order `m + 2`. -/
theorem inclusionOfLEL_timeDerivL (hα : α ≤ 1) {m : ℕ} (h : m ≤ k)
    (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    inclusionOfLEL hα h (timeDerivL k α E F hab u) =
      timeDerivL m α E F hab (inclusionOfLEL hα (Nat.add_le_add_right h 2) u) :=
  ext fun p ↦ by
    simp only [inclusionOfLEL_apply, timeDerivL_apply,
      mixedDerivL_inclusionOfLEL hα (Nat.add_le_add_right h 2) u (r := 1) (m := 0) (by omega)]

/-- The spatial operator commutes with the inclusions between orders: reading `L u` at a lower
order `m` is applying the operator with the coefficients and `u` read at that order. -/
theorem inclusionOfLEL_spatialOperatorL (hα : α ≤ 1) {m : ℕ} (h : m ≤ k)
    (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab)
    (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    inclusionOfLEL hα h (spatialOperatorL hα A B C u) =
      spatialOperatorL hα (inclusionOfLEL hα h A) (inclusionOfLEL hα h B)
        (inclusionOfLEL hα h C) (inclusionOfLEL hα (Nat.add_le_add_right h 2) u) := by
  refine ext fun p ↦ ?_
  have h₂ := Nat.add_le_add_right h 2
  simp only [inclusionOfLEL_apply, spatialOperatorL_apply, spatialFDerivBCF_apply,
    mixedDerivL_inclusionOfLEL hα h₂ u (r := 0) (m := 2) (by omega),
    mixedDerivL_inclusionOfLEL hα h₂ u (r := 0) (m := 1) (by omega)]

/-- The parabolic operator commutes with the inclusions between orders: reading `P u` at a lower
order `m` is applying the operator with the coefficients and `u` read at that order. -/
theorem inclusionOfLEL_parabolicOperatorL (hα : α ≤ 1) {m : ℕ} (h : m ≤ k)
    (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab)
    (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    inclusionOfLEL hα h (parabolicOperatorL hα A B C u) =
      parabolicOperatorL hα (inclusionOfLEL hα h A) (inclusionOfLEL hα h B)
        (inclusionOfLEL hα h C) (inclusionOfLEL hα (Nat.add_le_add_right h 2) u) := by
  rw [parabolicOperatorL_def, parabolicOperatorL_def, _root_.sub_apply, map_sub,
    _root_.sub_apply, inclusionOfLEL_timeDerivL, inclusionOfLEL_spatialOperatorL]

/-- Reading a map at a lower order keeps its spatial traces. -/
theorem coe_spatialTrace_inclusionOfLEL (hα : α ≤ 1) {m n : ℕ} (h : m ≤ n)
    (u : ParabolicCkHolderSpace n α E F hab) (t : Icc a b) :
    ⇑((inclusionOfLEL hα h u).spatialTrace t) = ⇑(u.spatialTrace t) :=
  funext fun x ↦ by simp

/-- Reading `u` and the coefficients at a lower order `m` reads the forcing of the initial data at
that order. -/
theorem initialDataL_inclusionOfLEL_fst (hα : α ≤ 1) {m : ℕ} (h : m ≤ k)
    (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab)
    (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    (initialDataL hα (inclusionOfLEL hα h A) (inclusionOfLEL hα h B) (inclusionOfLEL hα h C)
        (inclusionOfLEL hα (Nat.add_le_add_right h 2) u)).1 =
      inclusionOfLEL hα h (initialDataL hα A B C u).1 := by
  rw [initialDataL_fst, initialDataL_fst, inclusionOfLEL_parabolicOperatorL]

/-- Reading `u` and the coefficients at a lower order keeps the initial trace. -/
theorem coe_initialDataL_inclusionOfLEL_snd (hα : α ≤ 1) {m : ℕ} (h : m ≤ k)
    (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab)
    (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    ⇑(initialDataL hα (inclusionOfLEL hα h A) (inclusionOfLEL hα h B) (inclusionOfLEL hα h C)
        (inclusionOfLEL hα (Nat.add_le_add_right h 2) u)).2 =
      ⇑(initialDataL hα A B C u).2 := by
  rw [initialDataL_snd, initialDataL_snd, coe_spatialTrace_inclusionOfLEL]

/-! ### Coordinate coefficients on Euclidean space

These are the order-`k` forms of the order-two coefficient fields
`TauCeti.ParabolicC2HolderSpace.euclideanSecondOrderCoeff`, `euclideanFirstOrderCoeff` and
`euclideanZerothOrderCoeff`, and agree with them at order zero. -/

section Euclidean

variable {ι : Type*} [Fintype ι]

/-- A local shortcut for the norm on covectors: instance search for the coefficient spaces of the
Euclidean operator fails without it, since the norm on their domain arises only as a nested
instance problem. -/
local instance instNormedAddCommGroupEuclideanCovector :
    NormedAddCommGroup (EuclideanSpace ℝ ι →L[ℝ] ℝ) := inferInstance
/-- A local shortcut for scalar operations on covectors. -/
local instance instNormedSpaceEuclideanCovector :
    NormedSpace ℝ (EuclideanSpace ℝ ι →L[ℝ] ℝ) := inferInstance
/-- A local shortcut for the norm on Euclidean Hessians. -/
local instance instNormedAddCommGroupEuclideanHessian :
    NormedAddCommGroup (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) := inferInstance
/-- A local shortcut for scalar operations on Euclidean Hessians. -/
local instance instNormedSpaceEuclideanHessian :
    NormedSpace ℝ (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) := inferInstance

variable [DecidableEq ι] {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- The second-order coefficient field `H ↦ aⁱʲ H(eᵢ, eⱼ)` on `ℝⁿ = EuclideanSpace ℝ ι`, assembled
from scalar coefficients `aⁱʲ` in `C_{par,b}^{k+α}`. -/
def euclideanSecondOrderCoeff
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht) :
    ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι)
      ((EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) →L[ℝ] ℝ) ht :=
  ∑ i, ∑ j, compLeftL (ContinuousLinearMap.toSpanSingleton ℝ
    ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ ι →L[ℝ] ℝ)
        (EuclideanSpace.single i (1 : ℝ))))) (a i j)

/-- The first-order coefficient field `v ↦ bⁱ v(eᵢ)` on `ℝⁿ = EuclideanSpace ℝ ι`, assembled from
scalar coefficients `bⁱ` in `C_{par,b}^{k+α}`. -/
def euclideanFirstOrderCoeff (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht) :
    ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ((EuclideanSpace ℝ ι →L[ℝ] ℝ) →L[ℝ] ℝ) ht :=
  ∑ i, compLeftL (ContinuousLinearMap.toSpanSingleton ℝ
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ)) :
      (EuclideanSpace ℝ ι →L[ℝ] ℝ) →L[ℝ] ℝ)) (b i)

omit [DecidableEq ι] in
/-- The zeroth-order coefficient field `y ↦ c y`, assembled from a scalar coefficient `c` in
`C_{par,b}^{k+α}`. -/
def euclideanZerothOrderCoeff (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht) :
    ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) (ℝ →L[ℝ] ℝ) ht :=
  compLeftL (ContinuousLinearMap.toSpanSingleton ℝ (ContinuousLinearMap.id ℝ ℝ)) c

/-- The values of the second-order coefficient field. -/
@[simp]
theorem euclideanSecondOrderCoeff_apply
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht)
    (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁)
    (H : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) :
    euclideanSecondOrderCoeff a p H =
      ∑ i, ∑ j, a i j p * H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  simp [euclideanSecondOrderCoeff, Finset.sum_apply]

/-- The values of the first-order coefficient field. -/
@[simp]
theorem euclideanFirstOrderCoeff_apply
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht)
    (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁) (v : EuclideanSpace ℝ ι →L[ℝ] ℝ) :
    euclideanFirstOrderCoeff b p v = ∑ i, b i p * v (EuclideanSpace.single i 1) := by
  simp [euclideanFirstOrderCoeff, Finset.sum_apply]

omit [DecidableEq ι] in
/-- The values of the zeroth-order coefficient field. -/
@[simp]
theorem euclideanZerothOrderCoeff_apply
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht)
    (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁) (y : ℝ) :
    euclideanZerothOrderCoeff c p y = c p * y := by
  simp [euclideanZerothOrderCoeff]

/-- Reading the second-order coefficient field at a lower order reads its scalar coefficients at
that order. -/
@[simp]
theorem inclusionOfLEL_euclideanSecondOrderCoeff (hα : α ≤ 1) {m : ℕ} (h : m ≤ k)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht) :
    inclusionOfLEL hα h (euclideanSecondOrderCoeff a) =
      euclideanSecondOrderCoeff fun i j ↦ inclusionOfLEL hα h (a i j) :=
  ext fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp

/-- Reading the first-order coefficient field at a lower order reads its scalar coefficients at
that order. -/
@[simp]
theorem inclusionOfLEL_euclideanFirstOrderCoeff (hα : α ≤ 1) {m : ℕ} (h : m ≤ k)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht) :
    inclusionOfLEL hα h (euclideanFirstOrderCoeff b) =
      euclideanFirstOrderCoeff fun i ↦ inclusionOfLEL hα h (b i) :=
  ext fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp

omit [DecidableEq ι] in
/-- Reading the zeroth-order coefficient field at a lower order reads its scalar coefficient at
that order. -/
@[simp]
theorem inclusionOfLEL_euclideanZerothOrderCoeff (hα : α ≤ 1) {m : ℕ} (h : m ≤ k)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht) :
    inclusionOfLEL hα h (euclideanZerothOrderCoeff c) =
      euclideanZerothOrderCoeff (inclusionOfLEL hα h c) :=
  ext fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp

/-- Reading the coefficients `aⁱʲ` at a lower order preserves uniform ellipticity, with the same
constant. -/
theorem ellipticity_inclusionOfLEL (hα : α ≤ 1) {m : ℕ} (h : m ≤ k)
    {a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht}
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ inclusionOfLEL hα h (a i j) p).toQuadraticForm' ξ := by
  simpa only [inclusionOfLEL_apply] using ha

/- In the next statements, the order-zero coefficients `equivHolderSpace c` are elaborated without
an expected type, as `(equivHolderSpace c :)`: unifying their type with that of the order-two
coefficient spaces first makes elaboration time out. -/

/-- At order zero, the second-order coefficient field is
`TauCeti.ParabolicC2HolderSpace.euclideanSecondOrderCoeff` of the scalar coefficients read in
`C_b^{α,α/2}`. -/
theorem equivHolderSpace_euclideanSecondOrderCoeff
    (a : ι → ι → ParabolicCkHolderSpace 0 α (EuclideanSpace ℝ ι) ℝ ht) :
    equivHolderSpace (euclideanSecondOrderCoeff a) =
      ParabolicC2HolderSpace.euclideanSecondOrderCoeff fun i j ↦ (equivHolderSpace (a i j) :) :=
  HolderSpace.ext fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp [equivHolderSpace_apply]

/-- At order zero, the first-order coefficient field is
`TauCeti.ParabolicC2HolderSpace.euclideanFirstOrderCoeff` of the scalar coefficients read in
`C_b^{α,α/2}`. -/
theorem equivHolderSpace_euclideanFirstOrderCoeff
    (b : ι → ParabolicCkHolderSpace 0 α (EuclideanSpace ℝ ι) ℝ ht) :
    equivHolderSpace (euclideanFirstOrderCoeff b) =
      ParabolicC2HolderSpace.euclideanFirstOrderCoeff fun i ↦ (equivHolderSpace (b i) :) :=
  HolderSpace.ext fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp [equivHolderSpace_apply]

omit [DecidableEq ι] in
/-- At order zero, the zeroth-order coefficient field is
`TauCeti.ParabolicC2HolderSpace.euclideanZerothOrderCoeff` of the scalar coefficient read in
`C_b^{α,α/2}`. -/
theorem equivHolderSpace_euclideanZerothOrderCoeff
    (c : ParabolicCkHolderSpace 0 α (EuclideanSpace ℝ ι) ℝ ht) :
    equivHolderSpace (euclideanZerothOrderCoeff c) =
      ParabolicC2HolderSpace.euclideanZerothOrderCoeff (equivHolderSpace c :) :=
  HolderSpace.ext fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp [equivHolderSpace_apply]

/-- **Agreement at order zero for coordinate coefficients.** For scalar coefficients of order
zero and `u` of order two, the Euclidean parabolic operator is
`TauCeti.ParabolicC2HolderSpace.euclideanParabolicOperatorL` on `C_b^{2+α,1+α/2}`, with the
coefficients read in `C_b^{α,α/2}`. -/
theorem equivHolderSpace_euclideanParabolicOperatorL (hα : α ≤ 1)
    (a : ι → ι → ParabolicCkHolderSpace 0 α (EuclideanSpace ℝ ι) ℝ ht)
    (b : ι → ParabolicCkHolderSpace 0 α (EuclideanSpace ℝ ι) ℝ ht)
    (c : ParabolicCkHolderSpace 0 α (EuclideanSpace ℝ ι) ℝ ht)
    (u : ParabolicCkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ ht) :
    equivHolderSpace (parabolicOperatorL hα (euclideanSecondOrderCoeff a)
        (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c) u) =
      ParabolicC2HolderSpace.euclideanParabolicOperatorL hα
        (fun i j ↦ (equivHolderSpace (a i j) :)) (fun i ↦ (equivHolderSpace (b i) :))
        (equivHolderSpace c :) (equivParabolicC2HolderSpace u) := by
  rw [equivHolderSpace_parabolicOperatorL, equivHolderSpace_euclideanSecondOrderCoeff,
    equivHolderSpace_euclideanFirstOrderCoeff, equivHolderSpace_euclideanZerothOrderCoeff,
    ParabolicC2HolderSpace.euclideanParabolicOperatorL_def]

end Euclidean

end ParabolicCkHolderSpace

end TauCeti
