/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Bilinear
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Differentiation
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Inclusion
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.LowOrder
public import TauCeti.Analysis.PDE.Parabolic.Holder.InitialData
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

At order `k = 0` these are the operators `TauCeti.ParabolicC2HolderSpace.parabolicOperatorL` and
`TauCeti.ParabolicC2HolderSpace.initialDataL` on `C_b^{2+α,1+α/2}`, under the identifications
`TauCeti.ParabolicCkHolderSpace.equivHolderSpace` and
`TauCeti.ParabolicCkHolderSpace.equivParabolicC2HolderSpace`
(`TauCeti.ParabolicCkHolderSpace.equivHolderSpace_parabolicOperatorL`).

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.spatialOperatorL` and
  `TauCeti.ParabolicCkHolderSpace.parabolicOperatorL`: the operators `L` and `P = ∂ₜ - L`, with
  their values in terms of the fields of `u`
  (`TauCeti.ParabolicCkHolderSpace.parabolicOperatorL_apply`) and in terms of the derivatives of
  its time slices (`TauCeti.ParabolicCkHolderSpace.parabolicOperatorL_slabMk`).
* `TauCeti.ParabolicCkHolderSpace.initialDataL`: the operator `u ↦ (P u, u(·, a))`.
* `TauCeti.ParabolicCkHolderSpace.norm_parabolicOperatorL_le` and
  `TauCeti.ParabolicCkHolderSpace.norm_parabolicOperatorL_sub_le`: the operator bound and the
  Lipschitz dependence on the coefficients.
* `TauCeti.ParabolicCkHolderSpace.equivHolderSpace_parabolicOperatorL`: agreement with the
  operator on `C_b^{2+α,1+α/2}` at order zero.

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

/-- The inclusion of order `n + 1` into order `n` has norm at most `8 (n + 1)²`. -/
private theorem norm_inclusionL_le_mul_sq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (n : ℕ) : ‖inclusionL (k := n) (α := α) (E := E) (F := G) (hab := hab) hα‖ ≤
      8 * (n + 1) ^ 2 := by
  refine (norm_inclusionL_le hα).trans ?_
  have := card_parabolicDerivPairs_le n
  rw [mul_comm]
  gcongr
  exact_mod_cast this

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
      (mul_le_mul (norm_inclusionL_le_mul_sq hα k) (norm_spatialFDerivL_le u) (norm_nonneg _)
        (by positivity))
  have h₀ : ‖inclusionL hα (inclusionL hα u)‖ ≤
      8 * (k + 1) ^ 2 * (8 * ((k + 1 : ℕ) + 1) ^ 2 * ‖u‖) := by
    refine ((inclusionL hα).le_opNorm _).trans
      (mul_le_mul (norm_inclusionL_le_mul_sq hα k) (((inclusionL hα).le_opNorm _).trans ?_)
        (norm_nonneg _) (by positivity))
    exact mul_le_mul_of_nonneg_right (norm_inclusionL_le_mul_sq hα (k + 1)) (norm_nonneg _)
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

/-- The first data component is the parabolic operator. -/
@[simp]
theorem initialDataL_fst (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    (initialDataL hα A B C u).1 = parabolicOperatorL hα A B C u := (rfl)

/-- The second data component is the initial spatial trace. -/
@[simp]
theorem initialDataL_snd (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    (initialDataL hα A B C u).2 = u.spatialTrace ⟨a, left_mem_Icc.2 hab.le⟩ := by
  simp [initialDataL_def]

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

/-- Initial traces cancel in a difference of initial-data operators, so the perturbation norm is
that of the parabolic operators. -/
theorem norm_initialDataL_sub :
    ‖initialDataL hα A B C - initialDataL hα A' B' C'‖ =
      ‖parabolicOperatorL hα A B C - parabolicOperatorL hα A' B' C'‖ := by
  have h : initialDataL hα A B C - initialDataL hα A' B' C' =
      (parabolicOperatorL hα A B C - parabolicOperatorL hα A' B' C').prod 0 := by
    ext u <;> simp
  rw [h, ContinuousLinearMap.opNorm_prod, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]

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
  rw [← slabMk_space_slabTime p]
  set x := (p : ParabolicSpaceTime E).space
  set t := slabTime p
  have hslice : (fun y ↦ equivParabolicC2HolderSpace u (slabMk y t)) = fun y ↦ u (slabMk y t) :=
    funext fun y ↦ equivParabolicC2HolderSpace_apply u _
  have htime : ParabolicC2HolderSpace.timeExtension hab.le (equivParabolicC2HolderSpace u) x =
      ParabolicC2HolderSpace.timeExtension hab.le u x := by
    simp only [ParabolicC2HolderSpace.timeExtension_def, equivParabolicC2HolderSpace_apply]
  rw [equivHolderSpace_apply, parabolicOperatorL_slabMk,
    ParabolicC2HolderSpace.parabolicOperatorL_apply, equivHolderSpace_apply,
    equivHolderSpace_apply, equivHolderSpace_apply, equivParabolicC2HolderSpace_apply,
    ← ParabolicC2HolderSpace.derivWithin_eq, htime, ← ParabolicC2HolderSpace.fderiv_fderiv_eq,
    hslice, ← ParabolicC2HolderSpace.fderiv_eq, hslice]

end ParabolicCkHolderSpace

end TauCeti
