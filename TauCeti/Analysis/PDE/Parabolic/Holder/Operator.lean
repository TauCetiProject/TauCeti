/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Interpolation
public import TauCeti.Analysis.PDE.Parabolic.Holder.Trace
public import TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.WholeSpace
public import TauCeti.Analysis.Holder.Bilinear

/-!
# Second-order parabolic operators on order-two parabolic Hölder spaces

For coefficient fields `A`, `B`, `C` in the bounded parabolic Hölder space `C_b^{α,α/2}` on the
slab `E × [t₀, t₁]`, with values in the continuous linear maps on Hessians, gradients and values,
this file defines the spatial operator `L u = A·D_x²u + B·D_xu + C·u` and the parabolic operator
`P u = ∂ₜu - L u` as bounded linear maps from `C_b^{2+α,1+α/2}` (`ParabolicC2HolderSpace`) to
`C_b^{α,α/2}`, for `α ≤ 1`. Both are linear in the coefficients, with explicit operator bounds,
so `P` depends Lipschitz continuously on its coefficients in operator norm.

On `ℝⁿ = EuclideanSpace ℝ ι` with scalar values, the coefficients of
`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u` are Hölder functions `aⁱʲ`, `bⁱ`, `c`. If the matrix
`a` is degenerate elliptic and `c ≤ γ` with `0 ≤ γ`, every `u` in `C_b^{2+α,1+α/2}` with
`P u ≤ K` and `u(·, t₀) ≤ M`, where `0 ≤ M` and `0 ≤ K`, satisfies
`u(x, t) ≤ exp (γ (t - t₀)) (M + (t - t₀) K)`; applied to `±u`, the same bound holds for `|u|`
when `|P u| ≤ K` and `|u(·, t₀)| ≤ M`. In particular `u` is determined by `P u` and its initial
trace. This is the whole-space comparison principle applied to the Hölder class; no lower bound on
`a` is needed.

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.spatialOperatorL` and
  `TauCeti.ParabolicC2HolderSpace.parabolicOperatorL`: the operators `L` and `P = ∂ₜ - L`.
* `TauCeti.ParabolicC2HolderSpace.norm_parabolicOperatorL_le` and
  `TauCeti.ParabolicC2HolderSpace.norm_parabolicOperatorL_sub_le`: the operator bound and the
  Lipschitz dependence on the coefficients.
* `TauCeti.ParabolicC2HolderSpace.euclideanParabolicOperatorL`: the operator with Hölder
  coefficients `aⁱʲ`, `bⁱ`, `c` on `ℝⁿ`.
* `TauCeti.ParabolicC2HolderSpace.le_exp_mul_mul_add_mul_of_euclideanParabolicOperatorL_le`,
  `TauCeti.ParabolicC2HolderSpace.abs_le_exp_mul_mul_add_mul_of_abs_euclideanParabolicOperatorL_le`
  and `TauCeti.ParabolicC2HolderSpace.eq_of_euclideanParabolicOperatorL_eq`: the one-sided and
  two-sided a priori bounds and uniqueness for the Cauchy problem.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004,
  Chapters 3 and 4.
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2, Section 4.
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- A local shortcut for the norm on Hessians. Without it, instance search for the operator norm on
`(E →L[ℝ] E →L[ℝ] F) →L[ℝ] F`, the coefficient space of the second-order term, fails: the norm
instance on its domain only arises as a nested instance problem during unification. -/
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on Hessians, needed for the same reason. -/
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-! ### General coefficients -/

section General

/-- The spatial operator `L u = A·D_x²u + B·D_xu + C·u` with coefficient fields in `C_b^{α,α/2}`,
as a continuous linear map from `C_b^{2+α,1+α/2}` to `C_b^{α,α/2}`. -/
def spatialOperatorL (hα : α ≤ 1)
    (A : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F))
    (B : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] F) →L[ℝ] F))
    (C : HolderSpace α (slab (E := E) t₀ t₁) (F →L[ℝ] F)) :
    ParabolicC2HolderSpace α E F ht →L[ℝ] HolderSpace α (slab (E := E) t₀ t₁) F :=
  (ContinuousLinearMap.id ℝ _).compHolder₂ A ∘L spatialSecondFDerivL +
    (ContinuousLinearMap.id ℝ _).compHolder₂ B ∘L spatialFDerivHolderL hα +
    (ContinuousLinearMap.id ℝ _).compHolder₂ C ∘L valueHolderL hα

/-- The parabolic operator `P u = ∂ₜu - A·D_x²u - B·D_xu - C·u` with coefficient fields in
`C_b^{α,α/2}`, as a continuous linear map from `C_b^{2+α,1+α/2}` to `C_b^{α,α/2}`. -/
def parabolicOperatorL (hα : α ≤ 1)
    (A : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F))
    (B : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] F) →L[ℝ] F))
    (C : HolderSpace α (slab (E := E) t₀ t₁) (F →L[ℝ] F)) :
    ParabolicC2HolderSpace α E F ht →L[ℝ] HolderSpace α (slab (E := E) t₀ t₁) F :=
  timeDerivL - spatialOperatorL hα A B C

variable (hα : α ≤ 1)
  {A A' : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)}
  {B B' : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] F) →L[ℝ] F)}
  {C C' : HolderSpace α (slab (E := E) t₀ t₁) (F →L[ℝ] F)}

@[simp]
theorem spatialOperatorL_apply (u : ParabolicC2HolderSpace α E F ht)
    (p : slab (E := E) t₀ t₁) :
    spatialOperatorL hα A B C u p =
      A p (spatialSecondFDerivL u p) + B p (spatialFDerivL u p) + C p (u p) := by
  simp [spatialOperatorL]

theorem parabolicOperatorL_def :
    parabolicOperatorL (ht := ht) hα A B C = timeDerivL - spatialOperatorL hα A B C := (rfl)

@[simp]
theorem parabolicOperatorL_apply (u : ParabolicC2HolderSpace α E F ht)
    (p : slab (E := E) t₀ t₁) :
    parabolicOperatorL hα A B C u p =
      timeDerivL u p - (A p (spatialSecondFDerivL u p) + B p (spatialFDerivL u p) +
        C p (u p)) := by
  simp [parabolicOperatorL]

/-- The spatial operator is linear in its coefficients. -/
theorem spatialOperatorL_sub :
    spatialOperatorL (ht := ht) hα (A - A') (B - B') (C - C') =
      spatialOperatorL hα A B C - spatialOperatorL hα A' B' C' := by
  ext u p
  simp only [spatialOperatorL_apply, _root_.sub_apply, HolderSpace.sub_apply]
  abel

/-- The difference of two parabolic operators is the spatial operator of the difference of
their coefficients. -/
theorem parabolicOperatorL_sub_parabolicOperatorL :
    parabolicOperatorL (ht := ht) hα A B C - parabolicOperatorL hα A' B' C' =
      spatialOperatorL hα (A' - A) (B' - B) (C' - C) := by
  rw [spatialOperatorL_sub, parabolicOperatorL_def, parabolicOperatorL_def]
  abel

/-- **The operator bound for the spatial operator.**
`‖L‖ ≤ ‖A‖ + 24 (‖B‖ + ‖C‖)`, uniformly over the spaces and the slab. -/
theorem norm_spatialOperatorL_le :
    ‖spatialOperatorL (ht := ht) hα A B C‖ ≤ ‖A‖ + 24 * (‖B‖ + ‖C‖) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  -- Pointwise application of a coefficient field does not increase norms.
  have hA := ContinuousLinearMap.norm_id_compHolder₂_apply_le A (spatialSecondFDerivL u)
  have hB := ContinuousLinearMap.norm_id_compHolder₂_apply_le B (spatialFDerivHolderL hα u)
  have hC := ContinuousLinearMap.norm_id_compHolder₂_apply_le C (valueHolderL hα u)
  have h₂ := norm_spatialSecondFDerivL_le u
  have h₁ := norm_valueHolderL_add_norm_spatialFDerivHolderL_le hα u one_pos le_rfl
  simp only [Real.one_rpow, mul_one] at h₁
  have hv := norm_valueL_le u
  have hDu := norm_nonneg (spatialFDerivHolderL hα u)
  have hu := norm_nonneg (valueHolderL hα u)
  have hL : ‖spatialOperatorL (ht := ht) hα A B C u‖ ≤
      ‖A‖ * ‖spatialSecondFDerivL u‖ + ‖B‖ * ‖spatialFDerivHolderL hα u‖ +
        ‖C‖ * ‖valueHolderL hα u‖ :=
    (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hA hB)) hC)
  nlinarith [mul_le_mul_of_nonneg_left h₂ (norm_nonneg A),
    mul_le_mul_of_nonneg_left (show ‖spatialFDerivHolderL hα u‖ ≤ 24 * ‖u‖ by linarith)
      (norm_nonneg B),
    mul_le_mul_of_nonneg_left (show ‖valueHolderL hα u‖ ≤ 24 * ‖u‖ by linarith) (norm_nonneg C)]

/-- **The operator bound for the parabolic operator.**
`‖P‖ ≤ 1 + ‖A‖ + 24 (‖B‖ + ‖C‖)`, uniformly over the spaces and the slab. -/
theorem norm_parabolicOperatorL_le :
    ‖parabolicOperatorL (ht := ht) hα A B C‖ ≤ 1 + ‖A‖ + 24 * (‖B‖ + ‖C‖) := by
  rw [parabolicOperatorL_def, add_assoc]
  exact (norm_sub_le _ _).trans (add_le_add norm_timeDerivL_le_one (norm_spatialOperatorL_le hα))

/-- **Lipschitz dependence on the coefficients.** In operator norm,
`‖P_{A,B,C} - P_{A',B',C'}‖ ≤ ‖A - A'‖ + 24 (‖B - B'‖ + ‖C - C'‖)`. -/
theorem norm_parabolicOperatorL_sub_le :
    ‖parabolicOperatorL (ht := ht) hα A B C - parabolicOperatorL hα A' B' C'‖ ≤
      ‖A - A'‖ + 24 * (‖B - B'‖ + ‖C - C'‖) := by
  rw [parabolicOperatorL_sub_parabolicOperatorL, norm_sub_rev A, norm_sub_rev B,
    norm_sub_rev C]
  exact norm_spatialOperatorL_le hα

end General

/-! ### Coordinate coefficients on Euclidean space -/

section Euclidean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A local shortcut for the norm on covectors, needed for scalar operations on gradient
coefficients for the reason explained at the Hessian shortcut. -/
local instance : NormedAddCommGroup (EuclideanSpace ℝ ι →L[ℝ] ℝ) := inferInstance
/-- A local shortcut for scalar operations on covectors. -/
local instance : NormedSpace ℝ (EuclideanSpace ℝ ι →L[ℝ] ℝ) := inferInstance

/-- The parabolic operator `P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u` on `ℝⁿ = EuclideanSpace ℝ ι`
with scalar coefficients `aⁱʲ`, `bⁱ`, `c` in `C_b^{α,α/2}`, as a continuous linear map from
`C_b^{2+α,1+α/2}` to `C_b^{α,α/2}`. -/
def euclideanParabolicOperatorL (hα : α ≤ 1)
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ) :
    ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht →L[ℝ]
      HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ :=
  parabolicOperatorL hα
    (∑ i, ∑ j, (ContinuousLinearMap.lsmul ℝ ℝ).compHolder₂ (a i j)
      (HolderSpace.const ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j 1)).comp
        (ContinuousLinearMap.apply ℝ _ (EuclideanSpace.single i 1)))))
    (∑ i, (ContinuousLinearMap.lsmul ℝ ℝ).compHolder₂ (b i)
      (HolderSpace.const (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1))))
    ((ContinuousLinearMap.lsmul ℝ ℝ).compHolder₂ c
      (HolderSpace.const (ContinuousLinearMap.id ℝ ℝ)))

variable (hα : α ≤ 1) {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}

theorem euclideanParabolicOperatorL_def :
    euclideanParabolicOperatorL (ht := ht) hα a b c =
      parabolicOperatorL hα
        (∑ i, ∑ j, (ContinuousLinearMap.lsmul ℝ ℝ).compHolder₂ (a i j)
          (HolderSpace.const ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j 1)).comp
            (ContinuousLinearMap.apply ℝ _ (EuclideanSpace.single i 1)))))
        (∑ i, (ContinuousLinearMap.lsmul ℝ ℝ).compHolder₂ (b i)
          (HolderSpace.const (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1))))
        ((ContinuousLinearMap.lsmul ℝ ℝ).compHolder₂ c
          (HolderSpace.const (ContinuousLinearMap.id ℝ ℝ))) := (rfl)

@[simp]
theorem euclideanParabolicOperatorL_apply
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht)
    (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁) :
    euclideanParabolicOperatorL hα a b c u p = timeDerivL u p -
      (∑ i, ∑ j, a i j p * spatialSecondFDerivL u p (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + ∑ i, b i p * spatialFDerivL u p (EuclideanSpace.single i 1) +
        c p * u p) := by
  simp [euclideanParabolicOperatorL]

/-- At an interior time, the time slice through `x`, shifted to start at `0`, has the recorded
time derivative as its ordinary derivative. -/
private theorem hasDerivAt_shift (u : ParabolicC2HolderSpace α E F ht) (x : E) {t : ℝ}
    (h : t ∈ Ioo 0 (t₁ - t₀)) :
    HasDerivAt (fun s ↦ u (slabMk x (projIcc t₀ t₁ ht.le (s + t₀))))
      (timeDerivL u (slabMk x (projIcc t₀ t₁ ht.le (t + t₀)))) t := by
  have hτ : ((projIcc t₀ t₁ ht.le (t + t₀) : Icc t₀ t₁) : ℝ) = t + t₀ :=
    congrArg Subtype.val (projIcc_of_mem ht.le ⟨by linarith [h.1], by linarith [h.2]⟩)
  have hd := (u.hasTimeDerivWithinAt x (projIcc t₀ t₁ ht.le (t + t₀))).hasDerivAt
    (Icc_mem_nhds (by rw [hτ]; linarith [h.1]) (by rw [hτ]; linarith [h.2]))
  rw [hτ, timeExtension_def] at hd
  exact hd.comp_add_const t t₀

/-- On a shifted interior time slice, the classical coordinate form of `P u` used by the
whole-space comparison principle is the value of `P u` at the corresponding slab point. -/
private theorem shift_operator_eq (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht)
    {t : ℝ} (h : t ∈ Ioo 0 (t₁ - t₀)) (x : EuclideanSpace ℝ ι) :
    deriv (fun s ↦ u (slabMk x (projIcc t₀ t₁ ht.le (s + t₀)))) t -
      (∑ i, ∑ j, (Matrix.of fun i j ↦ a i j (slabMk x (projIcc t₀ t₁ ht.le (t + t₀)))) i j *
          fderiv ℝ (fderiv ℝ fun y ↦ u (slabMk y (projIcc t₀ t₁ ht.le (t + t₀)))) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        fderiv ℝ (fun y ↦ u (slabMk y (projIcc t₀ t₁ ht.le (t + t₀)))) x
          (∑ i, b i (slabMk x (projIcc t₀ t₁ ht.le (t + t₀))) • EuclideanSpace.single i 1) +
        c (slabMk x (projIcc t₀ t₁ ht.le (t + t₀))) *
          u (slabMk x (projIcc t₀ t₁ ht.le (t + t₀)))) =
      euclideanParabolicOperatorL hα a b c u (slabMk x (projIcc t₀ t₁ ht.le (t + t₀))) := by
  have hx : fderiv ℝ (fun y ↦ u (slabMk y (projIcc t₀ t₁ ht.le (t + t₀)))) =
      fun y ↦ spatialFDerivL u (slabMk y (projIcc t₀ t₁ ht.le (t + t₀))) :=
    funext (u.fderiv_eq _)
  rw [(hasDerivAt_shift u x h).deriv, hx, u.fderiv_spatialFDeriv_eq,
    euclideanParabolicOperatorL_apply]
  simp only [Matrix.of_apply, map_sum, map_smul, smul_eq_mul]

/-- **The one-sided a priori bound for the Cauchy problem.** Let `a` be degenerate elliptic and
`c ≤ γ` with `0 ≤ γ`. If `u ∈ C_b^{2+α,1+α/2}` on `ℝⁿ × [t₀, t₁]` satisfies `P u ≤ K` and
`u(·, t₀) ≤ M` with `0 ≤ M` and `0 ≤ K`, then `u(x, t) ≤ exp (γ (t - t₀)) (M + (t - t₀) K)`. -/
theorem le_exp_mul_mul_add_mul_of_euclideanParabolicOperatorL_le
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {γ : ℝ} (hc : ∀ p, c p ≤ γ) (hγ : 0 ≤ γ) {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht)
    (hP : ∀ p, euclideanParabolicOperatorL hα a b c u p ≤ K)
    (hinit : ∀ x, u (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩) ≤ M)
    (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁) :
    u p ≤ Real.exp (γ * (slabTime p - t₀)) * (M + (slabTime p - t₀) * K) := by
  -- Shift the slab to `[0, t₁ - t₀]` and extend every field constantly in time outside it.
  have hcont : Continuous fun z : ℝ × EuclideanSpace ℝ ι ↦
      u (slabMk z.2 (projIcc t₀ t₁ ht.le (z.1 + t₀))) :=
    (valueL u).continuous.comp (continuous_slabMk.comp (continuous_snd.prodMk
      ((continuous_projIcc (h := ht.le)).comp (continuous_fst.add continuous_const))))
  have hbdd : Bornology.IsBounded (Set.range fun z : ℝ × EuclideanSpace ℝ ι ↦
      u (slabMk z.2 (projIcc t₀ t₁ ht.le (z.1 + t₀)))) := by
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨‖valueL u‖, ?_⟩
    rintro _ ⟨z, rfl⟩
    simpa using (valueL u).norm_coe_le_norm _
  have key :=
    PDE.le_exp_mul_mul_add_mul_of_deriv_le_sum_mul_fderiv_fderiv_add_fderiv_add_mul_add
      (u := fun t x ↦ u (slabMk x (projIcc t₀ t₁ ht.le (t + t₀))))
      (a := fun t x ↦ Matrix.of fun i j ↦ a i j (slabMk x (projIcc t₀ t₁ ht.le (t + t₀))))
      (b := fun t x ↦
        ∑ i, b i (slabMk x (projIcc t₀ t₁ ht.le (t + t₀))) • EuclideanSpace.single i 1)
      (c := fun t x ↦ c (slabMk x (projIcc t₀ t₁ ht.le (t + t₀))))
      (T := t₁ - t₀) (Lam := ∑ i, ‖a i i‖) (β := ∑ i, ‖b i‖)
      (fun t _ x ξ ↦ ha _ ξ)
      (fun t _ x ↦ by
        have hx : 1 ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
        have h₀ : 0 ≤ ∑ i, ‖a i i‖ := by positivity
        calc _ ≤ ∑ i, ‖a i i‖ := Finset.sum_le_sum fun i _ ↦
                (le_abs_self _).trans (HolderSpace.norm_apply_le (a i i) _)
          _ ≤ _ := le_mul_of_one_le_right h₀ hx)
      (fun t _ x ↦ by
        have h₀ : 0 ≤ ∑ i, ‖b i‖ := by positivity
        calc _ ≤ ∑ i, ‖b i‖ := (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ by
                simpa [norm_smul] using HolderSpace.norm_apply_le (b i) _)
          _ ≤ _ := le_mul_of_one_le_right h₀ (by linarith [norm_nonneg x]))
      (fun t _ x ↦ hc _) hγ hM hK hcont.continuousOn
      (hbdd.subset (image_subset_range _ _)).bddAbove
      (fun t _ x ↦ (u.contDiff_spatialSlice _).contDiffAt)
      (fun t h x ↦ (hasDerivAt_shift u x h).differentiableAt)
      (fun t h x ↦ sub_le_iff_le_add'.1 ((shift_operator_eq hα u h x).trans_le (hP _)))
      (fun x ↦ by simpa using hinit x)
  have hp : slabTime p - t₀ ∈ Icc 0 (t₁ - t₀) :=
    ⟨by linarith [(slabTime p).2.1], by linarith [(slabTime p).2.2]⟩
  have hτ : projIcc t₀ t₁ ht.le (slabTime p - t₀ + t₀) = slabTime p := by
    rw [sub_add_cancel, projIcc_val]
  simpa only [hτ, slabMk_space_slabTime] using key hp (p : ParabolicSpaceTime _).space

/-- **The a priori bound for the Cauchy problem.** Let `a` be degenerate elliptic and `c ≤ γ`
with `0 ≤ γ`. If `u ∈ C_b^{2+α,1+α/2}` on `ℝⁿ × [t₀, t₁]` satisfies `|P u| ≤ K` and
`|u(·, t₀)| ≤ M`, then `|u(x, t)| ≤ exp (γ (t - t₀)) (M + (t - t₀) K)`. -/
theorem abs_le_exp_mul_mul_add_mul_of_abs_euclideanParabolicOperatorL_le
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {γ : ℝ} (hc : ∀ p, c p ≤ γ) (hγ : 0 ≤ γ) {M K : ℝ}
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht)
    (hP : ∀ p, |euclideanParabolicOperatorL hα a b c u p| ≤ K)
    (hinit : ∀ x, |u (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩)| ≤ M)
    (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁) :
    |u p| ≤ Real.exp (γ * (slabTime p - t₀)) * (M + (slabTime p - t₀) * K) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hinit 0)
  have hK : 0 ≤ K := (abs_nonneg _).trans (hP (slabMk 0 ⟨t₀, left_mem_Icc.2 ht.le⟩))
  -- The lower bound is the upper bound for `-u`.
  have hge := le_exp_mul_mul_add_mul_of_euclideanParabolicOperatorL_le hα ha hc hγ hM hK (-u)
    (fun q ↦ by rw [map_neg, HolderSpace.neg_apply]; exact neg_le.1 (abs_le.1 (hP q)).1)
    (fun x ↦ by rw [neg_apply]; exact neg_le.1 (abs_le.1 (hinit x)).1) p
  rw [neg_apply] at hge
  exact abs_le.2 ⟨neg_le.1 hge, le_exp_mul_mul_add_mul_of_euclideanParabolicOperatorL_le hα ha hc
    hγ hM hK u (fun q ↦ (abs_le.1 (hP q)).2) (fun x ↦ (abs_le.1 (hinit x)).2) p⟩

/-- **Uniqueness for the Cauchy problem.** For degenerate elliptic `a`, an element of
`C_b^{2+α,1+α/2}` on `ℝⁿ × [t₀, t₁]` is determined by `P u` and its initial trace `u(·, t₀)`. -/
theorem eq_of_euclideanParabolicOperatorL_eq
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {u v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht}
    (hP : euclideanParabolicOperatorL hα a b c u = euclideanParabolicOperatorL hα a b c v)
    (hinit : ∀ x, u (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩) =
      v (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩)) :
    u = v := by
  ext p
  have h := abs_le_exp_mul_mul_add_mul_of_abs_euclideanParabolicOperatorL_le hα ha
    (fun q ↦ (le_abs_self _).trans (HolderSpace.norm_apply_le c q)) (norm_nonneg c)
    (b := b) (M := 0) (K := 0) (u - v)
    (fun q ↦ by simp only [map_sub, hP, sub_self, HolderSpace.zero_apply, abs_zero, le_refl])
    (fun x ↦ by simp [hinit]) p
  simpa [sub_apply, sub_eq_zero] using h

end Euclidean

end TauCeti.ParabolicC2HolderSpace
