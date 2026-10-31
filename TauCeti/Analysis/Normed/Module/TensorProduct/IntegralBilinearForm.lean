/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.TensorProduct.Map
public import TauCeti.Analysis.OperatorIdeal.Carrier

/-!
# Integral bilinear forms

A bounded bilinear form `B : E →L[𝕜] F →L[𝕜] 𝕜` induces the linear functional
`TensorProduct.lift B` on the algebraic tensor product `E ⊗[𝕜] F`, sending `x ⊗ₜ y` to `B x y`.
This functional is always bounded for the projective seminorm. The form is *integral* when the
functional is also bounded for the injective seminorm `ε`, and its *integral norm* is the least
such bound. The integral bilinear forms are therefore exactly the continuous linear functionals
on the injective tensor product `TauCeti.InjectiveTensor 𝕜 E F`, and the integral norm is the
dual norm.

We record the integral norm as the extended gauge `ContinuousLinearMap.integralENorm B ∈ [0, ∞]`,
the supremum over tensors `u` of `‖lift B u‖ / ε(u)`. It dominates the operator norm of `B`, the
norm `B` carries as a bounded bilinear form, and the two are kept on separate types below. It
takes the value `‖f‖ ‖g‖` on the rank-one form `(x, y) ↦ f x * g y`, and composing with bounded
operators `a` and `b` in the two variables multiplies it by at most `‖a‖ ‖b‖`.

A bilinear form `E →L[𝕜] F →L[𝕜] 𝕜` is the same as its currying, the bounded operator
`E →L[𝕜] StrongDual 𝕜 F`. Through this identification the integral norm is an operator gauge,
and the integral bilinear forms make up its normed carrier `TauCeti.IntegralBilinearForm 𝕜 E F`.
The forgetful map to bounded bilinear forms is the contraction
`OperatorGauge.Carrier.toContinuousLinearMapL`. The isometric identification
`TauCeti.IntegralBilinearForm.liftIsometry` of integral bilinear forms with the dual of the
injective tensor product shows that the carrier is a Banach space when `𝕜` is complete.
Restricting a functional on the injective tensor product along the contraction from the projective
tensor product recovers the functional induced by the underlying bounded bilinear form.

## Main declarations

* `ContinuousLinearMap.integralENorm`: the extended integral norm of a bounded bilinear form.
* `ContinuousLinearMap.integralENorm_le_ofReal_iff`: the integral norm is at most `C` iff
  `‖lift B u‖ ≤ C * ε(u)` for every tensor `u`.
* `ContinuousLinearMap.enorm_le_integralENorm`: the operator norm is at most the integral norm.
* `ContinuousLinearMap.integralENorm_smulRight`: the integral norm of a rank-one form.
* `ContinuousLinearMap.integralENorm_bilinearComp_le`: bounded functoriality in both variables.
* `TauCeti.integralGauge`: the integral norm as an operator gauge on `E →L[𝕜] StrongDual 𝕜 F`.
* `TauCeti.IntegralBilinearForm`: the normed space of integral bilinear forms.
* `TauCeti.IntegralBilinearForm.liftIsometry`: integral bilinear forms are isometrically the
  continuous dual of the injective tensor product.
* `TauCeti.IntegralBilinearForm.bilinearComp`: composition with bounded operators `a` and `b` in
  both variables, multiplying norms by at most `‖a‖ ‖b‖`.
* `TauCeti.IntegralBilinearForm.smulRight`: the rank-one integral bilinear forms.

## References

* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, §3.4.
-/

public section

noncomputable section

open TauCeti TensorProduct
open scoped ENNReal

namespace ContinuousLinearMap

variable {𝕜 E E' F F' : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- The extended **integral norm** of a bounded bilinear form `B`: the supremum over tensors `u`
of `‖lift B u‖ / ε(u)`, where `ε` is the injective seminorm. A tensor of zero injective seminorm
on which the induced functional does not vanish contributes `∞`. It is the least constant `C` with
`‖lift B u‖ ≤ C * ε(u)` for all `u` (`integralENorm_le_ofReal_iff`). -/
def integralENorm (B : E →L[𝕜] F →L[𝕜] 𝕜) : ℝ≥0∞ :=
  ⨆ u : E ⊗[𝕜] F, ‖lift B.toLinearMap₁₂ u‖ₑ / ENNReal.ofReal (injectiveSeminorm 𝕜 E F u)

/-- The integral norm as a supremum of ratios over tensors. -/
theorem integralENorm_def (B : E →L[𝕜] F →L[𝕜] 𝕜) :
    B.integralENorm =
      ⨆ u : E ⊗[𝕜] F, ‖lift B.toLinearMap₁₂ u‖ₑ / ENNReal.ofReal (injectiveSeminorm 𝕜 E F u) :=
  (rfl)

/-- Each tensor bounds the integral norm from below by the ratio of the two sides. -/
theorem enorm_lift_div_le_integralENorm (B : E →L[𝕜] F →L[𝕜] 𝕜) (u : E ⊗[𝕜] F) :
    ‖lift B.toLinearMap₁₂ u‖ₑ / ENNReal.ofReal (injectiveSeminorm 𝕜 E F u) ≤ B.integralENorm :=
  le_iSup (fun u : E ⊗[𝕜] F ↦
    ‖lift B.toLinearMap₁₂ u‖ₑ / ENNReal.ofReal (injectiveSeminorm 𝕜 E F u)) u

/-- The integral norm is at most `C` exactly when the induced functional is bounded by `C` times
the injective seminorm. -/
theorem integralENorm_le_ofReal_iff {B : E →L[𝕜] F →L[𝕜] 𝕜} {C : ℝ} (hC : 0 ≤ C) :
    B.integralENorm ≤ ENNReal.ofReal C ↔
      ∀ u : E ⊗[𝕜] F, ‖lift B.toLinearMap₁₂ u‖ ≤ C * injectiveSeminorm 𝕜 E F u := by
  simp only [integralENorm_def, iSup_le_iff]
  refine forall_congr' fun u ↦ ?_
  rw [ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.ofReal_mul hC, ← ofReal_norm,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (apply_nonneg _ _))]

/-- A finite integral norm bounds the induced functional by a multiple of the injective
seminorm. -/
theorem norm_lift_le_toReal_integralENorm_mul {B : E →L[𝕜] F →L[𝕜] 𝕜}
    (hB : B.integralENorm ≠ ∞) (u : E ⊗[𝕜] F) :
    ‖lift B.toLinearMap₁₂ u‖ ≤ B.integralENorm.toReal * injectiveSeminorm 𝕜 E F u :=
  (integralENorm_le_ofReal_iff ENNReal.toReal_nonneg).1 (ENNReal.ofReal_toReal hB).ge u

/-- A form of zero operator norm has zero integral norm. -/
theorem integralENorm_eq_zero_of_norm_eq_zero {B : E →L[𝕜] F →L[𝕜] 𝕜} (hB : ‖B‖ = 0) :
    B.integralENorm = 0 := by
  refine le_antisymm ?_ bot_le
  rw [← ENNReal.ofReal_zero, integralENorm_le_ofReal_iff le_rfl]
  intro u
  simpa [hB] using norm_lift_le_projectiveSeminorm B u

/-- The zero form has zero integral norm. -/
@[simp]
theorem integralENorm_zero : (0 : E →L[𝕜] F →L[𝕜] 𝕜).integralENorm = 0 :=
  integralENorm_eq_zero_of_norm_eq_zero opNorm_zero

/-- The functional induced on algebraic tensors by `B` is the functional on the projective tensor
product given by its universal property; this makes it linear in `B`. -/
private theorem lift_eq_liftIsometry (B : E →L[𝕜] F →L[𝕜] 𝕜) (u : E ⊗[𝕜] F) :
    lift B.toLinearMap₁₂ u = ProjectiveTensor.liftIsometry 𝕜 E F 𝕜 B ⟨u⟩ :=
  (ProjectiveTensor.liftIsometry_apply B ⟨u⟩).symm

/-- Absolute homogeneity of the integral norm, including its infinite values. -/
@[simp]
theorem integralENorm_smul (c : 𝕜) (B : E →L[𝕜] F →L[𝕜] 𝕜) :
    (c • B).integralENorm = ‖c‖ₑ * B.integralENorm := by
  simp only [integralENorm_def, lift_eq_liftIsometry]
  simp only [map_smul, _root_.smul_apply, smul_eq_mul, enorm_mul, mul_div_assoc, ENNReal.mul_iSup]

/-- Negation preserves the integral norm. -/
@[simp]
theorem integralENorm_neg (B : E →L[𝕜] F →L[𝕜] 𝕜) : (-B).integralENorm = B.integralENorm := by
  rw [← neg_one_smul 𝕜 B, integralENorm_smul, enorm_neg, enorm_one, one_mul]

/-- The integral norm is subadditive. -/
theorem integralENorm_add_le (B B' : E →L[𝕜] F →L[𝕜] 𝕜) :
    (B + B').integralENorm ≤ B.integralENorm + B'.integralENorm := by
  refine iSup_le fun u ↦ ?_
  rw [lift_eq_liftIsometry, map_add, _root_.add_apply, ← lift_eq_liftIsometry,
    ← lift_eq_liftIsometry]
  calc
    _ ≤ (‖lift B.toLinearMap₁₂ u‖ₑ + ‖lift B'.toLinearMap₁₂ u‖ₑ) /
        ENNReal.ofReal (injectiveSeminorm 𝕜 E F u) := by gcongr; exact enorm_add_le _ _
    _ = _ := ENNReal.add_div
    _ ≤ _ := add_le_add (B.enorm_lift_div_le_integralENorm u) (B'.enorm_lift_div_le_integralENorm u)

/-- The operator norm of a bilinear form is at most its integral norm. -/
theorem enorm_le_integralENorm (B : E →L[𝕜] F →L[𝕜] 𝕜) : ‖B‖ₑ ≤ B.integralENorm := by
  rcases eq_or_ne B.integralENorm ∞ with hB | hB
  · simp [hB]
  rw [← ENNReal.ofReal_toReal hB, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal (B.opNorm_le_bound₂ ENNReal.toReal_nonneg fun x y ↦ ?_)
  calc
    ‖B x y‖ = ‖lift B.toLinearMap₁₂ (x ⊗ₜ y)‖ := by simp
    _ ≤ B.integralENorm.toReal * injectiveSeminorm 𝕜 E F (x ⊗ₜ y) :=
      norm_lift_le_toReal_integralENorm_mul hB _
    _ ≤ B.integralENorm.toReal * (‖x‖ * ‖y‖) := by gcongr; exact injectiveSeminorm_tmul_le x y
    _ = _ := (mul_assoc _ _ _).symm

/-- Composing a bilinear form with bounded operators `a` and `b` in its two variables multiplies
the integral norm by at most `‖a‖ ‖b‖`. -/
theorem integralENorm_bilinearComp_le (B : E →L[𝕜] F →L[𝕜] 𝕜) (a : E' →L[𝕜] E)
    (b : F' →L[𝕜] F) :
    (B.bilinearComp a b).integralENorm ≤ ‖a‖ₑ * ‖b‖ₑ * B.integralENorm := by
  rcases eq_or_ne B.integralENorm ∞ with hB | hB
  · rcases eq_or_ne (‖a‖ₑ * ‖b‖ₑ) 0 with hab | hab
    · -- A null factor makes the composite null, whatever the integral norm of `B`.
      have hab' : ‖a‖ * ‖b‖ = 0 := by
        simpa [ENNReal.toReal_mul] using congrArg ENNReal.toReal hab
      refine le_trans (b := 0) ?_ (by simp)
      rw [← ENNReal.ofReal_zero, integralENorm_le_ofReal_iff le_rfl]
      intro u
      rw [lift_bilinearComp, zero_mul]
      refine (norm_lift_le_projectiveSeminorm B _).trans ?_
      simpa [hab'] using mul_le_mul_of_nonneg_left (projectiveSeminorm_map_le a b u) (norm_nonneg B)
    · simp [hB, ENNReal.mul_top hab]
  · rw [← ENNReal.ofReal_toReal hB, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity),
      integralENorm_le_ofReal_iff (by positivity)]
    intro u
    rw [lift_bilinearComp]
    calc
      _ ≤ B.integralENorm.toReal * injectiveSeminorm 𝕜 E F (map a.toLinearMap b.toLinearMap u) :=
        norm_lift_le_toReal_integralENorm_mul hB _
      _ ≤ B.integralENorm.toReal * (‖a‖ * ‖b‖ * injectiveSeminorm 𝕜 E' F' u) := by
        gcongr; exact injectiveSeminorm_map_le a b u
      _ = _ := by ring

/-- The rank-one form `(x, y) ↦ f x * g y` has integral norm `‖f‖ ‖g‖`. -/
@[simp]
theorem integralENorm_smulRight (f : StrongDual 𝕜 E) (g : StrongDual 𝕜 F) :
    (f.smulRight g).integralENorm = ‖f‖ₑ * ‖g‖ₑ := by
  refine le_antisymm ?_ ?_
  · rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
      integralENorm_le_ofReal_iff (by positivity)]
    intro u
    rw [lift_smulRight]
    calc
      _ ≤ ‖g‖ * ‖contractStrongDual 𝕜 E F u f‖ := g.le_opNorm _
      _ ≤ ‖g‖ * (injectiveSeminorm 𝕜 E F u * ‖f‖) := by
        gcongr; exact norm_contractStrongDual_apply_le u f
      _ = _ := by ring
  · simpa [← ofReal_norm, ENNReal.ofReal_mul] using enorm_le_integralENorm (f.smulRight g)

end ContinuousLinearMap

namespace TauCeti

section Gauge

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The integral norm as an operator gauge on bounded operators `E →L[𝕜] StrongDual 𝕜 F`, the
curried bounded bilinear forms on `E × F`. -/
def integralGauge : OperatorGauge 𝕜 E (StrongDual 𝕜 F) where
  toFun B := B.integralENorm
  map_add_le' := ContinuousLinearMap.integralENorm_add_le
  map_smul' := ContinuousLinearMap.integralENorm_smul
  enorm_le' := ContinuousLinearMap.enorm_le_integralENorm

variable {𝕜 E F}

@[simp]
theorem integralGauge_apply (B : E →L[𝕜] F →L[𝕜] 𝕜) : integralGauge 𝕜 E F B = B.integralENorm :=
  (rfl)

variable (𝕜 E F) in
/-- The normed space of **integral bilinear forms** on `E × F`: the bounded bilinear forms of
finite integral norm, normed by the integral norm. It is identified isometrically with the dual
of the injective tensor product by `IntegralBilinearForm.liftIsometry`, and its inclusion
`OperatorGauge.Carrier.toContinuousLinearMapL` into the bounded bilinear forms is a
contraction. -/
abbrev IntegralBilinearForm := (integralGauge 𝕜 E F).Carrier

end Gauge

namespace IntegralBilinearForm

variable {𝕜 E E' F F' : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- The norm of an integral bilinear form is its integral norm. -/
theorem norm_def (B : IntegralBilinearForm 𝕜 E F) :
    ‖B‖ = B.toContinuousLinearMap.integralENorm.toReal :=
  OperatorGauge.Carrier.norm_def B

/-- The extended norm of an integral bilinear form is its integral norm. -/
theorem enorm_eq_integralENorm (B : IntegralBilinearForm 𝕜 E F) :
    ‖B‖ₑ = B.toContinuousLinearMap.integralENorm :=
  OperatorGauge.Carrier.enorm_eq_gauge B

/-- The functional induced by an integral bilinear form is bounded by its norm times the
injective seminorm. -/
theorem norm_lift_le (B : IntegralBilinearForm 𝕜 E F) (u : E ⊗[𝕜] F) :
    ‖lift B.toContinuousLinearMap.toLinearMap₁₂ u‖ ≤ ‖B‖ * injectiveSeminorm 𝕜 E F u := by
  rw [norm_def]
  exact ContinuousLinearMap.norm_lift_le_toReal_integralENorm_mul B.gauge_lt_top.ne u

/-- The norm of an integral bilinear form is the least bound of its induced functional relative
to the injective seminorm. -/
theorem norm_le_iff {B : IntegralBilinearForm 𝕜 E F} {C : ℝ} (hC : 0 ≤ C) :
    ‖B‖ ≤ C ↔ ∀ u : E ⊗[𝕜] F,
      ‖lift B.toContinuousLinearMap.toLinearMap₁₂ u‖ ≤ C * injectiveSeminorm 𝕜 E F u := by
  rw [← ContinuousLinearMap.integralENorm_le_ofReal_iff hC, ← enorm_eq_integralENorm,
    ← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hC]

/-- The bounded bilinear form `(x, y) ↦ φ (x ⊗ₜ y)` defined by a functional `φ` on the injective
tensor product. -/
private def ofStrongDual (φ : StrongDual 𝕜 (InjectiveTensor 𝕜 E F)) : E →L[𝕜] F →L[𝕜] 𝕜 :=
  (ProjectiveTensor.liftIsometry 𝕜 E F 𝕜).symm (φ ∘L ProjectiveTensor.toInjectiveTensor 𝕜 E F)

private theorem lift_ofStrongDual (φ : StrongDual 𝕜 (InjectiveTensor 𝕜 E F)) (u : E ⊗[𝕜] F) :
    lift (ofStrongDual φ).toLinearMap₁₂ u = φ ⟨u⟩ := by
  induction u with
  | tmul x y => simp [ofStrongDual]
  | add u v hu hv => simp [hu, hv]

private theorem integralENorm_ofStrongDual_le (φ : StrongDual 𝕜 (InjectiveTensor 𝕜 E F)) :
    (ofStrongDual φ).integralENorm ≤ ENNReal.ofReal ‖φ‖ := by
  rw [ContinuousLinearMap.integralENorm_le_ofReal_iff (norm_nonneg φ)]
  intro u
  rw [lift_ofStrongDual, ← InjectiveTensor.norm_def ⟨u⟩]
  exact φ.le_opNorm _

variable (𝕜 E F) in
/-- **Integral bilinear forms are the dual of the injective tensor product**: an integral
bilinear form `B` induces the bounded functional on `InjectiveTensor 𝕜 E F` sending `x ⊗ₜ y` to
`B x y`, and this is an isometric equivalence. -/
def liftIsometry : IntegralBilinearForm 𝕜 E F ≃ₗᵢ[𝕜] StrongDual 𝕜 (InjectiveTensor 𝕜 E F) :=
  LinearIsometryEquiv.ofBounds
    { toFun B := LinearMap.mkContinuous
        (lift B.toContinuousLinearMap.toLinearMap₁₂ ∘ₗ
          (InjectiveTensor.linearEquiv 𝕜 E F).toLinearMap) ‖B‖
        fun u ↦ by simpa [InjectiveTensor.norm_def] using norm_lift_le B u.toTensorProduct
      map_add' B B' := InjectiveTensor.continuousLinearMap_ext fun x y ↦ by simp
      map_smul' a B := InjectiveTensor.continuousLinearMap_ext fun x y ↦ by simp
      invFun φ := ⟨ofStrongDual φ, OperatorGauge.mem_finiteSubmodule.2 <|
        (integralENorm_ofStrongDual_le φ).trans_lt ENNReal.ofReal_lt_top⟩
      left_inv B := by ext x y; simp [ofStrongDual]
      right_inv φ := InjectiveTensor.continuousLinearMap_ext fun x y ↦ by simp [ofStrongDual] }
    (fun B ↦ LinearMap.mkContinuous_norm_le _ (norm_nonneg B) fun u ↦ by
      simpa [InjectiveTensor.norm_def] using norm_lift_le B u.toTensorProduct)
    (fun φ ↦ by
      rw [norm_def]
      exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg φ) (integralENorm_ofStrongDual_le φ))

/-- The functional induced by an integral bilinear form acts on the underlying tensor by
`TensorProduct.lift`. -/
theorem liftIsometry_apply (B : IntegralBilinearForm 𝕜 E F) (u : InjectiveTensor 𝕜 E F) :
    liftIsometry 𝕜 E F B u = lift B.toContinuousLinearMap.toLinearMap₁₂ u.toTensorProduct := by
  simp [liftIsometry, LinearIsometryEquiv.ofBounds]

/-- The functional induced by an integral bilinear form `B` sends `x ⊗ₜ y` to `B x y`. -/
@[simp]
theorem liftIsometry_apply_tmul (B : IntegralBilinearForm 𝕜 E F) (x : E) (y : F) :
    liftIsometry 𝕜 E F B ⟨x ⊗ₜ y⟩ = B.toContinuousLinearMap x y := by
  simp [liftIsometry_apply]

/-- The integral bilinear form corresponding to a functional `φ` on the injective tensor product
is `(x, y) ↦ φ (x ⊗ₜ y)`. -/
@[simp]
theorem liftIsometry_symm_apply_apply (φ : StrongDual 𝕜 (InjectiveTensor 𝕜 E F)) (x : E) (y : F) :
    ((liftIsometry 𝕜 E F).symm φ).toContinuousLinearMap x y = φ ⟨x ⊗ₜ y⟩ := by
  rw [← liftIsometry_apply_tmul, LinearIsometryEquiv.apply_symm_apply]

/-- Restricting the functional induced by an integral bilinear form along the contraction from
the projective to the injective tensor product gives the functional induced by the underlying
bounded bilinear form. -/
theorem liftIsometry_comp_toInjectiveTensor (B : IntegralBilinearForm 𝕜 E F) :
    liftIsometry 𝕜 E F B ∘L ProjectiveTensor.toInjectiveTensor 𝕜 E F =
      ProjectiveTensor.liftIsometry 𝕜 E F 𝕜 B.toContinuousLinearMap :=
  ProjectiveTensor.continuousLinearMap_ext fun x y ↦ by simp

/-- Over a complete field, the integral bilinear forms form a Banach space. -/
instance [CompleteSpace 𝕜] : CompleteSpace (IntegralBilinearForm 𝕜 E F) :=
  (liftIsometry 𝕜 E F).toIsometryEquiv.completeSpace

/-- An integral bilinear form composed with bounded operators in its two variables, as an
integral bilinear form. -/
private def bilinearCompAux (a : E' →L[𝕜] E) (b : F' →L[𝕜] F) (B : IntegralBilinearForm 𝕜 E F) :
    IntegralBilinearForm 𝕜 E' F' :=
  ⟨B.toContinuousLinearMap.bilinearComp a b, OperatorGauge.mem_finiteSubmodule.2 <|
    (ContinuousLinearMap.integralENorm_bilinearComp_le _ a b).trans_lt <|
      ENNReal.mul_lt_top (ENNReal.mul_lt_top enorm_lt_top enorm_lt_top) B.gauge_lt_top⟩

private theorem norm_bilinearCompAux_le (a : E' →L[𝕜] E) (b : F' →L[𝕜] F)
    (B : IntegralBilinearForm 𝕜 E F) : ‖bilinearCompAux a b B‖ ≤ ‖a‖ * ‖b‖ * ‖B‖ := by
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm, ofReal_norm, ofReal_norm,
    enorm_eq_integralENorm, enorm_eq_integralENorm]
  exact ContinuousLinearMap.integralENorm_bilinearComp_le _ a b

/-- Composition with bounded operators `a` and `b` in the two variables, as a bounded linear map
between spaces of integral bilinear forms. It multiplies norms by at most `‖a‖ ‖b‖`
(`norm_bilinearComp_apply_le`). -/
def bilinearComp (a : E' →L[𝕜] E) (b : F' →L[𝕜] F) :
    IntegralBilinearForm 𝕜 E F →L[𝕜] IntegralBilinearForm 𝕜 E' F' :=
  LinearMap.mkContinuous
    { toFun := bilinearCompAux a b
      map_add' _ _ := OperatorGauge.Carrier.ext (by ext; simp [bilinearCompAux])
      map_smul' _ _ := OperatorGauge.Carrier.ext (by ext; simp [bilinearCompAux]) }
    (‖a‖ * ‖b‖) (norm_bilinearCompAux_le a b)

@[simp]
theorem toContinuousLinearMap_bilinearComp (a : E' →L[𝕜] E) (b : F' →L[𝕜] F)
    (B : IntegralBilinearForm 𝕜 E F) :
    (bilinearComp a b B).toContinuousLinearMap = B.toContinuousLinearMap.bilinearComp a b :=
  (rfl)

/-- Composition with `a` and `b` multiplies the integral norm by at most `‖a‖ ‖b‖`. -/
theorem norm_bilinearComp_apply_le (a : E' →L[𝕜] E) (b : F' →L[𝕜] F)
    (B : IntegralBilinearForm 𝕜 E F) : ‖bilinearComp a b B‖ ≤ ‖a‖ * ‖b‖ * ‖B‖ :=
  norm_bilinearCompAux_le a b B

/-- Under the identification with the dual of the injective tensor product, composition with
`a` and `b` is the adjoint of the induced map `a ⊗ b` of injective tensor products. -/
theorem liftIsometry_bilinearComp (a : E' →L[𝕜] E) (b : F' →L[𝕜] F)
    (B : IntegralBilinearForm 𝕜 E F) :
    liftIsometry 𝕜 E' F' (bilinearComp a b B) = liftIsometry 𝕜 E F B ∘L InjectiveTensor.mapL a b :=
  InjectiveTensor.continuousLinearMap_ext fun x y ↦ by simp

/-- The rank-one integral bilinear form `(x, y) ↦ f x * g y`. -/
def smulRight (f : StrongDual 𝕜 E) (g : StrongDual 𝕜 F) : IntegralBilinearForm 𝕜 E F :=
  ⟨f.smulRight g, OperatorGauge.mem_finiteSubmodule.2 <| by
    simpa using ENNReal.mul_lt_top enorm_lt_top enorm_lt_top⟩

@[simp]
theorem toContinuousLinearMap_smulRight (f : StrongDual 𝕜 E) (g : StrongDual 𝕜 F) :
    (smulRight f g).toContinuousLinearMap = f.smulRight g :=
  (rfl)

/-- The rank-one integral bilinear form `(x, y) ↦ f x * g y` has norm `‖f‖ ‖g‖`. -/
@[simp]
theorem norm_smulRight (f : StrongDual 𝕜 E) (g : StrongDual 𝕜 F) :
    ‖smulRight f g‖ = ‖f‖ * ‖g‖ := by
  rw [norm_def, toContinuousLinearMap_smulRight, ContinuousLinearMap.integralENorm_smulRight,
    ENNReal.toReal_mul, toReal_enorm, toReal_enorm]

end IntegralBilinearForm

end TauCeti
