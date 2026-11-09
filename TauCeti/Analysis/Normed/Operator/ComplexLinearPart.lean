/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.LinearAlgebra.Complex.LinearPart
public import TauCeti.LinearAlgebra.Complex.Module
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The complex-linear part of a real-linear operator

A continuous real-linear operator `Ψ : E →L[ℝ] F` between complex normed spaces has a
**complex-linear part**

`Ψ.complexLinearPart z = ½ (Ψ z - i Ψ (i z))`,

which is a continuous complex-linear operator (`ContinuousLinearMap.complexLinearPart`). Its
underlying real-linear map is the algebraic complex-linear part `TauCeti.complexLinearPart` for the
complex structures given by multiplication by `i`
(`ContinuousLinearMap.coe_complexLinearPart`), and the difference `Ψ - Ψ.complexLinearPart` is the
complex-antilinear part. A complex-linear operator is its own complex-linear part, and taking the
complex-linear part commutes with composition by complex-linear operators on either side. The
complex-linear part depends continuously on `Ψ`
(`ContinuousLinearMap.continuous_complexLinearPart`), so a continuous family of real-linear
operators has a continuous family of complex-linear parts.

For a real-linear map `Ψ` between complex inner product spaces preserving the standard
symplectic form `Im ⟪·, ·⟫`, the complex-linear part `P` and the complex-antilinear part `Ψ - P`
satisfy `‖P z‖² = ‖z‖² + ‖Ψ z - P z‖²` (`ContinuousLinearMap.norm_sq_complexLinearPart_apply`).
So the complex-linear part of a linear symplectic map is injective, and for an endomorphism of a
finite-dimensional space it is a complex-linear automorphism
(`ContinuousLinearMap.complexLinearPartEquiv`). This is how the graph of a linear symplectic map
is moved into place by complex-linear automorphisms in
`TauCeti.LinearAlgebra.TotallyReal.Maslov.Symplectic`.

## Main declarations

* `ContinuousLinearMap.complexLinearPart`: the complex-linear part of a real-linear operator.
* `ContinuousLinearMap.complexLinearPart_restrictScalars`: a complex-linear operator is its own
  complex-linear part.
* `ContinuousLinearMap.complexLinearPart_restrictScalars_comp`,
  `ContinuousLinearMap.complexLinearPart_comp_restrictScalars`: compatibility with composition by
  complex-linear operators.
* `ContinuousLinearMap.restrictScalars_complexLinearPart`: the underlying real-linear operator
  `½ (Ψ - i ∘ Ψ ∘ i)`.
* `ContinuousLinearMap.continuous_complexLinearPart`: continuity in the operator.
* `ContinuousLinearMap.norm_sq_complexLinearPart_apply`: the norm identity for a linear map
  preserving `Im ⟪·, ·⟫`.
* `ContinuousLinearMap.complexLinearPartEquiv`: the complex-linear part of such a map, as a
  complex-linear automorphism in finite dimension.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 2.2 (the complex-linear part of a real-linear map).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 2.2 (linear symplectic maps of `ℂⁿ` and their complex-linear parts).
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Multiplication by `i`, as a real-linear map, squares to `-1`. -/
private theorem lsmul_I_comp_lsmul_I (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] :
    ((LinearMap.lsmul ℂ V Complex.I).restrictScalars ℝ) ∘ₗ
        ((LinearMap.lsmul ℂ V Complex.I).restrictScalars ℝ) = -LinearMap.id := by
  ext v
  simp [smul_smul]

/-- The **complex-linear part** `z ↦ ½ (Ψ z - i Ψ (i z))` of a continuous real-linear operator
between complex normed spaces, as a continuous complex-linear operator. -/
def complexLinearPart (Ψ : E →L[ℝ] F) : E →L[ℂ] F where
  toLinearMap := LinearMap.complexOfMapISmul
    (TauCeti.complexLinearPart ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ)
      ((LinearMap.lsmul ℂ F Complex.I).restrictScalars ℝ) (Ψ : E →ₗ[ℝ] F))
    fun v => by
      have h := (TauCeti.complexLinearPart_isComplexLinear (lsmul_I_comp_lsmul_I E)
        (lsmul_I_comp_lsmul_I F) (Ψ : E →ₗ[ℝ] F)).apply v
      simp only [TauCeti.complexLinearPart_apply, LinearMap.coe_restrictScalars,
        LinearMap.lsmul_apply] at h ⊢
      rw [h]
  cont := by
    refine Continuous.congr (f := fun v => (2⁻¹ : ℝ) • (Ψ v - Complex.I • Ψ (Complex.I • v)))
      (by fun_prop) fun v => ?_
    simp

/-- The defining formula of the complex-linear part. -/
@[simp]
theorem complexLinearPart_apply (Ψ : E →L[ℝ] F) (v : E) :
    Ψ.complexLinearPart v = (2⁻¹ : ℝ) • (Ψ v - Complex.I • Ψ (Complex.I • v)) := by
  simp [complexLinearPart]

/-- The complex-linear part is, as a function, the algebraic complex-linear part
`TauCeti.complexLinearPart` for the complex structures given by multiplication by `i`. -/
theorem coe_complexLinearPart (Ψ : E →L[ℝ] F) :
    ⇑Ψ.complexLinearPart =
      TauCeti.complexLinearPart ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ)
        ((LinearMap.lsmul ℂ F Complex.I).restrictScalars ℝ) (Ψ : E →ₗ[ℝ] F) := by
  ext v
  simp

/-- A complex-linear operator is its own complex-linear part. -/
@[simp]
theorem complexLinearPart_restrictScalars (f : E →L[ℂ] F) :
    (f.restrictScalars ℝ).complexLinearPart = f := by
  ext v
  simp only [complexLinearPart_apply, coe_restrictScalars', map_smul, smul_smul, Complex.I_mul_I,
    neg_one_smul, sub_neg_eq_add]
  module

/-- Postcomposing with a complex-linear operator commutes with taking complex-linear parts. -/
@[simp]
theorem complexLinearPart_restrictScalars_comp (f : F →L[ℂ] G) (Ψ : E →L[ℝ] F) :
    ((f.restrictScalars ℝ).comp Ψ).complexLinearPart = f.comp Ψ.complexLinearPart := by
  ext v
  simp [map_smul, map_sub]

/-- Precomposing with a complex-linear operator commutes with taking complex-linear parts. -/
@[simp]
theorem complexLinearPart_comp_restrictScalars (Ψ : F →L[ℝ] G) (f : E →L[ℂ] F) :
    (Ψ.comp (f.restrictScalars ℝ)).complexLinearPart = Ψ.complexLinearPart.comp f := by
  ext v
  simp [map_smul]

/-- The real-linear operator underlying the complex-linear part is
`½ (Ψ - i ∘ Ψ ∘ i)`. -/
theorem restrictScalars_complexLinearPart (Ψ : E →L[ℝ] F) :
    Ψ.complexLinearPart.restrictScalars ℝ =
      (2⁻¹ : ℝ) • (Ψ - (Complex.I • ContinuousLinearMap.id ℝ F).comp
        (Ψ.comp (Complex.I • ContinuousLinearMap.id ℝ E))) := by
  ext v
  simp

/-- **The complex-linear part depends continuously on the operator.** -/
theorem continuous_complexLinearPart :
    Continuous (complexLinearPart : (E →L[ℝ] F) → E →L[ℂ] F) := by
  refine (restrictScalarsIsometry ℂ E F ℝ ℝ).isometry.isUniformInducing.isInducing.continuous_iff.2
    ?_
  simp only [Function.comp_def, coe_restrictScalarsIsometry, restrictScalars_complexLinearPart]
  have hJE : Continuous fun _ : E →L[ℝ] F => Complex.I • ContinuousLinearMap.id ℝ E :=
    continuous_const
  have hJF : Continuous fun _ : E →L[ℝ] F => Complex.I • ContinuousLinearMap.id ℝ F :=
    continuous_const
  exact (continuous_id.sub (hJF.clm_comp (continuous_id.clm_comp hJE))).const_smul (2⁻¹ : ℝ)

/-! ### The complex-linear part of a linear symplectic map -/

section Symplectic

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- For a real-linear map `Ψ` preserving the symplectic form `Im ⟪·, ·⟫`, the complex-linear part
`P` and the complex-antilinear part `Ψ - P` satisfy `‖P z‖² = ‖z‖² + ‖Ψ z - P z‖²`. -/
theorem norm_sq_complexLinearPart_apply {Ψ : V →L[ℝ] W}
    (hΨ : ∀ x y, (⟪Ψ x, Ψ y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) (z : V) :
    ‖Ψ.complexLinearPart z‖ ^ 2 = ‖z‖ ^ 2 + ‖Ψ z - Ψ.complexLinearPart z‖ ^ 2 := by
  set a := Ψ.complexLinearPart z
  set b := Ψ z - a
  -- `Ψ z = a + b` and `Ψ (i z) = i a - i b`.
  have hz : Ψ z = a + b := by simp [b]
  have hIz : Ψ (Complex.I • z) = Complex.I • a - Complex.I • b := by
    have hI : Complex.I • Complex.I • Ψ (Complex.I • z) = -Ψ (Complex.I • z) := by
      rw [smul_smul, Complex.I_mul_I, neg_one_smul]
    simp only [a, b, complexLinearPart_apply]
    linear_combination (norm := module) hI
  have key := hΨ z (Complex.I • z)
  rw [hz, hIz] at key
  simp only [inner_add_left, inner_sub_right, inner_smul_right, Complex.add_im, Complex.sub_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] at key
  rw [← inner_conj_symm a b] at key
  have hV (v : V) : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  have hW (w : W) : (⟪w, w⟫_ℂ).re = ‖w‖ ^ 2 := by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) w
  simp only [Complex.add_re, Complex.conj_re, hV, hW] at key
  linarith

/-- The complex-linear part of a real-linear map preserving `Im ⟪·, ·⟫` is injective. -/
theorem complexLinearPart_injective {Ψ : V →L[ℝ] W}
    (hΨ : ∀ x y, (⟪Ψ x, Ψ y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) :
    Function.Injective Ψ.complexLinearPart := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  have h := norm_sq_complexLinearPart_apply hΨ z
  rw [hz, norm_zero] at h
  have hz2 : ‖z‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖Ψ z - 0‖, sq_nonneg ‖z‖]
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hz2)

variable [FiniteDimensional ℂ V]

/-- The complex-linear part of a real-linear map preserving `Im ⟪·, ·⟫`, as a complex-linear
automorphism. -/
def complexLinearPartEquiv (Ψ : V →L[ℝ] V) (hΨ : ∀ x y, (⟪Ψ x, Ψ y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) :
    V ≃L[ℂ] V :=
  (LinearEquiv.ofInjectiveEndo (Ψ.complexLinearPart : V →ₗ[ℂ] V)
    (complexLinearPart_injective hΨ)).toContinuousLinearEquiv

/-- The automorphism `ContinuousLinearMap.complexLinearPartEquiv` is the complex-linear part. -/
@[simp]
theorem coe_complexLinearPartEquiv (Ψ : V →L[ℝ] V)
    (hΨ : ∀ x y, (⟪Ψ x, Ψ y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) :
    (Ψ.complexLinearPartEquiv hΨ : V →L[ℂ] V) = Ψ.complexLinearPart :=
  (rfl)

/-- The automorphism `ContinuousLinearMap.complexLinearPartEquiv` acts as the complex-linear
part. -/
@[simp]
theorem complexLinearPartEquiv_apply (Ψ : V →L[ℝ] V)
    (hΨ : ∀ x y, (⟪Ψ x, Ψ y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) (z : V) :
    Ψ.complexLinearPartEquiv hΨ z = Ψ.complexLinearPart z :=
  (rfl)

end Symplectic


end ContinuousLinearMap
