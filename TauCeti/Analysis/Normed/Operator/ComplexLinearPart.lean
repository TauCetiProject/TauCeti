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
public import TauCeti.Topology.Algebra.Module.ComplexSmulI
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.Analysis.Normed.Module.RCLike.Basic

/-!
# The complex-linear part of a real-linear operator

A continuous real-linear operator `Ψ : E →L[ℝ] F` between complex normed spaces has a
**complex-linear part**

`Ψ.complexLinearPart z = ½ (Ψ z - i Ψ (i z))`,

which is a continuous complex-linear operator (`ContinuousLinearMap.complexLinearPart`). Its
underlying real-linear map is the algebraic complex-linear part `TauCeti.complexLinearPart` for the
complex structures given by multiplication by `i`
(`ContinuousLinearMap.coe_complexLinearPart`). Likewise the **complex-antilinear part**
`Ψ.complexAntilinearPart z = ½ (Ψ z + i Ψ (i z))` is a continuous complex-antilinear operator
(`ContinuousLinearMap.complexAntilinearPart`), and `Ψ` is the sum of its two parts. A
complex-linear operator is its own complex-linear part and has zero complex-antilinear part, and
taking either part commutes with composition by complex-linear operators on either side. Both
parts depend continuously on `Ψ` (`ContinuousLinearMap.continuous_complexLinearPart`,
`ContinuousLinearMap.continuous_complexAntilinearPart`), so a continuous family of real-linear
operators has continuous families of complex-linear and complex-antilinear parts.

For a real-linear map `Ψ` between complex inner product spaces preserving the standard
symplectic form `Im ⟪·, ·⟫`, the complex-linear part `P` and the complex-antilinear part `A`
satisfy `‖P z‖² = ‖z‖² + ‖A z‖²` (`ContinuousLinearMap.norm_sq_complexLinearPart_apply`).
So the complex-linear part of a linear symplectic map is injective, and for an endomorphism of a
finite-dimensional space it is a complex-linear automorphism
(`ContinuousLinearMap.complexLinearPartEquiv`), in particular of nonzero determinant
(`ContinuousLinearMap.det_complexLinearPart_ne_zero`). This is how the graph of a linear
symplectic map is moved into place by complex-linear automorphisms in
`TauCeti.LinearAlgebra.TotallyReal.Maslov.Symplectic`.

## Main declarations

* `ContinuousLinearMap.complexLinearPart`: the complex-linear part of a real-linear operator.
* `ContinuousLinearMap.complexAntilinearPart`: the complex-antilinear part of a real-linear
  operator, with `ContinuousLinearMap.complexLinearPart_add_complexAntilinearPart_apply`.
* `ContinuousLinearMap.complexLinearPart_add`, `ContinuousLinearMap.complexLinearPart_smul`, …:
  real-linearity in the operator.
* `ContinuousLinearMap.complexLinearPart_restrictScalars`: a complex-linear operator is its own
  complex-linear part.
* `ContinuousLinearMap.complexLinearPart_restrictScalars_comp`,
  `ContinuousLinearMap.complexLinearPart_comp_restrictScalars`: compatibility with composition by
  complex-linear operators.
* `ContinuousLinearMap.restrictScalars_complexLinearPart`: the underlying real-linear operator
  `½ (Ψ - i ∘ Ψ ∘ i)`.
* `ContinuousLinearMap.continuous_complexLinearPart`: continuity in the operator.
* `ContinuousLinearMap.complexAntilinearPart_add`, `ContinuousLinearMap.complexAntilinearPart_smul`,
  `ContinuousLinearMap.complexAntilinearPart_restrictScalars`,
  `ContinuousLinearMap.complexAntilinearPart_restrictScalars_comp`,
  `ContinuousLinearMap.complexAntilinearPart_comp_restrictScalars`,
  `ContinuousLinearMap.continuous_complexAntilinearPart`: the same API for the complex-antilinear
  part.
* `ContinuousLinearMap.norm_sq_complexLinearPart_apply`: the norm identity for a linear map
  preserving `Im ⟪·, ·⟫`.
* `ContinuousLinearMap.complexLinearPartEquiv`: the complex-linear part of such a map, as a
  complex-linear automorphism in finite dimension.
* `ContinuousLinearMap.det_complexLinearPart_ne_zero`: its determinant is nonzero.

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

/-- The **complex-linear part** `z ↦ ½ (Ψ z - i Ψ (i z))` of a continuous real-linear operator
between complex normed spaces, as a continuous complex-linear operator. -/
def complexLinearPart (Ψ : E →L[ℝ] F) : E →L[ℂ] F :=
  complexOfMapISmul
    ((2⁻¹ : ℝ) • (Ψ - (Complex.smulIEquiv F : F →L[ℝ] F).comp
      (Ψ.comp (Complex.smulIEquiv E : E →L[ℝ] E))))
    fun v => by
      have hI : Complex.I • Complex.I • Ψ (Complex.I • v) = -Ψ (Complex.I • v) := by
        rw [smul_smul, Complex.I_mul_I, neg_one_smul]
      simp only [smul_apply, sub_apply, comp_apply, ContinuousLinearEquiv.coe_coe,
        Complex.smulIEquiv_apply, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
      linear_combination (norm := module) (2⁻¹ : ℝ) • hI

/-- The defining formula of the complex-linear part. -/
@[simp]
theorem complexLinearPart_apply (Ψ : E →L[ℝ] F) (v : E) :
    Ψ.complexLinearPart v = (2⁻¹ : ℝ) • (Ψ v - Complex.I • Ψ (Complex.I • v)) := by
  simp [complexLinearPart]

/-- The complex-linear part is, as a function, the algebraic complex-linear part
`TauCeti.complexLinearPart` for the complex structures given by multiplication by `i`. -/
theorem coe_complexLinearPart (Ψ : E →L[ℝ] F) :
    ⇑Ψ.complexLinearPart =
      TauCeti.complexLinearPart (DistribSMul.toLinearMap ℝ E Complex.I)
        (DistribSMul.toLinearMap ℝ F Complex.I) (Ψ : E →ₗ[ℝ] F) := by
  ext v
  simp

/-- The **complex-antilinear part** `z ↦ ½ (Ψ z + i Ψ (i z))` of a continuous real-linear
operator between complex normed spaces, as a continuous complex-antilinear operator. -/
def complexAntilinearPart (Ψ : E →L[ℝ] F) : E →L⋆[ℂ] F where
  toFun v := (2⁻¹ : ℝ) • (Ψ v + Complex.I • Ψ (Complex.I • v))
  map_add' v w := by simp only [map_add, smul_add]; module
  map_smul' c v := by
    -- Split `c • v` into real multiples of `v` and `I • v`.
    rw [← Complex.re_smul_add_im_smul c v, ← Complex.re_smul_add_im_smul (starRingEnd ℂ c)]
    simp only [smul_add, smul_comm Complex.I, smul_smul, Complex.I_mul_I, neg_smul, one_smul,
      map_add, map_smul, map_neg, Complex.conj_re, Complex.conj_im]
    module
  cont := by fun_prop

/-- The defining formula of the complex-antilinear part. -/
@[simp]
theorem complexAntilinearPart_apply (Ψ : E →L[ℝ] F) (v : E) :
    Ψ.complexAntilinearPart v = (2⁻¹ : ℝ) • (Ψ v + Complex.I • Ψ (Complex.I • v)) :=
  (rfl)

/-- The complex-antilinear part is, as a function, the algebraic complex-antilinear part
`TauCeti.complexAntilinearPart` for the complex structures given by multiplication by `i`. -/
theorem coe_complexAntilinearPart (Ψ : E →L[ℝ] F) :
    ⇑Ψ.complexAntilinearPart =
      TauCeti.complexAntilinearPart (DistribSMul.toLinearMap ℝ E Complex.I)
        (DistribSMul.toLinearMap ℝ F Complex.I) (Ψ : E →ₗ[ℝ] F) := by
  ext v
  simp

/-- A real-linear operator is the sum of its complex-linear and complex-antilinear parts. -/
theorem complexLinearPart_add_complexAntilinearPart_apply (Ψ : E →L[ℝ] F) (v : E) :
    Ψ.complexLinearPart v + Ψ.complexAntilinearPart v = Ψ v := by
  simp only [complexLinearPart_apply, complexAntilinearPart_apply]
  module

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

/-- The complex-linear part of `0` is `0`. -/
@[simp]
theorem complexLinearPart_zero : (0 : E →L[ℝ] F).complexLinearPart = 0 := by
  ext v
  simp

/-- The complex-linear part is additive. -/
@[simp]
theorem complexLinearPart_add (Ψ Φ : E →L[ℝ] F) :
    (Ψ + Φ).complexLinearPart = Ψ.complexLinearPart + Φ.complexLinearPart := by
  ext v
  simp only [complexLinearPart_apply, add_apply]
  module

/-- The complex-linear part commutes with negation. -/
@[simp]
theorem complexLinearPart_neg (Ψ : E →L[ℝ] F) :
    (-Ψ).complexLinearPart = -Ψ.complexLinearPart := by
  ext v
  simp only [complexLinearPart_apply, neg_apply]
  module

/-- The complex-linear part commutes with subtraction. -/
@[simp]
theorem complexLinearPart_sub (Ψ Φ : E →L[ℝ] F) :
    (Ψ - Φ).complexLinearPart = Ψ.complexLinearPart - Φ.complexLinearPart := by
  ext v
  simp only [complexLinearPart_apply, sub_apply]
  module

/-- The complex-linear part commutes with real scalar multiplication. -/
@[simp]
theorem complexLinearPart_smul (c : ℝ) (Ψ : E →L[ℝ] F) :
    (c • Ψ).complexLinearPart = c • Ψ.complexLinearPart := by
  ext v
  simp only [complexLinearPart_apply, smul_apply]
  rw [smul_comm Complex.I c]
  module

/-- The real-linear operator underlying the complex-linear part is
`½ (Ψ - i ∘ Ψ ∘ i)`. -/
theorem restrictScalars_complexLinearPart (Ψ : E →L[ℝ] F) :
    Ψ.complexLinearPart.restrictScalars ℝ =
      (2⁻¹ : ℝ) • (Ψ - (Complex.smulIEquiv F : F →L[ℝ] F).comp
        (Ψ.comp (Complex.smulIEquiv E : E →L[ℝ] E))) :=
  restrictScalars_complexOfMapISmul _ _

/-- **The complex-linear part depends continuously on the operator.** -/
theorem continuous_complexLinearPart :
    Continuous (complexLinearPart : (E →L[ℝ] F) → E →L[ℂ] F) := by
  refine (restrictScalarsIsometry ℂ E F ℝ ℝ).isometry.isUniformInducing.isInducing.continuous_iff.2
    ?_
  simp only [Function.comp_def, coe_restrictScalarsIsometry, restrictScalars_complexLinearPart]
  have hJE : Continuous fun _ : E →L[ℝ] F => (Complex.smulIEquiv E : E →L[ℝ] E) :=
    continuous_const
  have hJF : Continuous fun _ : E →L[ℝ] F => (Complex.smulIEquiv F : F →L[ℝ] F) :=
    continuous_const
  exact (continuous_id.sub (hJF.clm_comp (continuous_id.clm_comp hJE))).const_smul (2⁻¹ : ℝ)

/-- The complex-antilinear part of `0` is `0`. -/
@[simp]
theorem complexAntilinearPart_zero : (0 : E →L[ℝ] F).complexAntilinearPart = 0 := by
  ext v
  simp

/-- The complex-antilinear part is additive. -/
@[simp]
theorem complexAntilinearPart_add (Ψ Φ : E →L[ℝ] F) :
    (Ψ + Φ).complexAntilinearPart = Ψ.complexAntilinearPart + Φ.complexAntilinearPart := by
  ext v
  simp only [complexAntilinearPart_apply, add_apply]
  module

/-- The complex-antilinear part commutes with negation. -/
@[simp]
theorem complexAntilinearPart_neg (Ψ : E →L[ℝ] F) :
    (-Ψ).complexAntilinearPart = -Ψ.complexAntilinearPart := by
  ext v
  simp only [complexAntilinearPart_apply, neg_apply]
  module

/-- The complex-antilinear part commutes with subtraction. -/
@[simp]
theorem complexAntilinearPart_sub (Ψ Φ : E →L[ℝ] F) :
    (Ψ - Φ).complexAntilinearPart = Ψ.complexAntilinearPart - Φ.complexAntilinearPart := by
  ext v
  simp only [complexAntilinearPart_apply, sub_apply]
  module

/-- The complex-antilinear part commutes with real scalar multiplication. -/
@[simp]
theorem complexAntilinearPart_smul (c : ℝ) (Ψ : E →L[ℝ] F) :
    (c • Ψ).complexAntilinearPart = c • Ψ.complexAntilinearPart := by
  ext v
  simp only [complexAntilinearPart_apply, smul_apply]
  rw [smul_comm Complex.I c]
  module

/-- A complex-linear operator has zero complex-antilinear part. -/
@[simp]
theorem complexAntilinearPart_restrictScalars (f : E →L[ℂ] F) :
    (f.restrictScalars ℝ).complexAntilinearPart = 0 := by
  ext v
  simp only [complexAntilinearPart_apply, coe_restrictScalars', map_smul, smul_smul,
    Complex.I_mul_I, neg_one_smul, add_neg_cancel, smul_zero, zero_apply]

/-- Postcomposing with a complex-linear operator commutes with taking complex-antilinear parts. -/
@[simp]
theorem complexAntilinearPart_restrictScalars_comp (f : F →L[ℂ] G) (Ψ : E →L[ℝ] F) :
    ((f.restrictScalars ℝ).comp Ψ).complexAntilinearPart = f.comp Ψ.complexAntilinearPart := by
  ext v
  simp [map_smul, map_add]

/-- Precomposing with a complex-linear operator commutes with taking complex-antilinear parts. -/
@[simp]
theorem complexAntilinearPart_comp_restrictScalars (Ψ : F →L[ℝ] G) (f : E →L[ℂ] F) :
    (Ψ.comp (f.restrictScalars ℝ)).complexAntilinearPart = Ψ.complexAntilinearPart.comp f := by
  ext v
  simp [map_smul]

/-- **The complex-antilinear part depends continuously on the operator.** -/
theorem continuous_complexAntilinearPart :
    Continuous (complexAntilinearPart : (E →L[ℝ] F) → E →L⋆[ℂ] F) := by
  -- The complex-antilinear part is additive in the operator and bounded by its norm.
  refine AddMonoidHomClass.continuous_of_bound
    (AddMonoidHom.mk' complexAntilinearPart complexAntilinearPart_add) 1 fun Ψ => ?_
  rw [one_mul]
  refine opNorm_le_bound _ (norm_nonneg Ψ) fun v => ?_
  have h := Ψ.le_opNorm_of_le (x := Complex.I • v) (c := ‖v‖) (by simp [norm_smul])
  exact TauCeti.norm_two_inv_smul_add_le (𝕜 := ℝ) (Ψ.le_opNorm v) (by simpa [norm_smul] using h)

/-! ### The complex-linear part of a linear symplectic map -/

section Symplectic

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- For a real-linear map `Ψ` preserving the symplectic form `Im ⟪·, ·⟫`, the complex-linear part
`P` and the complex-antilinear part `A` satisfy `‖P z‖² = ‖z‖² + ‖A z‖²`. -/
theorem norm_sq_complexLinearPart_apply {Ψ : V →L[ℝ] W}
    (hΨ : ∀ x y, (⟪Ψ x, Ψ y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) (z : V) :
    ‖Ψ.complexLinearPart z‖ ^ 2 = ‖z‖ ^ 2 + ‖Ψ.complexAntilinearPart z‖ ^ 2 := by
  set a := Ψ.complexLinearPart z
  set b := Ψ.complexAntilinearPart z
  -- `Ψ z = a + b` and `Ψ (i z) = i a - i b`.
  have hz : Ψ z = a + b := (complexLinearPart_add_complexAntilinearPart_apply Ψ z).symm
  have hIz : Ψ (Complex.I • z) = Complex.I • a - Complex.I • b := by
    have hI : Complex.I • Complex.I • Ψ (Complex.I • z) = -Ψ (Complex.I • z) := by
      rw [smul_smul, Complex.I_mul_I, neg_one_smul]
    simp only [a, b, complexLinearPart_apply, complexAntilinearPart_apply]
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
  have hz2 : ‖z‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖Ψ.complexAntilinearPart z‖, sq_nonneg ‖z‖]
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

/-- The linear automorphism underlying `ContinuousLinearMap.complexLinearPartEquiv` is the
complex-linear part. -/
@[simp]
theorem coe_toLinearEquiv_complexLinearPartEquiv (Ψ : V →L[ℝ] V)
    (hΨ : ∀ x y, (⟪Ψ x, Ψ y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) :
    ((Ψ.complexLinearPartEquiv hΨ).toLinearEquiv : V →ₗ[ℂ] V) = Ψ.complexLinearPart :=
  (rfl)

/-- The complex-linear part of a real-linear endomorphism preserving `Im ⟪·, ·⟫` has nonzero
determinant. -/
theorem det_complexLinearPart_ne_zero {Ψ : V →L[ℝ] V}
    (hΨ : ∀ x y, (⟪Ψ x, Ψ y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) :
    LinearMap.det (Ψ.complexLinearPart : V →ₗ[ℂ] V) ≠ 0 := by
  rw [← coe_toLinearEquiv_complexLinearPartEquiv Ψ hΨ]
  exact (Ψ.complexLinearPartEquiv hΨ).toLinearEquiv.isUnit_det'.ne_zero

/-- The automorphism `ContinuousLinearMap.complexLinearPartEquiv` acts as the complex-linear
part. -/
@[simp]
theorem complexLinearPartEquiv_apply (Ψ : V →L[ℝ] V)
    (hΨ : ∀ x y, (⟪Ψ x, Ψ y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) (z : V) :
    Ψ.complexLinearPartEquiv hΨ z = Ψ.complexLinearPart z :=
  (rfl)

end Symplectic


end ContinuousLinearMap
