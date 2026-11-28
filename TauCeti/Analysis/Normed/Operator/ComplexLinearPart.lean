/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.Algebra.Module.Complement
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

A continuous real-linear operator `Ψ : E →L[ℝ] F` between complex topological modules has a
**complex-linear part**

`Ψ.complexLinearPart z = ½ (Ψ z - i Ψ (i z))`,

which is a continuous complex-linear operator (`ContinuousLinearMap.complexLinearPart`). Its
underlying real-linear map is the algebraic complex-linear part `TauCeti.complexLinearPart` for the
complex structures given by multiplication by `i`
(`ContinuousLinearMap.coe_complexLinearPart`). Likewise the **complex-antilinear part**
`Ψ.complexAntilinearPart z = ½ (Ψ z + i Ψ (i z))` is a continuous complex-antilinear operator
(`ContinuousLinearMap.complexAntilinearPart`), and `Ψ` is the sum of its two parts. A
complex-linear operator is its own complex-linear part and has zero complex-antilinear part, and
taking either part commutes with composition by complex-linear operators on either side. Between
complex normed spaces both parts depend continuously on `Ψ`
(`ContinuousLinearMap.continuous_complexLinearPart`,
`ContinuousLinearMap.continuous_complexAntilinearPart`), so a continuous family of real-linear
operators has continuous families of complex-linear and complex-antilinear parts. The
complex-linear part of a continuous real-linear projection onto a complex submodule is a
continuous complex-linear projection onto it, so a complex submodule complemented over the reals
is complemented over the complex numbers (`Submodule.ClosedComplemented.of_restrictScalars`).
For real structures on `E` and `F` given separately and compatible with the complex ones, the
complex-antilinear part is a continuous real-linear operator on `E →L[ℝ] F`
(`ContinuousLinearMap.complexAntilinearPartL`), an idempotent operator whose fixed points are the
complex-antilinear maps (`ContinuousLinearMap.complexAntilinearPartL_eq_self_iff`) and whose kernel
consists of the complex-linear maps (`ContinuousLinearMap.complexAntilinearPartL_eq_zero_iff`).

For a real-linear map `Ψ` between complex inner product spaces preserving the standard
symplectic form `Im ⟪·, ·⟫`, the complex-linear part `P` and the complex-antilinear part `A`
satisfy `‖P z‖² = ‖z‖² + ‖A z‖²` (`ContinuousLinearMap.norm_sq_complexLinearPart_apply`).
So the complex-linear part of a linear symplectic map is injective, and for an endomorphism of a
finite-dimensional space it is a complex-linear automorphism
(`ContinuousLinearMap.complexLinearPartEquiv`), in particular of nonzero determinant
(`ContinuousLinearMap.det_complexLinearPart_ne_zero`). This is how the graph of a linear
symplectic map is moved into place by complex-linear automorphisms in
`TauCeti.LinearAlgebra.TotallyReal.Maslov.Symplectic`.

For a continuous real-bilinear map `L : E →L[ℝ] E' →L[ℝ] F` between complex seminormed spaces with
compatible real structures, applying the complex-linear/antilinear projections in each argument
decomposes `L` into four `(ℂ, ℂ)`-linear/antilinear components `L.sesquiPart b₁ b₂`
(`b₁, b₂ : Bool`, where `false` selects complex-linearity and `true` selects complex-antilinearity).
These are mutually orthogonal contractive projections summing to `L`
(`ContinuousLinearMap.sum_sesquiPart`, `ContinuousLinearMap.sesquiPart_sesquiPart`,
`ContinuousLinearMap.norm_sesquiPart_le`).

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
* `Submodule.ClosedComplemented.of_restrictScalars`: a complex submodule with a continuous
  real-linear projection onto it has a continuous complex-linear one.
* `ContinuousLinearMap.complexAntilinearPart_add`, `ContinuousLinearMap.complexAntilinearPart_smul`,
  `ContinuousLinearMap.complexAntilinearPart_restrictScalars`,
  `ContinuousLinearMap.complexAntilinearPart_restrictScalars_comp`,
  `ContinuousLinearMap.complexAntilinearPart_comp_restrictScalars`,
  `ContinuousLinearMap.continuous_complexAntilinearPart`: the same API for the complex-antilinear
  part.
* `ContinuousLinearMap.complexAntilinearPartL`: the complex-antilinear part as a continuous
  real-linear operator on real-linear maps, for arbitrary compatible real structures, with
  `ContinuousLinearMap.complexAntilinearPartL_eq_self_iff`,
  `ContinuousLinearMap.complexAntilinearPartL_eq_zero_iff` and the postcomposition and
  precomposition rules `ContinuousLinearMap.complexAntilinearPartL_restrictScalars_comp` and
  `ContinuousLinearMap.complexAntilinearPartL_comp_restrictScalars`.
* `ContinuousLinearMap.sesquiPart`: the four-part `(ℂ, ℂ)`-linear/antilinear decomposition of a
  continuous real-bilinear operator `L : E →L[ℝ] E' →L[ℝ] F`, with explicit evaluation formulas,
  real-linearity, flip symmetry, reconstruction (`ContinuousLinearMap.sum_sesquiPart`), complex
  scalar actions (`ContinuousLinearMap.sesquiPart_apply_smul`), mutual orthogonality/idempotence
  (`ContinuousLinearMap.sesquiPart_sesquiPart`), norm contraction
  (`ContinuousLinearMap.norm_sesquiPart_le`), and continuity.
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

section Module

variable {E F G : Type*} [AddCommGroup E] [TopologicalSpace E] [Module ℝ E] [Module ℂ E]
  [IsScalarTower ℝ ℂ E] [ContinuousConstSMul ℂ E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module ℝ F] [Module ℂ F]
  [IsScalarTower ℝ ℂ F] [ContinuousConstSMul ℝ F] [ContinuousConstSMul ℂ F]
  [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [Module ℝ G] [Module ℂ G]
  [IsScalarTower ℝ ℂ G] [ContinuousConstSMul ℝ G] [ContinuousConstSMul ℂ G]

/-- The **complex-linear part** `z ↦ ½ (Ψ z - i Ψ (i z))` of a continuous real-linear operator
between complex modules, as a continuous complex-linear operator. -/
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
operator between complex modules, as a continuous complex-antilinear operator. -/
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

omit [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F] in
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

omit [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F] in
/-- Precomposing with a complex-linear operator commutes with taking complex-antilinear parts. -/
@[simp]
theorem complexAntilinearPart_comp_restrictScalars (Ψ : F →L[ℝ] G) (f : E →L[ℂ] F) :
    (Ψ.comp (f.restrictScalars ℝ)).complexAntilinearPart = Ψ.complexAntilinearPart.comp f := by
  ext v
  simp [map_smul]

end Module

section Normed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

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

end Normed

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

/-! ### Complex complements from real ones -/

section ClosedComplemented

open Complex

variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [Module ℝ V]
  [Module ℂ V] [IsScalarTower ℝ ℂ V] [ContinuousConstSMul ℂ V]

/-- **Complex complements from real ones.** A complex submodule `K` that is the range of a
continuous real-linear projection `P` is the range of a continuous complex-linear projection, the
complex-linear part `x ↦ ½ (P x - i • P (i • x))` of `P`. -/
theorem Submodule.ClosedComplemented.of_restrictScalars {K : Submodule ℂ V}
    (hK : (K.restrictScalars ℝ).ClosedComplemented) : K.ClosedComplemented := by
  obtain ⟨P, hP⟩ := hK
  -- `P` lands in `K.restrictScalars ℝ`, whose carrier is definitionally that of `K`, so `P` is
  -- retyped as a map into `K` by definitional unfolding.
  let P' : V →L[ℝ] K := P
  have hP' (x : K) : P' x = x := hP x
  -- Real scalars act continuously on `K` since they act through the complex ones.
  have : ContinuousConstSMul ℝ K := IsScalarTower.continuousConstSMul ℝ ℂ K
  refine ⟨P'.complexLinearPart, fun x ↦ ?_⟩
  have hIx : P' (I • (x : V)) = I • x := hP' (I • x)
  rw [ContinuousLinearMap.complexLinearPart_apply, hP', hIx]
  match_scalars; norm_num [I_mul_I]

end ClosedComplemented

/-! ### The complex-antilinear part as an operator on real-linear maps -/

namespace ContinuousLinearMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G]
  [IsScalarTower ℝ ℂ G]

/-- Multiplication by `i`, as a real-linear map, squares to `-1`. -/
theorem lsmul_I_mul_lsmul_I :
    (lsmul ℝ ℂ Complex.I : F →L[ℝ] F) * lsmul ℝ ℂ Complex.I = -1 := by
  ext v
  simp [smul_smul]

/-- The complex-antilinear part `Ψ ↦ ½ (Ψ + i • Ψ ∘ i)`, as a continuous real-linear operator on
the real-linear maps `E →L[ℝ] F` between complex normed spaces. Unlike
`ContinuousLinearMap.complexAntilinearPart`, the real structures of `E` and `F` are arbitrary real
normed space structures compatible with the complex ones, such as the real model fibre of a
complex vector bundle restricted to the reals by `VectorBundle.restrictScalars`. -/
def complexAntilinearPartL : (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
  (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ (E →L[ℝ] F) +
    (compL ℝ E F F (Complex.I • ContinuousLinearMap.id ℝ F)).comp
      ((compL ℝ E E F).flip (Complex.I • ContinuousLinearMap.id ℝ E)))

/-- The defining formula of `ContinuousLinearMap.complexAntilinearPartL`. -/
@[simp]
theorem complexAntilinearPartL_apply_apply (Ψ : E →L[ℝ] F) (v : E) :
    complexAntilinearPartL Ψ v = (2⁻¹ : ℝ) • (Ψ v + Complex.I • Ψ (Complex.I • v)) :=
  (rfl)

/-- The value on `1` of the complex antilinear part of a real linear map `L : ℂ → F` is
`½ (L 1 + i L i)`. -/
theorem complexAntilinearPartL_apply_one (L : ℂ →L[ℝ] F) :
    complexAntilinearPartL L 1 = (2⁻¹ : ℝ) • (L 1 + lsmul ℝ ℂ Complex.I (L Complex.I)) := by
  simp

/-- `ContinuousLinearMap.complexAntilinearPartL` is the algebraic complex-antilinear part
`TauCeti.complexAntilinearPart` for the complex structures given by multiplication by `i`. -/
theorem toLinearMap_complexAntilinearPartL (Ψ : E →L[ℝ] F) :
    (complexAntilinearPartL Ψ : E →ₗ[ℝ] F) =
      TauCeti.complexAntilinearPart (DistribSMul.toLinearMap ℝ E Complex.I)
        (DistribSMul.toLinearMap ℝ F Complex.I) (Ψ : E →ₗ[ℝ] F) := by
  ext v
  simp [TauCeti.complexAntilinearPart_apply]

/-- A real-linear map is fixed by `ContinuousLinearMap.complexAntilinearPartL` exactly when it is
complex antilinear. -/
theorem complexAntilinearPartL_eq_self_iff {Ψ : E →L[ℝ] F} :
    complexAntilinearPartL Ψ = Ψ ↔ ∀ v, Ψ (Complex.I • v) = -(Complex.I • Ψ v) := by
  rw [← coe_inj, toLinearMap_complexAntilinearPartL]
  refine ⟨fun h ↦ (h ▸ TauCeti.isComplexAntilinear_complexAntilinearPart
    Complex.toLinearMap_I_comp_toLinearMap_I Complex.toLinearMap_I_comp_toLinearMap_I _).apply,
    fun h ↦ (TauCeti.isComplexAntilinear_of_apply h).complexAntilinearPart_eq
      Complex.toLinearMap_I_comp_toLinearMap_I⟩

/-- The image of `ContinuousLinearMap.complexAntilinearPartL` is complex antilinear. -/
theorem complexAntilinearPartL_apply_I_smul (Ψ : E →L[ℝ] F) (v : E) :
    complexAntilinearPartL Ψ (Complex.I • v) = -(Complex.I • complexAntilinearPartL Ψ v) :=
  (toLinearMap_complexAntilinearPartL Ψ ▸ TauCeti.isComplexAntilinear_complexAntilinearPart
    Complex.toLinearMap_I_comp_toLinearMap_I Complex.toLinearMap_I_comp_toLinearMap_I _).apply v

/-- `ContinuousLinearMap.complexAntilinearPartL` is idempotent. -/
@[simp]
theorem complexAntilinearPartL_complexAntilinearPartL (Ψ : E →L[ℝ] F) :
    complexAntilinearPartL (complexAntilinearPartL Ψ) = complexAntilinearPartL Ψ :=
  complexAntilinearPartL_eq_self_iff.2 (complexAntilinearPartL_apply_I_smul Ψ)

/-- A real-linear map is in the kernel of `ContinuousLinearMap.complexAntilinearPartL` exactly when
it is complex linear. -/
theorem complexAntilinearPartL_eq_zero_iff {Ψ : E →L[ℝ] F} :
    complexAntilinearPartL Ψ = 0 ↔ ∀ v, Ψ (Complex.I • v) = Complex.I • Ψ v := by
  rw [← coe_inj, toLinearMap_complexAntilinearPartL, ContinuousLinearMap.toLinearMap_zero,
    ← TauCeti.isComplexLinear_iff_complexAntilinearPart_eq_zero
      Complex.toLinearMap_I_comp_toLinearMap_I]
  exact ⟨fun h v ↦ h.apply v, fun h ↦ TauCeti.isComplexLinear_of_apply h⟩

/-- The complex-antilinear part of a complex-linear map vanishes. -/
@[simp]
theorem complexAntilinearPartL_restrictScalars (f : E →L[ℂ] F) :
    complexAntilinearPartL (f.restrictScalars ℝ) = 0 :=
  complexAntilinearPartL_eq_zero_iff.2 fun v ↦ by simp

/-- Postcomposing with a complex-linear operator commutes with
`ContinuousLinearMap.complexAntilinearPartL`. -/
@[simp]
theorem complexAntilinearPartL_restrictScalars_comp (f : F →L[ℂ] G) (Ψ : E →L[ℝ] F) :
    complexAntilinearPartL ((f.restrictScalars ℝ).comp Ψ) =
      (f.restrictScalars ℝ).comp (complexAntilinearPartL Ψ) := by
  ext v
  simp [map_smul]

/-- Precomposing with a complex-linear operator commutes with
`ContinuousLinearMap.complexAntilinearPartL`. -/
@[simp]
theorem complexAntilinearPartL_comp_restrictScalars (Ψ : F →L[ℝ] G) (f : E →L[ℂ] F) :
    complexAntilinearPartL (Ψ.comp (f.restrictScalars ℝ)) =
      (complexAntilinearPartL Ψ).comp (f.restrictScalars ℝ) := by
  ext v
  simp [map_smul]

end ContinuousLinearMap

/-! ### Four-part decomposition of continuous real-bilinear operators -/

namespace ContinuousLinearMap

variable {E E' F : Type*}
  [SeminormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [SeminormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedSpace ℂ E'] [IsScalarTower ℝ ℂ E']
  [SeminormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

/-- The four-part `(ℂ, ℂ)`-linear/antilinear decomposition of a continuous real-bilinear map
`L : E →L[ℝ] E' →L[ℝ] F` between complex seminormed spaces with compatible real structures.
For `b₁ b₂ : Bool`, `b₁ = false` (resp. `true`) selects complex-linearity (resp.
complex-antilinearity) in the first argument, and `b₂` selects the same in the second argument. -/
def sesquiPart (L : E →L[ℝ] E' →L[ℝ] F) (b₁ b₂ : Bool) : E →L[ℝ] E' →L[ℝ] F :=
  let S₂ := (compL ℝ E' F F (Complex.smulIEquiv F)).comp
    (L.flip.comp (Complex.smulIEquiv E' : E' →L[ℝ] E')).flip
  let L₂ := (2⁻¹ : ℝ) • if b₂ then L + S₂ else L - S₂
  let S₁ := ((compL ℝ E' F F (Complex.smulIEquiv F)).comp L₂).comp
    (Complex.smulIEquiv E : E →L[ℝ] E)
  (2⁻¹ : ℝ) • if b₁ then L₂ + S₁ else L₂ - S₁

/-- Explicit formula for `L.sesquiPart b₁ b₂ u v` in terms of `L` and multiplication by `I`. -/
theorem sesquiPart_apply (L : E →L[ℝ] E' →L[ℝ] F) (b₁ b₂ : Bool) (u : E) (v : E') :
    L.sesquiPart b₁ b₂ u v = (4⁻¹ : ℝ) • (L u v +
      (if b₁ then (1 : ℝ) else -1) • (Complex.I • L (Complex.I • u) v) +
      (if b₂ then (1 : ℝ) else -1) • (Complex.I • L u (Complex.I • v)) -
      (if b₁ = b₂ then (1 : ℝ) else -1) • L (Complex.I • u) (Complex.I • v)) := by
  have hI (x : F) : Complex.I • Complex.I • x = -x := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  cases b₁ <;> cases b₂ <;> simp only [sesquiPart, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, smul_apply, add_apply, sub_apply, comp_apply, flip_apply, compL_apply,
    ContinuousLinearEquiv.coe_coe, Complex.smulIEquiv_apply, smul_add, smul_sub,
    smul_comm Complex.I (2⁻¹ : ℝ), hI, smul_neg, neg_smul, one_smul] <;> module

/-- The four-part decomposition of `0` is `0`. -/
@[simp] theorem sesquiPart_zero (b₁ b₂ : Bool) : (0 : E →L[ℝ] E' →L[ℝ] F).sesquiPart b₁ b₂ = 0 := by
  ext u v; simp [sesquiPart_apply]

/-- `sesquiPart` is additive in the bilinear operator. -/
@[simp] theorem sesquiPart_add (L M : E →L[ℝ] E' →L[ℝ] F) (b₁ b₂ : Bool) :
    (L + M).sesquiPart b₁ b₂ = L.sesquiPart b₁ b₂ + M.sesquiPart b₁ b₂ := by
  ext u v; simp only [add_apply, sesquiPart_apply, smul_add]; module

/-- `sesquiPart` commutes with negation of the bilinear operator. -/
@[simp] theorem sesquiPart_neg (L : E →L[ℝ] E' →L[ℝ] F) (b₁ b₂ : Bool) :
    (-L).sesquiPart b₁ b₂ = -L.sesquiPart b₁ b₂ := by
  ext u v; simp only [neg_apply, sesquiPart_apply, smul_neg]; module

/-- `sesquiPart` commutes with subtraction of bilinear operators. -/
@[simp] theorem sesquiPart_sub (L M : E →L[ℝ] E' →L[ℝ] F) (b₁ b₂ : Bool) :
    (L - M).sesquiPart b₁ b₂ = L.sesquiPart b₁ b₂ - M.sesquiPart b₁ b₂ := by
  rw [sub_eq_add_neg, sesquiPart_add, sesquiPart_neg, ← sub_eq_add_neg]

/-- `sesquiPart` commutes with real scalar multiplication of the bilinear operator. -/
@[simp] theorem sesquiPart_smul (c : ℝ) (L : E →L[ℝ] E' →L[ℝ] F) (b₁ b₂ : Bool) :
    (c • L).sesquiPart b₁ b₂ = c • L.sesquiPart b₁ b₂ := by
  ext u v; simp only [smul_apply, sesquiPart_apply, smul_comm Complex.I c,
    smul_comm (if _ then (1 : ℝ) else -1) c]; module

/-- Flipping the arguments of `L` swaps the two Boolean indices of `sesquiPart`. -/
@[simp] theorem sesquiPart_flip (L : E →L[ℝ] E' →L[ℝ] F) (b₁ b₂ : Bool) :
    L.flip.sesquiPart b₁ b₂ = (L.sesquiPart b₂ b₁).flip := by
  ext v u; cases b₁ <;> cases b₂ <;> simp only [flip_apply, sesquiPart_apply, Bool.false_eq_true,
    Bool.true_eq_false, ↓reduceIte, one_smul, neg_smul] <;> module

/-- Every continuous real-bilinear map is the sum of its four `sesquiPart` components. -/
@[simp] theorem sum_sesquiPart (L : E →L[ℝ] E' →L[ℝ] F) :
    ∑ p : Bool × Bool, L.sesquiPart p.1 p.2 = L := by
  ext u v; simp only [Fintype.sum_prod_type, Fintype.sum_bool, add_apply, sesquiPart_apply,
    Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, one_smul, neg_smul]; module

/-- Pointwise reconstruction: `L u v` is the sum of its four `sesquiPart` components. -/
theorem sum_sesquiPart_apply (L : E →L[ℝ] E' →L[ℝ] F) (u : E) (v : E') :
    ∑ p : Bool × Bool, L.sesquiPart p.1 p.2 u v = L u v := by
  simpa only [sum_apply] using congrArg (fun M : E →L[ℝ] E' →L[ℝ] F ↦ M u v) (sum_sesquiPart L)

/-- Action of `Complex.I` in the first argument of `L.sesquiPart b₁ b₂`. -/
theorem sesquiPart_apply_I_smul_left (L : E →L[ℝ] E' →L[ℝ] F) (b₁ b₂ : Bool) (u : E) (v : E') :
    L.sesquiPart b₁ b₂ (Complex.I • u) v =
      (if b₁ then -Complex.I else Complex.I) • L.sesquiPart b₁ b₂ u v := by
  have hIE : Complex.I • Complex.I • u = -u := by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have hIF (x : F) : Complex.I • Complex.I • x = -x := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  cases b₁ <;> cases b₂ <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
    sesquiPart_apply, one_smul, hIE, hIF, map_neg, neg_apply, neg_smul, smul_add, smul_sub,
    smul_neg, smul_comm Complex.I (4⁻¹ : ℝ)] <;> module

/-- Action of `Complex.I` in the second argument of `L.sesquiPart b₁ b₂`. -/
theorem sesquiPart_apply_I_smul_right (L : E →L[ℝ] E' →L[ℝ] F) (b₁ b₂ : Bool) (u : E) (v : E') :
    L.sesquiPart b₁ b₂ u (Complex.I • v) =
      (if b₂ then -Complex.I else Complex.I) • L.sesquiPart b₁ b₂ u v := by
  simpa only [sesquiPart_flip, flip_apply] using sesquiPart_apply_I_smul_left L.flip b₂ b₁ v u

/-- Complex scalar action in the first argument of `L.sesquiPart b₁ b₂`. -/
theorem sesquiPart_apply_smul_left (L : E →L[ℝ] E' →L[ℝ] F) (b₁ b₂ : Bool) (z : ℂ) (u : E)
    (v : E') : L.sesquiPart b₁ b₂ (z • u) v =
      (if b₁ then starRingEnd ℂ z else z) • L.sesquiPart b₁ b₂ u v := by
  cases b₁
  · have h := ((L.sesquiPart false b₂).flip v).toLinearMap.complexOfMapISmul
      (fun x ↦ by simpa using sesquiPart_apply_I_smul_left L false b₂ x v) |>.map_smul z u
    rw [LinearMap.coe_complexOfMapISmul] at h
    simpa only [Bool.false_eq_true, ↓reduceIte, coe_coe, flip_apply] using h
  · exact ((L.sesquiPart true b₂).flip v).toLinearMap.map_smul_eq_conj_smul_of_map_I_smul
      (fun x ↦ by simpa [neg_smul] using sesquiPart_apply_I_smul_left L true b₂ x v) z u

/-- Complex scalar action in the second argument of `L.sesquiPart b₁ b₂`. -/
theorem sesquiPart_apply_smul_right (L : E →L[ℝ] E' →L[ℝ] F) (b₁ b₂ : Bool) (w : ℂ) (u : E)
    (v : E') : L.sesquiPart b₁ b₂ u (w • v) =
      (if b₂ then starRingEnd ℂ w else w) • L.sesquiPart b₁ b₂ u v := by
  simpa only [sesquiPart_flip, flip_apply] using sesquiPart_apply_smul_left L.flip b₂ b₁ w v u

/-- Simultaneous complex scalar action in both arguments of `L.sesquiPart b₁ b₂`. -/
theorem sesquiPart_apply_smul (L : E →L[ℝ] E' →L[ℝ] F) (b₁ b₂ : Bool) (z w : ℂ) (u : E) (v : E') :
    L.sesquiPart b₁ b₂ (z • u) (w • v) =
      ((if b₁ then starRingEnd ℂ z else z) * (if b₂ then starRingEnd ℂ w else w)) •
        L.sesquiPart b₁ b₂ u v := by
  rw [sesquiPart_apply_smul_left, sesquiPart_apply_smul_right, smul_smul]

/-- The four `sesquiPart` projections are mutually orthogonal idempotents. -/
@[simp] theorem sesquiPart_sesquiPart (L : E →L[ℝ] E' →L[ℝ] F) (b₁ b₂ c₁ c₂ : Bool) :
    (L.sesquiPart b₁ b₂).sesquiPart c₁ c₂ =
      if c₁ = b₁ ∧ c₂ = b₂ then L.sesquiPart b₁ b₂ else 0 := by
  ext u v; have hIF (x : F) : Complex.I • Complex.I • x = -x := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [sesquiPart_apply]; simp only [sesquiPart_apply_I_smul_left, sesquiPart_apply_I_smul_right]
  cases b₁ <;> cases b₂ <;> cases c₁ <;> cases c₂ <;> simp only [Bool.false_eq_true,
    Bool.true_eq_false, and_self, and_false, false_and, ↓reduceIte, zero_apply, one_smul, neg_smul,
    smul_neg, hIF] <;> module

/-- A continuous real-bilinear map is fixed by `sesquiPart · b₁ b₂` iff multiplication by `I` in
each argument acts by `± I`. -/
theorem sesquiPart_eq_self_iff {L : E →L[ℝ] E' →L[ℝ] F} {b₁ b₂ : Bool} :
    L.sesquiPart b₁ b₂ = L ↔
      (∀ u v, L (Complex.I • u) v = (if b₁ then -Complex.I else Complex.I) • L u v) ∧
      (∀ u v, L u (Complex.I • v) = (if b₂ then -Complex.I else Complex.I) • L u v) := by
  refine ⟨fun h ↦ ⟨fun u v ↦ by rw [← h, sesquiPart_apply_I_smul_left],
    fun u v ↦ by rw [← h, sesquiPart_apply_I_smul_right]⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  ext u v; have hIF (x : F) : Complex.I • Complex.I • x = -x := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [sesquiPart_apply, h₁, h₂, h₁, h₂]
  cases b₁ <;> cases b₂ <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
    one_smul, neg_smul, smul_neg, hIF] <;> module

/-- Each `sesquiPart` projection is contractive in operator norm: `‖L.sesquiPart b₁ b₂‖ ≤ ‖L‖`. -/
theorem norm_sesquiPart_le (L : E →L[ℝ] E' →L[ℝ] F) (b₁ b₂ : Bool) :
    ‖L.sesquiPart b₁ b₂‖ ≤ ‖L‖ := by
  refine opNorm_le_bound _ (norm_nonneg L) fun u ↦
    opNorm_le_bound _ (mul_nonneg (norm_nonneg L) (norm_nonneg u)) fun v ↦ ?_
  have h (x : E) (y : E') (hx : ‖x‖ = ‖u‖) (hy : ‖y‖ = ‖v‖) : ‖L x y‖ ≤ ‖L‖ * ‖u‖ * ‖v‖ :=
    hx ▸ hy ▸ L.le_opNorm₂ x y
  have hs (p : Prop) [Decidable p] (w : F) : ‖(if p then (1 : ℝ) else -1) • w‖ = ‖w‖ := by
    split_ifs <;> simp
  rw [sesquiPart_apply, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4⁻¹)]
  set t₁ := (if b₁ then (1 : ℝ) else -1) • (Complex.I • L (Complex.I • u) v)
  set t₂ := (if b₂ then (1 : ℝ) else -1) • (Complex.I • L u (Complex.I • v))
  set t₃ := (if b₁ = b₂ then (1 : ℝ) else -1) • L (Complex.I • u) (Complex.I • v)
  have ht₁ : ‖t₁‖ ≤ ‖L‖ * ‖u‖ * ‖v‖ := by
    rw [hs, norm_smul, Complex.norm_I, one_mul]; exact h _ _ (by simp [norm_smul]) rfl
  have ht₂ : ‖t₂‖ ≤ ‖L‖ * ‖u‖ * ‖v‖ := by
    rw [hs, norm_smul, Complex.norm_I, one_mul]; exact h _ _ rfl (by simp [norm_smul])
  have ht₃ : ‖t₃‖ ≤ ‖L‖ * ‖u‖ * ‖v‖ :=
    (hs _ _).trans_le (h _ _ (by simp [norm_smul]) (by simp [norm_smul]))
  linarith [norm_sub_le (L u v + t₁ + t₂) t₃, norm_add_le (L u v + t₁) t₂, norm_add_le (L u v) t₁,
    h u v rfl rfl]

/-- Each `sesquiPart` projection depends continuously on the bilinear operator. -/
theorem continuous_sesquiPart (b₁ b₂ : Bool) :
    Continuous (fun L : E →L[ℝ] E' →L[ℝ] F ↦ L.sesquiPart b₁ b₂) :=
  AddMonoidHomClass.continuous_of_bound
    (AddMonoidHom.mk' (fun L : E →L[ℝ] E' →L[ℝ] F ↦ L.sesquiPart b₁ b₂)
      fun L M ↦ sesquiPart_add L M b₁ b₂)
    1 fun L ↦ by simpa using norm_sesquiPart_le L b₁ b₂

end ContinuousLinearMap
