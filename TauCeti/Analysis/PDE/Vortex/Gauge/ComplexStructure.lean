/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.PrincipalPart
public import TauCeti.Analysis.PDE.Vortex.Sobolev.Realization
public import TauCeti.Geometry.Symplectic.AlmostComplex.Lp

/-!
# The gauge-fixed vortex operator is complex linear

In the coordinates of `TauCeti.Vortex.equation`, a variation `y = (y₀, y₁, y₂, y₃)` of a plane
vortex field represents the connection variation `δa = i (y₀ ds + y₁ dt)` and the section variation
`δα = 2 (y₂ + i y₃)`. Both carry natural complex structures: the Hodge star `⋆` on one-forms, which
is multiplication by `i` in the complex coordinate `y₀ + i y₁`, and multiplication by `i` on `δα`.
Together they give the complex structure

`J (y₀, y₁, y₂, y₃) = (-y₁, y₀, -y₃, y₂)`

on variations (`TauCeti.Vortex.variationComplexStructure`). The target of the gauge-fixed operator
`L_x = d₀* ⊕ d₁` (`TauCeti.Vortex.gaugeFixedOperator`) is `ℝ ⊕ ℝ ⊕ ℂ`: the gauge-fixing row, the
curvature row and the complex row `∂bar_a α`. Its complex structure pairs the first two rows,
in the complex coordinate `v₁ + i v₀` (curvature plus `i` times gauge), and multiplies the complex
row by `i`:

`J' (v₀, v₁, v₂, v₃) = (v₁, -v₀, -v₃, v₂)`

(`TauCeti.Vortex.targetComplexStructure`). Both are orthogonal and square to `-1`, so they are
almost complex structures (`TauCeti.Vortex.variationAlmostComplexStructure`,
`TauCeti.Vortex.targetAlmostComplexStructure`).

At every field `x`, with no equation or regularity assumption, the gauge-fixed operator is complex
linear for these structures, `L_x (J y) = J' (L_x y)`
(`TauCeti.Vortex.gaugeFixedOperator_variationComplexStructure`), and so is its formal adjoint,
`L_x* (J' η) = J (L_x* η)` (`TauCeti.Vortex.gaugeFixedAdjoint_targetComplexStructure`). The same
holds for its first-order and zeroth-order parts and for both principal symbols. This is the
complex linearity of the deformation theory of plane vortices behind the complex structure of
the vortex moduli space `Sym^m ℂ`: the complex row of `L_x` is the linearization of the
holomorphicity equation `∂bar_a α = 0`, and the pair of real rows is the linearization of the
(real) moment-map, i.e. curvature, equation and the gauge-fixing equation.

Consequences:

* **The kernel is a complex vector space.** The `C²` square-integrable kernel of `L_x`
  (`TauCeti.Vortex.gaugeFixedKernel`) is preserved by `J`, which restricts to an almost complex
  structure on the kernel (`TauCeti.Vortex.gaugeFixedKernelAlmostComplexStructure`), making it a
  complex vector space by `TauCeti.AlmostComplexStructure.complexModule`. Weak solutions
  of `L_x y = f` are carried to weak solutions of `L_x (J y) = J' f`
  (`TauCeti.Vortex.integral_inner_variationComplexStructure_gaugeFixedAdjoint_eq_integral_inner`).
* **The principal-part map is complex linear.** The section variation of `J y` is
  `δα(J y) = i δα(y)` (`TauCeti.Vortex.sectionValue_variationComplexStructure`), so the principal
  parts of `δα / α` at the zeros of `α` are multiplied by `i`
  (`TauCeti.Vortex.principalPart_variationComplexStructure`,
  `TauCeti.Vortex.principalPartMap_variationComplexStructure`). At a vortex with divisor `D` the
  principal-part map is injective on the kernel of `L_x`, which has real dimension `2 |D|`
  (`TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_mul_card`), so it identifies the kernel with
  the space `ℂ^|D|` of principal parts, the tangent space of the divisor space `Sym^|D| ℂ` at `D`.
  By the above, this identification respects the complex structures.
* **The Sobolev realization is complex linear.** On `H¹(ℂ)⁴`, `J` acts by the same signed
  permutation of coordinates, an almost complex structure
  (`TauCeti.Vortex.sobolevVariationAlmostComplexStructure`), and the
  realization `TauCeti.Vortex.sobolevGaugeFixedOperator a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` intertwines it with
  `J'` (`TauCeti.Vortex.sobolevGaugeFixedOperator_sobolevVariationAlmostComplexStructure`), which
  acts pointwise on `L²(ℂ; ℝ⁴)` as an almost complex structure
  (`TauCeti.Vortex.lpTargetAlmostComplexStructure`), so the realization is a complex-linear map
  (`TauCeti.Vortex.isComplexLinearMap_sobolevGaugeFixedOperator`). Both almost complex structures
  are continuous (`TauCeti.Vortex.continuous_sobolevVariationAlmostComplexStructure`,
  `TauCeti.Vortex.continuous_lpTargetAlmostComplexStructure`). In particular its kernel is
  preserved by `J`
  (`TauCeti.Vortex.sobolevVariationAlmostComplexStructure_mem_ker_sobolevGaugeFixedOperator`), and
  `J` restricts to an almost complex structure on that kernel
  (`TauCeti.Vortex.sobolevGaugeFixedKernelAlmostComplexStructure`).

These are the inputs for orienting the determinant line of the vortex deformation operator by
the complex orientation of its kernel.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace RealInnerProductSpace

/-! ### The complex structures on variations and on the target -/

/-- The complex structure `J (y₀, y₁, y₂, y₃) = (-y₁, y₀, -y₃, y₂)` on variations of plane vortex
fields: the Hodge star on the connection variation `i (y₀ ds + y₁ dt)` and multiplication by `i`
on the section variation `2 (y₂ + i y₃)`. -/
def variationComplexStructure : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) where
  toFun v := !₂[-v 1, v 0, -v 3, v 2]
  invFun v := !₂[v 1, -v 0, v 3, -v 2]
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' t v := by ext i; fin_cases i <;> simp
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp
  norm_map' v := by
    simp only [EuclideanSpace.norm_eq, Fin.sum_univ_four]
    congr 1
    simp
    ring

/-- The complex structure `J' (v₀, v₁, v₂, v₃) = (v₁, -v₀, -v₃, v₂)` on the target `ℝ ⊕ ℝ ⊕ ℂ` of
the gauge-fixed operator: multiplication by `i` in the complex coordinate `v₁ + i v₀` of the
curvature and gauge-fixing rows, and on the complex row `v₂ + i v₃`. -/
def targetComplexStructure : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) where
  toFun v := !₂[v 1, -v 0, -v 3, v 2]
  invFun v := !₂[-v 1, v 0, v 3, -v 2]
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' t v := by ext i; fin_cases i <;> simp
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp
  norm_map' v := by
    simp only [EuclideanSpace.norm_eq, Fin.sum_univ_four]
    congr 1
    simp
    ring

/-- The coordinates of `J v`. -/
theorem variationComplexStructure_apply (v : EuclideanSpace ℝ (Fin 4)) :
    variationComplexStructure v = !₂[-v 1, v 0, -v 3, v 2] :=
  (rfl)

@[simp] theorem variationComplexStructure_apply_zero (v : EuclideanSpace ℝ (Fin 4)) :
    variationComplexStructure v 0 = -v 1 := (rfl)

@[simp] theorem variationComplexStructure_apply_one (v : EuclideanSpace ℝ (Fin 4)) :
    variationComplexStructure v 1 = v 0 := (rfl)

@[simp] theorem variationComplexStructure_apply_two (v : EuclideanSpace ℝ (Fin 4)) :
    variationComplexStructure v 2 = -v 3 := (rfl)

@[simp] theorem variationComplexStructure_apply_three (v : EuclideanSpace ℝ (Fin 4)) :
    variationComplexStructure v 3 = v 2 := (rfl)

/-- The coordinates of `J' v`. -/
theorem targetComplexStructure_apply (v : EuclideanSpace ℝ (Fin 4)) :
    targetComplexStructure v = !₂[v 1, -v 0, -v 3, v 2] :=
  (rfl)

@[simp] theorem targetComplexStructure_apply_zero (v : EuclideanSpace ℝ (Fin 4)) :
    targetComplexStructure v 0 = v 1 := (rfl)

@[simp] theorem targetComplexStructure_apply_one (v : EuclideanSpace ℝ (Fin 4)) :
    targetComplexStructure v 1 = -v 0 := (rfl)

@[simp] theorem targetComplexStructure_apply_two (v : EuclideanSpace ℝ (Fin 4)) :
    targetComplexStructure v 2 = -v 3 := (rfl)

@[simp] theorem targetComplexStructure_apply_three (v : EuclideanSpace ℝ (Fin 4)) :
    targetComplexStructure v 3 = v 2 := (rfl)

/-- `J` as an almost complex structure on `ℝ⁴`, for the `TauCeti.AlmostComplexStructure` API
(for instance the complex vector space structure `TauCeti.AlmostComplexStructure.complexModule`).
-/
def variationAlmostComplexStructure : AlmostComplexStructure (EuclideanSpace ℝ (Fin 4)) where
  toLinearMap := variationComplexStructure.toLinearEquiv.toLinearMap
  square_neg := LinearMap.ext fun v ↦ by ext i; fin_cases i <;> simp

/-- `J'` as an almost complex structure on `ℝ⁴`, for the `TauCeti.AlmostComplexStructure` API
(for instance the complex vector space structure `TauCeti.AlmostComplexStructure.complexModule`).
-/
def targetAlmostComplexStructure : AlmostComplexStructure (EuclideanSpace ℝ (Fin 4)) where
  toLinearMap := targetComplexStructure.toLinearEquiv.toLinearMap
  square_neg := LinearMap.ext fun v ↦ by ext i; fin_cases i <;> simp

/-- The almost complex structure `variationAlmostComplexStructure` acts by `J`. -/
@[simp]
theorem variationAlmostComplexStructure_apply (v : EuclideanSpace ℝ (Fin 4)) :
    variationAlmostComplexStructure v = variationComplexStructure v :=
  (rfl)

/-- The almost complex structure `targetAlmostComplexStructure` acts by `J'`. -/
@[simp]
theorem targetAlmostComplexStructure_apply (v : EuclideanSpace ℝ (Fin 4)) :
    targetAlmostComplexStructure v = targetComplexStructure v :=
  (rfl)

/-- `J` is a complex structure: `J (J v) = -v`. -/
@[simp]
theorem variationComplexStructure_variationComplexStructure (v : EuclideanSpace ℝ (Fin 4)) :
    variationComplexStructure (variationComplexStructure v) = -v :=
  variationAlmostComplexStructure.apply_apply v

/-- `J'` is a complex structure: `J' (J' v) = -v`. -/
@[simp]
theorem targetComplexStructure_targetComplexStructure (v : EuclideanSpace ℝ (Fin 4)) :
    targetComplexStructure (targetComplexStructure v) = -v :=
  targetAlmostComplexStructure.apply_apply v

/-- The inverse of `J` is `-J`. -/
@[simp]
theorem variationComplexStructure_symm_apply (v : EuclideanSpace ℝ (Fin 4)) :
    variationComplexStructure.symm v = -variationComplexStructure v :=
  variationComplexStructure.symm_apply_eq.2 (by simp)

/-- The inverse of `J'` is `-J'`. -/
@[simp]
theorem targetComplexStructure_symm_apply (v : EuclideanSpace ℝ (Fin 4)) :
    targetComplexStructure.symm v = -targetComplexStructure v :=
  targetComplexStructure.symm_apply_eq.2 (by simp)

/-- `J` is skew-adjoint: `⟪J v, w⟫ = -⟪v, J w⟫`. -/
theorem inner_variationComplexStructure_left (v w : EuclideanSpace ℝ (Fin 4)) :
    ⟪variationComplexStructure v, w⟫ = -⟪v, variationComplexStructure w⟫ := by
  simp only [variationComplexStructure_apply, PiLp.inner_apply, Fin.sum_univ_four]
  simp
  ring

/-- `J'` is skew-adjoint: `⟪J' v, w⟫ = -⟪v, J' w⟫`. -/
theorem inner_targetComplexStructure_left (v w : EuclideanSpace ℝ (Fin 4)) :
    ⟪targetComplexStructure v, w⟫ = -⟪v, targetComplexStructure w⟫ := by
  simp only [targetComplexStructure_apply, PiLp.inner_apply, Fin.sum_univ_four]
  simp
  ring

/-- `J v` is orthogonal to `v`, as `J` is skew-adjoint. -/
theorem inner_variationComplexStructure_self (v : EuclideanSpace ℝ (Fin 4)) :
    ⟪v, variationComplexStructure v⟫ = 0 := by
  have h := inner_variationComplexStructure_left v v
  rw [real_inner_comm] at h
  linarith

/-- `J' v` is orthogonal to `v`, as `J'` is skew-adjoint. -/
theorem inner_targetComplexStructure_self (v : EuclideanSpace ℝ (Fin 4)) :
    ⟪v, targetComplexStructure v⟫ = 0 := by
  have h := inner_targetComplexStructure_left v v
  rw [real_inner_comm] at h
  linarith

/-- The pairing `⟪v, J w⟫` is alternating, as `J` is skew-adjoint. -/
theorem isAlt_compl₂_variationComplexStructure :
    ((innerₗ (EuclideanSpace ℝ (Fin 4))).compl₂
      variationComplexStructure.toLinearEquiv.toLinearMap).IsAlt :=
  inner_variationComplexStructure_self

/-- The pairing `⟪v, J' w⟫` is alternating, as `J'` is skew-adjoint. -/
theorem isAlt_compl₂_targetComplexStructure :
    ((innerₗ (EuclideanSpace ℝ (Fin 4))).compl₂
      targetComplexStructure.toLinearEquiv.toLinearMap).IsAlt :=
  inner_targetComplexStructure_self

/-- **`J` multiplies the section variation by `i`**: `δα (J y) = i δα (y)`. -/
@[simp]
theorem sectionValue_variationComplexStructure (y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    sectionValue (fun w ↦ variationComplexStructure (y w)) z = I * sectionValue y z := by
  simp only [sectionValue_apply, variationComplexStructure_apply_two,
    variationComplexStructure_apply_three, ofReal_neg]
  linear_combination (-2 * (y z 3 : ℂ)) * I_sq

/-! ### Complex linearity of the gauge-fixed operator -/

/-- **The first-order part of `L_x` is complex linear.** On the gradients `g` of the coordinates
of a variation, `J` acts by `(g₀, g₁, g₂, g₃) ↦ (-g₁, g₀, -g₃, g₂)`, and the first-order part
intertwines this with `J'`. -/
theorem gaugeFixedFirstOrder_eq_targetComplexStructure (g : Fin 4 → ℂ) :
    gaugeFixedFirstOrder ![-g 1, g 0, -g 3, g 2] =
      targetComplexStructure (gaugeFixedFirstOrder g) := by
  ext i; fin_cases i <;> simp [inner_neg_left] <;> ring

/-- **The zeroth-order part of `L_x` is complex linear**: for every field value `w`,
`Z(w) (J v) = J' (Z(w) v)`. -/
theorem gaugeFixedZerothOrder_variationComplexStructure (w v : EuclideanSpace ℝ (Fin 4)) :
    gaugeFixedZerothOrder w (variationComplexStructure v) =
      targetComplexStructure (gaugeFixedZerothOrder w v) := by
  ext i; fin_cases i <;> simp [gaugeFixedZerothOrderMatrix, Fin.sum_univ_four] <;> ring

/-- **The gauge-fixed vortex operator is complex linear.** At every field `x`,
`L_x (J y) = J' (L_x y)`. No regularity of `x` or `y` and no equation is assumed. -/
theorem gaugeFixedOperator_variationComplexStructure (x y : ℂ → EuclideanSpace ℝ (Fin 4))
    (z : ℂ) :
    gaugeFixedOperator x (fun w ↦ variationComplexStructure (y w)) z =
      targetComplexStructure (gaugeFixedOperator x y z) := by
  ext i; fin_cases i <;> simp [linearizedEquation_apply_zero, linearizedEquation_apply_one,
    linearizedEquation_apply_two] <;> ring

/-- **The formal adjoint of the gauge-fixed vortex operator is complex linear.** At every field
`x`, `L_x* (J' η) = J (L_x* η)`. -/
theorem gaugeFixedAdjoint_targetComplexStructure (x η : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeFixedAdjoint x (fun w ↦ targetComplexStructure (η w)) z =
      variationComplexStructure (gaugeFixedAdjoint x η z) := by
  ext i; fin_cases i <;> simp <;> ring

/-- **The principal symbol of `L_x` is complex linear**: `σ(d) (J v) = J' (σ(d) v)`. -/
theorem gaugeFixedOperatorSymbol_variationComplexStructure (d : ℂ →L[ℝ] ℝ)
    (v : EuclideanSpace ℝ (Fin 4)) :
    gaugeFixedOperatorSymbol d (variationComplexStructure v) =
      targetComplexStructure (gaugeFixedOperatorSymbol d v) := by
  ext i; fin_cases i <;> simp [gaugeFixedOperatorSymbol_def] <;> ring

/-- **The principal symbol of `L_x*` is complex linear**: `σ*(d) (J' v) = J (σ*(d) v)`. -/
theorem gaugeFixedAdjointSymbol_targetComplexStructure (d : ℂ →L[ℝ] ℝ)
    (v : EuclideanSpace ℝ (Fin 4)) :
    gaugeFixedAdjointSymbol d (targetComplexStructure v) =
      variationComplexStructure (gaugeFixedAdjointSymbol d v) := by
  ext i; fin_cases i <;> simp [gaugeFixedAdjointSymbol_def] <;> ring

/-! ### Weak solutions and the kernel -/

/-- Pairing `J u` with `L_x* η` is pairing `u` with `-L_x* (J' η)`, pointwise and hence after
integration. -/
theorem integral_inner_variationComplexStructure_gaugeFixedAdjoint_eq_neg_integral
    (x u η : ℂ → EuclideanSpace ℝ (Fin 4)) :
    ∫ z, ⟪variationComplexStructure (u z), gaugeFixedAdjoint x η z⟫ =
      -∫ z, ⟪u z, gaugeFixedAdjoint x (fun w ↦ targetComplexStructure (η w)) z⟫ := by
  rw [← integral_neg]
  congr 1 with z
  rw [inner_variationComplexStructure_left, gaugeFixedAdjoint_targetComplexStructure]

/-- **`J` carries weak solutions to weak solutions.** If `y` solves `L_x y = f` weakly against
`Cⁿ` compactly supported test fields, then `J y` solves `L_x (J y) = J' f` weakly. -/
theorem integral_inner_variationComplexStructure_gaugeFixedAdjoint_eq_integral_inner
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} {n : WithTop ℕ∞}
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ n η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫)
    (η : ℂ → EuclideanSpace ℝ (Fin 4)) (hη : ContDiff ℝ n η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪variationComplexStructure (y z), gaugeFixedAdjoint x η z⟫ =
      ∫ z, ⟪targetComplexStructure (f z), η z⟫ := by
  have hJη : ContDiff ℝ n fun w ↦ targetComplexStructure (η w) :=
    targetComplexStructure.contDiff.comp hη
  have hJηc : HasCompactSupport fun w ↦ targetComplexStructure (η w) :=
    hηc.comp_left (map_zero _)
  rw [integral_inner_variationComplexStructure_gaugeFixedAdjoint_eq_neg_integral, hweak _ hJη hJηc,
    ← integral_neg]
  congr 1 with z
  rw [inner_targetComplexStructure_left]

/-- **The kernel of `L_x` is preserved by `J`.** -/
theorem variationComplexStructure_comp_mem_gaugeFixedKernel {x y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ gaugeFixedKernel x) :
    (fun w ↦ variationComplexStructure (y w)) ∈ gaugeFixedKernel x := by
  obtain ⟨hy, hy₂, hyk⟩ := mem_gaugeFixedKernel.1 hy
  refine mem_gaugeFixedKernel.2 ⟨variationComplexStructure.contDiff.comp hy,
    variationComplexStructure.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hy₂,
    fun z ↦ ?_⟩
  rw [gaugeFixedOperator_variationComplexStructure, hyk, map_zero]

/-- **The complex structure of the kernel of `L_x`.** The restriction of `J` to the `C²`
square-integrable kernel of the gauge-fixed operator, an almost complex structure; through
`TauCeti.AlmostComplexStructure.complexModule` it makes the kernel a complex vector space. -/
def gaugeFixedKernelAlmostComplexStructure (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    AlmostComplexStructure (gaugeFixedKernel x) where
  toLinearMap := (variationComplexStructure.toLinearEquiv.toLinearMap.compLeft ℂ).restrict
    fun _ ↦ variationComplexStructure_comp_mem_gaugeFixedKernel
  square_neg := LinearMap.ext fun y ↦ Subtype.ext <| funext fun z ↦
    variationComplexStructure_variationComplexStructure ((y : ℂ → EuclideanSpace ℝ (Fin 4)) z)

/-- The complex structure of the kernel acts by `J` pointwise. -/
@[simp]
theorem coe_gaugeFixedKernelAlmostComplexStructure_apply (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (y : gaugeFixedKernel x) (z : ℂ) :
    (gaugeFixedKernelAlmostComplexStructure x y : ℂ → EuclideanSpace ℝ (Fin 4)) z =
      variationComplexStructure ((y : ℂ → EuclideanSpace ℝ (Fin 4)) z) :=
  (rfl)

/-! ### Complex linearity of the principal-part map -/

section PrincipalPart

variable {x y : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- **The principal parts of `J y` are `i` times those of `y`.** If the section variation of `y`
decomposes as `δα = α G + e^ν H` with `G` continuous and `H` entire, then below the zero
multiplicity of `α` the principal-part data of `J y` are `i` times those of `y`, since
`δα (J y) = α (i G) + e^ν (i H)`. -/
theorem principalPart_variationComplexStructure {n : ℂ → ℕ}
    (hα : IsZeroMultiplicity (sectionValue x) n) {ν G H : ℂ → ℂ} (hν : Continuous ν)
    (hG : Continuous G) (hH : Differentiable ℂ H)
    (hy : ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w) {z : ℂ} {j : ℕ}
    (hj : j < n z) :
    principalPart x ν (fun w ↦ variationComplexStructure (y w)) z j =
      I * principalPart x ν y z j :=
  principalPart_eq_mul_of_sectionValue_eq_mul hα hν hG hH hy I
    (sectionValue_variationComplexStructure y) hj

/-- **The principal-part map is complex linear.** On a real vector space `V` of variations whose
section variations decompose as `δα = α G + e^ν H`, the principal-part map sends `J y` to `i`
times the principal parts of `y`, whenever `J y` lies in `V` as well. -/
theorem principalPartMap_variationComplexStructure {D : Multiset ℂ}
    (hα : IsZeroMultiplicity (sectionValue x) fun z ↦ Multiset.count z D) {ν : ℂ → ℂ}
    (hν : Continuous ν) {V : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4))}
    (hV : ∀ y ∈ V, ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w)
    (y : V) (hJy : (fun w ↦ variationComplexStructure ((y : ℂ → EuclideanSpace ℝ (Fin 4)) w)) ∈ V) :
    principalPartMap hα hν hV ⟨_, hJy⟩ = I • principalPartMap hα hν hV y := by
  obtain ⟨G, hG, H, hH, hy⟩ := hV y y.property
  funext i
  simp only [principalPartMap_apply, Pi.smul_apply, smul_eq_mul]
  exact principalPart_variationComplexStructure hα hν hG hH hy i.2.isLt

end PrincipalPart

/-! ### The Sobolev realization -/

section Sobolev

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

/-- The almost complex structure `J` on `H¹(ℂ)⁴`, the domain of `sobolevGaugeFixedOperator`: the
signed permutation `(y₀, y₁, y₂, y₃) ↦ (-y₁, y₀, -y₃, y₂)` of the four coordinates. -/
def sobolevVariationAlmostComplexStructure :
    AlmostComplexStructure (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) where
  toLinearMap := LinearMap.pi (R := ℝ) (φ := fun _ : Fin 4 ↦ W1p (volume : Measure ℂ) ⊤ 2)
    ![-LinearMap.proj 1, LinearMap.proj 0, -LinearMap.proj 3, LinearMap.proj 2]
  square_neg := LinearMap.ext fun y ↦ by funext j; fin_cases j <;> simp

/-- The coordinates of `J y` in `H¹(ℂ)⁴`. -/
theorem sobolevVariationAlmostComplexStructure_apply (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevVariationAlmostComplexStructure y = ![-y 1, y 0, -y 3, y 2] := by
  funext j; fin_cases j <;> rfl

@[simp] theorem sobolevVariationAlmostComplexStructure_apply_zero
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevVariationAlmostComplexStructure y 0 = -y 1 :=
  (rfl)

@[simp] theorem sobolevVariationAlmostComplexStructure_apply_one
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) : sobolevVariationAlmostComplexStructure y 1 = y 0 :=
  (rfl)

@[simp] theorem sobolevVariationAlmostComplexStructure_apply_two
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevVariationAlmostComplexStructure y 2 = -y 3 :=
  (rfl)

@[simp] theorem sobolevVariationAlmostComplexStructure_apply_three
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) : sobolevVariationAlmostComplexStructure y 3 = y 2 :=
  (rfl)

/-- The values of `J y`, for `y ∈ H¹(ℂ)⁴`, are almost everywhere `J` applied to the values of
`y`. -/
theorem values_sobolevVariationAlmostComplexStructure_ae
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    (fun z ↦ (WithLp.toLp 2 fun j ↦ W1p.value (sobolevVariationAlmostComplexStructure y j) z :
      EuclideanSpace ℝ (Fin 4))) =ᵐ[μ⊤]
      fun z ↦ variationComplexStructure (WithLp.toLp 2 fun j ↦ W1p.value (y j) z) := by
  filter_upwards [W1p.value_neg_ae (y 1), W1p.value_neg_ae (y 3)] with z h₁ h₃
  ext j
  fin_cases j <;> simp [h₁, h₃]

/-- The almost complex structure `J` on `H¹(ℂ)⁴` is continuous. -/
theorem continuous_sobolevVariationAlmostComplexStructure :
    Continuous sobolevVariationAlmostComplexStructure := by
  rw [show ⇑sobolevVariationAlmostComplexStructure = fun y ↦ ![-y 1, y 0, -y 3, y 2] from
    funext sobolevVariationAlmostComplexStructure_apply]
  fun_prop

/-- **The Sobolev realization of `L_x` is complex linear.** For every `L∞` coefficient class `a`,
the realization `H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` sends `J y` to `J' (L_a y)`. -/
theorem sobolevGaugeFixedOperator_sobolevVariationAlmostComplexStructure
    (a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevGaugeFixedOperator a (sobolevVariationAlmostComplexStructure y) =
      targetComplexStructure.toContinuousLinearEquiv.toContinuousLinearMap.compLp
        (sobolevGaugeFixedOperator a y) := by
  refine Lp.ext ?_
  have hg (j : Fin 4) : W1p.gradient (-y j) =ᵐ[μ⊤] fun z ↦ -W1p.gradient (y j) z := by
    rw [W1p.gradient_neg]; exact Lp.coeFn_neg _
  filter_upwards [sobolevGaugeFixedOperator_apply_ae a (sobolevVariationAlmostComplexStructure y),
    sobolevGaugeFixedOperator_apply_ae a y,
    ContinuousLinearMap.coeFn_compLp
      targetComplexStructure.toContinuousLinearEquiv.toContinuousLinearMap
      (sobolevGaugeFixedOperator a y),
    hg 1, hg 3, values_sobolevVariationAlmostComplexStructure_ae y] with z hJ h hc hg₁ hg₃ hval
  rw [hJ, hc, h]
  have hgrad : (fun j ↦ W1p.gradient (sobolevVariationAlmostComplexStructure y j) z) =
      ![-W1p.gradient (y 1) z, W1p.gradient (y 0) z, -W1p.gradient (y 3) z,
        W1p.gradient (y 2) z] := by
    funext j; fin_cases j <;> simp [hg₁, hg₃]
  rw [hgrad, hval, gaugeFixedFirstOrder_eq_targetComplexStructure (fun j ↦ W1p.gradient (y j) z),
    gaugeFixedZerothOrder_variationComplexStructure]
  simp

/-- **The kernel of the Sobolev realization is preserved by `J`.** -/
theorem sobolevVariationAlmostComplexStructure_mem_ker_sobolevGaugeFixedOperator
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2}
    (hy : y ∈ (sobolevGaugeFixedOperator a).ker) :
    sobolevVariationAlmostComplexStructure y ∈ (sobolevGaugeFixedOperator a).ker := by
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hy ⊢
  rw [sobolevGaugeFixedOperator_sobolevVariationAlmostComplexStructure, hy]
  exact (targetComplexStructure.toContinuousLinearEquiv.toContinuousLinearMap.compLpₗ (p := 2)
    (μ := μ⊤)).map_zero

/-- **The complex structure of the kernel of the Sobolev realization.** The restriction of `J` to
the kernel of `sobolevGaugeFixedOperator a`, an almost complex structure; through
`TauCeti.AlmostComplexStructure.complexModule` it makes the kernel a complex vector space. -/
def sobolevGaugeFixedKernelAlmostComplexStructure (a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    AlmostComplexStructure (sobolevGaugeFixedOperator a).ker :=
  sobolevVariationAlmostComplexStructure.restrict _ fun _ ↦
    sobolevVariationAlmostComplexStructure_mem_ker_sobolevGaugeFixedOperator

/-- The complex structure of the kernel of the Sobolev realization acts by `J`. This is not a
`simp` lemma: the carrier of the kernel mentions `((⊤ : Opens ℂ) : Set ℂ)`, which `simp` rewrites
to `Set.univ` inside the type, so the left-hand side is not in `simp` normal form. -/
theorem coe_sobolevGaugeFixedKernelAlmostComplexStructure_apply
    (a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) (y : (sobolevGaugeFixedOperator a).ker) :
    (sobolevGaugeFixedKernelAlmostComplexStructure a y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) =
      sobolevVariationAlmostComplexStructure y :=
  AlmostComplexStructure.coe_restrict_apply _ _ _ y

/-- The complex structure `J'` of the target `ℝ ⊕ ℝ ⊕ ℂ` of the gauge-fixed operator, acting
pointwise on `L²(ℂ; ℝ⁴)`, as an almost complex structure: `TauCeti.AlmostComplexStructure.compLp`
for `J'`. -/
def lpTargetAlmostComplexStructure :
    AlmostComplexStructure (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :=
  AlmostComplexStructure.compLp
    targetComplexStructure.toContinuousLinearEquiv.toContinuousLinearMap
    targetAlmostComplexStructure.apply_apply 2 μ⊤

/-- The almost complex structure of `L²(ℂ; ℝ⁴)` is `J'` composed with the classes. This is not a
`simp` lemma: `μ⊤` mentions `((⊤ : Opens ℂ) : Set ℂ)`, which `simp` rewrites to `Set.univ` inside
the type, so the left-hand side is not in `simp` normal form. -/
theorem lpTargetAlmostComplexStructure_apply (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
    lpTargetAlmostComplexStructure g =
      targetComplexStructure.toContinuousLinearEquiv.toContinuousLinearMap.compLp g :=
  AlmostComplexStructure.compLp_apply _ _ _ _ g

/-- The almost complex structure of `L²(ℂ; ℝ⁴)` acts by `J'` pointwise. -/
theorem coeFn_lpTargetAlmostComplexStructure (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
    lpTargetAlmostComplexStructure g =ᵐ[μ⊤] fun z ↦ targetComplexStructure (g z) :=
  AlmostComplexStructure.coeFn_compLp _ _ _ _ g

/-- The almost complex structure `J'` on `L²(ℂ; ℝ⁴)` is continuous. -/
theorem continuous_lpTargetAlmostComplexStructure :
    Continuous lpTargetAlmostComplexStructure :=
  (targetComplexStructure.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2
    μ⊤).continuous.congr fun g ↦ (lpTargetAlmostComplexStructure_apply g).symm

/-- **The Sobolev realization of `L_x` is complex linear**: it intertwines the almost complex
structure `J` of `H¹(ℂ)⁴` with the almost complex structure `J'` of `L²(ℂ; ℝ⁴)`. -/
theorem isComplexLinearMap_sobolevGaugeFixedOperator (a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    IsComplexLinearMap sobolevVariationAlmostComplexStructure lpTargetAlmostComplexStructure
      (sobolevGaugeFixedOperator a : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →ₗ[ℝ] _) :=
  (isComplexLinearMap_iff_apply _ _ _).2 fun y ↦ by
    rw [lpTargetAlmostComplexStructure_apply]
    exact sobolevGaugeFixedOperator_sobolevVariationAlmostComplexStructure a y

end Sobolev

end TauCeti.Vortex
