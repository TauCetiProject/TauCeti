/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.PrincipalPart
public import TauCeti.Analysis.PDE.Vortex.SobolevRealization

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

(`TauCeti.Vortex.targetComplexStructure`). Both are orthogonal and square to `-1`.

At every field `x`, with no equation or regularity assumption, the gauge-fixed operator is complex
linear for these structures, `L_x (J y) = J' (L_x y)`
(`TauCeti.Vortex.gaugeFixedOperator_variationComplexStructure`), and so is its formal adjoint,
`L_x* (J' η) = J (L_x* η)` (`TauCeti.Vortex.gaugeFixedAdjoint_targetComplexStructure`). The same
holds for its first-order and zeroth-order parts and for both principal symbols. This is the
complex linearity of the deformation theory of plane vortices behind the complex structure of
the vortex moduli space `Sym^m ℂ`: the complex row of `L_x` is the linearization of the
holomorphicity equation `∂bar_a α = 0`, and the pair of real rows is the linearization of the
complex moment-map and gauge-fixing equations.

Consequences:

* **The kernel is a complex vector space.** The `C²` square-integrable kernel of `L_x`
  (`TauCeti.Vortex.gaugeFixedKernel`) is preserved by `J`, which restricts to an endomorphism of
  the kernel squaring to `-1` (`TauCeti.Vortex.gaugeFixedKernelComplexStructure`). Weak solutions
  of `L_x y = f` are carried to weak solutions of `L_x (J y) = J' f`
  (`TauCeti.Vortex.integral_inner_variationComplexStructure_gaugeFixedAdjoint_eq`).
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
  permutation of coordinates (`TauCeti.Vortex.sobolevVariationComplexStructure`), and the
  realization `TauCeti.Vortex.sobolevGaugeFixedOperator a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` intertwines it with
  `J'` (`TauCeti.Vortex.sobolevGaugeFixedOperator_sobolevVariationComplexStructure`). In
  particular its kernel is preserved by `J`
  (`TauCeti.Vortex.sobolevVariationComplexStructure_mem_ker_sobolevGaugeFixedOperator`).

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

/-- `J` is a complex structure: `J (J v) = -v`. -/
@[simp]
theorem variationComplexStructure_variationComplexStructure (v : EuclideanSpace ℝ (Fin 4)) :
    variationComplexStructure (variationComplexStructure v) = -v := by
  ext i; fin_cases i <;> simp

/-- `J'` is a complex structure: `J' (J' v) = -v`. -/
@[simp]
theorem targetComplexStructure_targetComplexStructure (v : EuclideanSpace ℝ (Fin 4)) :
    targetComplexStructure (targetComplexStructure v) = -v := by
  ext i; fin_cases i <;> simp

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
theorem gaugeFixedFirstOrder_complexStructure (g : Fin 4 → ℂ) :
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
theorem integral_inner_variationComplexStructure_gaugeFixedAdjoint
    (x u η : ℂ → EuclideanSpace ℝ (Fin 4)) :
    ∫ z, ⟪variationComplexStructure (u z), gaugeFixedAdjoint x η z⟫ =
      -∫ z, ⟪u z, gaugeFixedAdjoint x (fun w ↦ targetComplexStructure (η w)) z⟫ := by
  rw [← integral_neg]
  congr 1 with z
  rw [inner_variationComplexStructure_left, gaugeFixedAdjoint_targetComplexStructure]

/-- **`J` carries weak solutions to weak solutions.** If `y` solves `L_x y = f` weakly against
`Cⁿ` compactly supported test fields, then `J y` solves `L_x (J y) = J' f` weakly. -/
theorem integral_inner_variationComplexStructure_gaugeFixedAdjoint_eq
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
  rw [integral_inner_variationComplexStructure_gaugeFixedAdjoint, hweak _ hJη hJηc,
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
square-integrable kernel of the gauge-fixed operator. It squares to `-1`
(`gaugeFixedKernelComplexStructure_apply_apply`), so it makes the kernel a complex vector space. -/
def gaugeFixedKernelComplexStructure (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Module.End ℝ (gaugeFixedKernel x) :=
  (variationComplexStructure.toLinearEquiv.toLinearMap.compLeft ℂ).restrict
    fun _ ↦ variationComplexStructure_comp_mem_gaugeFixedKernel

/-- The complex structure of the kernel acts by `J` pointwise. -/
@[simp]
theorem coe_gaugeFixedKernelComplexStructure_apply (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (y : gaugeFixedKernel x) (z : ℂ) :
    (gaugeFixedKernelComplexStructure x y : ℂ → EuclideanSpace ℝ (Fin 4)) z =
      variationComplexStructure ((y : ℂ → EuclideanSpace ℝ (Fin 4)) z) :=
  (rfl)

/-- The complex structure of the kernel squares to `-1`. -/
@[simp]
theorem gaugeFixedKernelComplexStructure_apply_apply (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (y : gaugeFixedKernel x) :
    gaugeFixedKernelComplexStructure x (gaugeFixedKernelComplexStructure x y) = -y := by
  ext z : 2
  simp only [coe_gaugeFixedKernelComplexStructure_apply,
    variationComplexStructure_variationComplexStructure, Submodule.coe_neg, Pi.neg_apply]

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
      I * principalPart x ν y z j := by
  rw [principalPart_eq_iteratedDeriv hα hν (G := fun w ↦ I * G w) (H := fun w ↦ I * H w)
      (continuous_const.mul hG) ((differentiable_const _).mul hH)
      (fun w ↦ by rw [sectionValue_variationComplexStructure, hy w]; ring) hj,
    principalPart_eq_iteratedDeriv hα hν hG hH hy hj, iteratedDeriv_const_mul_field]

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
  obtain ⟨G, hG, H, hH, hy⟩ := hV y y.2
  funext i
  simp only [principalPartMap_apply, Pi.smul_apply, smul_eq_mul]
  exact principalPart_variationComplexStructure hα hν hG hH hy i.2.2

end PrincipalPart

/-! ### The Sobolev realization -/

section Sobolev

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

/-- The complex structure `J` on `H¹(ℂ)⁴`, the domain of `sobolevGaugeFixedOperator`: the signed
permutation `(y₀, y₁, y₂, y₃) ↦ (-y₁, y₀, -y₃, y₂)` of the four coordinates. -/
def sobolevVariationComplexStructure :
    (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :=
  ContinuousLinearMap.pi ![-ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 0,
    -ContinuousLinearMap.proj 3, ContinuousLinearMap.proj 2]

/-- The coordinates of `J y` in `H¹(ℂ)⁴`. -/
theorem sobolevVariationComplexStructure_apply (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevVariationComplexStructure y = ![-y 1, y 0, -y 3, y 2] := by
  funext j; fin_cases j <;> rfl

@[simp] theorem sobolevVariationComplexStructure_apply_zero
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) : sobolevVariationComplexStructure y 0 = -y 1 :=
  (rfl)

@[simp] theorem sobolevVariationComplexStructure_apply_one
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) : sobolevVariationComplexStructure y 1 = y 0 :=
  (rfl)

@[simp] theorem sobolevVariationComplexStructure_apply_two
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) : sobolevVariationComplexStructure y 2 = -y 3 :=
  (rfl)

@[simp] theorem sobolevVariationComplexStructure_apply_three
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) : sobolevVariationComplexStructure y 3 = y 2 :=
  (rfl)

/-- `J` is a complex structure on `H¹(ℂ)⁴`: `J (J y) = -y`. -/
@[simp]
theorem sobolevVariationComplexStructure_sobolevVariationComplexStructure
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevVariationComplexStructure (sobolevVariationComplexStructure y) = -y := by
  funext j; fin_cases j <;> simp

/-- **The Sobolev realization of `L_x` is complex linear.** For every `L∞` coefficient class `a`,
the realization `H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` sends `J y` to `J' (L_a y)`. -/
theorem sobolevGaugeFixedOperator_sobolevVariationComplexStructure
    (a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevGaugeFixedOperator a (sobolevVariationComplexStructure y) =
      targetComplexStructure.toContinuousLinearEquiv.toContinuousLinearMap.compLp
        (sobolevGaugeFixedOperator a y) := by
  refine Lp.ext ?_
  have hg (j : Fin 4) : W1p.gradient (-y j) =ᵐ[μ⊤] fun z ↦ -W1p.gradient (y j) z := by
    rw [← W1p.gradientL_apply, map_neg, W1p.gradientL_apply]
    exact Lp.coeFn_neg _
  have hv (j : Fin 4) : W1p.value (-y j) =ᵐ[μ⊤] fun z ↦ -W1p.value (y j) z := by
    rw [← W1p.valueL_apply, map_neg, W1p.valueL_apply]
    exact Lp.coeFn_neg _
  filter_upwards [sobolevGaugeFixedOperator_apply_ae a (sobolevVariationComplexStructure y),
    sobolevGaugeFixedOperator_apply_ae a y,
    ContinuousLinearMap.coeFn_compLp
      targetComplexStructure.toContinuousLinearEquiv.toContinuousLinearMap
      (sobolevGaugeFixedOperator a y),
    hg 1, hg 3, hv 1, hv 3] with z hJ h hc hg₁ hg₃ hv₁ hv₃
  rw [hJ, hc, h]
  have hgrad : (fun j ↦ W1p.gradient (sobolevVariationComplexStructure y j) z) =
      ![-W1p.gradient (y 1) z, W1p.gradient (y 0) z, -W1p.gradient (y 3) z,
        W1p.gradient (y 2) z] := by
    funext j; fin_cases j <;> simp [hg₁, hg₃]
  have hval : (WithLp.toLp 2 fun j ↦ W1p.value (sobolevVariationComplexStructure y j) z :
      EuclideanSpace ℝ (Fin 4)) =
      variationComplexStructure (WithLp.toLp 2 fun j ↦ W1p.value (y j) z) := by
    ext j; fin_cases j <;> simp [hv₁, hv₃]
  rw [hgrad, hval, gaugeFixedFirstOrder_complexStructure (fun j ↦ W1p.gradient (y j) z),
    gaugeFixedZerothOrder_variationComplexStructure]
  simp

/-- **The kernel of the Sobolev realization is preserved by `J`.** -/
theorem sobolevVariationComplexStructure_mem_ker_sobolevGaugeFixedOperator
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2}
    (hy : y ∈ (sobolevGaugeFixedOperator a).ker) :
    sobolevVariationComplexStructure y ∈ (sobolevGaugeFixedOperator a).ker := by
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hy ⊢
  rw [sobolevGaugeFixedOperator_sobolevVariationComplexStructure, hy]
  exact (targetComplexStructure.toContinuousLinearEquiv.toContinuousLinearMap.compLpₗ (p := 2)
    (μ := μ⊤)).map_zero

end Sobolev

end TauCeti.Vortex
