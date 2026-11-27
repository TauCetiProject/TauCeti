/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Algebra
public import TauCeti.MeasureTheory.Measure.Count.Topology
import TauCeti.MeasureTheory.Group.ModularCharacter
import TauCeti.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Point masses in the convolution algebra of a discrete group

Let `G` be a discrete group with counting measure and `α` an action of `G` on a C⋆-algebra `A`.
Every finitely supported function `G → A` is continuous with compact support, so the twisted
convolution algebra contains the point masses `δ_g ⊗ a`, `ConvolutionAlgebra.single g a`, and
every element is a finite sum of them. Convolution against counting measure is a sum, so point
masses multiply by `(δ_g ⊗ a) ⋆ (δ_h ⊗ b) = δ_{gh} ⊗ a α_g(b)` and, since a discrete group is
unimodular, `(δ_g ⊗ a)⋆ = δ_{g⁻¹} ⊗ α_{g⁻¹}(a⋆)`. For unital `A`, `δ_1 ⊗ 1` is a unit. These
formulas describe the full and reduced crossed products by discrete groups on their dense
subalgebras.

## Main definitions

* `TauCeti.CStarAction.ConvolutionAlgebra.single`: the point mass `δ_g ⊗ a`.

## Main statements

* `TauCeti.CStarAction.ConvolutionAlgebra.sum_single`: every element is a finite sum of point
  masses.
* `TauCeti.CStarAction.ConvolutionAlgebra.ofConv_single_mul_apply` and
  `TauCeti.CStarAction.ConvolutionAlgebra.ofConv_mul_single_apply`: convolution with a point mass
  is a twisted translation.
* `TauCeti.CStarAction.ConvolutionAlgebra.single_mul_single` and
  `TauCeti.CStarAction.ConvolutionAlgebra.star_single`: the product and involution of point
  masses.
* `TauCeti.CStarAction.ConvolutionAlgebra.single_one_one_mul` and
  `TauCeti.CStarAction.ConvolutionAlgebra.mul_single_one_one`: `δ_1 ⊗ 1` is a unit.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported

namespace TauCeti.CStarAction

variable {G A : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] [MeasurableSpace G]

namespace ConvolutionAlgebra

section Single

variable [NonUnitalCStarAlgebra A] {α : CStarAction G A}

open scoped Classical in
/-- The point mass `δ_g ⊗ a` in the convolution algebra of a discrete group with counting
measure: the function with value `a` at `g` and `0` elsewhere. -/
def single (g : G) (a : A) : ConvolutionAlgebra α Measure.count :=
  toConv
    { toFun := fun s => if s = g then a else 0
      continuous_toFun := continuous_of_discreteTopology
      hasCompactSupport' := HasCompactSupport.intro isCompact_singleton fun _ hs =>
        ite_eq_right_iff.2 fun h => absurd h hs }

/-- A point mass takes its value at its base point. -/
@[simp]
theorem ofConv_single_same (g : G) (a : A) :
    (single g a : ConvolutionAlgebra α Measure.count).ofConv g = a := by
  simp [single]

/-- A point mass vanishes off its base point. -/
theorem ofConv_single_of_ne {g s : G} (h : s ≠ g) (a : A) :
    (single g a : ConvolutionAlgebra α Measure.count).ofConv s = 0 := by
  simp [single, h]

/-- The values of a point mass, for any decidability instance. -/
theorem ofConv_single_apply (g : G) (a : A) (s : G) [Decidable (s = g)] :
    (single g a : ConvolutionAlgebra α Measure.count).ofConv s = if s = g then a else 0 := by
  by_cases h : s = g <;> simp [single, h]

@[simp]
theorem single_zero (g : G) : (single g 0 : ConvolutionAlgebra α Measure.count) = 0 := by
  ext1
  ext s
  classical
  simp [ofConv_single_apply]

theorem single_add (g : G) (a b : A) :
    (single g (a + b) : ConvolutionAlgebra α Measure.count) = single g a + single g b := by
  ext1
  ext s
  classical
  simp only [ofConv_single_apply, ofConv_add, CompactlySupportedContinuousMap.coe_add,
    Pi.add_apply]
  split_ifs <;> simp

theorem single_smul (g : G) (c : ℂ) (a : A) :
    (single g (c • a) : ConvolutionAlgebra α Measure.count) = c • single g a := by
  ext1
  ext s
  classical
  simp only [ofConv_single_apply, ofConv_smul, CompactlySupportedContinuousMap.coe_smul,
    Pi.smul_apply]
  split_ifs <;> simp

/-- An element of the convolution algebra of a discrete group has finite support. -/
theorem finite_support_ofConv (f : ConvolutionAlgebra α Measure.count) :
    (Function.support f.ofConv).Finite :=
  f.ofConv.hasCompactSupport.isCompact.finite_of_discrete.subset (subset_tsupport _)

/-- **Every element is a finite sum of point masses**: `f = ∑ g ∈ s, δ_g ⊗ f(g)` for every finite
set `s` containing the support of `f`. -/
theorem sum_single (f : ConvolutionAlgebra α Measure.count) {s : Finset G}
    (hs : Function.support f.ofConv ⊆ s) : ∑ g ∈ s, single g (f.ofConv g) = f := by
  classical
  ext1
  ext r
  rw [← addEquiv_apply, map_sum]
  simp only [addEquiv_apply, CompactlySupportedContinuousMap.coe_sum, Finset.sum_apply,
    ofConv_single_apply, Finset.sum_ite_eq]
  split_ifs with hr
  · rfl
  · exact (Function.notMem_support.1 fun h => hr (hs h)).symm

variable [OpensMeasurableSpace G]

/-- Left multiplication by a point mass translates and twists:
`((δ_g ⊗ a) ⋆ f)(s) = a α_g(f(g⁻¹ s))`. -/
theorem ofConv_single_mul_apply (g : G) (a : A) (f : ConvolutionAlgebra α Measure.count)
    (s : G) : (single g a * f).ofConv s = a * α g (f.ofConv (g⁻¹ * s)) := by
  rw [ofConv_mul, convolution_apply,
    integral_count_eq_single g fun r hr => by rw [ofConv_single_of_ne hr, zero_mul],
    ofConv_single_same]

/-- Right multiplication by a point mass translates and twists:
`(f ⋆ (δ_g ⊗ a))(s) = f(s g⁻¹) α_{s g⁻¹}(a)`. -/
theorem ofConv_mul_single_apply (f : ConvolutionAlgebra α Measure.count) (g : G) (a : A)
    (s : G) : (f * single g a).ofConv s = f.ofConv (s * g⁻¹) * α (s * g⁻¹) a := by
  rw [ofConv_mul, convolution_apply, integral_count_eq_single (s * g⁻¹) fun r hr => ?_]
  · simp
  · rw [ofConv_single_of_ne, map_zero, mul_zero]
    rintro h
    exact hr (by rw [← h]; group)

/-- **The product of point masses**: `(δ_g ⊗ a) ⋆ (δ_h ⊗ b) = δ_{gh} ⊗ a α_g(b)`. -/
@[simp]
theorem single_mul_single (g h : G) (a b : A) :
    (single g a * single h b : ConvolutionAlgebra α Measure.count) =
      single (g * h) (a * α g b) := by
  classical
  ext1
  ext s
  rw [ofConv_single_mul_apply, ofConv_single_apply, ofConv_single_apply]
  simp only [inv_mul_eq_iff_eq_mul]
  split_ifs <;> simp

omit [OpensMeasurableSpace G] in
/-- **The adjoint of a point mass**: `(δ_g ⊗ a)⋆ = δ_{g⁻¹} ⊗ α_{g⁻¹}(a⋆)`; a discrete group is
unimodular. -/
@[simp]
theorem star_single (g : G) (a : A) :
    star (single g a : ConvolutionAlgebra α Measure.count) = single g⁻¹ (α g⁻¹ (star a)) := by
  classical
  ext1
  ext s
  rw [ofConv_star, twistedInvolution_apply, modularCharacter_eq_one_of_discreteTopology,
    ofConv_single_apply, ofConv_single_apply]
  simp only [inv_eq_iff_eq_inv]
  split_ifs with h
  · simp [h]
  · simp

end Single

section Unital

variable [CStarAlgebra A] {α : CStarAction G A} [OpensMeasurableSpace G]

/-- The point mass `δ_1 ⊗ 1` is a left unit of the convolution algebra. -/
@[simp]
theorem single_one_one_mul (f : ConvolutionAlgebra α Measure.count) : single 1 1 * f = f := by
  ext1
  ext s
  rw [ofConv_single_mul_apply]
  simp

/-- The point mass `δ_1 ⊗ 1` is a right unit of the convolution algebra. -/
@[simp]
theorem mul_single_one_one (f : ConvolutionAlgebra α Measure.count) : f * single 1 1 = f := by
  ext1
  ext s
  rw [ofConv_mul_single_apply]
  simp

end Unital

end ConvolutionAlgebra

end TauCeti.CStarAction
