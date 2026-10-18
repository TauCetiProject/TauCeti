/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.IsManifold.Basic
public import TauCeti.LinearAlgebra.Orientation.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# Orientability of product manifolds

The preferred transition derivative of a product is block diagonal. Products of source signs
therefore give an orientation lift of the product, including manifolds with boundary and corners.
-/

public section

noncomputable section

open Set
open scoped Manifold

variable {E H M E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' 1 M']

namespace TauCeti.Manifold.OrientationLift

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  {m n : ℕ}

/-- Product lifts use the product model orientation and the product of the source signs. -/
def prod (o : OrientationLift I M (Fin m)) (o' : OrientationLift I' M' (Fin n)) :
    OrientationLift (I.prod I') (M × M') (Fin (m + n)) := by
  let source (α : M × M') (x : (chartAt (ModelProd H H') α).source) :
      x.val ∈ (chartAt H α.1).source ×ˢ (chartAt H' α.2).source := by
    simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source] using x.property
  let left (α : M × M') (x : (chartAt (ModelProd H H') α).source) :
      (chartAt H α.1).source := ⟨x.val.1, (source α x).1⟩
  let right (α : M × M') (x : (chartAt (ModelProd H H') α).source) :
      (chartAt H' α.2).source := ⟨x.val.2, (source α x).2⟩
  refine {
    modelOrientation := _root_.Orientation.prod o.modelOrientation o'.modelOrientation
      (by simpa using o.card_eq.symm) (by simpa using o'.card_eq.symm)
    card_eq := by simpa [Module.finrank_prod] using congrArg₂ (· + ·) o.card_eq o'.card_eq
    sign := fun α x ↦ o.sign α.1 (left α x) * o'.sign α.2 (right α x)
    locallyConstant_sign := ?_
    compatible := ?_ }
  · intro α
    exact ((o.locallyConstant_sign α.1).comp_continuous
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _)).mul
        ((o'.locallyConstant_sign α.2).comp_continuous
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
  · intro α β x hα hβ
    have h₁ := o.compatible α.1 β.1 x.1 (left α ⟨x, hα⟩).property
      (left β ⟨x, hβ⟩).property
    have h₂ := o'.compatible α.2 β.2 x.2 (right α ⟨x, hα⟩).property
      (right β ⟨x, hβ⟩).property
    rw [← tangentCoordChange_def, TauCeti.Manifold.tangentCoordChange_prod
      ⟨by simpa only [extChartAt_source] using hα,
        by simpa only [extChartAt_source] using hβ⟩, ContinuousLinearMap.det,
      ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap]
    rw [← tangentCoordChange_def] at h₁ h₂
    simp only [Units.val_mul, Int.cast_mul]
    convert mul_pos h₁ h₂ using 1
    ring

/-- The product lift carries the product linear orientation of its two models. -/
@[simp]
theorem prod_modelOrientation (o : OrientationLift I M (Fin m))
    (o' : OrientationLift I' M' (Fin n)) :
    (o.prod o').modelOrientation = _root_.Orientation.prod o.modelOrientation o'.modelOrientation
      (by simpa using o.card_eq.symm) (by simpa using o'.card_eq.symm) := (rfl)

/-- The source sign of a product chart is the product of the signs in its factor charts. -/
@[simp]
theorem prod_sign (o : OrientationLift I M (Fin m)) (o' : OrientationLift I' M' (Fin n))
    (α : M × M') (x : (chartAt H α.1).source) (x' : (chartAt H' α.2).source) :
    (o.prod o').sign α ⟨(x.val, x'.val), by
      simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, mem_prod] using
        And.intro x.property x'.property⟩ = o.sign α.1 x * o'.sign α.2 x' := (rfl)

/-- Replacing the first factor lift by its diagonal flip flips the product lift. -/
@[simp]
theorem flip_prod (o : OrientationLift I M (Fin m))
    (o' : OrientationLift I' M' (Fin n)) : o.flip.prod o' = (o.prod o').flip := by
  ext α x
  · simp only [prod_modelOrientation, flip_modelOrientation, _root_.Orientation.prod_neg_left]
  · simp only [prod, flip_sign, neg_mul]

/-- Replacing the second factor lift by its diagonal flip flips the product lift. -/
@[simp]
theorem prod_flip (o : OrientationLift I M (Fin m))
    (o' : OrientationLift I' M' (Fin n)) : o.prod o'.flip = (o.prod o').flip := by
  ext α x
  · simp only [prod_modelOrientation, flip_modelOrientation, _root_.Orientation.prod_neg_right]
  · simp only [prod, flip_sign, mul_neg]

end TauCeti.Manifold.OrientationLift

namespace TauCeti.Manifold.Orientation

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] {m n : ℕ}

/-- The product orientation, with the first factor's tangent directions before the second's. -/
def prod (o : Orientation I M (Fin m)) (o' : Orientation I' M' (Fin n)) :
    Orientation (I.prod I') (M × M') (Fin (m + n)) :=
  mk ((Classical.choose o.exists_lift).prod (Classical.choose o'.exists_lift))

/-- The product does not depend on the lifts used to represent its factors. -/
@[simp]
theorem prod_mk (l : OrientationLift I M (Fin m))
    (l' : OrientationLift I' M' (Fin n)) :
    (mk l).prod (mk l') = mk (l.prod l') := by
  have h := (mk_eq_mk_iff _ _).mp (Classical.choose_spec (mk l).exists_lift)
  have h' := (mk_eq_mk_iff _ _).mp (Classical.choose_spec (mk l').exists_lift)
  unfold prod
  rcases h with h | h <;> rcases h' with h' | h' <;> rw [h, h']
  all_goals simp only [OrientationLift.flip_prod, OrientationLift.prod_flip,
    OrientationLift.flip_flip]
  all_goals exact (mk_eq_mk_iff _ _).mpr (.inr rfl)

/-- The product manifold orientation induces the ordered product of its tangent orientations. -/
@[simp]
theorem orientationAt_prod (o : Orientation I M (Fin m))
    (o' : Orientation I' M' (Fin n)) (x : M × M') :
    (o.prod o').orientationAt x =
      _root_.Orientation.prod (o.orientationAt x.1) (o'.orientationAt x.2)
        (by simpa using o.finrank_tangentSpace_eq x.1)
        (by simpa using o'.finrank_tangentSpace_eq x.2) := by
  induction o using Orientation.inductionOn with | h l =>
    induction o' using Orientation.inductionOn with | h l' =>
      rw [prod_mk, orientationAt_mk, OrientationLift.orientationAt_eq,
        OrientationLift.chartOrientation_eq_ite, orientationAt_mk, OrientationLift.orientationAt_eq,
        OrientationLift.chartOrientation_eq_ite, orientationAt_mk, OrientationLift.orientationAt_eq,
        OrientationLift.chartOrientation_eq_ite]
      -- Expand only the product lift fields; the chart-orientation equations above
      -- already identify each tangent orientation with its signed model orientation.
      change (if l.sign x.1 ⟨x.1, mem_chart_source H x.1⟩ *
          l'.sign x.2 ⟨x.2, mem_chart_source H' x.2⟩ = 1 then
          _root_.Orientation.prod l.modelOrientation l'.modelOrientation _ _ else
          -_root_.Orientation.prod l.modelOrientation l'.modelOrientation _ _) =
        _root_.Orientation.prod
          (if l.sign x.1 ⟨x.1, mem_chart_source H x.1⟩ = 1 then l.modelOrientation
            else -l.modelOrientation)
          (if l'.sign x.2 ⟨x.2, mem_chart_source H' x.2⟩ = 1 then l'.modelOrientation
            else -l'.modelOrientation) _ _
      have hneg : (-1 : ℤˣ) ≠ 1 := by decide
      rcases Int.units_eq_one_or (l.sign x.1 ⟨x.1, mem_chart_source H x.1⟩) with h | h <;>
        rcases Int.units_eq_one_or (l'.sign x.2 ⟨x.2, mem_chart_source H' x.2⟩) with h' | h' <;>
        simp only [h, h', one_mul, mul_one, neg_mul_neg, ite_true,
          hneg, ite_false]
      · exact (_root_.Orientation.prod_neg_right l.modelOrientation l'.modelOrientation _ _).symm
      · exact (_root_.Orientation.prod_neg_left l.modelOrientation l'.modelOrientation _ _).symm
      · exact (_root_.Orientation.prod_neg_neg l.modelOrientation l'.modelOrientation _ _).symm

/-- Reversing the first factor reverses the product manifold orientation. -/
@[simp]
theorem prod_neg_left (o : Orientation I M (Fin m)) (o' : Orientation I' M' (Fin n)) :
    (-o).prod o' = -(o.prod o') := by
  apply ext
  intro x
  simp only [orientationAt_prod, orientationAt_neg, _root_.Orientation.prod_neg_left]
  -- Tangent-space and model-space scalar structures coincide; rank proofs are proof-irrelevant.
  rfl

/-- Reversing the second factor reverses the product manifold orientation. -/
@[simp]
theorem prod_neg_right (o : Orientation I M (Fin m)) (o' : Orientation I' M' (Fin n)) :
    o.prod (-o') = -(o.prod o') := by
  apply ext
  intro x
  simp only [orientationAt_prod, orientationAt_neg, _root_.Orientation.prod_neg_right]
  -- Tangent-space and model-space scalar structures coincide; rank proofs are proof-irrelevant.
  rfl

/-- Reversing both factors preserves the product manifold orientation. -/
theorem prod_neg_neg (o : Orientation I M (Fin m)) (o' : Orientation I' M' (Fin n)) :
    (-o).prod (-o') = o.prod o' := by
  rw [prod_neg_left, prod_neg_right, neg_neg]

end TauCeti.Manifold.Orientation

namespace TauCeti

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

/-- Products of orientable manifolds with corners are orientable. -/
instance [Orientable I M] [Orientable I' M'] : Orientable (I.prod I') (M × M') := by
  obtain ⟨o⟩ := Orientable.nonempty_orientation (I := I) (M := M)
  obtain ⟨o'⟩ := Orientable.nonempty_orientation (I := I') (M := M')
  constructor
  rw [Module.finrank_prod]
  exact ⟨o.prod o'⟩

end TauCeti
