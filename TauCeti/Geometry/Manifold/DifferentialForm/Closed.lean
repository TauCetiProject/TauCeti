/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
public import TauCeti.Geometry.Manifold.DifferentialForm.Squared

/-!
# Closed smooth differential forms

Closedness is the vanishing of the generic manifold exterior derivative of a smooth form. This
module also characterizes it by vanishing of the exterior derivatives of the chart expressions.
It also restates closedness through the bundled derivative `mextDerivₗ` and shows that
exterior derivatives are closed.
The degree-two specialization in `TwoForm.Closed` supplies a constant-form convenience theorem.
The predicate and its generic API live here so they can be reused at every degree.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

namespace SmoothForm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
variable {form : SmoothForm I M F k}

/-- A smooth form is closed when the generic manifold exterior derivative vanishes. -/
def IsClosed (form : SmoothForm I M F k) : Prop := mextDeriv form.1 = 0

/-- Closedness is exactly the vanishing of the manifold exterior derivative. -/
theorem isClosed_def (form : SmoothForm I M F k) :
    form.IsClosed ↔ mextDeriv form.1 = 0 :=
  Iff.rfl

/-- Closedness is equivalent to vanishing of the exterior derivative of every chart expression
within the model range, at every point of the chart target. -/
theorem isClosed_iff_forall_extDerivWithin_inChartAt_eq_zero [IsManifold I 2 M]
    (form : SmoothForm I M F k) :
    form.IsClosed ↔ ∀ x₀ z, z ∈ (extChartAt I x₀).target →
      extDerivWithin (form.1.inChartAt x₀) (Set.range I) z = 0 := by
  have hform : IsSmoothForm I 1 form.1 := form.isSmoothForm.of_le (by norm_num)
  constructor
  · intro h x₀ z hz
    rw [isClosed_def] at h
    rw [← hform.inChartAt_mextDeriv_eq x₀ hz, h, RoughForm.inChartAt_zero]
    simp
  · intro h
    rw [isClosed_def]
    funext x
    rw [mextDeriv_def]
    exact h x (extChartAt I x x) (mem_extChartAt_target x)

/-- Closedness can equivalently be checked pointwise on the exterior derivative. -/
theorem isClosed_iff_forall_mextDeriv_apply_eq_zero (form : SmoothForm I M F k) :
    form.IsClosed ↔ ∀ x, mextDeriv form.1 x = 0 := by
  rw [isClosed_def, funext_iff]
  simp only [Pi.zero_apply]

/-- Closedness is the vanishing of the bundled exterior derivative. -/
theorem isClosed_iff_mextDerivₗ_eq_zero [IsManifold I 2 M] (form : SmoothForm I M F k) :
    form.IsClosed ↔ mextDerivₗ I k form = 0 := by
  rw [isClosed_def, ← mextDerivₗ_apply I k form, ZeroMemClass.coe_eq_zero]

/-- The exterior derivative of a smooth form is closed. -/
theorem isClosed_mextDerivₗ [IsManifold I 2 M] (form : SmoothForm I M F k) :
    (mextDerivₗ I k form).IsClosed := by
  rw [isClosed_def, mextDerivₗ_apply, SmoothForm.mextDeriv_mextDeriv]

/-- The zero smooth form is closed. -/
theorem isClosed_zero : (0 : SmoothForm I M F k).IsClosed := by
  rw [isClosed_def]
  exact mextDeriv_zero

/-- The sum of two closed smooth forms is closed. -/
theorem IsClosed.add {form' : SmoothForm I M F k} (h : form.IsClosed)
    (h' : form'.IsClosed) : (form + form').IsClosed := by
  rw [isClosed_def, SmoothForm.add_toRoughForm]
  have hform : IsSmoothForm I ∞ form.1 := form.isSmoothForm
  have hform' : IsSmoothForm I ∞ form'.1 := form'.isSmoothForm
  funext x
  rw [mextDeriv_add
    ((hform.contDiffWithinAt_inChartAt_self x).differentiableWithinAt (by simp))
    ((hform'.contDiffWithinAt_inChartAt_self x).differentiableWithinAt (by simp)), h, h']
  simp

/-- A scalar multiple of a closed smooth form is closed, for any scalars acting continuously on
the coefficients and commuting with the real action (for instance `ℝ`, or `ℂ` on complex-valued
forms). -/
theorem IsClosed.smul {S : Type*} [Monoid S] [DistribMulAction S F] [ContinuousConstSMul S F]
    [SMulCommClass ℝ S F] (c : S) (h : form.IsClosed) : (c • form).IsClosed := by
  rw [isClosed_def, SmoothForm.smul_toRoughForm, RoughForm.smul_eq_mapCoeff,
    mextDeriv_mapCoeff _ (form.isSmoothForm.of_le (by simp)), h, RoughForm.mapCoeff_zero]

/-- The negative of a closed smooth form is closed. -/
theorem IsClosed.neg (h : form.IsClosed) : (-form).IsClosed := by
  rw [isClosed_def, SmoothForm.neg_toRoughForm]
  rw [mextDeriv_neg, h, neg_zero]

/-- The difference of two closed smooth forms is closed. -/
theorem IsClosed.sub {form' : SmoothForm I M F k} (h : form.IsClosed)
    (h' : form'.IsClosed) : (form - form').IsClosed := by
  rw [sub_eq_add_neg]
  exact SmoothForm.IsClosed.add (form := form) h
    (SmoothForm.IsClosed.neg (form := form') h')

/-- Constant forms on a model space are closed. -/
theorem isClosed_const {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    (A : V [⋀^Fin k]→L[ℝ] F) :
    (SmoothForm.const A : SmoothForm (modelWithCornersSelf ℝ V) V F k).IsClosed := by
  rw [isClosed_def]
  have hconst : (fun y : V => A.compContinuousLinearMap
      (NormedSpace.fromTangentSpace y).toContinuousLinearMap) = fun _ => A := by
    funext y
    ext v
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    simp [NormedSpace.fromTangentSpace, tangentSpaceCastModel]
    congr 1
  rw [SmoothForm.const_toRoughForm]
  rw [hconst]
  exact mextDeriv_const A

end SmoothForm

end TauCeti

end
