/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Icc

/-!
# Coordinates and derivatives of a rectangle with corners

A rectangle uses the actual product of the two closed-interval manifolds. Its preferred charts
are products of the interval charts; their inverse inclusion derivatives retain the signs of
both interval factors.
-/

public section

noncomputable section

open Set Fact.Manifold
open scoped Manifold

namespace TauCeti

variable {a b c d : ℝ} [Fact (a < b)] [Fact (c < d)]

/-- Every intrinsic interior point of the rectangle lies in the bottom-left preferred chart. -/
theorem interior_rectangle_subset_extChartAt_bot_source :
    ((𝓡∂ 1).prod (𝓡∂ 1)).interior (Icc a b × Icc c d) ⊆
      (extChartAt ((𝓡∂ 1).prod (𝓡∂ 1)) (⊥ : Icc a b × Icc c d)).source := by
  rw [ModelWithCorners.interior_prod, extChartAt_prod, PartialEquiv.prod_source]
  exact prod_mono interior_Icc_subset_extChartAt_bot_source
    interior_Icc_subset_extChartAt_bot_source

/-- On its actual target, the inverse rectangle chart is the coordinatewise affine inverse
of the two preferred interval charts. -/
theorem subtypeVal_extChartAt_rectangle_symm
    (α : Icc a b × Icc c d) {z : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)}
    (hz : z ∈ (extChartAt ((𝓡∂ 1).prod (𝓡∂ 1)) α).target) :
    (((extChartAt ((𝓡∂ 1).prod (𝓡∂ 1)) α).symm z).1.val,
        ((extChartAt ((𝓡∂ 1).prod (𝓡∂ 1)) α).symm z).2.val) =
      (if (α.1 : ℝ) < b then z.1 0 + a else b - z.1 0,
        if (α.2 : ℝ) < d then z.2 0 + c else d - z.2 0) := by
  rw [extChartAt_prod, PartialEquiv.prod_target] at hz
  rw [extChartAt_prod, PartialEquiv.prod_coe_symm]
  exact Prod.ext (subtypeVal_extChartAt_Icc_symm α.1 hz.1)
    (subtypeVal_extChartAt_Icc_symm α.2 hz.2)

/-- The inverse rectangle chart followed by the actual coordinate inclusion has the product
of the two signed interval derivatives. -/
theorem hasFDerivWithinAt_subtypeVal_extChartAt_rectangle_symm
    (α : Icc a b × Icc c d) {z : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)}
    (hz : z ∈ (extChartAt ((𝓡∂ 1).prod (𝓡∂ 1)) α).target) :
    HasFDerivWithinAt
      (fun w ↦ (((extChartAt ((𝓡∂ 1).prod (𝓡∂ 1)) α).symm w).1.val,
        ((extChartAt ((𝓡∂ 1).prod (𝓡∂ 1)) α).symm w).2.val))
      (((if (α.1 : ℝ) < b then (1 : ℝ) else -1) •
          EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).prodMap
        ((if (α.2 : ℝ) < d then (1 : ℝ) else -1) • EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0))
      (range ((𝓡∂ 1).prod (𝓡∂ 1))) z := by
  rw [extChartAt_prod, PartialEquiv.prod_target] at hz
  have h₁ := hasFDerivWithinAt_subtypeVal_extChartAt_Icc_symm α.1 hz.1
  have h₂ := hasFDerivWithinAt_subtypeVal_extChartAt_Icc_symm α.2 hz.2
  have hfst : Prod.fst '' (range (𝓡∂ 1) ×ˢ range (𝓡∂ 1)) ⊆ range (𝓡∂ 1) := by
    rintro _ ⟨w, hw, rfl⟩
    exact hw.1
  have hsnd : Prod.snd '' (range (𝓡∂ 1) ×ˢ range (𝓡∂ 1)) ⊆ range (𝓡∂ 1) := by
    rintro _ ⟨w, hw, rfl⟩
    exact hw.2
  have h := HasFDerivWithinAt.prodMap z (s := range (𝓡∂ 1) ×ˢ range (𝓡∂ 1))
    (h₁.mono hfst) (h₂.mono hsnd)
  simpa only [ModelWithCorners.range_prod, extChartAt_prod, PartialEquiv.prod_coe_symm,
    Prod.map_def] using h

/-- The actual derivative of rectangle inclusion is the product of the two signed coordinate
projections, including at edges and corners. -/
theorem mfderiv_subtypeVal_rectangle (x : Icc a b × Icc c d) :
    mfderiv ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ × ℝ)
        (fun y : Icc a b × Icc c d ↦ (y.1.val, y.2.val)) x =
      (((if (x.1 : ℝ) < b then (1 : ℝ) else -1) •
          EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).prodMap
        ((if (x.2 : ℝ) < d then (1 : ℝ) else -1) •
          EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0)) := by
  have hmap : (fun y : Icc a b × Icc c d ↦ (y.1.val, y.2.val)) =
      Prod.map (Subtype.val : Icc a b → ℝ) (Subtype.val : Icc c d → ℝ) := Prod.map_def.symm
  rw [hmap]
  have h := mfderiv_prodMap
    ((contMDiff_subtypeVal_Icc (x := a) (y := b) (n := 1)).mdifferentiable one_ne_zero x.1)
    ((contMDiff_subtypeVal_Icc (x := c) (y := d) (n := 1)).mdifferentiable one_ne_zero x.2)
  -- Normalize the product target model and its self-chart instance to the product normed space.
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  rw [mfderiv_subtypeVal_Icc, mfderiv_subtypeVal_Icc] at h
  exact h

/-- The actual rectangle inclusion derivative as an invertible map of tangent spaces to the
coordinate plane. Both interval endpoint signs are retained. -/
def subtypeValRectangleTangentEquiv (x : Icc a b × Icc c d) :
    TangentSpace ((𝓡∂ 1).prod (𝓡∂ 1)) x ≃L[ℝ] ℝ × ℝ :=
  (subtypeValIccTangentEquiv x.1).prodCongr (subtypeValIccTangentEquiv x.2)

/-- Rectangle tangent coordinates are the two signed interval projections. -/
@[simp]
theorem subtypeValRectangleTangentEquiv_apply (x : Icc a b × Icc c d)
    (v : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) :
    subtypeValRectangleTangentEquiv x v =
      ((if (x.1 : ℝ) < b then (1 : ℝ) else -1) * v.1 0,
        (if (x.2 : ℝ) < d then (1 : ℝ) else -1) * v.2 0) := by
  -- Evaluate prodCongr as a pair before applying the two interval evaluation lemmas.
  change (subtypeValIccTangentEquiv x.1 v.1, subtypeValIccTangentEquiv x.2 v.2) = _
  simp only [subtypeValIccTangentEquiv_apply, PiLp.proj_apply]

/-- The inverse rectangle tangent map multiplies each coordinate by its chart sign. -/
@[simp]
theorem subtypeValRectangleTangentEquiv_symm_apply (x : Icc a b × Icc c d) (v : ℝ × ℝ) :
    (subtypeValRectangleTangentEquiv x).symm v =
      (WithLp.toLp 2 (fun _ : Fin 1 ↦ (if (x.1 : ℝ) < b then (1 : ℝ) else -1) * v.1),
        WithLp.toLp 2 (fun _ : Fin 1 ↦ (if (x.2 : ℝ) < d then (1 : ℝ) else -1) * v.2)) := by
  -- The inverse of prodCongr acts independently on the two tangent model fibers.
  change ((subtypeValIccTangentEquiv x.1).symm v.1,
    (subtypeValIccTangentEquiv x.2).symm v.2) = _
  ext <;> simp only [subtypeValIccTangentEquiv_symm_apply]

/-- The product tangent equivalence is the actual rectangle inclusion derivative. -/
theorem subtypeValRectangleTangentEquiv_toContinuousLinearMap (x : Icc a b × Icc c d) :
    (subtypeValRectangleTangentEquiv x).toContinuousLinearMap =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (x.1.val, x.2.val)).toContinuousLinearMap.comp
        (mfderiv ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ × ℝ)
          (fun y : Icc a b × Icc c d ↦ (y.1.val, y.2.val)) x) := by
  -- Expose prodCongr as the product of its two underlying continuous linear maps.
  change ((subtypeValIccTangentEquiv x.1).toContinuousLinearMap.prodMap
    (subtypeValIccTangentEquiv x.2).toContinuousLinearMap) = _
  rw [subtypeValIccTangentEquiv_toContinuousLinearMap,
    subtypeValIccTangentEquiv_toContinuousLinearMap, mfderiv_subtypeVal_Icc,
    mfderiv_subtypeVal_Icc, mfderiv_subtypeVal_rectangle]
  rfl

end TauCeti
