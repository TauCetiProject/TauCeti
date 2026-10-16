/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Manifold.Orientation.Interval
public import TauCeti.Geometry.Manifold.Orientation.Prod

/-!
# Coordinates and orientation of a rectangle with corners

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
  have h := (h₁.comp z hasFDerivWithinAt_fst
    (show MapsTo Prod.fst (range (𝓡∂ 1) ×ˢ range (𝓡∂ 1)) (range (𝓡∂ 1))
      from fun _ h ↦ h.1)).prodMk
    (h₂.comp z hasFDerivWithinAt_snd
      (show MapsTo Prod.snd (range (𝓡∂ 1) ×ˢ range (𝓡∂ 1)) (range (𝓡∂ 1))
      from fun _ h ↦ h.2))
  simp only [ModelWithCorners.range_prod, extChartAt_prod, PartialEquiv.prod_coe_symm]
  convert h using 1
  · rfl
  · ext v <;> rfl

/-- The actual derivative of rectangle inclusion is the product of the two signed coordinate
projections, including at edges and corners. -/
theorem mfderiv_subtypeVal_rectangle (x : Icc a b × Icc c d) :
    mfderiv ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ × ℝ)
        (fun y : Icc a b × Icc c d ↦ (y.1.val, y.2.val)) x =
      (((if (x.1 : ℝ) < b then (1 : ℝ) else -1) •
          EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).prodMap
        ((if (x.2 : ℝ) < d then (1 : ℝ) else -1) •
          EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0)) := by
  apply HasMFDerivAt.mfderiv
  refine ⟨(continuous_subtype_val.comp continuous_fst).continuousAt.prodMk
    (continuous_subtype_val.comp continuous_snd).continuousAt, ?_⟩
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp]
  convert! hasFDerivWithinAt_subtypeVal_extChartAt_rectangle_symm x
    (mem_extChartAt_target x) using 1

/-- The actual rectangle inclusion derivative as an invertible map of tangent spaces to the
coordinate plane. Both interval endpoint signs are retained. -/
def subtypeValRectangleTangentEquiv (x : Icc a b × Icc c d) :
    TangentSpace ((𝓡∂ 1).prod (𝓡∂ 1)) x ≃L[ℝ] ℝ × ℝ :=
  (subtypeValIccTangentEquiv x.1).prodCongr (subtypeValIccTangentEquiv x.2)

/-- The product tangent equivalence is the actual rectangle inclusion derivative. -/
theorem subtypeValRectangleTangentEquiv_toContinuousLinearMap (x : Icc a b × Icc c d) :
    (subtypeValRectangleTangentEquiv x).toContinuousLinearMap =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (x.1.val, x.2.val)).toContinuousLinearMap.comp
        (mfderiv ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ × ℝ)
          (fun y : Icc a b × Icc c d ↦ (y.1.val, y.2.val)) x) := by
  change ((subtypeValIccTangentEquiv x.1).toContinuousLinearMap.prodMap
    (subtypeValIccTangentEquiv x.2).toContinuousLinearMap) = _
  rw [subtypeValIccTangentEquiv_toContinuousLinearMap,
    subtypeValIccTangentEquiv_toContinuousLinearMap, mfderiv_subtypeVal_Icc,
    mfderiv_subtypeVal_Icc, mfderiv_subtypeVal_rectangle]
  rfl

/-- Inclusion carries the canonical rectangle orientation to the standard coordinate-plane
orientation at every point, including all four corners. -/
theorem Manifold.Orientation.map_orientationAt_interval_prod (x : Icc a b × Icc c d) :
    _root_.Orientation.map (Fin 2) (subtypeValRectangleTangentEquiv x).toLinearEquiv
      (((interval a b).prod (interval c d)).orientationAt x) =
        (((Module.Basis.singleton (Fin 1) ℝ).prod
          (Module.Basis.singleton (Fin 1) ℝ)).reindex finSumFinEquiv).orientation := by
  have hx := map_orientationAt_interval x.1
  have hy := map_orientationAt_interval x.2
  rw [orientationAt_interval] at hx hy
  rw [orientationAt_prod, orientationAt_interval, orientationAt_interval]
  -- State product transport on the fixed models with their model finrank proofs;
  -- the tangent-space finrank proofs otherwise retain the dependent base points.
  change _root_.Orientation.map (Fin (1 + 1))
    ((subtypeValIccTangentEquiv x.1).toLinearEquiv.prodCongr
      (subtypeValIccTangentEquiv x.2).toLinearEquiv)
    (_root_.Orientation.prod
      (if (x.1 : ℝ) < b then (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation
        else -(EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation)
      (if (x.2 : ℝ) < d then (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation
        else -(EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation) (by simp) (by simp)) = _
  rw [_root_.Orientation.map_prod, hx, hy, _root_.Orientation.prod_basis_orientation]

/-- Wherever both preferred charts are increasing, the actual tangent orientation of the
rectangle is the ordered standard coordinate orientation. -/
theorem orientationAt_interval_prod_of_lt (x : Icc a b × Icc c d)
    (hx : (x.1 : ℝ) < b) (hy : (x.2 : ℝ) < d) :
    Manifold.Orientation.orientationAt
        ((Manifold.Orientation.interval a b).prod (Manifold.Orientation.interval c d)) x =
      (((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.prod
        (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis).reindex finSumFinEquiv).orientation := by
  rw [Manifold.Orientation.orientationAt_prod,
    Manifold.Orientation.orientationAt_interval, Manifold.Orientation.orientationAt_interval]
  simp only [hx, hy, ↓reduceIte]
  exact _root_.Orientation.prod_basis_orientation _ _ _ _

end TauCeti
