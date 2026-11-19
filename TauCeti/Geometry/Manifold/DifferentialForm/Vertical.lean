/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Families of forms as vertical forms on a product

A family `σ : N → RoughForm I M F k` of differential forms on a manifold `M`, indexed by the
points of a manifold `N`, is recorded by a single form on `N × M` which does not see the tangent
directions of `N`: the **vertical form** `TauCeti.verticalForm J σ`, whose value at `(p, y)` is
`σ p y` precomposed with the projection `T_p N × T_y M → T_y M`. Its slice along the inclusion
`ι_p : y ↦ (p, y)` is the member `σ p` of the family (`TauCeti.mpullback_prodMk_verticalForm`).
This is how a family of forms, such as a family of primitives of the slices of a form on `N × M`,
becomes a form on `N × M` to which the calculus of forms on manifolds applies.

Coordinate expressions on `N × M` are read in product charts. The inverse of the extended chart of
`N × M` at `a` differentiates componentwise
(`TauCeti.mfderivWithin_extChartAt_prod_symm_apply`). Consequently the coordinate expression of a
vertical form is that of the family member read in the chart of `M`, precomposed with the second
projection (`TauCeti.verticalForm_inChartAt`), and the coordinate expression of a slice of a form
`φ` on `N × M` is that of `φ` precomposed with the inclusion of the second factor
(`TauCeti.inChartAt_mpullback_prodMk`).

## Main definitions

* `TauCeti.verticalForm`: the form on `N × M` of a family of forms on `M` indexed by `N`.

## Main results

* `TauCeti.mpullback_prodMk_verticalForm`: the slices of a vertical form are the members of the
  family.
* `TauCeti.verticalForm_inChartAt`: the coordinate expression of a vertical form in a product
  chart.
* `TauCeti.inChartAt_mpullback_prodMk`: the coordinate expression of a slice of a form on `N × M`
  in terms of that of the form in a product chart.
* `TauCeti.IsSmoothForm.contDiffOn_inChartAt_mpullback_prodMk`: the coordinate expressions of the
  slices of a smooth form on `N × M` are jointly smooth in the point of `N` and the coordinate.
-/

public section

noncomputable section

open Set
open scoped Manifold

namespace TauCeti

variable {E H M EN HN N F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The **vertical form** of a family `σ` of forms on `M` indexed by `N`: the form on `N × M`
whose value at `(p, y)` is `σ p y` applied to the `T_y M`-components of tangent vectors, so that
it vanishes as soon as one argument is tangent to `N`. Its slices `ι_p^* (verticalForm J σ)` are the
forms `σ p` (`TauCeti.mpullback_prodMk_verticalForm`). -/
def verticalForm (J : ModelWithCorners ℝ EN HN) (σ : N → RoughForm I M F k) :
    RoughForm (J.prod I) (N × M) F k :=
  fun z ↦ (σ z.1 z.2).compContinuousLinearMap (ContinuousLinearMap.snd ℝ EN E)

/-- The vertical form evaluates the family member on the `T M`-components of tangent vectors. -/
@[simp]
theorem verticalForm_apply (σ : N → RoughForm I M F k) (z : N × M)
    (v : Fin k → TangentSpace (J.prod I) z) :
    verticalForm J σ z v = σ z.1 z.2 fun i ↦ (v i).2 :=
  (rfl)

/-- Multiplying every member of a family by a function on `M` multiplies its vertical form by that
function of the second coordinate. -/
theorem verticalForm_smul (f : M → ℝ) (σ : N → RoughForm I M F k) :
    verticalForm J (fun p y ↦ f y • σ p y) = fun z ↦ f z.2 • verticalForm J σ z :=
  (rfl)

/-- The slice of a vertical form along the inclusion `y ↦ (p, y)` is the member `σ p` of the
family. -/
@[simp]
theorem mpullback_prodMk_verticalForm (σ : N → RoughForm I M F k) (p : N) :
    mpullback I (J.prod I) (Prod.mk p) (verticalForm J σ) = σ p := by
  ext y v
  have h : mfderiv I (J.prod I) (Prod.mk p) y =
      ContinuousLinearMap.inr ℝ (TangentSpace J p) (TangentSpace I y) := mfderiv_prod_right
  simp only [mpullback_apply, verticalForm_apply, h]
  -- The second component of `inr ℝ _ _ v` is `v`.
  rfl

/-- **The inverse of a product chart differentiates componentwise.** At a point `x` of the target
of the extended chart of `N × M` at `a`, the derivative of its inverse, within the model range,
applies the derivatives of the inverses of the charts of the factors to the components of a
vector. -/
theorem mfderivWithin_extChartAt_prod_symm_apply [IsManifold I 1 M] [IsManifold J 1 N]
    {a : N × M} {x : EN × E} (hx : x ∈ (extChartAt (J.prod I) a).target) (u : EN × E) :
    mfderivWithin 𝓘(ℝ, EN × E) (J.prod I) (extChartAt (J.prod I) a).symm (range (J.prod I)) x u =
      (mfderivWithin 𝓘(ℝ, EN) J (extChartAt J a.1).symm (range J) x.1 u.1,
        mfderivWithin 𝓘(ℝ, E) I (extChartAt I a.2).symm (range I) x.2 u.2) := by
  obtain ⟨z, hz, rfl⟩ : ∃ z ∈ (extChartAt (J.prod I) a).source, extChartAt (J.prod I) a z = x :=
    ⟨_, (extChartAt (J.prod I) a).map_target hx, (extChartAt (J.prod I) a).right_inv hx⟩
  have hz' : z ∈ (chartAt (ModelProd HN H) a).source := by
    rwa [← extChartAt_source (I := J.prod I)]
  have hz₁ : z.1 ∈ (chartAt HN a.1).source ∧ z.2 ∈ (chartAt H a.2).source := by
    simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, mem_prod] using hz'
  rw [← TangentBundle.symmL_trivializationAt hz', extChartAt_prod_apply,
    ← TangentBundle.symmL_trivializationAt hz₁.1, ← TangentBundle.symmL_trivializationAt hz₁.2]
  exact (Manifold.tangentSpaceProdEquiv_apply (I := J) (J := I) z _).symm.trans
    (Manifold.tangentSpaceProdEquiv_symmL_trivializationAt hz' u)

/-- **Coordinates of a vertical form.** In the product chart at `a`, the coordinate expression of
the vertical form of a family `σ` at `x` is the coordinate expression of `σ p`, for the point `p`
of `N` with coordinate `x.1`, in the chart of `M` at `a.2` at `x.2`, precomposed with the second
projection. -/
theorem verticalForm_inChartAt [IsManifold I 1 M] [IsManifold J 1 N]
    (σ : N → RoughForm I M F k) (a : N × M) {x : EN × E}
    (hx : x ∈ (extChartAt (J.prod I) a).target) :
    (verticalForm J σ).inChartAt a x =
      ((σ ((extChartAt J a.1).symm x.1)).inChartAt a.2 x.2).compContinuousLinearMap
        (ContinuousLinearMap.snd ℝ EN E) := by
  ext v
  simp only [RoughForm.inChartAt_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    mfderivWithin_extChartAt_prod_symm_apply hx]
  -- Both sides evaluate `σ` at the components of `(extChartAt (J.prod I) a).symm x`.
  rfl

/-- **Coordinates of a slice.** In the chart of `M` at `a.2`, the coordinate expression of the
slice `ι_p^* φ` of a form `φ` on `N × M`, for `p` in the chart of `N` at `a.1`, is the coordinate
expression of `φ` in the product chart at `a`, at the coordinates of `p`, precomposed with the
inclusion of the second factor. -/
theorem inChartAt_mpullback_prodMk [IsManifold I 1 M] [IsManifold J 1 N]
    (φ : RoughForm (J.prod I) (N × M) F k) (a : N × M) {p : N}
    (hp : p ∈ (extChartAt J a.1).source) {w : E} (hw : w ∈ (extChartAt I a.2).target) :
    (mpullback I (J.prod I) (Prod.mk p) φ).inChartAt a.2 w =
      (φ.inChartAt a (extChartAt J a.1 p, w)).compContinuousLinearMap
        (ContinuousLinearMap.inr ℝ EN E) := by
  have hx : (extChartAt J a.1 p, w) ∈ (extChartAt (J.prod I) a).target := by
    rw [extChartAt_prod, PartialEquiv.prod_target]
    exact ⟨(extChartAt J a.1).map_source hp, hw⟩
  have hsymm : (extChartAt (J.prod I) a).symm (extChartAt J a.1 p, w) =
      (p, (extChartAt I a.2).symm w) := by
    rw [extChartAt_prod_symm_apply, (extChartAt J a.1).left_inv hp]
  have h : mfderiv I (J.prod I) (Prod.mk p) ((extChartAt I a.2).symm w) =
      ContinuousLinearMap.inr ℝ (TangentSpace J p) (TangentSpace I _) := mfderiv_prod_right
  -- `φ` takes the same value at equal points on vectors with equal components.
  have hφ {z₁ z₂ : N × M} (hz : z₁ = z₂) {v₁ : Fin k → TangentSpace (J.prod I) z₁}
      {v₂ : Fin k → TangentSpace (J.prod I) z₂} (hv : ∀ i, (v₁ i : EN × E) = v₂ i) :
      φ z₁ v₁ = φ z₂ v₂ := by
    subst hz
    exact congrArg (φ z₁) (funext hv)
  ext v
  rw [RoughForm.inChartAt_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    RoughForm.inChartAt_apply, mpullback_apply]
  refine hφ hsymm.symm fun i ↦ ?_
  rw [mfderivWithin_extChartAt_prod_symm_apply hx, h]
  -- The first component of `inr ℝ _ _ u` is `0`, and the second is `u`.
  exact Prod.ext (map_zero _).symm rfl

/-- **The slices of a smooth form are jointly smooth in coordinates.** For a `C^n` form `φ` on
`N × M`, the coordinate expression in the chart of `M` at `a.2` of the slice `ι_p^* φ`, at the
point of `N` with coordinate `X.1` in the chart at `a.1` and at the coordinate `X.2`, is jointly
`C^n` in `X` on the target of the product chart at `a`. -/
theorem IsSmoothForm.contDiffOn_inChartAt_mpullback_prodMk {n : WithTop ℕ∞}
    [IsManifold I 1 M] [IsManifold J 1 N] [IsManifold I (n + 1) M] [IsManifold J (n + 1) N]
    {φ : RoughForm (J.prod I) (N × M) F k}
    (hφ : IsSmoothForm (J.prod I) n φ) (a : N × M) :
    ContDiffOn ℝ n
      (fun X : EN × E ↦
        (mpullback I (J.prod I) (Prod.mk ((extChartAt J a.1).symm X.1)) φ).inChartAt a.2 X.2)
      (extChartAt (J.prod I) a).target := by
  -- Precomposition with the inclusion of the second factor, a continuous linear map.
  let L : (EN × E) [⋀^Fin k]→L[ℝ] F →L[ℝ] E [⋀^Fin k]→L[ℝ] F :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM (ContinuousLinearMap.inr ℝ EN E)
  have hφa : ContDiffOn ℝ n (L ∘ φ.inChartAt a) (extChartAt (J.prod I) a).target := fun X hX ↦
    (L.contDiff.comp_contDiffWithinAt
      (φ.contDiffWithinAt_inChartAt_of_contDiffWithinAt_inChartAt hX
        (mem_extChartAt_source _) (hφ.contDiffWithinAt_inChartAt_self _))).mono
      (extChartAt_target_subset_range a)
  refine hφa.congr fun X hX ↦ ?_
  have hX' : X.1 ∈ (extChartAt J a.1).target ∧ X.2 ∈ (extChartAt I a.2).target := by
    simpa only [extChartAt_prod, PartialEquiv.prod_target, mem_prod] using hX
  rw [inChartAt_mpullback_prodMk φ a ((extChartAt J a.1).map_target hX'.1) hX'.2,
    (extChartAt J a.1).right_inv hX'.1]
  exact ContinuousAlternatingMap.compContinuousLinearMapCLM_apply _ _

end TauCeti
