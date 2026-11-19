/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
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

Coordinate expressions on `N × M` are read in product charts. The coordinate expression of a
vertical form is that of the family member read in the chart of `M`, precomposed with the second
projection (`TauCeti.inChartAt_verticalForm`). So a vertical form is `C^n` as soon as these
coordinate expressions are jointly `C^n` in the chart coordinates of the parameter and the point
(`TauCeti.contMDiffAt_verticalForm`, `TauCeti.isSmoothForm_verticalForm`). In particular a family
of flat forms pulled back along a chart and cut off by a function supported in the chart domain is
`C^n` as soon as the flat family is jointly `C^n`
(`TauCeti.isSmoothForm_verticalForm_smul_mpullback_extChartAt`), the family version of
`TauCeti.isSmoothForm_smul_mpullback_extChartAt`.

## Main definitions

* `TauCeti.verticalForm`: the form on `N × M` of a family of forms on `M` indexed by `N`.

## Main results

* `TauCeti.mpullback_prodMk_verticalForm`: the slices of a vertical form are the members of the
  family.
* `TauCeti.inChartAt_verticalForm`: the coordinate expression of a vertical form in a product
  chart.
* `TauCeti.contMDiffAt_verticalForm` and `TauCeti.isSmoothForm_verticalForm`: a vertical form is
  `C^n` where the coordinate expressions of the family are jointly `C^n`.
* `TauCeti.contMDiffAt_verticalForm_mpullback_extChartAt` and
  `TauCeti.isSmoothForm_verticalForm_smul_mpullback_extChartAt`: the vertical form of a family of
  flat forms pulled back along a chart, and cut off by a function supported in the chart domain, is
  `C^n` where the flat family is jointly `C^n`.
-/

public section

noncomputable section

open Bundle Set
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
theorem verticalForm_fun_smul (f : M → ℝ) (σ : N → RoughForm I M F k) :
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

/-- **Coordinates of a vertical form.** In the product chart at `a`, the coordinate expression of
the vertical form of a family `σ` at `x` is the coordinate expression of `σ p`, for the point `p`
of `N` with coordinate `x.1`, in the chart of `M` at `a.2` at `x.2`, precomposed with the second
projection. -/
theorem inChartAt_verticalForm [IsManifold I 1 M] [IsManifold J 1 N]
    (σ : N → RoughForm I M F k) (a : N × M) {x : EN × E}
    (hx : x ∈ (extChartAt (J.prod I) a).target) :
    (verticalForm J σ).inChartAt a x =
      ((σ ((extChartAt J a.1).symm x.1)).inChartAt a.2 x.2).compContinuousLinearMap
        (ContinuousLinearMap.snd ℝ EN E) := by
  ext v
  rw [RoughForm.inChartAt_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    RoughForm.inChartAt_apply]
  exact (verticalForm J σ).apply_congr (extChartAt_prod_symm_apply a x)
    fun i ↦ Manifold.mfderivWithin_extChartAt_prod_symm_apply hx (v i)

/-- **A vertical form is smooth where its family is smooth in coordinates.** The vertical form of
a family `σ` is `C^n` at a point `z` in the domain of the product chart at `a` if the coordinate
expression of `σ p` in the chart of `M` at `a.2`, for the point `p` of `N` with coordinate `X.1` in
the chart at `a.1`, is jointly `C^n` in the coordinates `X` at the chart image of `z`. -/
theorem contMDiffAt_verticalForm {n : WithTop ℕ∞} [IsManifold I 1 M] [IsManifold J 1 N]
    [IsManifold I (n + 1) M] [IsManifold J (n + 1) N] {σ : N → RoughForm I M F k} {a z : N × M}
    (hz : z ∈ (extChartAt (J.prod I) a).source)
    (hσ : ContDiffWithinAt ℝ n
      (fun X : EN × E ↦ (σ ((extChartAt J a.1).symm X.1)).inChartAt a.2 X.2)
      (range J ×ˢ range I) (extChartAt J a.1 z.1, extChartAt I a.2 z.2)) :
    ContMDiffAt (J.prod I) ((J.prod I).prod 𝓘(ℝ, (EN × E) [⋀^Fin k]→L[ℝ] F)) n
      (fun z ↦ TotalSpace.mk' ((EN × E) [⋀^Fin k]→L[ℝ] F) z (verticalForm J σ z)) z := by
  rw [← extChartAt_prod_apply, ← ModelWithCorners.range_prod] at hσ
  refine contMDiffAt_form_of_contDiffWithinAt_inChartAt hz
    (((ContinuousAlternatingMap.compContinuousLinearMapCLM
      (ContinuousLinearMap.snd ℝ EN E)).contDiff.comp_contDiffWithinAt
        hσ).congr_of_eventuallyEq_of_mem ?_
      (extChartAt_target_subset_range _ ((extChartAt (J.prod I) a).map_source hz)))
  filter_upwards [extChartAt_target_mem_nhdsWithin' hz] with X hX
  rw [inChartAt_verticalForm σ a hX]
  exact (ContinuousAlternatingMap.compContinuousLinearMapCLM_apply _ _).symm

/-- **A vertical form is smooth if its family is smooth in coordinates.** The vertical form of a
family `σ` is `C^n` if, at every point `z` of `N × M`, the coordinate expression of `σ p` in the
chart of `M` at `z.2`, for the point `p` of `N` with coordinate `X.1` in the chart at `z.1`, is
jointly `C^n` in the coordinates `X` at the chart image of `z`. -/
theorem isSmoothForm_verticalForm {n : WithTop ℕ∞} [IsManifold I 1 M] [IsManifold J 1 N]
    [IsManifold I (n + 1) M] [IsManifold J (n + 1) N] {σ : N → RoughForm I M F k}
    (hσ : ∀ z : N × M, ContDiffWithinAt ℝ n
      (fun X : EN × E ↦ (σ ((extChartAt J z.1).symm X.1)).inChartAt z.2 X.2)
      (range J ×ˢ range I) (extChartAt J z.1 z.1, extChartAt I z.2 z.2)) :
    IsSmoothForm (J.prod I) n (verticalForm J σ) :=
  (isSmoothForm_def _ _).mpr fun z ↦ contMDiffAt_verticalForm (mem_extChartAt_source z) (hσ z)

/-- The vertical form of a family `K p` of flat forms pulled back along the chart at `x` is `C^n` at
a point `z` over the chart domain if `K p`, for the point `p` of `N` with coordinate `X.1` in the
chart at `z.1`, is jointly `C^n` in `X` at the coordinates of `z`. -/
theorem contMDiffAt_verticalForm_mpullback_extChartAt {n : WithTop ℕ∞} [IsManifold I 1 M]
    [IsManifold J 1 N] [IsManifold I (n + 1) M] [IsManifold J (n + 1) N] {x : M}
    {K : N → E → E [⋀^Fin k]→L[ℝ] F} {z : N × M} (hz : z.2 ∈ (extChartAt I x).source)
    (hK : ContDiffWithinAt ℝ n (fun X : EN × E ↦ K ((extChartAt J z.1).symm X.1) X.2)
      (range J ×ˢ range I) (extChartAt J z.1 z.1, extChartAt I x z.2)) :
    ContMDiffAt (J.prod I) ((J.prod I).prod 𝓘(ℝ, (EN × E) [⋀^Fin k]→L[ℝ] F)) n
      (fun z ↦ TotalSpace.mk' ((EN × E) [⋀^Fin k]→L[ℝ] F) z (verticalForm J (fun p ↦
        mpullback I 𝓘(ℝ, E) (extChartAt I x) (K p : RoughForm 𝓘(ℝ, E) E F k)) z)) z := by
  have hz' : z ∈ (extChartAt (J.prod I) (z.1, x)).source := by
    rw [extChartAt_prod, PartialEquiv.prod_source]
    exact ⟨mem_extChartAt_source _, hz⟩
  -- In the chart at `x` the coordinate expression of the pullback of `K p` is `K p`.
  refine contMDiffAt_verticalForm hz' (hK.congr_of_eventuallyEq_of_mem ?_
    ⟨extChartAt_target_subset_range _ (mem_extChartAt_target _),
      extChartAt_target_subset_range _ ((extChartAt I x).map_source hz)⟩)
  rw [nhdsWithin_prod_eq]
  filter_upwards [Filter.prod_mem_prod self_mem_nhdsWithin
    (extChartAt_target_mem_nhdsWithin' hz)] with X hX
  exact RoughForm.inChartAt_mpullback_extChartAt _ x hX.2

/-- A family `K p` of flat forms on an open set `s` intersected with the model range, jointly `C^n`
in the chart coordinates of `p` and the point, pulled back along the chart at `x` and cut off by a
`C^n` function supported where the chart lands in `s`, is a `C^n` vertical form on `N × M`. This is
the family version of `TauCeti.isSmoothForm_smul_mpullback_extChartAt`. -/
theorem isSmoothForm_verticalForm_smul_mpullback_extChartAt {n : WithTop ℕ∞} [IsManifold I 1 M]
    [IsManifold J 1 N] [IsManifold I (n + 1) M] [IsManifold J (n + 1) N] {x : M} {s : Set E}
    (hs : IsOpen s) {K : N → E → E [⋀^Fin k]→L[ℝ] F}
    (hK : ∀ p₀ : N, ∀ w ∈ s ∩ range I, ContDiffWithinAt ℝ n
      (fun X : EN × E ↦ K ((extChartAt J p₀).symm X.1) X.2) (range J ×ˢ range I)
      (extChartAt J p₀ p₀, w))
    {χ : M → ℝ} (hχ : ContMDiff I 𝓘(ℝ) n χ)
    (hχs : tsupport χ ⊆ (chartAt H x).source ∩ extChartAt I x ⁻¹' s) :
    IsSmoothForm (J.prod I) n (verticalForm J fun p y ↦
      χ y • mpullback I 𝓘(ℝ, E) (extChartAt I x) (K p : RoughForm 𝓘(ℝ, E) E F k) y) := by
  rw [isSmoothForm_def, verticalForm_fun_smul]
  -- The uncut vertical form is `C^n` over the chart domain, which contains the support of the
  -- cutoff.
  refine (hχ.comp contMDiff_snd).contMDiffOn.smul_section_of_tsupport
    (isOpen_univ.prod (isOpen_extChartAt_preimage x hs))
    ((tsupport_comp_subset_preimage χ continuous_snd).trans fun z hz ↦ ⟨mem_univ _, hχs hz⟩)
    fun z hz ↦ ContMDiffAt.contMDiffWithinAt ?_
  obtain ⟨hzs, hzr⟩ := mem_extChartAt_source_and_mem_of_mem_preimage hz.2
  exact contMDiffAt_verticalForm_mpullback_extChartAt hzs (hK z.1 _ hzr)

end TauCeti
