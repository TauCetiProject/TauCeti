/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Symplectic.Darboux.EuclideanBasis
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Symplectic.Darboux.Basic
import TauCeti.Geometry.Symplectic.WittExtension

/-!
# Darboux's theorem on symplectic manifolds

Let `form` be a symplectic two-form (`TauCeti.SmoothTwoForm.IsSymplectic`: closed and fiberwise
nondegenerate) on a smooth manifold `M` with finite-dimensional real model space `E`. **Darboux's
theorem** states that around any interior point `x₀` of `M`—in particular, around every point when
`M` is boundaryless—there is a smooth partial diffeomorphism `chart` from `M` to `E` with
`x₀ ∈ chart.source` and `chart x₀ = 0` in which `form` becomes constant: for every
`x ∈ chart.source` and `v, w : TangentSpace I x`,

`form.eval₂ x v w = form₀ (mvfderiv I chart x v) (mvfderiv I chart x w)`.

Equivalently (`TauCeti.SmoothTwoForm.mpullback_constSmooth_eq_mpullback_subtype_val_iff`), on the
open submanifold `chart.source`, pulling the constant smooth symplectic form `form₀.constSmooth`
back along `chart` recovers the restriction of `form`.

Because any two symplectic forms on `E` are continuous-linearly symplectomorphic
(`TauCeti.SymplecticForm.exists_isSymplectomorphism`), the model symplectic form `form₀` on `E` may
be prescribed arbitrarily (`IsSymplectic.exists_darbouxChart_of_symplecticForm`). Composing instead
with a Darboux-basis isomorphism to `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)` produces
standard Euclidean Darboux coordinates pulling `TauCeti.stdSymplecticForm` back to `form`
(`IsSymplectic.exists_standardDarbouxChart`), and using a basis adapted to a nonzero vector
straightens any prescribed nonzero tangent vector at `x₀` to `(0, EuclideanSpace.single 0 1)` or
`(EuclideanSpace.single 0 1, 0)`.

The proof reads `form` in the preferred extended chart at `x₀` on the interior of its target,
applies the flat Moser–Darboux theorem
`TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq`, centers the resulting
coordinate diffeomorphism by translation, and transports the constant model form along continuous
linear symplectomorphisms.

## Main declarations

* `TauCeti.SmoothTwoForm.eval₂_constSmooth_mfderiv_eq` and
  `TauCeti.SmoothTwoForm.mpullback_constSmooth_eq_mpullback_subtype_val_iff`: equivalence between
  the pointwise `mvfderiv` Darboux formula, evaluation of `constSmooth` on `mfderiv`, and smooth
  pullback equality on the open submanifold `chart.source`.
* `TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_of_isInteriorPoint` and
  `TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart`: Darboux charts into the model space `E`.
* `TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_of_symplecticForm_of_isInteriorPoint` and
  `TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_of_symplecticForm`: Darboux charts pulling
  back any prescribed `form₀ : SymplecticForm E`.
* `TauCeti.SmoothTwoForm.IsSymplectic.exists_standardDarbouxChart`,
  `TauCeti.SmoothTwoForm.IsSymplectic.exists_standardDarbouxChart_of_finrank_eq`, and their
  `_of_isInteriorPoint` counterparts: standard Euclidean Darboux charts onto
  `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)` with `stdSymplecticForm`.
* `TauCeti.SmoothTwoForm.IsSymplectic.exists_standardDarbouxChart_snd_single`,
  `TauCeti.SmoothTwoForm.IsSymplectic.exists_standardDarbouxChart_fst_single`, and their
  `_of_isInteriorPoint` counterparts: standard Euclidean Darboux charts straightening a prescribed
  nonzero tangent vector at `x₀`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (Moser's argument and Darboux's theorem).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Theorem 22.13.
-/

public section

noncomputable section

open Set Filter TopologicalSpace
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothTwoForm

section PullbackCharacterization

variable {E H M F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Evaluating the constant smooth two-form `form₀.constSmooth` on `mfderiv` of a model-valued map
agrees with evaluating `form₀` directly on `mvfderiv`. -/
theorem eval₂_constSmooth_mfderiv_eq (form₀ : SymplecticForm F) (f : M → F) (x : M)
    (v w : TangentSpace I x) :
    form₀.constSmooth.eval₂ (f x) (mfderiv I 𝓘(ℝ, F) f x v) (mfderiv I 𝓘(ℝ, F) f x w) =
      form₀ (mvfderiv I f x v) (mvfderiv I f x w) := by
  rw [SymplecticForm.fromTangentSpace_constSmooth_apply]
  rfl

variable [IsManifold I ∞ M]

/-- A partial diffeomorphism `chart : M → F` pulls the constant smooth form `form₀.constSmooth`
back to the restriction of `form` on the open submanifold `chart.source` if and only if `form`
agrees pointwise on `chart.source` with `form₀` pulled back by `mvfderiv I chart`. -/
theorem mpullback_constSmooth_eq_mpullback_subtype_val_iff (form : SmoothTwoForm I M)
    (form₀ : SymplecticForm F) (chart : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞) :
    SmoothForm.mpullback (fun x : (⟨chart.source, chart.open_source⟩ : Opens M) ↦ chart x.1)
        (chart.contMDiffOn_toFun.comp_contMDiff contMDiff_subtype_val fun x ↦ x.2)
        form₀.constSmooth =
      SmoothForm.mpullback (Subtype.val : (⟨chart.source, chart.open_source⟩ : Opens M) → M)
        contMDiff_subtype_val form ↔
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w = form₀ (mvfderiv I chart x v) (mvfderiv I chart x w) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let U : Opens M := ⟨chart.source, chart.open_source⟩
  have hpoint (x : U) (v w : TangentSpace I x) :
      (SmoothForm.mpullback (fun y : U ↦ chart y.1)
          (chart.contMDiffOn_toFun.comp_contMDiff contMDiff_subtype_val fun y ↦ y.2)
          form₀.constSmooth).eval₂ x v w =
        form₀ (mvfderiv I chart x.1 (Manifold.tangentSpaceOpenEquiv (I := I) x v))
          (mvfderiv I chart x.1 (Manifold.tangentSpaceOpenEquiv (I := I) x w)) := by
    have hmd : MDifferentiableAt I 𝓘(ℝ, F) chart x.1 :=
      (chart.contMDiffOn_toFun.contMDiffAt (chart.open_source.mem_nhds x.2)).mdifferentiableAt
        (by simp)
    have hsub : MDifferentiableAt I I (Subtype.val : U → M) x :=
      (contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)
    rw [SmoothForm.eval₂_mpullback]
    refine (eval₂_constSmooth_mfderiv_eq form₀ (chart ∘ Subtype.val) x v w).trans ?_
    rw [mvfderiv_comp_apply x hmd hsub, mvfderiv_comp_apply x hmd hsub,
      Manifold.mfderiv_subtype_val]
    rfl
  rw [SmoothBundleForm.ext_eval₂_iff]
  constructor
  · intro h x hx v w
    let xU : U := ⟨x, hx⟩
    let vU : TangentSpace I xU := (Manifold.tangentSpaceOpenEquiv (I := I) xU).symm v
    let wU : TangentSpace I xU := (Manifold.tangentSpaceOpenEquiv (I := I) xU).symm w
    have hvw := h xU vU wU
    rw [hpoint, SmoothForm.eval₂_mpullback, Manifold.mfderiv_subtype_val] at hvw
    dsimp only [vU, wU, ContinuousLinearEquiv.coe_coe] at hvw
    rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply] at hvw
    exact hvw.symm
  · intro h x v w
    rw [hpoint, SmoothForm.eval₂_mpullback, Manifold.mfderiv_subtype_val]
    exact (h x.1 x.2 _ _).symm

/-- Transporting a Darboux chart along a continuous-linear symplectomorphism preserves its source,
maps `0` to `0`, composes `mvfderiv` with the linear equivalence, and pulls back the target
symplectic form. -/
private theorem trans_toDiffeomorph_darboux {F₁ F₂ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    {form : SmoothTwoForm I M} {ω₁ : SymplecticForm F₁} {ω₂ : SymplecticForm F₂}
    {chart : PartialDiffeomorph I 𝓘(ℝ, F₁) M F₁ ∞} {x₀ : M}
    (hx₀ : x₀ ∈ chart.source) (h0 : chart x₀ = 0)
    (hchart : ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
      form.eval₂ x v w = ω₁ (mvfderiv I chart x v) (mvfderiv I chart x w))
    (L : F₁ ≃L[ℝ] F₂) (hL : SymplecticForm.IsSymplectomorphism ω₁ ω₂ L.toLinearEquiv) :
    let chart' := chart.trans L.toDiffeomorph.toPartialDiffeomorph
    x₀ ∈ chart'.source ∧ chart' x₀ = 0 ∧
      (∀ x ∈ chart'.source,
        mvfderiv I chart' x = L.toContinuousLinearMap.comp (mvfderiv I chart x)) ∧
      ∀ x ∈ chart'.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w = ω₂ (mvfderiv I chart' x v) (mvfderiv I chart' x w) := by
  let chart' := chart.trans L.toDiffeomorph.toPartialDiffeomorph
  have hsrc : chart'.source = chart.source := by simp [chart']
  have hcoe (y : M) : chart' y = L (chart y) := by simp [chart']
  have hderiv (x : M) (hx : x ∈ chart'.source) :
      mvfderiv I chart' x = L.toContinuousLinearMap.comp (mvfderiv I chart x) := by
    have hx' : x ∈ chart.source := hsrc ▸ hx
    have hmd : MDifferentiableAt I 𝓘(ℝ, F₁) chart x :=
      (chart.contMDiffOn_toFun.contMDiffAt (chart.open_source.mem_nhds hx')).mdifferentiableAt
        (by simp)
    ext v
    have heq : ⇑chart' = ⇑L ∘ ⇑chart := funext hcoe
    rw [heq, mvfderiv_comp_apply_of_differentiableAt L.differentiableAt hmd,
      ContinuousLinearEquiv.fderiv, ContinuousLinearMap.comp_apply]
  refine ⟨hsrc.symm ▸ hx₀, by rw [hcoe, h0, map_zero], hderiv, fun x hx v w ↦ ?_⟩
  rw [hderiv x hx, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ← ContinuousLinearEquiv.coe_toLinearEquiv,
    hL.apply, hchart x (hsrc ▸ hx) v w]

end PullbackCharacterization

section ChartCoordinateHelpers

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The coordinate expression of a smooth two-form in `extChartAt I x₀` is `C^∞` on the interior of
the chart target. -/
private theorem contDiffOn_inChartAt_interior_target (form : SmoothTwoForm I M) (x₀ : M) :
    ContDiffOn ℝ (⊤ : ℕ∞) (RoughForm.inChartAt form.1 x₀) (interior (extChartAt I x₀).target) := by
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  intro z hz
  have hzt : z ∈ (extChartAt I x₀).target := interior_subset hz
  have hrange : ContDiffWithinAt ℝ ∞ (RoughForm.inChartAt form.1 x₀) (range I) z :=
    RoughForm.contDiffWithinAt_inChartAt_of_contDiffWithinAt_inChartAt form.1 hzt
      (mem_extChartAt_source _) (form.isSmoothForm.contDiffWithinAt_inChartAt_self _)
  have hnhds : range I ∈ 𝓝 z :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hz)
      (interior_subset.trans (extChartAt_target_subset_range x₀))
  exact (hrange.contDiffAt hnhds).contDiffWithinAt

/-- For a closed smooth two-form, the flat exterior derivative of its coordinate expression in
`extChartAt I x₀` vanishes on the interior of the chart target. -/
private theorem extDeriv_inChartAt_eq_zero_of_mem_interior_target {form : SmoothTwoForm I M}
    (hc : form.IsClosed) (x₀ : M) {z : E} (hz : z ∈ interior (extChartAt I x₀).target) :
    extDeriv (RoughForm.inChartAt form.1 x₀) z = 0 := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have hnhds : range I ∈ 𝓝 z :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hz)
      (interior_subset.trans (extChartAt_target_subset_range x₀))
  rw [← extDerivWithin_univ, ← extDerivWithin_congr_set (Filter.eventuallyEqSet_univ.2 hnhds)]
  exact (SmoothForm.isClosed_iff_forall_extDerivWithin_inChartAt_eq_zero form).1 hc
    x₀ z (interior_subset hz)

/-- On `(extChartAt I x₀).source`, evaluating `form` on two tangent vectors agrees with evaluating
`RoughForm.inChartAt form.1 x₀` on their `mvfderiv` images under `extChartAt I x₀`. -/
private theorem eval₂_eq_inChartAt_mvfderiv (form : SmoothTwoForm I M) {x₀ x : M}
    (hx : x ∈ (extChartAt I x₀).source) (v w : TangentSpace I x) :
    form.eval₂ x v w =
      RoughForm.inChartAt form.1 x₀ (extChartAt I x₀ x)
        ![mvfderiv I (extChartAt I x₀) x v, mvfderiv I (extChartAt I x₀) x w] := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have hz : extChartAt I x₀ x ∈ (extChartAt I x₀).target := (extChartAt I x₀).map_source hx
  let α : RoughForm 𝓘(ℝ, E) E ℝ 2 := RoughForm.inChartAt form.1 x₀
  have heq : mpullback I 𝓘(ℝ, E) (extChartAt I x₀) α x = form.1 x :=
    (RoughForm.inChartAt_chart_eq_iff hx).1
      (RoughForm.inChartAt_mpullback_extChartAt α x₀ hz)
  rw [SmoothBundleForm.eval₂_apply, ← heq, mpullback_apply]
  congr 1
  ext i
  fin_cases i <;>
    · simp
      rfl

/-- If `form` is fiberwise nondegenerate and equals `ω₁` pulled back by `mvfderiv I chart₁` at `x₀`,
then `mvfderiv I chart₁ x₀` carries nonzero tangent vectors to nonzero vectors. -/
private theorem mvfderiv_ne_zero_of_eval₂_eq {form : SmoothTwoForm I M}
    (hnd : form.IsNondegenerate) {chart₁ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞}
    {ω₁ : SymplecticForm E} {x₀ : M} {v₀ : TangentSpace I x₀} (hv₀ : v₀ ≠ 0)
    (hchart₁ : ∀ w : TangentSpace I x₀,
      form.eval₂ x₀ v₀ w = ω₁ (mvfderiv I chart₁ x₀ v₀) (mvfderiv I chart₁ x₀ w)) :
    mvfderiv I chart₁ x₀ v₀ ≠ 0 := fun hu ↦
  hv₀ (isNondegenerate_iff_separatingLeft.1 hnd x₀ v₀ fun w ↦ by
    rw [hchart₁ w, hu]
    exact LinearMap.map_zero₂ ω₁.toBilinForm _)

end ChartCoordinateHelpers

section Darboux

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Darboux's theorem at an interior point.** Around any interior point `x₀` of a smooth manifold
carrying a symplectic two-form `form`, there are a smooth partial diffeomorphism `chart` into the
model space `E` with `x₀ ∈ chart.source` and `chart x₀ = 0` and a constant symplectic form `form₀`
on `E` whose pullback by `mvfderiv I chart` equals `form` on `chart.source`. -/
theorem IsSymplectic.exists_darbouxChart_of_isInteriorPoint
    {form : SmoothTwoForm I M} (hform : form.IsSymplectic) {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (chart : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (form₀ : SymplecticForm E),
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w = form₀ (mvfderiv I chart x v) (mvfderiv I chart x w) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let η : E → E [⋀^Fin 2]→L[ℝ] ℝ := RoughForm.inChartAt form.1 x₀
  let W : Set E := interior (extChartAt I x₀).target
  let y₀ : E := extChartAt I x₀ x₀
  have hy₀W : y₀ ∈ W := (ModelWithCorners.isInteriorPoint_iff (I := I)).mp hx₀
  have hηy₀ : η y₀ = form.1 x₀ := RoughForm.inChartAt_extChartAt_self form.1 x₀
  have hnd : ∀ v : E, (∀ w : E, η y₀ ![v, w] = 0) → v = 0 := by
    intro v hv
    let v' : TangentSpace I x₀ := v
    exact isNondegenerate_iff_separatingLeft.1 hform.isNondegenerate x₀ v' fun w ↦
      (SmoothBundleForm.eval₂_apply form x₀ v' w).trans
        ((congrArg (fun A : E [⋀^Fin 2]→L[ℝ] ℝ ↦ A ![v, w]) hηy₀.symm).trans (hv w))
  -- Build the constant algebraic symplectic form `form₀` from `η y₀`.
  let B₀ : LinearMap.BilinForm ℝ E := MultilinearMap.toBilinMap (η y₀).toMultilinearMap
  have hB₀_apply (u w : E) : B₀ u w = η y₀ ![u, w] := by simp [B₀]
  have hB₀_alt : B₀.IsAlt :=
    MultilinearMap.isAlt_toBilinMap fun v ↦ (η y₀).map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one
  let form₀ : SymplecticForm E :=
    { toBilinForm := B₀
      isAlt := hB₀_alt
      nondegenerate := (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hB₀_alt.isRefl).2
        fun v hv ↦ hnd v fun w ↦ (hB₀_apply v w).symm.trans (hv w) }
  -- Apply the flat Moser–Darboux theorem to `η` on `W` around `y₀`.
  obtain ⟨ψ, hψy₀, hev⟩ :=
    exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq (r := (⊤ : ℕ∞)) le_top
      isOpen_interior hy₀W (contDiffOn_inChartAt_interior_target form x₀)
      (fun z hz ↦ extDeriv_inChartAt_eq_zero_of_mem_interior_target hform.isClosed x₀ hz) hnd
  have hψsymm_y₀ : ψ.symm y₀ = y₀ := ψ.symm_apply_eq.2 hψy₀.symm
  -- Pull the neighborhood where `ψ^* η = η y₀` back along `ψ.symm` and intersect with `W`.
  have hnhds_symm :
      {y : E | (η (ψ (ψ.symm y))).compContinuousLinearMap (fderiv ℝ ψ (ψ.symm y)) = η y₀} ∩ W ∈
        𝓝 y₀ := by
    refine Filter.inter_mem ?_ (isOpen_interior.mem_nhds hy₀W)
    have hcont : ContinuousAt ψ.symm y₀ := ψ.symm.continuous.continuousAt
    rw [ContinuousAt, hψsymm_y₀] at hcont
    exact hcont hev
  obtain ⟨V₀, hV₀_sub, hV₀_open, hy₀V₀⟩ := mem_nhds_iff.1 hnhds_symm
  -- Invert the flat pullback identity on `V₀`:
  -- `η y = (η y₀).compContinuousLinearMap (fderiv ℝ ψ.symm y)`.
  have hψ_diff : Differentiable ℝ ψ :=
    (contMDiff_iff_contDiff.1 ψ.contMDiff).differentiable (by simp)
  have hψsymm_diff : Differentiable ℝ ψ.symm :=
    (contMDiff_iff_contDiff.1 ψ.symm.contMDiff).differentiable (by simp)
  have hη_inv (y : E) (hy : y ∈ V₀) (u₁ u₂ : E) :
      η y ![u₁, u₂] = η y₀ ![fderiv ℝ ψ.symm y u₁, fderiv ℝ ψ.symm y u₂] := by
    have hzy := (hV₀_sub hy).1
    have hcomp : (fderiv ℝ ψ (ψ.symm y)).comp (fderiv ℝ ψ.symm y) = ContinuousLinearMap.id ℝ E := by
      have hc := (fderiv_comp y (hψ_diff (ψ.symm y)) (hψsymm_diff y)).symm
      have hid : ⇑ψ ∘ ⇑ψ.symm = id := funext ψ.apply_symm_apply
      rwa [hid, fderiv_id] at hc
    have happ := congrArg
      (fun A : E [⋀^Fin 2]→L[ℝ] ℝ ↦ A ![fderiv ℝ ψ.symm y u₁, fderiv ℝ ψ.symm y u₂]) hzy
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ψ.apply_symm_apply] at happ
    rw [← happ]
    congr 1
    ext i
    fin_cases i <;> dsimp
    · exact (DFunLike.congr_fun hcomp u₁).symm
    · exact (DFunLike.congr_fun hcomp u₂).symm
  -- Center the flat diffeomorphism at `0` by subtracting `y₀`.
  let Φ_flat : E ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E :=
    ψ.symm.trans (Diffeomorph.smulAdd ∞ (1 : ℝ) (-y₀) one_ne_zero)
  have hΦ_coe : ⇑Φ_flat = fun y ↦ ψ.symm y - y₀ := by
    ext y
    simp [Φ_flat, sub_eq_add_neg]
  have hΦ_diff : Differentiable ℝ Φ_flat :=
    (contMDiff_iff_contDiff.1 Φ_flat.contMDiff).differentiable (by simp)
  -- Restrict `extChartPartialDiffeomorph` to the preimage of `V₀` and compose with `Φ_flat`.
  let e₀ := extChartPartialDiffeomorph I ∞ x₀
  let S : Set M := (extChartAt I x₀).source ∩ extChartAt I x₀ ⁻¹' V₀
  have hS_open : IsOpen S := isOpen_extChartAt_preimage' (I := I) x₀ hV₀_open
  have hS_sub : S ⊆ e₀.source := by
    rw [extChartPartialDiffeomorph_source]
    exact inter_subset_inter_right _ (preimage_mono fun z hz ↦ (hV₀_sub hz).2)
  let chart : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ :=
    (e₀.restrOpen S hS_open).trans Φ_flat.toPartialDiffeomorph
  have hchart_src : chart.source = S := by
    simp [chart, inter_eq_right.2 hS_sub]
  have hchart_coe (y : M) : chart y = Φ_flat (extChartAt I x₀ y) := by
    simp [chart, e₀]
  have hx₀_src : x₀ ∈ chart.source := by
    rw [hchart_src]
    exact ⟨mem_extChartAt_source x₀, hy₀V₀⟩
  have hchart_x₀ : chart x₀ = 0 := by
    rw [hchart_coe, congrFun hΦ_coe, hψsymm_y₀, sub_self]
  refine ⟨chart, form₀, hx₀_src, hchart_x₀, fun x hx v w ↦ ?_⟩
  have hxS : x ∈ S := hchart_src ▸ hx
  have hx_chart : x ∈ (chartAt H x₀).source := by simpa only [extChartAt_source] using hxS.1
  have hmd_ext : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x₀) x :=
    mdifferentiableAt_extChartAt hx_chart
  have hmvf (u : TangentSpace I x) :
      mvfderiv I chart x u =
        fderiv ℝ ψ.symm (extChartAt I x₀ x) (mvfderiv I (extChartAt I x₀) x u) := by
    have heq_fn : ⇑chart = ⇑Φ_flat ∘ ⇑(extChartAt I x₀) := funext hchart_coe
    rw [heq_fn, mvfderiv_comp_apply_of_differentiableAt (hΦ_diff _) hmd_ext, hΦ_coe,
      fderiv_sub_const]
  rw [eval₂_eq_inChartAt_mvfderiv form hxS.1 v w, hmvf v, hmvf w]
  exact (hη_inv (extChartAt I x₀ x) hxS.2 _ _).trans (hB₀_apply _ _).symm

/-- **Darboux's theorem for a prescribed model symplectic form at an interior point.** Around any
interior point `x₀` of `(M, form)` and for any chosen symplectic form `form₀` on `E`, there is a
centered smooth partial diffeomorphism pulling `form₀` back to `form`. -/
theorem IsSymplectic.exists_darbouxChart_of_symplecticForm_of_isInteriorPoint
    {form : SmoothTwoForm I M} (hform : form.IsSymplectic) (form₀ : SymplecticForm E)
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    ∃ chart : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞,
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w = form₀ (mvfderiv I chart x v) (mvfderiv I chart x w) := by
  obtain ⟨chart₁, ω₁, hx₀₁, h0₁, hchart₁⟩ := hform.exists_darbouxChart_of_isInteriorPoint hx₀
  obtain ⟨e, he⟩ := ω₁.exists_isSymplectomorphism form₀ rfl
  obtain ⟨hx₀', h0', -, hpull⟩ :=
    trans_toDiffeomorph_darboux hx₀₁ h0₁ hchart₁ e.toContinuousLinearEquiv he
  exact ⟨_, hx₀', h0', hpull⟩

/-- **Standard Euclidean Darboux coordinates at an interior point.** Around any interior point `x₀`
of `(M, form)`, there are `n : ℕ` and a smooth partial diffeomorphism onto an open neighborhood of
`0` in `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)` pulling `stdSymplecticForm` back to
`form`. -/
theorem IsSymplectic.exists_standardDarbouxChart_of_isInteriorPoint
    {form : SmoothTwoForm I M} (hform : form.IsSymplectic) {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) M
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∞),
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w =
          stdSymplecticForm (mvfderiv I chart x v) (mvfderiv I chart x w) := by
  obtain ⟨chart₁, ω₁, hx₀₁, h0₁, hchart₁⟩ := hform.exists_darbouxChart_of_isInteriorPoint hx₀
  obtain ⟨n, L, hL⟩ := ω₁.exists_continuousLinearEquiv_stdSymplecticForm
  obtain ⟨hx₀', h0', -, hpull⟩ := trans_toDiffeomorph_darboux hx₀₁ h0₁ hchart₁ L hL
  exact ⟨n, _, hx₀', h0', hpull⟩

/-- **Standard Euclidean Darboux coordinates at fixed dimension `2 * n` (interior point).** -/
theorem IsSymplectic.exists_standardDarbouxChart_of_finrank_eq_of_isInteriorPoint
    {form : SmoothTwoForm I M} (hform : form.IsSymplectic) {n : ℕ}
    (hn : Module.finrank ℝ E = 2 * n) {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    ∃ chart : PartialDiffeomorph I
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) M
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∞,
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w =
          stdSymplecticForm (mvfderiv I chart x v) (mvfderiv I chart x w) := by
  obtain ⟨chart₁, ω₁, hx₀₁, h0₁, hchart₁⟩ := hform.exists_darbouxChart_of_isInteriorPoint hx₀
  obtain ⟨L, hL⟩ := ω₁.exists_continuousLinearEquiv_stdSymplecticForm_of_finrank_eq hn
  obtain ⟨hx₀', h0', -, hpull⟩ := trans_toDiffeomorph_darboux hx₀₁ h0₁ hchart₁ L hL
  exact ⟨_, hx₀', h0', hpull⟩

/-- **Standard Euclidean Darboux coordinates straightening a nonzero tangent vector to
`(0, single 0 1)` at an interior point.** -/
theorem IsSymplectic.exists_standardDarbouxChart_snd_single_of_isInteriorPoint
    {form : SmoothTwoForm I M} (hform : form.IsSymplectic) {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) {v₀ : TangentSpace I x₀} (hv₀ : v₀ ≠ 0) :
    ∃ (m : ℕ) (chart : PartialDiffeomorph I
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (m + 1))) M
      (EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (m + 1))) ∞),
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      mvfderiv I chart x₀ v₀ = (0, EuclideanSpace.single 0 1) ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w =
          stdSymplecticForm (mvfderiv I chart x v) (mvfderiv I chart x w) := by
  obtain ⟨chart₁, ω₁, hx₀₁, h0₁, hchart₁⟩ := hform.exists_darbouxChart_of_isInteriorPoint hx₀
  obtain ⟨m, L, hL, hLv₀⟩ :=
    ω₁.exists_continuousLinearEquiv_stdSymplecticForm_apply_eq_snd_single
      (mvfderiv_ne_zero_of_eval₂_eq hform.isNondegenerate hv₀ (hchart₁ x₀ hx₀₁ v₀))
  obtain ⟨hx₀', h0', hderiv, hpull⟩ := trans_toDiffeomorph_darboux hx₀₁ h0₁ hchart₁ L hL
  refine ⟨m, _, hx₀', h0', ?_, hpull⟩
  rw [hderiv x₀ hx₀', ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hLv₀]

/-- **Standard Euclidean Darboux coordinates straightening a nonzero tangent vector to
`(single 0 1, 0)` at an interior point.** -/
theorem IsSymplectic.exists_standardDarbouxChart_fst_single_of_isInteriorPoint
    {form : SmoothTwoForm I M} (hform : form.IsSymplectic) {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) {v₀ : TangentSpace I x₀} (hv₀ : v₀ ≠ 0) :
    ∃ (m : ℕ) (chart : PartialDiffeomorph I
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (m + 1))) M
      (EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (m + 1))) ∞),
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      mvfderiv I chart x₀ v₀ = (EuclideanSpace.single 0 1, 0) ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w =
          stdSymplecticForm (mvfderiv I chart x v) (mvfderiv I chart x w) := by
  obtain ⟨chart₁, ω₁, hx₀₁, h0₁, hchart₁⟩ := hform.exists_darbouxChart_of_isInteriorPoint hx₀
  obtain ⟨m, L, hL, hLv₀⟩ :=
    ω₁.exists_continuousLinearEquiv_stdSymplecticForm_apply_eq_fst_single
      (mvfderiv_ne_zero_of_eval₂_eq hform.isNondegenerate hv₀ (hchart₁ x₀ hx₀₁ v₀))
  obtain ⟨hx₀', h0', hderiv, hpull⟩ := trans_toDiffeomorph_darboux hx₀₁ h0₁ hchart₁ L hL
  refine ⟨m, _, hx₀', h0', ?_, hpull⟩
  rw [hderiv x₀ hx₀', ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hLv₀]

section Boundaryless

variable [BoundarylessManifold I M]

/-- **Darboux's theorem.** Around every point `x₀` of a finite-dimensional boundaryless symplectic
manifold `(M, form)`, there are a smooth partial diffeomorphism `chart` into `E` with
`x₀ ∈ chart.source` and `chart x₀ = 0` and a constant symplectic form `form₀` on `E` whose pullback
by `mvfderiv I chart` equals `form` on `chart.source`. -/
theorem IsSymplectic.exists_darbouxChart
    {form : SmoothTwoForm I M} (hform : form.IsSymplectic) (x₀ : M) :
    ∃ (chart : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (form₀ : SymplecticForm E),
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w = form₀ (mvfderiv I chart x v) (mvfderiv I chart x w) :=
  hform.exists_darbouxChart_of_isInteriorPoint BoundarylessManifold.isInteriorPoint

/-- **Darboux's theorem for a prescribed model symplectic form.** Around every point `x₀` of a
finite-dimensional boundaryless symplectic manifold `(M, form)` and for any symplectic form `form₀`
on `E`, there is a centered smooth partial diffeomorphism pulling `form₀` back to `form`. -/
theorem IsSymplectic.exists_darbouxChart_of_symplecticForm
    {form : SmoothTwoForm I M} (hform : form.IsSymplectic) (form₀ : SymplecticForm E) (x₀ : M) :
    ∃ chart : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞,
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w = form₀ (mvfderiv I chart x v) (mvfderiv I chart x w) :=
  hform.exists_darbouxChart_of_symplecticForm_of_isInteriorPoint form₀
    BoundarylessManifold.isInteriorPoint

/-- **Standard Euclidean Darboux coordinates.** Around every point `x₀` of a finite-dimensional
boundaryless symplectic manifold `(M, form)`, there are `n : ℕ` and a smooth partial diffeomorphism
onto an open neighborhood of `0` in `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)` pulling
`stdSymplecticForm` back to `form`. -/
theorem IsSymplectic.exists_standardDarbouxChart
    {form : SmoothTwoForm I M} (hform : form.IsSymplectic) (x₀ : M) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) M
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∞),
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w =
          stdSymplecticForm (mvfderiv I chart x v) (mvfderiv I chart x w) :=
  hform.exists_standardDarbouxChart_of_isInteriorPoint BoundarylessManifold.isInteriorPoint

/-- **Standard Euclidean Darboux coordinates at fixed dimension `2 * n`.** -/
theorem IsSymplectic.exists_standardDarbouxChart_of_finrank_eq
    {form : SmoothTwoForm I M} (hform : form.IsSymplectic) {n : ℕ}
    (hn : Module.finrank ℝ E = 2 * n) (x₀ : M) :
    ∃ chart : PartialDiffeomorph I
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) M
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∞,
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w =
          stdSymplecticForm (mvfderiv I chart x v) (mvfderiv I chart x w) :=
  hform.exists_standardDarbouxChart_of_finrank_eq_of_isInteriorPoint hn
    BoundarylessManifold.isInteriorPoint

/-- **Standard Euclidean Darboux coordinates straightening a nonzero tangent vector to
`(0, single 0 1)`.** -/
theorem IsSymplectic.exists_standardDarbouxChart_snd_single
    {form : SmoothTwoForm I M} (hform : form.IsSymplectic) (x₀ : M)
    {v₀ : TangentSpace I x₀} (hv₀ : v₀ ≠ 0) :
    ∃ (m : ℕ) (chart : PartialDiffeomorph I
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (m + 1))) M
      (EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (m + 1))) ∞),
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      mvfderiv I chart x₀ v₀ = (0, EuclideanSpace.single 0 1) ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w =
          stdSymplecticForm (mvfderiv I chart x v) (mvfderiv I chart x w) :=
  hform.exists_standardDarbouxChart_snd_single_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint hv₀

/-- **Standard Euclidean Darboux coordinates straightening a nonzero tangent vector to
`(single 0 1, 0)`.** -/
theorem IsSymplectic.exists_standardDarbouxChart_fst_single
    {form : SmoothTwoForm I M} (hform : form.IsSymplectic) (x₀ : M)
    {v₀ : TangentSpace I x₀} (hv₀ : v₀ ≠ 0) :
    ∃ (m : ℕ) (chart : PartialDiffeomorph I
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (m + 1))) M
      (EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (m + 1))) ∞),
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      mvfderiv I chart x₀ v₀ = (EuclideanSpace.single 0 1, 0) ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w =
          stdSymplecticForm (mvfderiv I chart x v) (mvfderiv I chart x w) :=
  hform.exists_standardDarbouxChart_fst_single_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint hv₀

end Boundaryless

end Darboux

end SmoothTwoForm

end TauCeti

end
