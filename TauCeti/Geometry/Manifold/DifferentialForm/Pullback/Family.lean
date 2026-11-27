/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Pullback of differential forms along smooth families of maps

Let `f : N → M → M'` be a family of maps depending jointly `C^n` on the parameter `p ∈ N` and the
point `y ∈ M`, and let `g : N → M` be `C^m`, with `m + 1 ≤ n`. For a `C^m` form `φ` on `M'`, the
pullbacks `(f p)^* φ` evaluated at `g p` form a section of the bundle of alternating maps on `TM`
along `g`, and this section is `C^m` (`ContMDiffAt.mpullback_form_family`). For the constant
family `f p = f₀` and `g = id` this is `ContMDiffAt.mpullback_form`.

The main instance is the family of **slices** of a form `α` on a product `N × M`: the forms
`α_t = ι_t^* α` on `M` pulled back along the inclusions `ι_t : y ↦ (t, y)`. They depend smoothly on
`(t, y)` (`TauCeti.contMDiff_mpullback_prodMk_form`). So do their exterior derivatives, which are
the slices of the exterior derivative (`TauCeti.SmoothForm.contMDiff_mextDeriv_mpullback_prodMk`).
A smooth form on `ℝ × M` is how a smooth time-dependent family of forms on `M` is represented,
and this joint smoothness is what makes pointwise constructions from the slices, such as Reeb and
Moser vector fields, into smooth time-dependent vector fields. The basic example is the linear
interpolation `α₀ + c(t) (α₁ - α₀)` of two forms (`TauCeti.SmoothForm.lineMapFamily`).

In coordinates, the coordinate expression of a slice in a chart of `M` is that of `α` in a product
chart, precomposed with the inclusion of the second factor (`TauCeti.inChartAt_mpullback_prodMk`).
So for a `C^m` form `α` the coordinate expressions of the slices are jointly `C^m` in the chart
coordinates of the parameter and the point
(`TauCeti.IsSmoothForm.contDiffOn_inChartAt_mpullback_prodMk`).

## Main results

* `ContMDiffAt.mpullback_form_family`: pullbacks along a jointly smooth family of maps, evaluated
  along a smooth map, depend smoothly on the parameter.
* `TauCeti.contMDiff_mpullback_prodMk_form`: the slices `ι_t^* α` of a smooth form on `N × M` are
  jointly smooth in `(t, y)`.
* `TauCeti.SmoothForm.contMDiff_mpullback_prodMk`: the same for smooth pullback of smooth forms.
* `TauCeti.SmoothForm.contMDiff_mextDeriv_mpullback_prodMk`: the exterior derivatives of the slices
  of a smooth form on `N × M` are jointly smooth in `(t, y)`.
* `TauCeti.inChartAt_mpullback_prodMk`: the coordinate expression of a slice of a form on `N × M`
  in terms of that of the form in a product chart.
* `TauCeti.IsSmoothForm.contDiffOn_inChartAt_mpullback_prodMk`: the coordinate expressions of the
  slices of a `C^m` form on `N × M` are jointly `C^m` in the chart coordinates of the parameter and
  the point, on the product chart target.
* `TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodMap_id`: reparametrizing a family along
  `g × id` replaces the slice at `u` by the slice at `g u`.
* `TauCeti.SmoothForm.lineMapFamily`, `TauCeti.SmoothForm.mpullback_prodMk_lineMapFamily`: the
  family `t ↦ α₀ + c(t) (α₁ - α₀)` interpolating two forms, as a form on `ℝ × M`.
* `TauCeti.mpullback_prodMk_mpullback_prodMap`: the slices of the pullback of a family along
  `id × g` are the pullbacks along `g` of the slices.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M E' H' M' EN HN N F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [IsManifold I 1 M] [IsManifold I' 1 M']
  {k : ℕ} {m n : WithTop ℕ∞}

omit [TopologicalSpace N] in
/-- In fibre coordinates centred at `g p₀` and `f p₀ (g p₀)`, the pullback of `φ` along `f p` at
`g p` precomposes the coordinates of `φ` with the coordinates of the derivative of `f p`. The
target tangent trivialization must be valid at `f p (g p)`. -/
theorem inCoordinates_mpullback_family (φ : RoughForm I' M' F k) (f : N → M → M') (g : N → M)
    (p₀ p : N)
    (hp : f p (g p) ∈ (trivializationAt E' (TangentSpace I') (f p₀ (g p₀))).baseSet) :
    ContinuousAlternatingMap.inCoordinates E F (g p₀) (g p) (g p₀) (g p)
        (mpullback I I' (f p) φ (g p)) =
      (ContinuousAlternatingMap.inCoordinates E' F (f p₀ (g p₀)) (f p (g p)) (f p₀ (g p₀))
        (f p (g p)) (φ (f p (g p)))).compContinuousLinearMap
          (inTangentCoordinates I I' g (fun p ↦ f p (g p)) (fun p ↦ mfderiv I I' (f p) (g p))
            p₀ p) := by
  have h := ContinuousAlternatingMap.inCoordinates_compContinuousLinearMap
    (F₁ := E) (F₂ := E') (F₃ := F) (V₁ := TangentSpace I) (V₂ := TangentSpace I')
    (V₃ := Trivial M' F) (x₀ := g p₀) (y₀ := f p₀ (g p₀)) (z₀ := f p₀ (g p₀))
    (φ (f p (g p))) (mfderiv I I' (f p) (g p)) hp
  ext v
  simpa only [ContinuousAlternatingMap.inCoordinates,
    Bundle.Trivial.eq_trivialization M F (trivializationAt F (Trivial M F) (g p₀)),
    Bundle.Trivial.eq_trivialization M' F (trivializationAt F (Trivial M' F) (f p₀ (g p₀))),
    Bundle.Trivial.continuousLinearMapAt_trivialization,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_def,
    ContinuousLinearMap.id_apply, inTangentCoordinates, id_eq, mpullback_apply]
    using congrArg (fun a ↦ a v) h

/-- **Pullback along a smooth family of maps.** Let `f : N → M → M'` be jointly `C^n` at
`(p₀, g p₀)` and `g : N → M` be `C^m` at `p₀`, with `m + 1 ≤ n`. If the form `φ` is `C^m` at
`f p₀ (g p₀)`, then the pullbacks `(f p)^* φ` at `g p` form a `C^m` section along `g` at `p₀`. -/
theorem _root_.ContMDiffAt.mpullback_form_family [IsManifold J 1 N] {φ : RoughForm I' M' F k}
    {f : N → M → M'} {g : N → M} {p₀ : N}
    (hφ : ContMDiffAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E' [⋀^Fin k]→L[ℝ] F) y (φ y)) (f p₀ (g p₀)))
    (hf : ContMDiffAt (J.prod I) I' n (Function.uncurry f) (p₀, g p₀))
    (hg : ContMDiffAt J I m g p₀) (hmn : m + 1 ≤ n) :
    ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun p ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) (g p)
        (mpullback I I' (f p) φ (g p))) p₀ := by
  have hfg : ContMDiffAt J I' m (fun p ↦ f p (g p)) p₀ :=
    (hf.of_le ((le_add_of_nonneg_right zero_le_one).trans hmn)).comp p₀
      (contMDiffAt_id.prodMk hg)
  have hcoeff := ((contMDiffAt_continuousAlternatingMap_bundle _).mp hφ).2
  have hc := hcoeff.comp p₀ hfg
  have hd := hf.mfderiv f g hg hmn
  have hpre := ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
    (𝕜 := ℝ) (E := E) (F := E') (G := F) (ι := Fin k) m
  have hp := (hpre.comp_contMDiffAt hd).clm_apply hc
  apply (contMDiffAt_continuousAlternatingMap_bundle _).mpr
  refine ⟨hg, hp.congr_of_eventuallyEq ?_⟩
  have hmem : (fun p ↦ f p (g p)) ⁻¹'
      (trivializationAt E' (TangentSpace I') (f p₀ (g p₀))).baseSet ∈ 𝓝 p₀ :=
    hfg.continuousAt.preimage_mem_nhds
      ((trivializationAt E' (TangentSpace I') (f p₀ (g p₀))).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' (f p₀ (g p₀))))
  filter_upwards [hmem] with p hp
  simpa only [Function.comp_apply, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply]
    using inCoordinates_mpullback_family (I := I) φ f g p₀ p hp

/-- **Slices of a form on a product are jointly smooth.** For a `C^m` form `α` on `N × M`, the
slices `ι_t^* α`, pulled back along the inclusions `ι_t : y ↦ (t, y)`, form a `C^m` section along
the projection `(t, y) ↦ y`. -/
theorem contMDiff_mpullback_prodMk_form [IsManifold J 1 N]
    {α : RoughForm (J.prod I) (N × M) F k}
    (hα : ContMDiff (J.prod I) ((J.prod I).prod 𝓘(ℝ, (EN × E) [⋀^Fin k]→L[ℝ] F)) m
      (fun p ↦ TotalSpace.mk' ((EN × E) [⋀^Fin k]→L[ℝ] F) p (α p))) :
    ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2
        (mpullback I (J.prod I) (Prod.mk p.1) α p.2)) := by
  intro p
  exact ContMDiffAt.mpullback_form_family (hα (p.1, p.2))
    (f := fun q : N × M ↦ Prod.mk q.1) (g := Prod.snd) (n := ω)
    ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).contMDiffAt contMDiffAt_snd le_top

/-- The slices `ι_t^* α` of a smooth form `α` on `N × M` form a smooth section along the projection
`(t, y) ↦ y`. This is `TauCeti.contMDiff_mpullback_prodMk_form` for smooth pullback. -/
theorem SmoothForm.contMDiff_mpullback_prodMk [IsManifold J ∞ N]
    (α : SmoothForm (J.prod I) (N × M) F k) :
    ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2
        ((mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α).val p.2)) := by
  simpa only [coe_mpullback] using contMDiff_mpullback_prodMk_form α.contMDiff

/-- **Exterior derivatives of slices are jointly smooth.** For a smooth form `α` on `N × M`, the
exterior derivatives `d(ι_t^* α)` of its slices form a smooth section along the projection
`(t, y) ↦ y`. -/
theorem SmoothForm.contMDiff_mextDeriv_mpullback_prodMk [IsManifold I 2 M] [IsManifold J 2 N]
    (α : SmoothForm (J.prod I) (N × M) F k) :
    ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] F)) ∞
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin (k + 1)]→L[ℝ] Trivial M F y) p.2
        (mextDeriv (mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α).val p.2)) := by
  -- The exterior derivative of a slice is the slice of the exterior derivative.
  convert contMDiff_mpullback_prodMk_form (contMDiff_mextDeriv α) using 3 with p
  rw [← mextDerivₗ_apply, mextDerivₗ_mpullback, coe_mpullback, mextDerivₗ_apply]

/-- **Coordinates of a slice.** In the chart of `M` at `a.2`, the coordinate expression of the
slice `ι_p^* φ` of a form `φ` on `N × M`, for `p` in the chart of `N` at `a.1`, is the coordinate
expression of `φ` in the product chart at `a`, at the coordinates of `p`, precomposed with the
inclusion of the second factor. -/
theorem inChartAt_mpullback_prodMk [IsManifold J 1 N]
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
  ext v
  rw [RoughForm.inChartAt_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    RoughForm.inChartAt_apply, mpullback_apply]
  refine φ.apply_congr hsymm.symm fun i ↦ ?_
  rw [Manifold.mfderivWithin_extChartAt_prod_symm_apply hx, h]
  -- The first component of `inr ℝ _ _ u` is `0`, and the second is `u`.
  exact Prod.ext (map_zero _).symm rfl

/-- **The slices of a smooth form are jointly smooth in coordinates.** For a `C^m` form `φ` on
`N × M`, the coordinate expression in the chart of `M` at `a.2` of the slice `ι_p^* φ`, at the
point of `N` with coordinate `X.1` in the chart at `a.1` and at the coordinate `X.2`, is jointly
`C^m` in `X` on the target of the product chart at `a`. -/
theorem IsSmoothForm.contDiffOn_inChartAt_mpullback_prodMk [IsManifold J 1 N]
    [IsManifold I (m + 1) M] [IsManifold J (m + 1) N] {φ : RoughForm (J.prod I) (N × M) F k}
    (hφ : IsSmoothForm (J.prod I) m φ) (a : N × M) :
    ContDiffOn ℝ m
      (fun X : EN × E ↦
        (TauCeti.mpullback I (J.prod I) (Prod.mk ((extChartAt J a.1).symm X.1)) φ).inChartAt a.2
          X.2)
      (extChartAt (J.prod I) a).target := by
  -- Precomposition with the inclusion of the second factor, a continuous linear map.
  let L : (EN × E) [⋀^Fin k]→L[ℝ] F →L[ℝ] E [⋀^Fin k]→L[ℝ] F :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM (ContinuousLinearMap.inr ℝ EN E)
  have hφa : ContDiffOn ℝ m (L ∘ φ.inChartAt a) (extChartAt (J.prod I) a).target := fun X hX ↦
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
/-! ### Linear interpolation of two forms -/

/-- **The linear interpolation of two forms, as a form on `ℝ × M`.** For smooth forms `α₀`, `α₁`
on `M` and a smooth function `c : ℝ → ℝ`, the smooth form on `ℝ × M` whose slice at time `t` is
`α₀ + c(t) (α₁ - α₀)` (`TauCeti.SmoothForm.mpullback_prodMk_lineMapFamily`). It is the pullback
of `α₀` along the projection to `M`, plus `c(t)` times the pullback of `α₁ - α₀`. Reparametrizing
the segment by a smooth step function `c` gives a family which is constant for `t ≤ 0` and for
`t ≥ 1`, as Moser's and Gray's arguments use. -/
def SmoothForm.lineMapFamily (α₀ α₁ : SmoothForm I M F k) {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) :
    SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F k :=
  mpullback Prod.snd contMDiff_snd α₀ +
    funSMulₗ ⟨fun p ↦ c p.1, by exact hc.contMDiff.comp contMDiff_fst⟩
      (mpullback Prod.snd contMDiff_snd (α₁ - α₀))

/-- The slices of the pullback of a form `τ` on `M` along the projection `N × M → M` are `τ`:
`ι_t^* pr₂^* τ = τ`, since `Prod.snd ∘ Prod.mk t` is the identity of `M`. -/
@[simp]
theorem SmoothForm.mpullback_prodMk_mpullback_snd [IsManifold J 1 N] (τ : SmoothForm I M F k)
    (t : N) :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
      (mpullback Prod.snd contMDiff_snd τ : SmoothForm (J.prod I) (N × M) F k) = τ :=
  (mpullback_mpullback (Prod.mk t) Prod.snd (I' := J.prod I)
    (contMDiff_const.prodMk contMDiff_id) contMDiff_snd τ).trans
      (LinearMap.congr_fun mpullback_id τ)

/-- **Reparametrizing a family.** The slices of the pullback of a form `β` on `N' × M` along
`g × id` are slices of `β`: `ι_u^* (g × id)^* β = ι_(g u)^* β`, since
`Prod.map g id ∘ Prod.mk u = Prod.mk (g u)`. -/
theorem SmoothForm.mpullback_prodMk_mpullback_prodMap_id {EN' HN' N' : Type*}
    [NormedAddCommGroup EN'] [NormedSpace ℝ EN'] [TopologicalSpace HN'] [TopologicalSpace N']
    [ChartedSpace HN' N'] {J' : ModelWithCorners ℝ EN' HN'} [IsManifold J 1 N] [IsManifold J' 1 N']
    (β : SmoothForm (J'.prod I) (N' × M) F k) {g : N → N'} (hg : ContMDiff J J' ∞ g) (u : N) :
    mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id)
        (mpullback (Prod.map g id) (hg.prodMap contMDiff_id) β :
          SmoothForm (J.prod I) (N × M) F k) =
      mpullback (Prod.mk (g u)) (contMDiff_const.prodMk contMDiff_id) β :=
  mpullback_mpullback (Prod.mk u) (Prod.map g id) (I' := J.prod I)
    (contMDiff_const.prodMk contMDiff_id) (hg.prodMap contMDiff_id) β

/-- The slices of `TauCeti.SmoothForm.lineMapFamily α₀ α₁ hc` are the forms
`α₀ + c(t) (α₁ - α₀)`. -/
@[simp]
theorem SmoothForm.mpullback_prodMk_lineMapFamily (α₀ α₁ : SmoothForm I M F k) {c : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (t : ℝ) :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (lineMapFamily α₀ α₁ hc) =
      α₀ + c t • (α₁ - α₀) := by
  rw [lineMapFamily, map_add, mpullback_prodMk_mpullback_snd]
  congr 1
  apply Subtype.ext
  -- `erw`: the coercion of `funSMulₗ` carries the `IsManifold _ 1` instance derived from the
  -- product, which differs syntactically from the one in the goal.
  erw [coe_mpullback, coe_funSMulₗ, mpullback_fun_smul,
    ← coe_mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id),
    mpullback_prodMk_mpullback_snd]
  -- The bundled function evaluates at `(t, x)` to `c t` by definition, and the scalar multiple of
  -- a smooth form is computed pointwise.
  rfl

omit [IsManifold I 1 M] [IsManifold I' 1 M'] in
/-- The slices of the pullback of a family of forms along `id × g` are the pullbacks along `g` of
the slices: `ι_p^* (id × g)^* η = g^* ι_p^* η`, for a differentiable map `g`. -/
theorem mpullback_prodMk_mpullback_prodMap {g : M → M'} (hg : MDifferentiable I I' g)
    (η : RoughForm (J.prod I') (N × M') F k) (p : N) :
    mpullback I (J.prod I) (Prod.mk p) (mpullback (J.prod I) (J.prod I') (Prod.map id g) η) =
      mpullback I I' g (mpullback I' (J.prod I') (Prod.mk p) η) := by
  have hι : MDifferentiable I (J.prod I) (Prod.mk p : M → N × M) :=
    mdifferentiable_const.prodMk mdifferentiable_id
  have hι' : MDifferentiable I' (J.prod I') (Prod.mk p : M' → N × M') :=
    mdifferentiable_const.prodMk mdifferentiable_id
  have hcomp : Prod.map id g ∘ (Prod.mk p : M → N × M) = Prod.mk p ∘ g := (rfl)
  rw [← mpullback_comp hι (mdifferentiable_id.prodMap hg), hcomp, mpullback_comp hg hι']

end TauCeti
