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

open Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothTwoForm

section Helpers

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

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

end Helpers

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
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  let η : E → E [⋀^Fin 2]→L[ℝ] ℝ := RoughForm.inChartAt form.1 x₀
  let W : Set E := interior (extChartAt I x₀).target
  let y₀ : E := extChartAt I x₀ x₀
  have hy₀W : y₀ ∈ W := (ModelWithCorners.isInteriorPoint_iff (I := I)).mp hx₀
  have hηy₀ : η y₀ = form.1 x₀ := RoughForm.inChartAt_extChartAt_self form.1 x₀
  -- `TangentSpace I x₀` carries the model vector-space structure of `E`.
  let form₀ : SymplecticForm E := hform.isNondegenerate.symplecticFormAt x₀
  have hform₀_apply (u w : E) : form₀ u w = η y₀ ![u, w] := by
    let u' : TangentSpace I x₀ := u
    let w' : TangentSpace I x₀ := w
    exact (hform.isNondegenerate.symplecticFormAt_apply x₀ u' w').trans
      ((SmoothBundleForm.eval₂_apply form x₀ u' w').trans
        (congrArg (fun A : E [⋀^Fin 2]→L[ℝ] ℝ ↦ A ![u, w]) hηy₀.symm))
  have hnd : ∀ v : E, (∀ w : E, η y₀ ![v, w] = 0) → v = 0 := fun v hv ↦
    form₀.separatingLeft v fun w ↦ (hform₀_apply v w).trans (hv w)
  -- Apply the flat Moser–Darboux theorem to `η` on `W` around `y₀`.
  obtain ⟨ψ, hψy₀, hev⟩ :=
    exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq (r := (⊤ : ℕ∞)) le_top
      isOpen_interior hy₀W (form.isSmoothForm.contDiffOn_inChartAt_interior_target x₀)
      (fun z hz ↦ hform.isClosed.extDeriv_inChartAt_eq_zero x₀ hz) hnd
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
  have hvec : (fun i ↦ mvfderiv I (extChartAt I x₀) x (![v, w] i)) =
      ![mvfderiv I (extChartAt I x₀) x v, mvfderiv I (extChartAt I x₀) x w] := by
    ext i
    fin_cases i <;> rfl
  rw [SmoothBundleForm.eval₂_apply, RoughForm.apply_eq_inChartAt_mvfderiv form.1 hxS.1, hvec,
    hmvf v, hmvf w]
  exact (hη_inv (extChartAt I x₀ x) hxS.2 _ _).trans (hform₀_apply _ _).symm

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
