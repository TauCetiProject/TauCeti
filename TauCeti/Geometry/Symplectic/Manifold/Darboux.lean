/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Symplectic.Darboux.EuclideanBasis
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Symplectic.Darboux.Basic
import TauCeti.Geometry.Symplectic.Darboux.Momentum
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

The **Carathéodory–Jacobi–Lie theorem** for one function refines this: a smooth function `f` with
nonzero differential at `x₀` is a momentum coordinate of a Darboux chart. Composing a Darboux chart
with the flat normal form `TauCeti.SymplecticForm.exists_openPartialHomeomorph_eq_add_fderiv`
makes `f` affine in the chart, and in standard Euclidean Darboux coordinates `f = f x₀ + p₁`.

The proof reads `form` in the preferred extended chart at `x₀` on the interior of its target,
applies the centred flat Moser–Darboux theorem
`TauCeti.exists_diffeomorph_centered_forall_mem_eq_compContinuousLinearMap_fderiv`, composes its
diffeomorphism with the extended chart restricted to an open set
(`TauCeti.exists_partialDiffeomorph_comp_extChartAt`), and transports the constant model form along
continuous linear symplectomorphisms.

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
* `TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_eq_add`,
  `TauCeti.SmoothTwoForm.IsSymplectic.exists_standardDarbouxChart_eq_add_snd`, and their
  `_of_isInteriorPoint` counterparts: the Carathéodory–Jacobi–Lie normal form, a Darboux chart in
  which a function with nonzero differential is affine, respectively is `f x₀ + p₁`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (Moser's argument and Darboux's theorem).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Theorem 22.13.
* P. Libermann and C.-M. Marle, *Symplectic Geometry and Analytical Mechanics*, Reidel, 1987,
  Chapter III (the Carathéodory–Jacobi–Lie theorem).
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
    rw [heq]
    exact (L.toContinuousLinearMap).mvfderiv_comp_apply hmd v
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

omit [IsManifold I ∞ M] in
/-- Composing a chart with a smooth open partial homeomorphism `κ` of the model space: the source,
the values and the derivative of the composite. -/
private theorem trans_ofOpenPartialHomeomorph {chart : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞}
    {κ : OpenPartialHomeomorph E E} (hκ : ContDiffOn ℝ ∞ κ κ.source)
    (hκs : ContDiffOn ℝ ∞ κ.symm κ.target) :
    let chart' := chart.trans (PartialDiffeomorph.ofOpenPartialHomeomorph κ hκ hκs)
    (∀ x, x ∈ chart'.source ↔ x ∈ chart.source ∧ chart x ∈ κ.source) ∧
      (∀ x, chart' x = κ (chart x)) ∧ ∀ x ∈ chart'.source, ∀ v : TangentSpace I x,
        mvfderiv I chart' x v = fderiv ℝ κ (chart x) (mvfderiv I chart x v) := by
  intro chart'
  have hsrc (x : M) : x ∈ chart'.source ↔ x ∈ chart.source ∧ chart x ∈ κ.source := by
    simp [chart']
  have hcoe (x : M) : chart' x = κ (chart x) := by
    simp [chart']
  refine ⟨hsrc, hcoe, fun x hx v ↦ ?_⟩
  obtain ⟨hxc, hxκ⟩ := (hsrc x).1 hx
  have hκd : DifferentiableAt ℝ κ (chart x) :=
    (hκ.differentiableOn (by simp) _ hxκ).differentiableAt (κ.open_source.mem_nhds hxκ)
  have hcd : MDifferentiableAt I 𝓘(ℝ, E) chart x :=
    (chart.contMDiffOn_toFun.contMDiffAt (chart.open_source.mem_nhds hxc)).mdifferentiableAt
      (by simp)
  have heq : ⇑chart' = ⇑κ ∘ ⇑chart := funext hcoe
  rw [heq]
  exact mvfderiv_comp_apply_of_differentiableAt hκd hcd v

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
  have hnd : ∀ v : E, (∀ w : E, η y₀ ![v, w] = 0) → v = 0 :=
    form.inChartAt_extChartAt_self_nondegenerate
      (hform.isNondegenerate.nondegenerate_bilinFormAt x₀)
  -- Apply the flat Moser–Darboux theorem to `η` on `W` around `y₀`.
  obtain ⟨Φ_flat, V₀, hΦy₀, hV₀_open, hy₀V₀, hV₀_sub, hη_inv⟩ :=
    exists_diffeomorph_centered_forall_mem_eq_compContinuousLinearMap_fderiv (r := (⊤ : ℕ∞))
      le_top isOpen_interior hy₀W (form.isSmoothForm.contDiffOn_inChartAt_interior_target x₀)
      (fun z hz ↦ hform.isClosed.extDeriv_inChartAt_eq_zero x₀ hz) hnd
  obtain ⟨chart, hchart_src, hchart_coe, hmvf⟩ :=
    exists_partialDiffeomorph_comp_extChartAt I ∞ x₀ hV₀_open hV₀_sub
      (by exact_mod_cast le_top) Φ_flat
  have hx₀_src : x₀ ∈ chart.source := by
    rw [hchart_src]
    exact ⟨mem_extChartAt_source x₀, hy₀V₀⟩
  have hchart_x₀ : chart x₀ = 0 := by
    rw [hchart_coe]
    exact hΦy₀
  refine ⟨chart, form₀, hx₀_src, hchart_x₀, fun x hx v w ↦ ?_⟩
  have hxS : x ∈ (extChartAt I x₀).source ∩ extChartAt I x₀ ⁻¹' V₀ :=
    hchart_src ▸ hx
  have hvec : (fun i ↦ mvfderiv I (extChartAt I x₀) x (![v, w] i)) =
      ![mvfderiv I (extChartAt I x₀) x v, mvfderiv I (extChartAt I x₀) x w] := by
    ext i
    fin_cases i <;> rfl
  rw [SmoothBundleForm.eval₂_apply, RoughForm.apply_eq_inChartAt_mvfderiv form.1 hxS.1, hvec,
    hmvf x hx v, hmvf x hx w]
  rw [hform₀_apply, hη_inv (extChartAt I x₀ x) hxS.2]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

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

/-- **The Carathéodory–Jacobi–Lie normal form for one function at an interior point.** Let `f` be
smooth near an interior point `x₀` of a finite-dimensional symplectic manifold `(M, form)`, with
nonzero differential at `x₀`. Then some Darboux chart around `x₀`, pulling a constant symplectic
form `form₀` on the model space back to `form`, makes `f` affine: `f = f x₀ + ℓ ∘ chart` for a
nonzero linear functional `ℓ`. In linear Darboux coordinates for `form₀` whose first momentum
coordinate is `ℓ`, the function `f - f x₀` is the momentum coordinate `p₁` of a Darboux chart
(`IsSymplectic.exists_standardDarbouxChart_eq_add_snd_of_isInteriorPoint`). -/
theorem IsSymplectic.exists_darbouxChart_eq_add_of_isInteriorPoint {form : SmoothTwoForm I M}
    (hform : form.IsSymplectic) {f : M → ℝ} {U : Set M} {x₀ : M} (hx₀ : I.IsInteriorPoint x₀)
    (hU : U ∈ 𝓝 x₀) (hf : ContMDiffOn I 𝓘(ℝ) ∞ f U) (hdf : mvfderiv I f x₀ ≠ 0) :
    ∃ (chart : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (form₀ : SymplecticForm E) (ℓ : E →L[ℝ] ℝ),
      ℓ ≠ 0 ∧ x₀ ∈ chart.source ∧ chart x₀ = 0 ∧ chart.source ⊆ U ∧
      (∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w = form₀ (mvfderiv I chart x v) (mvfderiv I chart x w)) ∧
      ∀ x ∈ chart.source, f x = f x₀ + ℓ (chart x) := by
  obtain ⟨c, form₀, hx₀c, hc0, hc⟩ := hform.exists_darbouxChart_of_isInteriorPoint hx₀
  -- Read `f` in the Darboux chart `c`, on an open neighbourhood `T` of `0 = c x₀`.
  let g : E → ℝ := fun y ↦ f (c.toPartialEquiv.symm y)
  set T := c.target ∩ c.toPartialEquiv.symm ⁻¹' interior U
  have hTo : IsOpen T := c.toOpenPartialHomeomorph.continuousOn_symm.isOpen_inter_preimage
    c.open_target isOpen_interior
  have hlinv (x : M) (hx : x ∈ c.source) : c.toPartialEquiv.symm (c x) = x :=
    c.toPartialEquiv.left_inv hx
  have hcs0 : c.toPartialEquiv.symm 0 = x₀ := by rw [← hc0, hlinv x₀ hx₀c]
  have h0T : (0 : E) ∈ T := by
    refine ⟨hc0 ▸ c.toPartialEquiv.map_source hx₀c, ?_⟩
    rw [mem_preimage, hcs0]
    exact mem_interior_iff_mem_nhds.2 hU
  have hg : ContDiffOn ℝ ∞ g T :=
    contMDiffOn_iff_contDiffOn.1 ((hf.mono interior_subset).comp
      (c.contMDiffOn_invFun.mono inter_subset_left) fun y hy ↦ hy.2)
  -- `f = g ∘ c` near `x₀`, so `dg_0 ≠ 0`.
  have hg0 : fderiv ℝ g 0 ≠ 0 := by
    intro h
    have hgd : DifferentiableAt ℝ g (c x₀) :=
      hc0 ▸ (hg.differentiableOn (by simp) 0 h0T).differentiableAt (hTo.mem_nhds h0T)
    have hcd : MDifferentiableAt I 𝓘(ℝ, E) c x₀ :=
      (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hx₀c)).mdifferentiableAt (by simp)
    have hfg : f =ᶠ[𝓝 x₀] g ∘ c := by
      filter_upwards [c.open_source.mem_nhds hx₀c] with x hx
      simp [g, hlinv x hx]
    refine hdf (ContinuousLinearMap.ext fun v ↦ ?_)
    rw [hfg.mvfderiv_eq, mvfderiv_comp_apply_of_differentiableAt hgd hcd, hc0, h]
    simp only [zero_apply]
  obtain ⟨κ, h0κ, hκ0, hκT, hκc, hκs, hκσ, hκg⟩ :=
    form₀.exists_openPartialHomeomorph_eq_add_fderiv (hTo.mem_nhds h0T) hg hg0
  obtain ⟨hsrc, hcoe, hd⟩ := trans_ofOpenPartialHomeomorph (chart := c) hκc hκs
  refine ⟨_, form₀, fderiv ℝ g 0, hg0, (hsrc x₀).2 ⟨hx₀c, hc0 ▸ h0κ⟩,
    by rw [hcoe, hc0, hκ0], fun x hx ↦ ?_, fun x hx v w ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨hxc, hxκ⟩ := (hsrc x).1 hx
    rw [← hlinv x hxc]
    exact interior_subset (hκT hxκ).2
  · rw [hd x hx, hd x hx, hκσ _ ((hsrc x).1 hx).2, hc x ((hsrc x).1 hx).1]
  · obtain ⟨hxc, hxκ⟩ := (hsrc x).1 hx
    have h := hκg (c x) hxκ
    simp only [g, hlinv x hxc, hcs0] at h
    rw [h, hcoe]

/-- **The Carathéodory–Jacobi–Lie normal form in standard Darboux coordinates at an interior
point.** Let `f` be smooth near an interior point `x₀` of a finite-dimensional symplectic manifold
`(M, form)`, with nonzero differential at `x₀`. Then there are standard Euclidean Darboux
coordinates `(q, p)` around `x₀`, pulling `stdSymplecticForm` back to `form`, in which `f` is
`f x₀` plus the first momentum coordinate: `f = f x₀ + p₁`. -/
theorem IsSymplectic.exists_standardDarbouxChart_eq_add_snd_of_isInteriorPoint
    {form : SmoothTwoForm I M} (hform : form.IsSymplectic) {f : M → ℝ} {U : Set M} {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) (hU : U ∈ 𝓝 x₀) (hf : ContMDiffOn I 𝓘(ℝ) ∞ f U)
    (hdf : mvfderiv I f x₀ ≠ 0) :
    ∃ (m : ℕ) (chart : PartialDiffeomorph I
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (m + 1))) M
      (EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (m + 1))) ∞),
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧ chart.source ⊆ U ∧
      (∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w = stdSymplecticForm (mvfderiv I chart x v) (mvfderiv I chart x w)) ∧
      ∀ x ∈ chart.source, f x = f x₀ + (chart x).2 0 := by
  obtain ⟨c, form₀, ℓ, hℓ, hx₀c, hc0, hcU, hc, hfc⟩ :=
    hform.exists_darbouxChart_eq_add_of_isInteriorPoint hx₀ hU hf hdf
  -- A Darboux basis whose first `q`-vector is the Hamiltonian vector field `X_ℓ` of `ℓ`.
  have hXℓ : form₀.hamiltonianVectorField ℓ 0 ≠ 0 := by
    rwa [Ne, form₀.hamiltonianVectorField_eq_zero_iff, ℓ.fderiv]
  obtain ⟨m, L, hL, hLX⟩ :=
    form₀.exists_continuousLinearEquiv_stdSymplecticForm_apply_eq_fst_single hXℓ
  obtain ⟨hx₀', h0', -, hpull⟩ := trans_toDiffeomorph_darboux hx₀c hc0 hc L hL
  have hsrc : (c.trans L.toDiffeomorph.toPartialDiffeomorph).source = c.source := by simp
  refine ⟨m, _, hx₀', h0', hsrc ▸ hcU, hpull, fun x hx ↦ ?_⟩
  -- `ℓ = form₀ (X_ℓ, ·)`, which `L` carries to `stdSymplecticForm ((single 0 1, 0), ·)`.
  have hℓL (z : E) : ℓ z = (L z).2 0 := by
    rw [← ℓ.fderiv (x := 0), ← form₀.apply_hamiltonianVectorField, ← hL.apply,
      ContinuousLinearEquiv.coe_toLinearEquiv, hLX]
    simp [EuclideanSpace.inner_single_left]
  rw [hfc x (hsrc ▸ hx), hℓL]
  simp

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

/-- **The Carathéodory–Jacobi–Lie normal form for one function.** Let `f` be smooth near a point
`x₀` of a finite-dimensional boundaryless symplectic manifold `(M, form)`, with nonzero
differential at `x₀`. Then some Darboux chart around `x₀`, pulling a constant symplectic form
`form₀` on the model space back to `form`, makes `f` affine: `f = f x₀ + ℓ ∘ chart` for a nonzero
linear functional `ℓ`. -/
theorem IsSymplectic.exists_darbouxChart_eq_add {form : SmoothTwoForm I M}
    (hform : form.IsSymplectic) {f : M → ℝ} {U : Set M} {x₀ : M} (hU : U ∈ 𝓝 x₀)
    (hf : ContMDiffOn I 𝓘(ℝ) ∞ f U) (hdf : mvfderiv I f x₀ ≠ 0) :
    ∃ (chart : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (form₀ : SymplecticForm E) (ℓ : E →L[ℝ] ℝ),
      ℓ ≠ 0 ∧ x₀ ∈ chart.source ∧ chart x₀ = 0 ∧ chart.source ⊆ U ∧
      (∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w = form₀ (mvfderiv I chart x v) (mvfderiv I chart x w)) ∧
      ∀ x ∈ chart.source, f x = f x₀ + ℓ (chart x) :=
  hform.exists_darbouxChart_eq_add_of_isInteriorPoint BoundarylessManifold.isInteriorPoint hU hf
    hdf

/-- **The Carathéodory–Jacobi–Lie normal form in standard Darboux coordinates.** Let `f` be smooth
near a point `x₀` of a finite-dimensional boundaryless symplectic manifold `(M, form)`, with
nonzero differential at `x₀`. Then there are standard Euclidean Darboux coordinates `(q, p)` around
`x₀` in which `f = f x₀ + p₁`. -/
theorem IsSymplectic.exists_standardDarbouxChart_eq_add_snd
    {form : SmoothTwoForm I M} (hform : form.IsSymplectic) {f : M → ℝ} {U : Set M} {x₀ : M}
    (hU : U ∈ 𝓝 x₀) (hf : ContMDiffOn I 𝓘(ℝ) ∞ f U) (hdf : mvfderiv I f x₀ ≠ 0) :
    ∃ (m : ℕ) (chart : PartialDiffeomorph I
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (m + 1))) M
      (EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (m + 1))) ∞),
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧ chart.source ⊆ U ∧
      (∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w = stdSymplecticForm (mvfderiv I chart x v) (mvfderiv I chart x w)) ∧
      ∀ x ∈ chart.source, f x = f x₀ + (chart x).2 0 :=
  hform.exists_standardDarbouxChart_eq_add_snd_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint hU hf hdf

end Boundaryless

end Darboux

end SmoothTwoForm

end TauCeti

end
