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
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
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
applies the centred flat Moser–Darboux theorem
`TauCeti.exists_diffeomorph_centered_forall_mem_eq_compContinuousLinearMap_fderiv`, composes its
diffeomorphism with the extended chart restricted to an open set
(`TauCeti.exists_partialDiffeomorph_comp_extChartAt`), and transports the constant model form along
continuous linear symplectomorphisms.

Only closedness of `form` and its nondegeneracy at `x₀` enter the proof, so the same chart exists
for a closed two-form that is nondegenerate at `x₀` alone
(`TauCeti.SmoothTwoForm.exists_darbouxChart_of_nondegenerate_of_isInteriorPoint`); it is then
nondegenerate on the whole source of the chart. Such forms arise as restrictions of a closed
two-form to a slice, for example the restriction of `dα` to a hypersurface transverse to the Reeb
field of a contact form `α`. Conversely, a two-form pulled back from a constant symplectic form by a
chart into any normed space is nondegenerate on the source of the chart, since the differential of
the chart is bijective there (`TauCeti.SmoothTwoForm.nondegenerate_bilinFormAt_of_darbouxChart`).
So for a closed two-form, a Darboux chart centred at an interior point `x₀` exists exactly when the
form is nondegenerate at `x₀`
(`TauCeti.SmoothTwoForm.exists_darbouxChart_iff_nondegenerate_of_isInteriorPoint`).

## Main declarations

* `TauCeti.SmoothTwoForm.exists_darbouxChart_of_nondegenerate_of_isInteriorPoint`: Darboux
  charts into the model space for a closed two-form nondegenerate at `x₀`.
* `TauCeti.SmoothTwoForm.nondegenerate_bilinFormAt_of_darbouxChart`: a two-form admitting a
  Darboux chart is nondegenerate on its source.
* `TauCeti.SmoothTwoForm.exists_darbouxChart_iff_nondegenerate_of_isInteriorPoint`: a closed
  two-form has a Darboux chart at an interior point exactly when it is nondegenerate there.
* `SmoothTwoForm.exists_standardDarbouxChart_of_nondegenerate_of_finrank_eq_of_isInteriorPoint`:
  standard Euclidean Darboux charts for a closed two-form nondegenerate at `x₀`.
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
* `TauCeti.SmoothTwoForm.eval₂_mfderiv_eq_of_darbouxChart`: a diffeomorphism of `M` which reads,
  in a Darboux chart, as a form-preserving diffeomorphism of the model space, and is the identity
  near every point outside the chart, preserves the symplectic form.

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

end Helpers

section Transport

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Transporting a form-preserving diffeomorphism through a Darboux chart.** Let `κ` be a Darboux
chart pulling the constant form `ω₀` on `E` back to `σ`, and `ψ` a diffeomorphism of `E` preserving
`ω₀` and mapping the target of `κ` into itself. A diffeomorphism `Φ` of `M` which is
`κ⁻¹ ∘ ψ ∘ κ` on the source of `κ`, and the identity near every point outside the source, preserves
`σ`. -/
theorem eval₂_mfderiv_eq_of_darbouxChart {σ : SmoothTwoForm I M}
    {κ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞} {ω₀ : SymplecticForm E}
    (hκσ : ∀ x ∈ κ.source, ∀ v w : TangentSpace I x,
      σ.eval₂ x v w = ω₀ (mvfderiv I κ x v) (mvfderiv I κ x w))
    {ψ : E ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E}
    (hψσ : ∀ y u v, ω₀ (fderiv ℝ ψ y u) (fderiv ℝ ψ y v) = ω₀ u v)
    (hψt : ∀ y ∈ κ.target, ψ y ∈ κ.target) {Φ : M ≃ₘ⟮I, I⟯ M}
    (hΦs : ∀ x ∈ κ.source, Φ x = κ.symm (ψ (κ x)))
    (hΦid : ∀ x ∉ κ.source, ⇑Φ =ᶠ[𝓝 x] id) (x : M) (v w : TangentSpace I x) :
    σ.eval₂ (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) = σ.eval₂ x v w := by
  by_cases hx : x ∈ κ.source
  · have hκx : κ x ∈ κ.target := κ.toPartialEquiv.map_source hx
    have hΦx : Φ x ∈ κ.source := by
      rw [hΦs x hx]
      exact κ.toPartialEquiv.map_target (hψt _ hκx)
    -- Read in the chart, `Φ` is `ψ`: `κ ∘ Φ = ψ ∘ κ` near `x`.
    have hcomp : κ ∘ Φ =ᶠ[𝓝 x] ψ ∘ κ := eventually_of_mem (κ.open_source.mem_nhds hx)
      fun z hz ↦ by
        rw [Function.comp_apply, hΦs z hz]
        exact κ.toPartialEquiv.right_inv (hψt _ (κ.toPartialEquiv.map_source hz))
    have h₁ : HasMFDerivAt I 𝓘(ℝ, E) (κ ∘ Φ) x
        ((mfderiv I 𝓘(ℝ, E) κ (Φ x)).comp (mfderiv I I Φ x)) :=
      (κ.mdifferentiableAt (by simp) hΦx).hasMFDerivAt.comp x
        ((Φ.contMDiff.mdifferentiable (by simp)) x).hasMFDerivAt
    have h₂ : HasMFDerivAt I 𝓘(ℝ, E) (ψ ∘ κ) x
        ((fderiv ℝ ψ (κ x)).comp (mfderiv I 𝓘(ℝ, E) κ x)) :=
      (hasMFDerivAt_iff_hasFDerivAt.2 (((contMDiff_iff_contDiff.1 ψ.contMDiff).differentiable
        (by simp)) (κ x)).hasFDerivAt).comp x (κ.mdifferentiableAt (by simp) hx).hasMFDerivAt
    have h₃ (u : TangentSpace I x) :
        mvfderiv I κ (Φ x) (mfderiv I I Φ x u) = fderiv ℝ ψ (κ x) (mvfderiv I κ x u) :=
      congrArg (· u) ((h₁.congr_of_eventuallyEq hcomp.symm).mfderiv.symm.trans h₂.mfderiv)
    rw [hκσ _ hΦx, hκσ _ hx, h₃, h₃, hψσ]
  · have hD : mfderiv I I Φ x = ContinuousLinearMap.id ℝ (TangentSpace I x) :=
      ((hasMFDerivAt_id x).congr_of_eventuallyEq (hΦid x hx)).mfderiv
    simp only [hD]
    rw [(hΦid x hx).eq_of_nhds, id_eq, ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply]

end Transport

section Converse

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **A Darboux chart forces nondegeneracy.** If a `C^n` partial diffeomorphism `chart` into a
normed space `F`, with `n ≠ 0`, pulls a symplectic form `form₀` on `F` back to `form` on its
source, then `form` is nondegenerate at every point of the source. So a two-form that degenerates
at `x` admits no Darboux chart around `x`, whether into the model space or into any other normed
space such as the standard Euclidean model. -/
theorem nondegenerate_bilinFormAt_of_darbouxChart {form : SmoothTwoForm I M} {n : WithTop ℕ∞}
    (hn : n ≠ 0) {chart : PartialDiffeomorph I 𝓘(ℝ, F) M F n} {form₀ : SymplecticForm F}
    (hchart : ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
      form.eval₂ x v w = form₀ (mvfderiv I chart x v) (mvfderiv I chart x w))
    {x : M} (hx : x ∈ chart.source) : (form.bilinFormAt x).Nondegenerate := by
  -- On the source the differential of the chart is bijective, so it carries the null space of
  -- `form` at `x` into the null space of the nondegenerate form `form₀`.
  have hD := chart.bijective_mvfderiv hn hx
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (SmoothForm.isAlt_bilinFormAt form x).isRefl).2 fun v hv ↦ hD.1 ?_
  rw [map_zero]
  refine form₀.nondegenerate.1 _ fun u ↦ ?_
  obtain ⟨w, rfl⟩ := hD.2 u
  have h := hchart x hx v w
  rw [← SmoothForm.bilinFormAt_apply, hv w] at h
  exact h.symm

end Converse

section Darboux

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Darboux's theorem at an interior point, for a closed two-form nondegenerate there.** Let
`form` be a closed smooth two-form on `M` which is nondegenerate at an interior point `x₀`. Then
there are a smooth partial diffeomorphism `chart` into the model space `E` with `x₀ ∈ chart.source`
and `chart x₀ = 0` and a constant symplectic form `form₀` on `E` whose pullback by
`mvfderiv I chart` equals `form` on `chart.source`. In particular `form` is nondegenerate on
`chart.source`. -/
theorem exists_darbouxChart_of_nondegenerate_of_isInteriorPoint
    {form : SmoothTwoForm I M} (hcl : form.IsClosed) {x₀ : M}
    (hnd₀ : (form.bilinFormAt x₀).Nondegenerate) (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (chart : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (form₀ : SymplecticForm E),
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w = form₀ (mvfderiv I chart x v) (mvfderiv I chart x w) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  let η : E → E [⋀^Fin 2]→L[ℝ] ℝ := RoughForm.inChartAt form.val x₀
  let W : Set E := interior (extChartAt I x₀).target
  let y₀ : E := extChartAt I x₀ x₀
  have hy₀W : y₀ ∈ W := (ModelWithCorners.isInteriorPoint_iff (I := I)).mp hx₀
  have hηy₀ : η y₀ = form.val x₀ := RoughForm.inChartAt_extChartAt_self form.val x₀
  -- `TangentSpace I x₀` carries the model vector-space structure of `E`.
  let form₀ : SymplecticForm E :=
    { toBilinForm := form.bilinFormAt x₀
      isAlt := SmoothForm.isAlt_bilinFormAt form x₀
      nondegenerate := hnd₀ }
  have hform₀_apply (u w : E) : form₀ u w = η y₀ ![u, w] := by
    let u' : TangentSpace I x₀ := u
    let w' : TangentSpace I x₀ := w
    exact (SmoothForm.bilinFormAt_apply form x₀ u' w').trans
      ((SmoothBundleForm.eval₂_apply form x₀ u' w').trans
        (congrArg (fun A : E [⋀^Fin 2]→L[ℝ] ℝ ↦ A ![u, w]) hηy₀.symm))
  have hnd : ∀ v : E, (∀ w : E, η y₀ ![v, w] = 0) → v = 0 :=
    form.inChartAt_extChartAt_self_nondegenerate hnd₀
  -- Apply the flat Moser–Darboux theorem to `η` on `W` around `y₀`.
  obtain ⟨Φ_flat, V₀, hΦy₀, hV₀_open, hy₀V₀, hV₀_sub, hη_inv⟩ :=
    exists_diffeomorph_centered_forall_mem_eq_compContinuousLinearMap_fderiv (r := (⊤ : ℕ∞))
      le_top isOpen_interior hy₀W (form.isSmoothForm.contDiffOn_inChartAt_interior_target x₀)
      (fun z hz ↦ hcl.extDeriv_inChartAt_eq_zero x₀ hz) hnd
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
  rw [SmoothBundleForm.eval₂_apply, RoughForm.apply_eq_inChartAt_mvfderiv form.val hxS.1, hvec,
    hmvf x hx v, hmvf x hx w]
  rw [hform₀_apply, hη_inv (extChartAt I x₀ x) hxS.2]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- **Darboux charts exist exactly at nondegenerate points.** A closed two-form has a Darboux chart
centred at an interior point `x₀`, pulling a constant symplectic form on the model space `E` back
to it, if and only if it is nondegenerate at `x₀`. -/
theorem exists_darbouxChart_iff_nondegenerate_of_isInteriorPoint
    {form : SmoothTwoForm I M} (hcl : form.IsClosed) {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    (∃ (chart : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (form₀ : SymplecticForm E),
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w = form₀ (mvfderiv I chart x v) (mvfderiv I chart x w)) ↔
      (form.bilinFormAt x₀).Nondegenerate :=
  ⟨fun ⟨_, _, hx₀s, _, hchart⟩ ↦ nondegenerate_bilinFormAt_of_darbouxChart (by simp) hchart hx₀s,
    fun hnd ↦ exists_darbouxChart_of_nondegenerate_of_isInteriorPoint hcl hnd hx₀⟩

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
        form.eval₂ x v w = form₀ (mvfderiv I chart x v) (mvfderiv I chart x w) :=
  exists_darbouxChart_of_nondegenerate_of_isInteriorPoint hform.isClosed
    (hform.isNondegenerate.nondegenerate_bilinFormAt x₀) hx₀

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

/-- **Standard Euclidean Darboux coordinates at fixed dimension `2 * n`, for a closed two-form
nondegenerate at an interior point.** -/
theorem exists_standardDarbouxChart_of_nondegenerate_of_finrank_eq_of_isInteriorPoint
    {form : SmoothTwoForm I M} (hcl : form.IsClosed) {n : ℕ}
    (hn : Module.finrank ℝ E = 2 * n) {x₀ : M} (hnd₀ : (form.bilinFormAt x₀).Nondegenerate)
    (hx₀ : I.IsInteriorPoint x₀) :
    ∃ chart : PartialDiffeomorph I
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) M
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∞,
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w =
          stdSymplecticForm (mvfderiv I chart x v) (mvfderiv I chart x w) := by
  obtain ⟨chart₁, ω₁, hx₀₁, h0₁, hchart₁⟩ :=
    exists_darbouxChart_of_nondegenerate_of_isInteriorPoint hcl hnd₀ hx₀
  obtain ⟨L, hL⟩ := ω₁.exists_continuousLinearEquiv_stdSymplecticForm_of_finrank_eq hn
  obtain ⟨hx₀', h0', -, hpull⟩ := trans_toDiffeomorph_darboux hx₀₁ h0₁ hchart₁ L hL
  exact ⟨_, hx₀', h0', hpull⟩

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
          stdSymplecticForm (mvfderiv I chart x v) (mvfderiv I chart x w) :=
  exists_standardDarbouxChart_of_nondegenerate_of_finrank_eq_of_isInteriorPoint hform.isClosed hn
    (hform.isNondegenerate.nondegenerate_bilinFormAt x₀) hx₀

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
