/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import TauCeti.Analysis.Calculus.SecondDerivative
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Mixed derivatives of a parametric map

For a map `F : P × E → F'` with the minimum smoothness needed for symmetric second derivatives,
differentiating its spatial Jacobian in a parameter direction at `p₀` is the spatial derivative
of its velocity in that direction at `p₀`. This is the mixed-partial identity needed to identify the
derivative of a parametric-family pullback with a Lie bracket. Over `ℝ` or `ℂ`, the required
smoothness is `C²`;
over a general nontrivially normed field, it is analyticity.

This supplies a prerequisite for Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main definitions

* `spatialFDeriv`: the spatial Jacobian of a parametric map.
* `timeFDeriv`: the parameter velocity at a specified parameter value.

## Main results

* `hasDerivAt_parameterCurve`: the parameter velocity differentiates the corresponding parameter
  curve.
* `hasFDerivAt_timeSlice`: the spatial Jacobian differentiates the corresponding fixed-parameter
  slice.
* `fderiv_timeSlice`: the derivative of a fixed-parameter slice is its spatial Jacobian.
* `TauCeti.hasDerivAt_comp_prodMk`: the chain rule along a curve `s ↦ F (s, γ s)`.
* `ContDiffAt.deriv_parameterCurve_eventuallyEq_timeFDeriv`: near a point, the derivatives of the
  parameter curves are the parameter-velocity field.
* `ContDiffAt.differentiableAt_timeFDeriv`: the parameter-velocity field of a jointly `C²` map is
  differentiable.
* `TauCeti.hasFDerivAt_fderivWithin_slice`: mixed derivatives for a normed parameter space, with
  spatial derivatives within a set accumulated by its interior, such as the range of a model with
  corners.
* `TauCeti.hasFDerivAt_spatialFDeriv`: mixed derivatives for a normed parameter space.
* `hasDerivAt_spatialFDeriv`: the spatial Jacobian differentiates to the spatial derivative of the
  parameter velocity.
* `TauCeti.hasDerivAt_fderivWithin_slice`: the case of a scalar parameter of mixed derivatives
  within a set.
* `deriv_spatialFDeriv_apply`: the parameter derivative of the spatial Jacobian equals the
  derivative of the parameter-velocity field.
* `deriv_deriv_comm`: for a map of two scalar variables, the two iterated partial derivatives
  agree.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The infinitesimal adjoint".
* Sébastien Gouëzel, `Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`, theorem
  `ContDiffAt.isSymmSndFDerivAt`.
-/

public section

noncomputable section

open Filter ContinuousLinearMap
open scoped Topology

variable {𝕜 E F' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- Applying a differentiable family of continuous linear maps to a constant vector. -/
private theorem HasDerivAt.clm_apply_const {t : 𝕜} {c : 𝕜 → E →L[𝕜] F'}
    {c' : E →L[𝕜] F'} (hc : HasDerivAt c c' t) (u : E) :
    HasDerivAt (fun s => c s u) (c' u) t := by
  simpa only [map_zero, add_zero] using hc.clm_apply (hasDerivAt_const t u)

section

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Applying a differentiable family of continuous linear maps to a constant vector. -/
private theorem HasFDerivAt.clm_apply_const {c : E → F' →L[𝕜] G}
    {c' : E →L[𝕜] F' →L[𝕜] G} {x : E} (hc : HasFDerivAt c c' x) (u : F') :
    HasFDerivAt (fun y => c y u) (c'.flip u) x := by
  simpa only [ContinuousLinearMap.comp_zero, zero_add] using
    hc.clm_apply (hasFDerivAt_const (x := x) u)

end

/-- The spatial Jacobian of a parametric map at `x`, as a function of the parameter. If `F` is not
differentiable at `(t, x)`, its value at `t` is the junk value `0`. -/
def spatialFDeriv (F : 𝕜 × E → F') (x : E) (t : 𝕜) : E →L[𝕜] F' :=
  (fderiv 𝕜 F (t, x)).comp (ContinuousLinearMap.inr 𝕜 𝕜 E)

/-- The spatial derivative as the restriction of the full derivative to the spatial factor. -/
theorem spatialFDeriv_def (F : 𝕜 × E → F') (x : E) (t : 𝕜) :
    spatialFDeriv F x t =
      (fderiv 𝕜 F (t, x)).comp (ContinuousLinearMap.inr 𝕜 𝕜 E) :=
  (rfl)

/-- The spatial derivative, as a function of the parameter. -/
theorem spatialFDeriv_eq (F : 𝕜 × E → F') (x : E) :
    spatialFDeriv F x = fun t =>
      (fderiv 𝕜 F (t, x)).comp (ContinuousLinearMap.inr 𝕜 𝕜 E) :=
  (rfl)

@[simp]
theorem spatialFDeriv_apply (F : 𝕜 × E → F') (x : E) (t : 𝕜) (w : E) :
    spatialFDeriv F x t w = fderiv 𝕜 F (t, x) (0, w) :=
  (rfl)

/-- The parameter velocity of a parametric map at `(t, x)`. If `F` is not differentiable there,
this is the junk value `0`. -/
def timeFDeriv (F : 𝕜 × E → F') (t : 𝕜) (x : E) : F' :=
  fderiv 𝕜 F (t, x) (1, 0)

@[simp]
theorem timeFDeriv_apply (F : 𝕜 × E → F') (t : 𝕜) (x : E) :
    timeFDeriv F t x = fderiv 𝕜 F (t, x) (1, 0) :=
  (rfl)

/-- The parameter velocity, as a function of the spatial variable. -/
theorem timeFDeriv_eq (F : 𝕜 × E → F') (t : 𝕜) :
    timeFDeriv F t = fun x => fderiv 𝕜 F (t, x) (1, 0) :=
  (rfl)

/-- The parameter velocity is the derivative of the parameter curve `fun s ↦ F (s, x)`. -/
theorem hasDerivAt_parameterCurve {F : 𝕜 × E → F'} {t : 𝕜} {x : E}
    (hF : DifferentiableAt 𝕜 F (t, x)) :
    HasDerivAt (fun s => F (s, x)) (timeFDeriv F t x) t := by
  simpa only [timeFDeriv_apply, Function.comp_def, ContinuousLinearMap.inl_apply] using
    hF.hasFDerivAt.comp_hasDerivAt t (hasFDerivAt_prodMk_left t x).hasDerivAt

/-- The spatial Jacobian is the derivative of the fixed-parameter slice `fun y ↦ F (t, y)`. -/
theorem hasFDerivAt_timeSlice {F : 𝕜 × E → F'} {t : 𝕜} {x : E}
    (hF : DifferentiableAt 𝕜 F (t, x)) :
    HasFDerivAt (fun y => F (t, y)) (spatialFDeriv F x t) x := by
  rw [spatialFDeriv_def]
  exact hF.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)

/-- The derivative of the fixed-parameter slice `fun y ↦ F (t, y)` is its spatial Jacobian. -/
theorem fderiv_timeSlice {F : 𝕜 × E → F'} {t : 𝕜} {x : E}
    (hF : DifferentiableAt 𝕜 F (t, x)) :
    fderiv 𝕜 (fun y => F (t, y)) x = spatialFDeriv F x t :=
  TauCeti.fderiv_slice_right hF

namespace TauCeti

/-- **The chain rule along a curve.** If `F` is differentiable at `(t, γ t)` and `γ` has velocity
`v` at `t`, then `s ↦ F (s, γ s)` has derivative the parameter velocity of `F` plus its spatial
Jacobian applied to `v`. -/
theorem hasDerivAt_comp_prodMk {F : 𝕜 × E → F'} {γ : 𝕜 → E} {v : E} {t : 𝕜}
    (hF : DifferentiableAt 𝕜 F (t, γ t)) (hγ : HasDerivAt γ v t) :
    HasDerivAt (fun s ↦ F (s, γ s)) (timeFDeriv F t (γ t) + spatialFDeriv F (γ t) t v) t := by
  refine (hF.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hγ)).congr_deriv ?_
  rw [timeFDeriv_apply, spatialFDeriv_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]

/-- **Mixed derivatives within a set.** Let `F : P × E → F'`, with `P` a normed parameter space, be
sufficiently smooth within `univ ×ˢ s` at `(p, x)`, where `s` has unique derivatives and `x ∈ s` is
accumulated by the interior of `s`. Then differentiating in the parameter the spatial derivative
within `s` of the slices `y ↦ F (q, y)` gives the spatial derivative within `s` of the parameter
derivative at `p`.

Over `ℝ` or `ℂ` the required smoothness is `C²`. The set `s` is typically the range of a model with
corners, so that this computes mixed derivatives of maps read in charts of manifolds with
boundary. -/
theorem hasFDerivAt_fderivWithin_slice {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    {F : P × E → F'} {s : Set E} {p : P} {x : E}
    (hF : ContDiffWithinAt 𝕜 (minSmoothness 𝕜 2) F (Set.univ ×ˢ s) (p, x))
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ closure (interior s)) (h'x : x ∈ s) :
    HasFDerivAt (fun q ↦ fderivWithin 𝕜 (fun y ↦ F (q, y)) s x)
      (fderivWithin 𝕜 (fun y ↦ fderiv 𝕜 (fun q ↦ F (q, y)) p) s x).flip p := by
  set S : Set (P × E) := Set.univ ×ˢ s
  have hS : UniqueDiffOn 𝕜 S := UniqueDiffOn.prod uniqueDiffOn_univ hs
  have hpx : (p, x) ∈ S := ⟨Set.mem_univ p, h'x⟩
  have hpx' : (p, x) ∈ closure (interior S) := by
    simp only [S, interior_prod_eq, interior_univ, closure_prod_eq, closure_univ]
    exact ⟨Set.mem_univ p, hx⟩
  -- `D` is the derivative of `F` within `S`; it is differentiable within `S` at `(p, x)`, with
  -- symmetric derivative.
  set D := fderivWithin 𝕜 F S
  have h2 : (1 : WithTop ℕ∞) + 1 ≤ minSmoothness 𝕜 2 :=
    le_trans (by norm_num) le_minSmoothness
  obtain ⟨u, hu, hxu, hFu⟩ := hF.contDiffOn' (m := 1 + 1) h2 (by simp)
  rw [Set.insert_eq_of_mem hpx] at hFu
  have hdiff : ∀ z ∈ S ∩ u, HasFDerivWithinAt F (D z) S z := fun z hz ↦
    (((hFu.differentiableOn (by simp)) z hz).mono_of_mem_nhdsWithin
      (inter_mem_nhdsWithin S (hu.mem_nhds hz.2))).hasFDerivWithinAt
  have hD : HasFDerivWithinAt D (fderivWithin 𝕜 D S (p, x)) S (p, x) :=
    ((hF.fderivWithin_right (m := 1) hS h2 hpx).differentiableWithinAt
      one_ne_zero).hasFDerivWithinAt
  have hsymm := hF.isSymmSndFDerivWithinAt le_rfl hS hpx' hpx
  -- Near `p`, the spatial derivative of the slice through `(q, x)` is read off from `D (q, x)`.
  have hslice : (fun q ↦ fderivWithin 𝕜 (fun y ↦ F (q, y)) s x) =ᶠ[𝓝 p]
      fun q ↦ (D (q, x)).comp (inr 𝕜 P E) := by
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (hu.mem_nhds hxu)] with q hq
    exact ((hdiff (q, x) ⟨⟨Set.mem_univ q, h'x⟩, hq⟩).comp x
      (hasFDerivAt_prodMk_right q x).hasFDerivWithinAt
      (fun y hy ↦ ⟨Set.mem_univ q, hy⟩)).fderivWithin (hs x h'x)
  have hleft : HasFDerivAt (fun q ↦ (D (q, x)).comp (inr 𝕜 P E))
      (((compL 𝕜 E (P × E) F').flip (inr 𝕜 P E)).comp
        ((fderivWithin 𝕜 D S (p, x)).comp (inl 𝕜 P E))) p :=
    ((compL 𝕜 E (P × E) F').flip (inr 𝕜 P E)).hasFDerivAt.comp p
      (hasFDerivWithinAt_univ.mp (hD.comp p (hasFDerivAt_prodMk_left p x).hasFDerivWithinAt
        (fun q _ ↦ Set.mk_mem_prod (Set.mem_univ q) h'x)))
  -- Near `x` in `s`, the parameter derivative at `p` is read off from `D (p, y)`.
  have hvel : (fun y ↦ fderiv 𝕜 (fun q ↦ F (q, y)) p) =ᶠ[𝓝[s] x]
      fun y ↦ (D (p, y)).comp (inl 𝕜 P E) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
      ((continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
        (hu.mem_nhds hxu))] with y hy hyu
    exact (hasFDerivWithinAt_univ.mp ((hdiff (p, y) ⟨⟨Set.mem_univ p, hy⟩, hyu⟩).comp p
      (hasFDerivAt_prodMk_left p y).hasFDerivWithinAt
        (fun q _ ↦ Set.mk_mem_prod (Set.mem_univ q) hy))).fderiv
  have hright : HasFDerivWithinAt (fun y ↦ (D (p, y)).comp (inl 𝕜 P E))
      (((compL 𝕜 P (P × E) F').flip (inl 𝕜 P E)).comp
        ((fderivWithin 𝕜 D S (p, x)).comp (inr 𝕜 P E))) s x :=
    ((compL 𝕜 P (P × E) F').flip (inl 𝕜 P E)).hasFDerivAt.comp_hasFDerivWithinAt x
      (hD.comp x (hasFDerivAt_prodMk_right p x).hasFDerivWithinAt fun _ hy ↦
        ⟨Set.mem_univ p, hy⟩)
  rw [hvel.fderivWithin_eq (mem_of_mem_nhdsWithin h'x hvel), hright.fderivWithin (hs x h'x)]
  refine (hleft.congr_of_eventuallyEq hslice).congr_fderiv ?_
  ext h w
  simpa using hsymm (h, 0) (0, w)

/-- For a jointly sufficiently smooth map with a normed parameter space, differentiating the
spatial derivative in the parameter is the spatial derivative of the parameter derivative.
The derivative in each argument is taken with the other argument fixed. -/
theorem hasFDerivAt_spatialFDeriv {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    {F : P × E → F'} {p : P} {x : E}
    (hF : ContDiffAt 𝕜 (minSmoothness 𝕜 2) F (p, x)) :
    HasFDerivAt (fun q ↦ fderiv 𝕜 (fun y ↦ F (q, y)) x)
      (fderiv 𝕜 (fun y ↦ fderiv 𝕜 (fun q ↦ F (q, y)) p) x).flip p := by
  have h := hasFDerivAt_fderivWithin_slice (𝕜 := 𝕜) (F := F) (s := Set.univ) (p := p) (x := x)
    (by rwa [Set.univ_prod_univ, contDiffWithinAt_univ]) uniqueDiffOn_univ (by simp)
    (Set.mem_univ x)
  simpa only [fderivWithin_univ] using h

/-- **Mixed derivatives within a set, scalar parameter.** The case `P = 𝕜` of
`hasFDerivAt_fderivWithin_slice`, with the parameter derivative written as `deriv`. -/
theorem hasDerivAt_fderivWithin_slice {F : 𝕜 × E → F'} {s : Set E} {t : 𝕜} {x : E}
    (hF : ContDiffWithinAt 𝕜 (minSmoothness 𝕜 2) F (Set.univ ×ˢ s) (t, x))
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ closure (interior s)) (h'x : x ∈ s) :
    HasDerivAt (fun r ↦ fderivWithin 𝕜 (fun y ↦ F (r, y)) s x)
      (fderivWithin 𝕜 (fun y ↦ _root_.deriv (fun r ↦ F (r, y)) t) s x) t := by
  refine (hasFDerivAt_fderivWithin_slice hF hs hx h'x).hasDerivAt.congr_deriv ?_
  -- The parameter derivatives `y ↦ ∂ᵣ F (r, y)` at `t` vary differentiably with `y` in `s`.
  have hswap : ContDiffWithinAt 𝕜 (minSmoothness 𝕜 2) (Function.uncurry fun y r ↦ F (r, y))
      (s ×ˢ Set.univ) (x, t) :=
    hF.comp (x, t) (contDiffWithinAt_snd.prodMk contDiffWithinAt_fst)
      fun z hz ↦ Set.mk_mem_prod (Set.mem_univ z.2) hz.1
  have hdiff : DifferentiableWithinAt 𝕜 (fun y ↦ fderiv 𝕜 (fun r ↦ F (r, y)) t) s x := by
    simpa only [fderivWithin_univ] using
      ((hswap.fderivWithin (m := 1) contDiffWithinAt_const uniqueDiffOn_univ
        (le_trans (by norm_num) le_minSmoothness) h'x (fun _ _ ↦ Set.mem_univ _)
        ).differentiableWithinAt one_ne_zero)
  simp only [← fderiv_apply_one_eq_deriv]
  rw [fderivWithin_clm_apply (hs x h'x) hdiff (differentiableWithinAt_const _)]
  simp

end TauCeti

namespace ContDiffAt

/-- Near `x`, the derivative of each parameter curve is the parameter-velocity field. -/
theorem deriv_parameterCurve_eventuallyEq_timeFDeriv {F : 𝕜 × E → F'} {t : 𝕜} {x : E}
    (hF : ContDiffAt 𝕜 1 F (t, x)) :
    (fun y ↦ _root_.deriv (fun s ↦ F (s, y)) t) =ᶠ[nhds x] timeFDeriv F t := by
  obtain ⟨w, hw, hFw⟩ := hF.contDiffOn (m := 1) le_rfl (by simp)
  have hdiff : ∀ᶠ z in nhds ((t, x) : 𝕜 × E), DifferentiableAt 𝕜 F z :=
    (hFw.differentiableOn one_ne_zero).eventually_differentiableAt hw
  have hsnd : ∀ᶠ y in nhds x, DifferentiableAt 𝕜 F (t, y) :=
    (continuous_const.prodMk continuous_id).continuousAt.eventually hdiff
  filter_upwards [hsnd] with y hy
  exact (hasDerivAt_parameterCurve hy).deriv

/-- For a jointly `C²` parametric map, the parameter-velocity field is differentiable in the
spatial variable. -/
theorem differentiableAt_timeFDeriv {F : 𝕜 × E → F'} {t : 𝕜} {x : E}
    (hF : ContDiffAt 𝕜 2 F (t, x)) : DifferentiableAt 𝕜 (timeFDeriv F t) x := by
  rw [timeFDeriv_eq]
  exact ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).comp x
    (differentiableAt_const t |>.prodMk differentiableAt_id) |>.clm_apply
      (differentiableAt_const (1, 0))

end ContDiffAt

/-- At `t`, the spatial Jacobian has derivative the spatial derivative of the parameter velocity. -/
theorem hasDerivAt_spatialFDeriv {F : 𝕜 × E → F'} {t : 𝕜} {x : E}
    (hF : ContDiffAt 𝕜 (minSmoothness 𝕜 2) F (t, x)) :
    HasDerivAt (spatialFDeriv F x) (fderiv 𝕜 (timeFDeriv F t) x) t := by
  have hSlice := (TauCeti.hasFDerivAt_spatialFDeriv hF).hasDerivAt
  have hswap : ContDiffAt 𝕜 (minSmoothness 𝕜 2)
      (Function.uncurry (fun y s ↦ F (s, y))) (x, t) :=
    hF.comp (x, t) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hParameter := (hswap.fderiv (m := 1) contDiffAt_const
    (le_trans (by norm_num) le_minSmoothness)).differentiableAt one_ne_zero
  have hcurve := (hF.of_le (le_trans (by norm_num) le_minSmoothness))
    |>.deriv_parameterCurve_eventuallyEq_timeFDeriv
  have hTime := (hParameter.hasFDerivAt.clm_apply_const 1).congr_of_eventuallyEq
    (f₁ := timeFDeriv F t) (by
      simpa only [← fderiv_apply_one_eq_deriv] using
        hcurve.symm)
  have hnear : ∀ᶠ z in 𝓝 (t, x), DifferentiableAt 𝕜 F z :=
    ((hF.of_le (le_trans (by norm_num) le_minSmoothness)).eventually (by simp)).mono fun _ hz ↦
        hz.differentiableAt one_ne_zero
  have hSpatial := hSlice.congr_of_eventuallyEq (f₁ := spatialFDeriv F x) (by
    filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually hnear] with s hs
    exact (fderiv_timeSlice hs).symm)
  simpa only [flip_apply, hTime.fderiv] using hSpatial

/-- For a sufficiently smooth parametric map, the parameter derivative of its spatial Jacobian,
applied to `w`, is the spatial derivative of its parameter-velocity field applied to `w`. -/
theorem deriv_spatialFDeriv_apply {F : 𝕜 × E → F'} {t : 𝕜} {x w : E}
    (hF : ContDiffAt 𝕜 (minSmoothness 𝕜 2) F (t, x)) :
    _root_.deriv (fun s => spatialFDeriv F x s w) t =
      fderiv 𝕜 (timeFDeriv F t) x w := by
  exact ((hasDerivAt_spatialFDeriv hF).clm_apply_const w).deriv

/-- **Iterated partial derivatives of a map of two scalar variables commute.** For a map
`g : 𝕜 × 𝕜 → F'` which is smooth enough at `(t, x)` for its second derivative to be symmetric,
differentiating the second partial derivative in the first variable gives the same value as
differentiating the first partial derivative in the second variable. -/
theorem deriv_deriv_comm {g : 𝕜 × 𝕜 → F'} {t x : 𝕜}
    (hg : ContDiffAt 𝕜 (minSmoothness 𝕜 2) g (t, x)) :
    _root_.deriv (fun s => _root_.deriv (fun r => g (s, r)) x) t =
      _root_.deriv (fun r => _root_.deriv (fun s => g (s, r)) t) x := by
  obtain ⟨w, hw, hgw⟩ :=
    hg.contDiffOn (m := 1) (le_trans (by norm_num) le_minSmoothness) (by simp)
  have hdiff : ∀ᶠ z in 𝓝 ((t, x) : 𝕜 × 𝕜), DifferentiableAt 𝕜 g z :=
    (hgw.differentiableOn one_ne_zero).eventually_differentiableAt hw
  have hfst : ∀ᶠ s in 𝓝 t, DifferentiableAt 𝕜 g (s, x) :=
    (continuous_id.prodMk continuous_const).continuousAt.eventually hdiff
  have h₁ : (fun s => _root_.deriv (fun r => g (s, r)) x) =ᶠ[𝓝 t]
      fun s => spatialFDeriv g x s 1 := by
    filter_upwards [hfst] with s hs
    rw [← fderiv_timeSlice hs, fderiv_apply_one_eq_deriv]
  have h₂ := (hg.of_le (le_trans (by norm_num) le_minSmoothness))
    |>.deriv_parameterCurve_eventuallyEq_timeFDeriv
  rw [h₁.deriv_eq, h₂.deriv_eq, deriv_spatialFDeriv_apply hg, fderiv_apply_one_eq_deriv]
