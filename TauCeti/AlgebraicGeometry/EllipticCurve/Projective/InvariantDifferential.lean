/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.LieGroup
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Pullback
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The invariant differential of a complex elliptic curve

On the points `E(ℂ)` of a complex elliptic curve, the local parameter `t = -X / Y`
(`WeierstrassCurve.Projective.Point.localParameter`) is holomorphic wherever `Y ≠ 0`, in particular
near the origin `O = [0 : 1 : 0]`
(`WeierstrassCurve.Projective.Point.contMDiffAt_localParameter_zero`, in
`TauCeti.AlgebraicGeometry.EllipticCurve.Projective.ComplexManifold`). Translating a tangent vector
at `P` to the origin and applying the differential of `t` there gives the normalized invariant
differential `ω` of `E(ℂ)`: at `P` it is the differential of `Q ↦ t (Q - P)`. It is invariant
under translations.

The form is characterized by translation invariance and its normalization at the origin
(`WeierstrassCurve.Projective.eq_invariantDifferential_of_pullback_add_right`). It is holomorphic
(`WeierstrassCurve.Projective.holomorphicAt_invariantDifferential`) and vanishes nowhere
(`WeierstrassCurve.Projective.invariantDifferential_ne_zero`).
Holomorphy follows by differentiating
the holomorphic function `t(e.symm v - e.symm u)` in `v` and restricting to `v = u` in each
chart `e`.
The results that use the exponential map are in
`TauCeti.Analysis.SpecialFunctions.Elliptic.Exponential`: its pullback along the exponential map
is `dz` (`WeierstrassCurve.Projective.pullback_invariantDifferential_exp`), and on affine coordinate
neighbourhoods where `2y + a₁x + a₃ ≠ 0` it is `dx / (2y + a₁x + a₃)`
(`WeierstrassCurve.Projective.invariantDifferential_eq_inv_smul_mvfderiv`).

## Main definitions

* `WeierstrassCurve.Projective.invariantDifferential`: the normalized invariant differential of
  `E(ℂ)`.

## Main results

* `WeierstrassCurve.Projective.invariantDifferential_zero`: at the origin the invariant
  differential is the differential of the local parameter.
* `WeierstrassCurve.Projective.pullback_invariantDifferential_add_right`: translations preserve it.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §III.5 and §IV.1.
-/

public section

open Filter IsManifold
open scoped Manifold ContDiff Topology

namespace WeierstrassCurve.Projective

variable (W : Projective ℂ) [W.IsElliptic]

/-- The normalized invariant differential on `E(ℂ)`: translate a tangent vector to the origin
and apply the differential of the local parameter `-X / Y` there. Its pullback along the
exponential map is `dz` (`WeierstrassCurve.Projective.pullback_invariantDifferential_exp`, in
`TauCeti.Analysis.SpecialFunctions.Elliptic.Exponential`). -/
noncomputable def invariantDifferential : TauCeti.RiemannSurface.OneForm W.Point := fun P ↦
  mvfderiv 𝓘(ℂ) (fun Q : W.Point ↦ (Q - P).localParameter) P

/-- At `P`, the invariant differential is the differential of `Q ↦ t (Q - P)`, for the local
parameter `t`. -/
theorem invariantDifferential_apply (P : W.Point) :
    W.invariantDifferential P = mvfderiv 𝓘(ℂ) (fun Q : W.Point ↦ (Q - P).localParameter) P :=
  (rfl)

/-- At the origin, the invariant differential is the differential of the local parameter. -/
@[simp]
theorem invariantDifferential_zero :
    W.invariantDifferential 0 = mvfderiv 𝓘(ℂ) Point.localParameter 0 := by
  simp only [invariantDifferential_apply, sub_zero]

/-- Translation preserves the invariant differential. -/
@[simp]
theorem pullback_invariantDifferential_add_right (P : W.Point) :
    W.invariantDifferential.pullback (fun Q ↦ Q + P) = W.invariantDifferential := by
  funext Q
  apply ContinuousLinearMap.ext
  intro v
  have hplus : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun R : W.Point ↦ R + P) Q :=
    (contMDiff_id.add contMDiff_const).mdifferentiableAt (n := 1) one_ne_zero
  have hsub : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun R : W.Point ↦ (R - (Q + P)).localParameter) (Q + P) :=
    ((Point.contMDiffAt_localParameter_zero (W := W) 1).mdifferentiableAt
      one_ne_zero).comp_of_eq (Q + P)
        ((contMDiff_id.sub contMDiff_const).mdifferentiableAt (n := 1) one_ne_zero)
        (sub_self _)
  have heq : (fun R : W.Point ↦ (R - (Q + P)).localParameter) ∘ (fun R ↦ R + P) =
      fun R ↦ (R - Q).localParameter := by
    funext R
    simp only [Function.comp_apply]
    exact congrArg Point.localParameter (by abel)
  rw [TauCeti.RiemannSurface.OneForm.pullback_apply, invariantDifferential_apply,
    invariantDifferential_apply, ← mvfderiv_comp_apply Q hsub hplus, heq]

/-- A translation-invariant form is determined by its value at the origin. In particular, the
normalization by the differential of `t` characterizes the invariant differential. -/
theorem eq_invariantDifferential_of_pullback_add_right
    {α : TauCeti.RiemannSurface.OneForm W.Point}
    (hα : ∀ P : W.Point, α.pullback (fun Q ↦ Q + P) = α)
    (h0 : α 0 = mvfderiv 𝓘(ℂ) Point.localParameter 0) : α = W.invariantDifferential := by
  funext P
  apply ContinuousLinearMap.ext
  intro v
  have h := DFunLike.congr_fun (congrFun (hα (-P)) P) v
  rw [TauCeti.RiemannSurface.OneForm.pullback_apply, add_neg_cancel, h0] at h
  rw [invariantDifferential_apply]
  have ht := (Point.contMDiffAt_localParameter_zero (W := W) 1).mdifferentiableAt one_ne_zero
  have hs : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun Q : W.Point ↦ Q - P) P :=
    (contMDiff_id.sub contMDiff_const).mdifferentiableAt (n := 1) one_ne_zero
  change α P v = mvfderiv 𝓘(ℂ) (Point.localParameter ∘ fun Q : W.Point ↦ Q - P) P v
  rw [mvfderiv_comp_apply P (by simpa using ht) hs, sub_self]
  have heq : (fun Q : W.Point ↦ Q + -P) = (fun Q ↦ Q - P) :=
    funext fun Q ↦ (sub_eq_add_neg Q P).symm
  rw [heq] at h
  exact h.symm

private theorem contMDiffAt_chart_sub (P : W.Point) :
    ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) ω
      (fun a : ℂ × ℂ ↦ (chartAt ℂ P).symm a.2 - (chartAt ℂ P).symm a.1)
      (chartAt ℂ P P, chartAt ℂ P P) := by
  let e := chartAt ℂ P
  have he : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e.symm (e P) :=
    contMDiffAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas P)
      (e.map_source (mem_chart_source ℂ P))
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact (he.comp (e P, e P) contMDiffAt_snd).sub (he.comp (e P, e P) contMDiffAt_fst)

private theorem contDiffAt_localParameter_chart_sub (P : W.Point) :
    ContDiffAt ℂ ω
      (fun a : ℂ × ℂ ↦ ((chartAt ℂ P).symm a.2 - (chartAt ℂ P).symm a.1).localParameter)
      (chartAt ℂ P P, chartAt ℂ P P) := by
  have ht := Point.contMDiffAt_localParameter_zero (W := W) ω
  have hcomp := ht.comp_of_eq (W.contMDiffAt_chart_sub P) (sub_self _)
  exact contMDiffAt_iff_contDiffAt.mp hcomp

private theorem coeff_invariantDifferential_chart (P : W.Point) {u : ℂ}
    (hu : u ∈ (chartAt ℂ P).target) :
    W.invariantDifferential.coeff (chartAt ℂ P) u =
      fderiv ℂ (fun v ↦ ((chartAt ℂ P).symm v - (chartAt ℂ P).symm u).localParameter) u 1 := by
  have hc := TauCeti.RiemannSurface.OneForm.coeff_eq_iff W.invariantDifferential
    (c := fderiv ℂ
      (fun v ↦ ((chartAt ℂ P).symm v - (chartAt ℂ P).symm u).localParameter) u 1)
    (chart_mem_maximalAtlas P) ((chartAt ℂ P).map_target hu)
  rw [(chartAt ℂ P).right_inv hu] at hc
  apply hc.mpr
  rw [invariantDifferential_apply]
  have hd := TauCeti.RiemannSurface.OneForm.mvfderiv_eq_deriv_smul
    (f := fun Q : W.Point ↦ (Q - (chartAt ℂ P).symm u).localParameter)
    (chart_mem_maximalAtlas P) ((chartAt ℂ P).map_target hu)
  rw [(chartAt ℂ P).right_inv hu] at hd
  simpa only [Function.comp_def, deriv] using hd.symm

/-- The invariant differential is holomorphic at every point. -/
theorem holomorphicAt_invariantDifferential (P : W.Point) :
    W.invariantDifferential.HolomorphicAt P := by
  let e := chartAt ℂ P
  let F : ℂ → ℂ → ℂ := fun u v ↦ (e.symm v - e.symm u).localParameter
  have hd : ContDiffAt ℂ ω (fun u ↦ fderiv ℂ (F u) u) (e P) :=
    (W.contDiffAt_localParameter_chart_sub P).fderiv contDiffAt_id (by simp)
  apply (TauCeti.RiemannSurface.OneForm.holomorphicAt_def _ P).mpr
  refine (hd.clm_apply (contDiffAt_const (c := (1 : ℂ)))).analyticAt.congr ?_
  filter_upwards [e.open_target.mem_nhds (e.map_source (mem_chart_source ℂ P))] with u hu
  exact (W.coeff_invariantDifferential_chart P hu).symm
/-- The invariant differential vanishes nowhere. -/
@[simp]
theorem invariantDifferential_ne_zero (P : W.Point) : W.invariantDifferential P ≠ 0 := by
  obtain ⟨v, hv⟩ := (W.isLocalDiffeomorphAt_localParameter_zero (n := 1)).isInvertible_mfderiv
    one_ne_zero |>.surjective (1 : ℂ)
  intro h
  have hz := DFunLike.congr_fun (congrFun (W.pullback_invariantDifferential_add_right P) 0) v
  rw [TauCeti.RiemannSurface.OneForm.pullback_apply, zero_add, h, zero_apply,
    W.invariantDifferential_zero, mvfderiv_apply_eq_mfderiv_apply, hv] at hz
  exact zero_ne_one hz

end WeierstrassCurve.Projective
