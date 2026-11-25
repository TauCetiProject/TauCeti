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

A translation-invariant form is determined by its value at the origin. So the form is
characterized by translation invariance and its normalization at the origin
(`WeierstrassCurve.Projective.eq_invariantDifferential_of_pullback_add_right`), and every
translation-invariant form is a unique scalar multiple of it
(`WeierstrassCurve.Projective.existsUnique_eq_smul_invariantDifferential`). It is holomorphic
(`WeierstrassCurve.Projective.holomorphicAt_invariantDifferential`) and vanishes nowhere
(`WeierstrassCurve.Projective.invariantDifferential_ne_zero`).
Holomorphy follows by differentiating
the holomorphic function `t(e.symm v - e.symm u)` in `v` and restricting to `v = u` in each
chart `e`.
Its pullback along the exponential map is `dz`
(`WeierstrassCurve.Projective.pullback_invariantDifferential_exp`, in
`TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Exponential`). On affine coordinate
neighbourhoods where `2y + a₁x + a₃ ≠ 0` it is `dx / (2y + a₁x + a₃)`
(`WeierstrassCurve.Projective.invariantDifferential_eq_inv_smul_mvfderiv`, in
`TauCeti.Analysis.SpecialFunctions.Elliptic.Exponential`).

## Main definitions

* `WeierstrassCurve.Projective.invariantDifferential`: the normalized invariant differential of
  `E(ℂ)`.

## Main results

* `WeierstrassCurve.Projective.invariantDifferential_zero`: at the origin the invariant
  differential is the differential of the local parameter.
* `WeierstrassCurve.Projective.pullback_invariantDifferential_add_right`: translations preserve it.
* `WeierstrassCurve.Projective.eq_invariantDifferential_of_pullback_add_right` and
  `WeierstrassCurve.Projective.existsUnique_eq_smul_invariantDifferential`: it is the normalized
  translation-invariant form, and every translation-invariant form is a multiple of it.
* `WeierstrassCurve.Projective.holomorphicAt_invariantDifferential` and
  `WeierstrassCurve.Projective.invariantDifferential_ne_zero`: it is holomorphic and nowhere zero.

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
`TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Exponential`). -/
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

/-- A translation-invariant form is determined by its value at the origin: at `P` it is that
value composed with the differential of the translation by `-P`. -/
private theorem oneForm_eq_of_pullback_add_right {α β : TauCeti.RiemannSurface.OneForm W.Point}
    (hα : ∀ P : W.Point, α.pullback (fun Q ↦ Q + P) = α)
    (hβ : ∀ P : W.Point, β.pullback (fun Q ↦ Q + P) = β) (h0 : α 0 = β 0) : α = β := by
  funext P
  apply ContinuousLinearMap.ext
  intro v
  have hαP := DFunLike.congr_fun (congrFun (hα (-P)) P) v
  have hβP := DFunLike.congr_fun (congrFun (hβ (-P)) P) v
  rw [TauCeti.RiemannSurface.OneForm.pullback_apply, add_neg_cancel, h0] at hαP
  rw [TauCeti.RiemannSurface.OneForm.pullback_apply, add_neg_cancel] at hβP
  exact hαP.symm.trans hβP

/-- **Characterization of the invariant differential**: it is the translation-invariant form
whose value at the origin is the differential of the local parameter. -/
theorem eq_invariantDifferential_of_pullback_add_right
    {α : TauCeti.RiemannSurface.OneForm W.Point}
    (hα : ∀ P : W.Point, α.pullback (fun Q ↦ Q + P) = α)
    (h0 : α 0 = mvfderiv 𝓘(ℂ) Point.localParameter 0) : α = W.invariantDifferential :=
  W.oneForm_eq_of_pullback_add_right hα W.pullback_invariantDifferential_add_right
    (h0.trans W.invariantDifferential_zero.symm)

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

/-- **The translation-invariant forms are the multiples of the invariant differential**: a form
invariant under all translations is `c • ω` for a unique `c : ℂ`. The zero form is the case
`c = 0`. -/
theorem existsUnique_eq_smul_invariantDifferential {α : TauCeti.RiemannSurface.OneForm W.Point}
    (hα : ∀ P : W.Point, α.pullback (fun Q ↦ Q + P) = α) :
    ∃! c : ℂ, α = c • W.invariantDifferential := by
  -- The tangent space at the origin is the line `ℂ`, on which `ω` does not vanish at `1`.
  let v : TangentSpace 𝓘(ℂ) (0 : W.Point) := (1 : ℂ)
  have hv : W.invariantDifferential 0 v ≠ 0 := fun h ↦
    W.invariantDifferential_ne_zero 0 (ContinuousLinearMap.ext_ring h)
  refine ⟨α 0 v / W.invariantDifferential 0 v, ?_, fun c hc ↦ ?_⟩
  · refine W.oneForm_eq_of_pullback_add_right hα (fun P ↦ by
      rw [TauCeti.RiemannSurface.OneForm.pullback_const_smul,
        pullback_invariantDifferential_add_right]) (ContinuousLinearMap.ext_ring ?_)
    -- Both sides are evaluated at the tangent vector `v = 1`.
    exact (div_mul_cancel₀ _ hv).symm
  · have h : α 0 v = c * W.invariantDifferential 0 v := DFunLike.congr_fun (congrFun hc 0) v
    rw [h, mul_div_cancel_right₀ _ hv]

end WeierstrassCurve.Projective
