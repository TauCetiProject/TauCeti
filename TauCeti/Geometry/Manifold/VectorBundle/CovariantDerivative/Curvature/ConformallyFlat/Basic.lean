/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Conformal.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Integrability
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Log
import TauCeti.Geometry.Manifold.Riemannian.Scaling

/-!
# Locally conformally flat metrics

A smooth Riemannian metric `g` on `M` is *locally conformally flat* if every point has a
neighbourhood on which some conformal rescaling `f g`, by a smooth positive function `f`, is flat.
This file defines the notion and proves its first properties: it depends only on the conformal
class of `g`, flat metrics are locally conformally flat, a flattening factor can be normalized to
take the value `1` at a given point, the Weyl tensor vanishes identically away from dimension `2`,
and the Cotton tensor vanishes identically in every dimension.

The last statements are one half of the Weyl–Schouten theorem; the converse (vanishing of the Weyl
tensor in dimension at least `4`, or of the Cotton tensor in dimension `3`, implies local conformal
flatness) is a Frobenius integrability argument and is not proved here: this file only reduces it
to local solvability of the conformal flattening equation (see below). The proof of the forward
direction combines two facts: the Weyl tensor of a flat metric vanishes, and the Weyl tensor of
`f g` is `f` times that of `g`, so its vanishing at a point is a conformal invariant. For the Cotton
tensor, in dimension `2` both the Schouten and Cotton tensors vanish identically by the
`(2 - 2)⁻¹ = 0` convention; away from dimension `2`, the Cotton tensor of `f g` vanishes at a point
near which `f g` is flat, and it differs from that of `g` by a contraction of the Weyl tensor of
`g`, which has just been shown to vanish.

This file reduces the converse to local solvability of a PDE. In dimension at least `3`, the metric
`e^(2φ) g` is flat exactly where the Weyl tensor of `g` vanishes and `φ` solves the conformal
flattening equation `Hess φ = P + dφ ⊗ dφ - (|dφ|² / 2) g`, since the curvature tensor vanishes
exactly when both the Weyl and the Schouten tensor do, the Weyl tensor transforms by a positive
factor, and the Schouten tensor of `e^(2φ) g` vanishes exactly where the equation holds. Hence `g`
is locally conformally flat exactly when its Weyl tensor vanishes and the equation has a smooth
solution near every point. In dimension `3` the Weyl condition is automatic
(`CovariantDerivative.IsMetricCompatible.weylTensor_eq_zero_of_finrank_eq_three`).

The conformal factor in the definition is a smooth positive function on all of `M`, while
flatness of `f g` is only required near the point. Classically the factor is only defined near the
point; the two formulations agree because curvature at a point only depends on the metric near
that point, and a local positive factor can be extended to a global one by a smooth cutoff without
changing it near the point. Requiring a global factor lets the definition use
`Bundle.ContMDiffRiemannianMetric.rescale` directly instead of metrics on open subsets. As for
`Bundle.ContMDiffRiemannianMetric.weylTensor_leviCivitaConnection_rescale`, the metric `f g` is
installed as the `RiemannianBundle` instance of the tangent bundle of `M` when its curvature is
evaluated.

Dimension `2` is excluded from the Weyl statement because there the Schouten tensor carries the
factor `1 / (n - 2)`, which is `0` by the convention for division by zero, so the Weyl tensor is
the full curvature tensor (while the Cotton tensor vanishes identically).

## Main declarations

* `Bundle.ContMDiffRiemannianMetric.IsLocallyConformallyFlatAt` and
  `Bundle.ContMDiffRiemannianMetric.IsLocallyConformallyFlat`: pointwise and global local conformal
  flatness of a smooth Riemannian metric on the tangent bundle.
* `Bundle.ContMDiffRiemannianMetric.isLocallyConformallyFlatAt_rescale_iff` and
  `Bundle.ContMDiffRiemannianMetric.isLocallyConformallyFlat_rescale_iff`: local conformal flatness
  of `f g` is equivalent to that of `g`.
* `Bundle.ContMDiffRiemannianMetric.IsLocallyConformallyFlatAt.of_mem_conformalClass` and
  `Bundle.ContMDiffRiemannianMetric.IsLocallyConformallyFlat.of_mem_conformalClass`: local
  conformal flatness depends only on the conformal class.
* `Bundle.ContMDiffRiemannianMetric.isLocallyConformallyFlat_of_curvatureTensor_eq_zero`: flat
  metrics are locally conformally flat.
* `IsLocallyConformallyFlatAt.exists_apply_eq_one_and_eventually_curvatureTensor_rescale_eq_zero`
  and `IsLocallyConformallyFlat.exists_apply_eq_one_and_eventually_curvatureTensor_rescale_eq_zero`
  (in `Bundle.ContMDiffRiemannianMetric`): normalizing a flattening conformal factor so `f x₀ = 1`.
* `TauCeti.Manifold.isLocallyConformallyFlat_rescale_model_space`: every metric conformal to the
  Euclidean metric is locally conformally flat.
* `Bundle.ContMDiffRiemannianMetric.weylTensor_eq_zero_of_curvatureTensor_rescale_eq_zero`,
  `Bundle.ContMDiffRiemannianMetric.IsLocallyConformallyFlatAt.weylTensor_eq_zero`, and
  `Bundle.ContMDiffRiemannianMetric.IsLocallyConformallyFlat.weylTensor_eq_zero`: away from
  dimension `2`, flatness of a conformal rescaling at a point (hence local conformal flatness)
  forces the Weyl tensor to vanish.
* `cottonTensor_eq_zero_of_eventually_curvatureTensor_rescale_eq_zero`,
  `IsLocallyConformallyFlatAt.cottonTensor_eq_zero`, and
  `IsLocallyConformallyFlat.cottonTensor_eq_zero` (in `Bundle.ContMDiffRiemannianMetric`): in every
  dimension, flatness of a conformal rescaling near a point (hence local conformal flatness) forces
  the Cotton tensor to vanish.
* `Bundle.ContMDiffRiemannianMetric.curvatureTensor_leviCivitaConnection_rescale_eq_zero_iff`:
  `e^(2φ) g` is flat at `x` exactly when `W = 0` and the conformal flattening equation holds at `x`.
* `isLocallyConformallyFlat_iff_forall_weylTensor_eq_zero_and_forall_exists_eventually_hessian_eq`
  (in `Bundle.ContMDiffRiemannianMetric`): in dimension at least `3`, local conformal flatness is
  equivalent to `W = 0` together with local solvability of the conformal flattening equation.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 2.
-/

public section

open Bundle Filter TauCeti.Manifold
open scoped ContDiff Manifold Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- A smooth Riemannian metric `g` is **locally conformally flat at `x`** if there is a smooth
positive function `f : M → ℝ` such that the rescaled metric `f g` has vanishing Levi-Civita
curvature tensor on a neighbourhood of `x`. -/
def IsLocallyConformallyFlatAt
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x : M) : Prop :=
  ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ y, 0 < f y),
    ∀ᶠ y in 𝓝 x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0

/-- Unfolding lemma for `Bundle.ContMDiffRiemannianMetric.IsLocallyConformallyFlatAt`. -/
theorem isLocallyConformallyFlatAt_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {x : M} :
    g.IsLocallyConformallyFlatAt x ↔
      ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ y, 0 < f y),
        ∀ᶠ y in 𝓝 x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 :=
  Iff.rfl

/-- Local conformal flatness at `x` holds on a neighbourhood of `x`. -/
theorem IsLocallyConformallyFlatAt.eventually
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {x : M}
    (hg : g.IsLocallyConformallyFlatAt x) :
    ∀ᶠ y in 𝓝 x, g.IsLocallyConformallyFlatAt y := by
  obtain ⟨f, hf, hf_pos, hflat⟩ := hg
  exact hflat.eventually_nhds.mono fun _ hy ↦ ⟨f, hf, hf_pos, hy⟩

/-- A smooth Riemannian metric `g` is **locally conformally flat** if every point `x` has a
neighbourhood on which a conformal rescaling `f g`, by a smooth positive function `f`, is flat:
the curvature tensor of the Levi-Civita connection of `f g` vanishes at every point near `x`. -/
def IsLocallyConformallyFlat
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) : Prop :=
  ∀ x : M, g.IsLocallyConformallyFlatAt x

/-- `g` is locally conformally flat if and only if it is locally conformally flat at every point. -/
theorem isLocallyConformallyFlat_iff_forall_isLocallyConformallyFlatAt
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    g.IsLocallyConformallyFlat ↔ ∀ x : M, g.IsLocallyConformallyFlatAt x :=
  Iff.rfl

/-- A locally conformally flat metric is locally conformally flat at every point. -/
theorem IsLocallyConformallyFlat.isLocallyConformallyFlatAt
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsLocallyConformallyFlat) (x : M) : g.IsLocallyConformallyFlatAt x :=
  hg x

/-- Unfolding lemma for `Bundle.ContMDiffRiemannianMetric.IsLocallyConformallyFlat`. -/
theorem isLocallyConformallyFlat_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    g.IsLocallyConformallyFlat ↔
      ∀ x : M, ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ y, 0 < f y),
        ∀ᶠ y in 𝓝 x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 :=
  Iff.rfl

/-- A flat metric is locally conformally flat, with the constant conformal factor `1`. -/
theorem isLocallyConformallyFlat_of_curvatureTensor_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (h : ∀ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x) = 0) :
    g.IsLocallyConformallyFlat := fun _ ↦
  ⟨fun _ ↦ 1, contMDiff_const, fun _ ↦ one_pos, Eventually.of_forall fun y ↦
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    (curvatureTensor_leviCivitaConnection_eq_of_riemannianBundle_eq (by rw [rescale_one]; rfl)
      y).trans (h y)⟩

/-- If `g` is locally conformally flat at `x`, then so is every conformal rescaling `h g` of `g`: a
conformal factor `f` flattening `g` near `x` gives the factor `f / h` flattening `h g`. -/
theorem IsLocallyConformallyFlatAt.rescale
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {x : M}
    (hg : g.IsLocallyConformallyFlatAt x) {h : M → ℝ} (hh : ContMDiff I 𝓘(ℝ) ∞ h)
    (hh_pos : ∀ y, 0 < h y) : (g.rescale h hh hh_pos).IsLocallyConformallyFlatAt x := by
  obtain ⟨f, hf, hf_pos, hflat⟩ := hg
  have hfh : ContMDiff I 𝓘(ℝ) ∞ fun y ↦ f y / h y :=
    hf.div₀ hh fun y ↦ (hh_pos y).ne'
  have hfh_pos (y : M) : 0 < f y / h y := div_pos (hf_pos y) (hh_pos y)
  have heq : (g.rescale h hh hh_pos).rescale (fun y ↦ f y / h y) hfh hfh_pos =
      g.rescale f hf hf_pos := by
    ext y v w
    simp [div_mul_cancel₀ _ (hh_pos y).ne']
  exact ⟨fun y ↦ f y / h y, hfh, hfh_pos, hflat.mono fun _ ↦
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩
      (curvatureTensor_leviCivitaConnection_eq_of_riemannianBundle_eq (by rw [heq]; rfl) _).trans⟩

/-- A conformal rescaling `h g` of `g` is locally conformally flat at `x` exactly when `g` is. -/
@[simp]
theorem isLocallyConformallyFlatAt_rescale_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {x : M} {h : M → ℝ}
    (hh : ContMDiff I 𝓘(ℝ) ∞ h) (hh_pos : ∀ y, 0 < h y) :
    (g.rescale h hh hh_pos).IsLocallyConformallyFlatAt x ↔ g.IsLocallyConformallyFlatAt x := by
  refine ⟨fun hg ↦ ?_, fun hg ↦ hg.rescale hh hh_pos⟩
  simpa only [rescale_inv_rescale] using
    hg.rescale (hh.inv₀ fun y ↦ (hh_pos y).ne') fun y ↦ inv_pos.2 (hh_pos y)

/-- Pointwise local conformal flatness depends only on the conformal class. -/
theorem IsLocallyConformallyFlatAt.of_mem_conformalClass
    {g g' : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {x : M}
    (hg : g.IsLocallyConformallyFlatAt x) (hg' : g' ∈ g.conformalClass) :
    g'.IsLocallyConformallyFlatAt x := by
  obtain ⟨h, hh, hh_pos, rfl⟩ := mem_conformalClass_iff.1 hg'
  exact hg.rescale hh hh_pos

/-- If `g` is locally conformally flat, then so is every conformal rescaling `h g` of `g`: a
conformal factor `f` flattening `g` near a point gives the factor `f / h` flattening `h g`. -/
theorem IsLocallyConformallyFlat.rescale
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsLocallyConformallyFlat) {h : M → ℝ} (hh : ContMDiff I 𝓘(ℝ) ∞ h)
    (hh_pos : ∀ x, 0 < h x) : (g.rescale h hh hh_pos).IsLocallyConformallyFlat :=
  fun x ↦ (hg x).rescale hh hh_pos

/-- A conformal rescaling `h g` of a metric `g` is locally conformally flat exactly when `g` is. -/
@[simp]
theorem isLocallyConformallyFlat_rescale_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {h : M → ℝ}
    (hh : ContMDiff I 𝓘(ℝ) ∞ h) (hh_pos : ∀ x, 0 < h x) :
    (g.rescale h hh hh_pos).IsLocallyConformallyFlat ↔ g.IsLocallyConformallyFlat :=
  forall_congr' fun _ ↦ g.isLocallyConformallyFlatAt_rescale_iff hh hh_pos

/-- Local conformal flatness depends only on the conformal class: every metric conformal to a
locally conformally flat metric is locally conformally flat. -/
theorem IsLocallyConformallyFlat.of_mem_conformalClass
    {g g' : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsLocallyConformallyFlat) (hg' : g' ∈ g.conformalClass) :
    g'.IsLocallyConformallyFlat := by
  obtain ⟨h, hh, hh_pos, rfl⟩ := mem_conformalClass_iff.1 hg'
  exact hg.rescale hh hh_pos

namespace IsLocallyConformallyFlatAt

/-- **Pointwise normalization of a local flattening conformal factor.** If `g` is locally
conformally flat at `x₀`, then rescaling a local flattening factor `f₀` by `(f₀ x₀)⁻¹` yields a
smooth positive factor `f : M → ℝ` normalized by `f x₀ = 1` such that `f g` is flat near `x₀`. -/
theorem exists_apply_eq_one_and_eventually_curvatureTensor_rescale_eq_zero
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {x₀ : M}
    (hg : g.IsLocallyConformallyFlatAt x₀) :
    ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ y, 0 < f y),
      f x₀ = 1 ∧
      ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 := by
  obtain ⟨f₀, hf₀, hf₀_pos, hflat⟩ := hg
  set c : ℝ := (f₀ x₀)⁻¹
  have hc : 0 < c := inv_pos.2 (hf₀_pos x₀)
  have hf : ContMDiff I 𝓘(ℝ) ∞ (fun y ↦ c * f₀ y) := contMDiff_const.mul hf₀
  have hf_pos (y : M) : 0 < c * f₀ y := mul_pos hc (hf₀_pos y)
  have hEq : g.rescale (fun y ↦ c * f₀ y) hf hf_pos =
      (g.rescale f₀ hf₀ hf₀_pos).rescale (fun _ ↦ c) contMDiff_const (fun _ ↦ hc) :=
    (g.rescale_rescale (hf := hf₀) (hf_pos := hf₀_pos) (fun _ ↦ c) contMDiff_const
      (fun _ ↦ hc)).symm
  refine ⟨fun y ↦ c * f₀ y, hf, hf_pos, inv_mul_cancel₀ (hf₀_pos x₀).ne', hflat.mono fun y hy ↦ ?_⟩
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨((g.rescale f₀ hf₀ hf₀_pos).rescale (fun _ ↦ c) contMDiff_const
      (fun _ ↦ hc)).toRiemannianMetric⟩
  rw [curvatureTensor_leviCivitaConnection_eq_of_riemannianBundle_eq
      (congrArg ContMDiffRiemannianMetric.toRiemannianMetric hEq.symm) y,
    (g.rescale f₀ hf₀ hf₀_pos).curvatureTensor_leviCivitaConnection_rescale_const hc y, hy]

end IsLocallyConformallyFlatAt

namespace IsLocallyConformallyFlat

/-- **Pointwise normalization of a flattening conformal factor.** If `g` is locally conformally
flat, then around every point `x₀` there is a smooth positive conformal factor `f : M → ℝ`
normalized by `f x₀ = 1` such that `f g` is flat near `x₀`. -/
theorem exists_apply_eq_one_and_eventually_curvatureTensor_rescale_eq_zero
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsLocallyConformallyFlat) (x₀ : M) :
    ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ y, 0 < f y),
      f x₀ = 1 ∧
      ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 :=
  (hg x₀).exists_apply_eq_one_and_eventually_curvatureTensor_rescale_eq_zero

end IsLocallyConformallyFlat

/-- **Pointwise Weyl necessity.** Away from dimension `2`, if a conformal rescaling `f g` has
vanishing curvature tensor at `x`, then the Weyl tensor of `g` vanishes at `x`. -/
theorem weylTensor_eq_zero_of_curvatureTensor_rescale_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ z, 0 < f z)
    (hn : Module.finrank ℝ E ≠ 2) {x : M}
    (hflat : (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x) = 0) :
    (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor x) = 0 := by
  refine (weylTensor_leviCivitaConnection_rescale_eq_zero_iff g hf hf_pos hn x).1 ?_
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
    ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩
  exact (CovariantDerivative.leviCivitaConnection I M).weylTensor_eq_zero_of_curvatureTensor_eq_zero
    x hflat

/-- **Local conformal flatness at `x` forces the Weyl tensor to vanish at `x`.** Away from dimension
`2`, if `g` is locally conformally flat at `x`, then its Weyl tensor vanishes at `x`. -/
theorem IsLocallyConformallyFlatAt.weylTensor_eq_zero
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {x : M}
    (hg : g.IsLocallyConformallyFlatAt x) (hn : Module.finrank ℝ E ≠ 2) :
    (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor x) = 0 := by
  obtain ⟨f, hf, hf_pos, hflat⟩ := hg
  exact g.weylTensor_eq_zero_of_curvatureTensor_rescale_eq_zero hf hf_pos hn hflat.self_of_nhds

/-- **Local conformal flatness forces the Weyl tensor to vanish.** Away from dimension `2`, the
Weyl tensor of a locally conformally flat metric vanishes at every point. This is the easy half of
the Weyl–Schouten theorem. -/
theorem IsLocallyConformallyFlat.weylTensor_eq_zero
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsLocallyConformallyFlat) (hn : Module.finrank ℝ E ≠ 2) (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor x) = 0 :=
  (hg x).weylTensor_eq_zero hn

/-- **Germ-to-point Cotton necessity.** In every dimension, if a conformal rescaling `f g` is flat
near `x`, then the Cotton tensor of `g` vanishes at `x` (in dimension `2`, the Schouten and Cotton
tensors vanish identically by the `(2 - 2)⁻¹ = 0` convention). -/
theorem cottonTensor_eq_zero_of_eventually_curvatureTensor_rescale_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ z, 0 < f z) {x : M}
    (hflat : ∀ᶠ y in 𝓝 x, (letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0) :
    (letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).cottonTensor x) = 0 := by
  by_cases hn : Module.finrank ℝ E = 2
  · let _ : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩
    exact (CovariantDerivative.leviCivitaConnection I M).cottonTensor_eq_zero_of_finrank_eq_two hn x
  · have hfφ (y : M) : f y = Real.exp (2 * (Real.log (f y) / 2)) := by
      rw [mul_div_cancel₀ _ (two_ne_zero' ℝ), Real.exp_log (hf_pos y)]
    have hC : (letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).cottonTensor x) = 0 :=
      letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩
      CovariantDerivative.cottonTensor_eq_zero_of_eventually_curvatureTensor_eq_zero _ hflat
    ext u v w
    have h := cottonTensor_leviCivitaConnection_rescale g hf hf_pos hfφ hn x u v w
    rw [hC, g.weylTensor_eq_zero_of_curvatureTensor_rescale_eq_zero hf hf_pos hn
      hflat.self_of_nhds] at h
    simpa using h.symm

/-- **Local conformal flatness at `x` forces the Cotton tensor to vanish at `x`.** In every
dimension, if `g` is locally conformally flat at `x`, then its Cotton tensor vanishes at `x`. -/
theorem IsLocallyConformallyFlatAt.cottonTensor_eq_zero
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {x : M}
    (hg : g.IsLocallyConformallyFlatAt x) :
    (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).cottonTensor x) = 0 := by
  obtain ⟨f, hf, hf_pos, hflat⟩ := hg
  exact g.cottonTensor_eq_zero_of_eventually_curvatureTensor_rescale_eq_zero hf hf_pos hflat

/-- **Local conformal flatness forces the Cotton tensor to vanish.** In every dimension, the Cotton
tensor of a locally conformally flat metric vanishes at every point (in dimension `2`, the Schouten
and Cotton tensors vanish identically by the `(2 - 2)⁻¹ = 0` convention). In dimension `3` this is
the easy half of the characterization of local conformal flatness by the Cotton tensor. -/
theorem IsLocallyConformallyFlat.cottonTensor_eq_zero
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsLocallyConformallyFlat) (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).cottonTensor x) = 0 :=
  (hg x).cottonTensor_eq_zero

/-- **When `e^(2φ) g` is flat.** In dimension at least `3`, the metric `f g` with `f = e^(2φ)` has
vanishing curvature tensor at `x` exactly when the Weyl tensor of `g` vanishes at `x` and `φ` solves
the conformal flattening equation `Hess φ = P + dφ ⊗ dφ - (|dφ|² / 2) g` at `x`, where the Hessian,
the gradient and the Schouten tensor `P` are those of `g`. -/
theorem curvatureTensor_leviCivitaConnection_rescale_eq_zero_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x) {φ : M → ℝ}
    (hfφ : ∀ x, f x = Real.exp (2 * φ x)) (hn : 3 ≤ Module.finrank ℝ E) (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x = 0) ↔
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0 ∧
      ∀ u v : TangentSpace I x, hessian I φ x u v =
        (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm x
          (mgradient I φ x) u v := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩
  refine Iff.trans
    (CovariantDerivative.curvatureTensor_eq_zero_iff_weylTensor_eq_zero_and_schoutenTensor_eq_zero
      (CovariantDerivative.leviCivitaConnection I M) x) ?_
  exact and_congr (weylTensor_leviCivitaConnection_rescale_eq_zero_iff g hf hf_pos (by omega) x)
    (schoutenTensor_leviCivitaConnection_rescale_eq_zero_iff g hf hf_pos hfφ hn x)

/-- **Local conformal flatness and the conformal flattening equation.** In dimension at least `3`,
a smooth metric `g` is locally conformally flat exactly when its Weyl tensor vanishes and every
point has a neighbourhood on which a smooth function `φ` solves the conformal flattening equation
`Hess φ = P + dφ ⊗ dφ - (|dφ|² / 2) g`. A solution `φ` near `x` gives the conformal factor
`e^(2φ)` flattening `g` near `x`, and conversely `φ = (log f) / 2` for a flattening factor `f`. -/
theorem
    isLocallyConformallyFlat_iff_forall_weylTensor_eq_zero_and_forall_exists_eventually_hessian_eq
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 3 ≤ Module.finrank ℝ E) :
    g.IsLocallyConformallyFlat ↔
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      (∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0) ∧
        ∀ x, ∃ φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ ∧ ∀ᶠ y in 𝓝 x, ∀ u v : TangentSpace I y,
          hessian I φ y u v = (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm
            y (mgradient I φ y) u v := by
  refine ⟨fun hg ↦ ⟨hg.weylTensor_eq_zero (by omega), fun x ↦ ?_⟩, fun ⟨hW, hsol⟩ x ↦ ?_⟩
  · obtain ⟨f, hf, hf_pos, hflat⟩ := hg x
    have hfφ (y : M) : f y = Real.exp (2 * (Real.log (f y) / 2)) := by
      rw [mul_div_cancel₀ _ (two_ne_zero' ℝ), Real.exp_log (hf_pos y)]
    exact ⟨fun y ↦ Real.log (f y) / 2, (hf.log fun y ↦ (hf_pos y).ne').div_const 2,
      hflat.mono fun y hy ↦
        ((curvatureTensor_leviCivitaConnection_rescale_eq_zero_iff g hf hf_pos hfφ hn y).1 hy).2⟩
  · obtain ⟨φ, hφ, hsolφ⟩ := hsol x
    have hf : ContMDiff I 𝓘(ℝ) ∞ fun y ↦ Real.exp (2 * φ y) :=
      Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ)
    exact ⟨fun y ↦ Real.exp (2 * φ y), hf, fun y ↦ Real.exp_pos _, hsolφ.mono fun y hy ↦
      (curvatureTensor_leviCivitaConnection_rescale_eq_zero_iff g hf (fun y ↦ Real.exp_pos _)
        (fun _ ↦ rfl) hn y).2 ⟨hW y, hy⟩⟩

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti.Manifold

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Conformally Euclidean metrics are locally conformally flat.** On a finite-dimensional real
inner-product space `F`, every conformal rescaling `f g` of the Euclidean metric `g` by a smooth
positive function `f` is locally conformally flat. -/
theorem isLocallyConformallyFlat_rescale_model_space {f : F → ℝ}
    (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x) :
    (((riemannianMetricVectorSpace F).ofLE le_top).rescale f hf hf_pos).IsLocallyConformallyFlat :=
  (((riemannianMetricVectorSpace F).ofLE le_top).isLocallyConformallyFlat_of_curvatureTensor_eq_zero
    fun x ↦
      (ContMDiffRiemannianMetric.curvatureTensor_leviCivitaConnection_eq_of_riemannianBundle_eq
        -- Mathlib's `RiemannianBundle` instance on the tangent spaces of `F` is defined to be
        -- the standard metric `riemannianMetricVectorSpace F`.
        (by rw [ContMDiffRiemannianMetric.toRiemannianMetric_ofLE]; rfl) x).trans
        (curvatureTensor_leviCivitaConnection_model_space x)).rescale hf hf_pos

end TauCeti.Manifold
