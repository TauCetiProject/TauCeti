/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Conformal
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic

/-!
# Locally conformally flat metrics

A smooth Riemannian metric `g` on `M` is *locally conformally flat* if every point has a
neighbourhood on which some conformal rescaling `f g`, by a smooth positive function `f`, is flat.
This file defines the notion and proves its first properties: it depends only on the conformal
class of `g`, flat metrics are locally conformally flat, and away from dimension `2` the Weyl
tensor of a locally conformally flat metric vanishes identically.

The last statement is one half of the Weyl–Schouten theorem; the converse (vanishing of the Weyl
tensor in dimension at least `4`, or of the Cotton tensor in dimension `3`, implies local conformal
flatness) is a Frobenius integrability argument and is not proved here. The proof of the forward
direction combines two facts: the Weyl tensor of a flat metric vanishes, and the Weyl tensor of
`f g` is `f` times that of `g`, so its vanishing at a point is a conformal invariant.

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
the full curvature tensor.

## Main declarations

* `Bundle.ContMDiffRiemannianMetric.IsLocallyConformallyFlat`: local conformal flatness of a smooth
  Riemannian metric on the tangent bundle.
* `Bundle.ContMDiffRiemannianMetric.isLocallyConformallyFlat_rescale_iff`: local conformal flatness
  of `f g` is equivalent to that of `g`.
* `Bundle.ContMDiffRiemannianMetric.IsLocallyConformallyFlat.of_mem_conformalClass`: local
  conformal flatness depends only on the conformal class.
* `Bundle.ContMDiffRiemannianMetric.isLocallyConformallyFlat_of_curvatureTensor_eq_zero`: flat
  metrics are locally conformally flat.
* `TauCeti.Manifold.isLocallyConformallyFlat_rescale_model_space`: every metric conformal to the
  Euclidean metric is locally conformally flat.
* `Bundle.ContMDiffRiemannianMetric.IsLocallyConformallyFlat.weylTensor_eq_zero`: away from
  dimension `2`, a locally conformally flat metric has vanishing Weyl tensor.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 2.
-/

public section

open Bundle Filter
open scoped ContDiff Manifold Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- A smooth Riemannian metric `g` is **locally conformally flat** if every point `x` has a
neighbourhood on which a conformal rescaling `f g`, by a smooth positive function `f`, is flat:
the curvature tensor of the Levi-Civita connection of `f g` vanishes at every point near `x`. -/
def IsLocallyConformallyFlat
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) : Prop :=
  ∀ x : M, ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ y, 0 < f y),
    ∀ᶠ y in 𝓝 x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0

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

/-- If `g` is locally conformally flat, then so is every conformal rescaling `h g` of `g`: a
conformal factor `f` flattening `g` near a point gives the factor `f / h` flattening `h g`. -/
theorem IsLocallyConformallyFlat.rescale
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsLocallyConformallyFlat) {h : M → ℝ} (hh : ContMDiff I 𝓘(ℝ) ∞ h)
    (hh_pos : ∀ x, 0 < h x) : (g.rescale h hh hh_pos).IsLocallyConformallyFlat := by
  intro x
  obtain ⟨f, hf, hf_pos, hflat⟩ := hg x
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

/-- A conformal rescaling `h g` of a metric `g` is locally conformally flat exactly when `g` is. -/
@[simp]
theorem isLocallyConformallyFlat_rescale_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {h : M → ℝ}
    (hh : ContMDiff I 𝓘(ℝ) ∞ h) (hh_pos : ∀ x, 0 < h x) :
    (g.rescale h hh hh_pos).IsLocallyConformallyFlat ↔ g.IsLocallyConformallyFlat := by
  refine ⟨fun hg ↦ ?_, fun hg ↦ hg.rescale hh hh_pos⟩
  simpa only [rescale_inv_rescale] using
    hg.rescale (hh.inv₀ fun x ↦ (hh_pos x).ne') fun x ↦ inv_pos.2 (hh_pos x)

/-- Local conformal flatness depends only on the conformal class: every metric conformal to a
locally conformally flat metric is locally conformally flat. -/
theorem IsLocallyConformallyFlat.of_mem_conformalClass
    {g g' : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsLocallyConformallyFlat) (hg' : g' ∈ g.conformalClass) :
    g'.IsLocallyConformallyFlat := by
  obtain ⟨h, hh, hh_pos, rfl⟩ := mem_conformalClass_iff.1 hg'
  exact hg.rescale hh hh_pos

/-- **Local conformal flatness forces the Weyl tensor to vanish.** Away from dimension `2`, the
Weyl tensor of a locally conformally flat metric vanishes at every point. This is the easy half of
the Weyl–Schouten theorem. -/
theorem IsLocallyConformallyFlat.weylTensor_eq_zero
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsLocallyConformallyFlat) (hn : Module.finrank ℝ E ≠ 2) (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor x) = 0 := by
  obtain ⟨f, hf, hf_pos, hflat⟩ := hg x
  -- The Weyl tensor of the flat metric `f g` vanishes at `x`, and with it that of `g`.
  refine (weylTensor_leviCivitaConnection_rescale_eq_zero_iff g hf hf_pos hn x).1 ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩
  exact (CovariantDerivative.leviCivitaConnection I M).weylTensor_eq_zero_of_curvatureTensor_eq_zero
    x hflat.self_of_nhds

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
