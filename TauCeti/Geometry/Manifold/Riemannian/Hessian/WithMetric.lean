/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hessian.Conformal
public import TauCeti.Geometry.Manifold.Riemannian.Hessian.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric

/-!
# Hessians on metric-indexed manifolds

The tautological diffeomorphism from `WithMetric g` to the original manifold transports the
Hessian for `g`. Consequently conformal Hessians can be compared on distinct metric-indexed
copies, with their tangent vectors transported by the differentials of the tautological maps.
Only the reference metric is installed on the original manifold; the rescaled metric is
installed exclusively on its own copy in the comparison theorem.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, §2, for conformal Hessians.
-/

public section

open Bundle TauCeti.Manifold
open scoped Manifold ContDiff InnerProductSpace

noncomputable section

namespace TauCeti.WithMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M] {n : ℕ∞ω}

/-- Transport of the scalar Hessian from a metric-indexed copy to the original manifold
carrying that same metric. Tangent vectors are transported by the tautological diffeomorphism. -/
@[simp]
theorem hessian_comp_ofWithMetric
    {g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)} (hn : 1 ≤ n)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u) (x : M) (v w : TangentSpace I x) :
    (letI : IsContMDiffRiemannianBundle I 1 E (fun x : WithMetric g ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      hessian I (u ∘ ofWithMetric) (toWithMetric g x)
        (mfderiv I I (toWithMetric g) x v) (mfderiv I I (toWithMetric g) x w)) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      hessian I u x v w) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hn
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : WithMetric g ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hn
  have hiso : IsLocalRiemannianIsometry I I (ofWithMetric : WithMetric g → M) := by
    refine ⟨contMDiff_ofWithMetric, ?_, ?_⟩
    · intro y
      rw [mfderiv_ofWithMetric]
      exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
    · intro y a b
      exact (inner_def y a b).symm
  have h := hiso.hessian_comp hu (toWithMetric g x)
    (mfderiv I I (toWithMetric g) x v) (mfderiv I I (toWithMetric g) x w)
  rw [mfderiv_ofWithMetric (g := g), mfderiv_toWithMetric] at h
  rw [mfderiv_toWithMetric]
  -- Congruence compares the transported tangent inputs without unfolding the Hessian.
  convert h using 1
  congr 1

/-- **Conformal Hessians on distinct metric-indexed copies.** The correction is evaluated
with the reference metric on `M`; each Hessian uses the canonical metric on its own copy.
No metric instance for the rescaled metric is installed on `M` in this statement. -/
theorem hessian_rescale
    {g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)} (hn : 1 ≤ n)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f) (hf_pos : ∀ x, 0 < f x)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u) (x : M) (v w : TangentSpace I x) :
    (letI : IsContMDiffRiemannianBundle I 1 E
        (fun x : WithMetric (g.rescale f hf hf_pos) ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      hessian I (u ∘ ofWithMetric) (toWithMetric (g.rescale f hf hf_pos) x)
        (mfderiv I I (toWithMetric (g.rescale f hf hf_pos)) x v)
        (mfderiv I I (toWithMetric (g.rescale f hf hf_pos)) x w)) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : WithMetric g ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      hessian I (u ∘ ofWithMetric) (toWithMetric g x)
          (mfderiv I I (toWithMetric g) x v) (mfderiv I I (toWithMetric g) x w) -
        (2 * f x)⁻¹ * (mvfderiv I f x v * mvfderiv I u x w +
          mvfderiv I f x w * mvfderiv I u x v -
          ⟪mgradient I f x, mgradient I u x⟫_ℝ * ⟪v, w⟫_ℝ)) := by
  rw [hessian_comp_ofWithMetric hn hu, hessian_comp_ofWithMetric hn hu]
  exact g.hessian_rescale hn hf hf_pos hu.contMDiffAt v w

/-- **Power-rescaled Hessians on metric-indexed copies.** Taking `p = 4 / (dim M - 2)`
gives the Hessian transformation for the Yamabe conformal factor, at `C¹` metric regularity. -/
theorem hessian_rescale_rpow
    {g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)} (hn : 1 ≤ n)
    {a : M → ℝ} (ha : ContMDiff I 𝓘(ℝ) n a) (ha_pos : ∀ x, 0 < a x) (p : ℝ)
    {hf : ContMDiff I 𝓘(ℝ) n fun x ↦ a x ^ p} {hf_pos : ∀ x, 0 < a x ^ p}
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u) (x : M) (v w : TangentSpace I x) :
    (letI : IsContMDiffRiemannianBundle I 1 E
        (fun x : WithMetric (g.rescale (fun x ↦ a x ^ p) hf hf_pos) ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      hessian I (u ∘ ofWithMetric) (toWithMetric (g.rescale (fun x ↦ a x ^ p) hf hf_pos) x)
        (mfderiv I I (toWithMetric (g.rescale (fun x ↦ a x ^ p) hf hf_pos)) x v)
        (mfderiv I I (toWithMetric (g.rescale (fun x ↦ a x ^ p) hf hf_pos)) x w)) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : WithMetric g ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      hessian I (u ∘ ofWithMetric) (toWithMetric g x)
          (mfderiv I I (toWithMetric g) x v) (mfderiv I I (toWithMetric g) x w) -
        p / (2 * a x) * (mvfderiv I a x v * mvfderiv I u x w +
          mvfderiv I a x w * mvfderiv I u x v -
          ⟪mgradient I a x, mgradient I u x⟫_ℝ * ⟪v, w⟫_ℝ)) := by
  rw [hessian_comp_ofWithMetric hn hu, hessian_comp_ofWithMetric hn hu]
  exact g.hessian_rescale_rpow hn ha ha_pos p hu.contMDiffAt v w

end TauCeti.WithMetric
