/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm.Smooth
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Weingarten.Basic

/-!
# Smoothness of the Weingarten map and the mean curvature of the boundary

Let `M` be a Riemannian manifold with boundary modelled on the half-space `𝓡∂ (n + 1)`, on a
`C^(k + 2)` manifold with a `C^(k + 1)` metric. The second fundamental form `II` of the boundary is
then a `C^k` section of the bundle of bilinear forms on `T∂M`
(`TauCeti.contMDiffAt_boundarySecondFundamentalForm_apply`). This file shows that the same holds for
the quantities built from `II` and the induced metric `h`:

* the Weingarten map `S` is a `C^k` section of the bundle of endomorphisms of `T∂M`: it carries a
  tangent field `U` of the boundary manifold that is `C^k` at `q₀` to the field `q ↦ S_q (U q)`,
  again `C^k` at `q₀` (`TauCeti.contMDiffAt_boundaryWeingarten_apply`);
* the mean curvature `H` is a `C^k` function on `∂M` (`TauCeti.contMDiffAt_boundaryMeanCurvature`).

Near every point the boundary carries tangent fields `e₁, …, eₙ` that are `C^k` and orthonormal
for `h` (`TauCeti.exists_contMDiffAt_boundaryInducedForm_orthonormal`). In such a frame
`S_q u = ∑ᵢ II_q(u, eᵢ) eᵢ` (`TauCeti.boundaryWeingarten_apply_eq_sum`) and
`n H = ∑ᵢ II_q(eᵢ, eᵢ)` (`TauCeti.sum_boundarySecondFundamentalForm_eq_mul_boundaryMeanCurvature`),
whose terms are `C^k`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 8.
-/

public section

noncomputable section

open Bundle Filter InnerProductSpace
open scoped Manifold ContDiff InnerProductSpace Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  {k m l : ℕ∞ω} [IsManifold (𝓡∂ (n + 1)) m M]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) l (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M)]

/-- **The Weingarten map of the boundary is a `C^k` section** of the bundle of endomorphisms of
`T∂M`, on a `C^(k + 2)` manifold with a `C^(k + 1)` metric: it carries a tangent field `U` of the
boundary manifold that is `C^k` at `q₀` to the field `q ↦ S_q (U q)`, again `C^k` at `q₀`. -/
theorem contMDiffAt_boundaryWeingarten_apply (hm : k + 2 ≤ m) (hl : k + 1 ≤ l)
    {U : (q : (𝓡∂ (n + 1)).boundary M) → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q}
    {q₀ : (𝓡∂ (n + 1)).boundary M}
    (hU : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).tangent k
      (T% U) q₀) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).tangent k
      (T% (fun q ↦ boundaryWeingarten q (U q))) q₀ := by
  have hm1 : k + 1 ≤ m := (add_le_add_right (by norm_num : (1 : ℕ∞ω) ≤ 2) k).trans hm
  obtain ⟨e, he, hon⟩ :=
    exists_contMDiffAt_boundaryInducedForm_orthonormal hm1 (le_self_add.trans hl) q₀
  -- `S_q (U q) = ∑ᵢ II_q(U q, eᵢ q) eᵢ q` near `q₀`.
  have hsum := ContMDiffAt.sum_section (s := Finset.univ) (t := fun i q ↦
    boundarySecondFundamentalForm q (U q) (e i q) • e i q) fun i _ ↦
      (contMDiffAt_boundarySecondFundamentalForm_apply hm hl hU (he i)).smul_section (he i)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hon] with q hq
  rw [boundaryWeingarten_apply_eq_sum q (fun i ↦ e i q) hq]

/-- **The Weingarten map of the boundary is a `C^k` section**: for a `C^k` tangent field `U` of the
boundary manifold, `q ↦ S_q (U q)` is `C^k`, on a `C^(k + 2)` manifold with a `C^(k + 1)`
metric. -/
theorem contMDiff_boundaryWeingarten_apply (hm : k + 2 ≤ m) (hl : k + 1 ≤ l)
    {U : (q : (𝓡∂ (n + 1)).boundary M) → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q}
    (hU : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).tangent k
      (T% U)) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).tangent k
      (T% (fun q ↦ boundaryWeingarten q (U q))) := fun q₀ ↦
  contMDiffAt_boundaryWeingarten_apply hm hl (hU q₀)

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M)]

/-- **The mean curvature of the boundary is `C^k`** at every point, on a `C^(k + 2)` manifold with
a `C^(k + 1)` metric. -/
theorem contMDiffAt_boundaryMeanCurvature (hm : k + 2 ≤ m) (hl : k + 1 ≤ l)
    (q₀ : (𝓡∂ (n + 1)).boundary M) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) k
      (boundaryMeanCurvature (n := n) (M := M)) q₀ := by
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M) :=
    isManifold_boundary M
  have hm1 : k + 1 ≤ m := (add_le_add_right (by norm_num : (1 : ℕ∞ω) ≤ 2) k).trans hm
  obtain ⟨e, he, hon⟩ :=
    exists_contMDiffAt_boundaryInducedForm_orthonormal hm1 (le_self_add.trans hl) q₀
  -- `n H(q) = ∑ᵢ II_q(eᵢ q, eᵢ q)` near `q₀`.
  have hsum : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) k
      (fun q ↦ (n : ℝ)⁻¹ * ∑ i, boundarySecondFundamentalForm q (e i q) (e i q)) q₀ :=
    contMDiffAt_const.mul (contMDiffAt_finsetSum fun i _ ↦
      contMDiffAt_boundarySecondFundamentalForm_apply hm hl (he i) (he i))
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hon] with q hq
  rw [sum_boundarySecondFundamentalForm_eq_mul_boundaryMeanCurvature q (fun i ↦ e i q) hq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [boundaryMeanCurvature_def]
  · rw [inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 hn)]

/-- **The mean curvature of the boundary is a `C^k` function**, on a `C^(k + 2)` manifold with a
`C^(k + 1)` metric. -/
theorem contMDiff_boundaryMeanCurvature (hm : k + 2 ≤ m) (hl : k + 1 ≤ l) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) k (boundaryMeanCurvature (n := n) (M := M)) :=
  contMDiffAt_boundaryMeanCurvature hm hl

end TauCeti
