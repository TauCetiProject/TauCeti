/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Uniform

/-!
# Normal charts for rescaled exponential maps

Let `K` be a compact set of points of a Riemannian manifold `M` and let `λ_j → ∞` be a family of
scales. For an orthonormal frame `e : F ≃ₗᵢ[ℝ] T_p M` at a point `p ∈ K`, consider the rescaled
exponential map `x ↦ exp_p (λ_j⁻¹ • e x)` on the model space `F`. For every radius `R`, these maps
are eventually partial diffeomorphisms with source exactly the Euclidean ball of radius `R`,
uniformly over all centres `p ∈ K` and all frames `e`. In particular, for `R = L + 1` they are
diffeomorphisms onto their images on a neighbourhood of the closed ball of radius `L`.

The proof uses a single normal radius for all points of `K`,
`IsCompact.exists_pos_exists_isOpen_superset_forall_isNormalDomain_ball`.

See J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 6.
-/

public section

open Bundle Filter Metric Set
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Rescaled normal charts.** For scales `λ_j → ∞` and every radius `R`, the rescaled
exponential maps `x ↦ exp_p (λ_j⁻¹ • e x)` are eventually partial diffeomorphisms with source the
Euclidean ball of radius `R`, simultaneously for all centres `p` of a compact set and all
orthonormal frames `e` at `p`. -/
theorem _root_.IsCompact.eventually_exists_partialDiffeomorph_riemannianExp_inv_smul
    {K : Set M} (hK : IsCompact K) {α : Type*} {l : Filter α} {scale : α → ℝ}
    (hscale : Tendsto scale l atTop) (R : ℝ) :
    ∀ᶠ j in l, ∀ p ∈ K, ∀ e : F ≃ₗᵢ[ℝ] TangentSpace I p,
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, F) I F M ∞,
        Φ.source = ball 0 R ∧ ⇑Φ = fun x ↦ riemannianExp I M p ((scale j)⁻¹ • e x) := by
  obtain ⟨r, hr, U, -, hKU, hnormal⟩ :=
    hK.exists_pos_exists_isOpen_superset_forall_isNormalDomain_ball (I := I)
  filter_upwards [hscale.eventually_gt_atTop 0, hscale.eventually_gt_atTop (R / r)]
    with j hj hjR p hp e
  let A : F ≃L[ℝ] TangentSpace I p :=
    e.toContinuousLinearEquiv.trans
      (LinearEquiv.smulOfNeZero ℝ (TangentSpace I p) (scale j)⁻¹
        (inv_ne_zero hj.ne')).toContinuousLinearEquiv
  have hA (x : F) : A x = (scale j)⁻¹ • e x := by simp [A]
  have hmap : MapsTo A (ball 0 R) (ball 0 r) := by
    intro x hx
    have hR : R < scale j * r := (div_lt_iff₀ hr).1 hjR
    simp only [mem_ball_zero_iff, hA, norm_smul, norm_inv, Real.norm_of_nonneg hj.le,
      LinearIsometryEquiv.norm_map, inv_mul_lt_iff₀ hj] at hx ⊢
    linarith
  obtain ⟨Φ, hsource, hΦ⟩ :=
    (hnormal p (hKU hp)).exists_partialDiffeomorph_riemannianExp_comp A isOpen_ball hmap
  exact ⟨Φ, hsource, hΦ.trans (funext fun x ↦ congrArg (riemannianExp I M p) (hA x))⟩

end TauCeti.Manifold
