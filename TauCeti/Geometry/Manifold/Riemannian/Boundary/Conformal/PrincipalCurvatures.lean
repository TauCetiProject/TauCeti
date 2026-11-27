/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Conformal.Weingarten

/-!
# The principal curvatures of the boundary under a conformal change

Let `M` be a manifold with boundary modelled on the half-space `𝓡∂ (n + 1)`, `g` a `C¹`
Riemannian metric on `M` and `ĝ = f g` its rescaling by a positive `C¹` function `f`. At a
boundary point `q`, write `c = (2 f q)⁻¹ df_q(ν_in)`, with `ν_in` the inward unit normal of `g`.
The Weingarten map changes by `S^ĝ_q = (√(f q))⁻¹ (S_q - c)`
(`Bundle.ContMDiffRiemannianMetric.boundaryWeingarten_rescale`). Since `x ↦ (√(f q))⁻¹ (x - c)`
is increasing, the principal curvatures of `ĝ`, listed in decreasing order, are
`κ^ĝᵢ = (√(f q))⁻¹ (κᵢ - c)` for the principal curvatures `κ₁ ≥ ⋯ ≥ κₙ` of `g`, with the same index
(`Bundle.ContMDiffRiemannianMetric.boundaryPrincipalCurvatures_rescale`). For `f = e^{2φ}` this is
`κ^ĝ = e^{-φ} (κ - dφ(ν_in))`.

The comparison rests on a characterisation of the principal curvatures that does not mention the
metric: they are the unique decreasing family `μ` for which some basis `(bᵢ)` of `T_q∂M` satisfies
`S_q bᵢ = μᵢ bᵢ` (`TauCeti.boundaryPrincipalCurvatures_eq_of_eigenbasis`). The principal basis of
`g` is such a basis for `S^ĝ_q`, although it is not orthonormal for `ĝ` unless `f q = 1`.

## Main statements

* `Bundle.ContMDiffRiemannianMetric.boundaryPrincipalCurvatures_rescale`:
  `κ^ĝᵢ = (√(f q))⁻¹ (κᵢ - (2 f q)⁻¹ df_q(ν_in))`.
* `Bundle.ContMDiffRiemannianMetric.boundaryPrincipalCurvatures_rescale_const`: for a constant
  `c > 0`, the principal curvatures of `c² g` are `κᵢ / c`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 7 and 8.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

/-! ### The conformal law -/

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] {k : ℕ∞ω} [IsManifold (𝓡∂ (n + 1)) 2 M]
  (g : ContMDiffRiemannianMetric (𝓡∂ (n + 1)) k (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x))
  {f : M → ℝ} (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) k f) (hf_pos : ∀ x, 0 < f x)

/-- **The principal curvatures of the boundary under a rescaling.** For `ĝ = f g` with `f`
positive and `C¹` and a `C¹` metric `g`, at `q ∈ ∂M`, the principal curvatures of `ĝ`, in
decreasing order, are `κ^ĝᵢ = (√(f q))⁻¹ (κᵢ - (2 f q)⁻¹ df_q(ν_in))`, where `κ₁ ≥ ⋯ ≥ κₙ` are those
of `g` and `ν_in` is the inward unit normal of `g`. For `f = e^{2φ}` this is
`κ^ĝᵢ = e^{-φ(q)} (κᵢ - dφ_q(ν_in))`. -/
theorem boundaryPrincipalCurvatures_rescale (hk : 1 ≤ k) (q : (𝓡∂ (n + 1)).boundary M)
    (i : Fin n) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
      boundaryPrincipalCurvatures q i) =
    (√(f q))⁻¹ * ((letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
          ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
          (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
        boundaryPrincipalCurvatures q i) -
      (2 * f q)⁻¹ * mvfderiv (𝓡∂ (n + 1)) f q
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
            ⟨g.toRiemannianMetric⟩; inwardUnitNormal q)) := by
  set c := (2 * f q)⁻¹ * mvfderiv (𝓡∂ (n + 1)) f q
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨g.toRiemannianMetric⟩; inwardUnitNormal q)
  set κ := (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨g.toRiemannianMetric⟩;
    letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
    boundaryPrincipalCurvatures q)
  set b := (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨g.toRiemannianMetric⟩;
    letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
    boundaryPrincipalBasis q)
  have hκ : Antitone κ := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk
    exact boundaryPrincipalCurvatures_antitone q
  have hb (j : Fin n) :
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
          (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
        boundaryWeingarten q) (b j) = ((√(f q))⁻¹ * (κ j - c)) • b j := by
    have hbj : b j = (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
      boundaryPrincipalDirection q j) := by
      simp only [b, coe_boundaryPrincipalBasis]
    rw [hbj]
    exact boundaryWeingarten_rescale_boundaryPrincipalDirection g hf hf_pos hk q j
  have hanti : Antitone fun j ↦ (√(f q))⁻¹ * (κ j - c) := fun i j hij ↦
    mul_le_mul_of_nonneg_left (sub_le_sub_right (hκ hij) c)
      (inv_nonneg.2 (Real.sqrt_nonneg _))
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk
  exact congrFun (boundaryPrincipalCurvatures_eq_of_eigenbasis q b hanti hb) i

/-- **Principal curvatures under a constant rescaling**: for a constant `c > 0`, the principal
curvatures of `c² g` are `κᵢ / c`. -/
theorem boundaryPrincipalCurvatures_rescale_const (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c)
    (q : (𝓡∂ (n + 1)).boundary M) (i : Fin n) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(g.rescale (fun _ ↦ c ^ 2) contMDiff_const fun _ ↦ pow_pos hc 2).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
      boundaryPrincipalCurvatures q i) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
          ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
          (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
        boundaryPrincipalCurvatures q i) / c := by
  rw [boundaryPrincipalCurvatures_rescale g _ _ hk q i]
  simp [mvfderiv_const, Real.sqrt_sq hc.le, div_eq_inv_mul]

end Bundle.ContMDiffRiemannianMetric
