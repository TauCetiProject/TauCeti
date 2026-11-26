/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Conformal.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Weingarten

/-!
# The Weingarten map and mean curvature of the boundary under a conformal change

Let `M` be a manifold with boundary modelled on the half-space `𝓡∂ (n + 1)`, `g` a `C¹`
Riemannian metric on `M` and `ĝ = f g` its rescaling by a positive `C¹` function `f`. At a
boundary point `q`, write `c = (2 f q)⁻¹ df_q(ν_in)`, with `ν_in` the inward unit normal of `g`;
for `f = e^{2φ}`, `√(f q) = e^{φ(q)}` and `c = dφ_q(ν_in)`. Then:

* the Weingarten map changes by `S^ĝ_q = (√(f q))⁻¹ (S_q - c)`
  (`Bundle.ContMDiffRiemannianMetric.boundaryWeingarten_rescale`), so every principal direction of
  `g` with principal curvature `κ` is an eigenvector of `S^ĝ_q` with eigenvalue
  `(√(f q))⁻¹ (κ - c)`
  (`Bundle.ContMDiffRiemannianMetric.boundaryWeingarten_rescale_boundaryPrincipalDirection`);
  for `f = e^{2φ}` the eigenvalue is `e^{-φ} (κ - dφ(ν_in))`;
* for `n ≥ 1` the mean curvature changes by `H^ĝ(q) = (√(f q))⁻¹ (H(q) - c)`
  (`Bundle.ContMDiffRiemannianMetric.boundaryMeanCurvature_rescale`); for `f = e^{2φ}` this is
  `H^ĝ = e^{-φ} (H - dφ(ν_in))`.

All follow from the conformal laws of the induced metric and the second fundamental form,
`Bundle.ContMDiffRiemannianMetric.boundaryInducedForm_rescale` and
`Bundle.ContMDiffRiemannianMetric.boundarySecondFundamentalForm_rescale`, and the uniqueness of the
Weingarten map `TauCeti.eq_boundaryWeingarten_iff`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 7 and 8.
-/

public section

noncomputable section

open Bundle TauCeti
open scoped Manifold ContDiff InnerProductSpace

namespace Bundle.ContMDiffRiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] {k : ℕ∞ω} [IsManifold (𝓡∂ (n + 1)) 2 M]
  (g : ContMDiffRiemannianMetric (𝓡∂ (n + 1)) k (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x))
  {f : M → ℝ} (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) k f) (hf_pos : ∀ x, 0 < f x)

/-- **The Weingarten map of the boundary under a rescaling.** For `ĝ = f g` with `f` positive and
`C¹` and a `C¹` metric `g`, at `q ∈ ∂M`, `S^ĝ_q = (√(f q))⁻¹ (S_q - (2 f q)⁻¹ df_q(ν_in))`, where
`ν_in` is the inward unit normal of `g`. For `f = e^{2φ}` this is
`S^ĝ_q = e^{-φ(q)} (S_q - dφ_q(ν_in))`. -/
theorem boundaryWeingarten_rescale (hk : 1 ≤ k) (q : (𝓡∂ (n + 1)).boundary M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
      boundaryWeingarten q) =
    (√(f q))⁻¹ • ((letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
          ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
          (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
        boundaryWeingarten q) -
      ((2 * f q)⁻¹ * mvfderiv (𝓡∂ (n + 1)) f q
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
            ⟨g.toRiemannianMetric⟩; inwardUnitNormal q)) • LinearMap.id) := by
  set c := (2 * f q)⁻¹ * mvfderiv (𝓡∂ (n + 1)) f q
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨g.toRiemannianMetric⟩; inwardUnitNormal q)
  set S := (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨g.toRiemannianMetric⟩;
    letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
    boundaryWeingarten q)
  -- The defining property of `S` and the bilinearity of `h`, for `g`.
  have hS (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
          ⟨g.toRiemannianMetric⟩; boundaryInducedForm q
            (((√(f q))⁻¹ • (S - c • (LinearMap.id : Module.End ℝ
              (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q)))) u) w) =
        (√(f q))⁻¹ * ((letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
            ⟨g.toRiemannianMetric⟩;
          letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
            (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
          boundarySecondFundamentalForm q u w) -
          c * g.inner q
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
              (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
              (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w)) := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, map_smul, map_sub,
      smul_eq_mul]
    rw [boundaryInducedForm_boundaryWeingarten, boundaryInducedForm_apply, inner_riemannianBundle]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk
  refine ((eq_boundaryWeingarten_iff q _).2 fun u w ↦ ?_).symm
  rw [boundaryInducedForm_rescale g hf hf_pos, hS, boundarySecondFundamentalForm_rescale g hf hf_pos
    hk q u w]
  have hs : 0 < √(f q) := Real.sqrt_pos.2 (hf_pos q)
  have hf' : f q = √(f q) ^ 2 := (Real.sq_sqrt (hf_pos q).le).symm
  simp only [c]
  generalize √(f q) = s at hs hf' ⊢
  rw [hf']
  field_simp

/-- **Principal directions under a rescaling.** For `ĝ = f g`, every principal direction `e` of `g`
at `q ∈ ∂M`, with principal curvature `κ`, is an eigenvector of the Weingarten map of `ĝ` with
eigenvalue `(√(f q))⁻¹ (κ - (2 f q)⁻¹ df_q(ν_in))`. For `f = e^{2φ}` the eigenvalue is
`e^{-φ(q)} (κ - dφ_q(ν_in))`. -/
theorem boundaryWeingarten_rescale_boundaryPrincipalDirection (hk : 1 ≤ k)
    (q : (𝓡∂ (n + 1)).boundary M) (i : Fin n) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
      boundaryWeingarten q) (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
          ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
          (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
        boundaryPrincipalDirection q i) =
    ((√(f q))⁻¹ * ((letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
          ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
          (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
        boundaryPrincipalCurvatures q i) -
      (2 * f q)⁻¹ * mvfderiv (𝓡∂ (n + 1)) f q
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
            ⟨g.toRiemannianMetric⟩; inwardUnitNormal q))) •
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
          ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
          (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
        boundaryPrincipalDirection q i) := by
  rw [boundaryWeingarten_rescale g hf hf_pos hk q]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
    boundaryWeingarten_boundaryPrincipalDirection, ← sub_smul, smul_smul]

/-- **The mean curvature of the boundary under a rescaling.** For `ĝ = f g` and `n ≥ 1`, at
`q ∈ ∂M`, `H^ĝ(q) = (√(f q))⁻¹ (H(q) - (2 f q)⁻¹ df_q(ν_in))`. For `f = e^{2φ}` this is
`H^ĝ = e^{-φ(q)} (H - dφ_q(ν_in))`. -/
theorem boundaryMeanCurvature_rescale (hk : 1 ≤ k) (hn : n ≠ 0) (q : (𝓡∂ (n + 1)).boundary M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
      boundaryMeanCurvature q) =
    (√(f q))⁻¹ * ((letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
          ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
          (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := IsContMDiffRiemannianBundle.of_le hk;
        boundaryMeanCurvature q) -
      (2 * f q)⁻¹ * mvfderiv (𝓡∂ (n + 1)) f q
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
            ⟨g.toRiemannianMetric⟩; inwardUnitNormal q)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  -- The tangent space of the boundary at `q` is by definition the model space `ℝⁿ`, so the
  -- trace of the identity on it is `n`.
  have hdim : Module.finrank ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) = n :=
    finrank_euclideanSpace_fin
  simp only [boundaryMeanCurvature_def]
  rw [boundaryWeingarten_rescale g hf hf_pos hk q, map_smul, map_sub, map_smul,
    LinearMap.trace_id, hdim, smul_eq_mul, smul_eq_mul]
  field_simp

end Bundle.ContMDiffRiemannianMetric
