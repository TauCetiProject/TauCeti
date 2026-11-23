/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.PointwiseBounds
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian.MaximumPrinciple
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear

/-!
# The projected Weitzenböck inequalities at large parameter

On a symplectic four-manifold Taubes writes the normalized spinor of a solution of the
large-parameter Seiberg–Witten equations as `χ = φ + β`, where `φ = α u₀` lies in the canonical
line of the positive spinors and `β` in its orthogonal complement. Combining the Weitzenböck
formula for the Dirac equation with the curvature equation gives an equation of Ginzburg–Landau
type for the whole spinor,

`∇*∇χ + (r / 4) (|χ|² - 1) χ + (r / 2) β + ρ = 0`,   `|ρ| ≤ K |χ|`,

where `ρ` collects the scalar curvature, the curvature of the canonical connection and the forcing;
the zeroth-order algebra behind this form is in
`TauCeti.Analysis.PDE.SeibergWitten.LargeParameter.Weitzenbock`. The canonical line is the image of
a field of self-adjoint endomorphisms `P` (Clifford multiplication by the symplectic form, suitably
normalized), with `P φ = φ` and `P β = 0`. When the almost complex structure is not integrable, the
almost-Kähler metric is not Kähler, the symplectic form is not parallel and neither is `P`, so the
projections of the equation onto the two summands are coupled through the derivatives of `P`.

This file derives from the vector equation Taubes's two scalar differential inequalities
(`TauCeti.SeibergWitten.neg_laplaceBeltrami_norm_sq_div_two_add_le_canonical`,
`TauCeti.SeibergWitten.neg_laplaceBeltrami_norm_sq_div_two_add_le_complement`):

`-Δ|φ|² / 2 + |∇φ|² + (r / 4) (|φ|² + |β|² - 1) |φ|² ≤ c |φ| (|∇β| + |φ| + |β|)`,
`-Δ|β|² / 2 + |∇β|² + (r / 4) (|φ|² + |β|² + 1) |β|² ≤ c |β| (|∇φ| + |φ| + |β|)`,

with `Δ = div ∘ grad` (`TauCeti.Manifold.laplaceBeltrami`), operator norms of the covariant
derivatives, and `c = 2 n c₁ + c₂ + K` for `n = dim M`, where `c₁ ≥ sup |∇P|` and
`c₂ ≥ sup |∇*∇P|` are uniform bounds, so that `c` is a constant independent of `r`. These
are exactly the hypotheses of the maximum-principle bounds of
`TauCeti.Analysis.PDE.SeibergWitten.PointwiseBounds`; for instance Taubes's bound
`|β|² ≤ (4 c² / r) (1 - |φ|²) + O(r⁻²)` on a closed manifold follows
(`TauCeti.SeibergWitten.norm_sq_le_div_mul_one_sub_add_div_sq_of_roughLaplacian_add_eq_zero`).

The derivation pairs the equation with `φ` and `β` and uses
`-Δ|σ|² / 2 + ∑ᵢ |∇_{eᵢ}σ|² = ⟪∇*∇σ, σ⟫` for an orthonormal basis `eᵢ`
(`CovariantDerivative.IsMetricCompatible.laplaceBeltrami_norm_sq`), together with
`|∇σ|² ≤ ∑ᵢ |∇_{eᵢ}σ|²` for the operator norm
(`ContinuousLinearMap.opNorm_sq_le_sum_norm_apply_sq_orthonormalBasis`). Since `⟪φ, β⟫ = 0`, the
term `(r / 2) β` drops out of the pairing with `φ`. The cross terms `⟪∇*∇β, φ⟫` and `⟪∇*∇φ, β⟫`
are of lower order: as `P β = 0`, the Leibniz rule
`∇*∇(P β) = (∇*∇P) β - 2 ∑ᵢ (∇_{eᵢ} P)(∇_{eᵢ} β) + P (∇*∇β)`
(`CovariantDerivative.roughLaplacian_clm_apply`) shows that `P (∇*∇β)`, the only part of `∇*∇β`
seen by `φ = P φ`, is first order in `β` with coefficients the derivatives of `P`. Symmetrically
`∇*∇φ - P (∇*∇φ)` is first order in `φ`.

## Main results

All in the namespace `TauCeti.SeibergWitten`:

* `neg_laplaceBeltrami_norm_sq_div_two_add_le_canonical`: the projected inequality for `|φ|²`.
* `neg_laplaceBeltrami_norm_sq_div_two_add_le_complement`: the projected inequality for `|β|²`.
* `norm_sq_le_div_mul_one_sub_add_div_sq_of_roughLaplacian_add_eq_zero`: Taubes's bound
  `|β|² ≤ (4 c² / r) (1 - |φ|²) + O(r⁻²)` for solutions of the vector equation on a closed
  manifold.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 2.
* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
-/

public section

open Bundle CovariantDerivative Module TauCeti.Manifold
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]
  {cov : _root_.CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]
  {P : Π x : M, V x →L[ℝ] V x} {φ β ρ : Π x : M, V x} {r K c₁ c₂ : ℝ}

omit [IsContMDiffRiemannianBundle I ∞ F V] in
/-- **The commutator of the rough Laplacian with `P`, paired with a vector.** For a smooth section
`s` and a vector `w`, the pairing of `∇*∇(P s) - P (∇*∇s)` with `w` is at most
`|w| (|∇*∇P| |s| + 2 n |∇P| |∇s|)`. -/
private theorem inner_roughLaplacian_clm_apply_sub_le
    (hP : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun z ↦ V z →L[ℝ] V z) y (P y)))
    (hP₁ : ∀ x, ‖cov.hom cov P x‖ ≤ c₁)
    (hP₂ : ∀ x, ‖(cov.hom cov).roughLaplacian (leviCivitaConnection I M) P x‖ ≤ c₂)
    {s : Π x : M, V x} (hs : CMDiff ∞ (T% s)) (x : M) (w : V x) :
    |⟪cov.roughLaplacian (leviCivitaConnection I M) (fun y ↦ P y (s y)) x -
        P x (cov.roughLaplacian (leviCivitaConnection I M) s x), w⟫| ≤
      ‖w‖ * (c₂ * ‖s x‖ + 2 * finrank ℝ E * c₁ * ‖cov s x‖) := by
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [mul_comm ‖w‖]
  gcongr
  refine (norm_roughLaplacian_clm_apply_sub_le _ cov cov hP hs x).trans ?_
  gcongr
  · exact hP₂ x
  · exact hP₁ x

omit [IsContMDiffRiemannianBundle I ∞ F V] in
/-- The bounds `|∇P| ≤ c₁` and `|∇*∇P| ≤ c₂` at a point force `0 ≤ c₁` and `0 ≤ c₂`. -/
private theorem nonneg_of_norm_hom_le
    (hP₁ : ∀ x, ‖cov.hom cov P x‖ ≤ c₁)
    (hP₂ : ∀ x, ‖(cov.hom cov).roughLaplacian (leviCivitaConnection I M) P x‖ ≤ c₂) (x : M) :
    0 ≤ c₁ ∧ 0 ≤ c₂ :=
  ⟨(ContinuousLinearMap.opNorm_nonneg _).trans (hP₁ x), (norm_nonneg _).trans (hP₂ x)⟩

omit [TopologicalSpace M] [T2Space M] in
/-- The forcing term `ρ`, with `|ρ| ≤ K |φ + β|`, pairs with a vector `w` to at least
`-K (|φ| + |β|) |w|`. -/
private theorem neg_mul_le_inner_of_norm_le (hK : 0 ≤ K)
    (hρ : ∀ x, ‖ρ x‖ ≤ K * ‖φ x + β x‖) (x : M) (w : V x) :
    -(K * (‖φ x‖ + ‖β x‖) * ‖w‖) ≤ ⟪ρ x, w⟫ := by
  refine le_trans ?_ (neg_le_of_abs_le (abs_real_inner_le_norm _ _))
  gcongr
  exact (hρ x).trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) hK)

variable (hcov : cov.IsMetricCompatible)
  (hP : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
    (fun y ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun z ↦ V z →L[ℝ] V z) y (P y)))
  (hPadj : ∀ x u v, ⟪P x u, v⟫ = ⟪u, P x v⟫)
  (hP₁ : ∀ x, ‖cov.hom cov P x‖ ≤ c₁)
  (hP₂ : ∀ x, ‖(cov.hom cov).roughLaplacian (leviCivitaConnection I M) P x‖ ≤ c₂)
  (hφ : CMDiff ∞ (T% φ)) (hβ : CMDiff ∞ (T% β))
  (hPφ : ∀ x, P x (φ x) = φ x) (hPβ : ∀ x, P x (β x) = 0)
  (hK : 0 ≤ K) (hρ : ∀ x, ‖ρ x‖ ≤ K * ‖φ x + β x‖)
  (heq : ∀ x, cov.roughLaplacian (leviCivitaConnection I M) (φ + β) x +
    (r / 4 * (‖φ x + β x‖ ^ 2 - 1)) • (φ x + β x) + (r / 2) • β x + ρ x = 0)
include hcov hP hPadj hP₁ hP₂ hφ hβ hPφ hPβ hK hρ heq

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V]
  hcov hP hPadj hP₁ hP₂ hPφ hPβ hK hρ in
/-- The pairing of the equation with a vector `w`, with the rough Laplacian of `χ = φ + β` split
into those of `φ` and `β`. -/
private theorem inner_roughLaplacian_add (x : M) (w : V x) :
    ⟪cov.roughLaplacian (leviCivitaConnection I M) φ x, w⟫ +
        ⟪cov.roughLaplacian (leviCivitaConnection I M) β x, w⟫ +
          r / 4 * (‖φ x + β x‖ ^ 2 - 1) * (⟪φ x, w⟫ + ⟪β x, w⟫) + r / 2 * ⟪β x, w⟫ +
            ⟪ρ x, w⟫ = 0 := by
  have h := congrArg (⟪·, w⟫) (heq x)
  simpa only [roughLaplacian_add _ _ hφ hβ, inner_add_left, inner_smul_left, inner_zero_left,
    RCLike.conj_to_real] using h

/-- **The projected Weitzenböck inequality for the canonical component.** If `χ = φ + β` solves
`∇*∇χ + (r / 4) (|χ|² - 1) χ + (r / 2) β + ρ = 0` with `|ρ| ≤ K |χ|`, where `P φ = φ` and
`P β = 0` for a smooth field `P` of self-adjoint endomorphisms with `|∇P| ≤ c₁` and
`|∇*∇P| ≤ c₂`, then
`-Δ|φ|² / 2 + |∇φ|² + (r / 4) (|φ|² + |β|² - 1) |φ|² ≤ c |φ| (|∇β| + |φ| + |β|)`
with `c = 2 n c₁ + c₂ + K`, `n = dim M`. -/
theorem neg_laplaceBeltrami_norm_sq_div_two_add_le_canonical (x : M) :
    -laplaceBeltrami I (fun y ↦ ‖φ y‖ ^ 2) x / 2 + ‖cov φ x‖ ^ 2 +
        r / 4 * (‖φ x‖ ^ 2 + ‖β x‖ ^ 2 - 1) * ‖φ x‖ ^ 2 ≤
      (2 * finrank ℝ E * c₁ + c₂ + K) * ‖φ x‖ * (‖cov β x‖ + ‖φ x‖ + ‖β x‖) := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  -- The two components are orthogonal, since `P` is self-adjoint.
  have horth : ⟪β x, φ x⟫ = 0 := by rw [← hPφ x, ← hPadj, hPβ x, inner_zero_left]
  have horth' : ⟪φ x, β x⟫ = 0 := by rw [real_inner_comm, horth]
  -- `-Δ|φ|² / 2 + |∇φ|² ≤ ⟪∇*∇φ, φ⟫`, as the operator norm is at most the
  -- Hilbert–Schmidt norm.
  have hΔ := hcov.laplaceBeltrami_norm_sq hφ x b
  have hop := (cov φ x).opNorm_sq_le_sum_norm_apply_sq_orthonormalBasis b
  -- The equation paired with `φ`; the term `(r / 2) β` drops out.
  have hpair := inner_roughLaplacian_add hφ hβ heq x (φ x)
  rw [real_inner_self_eq_norm_sq, horth, norm_add_sq_real, horth'] at hpair
  -- The cross term `⟪∇*∇β, φ⟫ = ⟪P (∇*∇β), φ⟫` is first order in `β`, since `∇*∇(P β) = 0`.
  have hcross := inner_roughLaplacian_clm_apply_sub_le hP hP₁ hP₂ hβ x (φ x)
  rw [show (fun y ↦ P y (β y)) = 0 from funext hPβ, roughLaplacian_zero, zero_sub,
    inner_neg_left, abs_neg, hPadj, hPφ] at hcross
  have hρφ := neg_mul_le_inner_of_norm_le hK hρ x (φ x)
  obtain ⟨hc₁, hc₂⟩ := nonneg_of_norm_hom_le hP₁ hP₂ x
  have hcb := (abs_le.1 hcross).1
  nlinarith [norm_nonneg (φ x), norm_nonneg (β x), norm_nonneg (cov β x),
    mul_nonneg (mul_nonneg hc₁ (norm_nonneg (φ x))) (add_nonneg (norm_nonneg (φ x))
      (norm_nonneg (β x))),
    mul_nonneg (mul_nonneg hc₂ (norm_nonneg (φ x))) (add_nonneg (norm_nonneg (cov β x))
      (norm_nonneg (φ x))),
    mul_nonneg (mul_nonneg hK (norm_nonneg (φ x))) (norm_nonneg (cov β x)),
    (Nat.cast_nonneg (finrank ℝ E) : (0 : ℝ) ≤ finrank ℝ E)]

/-- **The projected Weitzenböck inequality for the complementary component.** Under the hypotheses
of `TauCeti.SeibergWitten.neg_laplaceBeltrami_norm_sq_div_two_add_le_canonical`,
`-Δ|β|² / 2 + |∇β|² + (r / 4) (|φ|² + |β|² + 1) |β|² ≤ c |β| (|∇φ| + |φ| + |β|)`
with `c = 2 n c₁ + c₂ + K`, `n = dim M`. -/
theorem neg_laplaceBeltrami_norm_sq_div_two_add_le_complement (x : M) :
    -laplaceBeltrami I (fun y ↦ ‖β y‖ ^ 2) x / 2 + ‖cov β x‖ ^ 2 +
        r / 4 * (‖φ x‖ ^ 2 + ‖β x‖ ^ 2 + 1) * ‖β x‖ ^ 2 ≤
      (2 * finrank ℝ E * c₁ + c₂ + K) * ‖β x‖ * (‖cov φ x‖ + ‖φ x‖ + ‖β x‖) := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have horth : ⟪φ x, β x⟫ = 0 := by rw [← hPφ x, hPadj, hPβ x, inner_zero_right]
  have hΔ := hcov.laplaceBeltrami_norm_sq hβ x b
  have hop := (cov β x).opNorm_sq_le_sum_norm_apply_sq_orthonormalBasis b
  -- The equation paired with `β`.
  have hpair := inner_roughLaplacian_add hφ hβ heq x (β x)
  rw [real_inner_self_eq_norm_sq, horth, norm_add_sq_real, horth] at hpair
  -- The cross term `⟪∇*∇φ, β⟫ = ⟪∇*∇φ - P (∇*∇φ), β⟫` is first order in `φ`, since `P φ = φ`.
  have hcross := inner_roughLaplacian_clm_apply_sub_le hP hP₁ hP₂ hφ x (β x)
  rw [show (fun y ↦ P y (φ y)) = φ from funext hPφ, inner_sub_left, hPadj, hPβ,
    inner_zero_right, sub_zero] at hcross
  have hρβ := neg_mul_le_inner_of_norm_le hK hρ x (β x)
  obtain ⟨hc₁, hc₂⟩ := nonneg_of_norm_hom_le hP₁ hP₂ x
  have hcb := (abs_le.1 hcross).1
  nlinarith [norm_nonneg (φ x), norm_nonneg (β x), norm_nonneg (cov φ x),
    mul_nonneg (mul_nonneg hc₁ (norm_nonneg (β x))) (add_nonneg (norm_nonneg (φ x))
      (norm_nonneg (β x))),
    mul_nonneg (mul_nonneg hc₂ (norm_nonneg (β x))) (add_nonneg (norm_nonneg (cov φ x))
      (norm_nonneg (β x))),
    mul_nonneg (mul_nonneg hK (norm_nonneg (β x))) (norm_nonneg (cov φ x)),
    (Nat.cast_nonneg (finrank ℝ E) : (0 : ℝ) ≤ finrank ℝ E)]

/-- **Taubes's bound `|β|² ≤ (4 c² / r) (1 - |φ|²) + O(r⁻²)` from the vector equation.** On a closed
Riemannian manifold, under the hypotheses of
`TauCeti.SeibergWitten.neg_laplaceBeltrami_norm_sq_div_two_add_le_canonical`, for every
`c ≥ 2 n c₁ + c₂ + K` and `r ≥ max 1 (max (32 c) (c² + 8 c))`,
`|β|² ≤ (4 c² / r) (1 - |φ|²) + (128 c² + 128 c³ + 4 c⁴ + 64 c⁶) / r²` everywhere. -/
theorem norm_sq_le_div_mul_one_sub_add_div_sq_of_roughLaplacian_add_eq_zero [CompactSpace M]
    [I.Boundaryless] {c : ℝ} (hc : 2 * finrank ℝ E * c₁ + c₂ + K ≤ c) (hr1 : 1 ≤ r)
    (hr32 : 32 * c ≤ r) (hrK : c ^ 2 + 8 * c ≤ r) (x : M) :
    ‖β x‖ ^ 2 ≤ 4 * c ^ 2 / r * (1 - ‖φ x‖ ^ 2) +
      (128 * c ^ 2 + 128 * c ^ 3 + 4 * c ^ 4 + 64 * c ^ 6) / r ^ 2 := by
  obtain ⟨hc₁, hc₂⟩ := nonneg_of_norm_hom_le hP₁ hP₂ x
  have hc0 : 0 ≤ c := le_trans (by positivity) hc
  have hsq {σ : Π x : M, V x} (hσ : CMDiff ∞ (T% σ)) : ContMDiff I 𝓘(ℝ) 2 fun y ↦ ‖σ y‖ ^ 2 := by
    simp_rw [← real_inner_self_eq_norm_sq]
    exact (hσ.inner_bundle hσ).of_le (by simp)
  refine norm_sq_le_div_mul_one_sub_add_div_sq (Dα := cov φ) (Dβ := cov β) hc0 hr1 hr32 hrK
    (hsq hφ) (hsq hβ) (fun y ↦ ?_) (fun y ↦ ?_) x
  · refine (neg_laplaceBeltrami_norm_sq_div_two_add_le_canonical hcov hP hPadj hP₁ hP₂ hφ hβ hPφ
      hPβ hK hρ heq y).trans ?_
    gcongr
  · refine (neg_laplaceBeltrami_norm_sq_div_two_add_le_complement hcov hP hPadj hP₁ hP₂ hφ hβ
      hPφ hPβ hK hρ heq y).trans ?_
    gcongr

end TauCeti.SeibergWitten
