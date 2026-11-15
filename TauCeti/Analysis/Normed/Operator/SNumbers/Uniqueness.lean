/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import TauCeti.Analysis.Normed.Operator.SNumbers.Approximation
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Compact
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Completion
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# Uniqueness of s-number sequences on inner product spaces

On Banach spaces the five classical s-number sequences (approximation, Gelfand, Kolmogorov,
Bernstein and Hilbert numbers) are pairwise distinct, with the approximation numbers at the top.
Between inner product spaces over `ℝ` or `ℂ`, every sequence satisfying Pietsch's five s-number
axioms collapses to the approximation numbers, and in finite dimension to the singular values.

* **Scalar factorization through `ℓ₂^{n+1}`.** For every bounded operator `T : H₁ →L[𝕜] H₂`
  between seminormed inner product spaces over `ℝ` or `ℂ` and every `0 ≤ c < aₙ(T)` there exist
  contractions `A : ℓ₂^{n+1} →L[𝕜] H₁` and `B : H₂ →L[𝕜] ℓ₂^{n+1}` with
  `B ∘L T ∘L A = c • id`. When `H₁` is complete and separated, the converse min–max localization
  supplies an `(n + 1)`-dimensional subspace `V ≤ H₁` on which `T` is `s`-coercive with `c < s`;
  `A` is an orthonormal parameterization of `V` and `B` is `c` times the inverse of `T ∘L A` on
  `T(V)` composed with the orthogonal projection onto `T(V)`. In the general incomplete or
  seminormed case, `T.completion` has the same approximation numbers as `T`, and perturbing the
  basis vectors of `A'` from `Completion H₁` into `H₁` produces an invertible endomorphism close to
  `c' • id` on `ℓ₂^{n+1}` whose inverse absorbs the perturbation into `B`.
* **Uniqueness on inner product spaces.** Every s-number sequence `s` satisfies `s T n ≤ aₙ(T)` on
  all normed spaces. Conversely, applying the two-sided ideal axiom, homogeneity and Euclidean
  normalization to `B ∘L T ∘L A = c • id` yields `c ≤ s T n` for every `0 ≤ c < aₙ(T)`, hence
  `s T n = aₙ(T)` with no completeness hypothesis on either space.
* **Singular values and compactness.** Combining uniqueness with the Eckart–Young theorem
  identifies `s T n` with Mathlib's `LinearMap.singularValues` in finite dimension, and combining
  it with the approximation-number compactness criterion shows that on inner product spaces with a
  complete codomain, `T` is compact if and only if `s T n → 0`.

## Main declarations

* `ContinuousLinearMap.exists_comp_comp_eq_smul_id`: for `0 ≤ c < aₙ(T)` between seminormed inner
  product spaces, `B ∘L T ∘L A = c • id` on `EuclideanSpace 𝕜 (Fin (n + 1))` with `‖A‖ ≤ 1` and
  `‖B‖ ≤ 1`.
* `TauCeti.SNumbers.IsSNumberSequence.eq_singularValue`: every s-number sequence agrees with the
  approximation numbers on bounded operators between inner product spaces.
* `TauCeti.SNumbers.IsSNumberSequence.eq_singularValues`: in finite dimension, every s-number
  sequence agrees with `LinearMap.singularValues`.
* `TauCeti.SNumbers.IsSNumberSequence.tendsto_nhds_zero_of_isCompactOperator`,
  `TauCeti.SNumbers.IsSNumberSequence.isCompactOperator_of_tendsto_nhds_zero`,
  `TauCeti.SNumbers.IsSNumberSequence.isCompactOperator_iff`: compactness criteria for s-number
  sequences on inner product spaces.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), Theorem 8.2.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), Theorem 2.11.9.
* C. Eckart, G. Young, *The approximation of one matrix by another of lower rank*,
  Psychometrika 1 (1936), 211–218.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/Uniqueness.lean`, `SNumbers/SingularValuesFinDim.lean`, `AddOns/Compact.lean`: an
  earlier Lean formalization of Hilbert-space uniqueness, finite-dimensional singular values and
  compactness for s-number sequences.
-/

public section

open Filter UniformSpace
open scoped InnerProductSpace NNReal Topology

namespace ContinuousLinearMap

section Factorization

/-- Scalar factorization through `EuclideanSpace 𝕜 (Fin (n + 1))` when `H₁` is a complete normed
inner product space and `H₂` is a normed inner product space. -/
private theorem exists_comp_comp_eq_smul_id_of_completeSpace {𝕜 H₁ H₂ : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < T.singularValue n) :
    ∃ (A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁)
      (B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ B ∘L T ∘L A = (c : 𝕜) • ContinuousLinearMap.id 𝕜 _ := by
  rcases hc0.eq_or_lt with rfl | hc_pos
  · exact ⟨0, 0, by simp, by simp, by ext; simp⟩
  obtain ⟨s, hcs, v, hv, hs⟩ :=
    TauCeti.hasMinMaxLowerBound_iff.mp TauCeti.HasMinMaxLowerBound.of_completeSpace T n hc0 hc
  have hs_pos : 0 < s := hc_pos.trans hcs
  set V : Submodule 𝕜 H₁ := Submodule.span 𝕜 (Set.range v)
  have : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  have hdim : Module.finrank 𝕜 V = n + 1 := by rw [finrank_span_eq_card hv, Fintype.card_fin]
  let e : OrthonormalBasis (Fin (n + 1)) 𝕜 V := (stdOrthonormalBasis 𝕜 V).reindex (finCongr hdim)
  let Aᵢ : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗᵢ[𝕜] H₁ := V.subtypeₗᵢ.comp e.repr.symm.toLinearIsometry
  let A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁ := Aᵢ.toContinuousLinearMap
  let F₀ : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₂ := T ∘L A
  have hcoerc (u : EuclideanSpace 𝕜 (Fin (n + 1))) : s * ‖u‖ ≤ ‖F₀ u‖ := by
    have hAu : A u ∈ V := (e.repr.symm u).2
    have hAnorm : ‖A u‖ = ‖u‖ := Aᵢ.norm_map u
    simpa only [F₀, comp_apply, hAnorm] using hs (A u) hAu
  have hF₀_inj : Function.Injective (F₀ : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] H₂) := by
    intro u₁ u₂ hu
    have hsub : F₀ (u₁ - u₂) = 0 := by rw [map_sub, sub_eq_zero]; exact hu
    have h0 : s * ‖u₁ - u₂‖ ≤ 0 := by simpa only [hsub, norm_zero] using hcoerc (u₁ - u₂)
    exact sub_eq_zero.mp
      (norm_eq_zero.mp (le_antisymm (nonpos_of_mul_nonpos_right h0 hs_pos) (norm_nonneg _)))
  set W : Submodule 𝕜 H₂ := LinearMap.range (F₀ : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] H₂)
  have : FiniteDimensional 𝕜 W := LinearMap.finiteDimensional_range _
  let eqv : EuclideanSpace 𝕜 (Fin (n + 1)) ≃ₗ[𝕜] W := LinearEquiv.ofInjective _ hF₀_inj
  let g : W →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
    LinearMap.toContinuousLinearMap eqv.symm.toLinearMap
  have hg_norm : ‖g‖ ≤ s⁻¹ := g.opNorm_le_bound (inv_nonneg.mpr hs_pos.le) fun w ↦ by
    have hw : F₀ (g w) = (w : H₂) := congrArg Subtype.val (eqv.apply_symm_apply w)
    rw [inv_mul_eq_div, le_div_iff₀' hs_pos]
    simpa only [hw, Submodule.norm_coe] using hcoerc (g w)
  let B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) := (c : 𝕜) • (g ∘L W.orthogonalProjectionOnto)
  refine ⟨A, B, Aᵢ.norm_toContinuousLinearMap_le, ?_, ContinuousLinearMap.ext fun u ↦ ?_⟩
  · dsimp only [B]
    calc ‖(c : 𝕜) • (g ∘L W.orthogonalProjectionOnto)‖
        = c * ‖g ∘L W.orthogonalProjectionOnto‖ := by
          rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hc0]
      _ ≤ c * (s⁻¹ * 1) := by
          gcongr
          exact (opNorm_comp_le _ _).trans
            (mul_le_mul hg_norm W.orthogonalProjectionOnto_norm_le (norm_nonneg _) (by positivity))
      _ ≤ 1 := by rw [mul_one, mul_inv_le_iff₀ hs_pos, one_mul]; exact hcs.le
  · have hproj : W.orthogonalProjectionOnto (T (A u)) = eqv u :=
      W.orthogonalProjectionOnto_mem_subspace_eq_self ⟨F₀ u, LinearMap.mem_range_self _ u⟩
    simp [B, g, hproj]

/-- Approximating the images of the standard basis under `A' : ℓ₂^{k} →L[𝕜] Completion H₁` inside
`H₁` produces an operator `A₀ : ℓ₂^{k} →L[𝕜] H₁` whose completion stays within `k * δ` of `A'`. -/
private theorem exists_sub_completion_le {𝕜 H₁ : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup H₁] [NormedSpace 𝕜 H₁] {k : ℕ}
    (A' : EuclideanSpace 𝕜 (Fin k) →L[𝕜] Completion H₁) (hA' : ‖A'‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A₀ : EuclideanSpace 𝕜 (Fin k) →L[𝕜] H₁, ‖A₀‖ ≤ 1 + k * δ ∧
      ∀ u, ‖(A₀ u : Completion H₁) - A' u‖ ≤ k * δ * ‖u‖ := by
  let b := EuclideanSpace.basisFun (Fin k) 𝕜
  choose v hv using fun i : Fin k ↦
    Metric.denseRange_iff.mp Completion.denseRange_coe (A' (b i)) δ hδ
  let A₀ : EuclideanSpace 𝕜 (Fin k) →L[𝕜] H₁ :=
    ∑ i : Fin k, (EuclideanSpace.proj i).smulRight (v i)
  have herr (u : EuclideanSpace 𝕜 (Fin k)) :
      ‖(A₀ u : Completion H₁) - A' u‖ ≤ k * δ * ‖u‖ := by
    have hu : A' u = ∑ i : Fin k, u i • A' (b i) := by
      simp_rw [← map_smul, ← map_sum]
      exact congrArg A' (b.sum_repr u).symm
    have hA₀u : (A₀ u : Completion H₁) = ∑ i : Fin k, u i • (v i : Completion H₁) := by
      simpa only [A₀, sum_apply, smulRight_apply, map_smul, Completion.coe_toComplL,
        PiLp.proj_apply] using map_sum (Completion.toComplL : H₁ →L[𝕜] Completion H₁)
        (fun i ↦ u i • v i) Finset.univ
    rw [hA₀u, hu, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i : Fin k, ‖u i • (v i : Completion H₁) - u i • A' (b i)‖
        ≤ ∑ _i : Fin k, ‖u‖ * δ := Finset.sum_le_sum fun i _ ↦ by
          rw [← smul_sub, norm_smul]
          exact mul_le_mul (PiLp.norm_apply_le u i)
            (by simpa [dist_eq_norm, norm_sub_rev] using (hv i).le) (norm_nonneg _) (norm_nonneg u)
      _ = k * δ * ‖u‖ := by simp [mul_assoc, mul_comm, mul_left_comm]
  refine ⟨A₀, A₀.opNorm_le_bound (by positivity) fun u ↦ ?_, herr⟩
  rw [← Completion.norm_coe]
  calc ‖(A₀ u : Completion H₁)‖
      ≤ ‖A' u‖ + ‖(A₀ u : Completion H₁) - A' u‖ := norm_le_insert' _ _
    _ ≤ 1 * ‖u‖ + k * δ * ‖u‖ := add_le_add ((A'.le_opNorm u).trans (by gcongr)) (herr u)
    _ = (1 + k * δ) * ‖u‖ := by ring

/-- If contractions `A` and `B₀` make the finite-dimensional endomorphism `B₀ ∘L T ∘L A` of
`EuclideanSpace 𝕜 (Fin k)` `c`-coercive (`c > 0`), post-composing `B₀` with `c` times its inverse
yields a contraction `B` with `B ∘L T ∘L A = c • id`. -/
private theorem exists_right_factor_of_coercive {𝕜 H₁ H₂ : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup H₁] [NormedSpace 𝕜 H₁]
    [SeminormedAddCommGroup H₂] [NormedSpace 𝕜 H₂] {k : ℕ}
    (T : H₁ →L[𝕜] H₂) (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] H₁)
    (B₀ : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin k)) (hA : ‖A‖ ≤ 1) (hB₀ : ‖B₀‖ ≤ 1)
    {c : ℝ} (hc_pos : 0 < c) (hcoerc : ∀ u, c * ‖u‖ ≤ ‖(B₀ ∘L T ∘L A) u‖) :
    ∃ (A₁ : EuclideanSpace 𝕜 (Fin k) →L[𝕜] H₁) (B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin k)),
      ‖A₁‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ B ∘L T ∘L A₁ = (c : 𝕜) • ContinuousLinearMap.id 𝕜 _ := by
  let S : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k) := B₀ ∘L T ∘L A
  have hS_inj :
      Function.Injective (S : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) := by
    intro u₁ u₂ hu
    have hsub : (B₀ ∘L T ∘L A) (u₁ - u₂) = 0 := by rw [map_sub, sub_eq_zero]; exact hu
    have h0 : c * ‖u₁ - u₂‖ ≤ 0 := by simpa only [hsub, norm_zero] using hcoerc (u₁ - u₂)
    exact sub_eq_zero.mp
      (norm_eq_zero.mp (le_antisymm (nonpos_of_mul_nonpos_right h0 hc_pos) (norm_nonneg _)))
  let eqv := LinearEquiv.ofInjectiveEndo
    (S : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) hS_inj
  let S_inv : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
    LinearMap.toContinuousLinearMap eqv.symm.toLinearMap
  have hS_inv : ‖(c : 𝕜) • S_inv‖ ≤ 1 := by
    refine opNorm_le_bound _ zero_le_one fun w ↦ ?_
    have hw : (B₀ ∘L T ∘L A) (S_inv w) = w := eqv.apply_symm_apply w
    rw [one_mul, smul_apply, norm_smul, RCLike.norm_ofReal, abs_of_pos hc_pos]
    simpa only [hw] using hcoerc (S_inv w)
  refine ⟨A, ((c : 𝕜) • S_inv) ∘L B₀, hA, ?_, ContinuousLinearMap.ext fun u ↦ ?_⟩
  · exact (opNorm_comp_le _ _).trans <|
      (mul_le_mul hS_inv hB₀ (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · have hu : S_inv (S u) = u := eqv.symm_apply_apply u
    simpa only [comp_apply, smul_apply, id_apply, S] using congrArg ((c : 𝕜) • ·) hu

/-- If `B' ∘L T.completion ∘L A' = (c' : 𝕜) • id` with `‖B'‖ ≤ 1` and `c' > 0`, and `A₀ u` stays
within `ε * ‖u‖` of `A' u` in `Completion H₁`, then `(B' ∘L toComplL) (T (A₀ u))` has norm at
least `(c' - ‖T‖ * ε) * ‖u‖`. -/
private theorem le_norm_comp_toComplL_apply {𝕜 E H₁ H₂ : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup H₁] [NormedSpace 𝕜 H₁]
    [SeminormedAddCommGroup H₂] [NormedSpace 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (A' : E →L[𝕜] Completion H₁) (B' : Completion H₂ →L[𝕜] E)
    (hB' : ‖B'‖ ≤ 1) {c' : ℝ} (hc' : 0 < c')
    (hfac' : B' ∘L T.completion ∘L A' = (c' : 𝕜) • ContinuousLinearMap.id 𝕜 E)
    (A₀ : E →L[𝕜] H₁) {ε : ℝ} (u : E) (herr : ‖(A₀ u : Completion H₁) - A' u‖ ≤ ε * ‖u‖) :
    (c' - ‖T‖ * ε) * ‖u‖ ≤ ‖(B' ∘L Completion.toComplL) (T (A₀ u))‖ := by
  have hdiff : (B' ∘L Completion.toComplL) (T (A₀ u)) - (c' : 𝕜) • u =
      B' (T.completion ((A₀ u : Completion H₁) - A' u)) := by
    have hfu := congrArg (· u) hfac'
    simp only [comp_apply, smul_apply, id_apply] at hfu
    simp [← hfu, map_sub]
  have hbound : ‖(B' ∘L Completion.toComplL) (T (A₀ u)) - (c' : 𝕜) • u‖ ≤ ‖T‖ * (ε * ‖u‖) := by
    rw [hdiff]
    calc ‖B' (T.completion ((A₀ u : Completion H₁) - A' u))‖
        ≤ ‖B'‖ * (‖T.completion‖ * ‖(A₀ u : Completion H₁) - A' u‖) :=
          (B'.le_opNorm _).trans (by gcongr; exact T.completion.le_opNorm _)
      _ ≤ 1 * (‖T‖ * (ε * ‖u‖)) := by
          rw [T.norm_completion]
          exact mul_le_mul hB' (mul_le_mul_of_nonneg_left herr (norm_nonneg T))
            (by positivity) zero_le_one
      _ = ‖T‖ * (ε * ‖u‖) := one_mul _
  have h := norm_le_insert' ((c' : 𝕜) • u) ((B' ∘L Completion.toComplL) (T (A₀ u)))
  rw [norm_sub_rev, norm_smul, RCLike.norm_ofReal, abs_of_pos hc'] at h
  linarith

/-- **Scalar factorization through Euclidean space.** For every bounded linear map
`T : H₁ →L[𝕜] H₂` between seminormed inner product spaces over `ℝ` or `ℂ` and every
`0 ≤ c < aₙ(T)` there exist contractions `A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁` and
`B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))` such that `B ∘L T ∘L A = c • id`. Neither `H₁` nor
`H₂` needs to be complete or separated. -/
theorem exists_comp_comp_eq_smul_id {𝕜 H₁ H₂ : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [SeminormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < T.singularValue n) :
    ∃ (A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁)
      (B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ B ∘L T ∘L A = (c : 𝕜) • ContinuousLinearMap.id 𝕜 _ := by
  rcases hc0.eq_or_lt with rfl | hc_pos
  · exact ⟨0, 0, by simp, by simp, by ext; simp⟩
  set c' : ℝ := (c + T.singularValue n) / 2 with hc'_def
  have hcc' : c < c' := by rw [hc'_def]; linarith
  have hc' : c' < T.completion.singularValue n := by
    rw [T.singularValue_completion, hc'_def]; linarith
  obtain ⟨A', B', hA', hB', hfac'⟩ :=
    exists_comp_comp_eq_smul_id_of_completeSpace T.completion n (by positivity) hc'
  set m : ℝ := ((n + 1 : ℕ) : ℝ)
  set D : ℝ := (c + ‖T‖) * m + 1 with hD_def
  have hD : 0 < D := by positivity
  set δ : ℝ := (c' - c) / D
  obtain ⟨A₀, hA₀_norm, hA₀_err⟩ := exists_sub_completion_le A' hA' (div_pos (sub_pos.mpr hcc') hD)
  set α : ℝ := 1 + m * δ with hα_def
  have hα : 0 < α := by positivity
  let A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁ := ((α : ℝ) : 𝕜)⁻¹ • A₀
  have hA_norm : ‖A‖ ≤ 1 := by
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hα]
    exact (inv_mul_le_iff₀ hα).mpr (by simpa [α, m] using hA₀_norm)
  let B₀ : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) := B' ∘L Completion.toComplL
  have hB₀_norm : ‖B₀‖ ≤ 1 := (opNorm_comp_le _ _).trans <|
    (mul_le_mul hB' (Completion.toComplₗᵢ : H₂ →ₗᵢ[𝕜] Completion H₂).norm_toContinuousLinearMap_le
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  refine exists_right_factor_of_coercive T A B₀ hA_norm hB₀_norm hc_pos fun u ↦ ?_
  have htri : (c' - ‖T‖ * (m * δ)) * ‖u‖ ≤ ‖B₀ (T (A₀ u))‖ :=
    le_norm_comp_toComplL_apply T A' B' hB' (hc_pos.trans hcc') hfac' A₀ u
      (by simpa [m] using hA₀_err u)
  have hSu : ‖(B₀ ∘L T ∘L A) u‖ = α⁻¹ * ‖B₀ (T (A₀ u))‖ := by
    simp [A, norm_smul, abs_of_pos hα]
  rw [hSu, ← div_eq_inv_mul, le_div_iff₀' hα, ← mul_assoc]
  refine (mul_le_mul_of_nonneg_right ?_ (norm_nonneg u)).trans htri
  have hcmδ : (c + ‖T‖) * (m * δ) ≤ c' - c := by
    calc (c + ‖T‖) * (m * δ) = ((c + ‖T‖) * m) * ((c' - c) / D) := by ring
      _ ≤ D * ((c' - c) / D) := by gcongr; rw [hD_def]; linarith
      _ = c' - c := mul_div_cancel₀ _ hD.ne'
  rw [hα_def]; nlinarith

end Factorization

end ContinuousLinearMap

universe u

namespace TauCeti.SNumbers.IsSNumberSequence

variable {𝕜 : Type u} [RCLike 𝕜] {s : SNumberFamily 𝕜} (hs : IsSNumberSequence s)
include hs

/-- **Uniqueness of s-number sequences on inner product spaces.** Between inner product spaces over
`ℝ` or `ℂ`, every s-number sequence coincides with the approximation numbers at every index,
without completeness assumptions on either space. -/
theorem eq_singularValue {H₁ H₂ : Type u}
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) :
    s T n = T.singularValue n := by
  refine (hs.le_singularValue T n).antisymm ?_
  rw [← NNReal.coe_le_coe]
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
  rcases le_or_gt c 0 with hc0 | hc_pos
  · exact hc0.trans (NNReal.coe_nonneg _)
  obtain ⟨A, B, hA, hB, hfac⟩ := T.exists_comp_comp_eq_smul_id n hc_pos.le hc
  have hA' : ‖A‖₊ ≤ 1 := by exact_mod_cast hA
  have hB' : ‖B‖₊ ≤ 1 := by exact_mod_cast hB
  have hle : s (B ∘L T ∘L A) n ≤ s T n :=
    (hs.comp_le B T A n).trans <| by
      calc ‖B‖₊ * s T n * ‖A‖₊ ≤ 1 * s T n * 1 := by gcongr
        _ = s T n := by simp
  rw [hfac, hs.smul, hs.normalize, mul_one, ← NNReal.coe_le_coe, coe_nnNorm, RCLike.norm_ofReal,
    abs_of_pos hc_pos] at hle
  exact hle

/-- **Finite-dimensional singular values.** Between finite-dimensional inner product spaces over
`ℝ` or `ℂ`, every s-number sequence equals Mathlib's `LinearMap.singularValues` at every index. -/
theorem eq_singularValues {H₁ H₂ : Type u}
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [FiniteDimensional 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [FiniteDimensional 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) :
    (s T n : ℝ) = (T : H₁ →ₗ[𝕜] H₂).singularValues n := by
  rw [hs.eq_singularValue, T.singularValue_eq_linearMap_singularValues]

/-- Every s-number sequence of a compact operator from a normed space into an inner product space
tends to zero. Neither space needs to be complete, and the domain needs no inner product. -/
theorem tendsto_nhds_zero_of_isCompactOperator {X H₂ : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    {T : X →L[𝕜] H₂} (hT : IsCompactOperator T) :
    Tendsto (s T) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT.tendsto_singularValue
    (fun _ ↦ zero_le) (hs.le_singularValue T)

/-- Between inner product spaces with a complete codomain, if some s-number sequence of `T` tends
to zero then `T` is a compact operator. -/
theorem isCompactOperator_of_tendsto_nhds_zero {H₁ H₂ : Type u}
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
    {T : H₁ →L[𝕜] H₂} (h : Tendsto (s T) atTop (𝓝 0)) :
    IsCompactOperator T :=
  ContinuousLinearMap.isCompactOperator_of_tendsto_singularValue
    (h.congr (hs.eq_singularValue T))

/-- **Compactness characterization by s-numbers on Hilbert spaces.** Between inner product spaces
over `ℝ` or `ℂ` with a complete codomain, a bounded operator is compact if and only if its terms
under an s-number sequence tend to zero. -/
theorem isCompactOperator_iff {H₁ H₂ : Type u}
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
    (T : H₁ →L[𝕜] H₂) :
    IsCompactOperator T ↔ Tendsto (s T) atTop (𝓝 0) :=
  ⟨hs.tendsto_nhds_zero_of_isCompactOperator, hs.isCompactOperator_of_tendsto_nhds_zero⟩

end TauCeti.SNumbers.IsSNumberSequence
