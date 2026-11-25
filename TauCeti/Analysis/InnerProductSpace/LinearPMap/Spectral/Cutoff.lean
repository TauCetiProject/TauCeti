/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Order.Northcott
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Projection
public import TauCeti.Analysis.Normed.Operator.Compact.Orthonormal
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Compact

/-!
# Spectral cutoffs of operators with compact resolvent

Let `A` be a partial linear map on an inner product space with compact resolvent. If `v` is an
orthonormal family of eigenvectors of `A`, with `A (v i) = λ i • v i`, then for every `R` only
finitely many eigenvalues satisfy `‖λ i‖ ≤ R`: the norm of the eigenvalue family is a Northcott
function (`LinearPMap.HasCompactResolvent.northcott_norm_of_orthonormal`). Indeed the compact
resolvent `R(z)` acts on `v i` as multiplication by `(z - λ i)⁻¹`, and a compact operator has only
finitely many orthonormal eigenvectors with eigenvalue of norm at least `δ > 0`
(`IsCompactOperator.finite_setOf_le_norm_of_orthonormal`). So a spectral cutoff of such an
operator, keeping the eigenbasis vectors with eigenvalues of norm at most `R`, keeps only finitely
many of them, and `0` is isolated among the eigenvalues.

For a symmetric operator with a Hilbert basis `b` of eigenvectors with real eigenvalues `λ k`, the
Parseval expansions `re ⟪A u, u⟫ = ∑ λ k ‖⟪b k, u⟫‖²` and `‖A u‖² = ∑ λ k ² ‖⟪b k, u⟫‖²` give
the lower bounds of a spectral cutoff: if the coefficients of `u` vanish on all eigenvalues below
`c`, then `c ‖u‖² ≤ re ⟪A u, u⟫`, and if they vanish on all eigenvalues of absolute value below
`c`, then `c ‖u‖ ≤ ‖A u‖`. With compact resolvent these give positive spectral gaps, the least
positive eigenvalue for the quadratic form and the least nonzero absolute value of an eigenvalue for
the norm. For a nonnegative operator the eigenvectors with nonpositive eigenvalues span its kernel.

The same expansion controls the *spectral truncation* of a nonnegative symmetric operator `A`. Let
`Π_R = b.projection {k | λ k ≤ R}` be the coordinate projection onto the eigenvectors with
eigenvalues at most `R` (`HilbertBasis.projection`). With compact resolvent it has finite rank, and
for every bounded operator `T` the truncation `T ∘ Π_R` approximates `T` on the domain of `A`:

`R ‖T u - T (Π_R u)‖² ≤ ‖T‖² re ⟪A u, u⟫`.

Measured in the form norm `re ⟪A u, u⟫ ^ (1/2)` on the domain of `A`, the error is at most
`‖T‖ / √R`. This is how a bounded operator is replaced by finite-rank operators built from
finitely many eigenvectors, up to an error controlled in the form norm.

## Main results

* `LinearPMap.HasCompactResolvent.northcott_norm_of_orthonormal`: the eigenvalues attached to an
  orthonormal family of eigenvectors of an operator with compact resolvent have only finitely many
  members of norm at most `R`, for every `R`.
* `LinearPMap.HasCompactResolvent.exists_pos_forall_norm_lt_imp_eq_zero`: `0` is isolated among the
  eigenvalues attached to an orthonormal family of eigenvectors.
* `LinearPMap.IsFormalAdjoint.mul_norm_sq_le_re_inner_of_hilbertBasis`: the lower bound
  `c ‖u‖² ≤ re ⟪A u, u⟫` for `u` orthogonal to the eigenbasis vectors with eigenvalues below `c`.
* `LinearPMap.IsFormalAdjoint.mul_norm_le_norm_apply_of_hilbertBasis`: the lower bound
  `c ‖u‖ ≤ ‖A u‖` for `u` orthogonal to the eigenbasis vectors with eigenvalues of absolute value
  below `c`.
* `LinearPMap.IsFormalAdjoint.hasSum_re_inner_of_hilbertBasis`: the quadratic form
  `re ⟪A u, u⟫` as the Parseval sum `∑ λ k ‖⟪b k, u⟫‖²`.
* `LinearPMap.IsFormalAdjoint.mul_norm_projection_sq_le_re_inner`,
  `LinearPMap.IsFormalAdjoint.mul_norm_apply_sub_apply_projection_sq_le_re_inner`: the spectral
  truncation estimate above, for nonnegative eigenvalues.
* `LinearPMap.HasCompactResolvent.hasFiniteRange_projection_setOf_le`: with compact resolvent and
  eigenvalues bounded below, the spectral truncation `Π_R` has finite rank.
* `LinearPMap.HasCompactResolvent.exists_pos_mul_norm_sq_le_re_inner`,
  `LinearPMap.HasCompactResolvent.exists_pos_mul_norm_le_norm_apply`: positive spectral gaps on the
  complement of the eigenvectors with nonpositive, respectively zero, eigenvalues.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics IV: Analysis of Operators*,
  §XIII.14.
-/

public section

open RCLike
open scoped InnerProductSpace

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {A : E →ₗ.[𝕜] E}

/-- If `A` has compact resolvent and `v` is an orthonormal family of eigenvectors of `A`, with
`A (v i) = λ i • v i`, then for every `R` only finitely many eigenvalues satisfy `‖λ i‖ ≤ R`. -/
theorem HasCompactResolvent.northcott_norm_of_orthonormal (h : A.HasCompactResolvent)
    {ι : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v) {lam : ι → 𝕜}
    (hA : ∀ i, ∃ hi : v i ∈ A.domain, A ⟨v i, hi⟩ = lam i • v i) :
    Northcott fun i ↦ ‖lam i‖ where
  finite_le R := by
    obtain ⟨z, hz, hK⟩ := hasCompactResolvent_def.mp h
    have hR (i : ι) : A.resolvent z (v i) = (z - lam i)⁻¹ • v i := by
      obtain ⟨hi, hAi⟩ := hA i
      exact resolvent_apply_of_apply_eq_smul hz ⟨v i, hi⟩ hAi
    -- `z` lies in the resolvent set, so it is not an eigenvalue.
    have hne (i : ι) : z - lam i ≠ 0 := by
      obtain ⟨hi, hAi⟩ := hA i
      exact sub_ne_zero_of_apply_eq_smul hz ⟨v i, hi⟩ (hv.ne_zero i) hAi
    set M := ‖z‖ + |R| + 1
    have hM : 0 < M := by positivity
    refine (hK.finite_setOf_le_norm_of_orthonormal (T := (A.resolvent z : E →ₗ[𝕜] E)) hv hR
      (inv_pos.2 hM)).subset fun i (hi : ‖lam i‖ ≤ R) ↦ ?_
    have hle : ‖z - lam i‖ ≤ M :=
      (norm_sub_le z (lam i)).trans (by linarith [le_abs_self R])
    simpa only [Set.mem_ofPred_eq, norm_inv] using inv_anti₀ (norm_pos_iff.2 (hne i)) hle

/-- If `A` has compact resolvent and `v` is an orthonormal family of eigenvectors of `A` with
eigenvalues `λ i`, then `0` is isolated among these eigenvalues: there is `c > 0`, the least norm
of a nonzero eigenvalue when one exists, such that `‖λ i‖ < c` forces `λ i = 0`. -/
theorem HasCompactResolvent.exists_pos_forall_norm_lt_imp_eq_zero (h : A.HasCompactResolvent)
    {ι : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v) {lam : ι → 𝕜}
    (hA : ∀ i, ∃ hi : v i ∈ A.domain, A ⟨v i, hi⟩ = lam i • v i) :
    ∃ c > 0, ∀ i, ‖lam i‖ < c → lam i = 0 := by
  by_cases hne : ∃ i, lam i ≠ 0
  · have := h.northcott_norm_of_orthonormal hv hA
    obtain ⟨i₀, hi₀ : lam i₀ ≠ 0, hmin⟩ :=
      Northcott.exists_min_image (fun i ↦ ‖lam i‖) {i | lam i ≠ 0} hne
    exact ⟨‖lam i₀‖, norm_pos_iff.2 hi₀, fun i hi ↦ not_not.1 fun hi' ↦ hi.not_ge (hmin i hi')⟩
  · exact ⟨1, one_pos, fun i _ ↦ not_not.1 fun hi ↦ hne ⟨i, hi⟩⟩

section HilbertBasis

variable {κ : Type*} (b : HilbertBasis κ 𝕜 E) {lam : κ → ℝ}

/-- **Parseval for the quadratic form.** Let `A` be symmetric with a Hilbert basis `b` of
eigenvectors, `A (b k) = λ k • b k` with `λ k` real. For `u` in the domain, the quadratic form
`re ⟪A u, u⟫` is the sum `∑ λ k ‖⟪b k, u⟫‖²`. -/
theorem IsFormalAdjoint.hasSum_re_inner_of_hilbertBasis (hA : A.IsFormalAdjoint A)
    (hb : ∀ k, ∃ hk : b k ∈ A.domain, A ⟨b k, hk⟩ = (lam k : 𝕜) • b k) (u : A.domain) :
    HasSum (fun k ↦ lam k * ‖⟪b k, (u : E)⟫_𝕜‖ ^ 2) (re ⟪A u, (u : E)⟫_𝕜) := by
  have hterm (k : κ) : ⟪A u, b k⟫_𝕜 * ⟪b k, (u : E)⟫_𝕜 =
      ((lam k * ‖⟪b k, (u : E)⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
    obtain ⟨hk, hAk⟩ := hb k
    have h1 := hA u ⟨b k, hk⟩
    simp only at h1
    rw [h1, hAk, inner_smul_right, ← inner_conj_symm (u : E) (b k), mul_assoc, RCLike.conj_mul]
    push_cast
    ring
  simpa only [hterm, ofReal_re] using hasSum_re _ (b.hasSum_inner_mul_inner (A u) u)

/-- Let `A` be symmetric with a Hilbert basis `b` of eigenvectors, `A (b k) = λ k • b k` with `λ k`
real. If the coefficients `⟪b k, u⟫` of `u` in the domain vanish whenever `λ k < c`, then
`c ‖u‖² ≤ re ⟪A u, u⟫`. -/
theorem IsFormalAdjoint.mul_norm_sq_le_re_inner_of_hilbertBasis (hA : A.IsFormalAdjoint A)
    (hb : ∀ k, ∃ hk : b k ∈ A.domain, A ⟨b k, hk⟩ = (lam k : 𝕜) • b k) {c : ℝ} (u : A.domain)
    (hu : ∀ k, lam k < c → ⟪b k, (u : E)⟫_𝕜 = 0) :
    c * ‖(u : E)‖ ^ 2 ≤ re ⟪A u, (u : E)⟫_𝕜 := by
  refine hasSum_le (fun k ↦ ?_) ((b.hasSum_norm_inner_sq u).mul_left c)
    (hA.hasSum_re_inner_of_hilbertBasis b hb u)
  rcases lt_or_ge (lam k) c with hk | hk
  · simp [hu k hk]
  · exact mul_le_mul_of_nonneg_right hk (sq_nonneg _)

/-- **Spectral cutoff estimate.** Let `A` be symmetric with a Hilbert basis `b` of eigenvectors,
`A (b k) = λ k • b k` with `λ k` real. If the coefficients `⟪b k, u⟫` of `u` in the domain vanish
whenever `|λ k| < c`, then `c ‖u‖ ≤ ‖A u‖`. -/
theorem IsFormalAdjoint.mul_norm_le_norm_apply_of_hilbertBasis (hA : A.IsFormalAdjoint A)
    (hb : ∀ k, ∃ hk : b k ∈ A.domain, A ⟨b k, hk⟩ = (lam k : 𝕜) • b k) {c : ℝ} (u : A.domain)
    (hu : ∀ k, |lam k| < c → ⟪b k, (u : E)⟫_𝕜 = 0) :
    c * ‖(u : E)‖ ≤ ‖A u‖ := by
  rcases lt_or_ge c 0 with hc | hc
  · exact (mul_nonpos_of_nonpos_of_nonneg hc.le (norm_nonneg _)).trans (norm_nonneg _)
  -- The coefficients of `A u` are `λ k ⟪b k, u⟫`; compare the two Parseval sums.
  have hcoef (k : κ) : ⟪b k, A u⟫_𝕜 = (lam k : 𝕜) * ⟪b k, (u : E)⟫_𝕜 := by
    obtain ⟨hk, hAk⟩ := hb k
    have h1 := hA ⟨b k, hk⟩ u
    simp only at h1
    rw [← h1, hAk, inner_smul_left, conj_ofReal]
  have hsq : (c * ‖(u : E)‖) ^ 2 ≤ ‖A u‖ ^ 2 := by
    rw [mul_pow]
    refine hasSum_le (fun k ↦ ?_) ((b.hasSum_norm_inner_sq u).mul_left (c ^ 2))
      (b.hasSum_norm_inner_sq (A u))
    rw [hcoef, norm_mul, norm_ofReal, mul_pow]
    rcases lt_or_ge |lam k| c with hk | hk
    · simp [hu k hk]
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc hk 2) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (mul_nonneg hc (norm_nonneg _)) (norm_nonneg _) two_ne_zero).1 hsq

/-- **Spectral gap of the quadratic form.** Let `A` be symmetric with compact resolvent and with a
Hilbert basis `b` of eigenvectors, `A (b k) = λ k • b k` with `λ k` real. There is `c > 0` such
that `c ‖u‖² ≤ re ⟪A u, u⟫` for every `u` in the domain orthogonal to the eigenbasis vectors with
nonpositive eigenvalues. When there is a positive eigenvalue, `c` can be taken to be the least
one. -/
theorem HasCompactResolvent.exists_pos_mul_norm_sq_le_re_inner (h : A.HasCompactResolvent)
    (hA : A.IsFormalAdjoint A) (hb : ∀ k, ∃ hk : b k ∈ A.domain, A ⟨b k, hk⟩ = (lam k : 𝕜) • b k) :
    ∃ c > 0, ∀ u : A.domain, (∀ k, lam k ≤ 0 → ⟪b k, (u : E)⟫_𝕜 = 0) →
      c * ‖(u : E)‖ ^ 2 ≤ re ⟪A u, (u : E)⟫_𝕜 := by
  obtain ⟨c, hc, hgap⟩ := h.exists_pos_forall_norm_lt_imp_eq_zero b.orthonormal hb
  refine ⟨c, hc, fun u hu ↦ hA.mul_norm_sq_le_re_inner_of_hilbertBasis b hb u fun k hk ↦ hu k ?_⟩
  -- No eigenvalue lies in `(0, c)`.
  exact not_lt.1 fun hk' ↦
    hk'.ne' (ofReal_eq_zero.1 (hgap k (by rwa [norm_ofReal, abs_of_pos hk'])))

/-- **Spectral gap on the kernel complement.** Let `A` be symmetric with compact resolvent and with
a Hilbert basis `b` of eigenvectors, `A (b k) = λ k • b k` with `λ k` real. There is `c > 0` such
that `c ‖u‖ ≤ ‖A u‖` for every `u` in the domain orthogonal to the eigenbasis vectors with
eigenvalue zero. When there is a nonzero eigenvalue, `c` can be taken to be the least absolute value
of one. -/
theorem HasCompactResolvent.exists_pos_mul_norm_le_norm_apply (h : A.HasCompactResolvent)
    (hA : A.IsFormalAdjoint A) (hb : ∀ k, ∃ hk : b k ∈ A.domain, A ⟨b k, hk⟩ = (lam k : 𝕜) • b k) :
    ∃ c > 0, ∀ u : A.domain, (∀ k, lam k = 0 → ⟪b k, (u : E)⟫_𝕜 = 0) →
      c * ‖(u : E)‖ ≤ ‖A u‖ := by
  obtain ⟨c, hc, hgap⟩ := h.exists_pos_forall_norm_lt_imp_eq_zero b.orthonormal hb
  exact ⟨c, hc, fun u hu ↦ hA.mul_norm_le_norm_apply_of_hilbertBasis b hb u fun k hk ↦
    hu k (ofReal_eq_zero.1 (hgap k (by rwa [norm_ofReal])))⟩

/-- **Spectral truncation of a nonnegative operator.** Let `A` be symmetric with a Hilbert basis `b`
of eigenvectors, `A (b k) = λ k • b k` with `λ k ≥ 0`. For every `R` and every `u` in the domain,
the part of `u` along the eigenvectors with eigenvalues greater than `R` satisfies
`R ‖b.projection {k | R < λ k} u‖² ≤ re ⟪A u, u⟫`. -/
theorem IsFormalAdjoint.mul_norm_projection_sq_le_re_inner (hA : A.IsFormalAdjoint A)
    (hb : ∀ k, ∃ hk : b k ∈ A.domain, A ⟨b k, hk⟩ = (lam k : 𝕜) • b k) (hlam : ∀ k, 0 ≤ lam k)
    (R : ℝ) (u : A.domain) :
    R * ‖b.projection {k | R < lam k} u‖ ^ 2 ≤ re ⟪A u, (u : E)⟫_𝕜 :=
  b.mul_norm_projection_sq_le _ (fun _ hk ↦ le_of_lt hk) (fun k _ ↦ hlam k)
    (hA.hasSum_re_inner_of_hilbertBasis b hb u)

/-- **Truncation estimate for a nonnegative operator.** Let `A` be symmetric with a Hilbert basis
`b` of eigenvectors, `A (b k) = λ k • b k` with `λ k ≥ 0`, and let
`Π_R = b.projection {k | λ k ≤ R}` be its spectral truncation at `R`. Every bounded operator `T`
satisfies `R ‖T u - T (Π_R u)‖² ≤ ‖T‖² re ⟪A u, u⟫` for `u` in the domain of `A`. -/
theorem IsFormalAdjoint.mul_norm_apply_sub_apply_projection_sq_le_re_inner
    {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] (hA : A.IsFormalAdjoint A)
    (hb : ∀ k, ∃ hk : b k ∈ A.domain, A ⟨b k, hk⟩ = (lam k : 𝕜) • b k) (hlam : ∀ k, 0 ≤ lam k)
    (T : E →L[𝕜] F) (R : ℝ) (u : A.domain) :
    R * ‖T u - T (b.projection {k | lam k ≤ R} u)‖ ^ 2 ≤ ‖T‖ ^ 2 * re ⟪A u, (u : E)⟫_𝕜 := by
  have hcompl : {k | R < lam k} = {k | lam k ≤ R}ᶜ := by
    ext k
    simp
  have hsub : T u - T (b.projection {k | lam k ≤ R} u) = T (b.projection {k | R < lam k} u) := by
    simp [hcompl, b.projection_compl]
  have hform := hA.hasSum_re_inner_of_hilbertBasis b hb u
  rw [hsub]
  rcases le_or_gt 0 R with hR | hR
  · exact b.mul_norm_apply_projection_sq_le _ T hR (fun _ hk ↦ le_of_lt hk) (fun k _ ↦ hlam k)
      hform
  -- For `R < 0` the left side is nonpositive and the quadratic form is nonnegative.
  exact (mul_nonpos_of_nonpos_of_nonneg hR.le (sq_nonneg _)).trans
    (mul_nonneg (sq_nonneg _) (hform.nonneg fun k ↦ mul_nonneg (hlam k) (sq_nonneg _)))

/-- **Spectral truncations have finite rank.** Let `A` have compact resolvent and a Hilbert basis
`b` of eigenvectors, `A (b k) = λ k • b k` with real eigenvalues bounded below by `m`. Then for
every `R` the spectral truncation `b.projection {k | λ k ≤ R}` has finite rank. -/
theorem HasCompactResolvent.hasFiniteRange_projection_setOf_le (h : A.HasCompactResolvent)
    (hb : ∀ k, ∃ hk : b k ∈ A.domain, A ⟨b k, hk⟩ = (lam k : 𝕜) • b k) {m : ℝ}
    (hlam : ∀ k, m ≤ lam k) (R : ℝ) :
    (b.projection {k | lam k ≤ R} : E →ₗ[𝕜] E).HasFiniteRange := by
  refine b.hasFiniteRange_projection _ <|
    ((h.northcott_norm_of_orthonormal b.orthonormal hb).finite_le (max R (-m))).subset ?_
  intro k (hk : lam k ≤ R)
  simp only [Set.mem_ofPred_eq, norm_ofReal, abs_le]
  constructor <;> linarith [hlam k, le_max_left R (-m), le_max_right R (-m)]

end HilbertBasis

end LinearPMap
