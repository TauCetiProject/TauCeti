/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Diagonal
import TauCeti.Analysis.InnerProductSpace.Variational.MinMax
import TauCeti.Analysis.InnerProductSpace.Variational.Spectrum

/-!
# The energy space in an eigenbasis

Let `B` be a bounded, coercive, symmetric bilinear form on a real Hilbert space `V` and
`J : V →L[ℝ] H` a continuous linear map into a real Hilbert space `H`. Suppose `H` has a Hilbert
basis `b` of images `b i = J (u i)` of variational eigenvectors,

`B (u i) v = κ i ⟪J (u i), J v⟫` for every `v : V`,

as produced by `IsCoercive.exists_hilbertBasis_forall_apply_eq_smul_inner` when `J` is compact
with dense range. The model is `V = H¹(M)` with its inner product, `H = L²(M)` and `J` the
inclusion, for a closed Riemannian manifold `M`: then `u i` are eigenfunctions of the Laplacian
`Δ⁺` and `κ i = μ i + 1`, with `μ i` the eigenvalues of `Δ⁺`.

This file describes `V` and `B` in the coordinates `⟪b i, h⟫` of `H`. The vectors of `J V` are
exactly those whose coordinates satisfy `∑ κ i ⟪b i, h⟫² < ∞`
(`IsCoercive.mem_range_iff_summable_mul_inner_sq`). For injective `J`, every `w : V` is the sum
of its eigenfunction expansion `w = ∑ ⟪b i, J w⟫ u i`, which converges in `V`
(`IsCoercive.hasSum_inner_smul`), and the form is diagonal:

`B w v = ∑ κ i ⟪b i, J w⟫ ⟪b i, J v⟫` (`IsCoercive.hasSum_mul_inner_mul_inner`).

Equivalently, `J V` is the domain of the diagonal operator `S` with entries `√κ i` in the basis
`b`, and for injective `J` also `‖S (J w)‖² = B w w`
(`IsCoercive.range_eq_diagonalPMap_sqrt_domain`, `IsCoercive.norm_diagonalPMap_sqrt_sq`).
Informally, `S` is the square root `A^{1/2}` of the operator `A` with eigenvalues `κ i`, so for
injective `J` these identify `V`, with its energy norm, with the form domain of `A`; no operator
`A` is defined here, and the identification of `S` with a power of a given operator is not proved.
For a closed manifold, `A` is informally `Δ⁺ + 1` and this identifies `H¹(M)` with the domain
of the diagonal operator with entries `√(μ i + 1)`, with equal norms.

The proofs only use Bessel's inequality in the energy `B`: the eigenvectors `u i` are orthogonal
for `B`, with `B (u i) (u i) = κ i`, so the partial sums of the expansion of `w` have energy
`∑ κ i ⟪b i, J w⟫²`, at most `B w w`, and by coercivity they form a Cauchy family in `V`.

## Main results

* `IsCoercive.summable_mul_inner_sq`, `IsCoercive.tsum_mul_inner_sq_le`: Bessel's inequality,
  `∑ κ i ⟪b i, J w⟫² ≤ B w w < ∞`.
* `IsCoercive.exists_apply_eq_and_hasSum_inner_smul_of_summable`: if `∑ κ i ⟪b i, h⟫² < ∞`,
  the expansion `∑ ⟪b i, h⟫ u i` converges in `V` to a preimage of `h`.
* `IsCoercive.mem_range_iff_summable_mul_inner_sq`: the range of `J` in coordinates.
* `IsCoercive.hasSum_inner_smul`, `IsCoercive.hasSum_mul_inner_mul_inner`,
  `IsCoercive.hasSum_mul_inner_sq`: for injective `J`, the expansion of `w` converges to `w` and
  the form and the energy are diagonal.
* `IsCoercive.range_eq_diagonalPMap_sqrt_domain`, `IsCoercive.norm_diagonalPMap_sqrt_sq`: the
  range of `J` is the domain of the diagonal operator `√κ`, which measures the energy.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.5.1, Theorem 1 and its proof (the
  eigenfunctions of a symmetric elliptic operator, rescaled by `κ^{-1/2}`, form an orthonormal
  basis of the energy space for the form `B`).
-/

public section

open scoped InnerProductSpace

namespace IsCoercive

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {B : V →L[ℝ] V →L[ℝ] ℝ} {J : V →L[ℝ] H} {ι : Type*} {b : HilbertBasis ι ℝ H} {κ : ι → ℝ}
  {u : ι → V}

/-- The variational eigenvalues are positive. -/
private theorem pos_of_hilbertBasis (hB : IsCoercive B) (hJu : ∀ i, J (u i) = b i)
    (heq : ∀ i v, B (u i) v = κ i * ⟪J (u i), J v⟫_ℝ) (i : ι) : 0 < κ i := by
  refine hB.pos_of_forall_apply_eq_smul_inner J (fun hu ↦ ?_) (heq i)
  have h := hJu i
  rw [hu, map_zero] at h
  exact b.orthonormal.ne_zero i h.symm

/-- **Bessel's inequality in the energy.** For `w : V`, the coordinates of `J w` satisfy
`∑ κ i ⟪b i, J w⟫² < ∞`; the sum is at most `B w w` (`IsCoercive.tsum_mul_inner_sq_le`). -/
theorem summable_mul_inner_sq (hB : IsCoercive B) (hsymm : ∀ v w, B v w = B w v)
    (hJu : ∀ i, J (u i) = b i) (heq : ∀ i v, B (u i) v = κ i * ⟪J (u i), J v⟫_ℝ) (w : V) :
    Summable fun i ↦ κ i * ⟪b i, J w⟫_ℝ ^ 2 :=
  summable_of_sum_le (fun i ↦ mul_nonneg (pos_of_hilbertBasis hB hJu heq i).le (sq_nonneg _))
    (TauCeti.sum_mul_inner_sq_le_apply_self (B := B.toLinearMap₁₂) hsymm hB.apply_self_nonneg
      b.orthonormal hJu heq w)

/-- **Bessel's inequality in the energy**, the bound: for `w : V`,
`∑ κ i ⟪b i, J w⟫² ≤ B w w`. -/
theorem tsum_mul_inner_sq_le (hB : IsCoercive B) (hsymm : ∀ v w, B v w = B w v)
    (hJu : ∀ i, J (u i) = b i) (heq : ∀ i v, B (u i) v = κ i * ⟪J (u i), J v⟫_ℝ) (w : V) :
    ∑' i, κ i * ⟪b i, J w⟫_ℝ ^ 2 ≤ B w w :=
  (summable_mul_inner_sq hB hsymm hJu heq w).tsum_le_of_sum_le
    (TauCeti.sum_mul_inner_sq_le_apply_self (B := B.toLinearMap₁₂) hsymm hB.apply_self_nonneg
      b.orthonormal hJu heq w)

variable [CompleteSpace V]

/-- **Convergence of the eigenfunction expansion.** If the coordinates of `h : H` satisfy
`∑ κ i ⟪b i, h⟫² < ∞`, then the expansion `∑ ⟪b i, h⟫ u i` converges in `V`, to a vector whose
image under `J` is `h`. -/
theorem exists_apply_eq_and_hasSum_inner_smul_of_summable (hB : IsCoercive B)
    (hJu : ∀ i, J (u i) = b i) (heq : ∀ i v, B (u i) v = κ i * ⟪J (u i), J v⟫_ℝ) {h : H}
    (hsum : Summable fun i ↦ κ i * ⟪b i, h⟫_ℝ ^ 2) :
    ∃ w : V, J w = h ∧ HasSum (fun i ↦ ⟪b i, h⟫_ℝ • u i) w := by
  obtain ⟨C, hC, hle⟩ := id hB
  -- The partial sums are Cauchy: coercivity bounds them by the tails of `∑ κ i ⟪b i, h⟫²`.
  have hs : Summable fun i ↦ ⟪b i, h⟫_ℝ • u i := by
    refine summable_iff_vanishing_norm.2 fun ε hε ↦ ?_
    obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.1 hsum (C * ε ^ 2) (by positivity)
    refine ⟨s, fun t ht ↦ ?_⟩
    have h1 := hle (∑ i ∈ t, ⟪b i, h⟫_ℝ • u i)
    have h3 : B (∑ i ∈ t, ⟪b i, h⟫_ℝ • u i) (∑ i ∈ t, ⟪b i, h⟫_ℝ • u i) =
        ∑ i ∈ t, κ i * ⟪b i, h⟫_ℝ ^ 2 :=
      TauCeti.apply_sum_smul_sum_smul_eq_sum_mul_sq (B := B.toLinearMap₁₂) b.orthonormal hJu heq _ t
    rw [h3] at h1
    have h2 : ∑ i ∈ t, κ i * ⟪b i, h⟫_ℝ ^ 2 < C * ε ^ 2 := (le_abs_self _).trans_lt (hs t ht)
    have h4 : ‖∑ i ∈ t, ⟪b i, h⟫_ℝ • u i‖ ^ 2 < ε ^ 2 := by
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h4
  refine ⟨∑' i, ⟪b i, h⟫_ℝ • u i, ?_, hs.hasSum⟩
  rw [J.map_tsum hs]
  simp only [map_smul, hJu, ← b.repr_apply_apply]
  exact (b.hasSum_repr h).tsum_eq

/-- **The range of `J` in coordinates.** A vector `h : H` is the image of some `w : V` if and
only if its coordinates satisfy `∑ κ i ⟪b i, h⟫² < ∞`. -/
theorem mem_range_iff_summable_mul_inner_sq (hB : IsCoercive B) (hsymm : ∀ v w, B v w = B w v)
    (hJu : ∀ i, J (u i) = b i) (heq : ∀ i v, B (u i) v = κ i * ⟪J (u i), J v⟫_ℝ) {h : H} :
    h ∈ Set.range J ↔ Summable fun i ↦ κ i * ⟪b i, h⟫_ℝ ^ 2 := by
  refine ⟨?_, fun hsum ↦ ?_⟩
  · rintro ⟨w, rfl⟩
    exact summable_mul_inner_sq hB hsymm hJu heq w
  · obtain ⟨w, hw, -⟩ := exists_apply_eq_and_hasSum_inner_smul_of_summable hB hJu heq hsum
    exact ⟨w, hw⟩

section Injective

variable (hB : IsCoercive B) (hsymm : ∀ v w, B v w = B w v) (hJ : Function.Injective J)
  (hJu : ∀ i, J (u i) = b i) (heq : ∀ i v, B (u i) v = κ i * ⟪J (u i), J v⟫_ℝ)
include hB hsymm hJ hJu heq

/-- **The eigenfunction expansion converges in the energy space.** For injective `J`, every
`w : V` is the sum `∑ ⟪b i, J w⟫ u i` of its eigenfunction expansion, converging in `V`. -/
theorem hasSum_inner_smul (w : V) : HasSum (fun i ↦ ⟪b i, J w⟫_ℝ • u i) w := by
  obtain ⟨w', hw', hsum⟩ :=
    exists_apply_eq_and_hasSum_inner_smul_of_summable hB hJu heq
      (summable_mul_inner_sq hB hsymm hJu heq w)
  rwa [hJ hw'] at hsum

/-- **The form is diagonal in the eigenbasis.** For injective `J`,
`B w v = ∑ κ i ⟪b i, J w⟫ ⟪b i, J v⟫`. -/
theorem hasSum_mul_inner_mul_inner (w v : V) :
    HasSum (fun i ↦ κ i * ⟪b i, J w⟫_ℝ * ⟪b i, J v⟫_ℝ) (B w v) := by
  have h := ((hasSum_inner_smul hB hsymm hJ hJu heq w).mapL B).mapL
    (ContinuousLinearMap.apply ℝ ℝ v)
  simp only [ContinuousLinearMap.apply_apply, map_smul, heq, hJu,
    smul_eq_mul] at h
  convert h using 2 with i
  ring

/-- **The energy is diagonal in the eigenbasis.** For injective `J`,
`B w w = ∑ κ i ⟪b i, J w⟫²`. -/
theorem hasSum_mul_inner_sq (w : V) : HasSum (fun i ↦ κ i * ⟪b i, J w⟫_ℝ ^ 2) (B w w) := by
  simpa only [mul_assoc, sq] using hasSum_mul_inner_mul_inner hB hsymm hJ hJu heq w w

end Injective

/-! ### The square root of the diagonal operator -/

/-- **The range of `J` is the domain of the diagonal operator `√κ`.** The image of `J` is the
domain of the diagonal operator with entries `√κ i` in the basis `b` (informally, the square root
of the operator with eigenvalues `κ i`). -/
theorem range_eq_diagonalPMap_sqrt_domain (hB : IsCoercive B) (hsymm : ∀ v w, B v w = B w v)
    (hJu : ∀ i, J (u i) = b i) (heq : ∀ i v, B (u i) v = κ i * ⟪J (u i), J v⟫_ℝ) :
    Set.range J = (b.diagonalPMap fun i ↦ √(κ i)).domain := by
  ext h
  rw [SetLike.mem_coe, mem_range_iff_summable_mul_inner_sq hB hsymm hJu heq,
    HilbertBasis.mem_diagonalPMap_domain_iff]
  refine summable_congr fun i ↦ ?_
  rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (pos_of_hilbertBasis hB hJu heq i).le]

/-- **The diagonal operator `√κ` measures the energy.** For injective `J`, the diagonal operator
with entries `√κ i` in the basis `b` sends `J w` to a vector of squared norm `B w w`. -/
theorem norm_diagonalPMap_sqrt_sq (hB : IsCoercive B) (hsymm : ∀ v w, B v w = B w v)
    (hJ : Function.Injective J) (hJu : ∀ i, J (u i) = b i)
    (heq : ∀ i v, B (u i) v = κ i * ⟪J (u i), J v⟫_ℝ) (w : V)
    (hw : J w ∈ (b.diagonalPMap fun i ↦ √(κ i)).domain) :
    ‖b.diagonalPMap (fun i ↦ √(κ i)) ⟨J w, hw⟩‖ ^ 2 = B w w := by
  refine (b.hasSum_norm_diagonalPMap_apply_sq _ ⟨J w, hw⟩).unique ?_
  convert hasSum_mul_inner_sq hB hsymm hJ hJu heq w using 2 with i
  rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (pos_of_hilbertBasis hB hJu heq i).le]

end IsCoercive
