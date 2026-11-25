/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Diagonal
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Spectral.Cutoff

/-!
# Spectrum and resolvent of diagonal operators

Let `b` be a Hilbert basis of an inner product space `E` and `c : ι → 𝕜` a family of scalars. The
diagonal operator `b.diagonalPMap c` multiplies the `i`-th coordinate by `c i`. This file computes
its spectral data.

* **Resolvent.** `z • I - b.diagonalPMap c` has a bounded inverse exactly when `z` stays at a
  positive distance from all the coefficients, `δ ≤ ‖z - c i‖` for some `δ > 0` and every `i`
  (`HilbertBasis.mem_resolventSet_diagonalPMap_iff`). The inverse is then the bounded diagonal
  operator with entries `(z - c i)⁻¹` (`HilbertBasis.inner_resolvent_diagonalPMap`). Conversely,
  the resolvent sends `b i` to `(z - c i)⁻¹ • b i`, so its norm bounds `‖z - c i‖⁻¹`.
* **Spectrum.** Hence the spectrum is the closure of the set of coefficients
  (`HilbertBasis.spectrum_diagonalPMap`). For instance the coefficients `1 / (n + 1)` give the
  spectrum `{0} ∪ {1 / (n + 1)}`, which contains `0` although `0` is not an eigenvalue.
* **Compact resolvent.** `b.diagonalPMap c` has compact resolvent exactly when the coefficient
  norms form a Northcott family, that is, only finitely many `i` satisfy `‖c i‖ ≤ R`, for every `R`
  (`HilbertBasis.hasCompactResolvent_diagonalPMap_iff`). One direction is the finiteness of the
  eigenvalues of an operator with compact resolvent in a bounded set
  (`LinearPMap.HasCompactResolvent.northcott_norm_of_orthonormal`). For the other, the Northcott
  property leaves only finitely many coefficients in the ball of radius `2`, so some real point
  `z` of `[0, 1]` lies outside the closure of the coefficients. The resolvent at `z` is the
  diagonal operator with entries `(z - c i)⁻¹`, which tend to zero along the cofinite filter, and
  such a diagonal operator is compact (`HilbertBasis.isCompactOperator_diagonal_iff`).

Every self-adjoint operator with a Hilbert basis of eigenvectors is the diagonal operator of its
eigenvalues (`IsSelfAdjoint.eq_diagonalPMap`), and diagonal operators model the tensor sums
`A ⊗ 1 + 1 ⊗ B` of such operators. The compact resolvent criterion therefore reduces the
compactness of the resolvent of a tensor sum to counting pairs of eigenvalues
(`Northcott.prod_add`).

## Main results

* `HilbertBasis.mem_resolventSet_diagonalPMap_iff`: the resolvent set of a diagonal operator.
* `HilbertBasis.inner_resolvent_diagonalPMap`: the coordinates of the resolvent.
* `HilbertBasis.spectrum_diagonalPMap`: the spectrum is the closure of the coefficients.
* `HilbertBasis.hasCompactResolvent_diagonalPMap_iff`: the compact resolvent criterion.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  §VIII.3 (the spectrum of a multiplication operator is the essential range of the multiplier).
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics IV: Analysis of Operators*,
  §XIII.14, Theorem XIII.64 (compact resolvent and eigenvalues tending to infinity).
-/

public section

noncomputable section

open Filter Topology LinearPMap
open scoped ENNReal InnerProductSpace lp

namespace HilbertBasis

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  (b : HilbertBasis ι 𝕜 E) (c : ι → 𝕜) {z : 𝕜}

/-! ### The resolvent -/

/-- The bounded family `(z - c i)⁻¹`, for `z` at distance at least `δ > 0` from every
coefficient. -/
private def resolventEntries (z : 𝕜) {δ : ℝ} (hδ : 0 < δ) (hz : ∀ i, δ ≤ ‖z - c i‖) :
    ℓ^∞(ι, 𝕜) :=
  ⟨fun i ↦ (z - c i)⁻¹, memℓp_infty ⟨δ⁻¹, by
    rintro _ ⟨i, rfl⟩
    dsimp only
    rw [norm_inv]
    exact inv_anti₀ hδ (hz i)⟩⟩

private theorem resolventEntries_apply {δ : ℝ} (hδ : 0 < δ) (hz : ∀ i, δ ≤ ‖z - c i‖) (i : ι) :
    resolventEntries c z hδ hz i = (z - c i)⁻¹ :=
  rfl

/-- The coordinates of the diagonal operator with entries `(z - c i)⁻¹`. -/
private theorem inner_diagonal_resolventEntries {δ : ℝ} (hδ : 0 < δ) (hz : ∀ i, δ ≤ ‖z - c i‖)
    (y : E) (i : ι) :
    ⟪b i, b.diagonal (resolventEntries c z hδ hz) y⟫_𝕜 = (z - c i)⁻¹ * ⟪b i, y⟫_𝕜 := by
  rw [← b.repr_apply_apply, repr_diagonal, b.repr_apply_apply, resolventEntries_apply]

/-- If `z` lies at distance at least `δ > 0` from every coefficient, the diagonal operator with
entries `(z - c i)⁻¹` inverts `z • I - b.diagonalPMap c`. -/
private theorem isResolventAt_diagonal_resolventEntries {δ : ℝ} (hδ : 0 < δ)
    (hz : ∀ i, δ ≤ ‖z - c i‖) :
    IsResolventAt (b.diagonalPMap c) z (b.diagonal (resolventEntries c z hδ hz)) := by
  have hne (i : ι) : z - c i ≠ 0 := norm_pos_iff.1 (hδ.trans_le (hz i))
  rw [isResolventAt_iff_forall_mem_graph]
  refine ⟨fun y ↦ (b.mem_graph_diagonalPMap_iff c).2 fun i ↦ ?_, fun p hp ↦ ?_⟩
  · simp only [inner_sub_right, inner_smul_right, inner_diagonal_resolventEntries]
    field_simp [hne i]
    ring
  · have hp' := (b.mem_graph_diagonalPMap_iff c).1 hp
    refine b.repr.injective (lp.ext (funext fun i ↦ ?_))
    simp only [b.repr_apply_apply, inner_diagonal_resolventEntries, inner_sub_right,
      inner_smul_right, hp' i]
    field_simp [hne i]

/-- **The resolvent set of a diagonal operator.** `z • I - b.diagonalPMap c` has a bounded inverse
if and only if `z` lies at a positive distance from all the coefficients `c i`. -/
theorem mem_resolventSet_diagonalPMap_iff :
    z ∈ (b.diagonalPMap c).resolventSet ↔ ∃ δ > 0, ∀ i, δ ≤ ‖z - c i‖ := by
  refine ⟨fun h ↦ ?_, fun ⟨δ, hδ, hz⟩ ↦
    (b.isResolventAt_diagonal_resolventEntries c hδ hz).mem_resolventSet⟩
  set R := (b.diagonalPMap c).resolvent z
  refine ⟨(‖R‖ + 1)⁻¹, by positivity, fun i ↦ ?_⟩
  have hbi := b.diagonalPMap_apply_self c i
  -- A point of the resolvent set is not an eigenvalue, so `z ≠ c i`.
  have hne : z - c i ≠ 0 := sub_ne_zero_of_apply_eq_smul h _ (b.orthonormal.ne_zero i) hbi
  -- The resolvent acts on `b i` as multiplication by `(z - c i)⁻¹`, so this has norm `≤ ‖R‖`.
  have hle : ‖z - c i‖⁻¹ ≤ ‖R‖ + 1 := by
    have hRb : R (b i) = (z - c i)⁻¹ • b i := resolvent_apply_of_apply_eq_smul h _ hbi
    have := R.le_opNorm (b i)
    simp only [hRb, norm_smul, norm_inv, b.orthonormal.1 i, mul_one] at this
    linarith
  exact inv_le_of_inv_le₀ (norm_pos_iff.2 hne) hle

/-- **The resolvent of a diagonal operator.** On the resolvent set, the resolvent of
`b.diagonalPMap c` at `z` is diagonal, with entries `(z - c i)⁻¹`. -/
@[simp]
theorem inner_resolvent_diagonalPMap (hz : z ∈ (b.diagonalPMap c).resolventSet) (x : E)
    (i : ι) :
    ⟪b i, (b.diagonalPMap c).resolvent z x⟫_𝕜 = (z - c i)⁻¹ * ⟪b i, x⟫_𝕜 := by
  obtain ⟨δ, hδ, hzδ⟩ := (b.mem_resolventSet_diagonalPMap_iff c).1 hz
  rw [resolvent_eq_of_isResolventAt (b.isResolventAt_diagonal_resolventEntries c hδ hzδ),
    inner_diagonal_resolventEntries]

/-- **The spectrum of a diagonal operator** is the closure of the set of its coefficients. -/
theorem spectrum_diagonalPMap : (b.diagonalPMap c).spectrum = closure (Set.range c) := by
  ext z
  rw [mem_spectrum_iff, mem_resolventSet_diagonalPMap_iff, Metric.mem_closure_range_iff]
  simp only [dist_eq_norm, not_exists, not_and, not_forall, not_le, gt_iff_lt]

/-! ### Compact resolvent -/

/-- If only finitely many coefficients have norm at most `2`, some real point of `[0, 1]` lies
outside the closure of the coefficients. -/
private theorem exists_ofReal_notMem_closure_range [Northcott fun i ↦ ‖c i‖] :
    ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ (t : 𝕜) ∉ closure (Set.range c) := by
  have hF : (c '' {i | ‖c i‖ ≤ 2}).Finite :=
    (Northcott.finite_le (h := fun i ↦ ‖c i‖) 2).image c
  -- The coefficients of norm greater than `2` stay in the closed set `{w | 2 ≤ ‖w‖}`.
  have hsub : closure (Set.range c) ⊆ c '' {i | ‖c i‖ ≤ 2} ∪ {w | 2 ≤ ‖w‖} := by
    refine closure_minimal ?_ (hF.isClosed.union (isClosed_le continuous_const continuous_norm))
    rintro _ ⟨i, rfl⟩
    by_cases hi : ‖c i‖ ≤ 2
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr (not_le.1 hi).le
  obtain ⟨_, ⟨t, ht, rfl⟩, htF⟩ :=
    (((Set.Icc_infinite (zero_lt_one' ℝ)).image
      (RCLike.ofReal_injective (K := 𝕜)).injOn).sdiff hF).nonempty
  refine ⟨t, ht, fun hmem ↦ (hsub hmem).elim htF fun h2 ↦ ?_⟩
  have h2' : (2 : ℝ) ≤ |t| := by simpa only [Set.mem_ofPred_eq, RCLike.norm_ofReal] using h2
  rw [abs_of_nonneg ht.1] at h2'
  linarith [ht.2]

/-- **Compact resolvent of a diagonal operator.** `b.diagonalPMap c` has compact resolvent if and
only if only finitely many coefficients satisfy `‖c i‖ ≤ R`, for every `R`. -/
theorem hasCompactResolvent_diagonalPMap_iff :
    (b.diagonalPMap c).HasCompactResolvent ↔ Northcott fun i ↦ ‖c i‖ := by
  refine ⟨fun h ↦ h.northcott_norm_of_orthonormal b.orthonormal fun i ↦
    ⟨b.self_mem_diagonalPMap_domain c i, b.diagonalPMap_apply_self c i⟩, fun hN ↦ ?_⟩
  obtain ⟨t, -, ht⟩ := exists_ofReal_notMem_closure_range c
  rw [← spectrum_diagonalPMap b, mem_spectrum_iff, not_not] at ht
  obtain ⟨δ, hδ, hzδ⟩ := (b.mem_resolventSet_diagonalPMap_iff c).1 ht
  refine HasCompactResolvent.of_isCompactOperator_resolvent ht ?_
  -- The coefficient norms tend to infinity, hence so do the distances `‖z - c i‖`.
  have hc : Tendsto (fun i ↦ ‖c i‖) cofinite atTop := (northcott_iff_tendsto _).1 hN
  have hdist : Tendsto (fun i ↦ ‖(t : 𝕜) - c i‖) cofinite atTop :=
    tendsto_atTop_mono (fun i ↦ by
      rw [norm_sub_rev]
      exact le_trans (by simp) (norm_sub_norm_le (c i) (t : 𝕜)))
      (tendsto_atTop_add_const_right _ (-‖(t : 𝕜)‖) hc)
  have h0 : Tendsto (fun i ↦ ‖(t : 𝕜) - c i‖⁻¹) cofinite (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hdist
  rw [resolvent_eq_of_isResolventAt (b.isResolventAt_diagonal_resolventEntries c hδ hzδ),
    isCompactOperator_diagonal_iff]
  refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
  simpa only [resolventEntries_apply, norm_inv] using h0

end HilbertBasis
