/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Schmidt
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax
public import TauCeti.Topology.Order.DecreasingRearrangement

/-!
# Approximation numbers from a Schmidt series

Let `T : E →L[𝕜] F` send a Hilbert basis `(bᵢ)` of `E` to pairwise orthogonal vectors. Then
`aₙ(T)` is the `n`-th term of the decreasing rearrangement `TauCeti.decreasingRearrangement` of
the family `i ↦ ‖T bᵢ‖`: the supremum of the common lower bounds of `n + 1` distinct norms
`‖T bᵢ‖`, and of zero. The index type is arbitrary and no enumeration of the indices is chosen.
When `‖T bᵢ‖` tends to zero cofinitely, for instance when `T` is compact, this lists the norms
`‖T bᵢ‖` in nonincreasing order with multiplicity, padded by zeros. In general a rearranged term
need not be one of the norms: if `‖T bᵢ‖ = 1 - 1 / (i + 2)` for `i : ℕ`, every rearranged term
is `1`.

Both bounds come from the min–max bounds for approximation numbers. At most `n` indices have
`‖T bᵢ‖` above the `n`-th rearranged value `rₙ`, and `T` is bounded by `rₙ` on the orthogonal
complement of their span, so `aₙ(T) ≤ rₙ`. Below `rₙ` every threshold is exceeded on `n + 1`
indices, and `T` is coercive with that constant on their span, so `rₙ ≤ aₙ(T)`. Neither bound
uses compactness or completeness.

For a compact operator from a Hilbert space such a basis exists, and combining this with the
Schmidt series gives its singular value decomposition: countable orthonormal families `(eᵢ)` and
`(fᵢ)` and positive numbers `σᵢ → 0` with `T = ∑ᵢ σᵢ ⟪eᵢ, ·⟫ fᵢ` in operator norm, whose
decreasing rearrangement is the sequence of approximation numbers of `T`.

## Main declarations

* `HilbertBasis.singularValue_le_of_pairwise_inner_eq_zero` and
  `HilbertBasis.le_singularValue_of_pairwise_inner_eq_zero`: the upper and lower bounds for a map
  with pairwise orthogonal basis images.
* `HilbertBasis.singularValue_eq_decreasingRearrangement`: `aₙ(T)` is the `n`-th term of the
  decreasing rearrangement of `i ↦ ‖T bᵢ‖`.
* `IsCompactOperator.exists_orthonormal_hasSum_rankOne`: the singular value decomposition of a
  compact operator from a Hilbert space.

## References

* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators*,
  Translations of Mathematical Monographs 18, AMS (1969), Chapter II, §2.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), §2.11.
-/

public section

open Filter Topology InnerProductSpace
open scoped NNReal InnerProductSpace

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace HilbertBasis

variable (b : HilbertBasis ι 𝕜 E) {T : E →L[𝕜] F}

/-- **Upper bound for a diagonal map.** Let `T` send the Hilbert basis `(bᵢ)` to pairwise
orthogonal vectors. If `‖T bᵢ‖ ≤ c` for every index outside a set of at most `n` indices, then
`aₙ(T) ≤ c`. -/
theorem singularValue_le_of_pairwise_inner_eq_zero
    (hT : Pairwise fun i j ↦ ⟪T (b i), T (b j)⟫_𝕜 = 0) {n : ℕ} {s : Finset ι}
    (hs : s.card ≤ n) {c : ℝ≥0} (hc : ∀ i ∉ s, ‖T (b i)‖ ≤ c) : T.singularValue n ≤ c := by
  classical
  set V := Submodule.span 𝕜 ((s.image b : Finset E) : Set E)
  have hV : Module.rank 𝕜 V ≤ n :=
    (rank_span_finset_le _).trans (by exact_mod_cast Finset.card_image_le.trans hs)
  refine (T.singularValue_le_nnnorm_comp_orthogonal hV).trans ?_
  refine NNReal.coe_le_coe.mp (ContinuousLinearMap.opNorm_le_bound _ c.2 fun x ↦ ?_)
  -- The coordinates of `x ∈ (span {bᵢ | i ∈ s})ᗮ` vanish on `s`.
  have hx : ∀ i ∈ (s : Set ι), ⟪b i, (x : E)⟫_𝕜 = 0 := fun i hi ↦
    (Submodule.mem_orthogonal _ _).mp x.2 _
      (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem b hi)))
  simpa using b.norm_apply_le_of_forall_inner_eq_zero hT hc hx

/-- **Lower bound for a diagonal map.** Let `T` send the Hilbert basis `(bᵢ)` to pairwise
orthogonal vectors. If `c ≤ ‖T bᵢ‖` for every index in a set of more than `n` indices, then
`c ≤ aₙ(T)`. -/
theorem le_singularValue_of_pairwise_inner_eq_zero
    (hT : Pairwise fun i j ↦ ⟪T (b i), T (b j)⟫_𝕜 = 0) {n : ℕ} {s : Finset ι}
    (hs : n < s.card) {c : ℝ} (hc : ∀ i ∈ s, c ≤ ‖T (b i)‖) : c ≤ T.singularValue n := by
  set v : s → E := fun i ↦ b i
  have hv : LinearIndependent 𝕜 v :=
    b.orthonormal.linearIndependent.comp _ Subtype.val_injective
  set V := Submodule.span 𝕜 (Set.range v)
  have : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  have hV : (n : Cardinal) < Module.rank 𝕜 V := by
    rw [← Module.finrank_eq_rank, finrank_span_eq_card hv, Fintype.card_coe]
    exact_mod_cast hs
  refine T.le_singularValue_of_lt_rank hV fun x hx ↦ ?_
  -- The coordinates of `x ∈ span {bᵢ | i ∈ s}` vanish off `s`.
  have hx' : ∀ j ∉ (s : Set ι), ⟪b j, x⟫_𝕜 = 0 := fun j hj ↦ by
    have hle : V ≤ LinearMap.ker (innerₛₗ 𝕜 (b j)) := Submodule.span_le.mpr <| by
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, innerₛₗ_apply_apply]
      exact b.orthonormal.inner_eq_zero fun h ↦ hj (h ▸ i.2)
    simpa only [LinearMap.mem_ker, innerₛₗ_apply_apply] using hle hx
  exact b.mul_norm_le_norm_apply_of_forall_inner_eq_zero hT hc hx'

/-- **Approximation numbers of a map with orthogonal basis images.** If `T` sends the Hilbert
basis `(bᵢ)` to pairwise orthogonal vectors, then `aₙ(T)` is the `n`-th term of the decreasing
rearrangement of the norms `‖T bᵢ‖`: the supremum of the common lower bounds of `n + 1` distinct
norms, and of zero. When `‖T bᵢ‖` tends to zero cofinitely, this lists the norms with
multiplicity, padded by zeros. -/
theorem singularValue_eq_decreasingRearrangement
    (hT : Pairwise fun i j ↦ ⟪T (b i), T (b j)⟫_𝕜 = 0) (n : ℕ) :
    (T.singularValue n : ℝ) = TauCeti.decreasingRearrangement (fun i ↦ ‖T (b i)‖) n := by
  set r := TauCeti.decreasingRearrangement (fun i ↦ ‖T (b i)‖)
  have hbdd : BddAbove (Set.range fun i ↦ ‖T (b i)‖) := ⟨‖T‖, by
    rintro _ ⟨i, rfl⟩
    simpa [b.orthonormal.1 i] using T.le_opNorm (b i)⟩
  have hr0 : 0 ≤ r n := TauCeti.decreasingRearrangement_nonneg hbdd n
  refine le_antisymm ?_ (le_of_forall_lt_imp_le_of_dense fun a ha ↦ ?_)
  · -- At most `n` indices have `‖T bᵢ‖ > rₙ`, and `T` is bounded by `rₙ` on the others.
    have hfin := TauCeti.finite_setOf_decreasingRearrangement_lt hbdd n
    have := b.singularValue_le_of_pairwise_inner_eq_zero hT (s := hfin.toFinset)
      (TauCeti.card_le_of_forall_decreasingRearrangement_lt hbdd fun i hi ↦ by simpa using hi)
      (c := (r n).toNNReal) fun i hi ↦ by
        rw [Real.coe_toNNReal _ hr0]
        simpa using hi
    rwa [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0] at this
  · -- Every threshold below `rₙ` is exceeded on `n + 1` indices.
    rcases lt_or_ge a 0 with ha0 | ha0
    · exact ha0.le.trans (NNReal.coe_nonneg _)
    obtain ⟨u, hu, hua⟩ := (TauCeti.lt_decreasingRearrangement_iff hbdd ha0 n).mp ha
    exact b.le_singularValue_of_pairwise_inner_eq_zero hT (by omega) fun i hi ↦ (hua i hi).le

end HilbertBasis

section SingularValueDecomposition

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **Singular value decomposition of a compact operator.** A compact operator `T` from a
Hilbert space to an inner product space is the operator-norm sum `T = ∑ᵢ σᵢ ⟪eᵢ, ·⟫ fᵢ` of a
countable family of rank-one maps, where `(eᵢ)` and `(fᵢ)` are orthonormal families and the
singular values `σᵢ` are positive and tend to zero. Their decreasing rearrangement is the sequence
of approximation numbers of `T`. -/
theorem IsCompactOperator.exists_orthonormal_hasSum_rankOne {T : E →L[𝕜] F}
    (hTc : IsCompactOperator T) :
    ∃ (ι : Type u) (e : ι → E) (f : ι → F) (σ : ι → ℝ), Countable ι ∧ Orthonormal 𝕜 e ∧
      Orthonormal 𝕜 f ∧ (∀ i, 0 < σ i) ∧ Tendsto σ cofinite (𝓝 0) ∧
      HasSum (fun i ↦ (σ i : 𝕜) • rankOne 𝕜 (f i) (e i)) T ∧
      ∀ n, (T.singularValue n : ℝ) = TauCeti.decreasingRearrangement σ n := by
  obtain ⟨s, b, -, hT⟩ := hTc.exists_hilbertBasis_pairwise_inner_eq_zero
  -- Keep the basis vectors with nonzero image and normalize their images.
  set J : Set s := {i | T (b i) ≠ 0}
  have hnull := b.orthonormal.tendsto_norm_apply_cofinite hTc
  have hJ : J.Countable := by
    have h := hnull.countable_compl_preimage_ker
    rw [ker_nhds] at h
    exact h.mono fun i (hi : T (b i) ≠ 0) ↦ by simpa using hi
  have hsupp : Function.support (fun i ↦ rankOne 𝕜 (T (b i)) (b i)) ⊆ J := fun i hi h ↦
    hi (by simp [h])
  refine ⟨J, fun i ↦ b i, fun i ↦ ((‖T (b i)‖⁻¹ : ℝ) : 𝕜) • T (b i), fun i ↦ ‖T (b i)‖,
    hJ.to_subtype, b.orthonormal.comp _ Subtype.val_injective,
    TauCeti.orthonormal_inv_norm_smul_of_pairwise_inner_eq_zero (v := T ∘ b) hT,
    fun i ↦ norm_pos_iff.mpr i.2,
    hnull.comp Subtype.val_injective.tendsto_cofinite, ?_, fun n ↦ ?_⟩
  · have hterm (i : J) : ((‖T (b i)‖ : ℝ) : 𝕜) • rankOne 𝕜 (((‖T (b i)‖⁻¹ : ℝ) : 𝕜) • T (b i))
        (b i) = rankOne 𝕜 (T (b i)) (b i) := by
      have hσ : ‖T (b i)‖ ≠ 0 := norm_ne_zero_iff.mpr i.2
      ext x
      simp [smul_smul, hσ]
    simp_rw [hterm]
    exact (hasSum_subtype_iff_of_support_subset hsupp).mpr (b.hasSum_rankOne hTc hT)
  · rw [b.singularValue_eq_decreasingRearrangement hT n]
    exact (TauCeti.decreasingRearrangement_comp_subtypeVal hnull.bddAbove_range_of_cofinite
      (fun i hi ↦ norm_pos_iff.mp hi) n).symm

end SingularValueDecomposition
