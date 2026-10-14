/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.BasisSpan
public import TauCeti.Analysis.InnerProductSpace.OrthogonalFamily
public import TauCeti.Analysis.InnerProductSpace.SingularValues
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax

/-!
# Approximation numbers of finite diagonal maps

A bounded map `T : E →L[𝕜] F` is diagonal with respect to an orthonormal basis `(eᵢ)` of `E` when
the images `T eᵢ` are pairwise orthogonal. Then `‖T x‖² = ∑ᵢ ‖⟪eᵢ, x⟫‖² ‖T eᵢ‖²`
(`LinearMap.norm_apply_sq_eq_sum_of_pairwise_inner_eq_zero`), and the approximation numbers of
`T` are the norms `‖T eᵢ‖` listed in nonincreasing order, followed by zeros. No relation between
the dimensions of `E` and `F` is needed, and the target need be neither complete nor
finite-dimensional.

Both directions come from the min–max bounds for approximation numbers. If every basis vector
outside an `n`-element index set is sent to a vector of norm at most `c`, then `T` is bounded by `c`
on the orthogonal complement of the span of that set, so `aₙ(T) ≤ c`. If more than `n` basis
vectors are sent to vectors of norm at least `c`, then `T` is `c`-coercive on their span, so
`c ≤ aₙ(T)`.

The main application is the rectangular diagonal map. For orthonormal bases `(eᵢ)_{i < m}` of `E`
and `(fⱼ)_{j < n}` of `F` and scalars `(dₖ)`, it is the map whose matrix in these bases has `dₖ` at
position `(k, k)` for `k < min m n` and zeros elsewhere, so that `D eₖ = dₖ fₖ` for `k < min m n`
and `D eₖ = 0` otherwise (`Matrix.toLin_of_ite_val_eq_apply`). This is the shape of the middle
factor in the rectangular singular value factorization
`LinearMap.exists_linearIsometryEquiv_eq_comp_toLin_comp`. Its approximation numbers are the
magnitudes `‖dₖ‖`, `k < min m n`, arranged in nonincreasing order, and they vanish from index
`min m n` on.

## Main declarations

* `ContinuousLinearMap.singularValue_le_of_pairwise_inner_eq_zero` and
  `ContinuousLinearMap.le_singularValue_of_pairwise_inner_eq_zero`: the upper and lower bounds
  for a map with pairwise orthogonal basis images.
* `ContinuousLinearMap.singularValue_eq_of_pairwise_inner_eq_zero`: the approximation numbers are
  the sorted norms `‖T eᵢ‖`.
* `Matrix.singularValue_toLin_of_ite_val_eq`,
  `Matrix.singularValue_toLin_of_ite_val_eq_eq_zero_of_le`: the approximation numbers of a
  rectangular diagonal map.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), Chapter 2.
-/

public section

open scoped NNReal InnerProductSpace

variable {𝕜 E F ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [Fintype ι]

namespace ContinuousLinearMap

variable {T : E →L[𝕜] F} {e : OrthonormalBasis ι 𝕜 E}

/-- **Upper bound for a diagonal map.** Let `T` send an orthonormal basis `(eᵢ)` to pairwise
orthogonal vectors. If `‖T eᵢ‖ ≤ c` for every index outside a set of at most `n` indices, then
`aₙ(T) ≤ c`. -/
theorem singularValue_le_of_pairwise_inner_eq_zero
    (hT : Pairwise fun i j ↦ ⟪T (e i), T (e j)⟫_𝕜 = 0) {n : ℕ} {s : Finset ι}
    (hs : s.card ≤ n) {c : ℝ≥0} (hc : ∀ i ∉ s, ‖T (e i)‖ ≤ c) : T.singularValue n ≤ c := by
  have : FiniteDimensional 𝕜 E := Module.Finite.of_basis e.toBasis
  have hV : Module.rank 𝕜 (e.spanIndices s) ≤ n := by
    rw [← Module.finrank_eq_rank, e.finrank_spanIndices]
    exact_mod_cast hs
  refine (T.singularValue_le_nnnorm_comp_orthogonal hV).trans ?_
  refine NNReal.coe_le_coe.mp (opNorm_le_bound _ c.2 fun x ↦ ?_)
  -- The coordinates of `x ∈ (span {eᵢ | i ∈ s})ᗮ` vanish on `s`.
  have hx : ∀ i ∈ s, ⟪e i, (x : E)⟫_𝕜 = 0 := fun i hi ↦
    (Submodule.mem_orthogonal _ _).mp x.2 _ (e.mem_spanIndices_of_mem hi)
  have hpy : ‖T x‖ ^ 2 = _ :=
    (T : E →ₗ[𝕜] F).norm_apply_sq_eq_sum_of_pairwise_inner_eq_zero e hT x
  have hsq : ‖T x‖ ^ 2 ≤ (c * ‖(x : E)‖) ^ 2 := by
    rw [hpy, mul_pow, ← e.sum_sq_norm_inner_right, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    by_cases hi : i ∈ s
    · simp [hx i hi]
    · rw [mul_comm]
      gcongr
      exact hc i hi
  simpa using (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- **Lower bound for a diagonal map.** Let `T` send an orthonormal basis `(eᵢ)` to pairwise
orthogonal vectors. If `c ≤ ‖T eᵢ‖` for every index in a set of more than `n` indices, then
`c ≤ aₙ(T)`. -/
theorem le_singularValue_of_pairwise_inner_eq_zero
    (hT : Pairwise fun i j ↦ ⟪T (e i), T (e j)⟫_𝕜 = 0) {n : ℕ} {s : Finset ι}
    (hs : n < s.card) {c : ℝ} (hc : ∀ i ∈ s, c ≤ ‖T (e i)‖) : c ≤ T.singularValue n := by
  have : FiniteDimensional 𝕜 E := Module.Finite.of_basis e.toBasis
  have hV : (n : Cardinal) < Module.rank 𝕜 (e.spanIndices s) := by
    rw [← Module.finrank_eq_rank, e.finrank_spanIndices]
    exact_mod_cast hs
  rcases le_or_gt c 0 with hc0 | hc0
  · exact hc0.trans (NNReal.coe_nonneg _)
  refine T.le_singularValue_of_lt_rank hV fun x hx ↦ ?_
  -- The coordinates of `x ∈ span {eᵢ | i ∈ s}` vanish off `s`.
  have hx' : ∀ i ∉ s, ⟪e i, x⟫_𝕜 = 0 := fun i hi ↦ by
    rw [← e.repr_apply_apply]
    exact e.repr_eq_zero_of_mem_spanIndices hx hi
  have hpy : ‖T x‖ ^ 2 = _ :=
    (T : E →ₗ[𝕜] F).norm_apply_sq_eq_sum_of_pairwise_inner_eq_zero e hT x
  have hsq : (c * ‖x‖) ^ 2 ≤ ‖T x‖ ^ 2 := by
    rw [hpy, mul_pow, ← e.sum_sq_norm_inner_right, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    by_cases hi : i ∈ s
    · rw [mul_comm]
      gcongr
      exact hc i hi
    · simp [hx' i hi]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp hsq

/-- **Approximation numbers of a diagonal map.** Let `T` send an orthonormal basis `(eᵢ)` to
pairwise orthogonal vectors, and let `π` list `p` indices so that the norms `‖T e_{π k}‖` are
nonincreasing and `T eᵢ = 0` at every unlisted index. Then `aₖ(T) = ‖T e_{π k}‖` for `k < p`.
From index `p` on the approximation numbers vanish: this is
`ContinuousLinearMap.singularValue_le_of_pairwise_inner_eq_zero` with `c = 0`. -/
theorem singularValue_eq_of_pairwise_inner_eq_zero
    (hT : Pairwise fun i j ↦ ⟪T (e i), T (e j)⟫_𝕜 = 0) {p : ℕ} (π : Fin p ↪ ι)
    (hπ : Antitone fun k ↦ ‖T (e (π k))‖) (h0 : ∀ i, i ∉ Set.range π → T (e i) = 0)
    (k : Fin p) : T.singularValue k = ‖T (e (π k))‖₊ := by
  refine le_antisymm (singularValue_le_of_pairwise_inner_eq_zero hT
    (s := (Finset.Iio k).map π) (by simp) fun i hi ↦ ?_) ?_
  · by_cases hr : i ∈ Set.range π
    · obtain ⟨j, rfl⟩ := hr
      exact hπ (by simpa using hi)
    · simp [h0 i hr]
  · exact_mod_cast le_singularValue_of_pairwise_inner_eq_zero hT
      (s := (Finset.Iic k).map π) (by simp) fun i hi ↦ by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
        exact hπ (Finset.mem_Iic.mp hj)

end ContinuousLinearMap

namespace Matrix

variable {m n : ℕ}

/-- The rectangular diagonal map sends the source basis to pairwise orthogonal vectors. -/
private theorem pairwise_inner_toLin_of_ite_val_eq (e : OrthonormalBasis (Fin m) 𝕜 E)
    (f : OrthonormalBasis (Fin n) 𝕜 F) (d : ℕ → 𝕜) :
    Pairwise fun i j : Fin m ↦ ⟪Matrix.toLin e.toBasis f.toBasis (Matrix.of fun (j : Fin n)
      (i : Fin m) ↦ if (j : ℕ) = i then d i else 0) (e i), Matrix.toLin e.toBasis f.toBasis
      (Matrix.of fun (j : Fin n) (i : Fin m) ↦ if (j : ℕ) = i then d i else 0) (e j)⟫_𝕜 = 0 := by
  intro i j hij
  simp only [toLin_of_ite_val_eq_apply]
  split_ifs with hi hj
  · rw [inner_smul_left, inner_smul_right, f.inner_eq_zero (fun h ↦ hij (Fin.ext
      (by simpa using congrArg Fin.val h))), mul_zero, mul_zero]
  all_goals simp

/-- **Approximation numbers of a rectangular diagonal map.** Let `D : E → F` have the matrix with
`dₖ` at position `(k, k)` for `k < min m n` and zeros elsewhere in orthonormal bases of the
`m`-dimensional space `E` and the `n`-dimensional space `F`. If `σ` lists the indices below
`min m n` so that the magnitudes `‖d (σ k)‖` are nonincreasing, then `aₖ(D) = ‖d (σ k)‖`. -/
theorem singularValue_toLin_of_ite_val_eq [FiniteDimensional 𝕜 E]
    (e : OrthonormalBasis (Fin m) 𝕜 E) (f : OrthonormalBasis (Fin n) 𝕜 F) (d : ℕ → 𝕜)
    (σ : Fin (min m n) ≃ Fin (min m n)) (hσ : Antitone fun k ↦ ‖d (σ k)‖) (k : Fin (min m n)) :
    (LinearMap.toContinuousLinearMap (Matrix.toLin e.toBasis f.toBasis (Matrix.of fun (j : Fin n)
      (i : Fin m) ↦ if (j : ℕ) = i then d i else 0))).singularValue k = ‖d (σ k)‖₊ := by
  set D : E →L[𝕜] F := LinearMap.toContinuousLinearMap (Matrix.toLin e.toBasis f.toBasis
    (Matrix.of fun (j : Fin n) (i : Fin m) ↦ if (j : ℕ) = i then d i else 0)) with hD
  have hDe (i : Fin m) : D (e i) = if h : (i : ℕ) < n then d i • f ⟨i, h⟩ else 0 := by
    rw [hD, LinearMap.coe_toContinuousLinearMap', toLin_of_ite_val_eq_apply]
  -- List the source indices below `min m n` in the order given by `σ`.
  let π : Fin (min m n) ↪ Fin m := σ.toEmbedding.trans (Fin.castLEEmb (min_le_left m n))
  have hnorm (k : Fin (min m n)) : ‖D (e (π k))‖ = ‖d (σ k)‖ := by
    have hk : ((σ k : ℕ)) < n := (σ k).isLt.trans_le (min_le_right m n)
    simp [π, hDe, hk, norm_smul]
  have h0 (i : Fin m) (hi : i ∉ Set.range π) : D (e i) = 0 := by
    have hin : ¬(i : ℕ) < n := fun hin ↦
      hi ⟨σ.symm ⟨i, lt_min i.isLt hin⟩, Fin.ext (by simp [π])⟩
    simp [hDe, hin]
  rw [ContinuousLinearMap.singularValue_eq_of_pairwise_inner_eq_zero
    (pairwise_inner_toLin_of_ite_val_eq e f d) π (by simpa only [hnorm] using hσ) h0 k]
  exact NNReal.coe_injective (by simpa using hnorm k)

/-- **Vanishing tail of a rectangular diagonal map.** The approximation numbers of the rectangular
diagonal map vanish from index `min m n` on. -/
theorem singularValue_toLin_of_ite_val_eq_eq_zero_of_le [FiniteDimensional 𝕜 E]
    (e : OrthonormalBasis (Fin m) 𝕜 E) (f : OrthonormalBasis (Fin n) 𝕜 F) (d : ℕ → 𝕜) {k : ℕ}
    (hk : min m n ≤ k) :
    (LinearMap.toContinuousLinearMap (Matrix.toLin e.toBasis f.toBasis (Matrix.of fun (j : Fin n)
      (i : Fin m) ↦ if (j : ℕ) = i then d i else 0))).singularValue k = 0 := by
  refine le_antisymm (ContinuousLinearMap.singularValue_le_of_pairwise_inner_eq_zero
    (pairwise_inner_toLin_of_ite_val_eq e f d)
    (s := ({i | (i : ℕ) < n} : Finset (Fin m))) ?_ fun i hi ↦ ?_) zero_le
  · simpa [Fin.card_filter_val_lt] using hk
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [toLin_of_ite_val_eq_apply, hi]

end Matrix
