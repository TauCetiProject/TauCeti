/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.InnerProductSpace.OrthogonalFamily
public import TauCeti.Analysis.InnerProductSpace.Parseval
public import TauCeti.Analysis.InnerProductSpace.Spectrum

/-!
# The Schmidt series of a compact operator

Let `T : E →L[𝕜] F` be a bounded map between inner product spaces over `ℝ` or `ℂ` and let `(bᵢ)`
be a Hilbert basis of `E` whose images `T bᵢ` are pairwise orthogonal. Expanding `x` in the
basis gives the Schmidt series
`T x = ∑ᵢ ⟪bᵢ, x⟫ T bᵢ = ∑ᵢ sᵢ ⟪bᵢ, x⟫ fᵢ`, where `sᵢ = ‖T bᵢ‖` and the unit vectors
`fᵢ = sᵢ⁻¹ T bᵢ`, for `sᵢ ≠ 0`, form an orthonormal family of `F`. Orthogonality of the images
gives Pythagoras, `‖T x‖² = ∑ᵢ ‖⟪bᵢ, x⟫‖² sᵢ²`, from which the norm of `T` on vectors supported
on a set of indices is controlled by the values `sᵢ` on that set. In particular, truncating the
series to a finite set `s` of indices leaves an error of operator norm at most the largest `sᵢ`
with `i ∉ s`, and each `bᵢ` with `sᵢ ≠ 0` is orthogonal to the kernel of `T`.

If `T` is compact, the images `T bᵢ` lie in a relatively compact set and are pairwise at distance
at least `√2 ε` once their norms are at least `ε`, so only finitely many `sᵢ` exceed any positive
threshold. The values `sᵢ` therefore tend to zero along the cofinite filter, and the Schmidt
series converges to `T` in operator norm.

Such a basis exists for every compact operator between Hilbert spaces: an orthonormal basis of
eigenvectors of the compact positive operator `T† T`, provided by
`ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector`, has pairwise orthogonal images,
since `⟪T bᵢ, T bⱼ⟫ = ⟪bᵢ, T† T bⱼ⟫`. The `sᵢ` are then the square roots of the eigenvalues of
`T† T`, the singular values of `T`, and `(bᵢ)` and `(fᵢ)` are its right and left singular
vectors.

## Main declarations

* `HilbertBasis.hasSum_inner_smul_apply`: `T x = ∑ᵢ ⟪bᵢ, x⟫ T bᵢ`.
* `HilbertBasis.hasSum_norm_sq_inner_mul_norm_sq_apply`: Pythagoras,
  `‖T x‖² = ∑ᵢ ‖⟪bᵢ, x⟫‖² ‖T bᵢ‖²`, for pairwise orthogonal images.
* `HilbertBasis.norm_apply_le_of_forall_inner_eq_zero` and
  `HilbertBasis.mul_norm_le_norm_apply_of_forall_inner_eq_zero`: upper and lower bounds for `T`
  on vectors whose coordinates vanish outside or inside a set of indices.
* `HilbertBasis.inner_eq_zero_of_apply_eq_zero`: the basis vectors with nonzero image are
  orthogonal to the kernel of `T`.
* `HilbertBasis.norm_sub_sum_rankOne_le`: the error of a finite truncation of the Schmidt series.
* `Orthonormal.finite_setOf_le_norm_apply` and `Orthonormal.tendsto_norm_apply_cofinite`: for
  compact `T` and an orthonormal family `(vᵢ)` with pairwise orthogonal images, only finitely many
  `‖T vᵢ‖` exceed any positive threshold.
* `HilbertBasis.hasSum_rankOne`: for compact `T`, the Schmidt series
  `∑ᵢ ⟪bᵢ, ·⟫ T bᵢ` converges to `T` in operator norm.
* `IsCompactOperator.exists_hilbertBasis_pairwise_inner_eq_zero`: a compact operator between
  Hilbert spaces sends some Hilbert basis to pairwise orthogonal vectors.

## References

* E. Schmidt, *Zur Theorie der linearen und nichtlinearen Integralgleichungen. I. Teil:
  Entwicklung willkürlicher Funktionen nach Systemen vorgeschriebener*, Math. Ann. **63**
  (1907), 433–476.
* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators*,
  Translations of Mathematical Monographs 18, AMS (1969), Chapter II, §2.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), §2.11.
-/

public section

open Filter Topology InnerProductSpace
open scoped InnerProductSpace

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace Orthonormal

variable {v : ι → E} (hv : Orthonormal 𝕜 v) {T : E →L[𝕜] F}
include hv

/-- **Finitely many large singular values.** If `T` is compact and sends the orthonormal
family `(vᵢ)` to pairwise orthogonal vectors, then only finitely many `‖T vᵢ‖` are at least a
given `ε > 0`. -/
theorem finite_setOf_le_norm_apply (hTc : IsCompactOperator T)
    (hT : Pairwise fun i j ↦ ⟪T (v i), T (v j)⟫_𝕜 = 0) {ε : ℝ} (hε : 0 < ε) :
    {i | ε ≤ ‖T (v i)‖}.Finite := by
  -- The images lie in the totally bounded set `T (closedBall 0 1)`, which is covered by
  -- finitely many balls of radius `ε / 2`.
  obtain ⟨t, -, ht, hcover⟩ := Metric.finite_approx_of_totallyBounded
    (hTc.isCompact_closure_image_closedBall 1).totallyBounded (ε / 2) (half_pos hε)
  have hmem (i : ι) : ∃ y ∈ t, dist (T (v i)) y < ε / 2 := by
    have : T (v i) ∈ closure (T '' Metric.closedBall 0 1) :=
      subset_closure ⟨v i, mem_closedBall_zero_iff.mpr (hv.1 i).le, rfl⟩
    simpa only [Set.mem_iUnion, Metric.mem_ball, exists_prop] using hcover this
  choose g hgt hgd using hmem
  refine Set.Finite.of_finite_image (ht.subset (Set.image_subset_iff.mpr fun i _ ↦ hgt i))
    fun i hi j hj hij ↦ ?_
  -- Two distinct large images are at distance at least `√2 ε > ε`, so they lie in different
  -- balls of radius `ε / 2`.
  by_contra hne
  have hdist : dist (T (v i)) (T (v j)) < ε := by
    calc dist (T (v i)) (T (v j)) ≤ dist (T (v i)) (g i) + dist (T (v j)) (g j) := by
          rw [hij]
          exact dist_triangle_right _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hgd i) (hgd j)
      _ = ε := add_halves ε
  have hsq : ‖T (v i) - T (v j)‖ ^ 2 = ‖T (v i)‖ ^ 2 + ‖T (v j)‖ ^ 2 := by
    rw [@norm_sub_sq 𝕜, hT hne, map_zero, mul_zero, sub_zero]
  have hi' : ε ^ 2 ≤ ‖T (v i)‖ ^ 2 := pow_le_pow_left₀ hε.le hi 2
  have hj' : ε ^ 2 ≤ ‖T (v j)‖ ^ 2 := pow_le_pow_left₀ hε.le hj 2
  have hlt : ε ^ 2 < ‖T (v i) - T (v j)‖ ^ 2 := by nlinarith
  rw [dist_eq_norm] at hdist
  exact hlt.not_ge (pow_le_pow_left₀ (norm_nonneg _) hdist.le 2)

/-- **The singular values of a compact operator tend to zero.** If `T` is compact and sends the
orthonormal family `(vᵢ)` to pairwise orthogonal vectors, then `‖T vᵢ‖ → 0` along the cofinite
filter. -/
theorem tendsto_norm_apply_cofinite (hTc : IsCompactOperator T)
    (hT : Pairwise fun i j ↦ ⟪T (v i), T (v j)⟫_𝕜 = 0) :
    Tendsto (fun i ↦ ‖T (v i)‖) cofinite (𝓝 0) :=
  tendsto_order.2 ⟨fun _ ha ↦ Eventually.of_forall fun _ ↦ ha.trans_le (norm_nonneg _),
    fun _ hε ↦ eventually_cofinite.2 (by
      simpa only [not_lt] using hv.finite_setOf_le_norm_apply hTc hT hε)⟩

end Orthonormal

namespace HilbertBasis

variable (b : HilbertBasis ι 𝕜 E) {T : E →L[𝕜] F}

/-- **Expansion of an operator in a Hilbert basis.** `T x = ∑ᵢ ⟪bᵢ, x⟫ T bᵢ`. -/
theorem hasSum_inner_smul_apply (T : E →L[𝕜] F) (x : E) :
    HasSum (fun i ↦ ⟪b i, x⟫_𝕜 • T (b i)) (T x) := by
  simpa only [map_smul, b.repr_apply_apply] using T.hasSum (b.hasSum_repr x)

/-- **Pythagoras for an operator with orthogonal basis images.** If `T` sends the Hilbert basis
`(bᵢ)` to pairwise orthogonal vectors, then `‖T x‖² = ∑ᵢ ‖⟪bᵢ, x⟫‖² ‖T bᵢ‖²`. -/
theorem hasSum_norm_sq_inner_mul_norm_sq_apply
    (hT : Pairwise fun i j ↦ ⟪T (b i), T (b j)⟫_𝕜 = 0) (x : E) :
    HasSum (fun i ↦ ‖⟪b i, x⟫_𝕜‖ ^ 2 * ‖T (b i)‖ ^ 2) (‖T x‖ ^ 2) := by
  have hv : Pairwise fun i j ↦ ⟪⟪b i, x⟫_𝕜 • T (b i), ⟪b j, x⟫_𝕜 • T (b j)⟫_𝕜 = 0 :=
    fun i j hij ↦ by simp [inner_smul_left, inner_smul_right, hT hij]
  simpa only [norm_smul, mul_pow] using
    TauCeti.hasSum_norm_sq_of_pairwise_inner_eq_zero hv (b.hasSum_inner_smul_apply T x)

/-- **Upper bound on vectors supported off a set of indices.** Let `T` send the Hilbert basis
`(bᵢ)` to pairwise orthogonal vectors, and let `‖T bᵢ‖ ≤ c` for `i ∉ s`. If the coordinates of
`x` vanish on `s`, then `‖T x‖ ≤ c ‖x‖`. -/
theorem norm_apply_le_of_forall_inner_eq_zero
    (hT : Pairwise fun i j ↦ ⟪T (b i), T (b j)⟫_𝕜 = 0) {s : Set ι} {c : ℝ}
    (hc : ∀ i ∉ s, ‖T (b i)‖ ≤ c) {x : E} (hx : ∀ i ∈ s, ⟪b i, x⟫_𝕜 = 0) :
    ‖T x‖ ≤ c * ‖x‖ := by
  rcases lt_or_ge c 0 with hc0 | hc0
  · -- A negative bound forces every index into `s`, so that `x = 0`.
    have hx0 : ‖x‖ ^ 2 = 0 := (b.hasSum_norm_sq_inner x).unique (by
      convert hasSum_zero with i
      by_cases hi : i ∈ s
      · simp [hx i hi]
      · exact ((norm_nonneg _).trans (hc i hi) |>.not_gt hc0).elim)
    simp [norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hx0)]
  have hsq : ‖T x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by
    rw [mul_pow]
    refine hasSum_le (fun i ↦ ?_) (b.hasSum_norm_sq_inner_mul_norm_sq_apply hT x)
      ((b.hasSum_norm_sq_inner x).mul_left (c ^ 2))
    by_cases hi : i ∈ s
    · simp [hx i hi]
    · rw [mul_comm]
      gcongr
      exact hc i hi
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- **Lower bound on vectors supported on a set of indices.** Let `T` send the Hilbert basis
`(bᵢ)` to pairwise orthogonal vectors, and let `c ≤ ‖T bᵢ‖` for `i ∈ s`. If the coordinates of
`x` vanish off `s`, then `c ‖x‖ ≤ ‖T x‖`. -/
theorem mul_norm_le_norm_apply_of_forall_inner_eq_zero
    (hT : Pairwise fun i j ↦ ⟪T (b i), T (b j)⟫_𝕜 = 0) {s : Set ι} {c : ℝ}
    (hc : ∀ i ∈ s, c ≤ ‖T (b i)‖) {x : E} (hx : ∀ i ∉ s, ⟪b i, x⟫_𝕜 = 0) :
    c * ‖x‖ ≤ ‖T x‖ := by
  rcases le_or_gt c 0 with hc0 | hc0
  · exact (mul_nonpos_of_nonpos_of_nonneg hc0 (norm_nonneg _)).trans (norm_nonneg _)
  have hsq : (c * ‖x‖) ^ 2 ≤ ‖T x‖ ^ 2 := by
    rw [mul_pow]
    refine hasSum_le (fun i ↦ ?_) ((b.hasSum_norm_sq_inner x).mul_left (c ^ 2))
      (b.hasSum_norm_sq_inner_mul_norm_sq_apply hT x)
    by_cases hi : i ∈ s
    · rw [mul_comm]
      gcongr
      exact hc i hi
    · simp [hx i hi]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp hsq

/-- **The singular vectors are orthogonal to the kernel.** If `T` sends the Hilbert basis `(bᵢ)`
to pairwise orthogonal vectors, then every `bᵢ` with `T bᵢ ≠ 0` is orthogonal to every `x` with
`T x = 0`. -/
theorem inner_eq_zero_of_apply_eq_zero (hT : Pairwise fun i j ↦ ⟪T (b i), T (b j)⟫_𝕜 = 0)
    {x : E} (hx : T x = 0) {i : ι} (hi : T (b i) ≠ 0) : ⟪b i, x⟫_𝕜 = 0 := by
  have h := b.hasSum_norm_sq_inner_mul_norm_sq_apply hT x
  rw [hx, norm_zero, zero_pow two_ne_zero, hasSum_zero_iff_of_nonneg fun _ ↦ by positivity] at h
  simpa [hi] using congrFun h i

/-- **Truncation error of the Schmidt series.** Let `T` send the Hilbert basis `(bᵢ)` to pairwise
orthogonal vectors. If `‖T bᵢ‖ ≤ c` for every `i ∉ s`, then the truncation of the series
`∑ᵢ ⟪bᵢ, ·⟫ T bᵢ` to `s` approximates `T` within `c` in operator norm. -/
theorem norm_sub_sum_rankOne_le (hT : Pairwise fun i j ↦ ⟪T (b i), T (b j)⟫_𝕜 = 0)
    {s : Finset ι} {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ i ∉ s, ‖T (b i)‖ ≤ c) :
    ‖T - ∑ i ∈ s, rankOne 𝕜 (T (b i)) (b i)‖ ≤ c := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ hc0 fun x ↦ ?_
  set y := x - ∑ j ∈ s, ⟪b j, x⟫_𝕜 • b j
  have hy : (T - ∑ i ∈ s, rankOne 𝕜 (T (b i)) (b i)) x = T y := by
    simp [y, map_sub, map_sum, map_smul]
  -- On `y` only the coordinates outside `s` survive, and they are those of `x`.
  have hcoord (i : ι) : ⟪b i, y⟫_𝕜 = if i ∈ s then 0 else ⟪b i, x⟫_𝕜 := by
    rw [inner_sub_right]
    split_ifs with hi
    · rw [b.orthonormal.inner_right_sum _ hi, sub_self]
    · rw [inner_sum, Finset.sum_eq_zero fun j hj ↦ ?_, sub_zero]
      rw [inner_smul_right, b.orthonormal.inner_eq_zero (ne_of_mem_of_not_mem hj hi).symm,
        mul_zero]
  have hTy : ‖T y‖ ≤ c * ‖y‖ :=
    b.norm_apply_le_of_forall_inner_eq_zero hT (s := ↑s) hc fun i hi ↦ by
      simp [hcoord i, Finset.mem_coe.mp hi]
  -- Dropping coordinates does not increase the norm.
  have hyx : ‖y‖ ≤ ‖x‖ := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (hasSum_le (fun i ↦ ?_) (b.hasSum_norm_sq_inner y) (b.hasSum_norm_sq_inner x))
    rw [hcoord i]
    split_ifs <;> simp
  rw [hy]
  exact hTy.trans (by gcongr)

/-- **The Schmidt series converges in operator norm.** If `T` is compact and sends the Hilbert
basis `(bᵢ)` to pairwise orthogonal vectors, then `T = ∑ᵢ ⟪bᵢ, ·⟫ T bᵢ`, the sum converging in
the operator norm along finite sets of indices. -/
theorem hasSum_rankOne (hTc : IsCompactOperator T)
    (hT : Pairwise fun i j ↦ ⟪T (b i), T (b j)⟫_𝕜 = 0) :
    HasSum (fun i ↦ rankOne 𝕜 (T (b i)) (b i)) T := by
  classical
  rw [HasSum, SummationFilter.unconditional_filter]
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  -- Once a truncation contains every index with `‖T bᵢ‖ ≥ ε / 2`, its error is at most `ε / 2`.
  obtain ⟨N, hN⟩ :=
    (b.orthonormal.finite_setOf_le_norm_apply hTc hT (half_pos hε)).exists_finset_coe
  refine ⟨N, fun s hs ↦ ?_⟩
  rw [dist_eq_norm']
  refine (b.norm_sub_sum_rankOne_le hT (half_pos hε).le fun i hi ↦ ?_).trans_lt (half_lt_self hε)
  refine le_of_lt (not_le.mp fun h ↦ hi (hs ?_))
  rw [← Finset.mem_coe, hN]
  exact h

end HilbertBasis

/-- **Existence of a Schmidt basis.** A compact operator between Hilbert spaces sends some
Hilbert basis of its source to pairwise orthogonal vectors: any orthonormal basis of eigenvectors
of `T† T` does, because `⟪T bᵢ, T bⱼ⟫ = ⟪bᵢ, T† T bⱼ⟫`. -/
theorem IsCompactOperator.exists_hilbertBasis_pairwise_inner_eq_zero [CompleteSpace E]
    [CompleteSpace F] {T : E →L[𝕜] F} (hT : IsCompactOperator T) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E), ⇑b = ((↑) : s → E) ∧
      Pairwise fun i j ↦ ⟪T (b i), T (b j)⟫_𝕜 = 0 := by
  set A : E →L[𝕜] E := ContinuousLinearMap.adjoint T ∘L T
  have hA : IsCompactOperator A := hT.clm_comp _
  have hA' : (A : E →ₗ[𝕜] E).IsSymmetric := fun x y ↦ by
    simp [A, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  obtain ⟨s, b, nu, hb, hev⟩ := ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector hA hA'
  refine ⟨s, b, hb, fun i j hij ↦ ?_⟩
  have hj : A (b j) = nu j • b j := by
    rw [hb]
    exact Module.End.mem_eigenspace_iff.mp (hev j).1
  calc ⟪T (b i), T (b j)⟫_𝕜 = ⟪b i, A (b j)⟫_𝕜 :=
        (ContinuousLinearMap.adjoint_inner_right T (b i) (T (b j))).symm
    _ = 0 := by rw [hj, inner_smul_right, b.orthonormal.inner_eq_zero hij, mul_zero]
