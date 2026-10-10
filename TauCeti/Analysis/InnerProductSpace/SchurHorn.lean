/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import TauCeti.Analysis.Convex.DoublyStochasticMatrix
public import TauCeti.Analysis.InnerProductSpace.CourantFischer

import Mathlib.Analysis.Convex.Mul

/-!
# The forward Schur–Horn inequality

Let `T` be a symmetric endomorphism of a finite-dimensional inner product space over `ℝ` or `ℂ`,
with eigenvalues `λᵢ` and orthonormal eigenbasis `(vᵢ)`, and let `(eₖ)` be any orthonormal basis.
The diagonal entries `dₖ = Re⟪T eₖ, eₖ⟫` of `T` in the basis `(eₖ)` are averages of the
eigenvalues:

`dₖ = ∑ᵢ wᵢₖ λᵢ`,   where `wᵢₖ = ‖⟪vᵢ, eₖ⟫‖²`.

The *Schur weight matrix* `w` of two orthonormal bases is doubly stochastic: its entries are
nonnegative, and each row and each column sums to `1` by Parseval's identity. So the diagonal
is the image of the spectrum under a doubly stochastic matrix, and Jensen's inequality gives the
forward Schur–Horn inequality in Karamata form: for every convex `φ`,

`∑ₖ φ(dₖ) ≤ ∑ᵢ φ(λᵢ)`.

The case `φ = x²` says that the Euclidean norm of the diagonal is at most that of the spectrum.
The sum of the diagonal entries is the trace, so it equals the sum of the eigenvalues in every
orthonormal basis.

## Main definitions

* `OrthonormalBasis.schurWeight v e`: the matrix of squared overlaps `‖⟪v i, e k⟫‖²` of two
  orthonormal bases.

## Main results

* `OrthonormalBasis.sum_schurWeight_row`, `OrthonormalBasis.sum_schurWeight_col`: the rows and
  columns of a Schur weight matrix sum to `1`.
* `OrthonormalBasis.schurWeight_mem_doublyStochastic`: a Schur weight matrix of two orthonormal
  bases with a common index type is doubly stochastic.
* `LinearMap.IsSymmetric.re_inner_apply_self_eq_sum_schurWeight_mul_eigenvalues`: the diagonal
  entries of a symmetric operator are Schur-weighted averages of its eigenvalues.
* `LinearMap.IsSymmetric.sum_map_re_inner_apply_self_le_sum_map_eigenvalues`: the forward
  Schur–Horn inequality `∑ₖ φ(dₖ) ≤ ∑ᵢ φ(λᵢ)` for convex `φ`.
* `LinearMap.IsSymmetric.sum_re_inner_apply_self_eq_sum_eigenvalues`: the diagonal entries sum to
  the sum of the eigenvalues in every orthonormal basis.
* `LinearMap.IsSymmetric.sum_sq_re_inner_apply_self_le_sum_sq_eigenvalues`:
  `∑ₖ dₖ² ≤ ∑ᵢ λᵢ²`.

## References

* I. Schur, *Über eine Klasse von Mittelbildungen mit Anwendungen auf die
  Determinantentheorie*, Sitzungsber. Berl. Math. Ges. **22** (1923), 9–20.
* A. W. Marshall, I. Olkin, B. C. Arnold, *Inequalities: Theory of Majorization and Its
  Applications*, 2nd ed., Springer (2011), Theorem 9.B.1.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), §II.1.
-/

public section

open Module (finrank)
open scoped InnerProductSpace Matrix

variable {𝕜 E ι κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι] [Fintype κ]

namespace OrthonormalBasis

/-- The **Schur weight matrix** of two orthonormal bases `v` and `e`: its `(i, k)` entry is the
squared overlap `‖⟪v i, e k⟫‖²`. When `v` is an eigenbasis of a symmetric operator, it expresses
the diagonal of the operator in the basis `e` as an average of the eigenvalues. -/
noncomputable def schurWeight (v : OrthonormalBasis ι 𝕜 E) (e : OrthonormalBasis κ 𝕜 E) :
    Matrix ι κ ℝ :=
  Matrix.of fun i k ↦ ‖⟪v i, e k⟫_𝕜‖ ^ 2

variable (v : OrthonormalBasis ι 𝕜 E) (e : OrthonormalBasis κ 𝕜 E)

@[simp]
theorem schurWeight_apply (i : ι) (k : κ) : v.schurWeight e i k = ‖⟪v i, e k⟫_𝕜‖ ^ 2 := by
  simp [schurWeight]

theorem schurWeight_nonneg (i : ι) (k : κ) : 0 ≤ v.schurWeight e i k := by
  rw [schurWeight_apply]
  positivity

/-- Exchanging the two bases transposes the Schur weight matrix. -/
theorem transpose_schurWeight : (v.schurWeight e).transpose = e.schurWeight v := by
  ext k i
  simp [norm_inner_symm]

/-- Each row of a Schur weight matrix sums to `1`. -/
theorem sum_schurWeight_row (i : ι) : ∑ k, v.schurWeight e i k = 1 := by
  simp [e.sum_sq_norm_inner_left]

/-- Each column of a Schur weight matrix sums to `1`. -/
theorem sum_schurWeight_col (k : κ) : ∑ i, v.schurWeight e i k = 1 := by
  simp [v.sum_sq_norm_inner_right]

/-- The Schur weight matrix of two orthonormal bases with a common index type is doubly
stochastic. -/
theorem schurWeight_mem_doublyStochastic [DecidableEq ι] (v e : OrthonormalBasis ι 𝕜 E) :
    v.schurWeight e ∈ doublyStochastic ℝ ι :=
  mem_doublyStochastic_iff_sum.2
    ⟨v.schurWeight_nonneg e, v.sum_schurWeight_row e, v.sum_schurWeight_col e⟩

end OrthonormalBasis

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} {n : ℕ}

/-- **The diagonal of a symmetric operator is a Schur-weighted average of its spectrum.** For
every orthonormal basis `e`, the diagonal entry `Re⟪T (e k), e k⟫` equals `∑ᵢ wᵢₖ λᵢ`, where `w`
is the Schur weight matrix of the eigenbasis of `T` and `e`. -/
theorem re_inner_apply_self_eq_sum_schurWeight_mul_eigenvalues (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (e : OrthonormalBasis κ 𝕜 E) (k : κ) :
    RCLike.re ⟪T (e k), e k⟫_𝕜 =
      ∑ i, (hT.eigenvectorBasis hn).schurWeight e i k * hT.eigenvalues hn i := by
  simp [hT.re_inner_apply_self_eq_sum_eigenvalues_mul_sq hn, OrthonormalBasis.repr_apply_apply,
    mul_comm]

/-- **Forward Schur–Horn inequality**, Karamata form. If `φ` is convex on a set `s` containing
the eigenvalues of a symmetric operator `T`, then for every orthonormal basis `e`, the sum of
`φ` over the diagonal entries `Re⟪T (e k), e k⟫` is at most the sum of `φ` over the
eigenvalues. -/
theorem sum_map_re_inner_apply_self_le_sum_map_eigenvalues (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (e : OrthonormalBasis κ 𝕜 E) {s : Set ℝ} {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ s φ)
    (hs : ∀ i, hT.eigenvalues hn i ∈ s) :
    ∑ k, φ (RCLike.re ⟪T (e k), e k⟫_𝕜) ≤ ∑ i, φ (hT.eigenvalues hn i) := by
  classical
  -- Reindex `e` by `Fin n`, so that the Schur weight matrix is square.
  let σ : κ ≃ Fin n :=
    Fintype.equivFinOfCardEq ((Module.finrank_eq_card_basis e.toBasis).symm.trans hn)
  let e' := e.reindex σ
  have hdiag : (fun k ↦ RCLike.re ⟪T (e' k), e' k⟫_𝕜) =
      e'.schurWeight (hT.eigenvectorBasis hn) *ᵥ hT.eigenvalues hn := by
    ext k
    rw [hT.re_inner_apply_self_eq_sum_schurWeight_mul_eigenvalues hn,
      ← OrthonormalBasis.transpose_schurWeight]
    simp [Matrix.mulVec, dotProduct]
  calc ∑ k, φ (RCLike.re ⟪T (e k), e k⟫_𝕜)
      = ∑ k, φ (RCLike.re ⟪T (e' k), e' k⟫_𝕜) := by
        rw [← σ.symm.sum_comp]
        simp [e']
    _ = ∑ k, φ ((e'.schurWeight (hT.eigenvectorBasis hn) *ᵥ hT.eigenvalues hn) k) := by
        rw [← hdiag]
    _ ≤ ∑ i, φ (hT.eigenvalues hn i) :=
        hφ.sum_map_mulVec_le_of_mem_doublyStochastic
          (e'.schurWeight_mem_doublyStochastic _) hs

/-- **The trace in an orthonormal basis.** For every orthonormal basis `e`, the diagonal entries
`Re⟪T (e k), e k⟫` of a symmetric operator sum to the sum of its eigenvalues. -/
theorem sum_re_inner_apply_self_eq_sum_eigenvalues (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (e : OrthonormalBasis κ 𝕜 E) :
    ∑ k, RCLike.re ⟪T (e k), e k⟫_𝕜 = ∑ i, hT.eigenvalues hn i := by
  rw [← hT.re_trace_eq_sum_eigenvalues hn, T.trace_eq_sum_inner e, map_sum]
  simp_rw [inner_re_symm (T _)]

/-- **The diagonal is shorter than the spectrum.** For every orthonormal basis `e`, the squared
diagonal entries `Re⟪T (e k), e k⟫` of a symmetric operator sum to at most the sum of the
squared eigenvalues. -/
theorem sum_sq_re_inner_apply_self_le_sum_sq_eigenvalues (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (e : OrthonormalBasis κ 𝕜 E) :
    ∑ k, RCLike.re ⟪T (e k), e k⟫_𝕜 ^ 2 ≤ ∑ i, hT.eigenvalues hn i ^ 2 :=
  hT.sum_map_re_inner_apply_self_le_sum_map_eigenvalues hn e (Even.convexOn_pow even_two)
    fun _ ↦ Set.mem_univ _

end LinearMap.IsSymmetric
