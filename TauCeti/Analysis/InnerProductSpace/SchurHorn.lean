/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import TauCeti.Analysis.Convex.DoublyStochasticMatrix
public import TauCeti.Analysis.Convex.Majorization
public import TauCeti.Analysis.Convex.PermutationOrbit
public import TauCeti.Analysis.InnerProductSpace.CourantFischer

import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Schur–Horn theorem

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

By Birkhoff's theorem the doubly stochastic matrices are the convex combinations of permutation
matrices, so the diagonal lies in the convex hull of the rearrangements of the spectrum.

The case `φ = x²` says that the Euclidean norm of the diagonal is at most that of the spectrum.
The sum of the diagonal entries is the trace, so it equals the sum of the eigenvalues in every
orthonormal basis.

Conversely (Horn), every point of that convex hull is the diagonal of `T` in some orthonormal
basis. Rotating two basis vectors `eᵢ, eⱼ` in the plane they span moves the diagonal entry at `i`
continuously from `dᵢ` to `dⱼ` while keeping `dᵢ + dⱼ` and the other entries fixed, so the
diagonals of `T` are closed under Robin Hood transfers. Since they contain the spectrum, the
transfer closure theorem of `TauCeti.Analysis.Convex.Majorization` and Rado's description of the
permutohedron by majorization show that they fill the convex hull. Thus the diagonals of `T` are
exactly the tuples majorized by its spectrum.

## Main definitions

* `OrthonormalBasis.schurWeight v e`: the matrix of squared overlaps `‖⟪v i, e k⟫‖²` of two
  orthonormal bases.

## Main results

* `OrthonormalBasis.sum_schurWeight_row`, `OrthonormalBasis.sum_schurWeight_col`: the rows and
  columns of a Schur weight matrix sum to `1`.
* `OrthonormalBasis.schurWeight_mem_doublyStochastic`: a Schur weight matrix of two orthonormal
  bases with a common index type is doubly stochastic.
* `LinearMap.IsSymmetric.re_inner_apply_self_eq_sum_schurWeight_mul_eigenvalues`: the diagonal
  entries of a symmetric operator are Schur-weighted averages of its eigenvalues;
  `LinearMap.IsSymmetric.re_inner_apply_self_eq_schurWeight_mulVec_eigenvalues` is the same
  statement as a matrix-vector product.
* `LinearMap.IsSymmetric.re_inner_apply_self_mem_convexHull_eigenvalues_comp_perm`: by
  Birkhoff's theorem, the diagonal lies in the convex hull of the rearrangements of the spectrum.
* `LinearMap.IsSymmetric.sum_map_re_inner_apply_self_le_sum_map_eigenvalues`: the forward
  Schur–Horn inequality `∑ₖ φ(dₖ) ≤ ∑ᵢ φ(λᵢ)` for convex `φ`.
* `LinearMap.IsSymmetric.sum_re_inner_apply_self_eq_sum_eigenvalues`: the diagonal entries sum to
  the sum of the eigenvalues in every orthonormal basis.
* `LinearMap.IsSymmetric.sum_sq_re_inner_apply_self_le_sum_sq_eigenvalues`:
  `∑ₖ dₖ² ≤ ∑ᵢ λᵢ²`.
* `LinearMap.IsSymmetric.sum_mul_re_inner_apply_self_le_sum_mul_eigenvalues`: for a decreasing
  weight sequence `c`, `∑ₖ cₖ dₖ ≤ ∑ₖ cₖ λₖ`, with the eigenvalues listed in decreasing order.
* `LinearMap.IsSymmetric.exists_orthonormalBasis_re_inner_apply_self_eq_robinHood`: a rotation in
  a coordinate plane realizes any Robin Hood transfer from a diagonal entry to a smaller one.
* `LinearMap.IsSymmetric.exists_orthonormalBasis_re_inner_apply_self_eq_of_mem_convexHull`:
  Horn's theorem, every point of the permutohedron of the spectrum is a diagonal of `T`.
* `LinearMap.IsSymmetric.range_re_inner_apply_self_eq_convexHull_eigenvalues_comp_perm`: the
  Schur–Horn theorem, the diagonals of `T` are exactly the permutohedron of its spectrum.
* `LinearMap.IsSymmetric.exists_orthonormalBasis_re_inner_apply_self_eq_iff`: the Schur–Horn
  theorem in majorization form.

## References

* I. Schur, *Über eine Klasse von Mittelbildungen mit Anwendungen auf die
  Determinantentheorie*, Sitzungsber. Berl. Math. Ges. **22** (1923), 9–20.
* A. Horn, *Doubly stochastic matrices and the diagonal of a rotation matrix*, Amer. J. Math.
  **76** (1954), 620–630.
* A. W. Marshall, I. Olkin, B. C. Arnold, *Inequalities: Theory of Majorization and Its
  Applications*, 2nd ed., Springer (2011), Theorems 9.B.1 and 9.B.2.
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

/-- **The diagonal of a symmetric operator is the image of its spectrum under a Schur weight
matrix.** For every orthonormal basis `e`, the vector of diagonal entries `Re⟪T (e k), e k⟫` is
`w *ᵥ λ`, where `w` is the Schur weight matrix of `e` and the eigenbasis of `T`. -/
theorem re_inner_apply_self_eq_schurWeight_mulVec_eigenvalues (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (e : OrthonormalBasis κ 𝕜 E) :
    (fun k ↦ RCLike.re ⟪T (e k), e k⟫_𝕜) =
      e.schurWeight (hT.eigenvectorBasis hn) *ᵥ hT.eigenvalues hn := by
  ext k
  rw [hT.re_inner_apply_self_eq_sum_schurWeight_mul_eigenvalues hn,
    ← OrthonormalBasis.transpose_schurWeight]
  simp [Matrix.mulVec, dotProduct]

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
  calc ∑ k, φ (RCLike.re ⟪T (e k), e k⟫_𝕜)
      = ∑ k, φ (RCLike.re ⟪T (e' k), e' k⟫_𝕜) := by
        rw [← σ.symm.sum_comp]
        simp [e']
    _ = ∑ k, φ ((e'.schurWeight (hT.eigenvectorBasis hn) *ᵥ hT.eigenvalues hn) k) := by
        rw [← hT.re_inner_apply_self_eq_schurWeight_mulVec_eigenvalues hn]
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

/-- **The diagonal lies in the permutohedron of the spectrum.** For every orthonormal basis `e`
indexed by `Fin n`, the vector of diagonal entries `Re⟪T (e k), e k⟫` of a symmetric operator `T`
lies in the convex hull of the rearrangements `λ ∘ σ` of its eigenvalues. -/
theorem re_inner_apply_self_mem_convexHull_eigenvalues_comp_perm (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (e : OrthonormalBasis (Fin n) 𝕜 E) :
    (fun k ↦ RCLike.re ⟪T (e k), e k⟫_𝕜) ∈
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) ↦ hT.eigenvalues hn ∘ σ) := by
  rw [hT.re_inner_apply_self_eq_schurWeight_mulVec_eigenvalues hn]
  exact Matrix.mulVec_mem_convexHull_range_comp_perm (e.schurWeight_mem_doublyStochastic _) _

/-- **Sorted weights of the diagonal.** For a symmetric `T`, an orthonormal basis `e`, and a
decreasing weight sequence `c`, the `c`-weighted sum of the diagonal entries `Re⟪T eₖ, eₖ⟫` is
at most the `c`-weighted sum of the eigenvalues of `T`, listed in decreasing order. -/
theorem sum_mul_re_inner_apply_self_le_sum_mul_eigenvalues (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (e : OrthonormalBasis (Fin n) 𝕜 E) {c : Fin n → ℝ}
    (hc : Antitone c) :
    ∑ k, c k * RCLike.re ⟪T (e k), e k⟫_𝕜 ≤ ∑ i, c i * hT.eigenvalues hn i := by
  -- The diagonal is the image of the spectrum under the doubly stochastic Schur weights.
  have hdiag : ∑ k, c k * RCLike.re ⟪T (e k), e k⟫_𝕜 =
      c ⬝ᵥ (e.schurWeight (hT.eigenvectorBasis hn) *ᵥ hT.eigenvalues hn) := by
    simp [hT.re_inner_apply_self_eq_sum_schurWeight_mul_eigenvalues hn,
      OrthonormalBasis.schurWeight_apply, dotProduct, Matrix.mulVec, norm_inner_symm]
  rw [hdiag]
  exact (hc.monovary (hT.eigenvalues_antitone hn)).dotProduct_mulVec_le_of_mem_doublyStochastic
    (e.schurWeight_mem_doublyStochastic _)

end LinearMap.IsSymmetric

/-! ### The converse: Horn's theorem -/

namespace OrthonormalBasis

variable [DecidableEq ι]

/-- The family obtained from `e` by rotating the pair `e i, e j` through the angle `θ` in the
plane they span, fixing the other vectors. -/
private noncomputable def planeRotation (e : OrthonormalBasis ι 𝕜 E) (i j : ι) (θ : ℝ) :
    ι → E := fun k ↦
  if k = i then (Real.cos θ : 𝕜) • e i + (Real.sin θ : 𝕜) • e j
  else if k = j then -((Real.sin θ : 𝕜) • e i) + (Real.cos θ : 𝕜) • e j else e k

private theorem orthonormal_planeRotation (e : OrthonormalBasis ι 𝕜 E) {i j : ι} (hij : i ≠ j)
    (θ : ℝ) : Orthonormal 𝕜 (e.planeRotation i j θ) := by
  have he := orthonormal_iff_ite.1 e.orthonormal
  have hcs : (Real.cos θ : 𝕜) * Real.cos θ + Real.sin θ * Real.sin θ = 1 := by
    rw [← RCLike.ofReal_mul, ← RCLike.ofReal_mul, ← RCLike.ofReal_add, ← sq, ← sq,
      Real.cos_sq_add_sin_sq, RCLike.ofReal_one]
  rw [orthonormal_iff_ite]
  intro a b
  -- Expand both vectors in the basis `e`, case by case on the positions of `a` and `b`.
  rcases eq_or_ne a i with rfl | hai
  · rcases eq_or_ne b a with rfl | hba
    · simp only [planeRotation, ite_true, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, he, hij, hij.symm, ite_false, RCLike.conj_ofReal]
      linear_combination hcs
    rcases eq_or_ne b j with rfl | hbj
    · simp only [planeRotation, ite_true, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, inner_neg_right, he, hij, hij.symm, ite_false, RCLike.conj_ofReal]
      ring
    · simp only [planeRotation, ite_true, hba, hbj, inner_add_left, inner_smul_left, he,
        hba.symm, hbj.symm, ite_false]
      ring
  rcases eq_or_ne a j with rfl | haj
  · rcases eq_or_ne b a with rfl | hba
    · simp only [planeRotation, ite_true, hai, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, inner_neg_left, inner_neg_right, he, hij, ite_false,
        RCLike.conj_ofReal]
      linear_combination hcs
    rcases eq_or_ne b i with rfl | hbi
    · simp only [planeRotation, ite_true, hai, hba, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, inner_neg_left, he, ite_false,
        RCLike.conj_ofReal]
      ring
    · simp only [planeRotation, ite_true, hai, hba, hbi, inner_add_left, inner_smul_left,
        inner_neg_left, he, hba.symm, hbi.symm, ite_false]
      ring
  · rcases eq_or_ne b i with rfl | hbi
    · simp only [planeRotation, hai, haj, ite_true, ite_false, inner_add_right, inner_smul_right,
        he]
      ring
    rcases eq_or_ne b j with rfl | hbj
    · simp only [planeRotation, hai, haj, hbi, ite_true, ite_false, inner_add_right,
        inner_neg_right, inner_smul_right, he]
      ring
    · simp only [planeRotation, hai, haj, hbi, hbj, ite_false, he]

variable {T : E →ₗ[𝕜] E}

private theorem planeRotation_apply_of_ne (e : OrthonormalBasis ι 𝕜 E) {i j k : ι} (hki : k ≠ i)
    (hkj : k ≠ j) (θ : ℝ) : e.planeRotation i j θ k = e k := by
  simp [planeRotation, hki, hkj]

/-- The diagonal entry of a symmetric operator at the first rotated vector. -/
private theorem re_inner_planeRotation_left (hT : T.IsSymmetric) (e : OrthonormalBasis ι 𝕜 E)
    (i j : ι) (θ : ℝ) :
    RCLike.re ⟪T (e.planeRotation i j θ i), e.planeRotation i j θ i⟫_𝕜 =
      Real.cos θ ^ 2 * RCLike.re ⟪T (e i), e i⟫_𝕜 +
        Real.sin θ ^ 2 * RCLike.re ⟪T (e j), e j⟫_𝕜 +
          2 * Real.cos θ * Real.sin θ * RCLike.re ⟪T (e i), e j⟫_𝕜 := by
  have hsym : RCLike.re ⟪T (e j), e i⟫_𝕜 = RCLike.re ⟪T (e i), e j⟫_𝕜 := by
    rw [hT, inner_re_symm]
  simp only [planeRotation, ite_true, map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, RCLike.conj_ofReal, RCLike.re_ofReal_mul, hsym]
  ring

/-- The diagonal entry of a symmetric operator at the second rotated vector. -/
private theorem re_inner_planeRotation_right (hT : T.IsSymmetric) (e : OrthonormalBasis ι 𝕜 E)
    {i j : ι} (hij : i ≠ j) (θ : ℝ) :
    RCLike.re ⟪T (e.planeRotation i j θ j), e.planeRotation i j θ j⟫_𝕜 =
      Real.sin θ ^ 2 * RCLike.re ⟪T (e i), e i⟫_𝕜 +
        Real.cos θ ^ 2 * RCLike.re ⟪T (e j), e j⟫_𝕜 -
          2 * Real.cos θ * Real.sin θ * RCLike.re ⟪T (e i), e j⟫_𝕜 := by
  have hsym : RCLike.re ⟪T (e j), e i⟫_𝕜 = RCLike.re ⟪T (e i), e j⟫_𝕜 := by
    rw [hT, inner_re_symm]
  simp only [planeRotation, hij.symm, ite_true, ite_false, map_add, map_neg, map_smul,
    inner_add_left, inner_add_right, inner_neg_left, inner_neg_right, inner_smul_left,
    inner_smul_right, RCLike.conj_ofReal, RCLike.re_ofReal_mul, map_neg, hsym]
  ring

end OrthonormalBasis

namespace LinearMap.IsSymmetric

open TauCeti

variable {T : E →ₗ[𝕜] E} {n : ℕ}

/-- **A plane rotation realizes a Robin Hood transfer of the diagonal.** Let `dₖ = Re⟪T eₖ, eₖ⟫`
be the diagonal of a symmetric operator `T` in an orthonormal basis `e`. For `0 ≤ δ ≤ dᵢ - dⱼ`,
rotating `eᵢ` and `eⱼ` in the plane they span gives an orthonormal basis in which the diagonal of
`T` is `robinHood d i j δ`: the entry at `i` drops by `δ`, the entry at `j` rises by `δ`, and the
other entries are unchanged. -/
theorem exists_orthonormalBasis_re_inner_apply_self_eq_robinHood [DecidableEq ι]
    (hT : T.IsSymmetric) (e : OrthonormalBasis ι 𝕜 E) (i j : ι) {δ : ℝ} (hδ : 0 ≤ δ)
    (hδ' : δ ≤ RCLike.re ⟪T (e i), e i⟫_𝕜 - RCLike.re ⟪T (e j), e j⟫_𝕜) :
    ∃ e' : OrthonormalBasis ι 𝕜 E, (fun k ↦ RCLike.re ⟪T (e' k), e' k⟫_𝕜) =
      robinHood (fun k ↦ RCLike.re ⟪T (e k), e k⟫_𝕜) i j δ := by
  rcases eq_or_ne i j with rfl | hij
  · exact ⟨e, by simp⟩
  have : FiniteDimensional 𝕜 E := .of_basis e.toBasis
  -- The diagonal entry at `i` after rotating by `θ` moves continuously from its value at `i` for
  -- `θ = 0` to its value at `j` for `θ = π / 2`, so it takes every value in between.
  set g : ℝ → ℝ := fun θ ↦
    Real.cos θ ^ 2 * RCLike.re ⟪T (e i), e i⟫_𝕜 + Real.sin θ ^ 2 * RCLike.re ⟪T (e j), e j⟫_𝕜 +
      2 * Real.cos θ * Real.sin θ * RCLike.re ⟪T (e i), e j⟫_𝕜
  have hg : Continuous g := by fun_prop
  obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc' Real.pi_div_two_pos.le hg.continuousOn
    (show RCLike.re ⟪T (e i), e i⟫_𝕜 - δ ∈ Set.Icc (g (Real.pi / 2)) (g 0) by
      simp only [g, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero]
      constructor <;> linarith)
  have hon := e.orthonormal_planeRotation hij θ
  refine ⟨OrthonormalBasis.mk hon (hon.linearIndependent.span_eq_top_of_card_eq_finrank'
    (Module.finrank_eq_card_basis e.toBasis).symm).ge, funext fun k ↦ ?_⟩
  simp only [OrthonormalBasis.coe_mk]
  rcases eq_or_ne k i with rfl | hki
  · rw [e.re_inner_planeRotation_left hT, robinHood_apply_left _ hij]
    exact hθ
  rcases eq_or_ne k j with rfl | hkj
  · rw [e.re_inner_planeRotation_right hT hij, robinHood_apply_right _ hij]
    linear_combination (RCLike.re ⟪T (e i), e i⟫_𝕜 + RCLike.re ⟪T (e k), e k⟫_𝕜) *
      Real.cos_sq_add_sin_sq θ - hθ
  · rw [e.planeRotation_apply_of_ne hki hkj, robinHood_apply_of_ne _ hki hkj]

variable [FiniteDimensional 𝕜 E]

/-- **Horn's theorem.** Every point `d` of the convex hull of the rearrangements of the spectrum
of a symmetric operator `T` is the diagonal of `T` in some orthonormal basis: there is an
orthonormal basis `e` with `Re⟪T eₖ, eₖ⟫ = dₖ` for every `k`. -/
theorem exists_orthonormalBasis_re_inner_apply_self_eq_of_mem_convexHull (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) {d : Fin n → ℝ}
    (hd : d ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) ↦ hT.eigenvalues hn ∘ σ)) :
    ∃ e : OrthonormalBasis (Fin n) 𝕜 E, ∀ k, RCLike.re ⟪T (e k), e k⟫_𝕜 = d k := by
  -- The diagonals of `T` contain its spectrum and are closed under Robin Hood transfers.
  set K := Set.range fun (e : OrthonormalBasis (Fin n) 𝕜 E) (k : Fin n) ↦
    RCLike.re ⟪T (e k), e k⟫_𝕜
  have hK : ∀ x ∈ K, ∀ (i j : Fin n) (δ : ℝ), 0 ≤ δ → δ ≤ x i - x j → robinHood x i j δ ∈ K := by
    rintro _ ⟨e, rfl⟩ i j δ hδ hδ'
    exact hT.exists_orthonormalBasis_re_inner_apply_self_eq_robinHood e i j hδ hδ'
  have hspec : hT.eigenvalues hn ∈ K := ⟨hT.eigenvectorBasis hn, funext fun k ↦ by
    simp [hT.apply_eigenvectorBasis, inner_smul_left]⟩
  -- The decreasing rearrangement of `d` is majorized by the spectrum, hence a diagonal of `T`.
  obtain ⟨hle, hsum⟩ := (mem_convexHull_range_comp_perm_iff_of_antitone
    (hT.eigenvalues_antitone hn) (Tuple.antitone_sortDesc d)).1
      (comp_perm_mem_convexHull_range_comp_perm hd (Tuple.sortDesc d))
  obtain ⟨e, he⟩ := mem_of_prefixSum_le_of_sum_eq hK hspec (Tuple.antitone_sortDesc d) hle hsum
  refine ⟨e.reindex (Tuple.sortDesc d), fun k ↦ ?_⟩
  simpa using congrFun he ((Tuple.sortDesc d).symm k)

/-- **The Schur–Horn theorem.** The diagonals `(Re⟪T eₖ, eₖ⟫)ₖ` of a symmetric operator `T` in
the orthonormal bases `e` indexed by `Fin n` form exactly the convex hull of the rearrangements of
the spectrum of `T`. -/
theorem range_re_inner_apply_self_eq_convexHull_eigenvalues_comp_perm (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) :
    (Set.range fun (e : OrthonormalBasis (Fin n) 𝕜 E) (k : Fin n) ↦ RCLike.re ⟪T (e k), e k⟫_𝕜) =
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) ↦ hT.eigenvalues hn ∘ σ) := by
  ext d
  refine ⟨?_, fun hd ↦ ?_⟩
  · rintro ⟨e, rfl⟩
    exact hT.re_inner_apply_self_mem_convexHull_eigenvalues_comp_perm hn e
  · obtain ⟨e, he⟩ := hT.exists_orthonormalBasis_re_inner_apply_self_eq_of_mem_convexHull hn hd
    exact ⟨e, funext he⟩

/-- **The Schur–Horn theorem**, majorization form. A real tuple `d` is the diagonal
`(Re⟪T eₖ, eₖ⟫)ₖ` of a symmetric operator `T` in some orthonormal basis `e` exactly when `d` is
majorized by the spectrum of `T`: the prefix sums of the decreasing rearrangement of `d` are at
most the corresponding sums of the largest eigenvalues, and the sum of `d` is the trace. -/
theorem exists_orthonormalBasis_re_inner_apply_self_eq_iff (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) {d : Fin n → ℝ} :
    (∃ e : OrthonormalBasis (Fin n) 𝕜 E, ∀ k, RCLike.re ⟪T (e k), e k⟫_𝕜 = d k) ↔
      (∀ k, prefixSum k (d ∘ Tuple.sortDesc d) ≤ prefixSum k (hT.eigenvalues hn)) ∧
        ∑ i, d i = ∑ i, hT.eigenvalues hn i := by
  rw [← mem_convexHull_range_comp_perm_iff (hT.eigenvalues_antitone hn),
    ← hT.range_re_inner_apply_self_eq_convexHull_eigenvalues_comp_perm hn]
  simp only [Set.mem_range, funext_iff]

end LinearMap.IsSymmetric
