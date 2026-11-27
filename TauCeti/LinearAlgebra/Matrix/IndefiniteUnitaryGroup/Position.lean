/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import TauCeti.LinearAlgebra.Matrix.FormAdjoint
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.LinearAlgebra.Matrix.Range

/-!
# Positions of a smaller unitary group in a larger one

Let `K` be a field with an involution `star`, and let `J` and `J'` be invertible Hermitian Gram
matrices on `n` and on `m`, for the forms `⟨x, y⟩_J = star x ⬝ᵥ J *ᵥ y` of
`Matrix.unitaryGroupOf`. A **position** of `U(J')` in `U(J)` with `d + 1` vectors
(`TauCeti.IsUnitaryPosition J J' d v i₀`) consists of a matrix `v : Matrix n (Fin (d + 1)) K` with
independent columns `v₁, …, v_{d+1}`, whose products for `J` all vanish except that
`⟨v_{d+1}, v_{d+1}⟩_J = ±1`, and of a matrix `i₀ : Matrix n m K` that is an isometry from the form
of `J'` into the orthogonal complement of the `v_j`; the ranks satisfy `#n = #m + 2 d + 1`.

A matrix `Y` **lowers the flag** of the `v_j` with sum `σ` (`TauCeti.LowersFlag v Y σ`) if it maps
the span of `v₁, …, v_j` into the span of `v₁, …, v_{j-1}` for `j ≤ d + 1`, and `σ` is the sum of
the coefficients of `v_j` in `Y v_{j+1}`. It **induces** `Y'` on the image of `i₀`
(`TauCeti.InducesModFlag v i₀ Y Y'`) if `Y i₀ = i₀ Y'` modulo the span of `v₁, …, v_d`.

The position is **stationary** for weights `μ` on `n` and `μ'` on `m` and maps `ι : X → n`,
`ι' : X → m` of a common index set (`TauCeti.IsStationaryPosition`) if `μ v_j = v_{j+1}` for
`j ≤ d`, the compression `i₀† μ i₀` is `μ'` (with `i₀† = Matrix.formAdjoint J' J i₀` the adjoint for
the two forms), and `i₀` is the identity on the coordinates `X`.

The two trace identities: if `Y` and its form adjoint `Y†` lower the flag, with sums `σ` and `σ'`,
and `Y` induces `Y'`, then `tr Y = tr Y'` (`TauCeti.IsUnitaryPosition.trace_eq`), and in a
stationary position with `J`-self-adjoint `μ` moreover
`tr (μ Y) - tr (μ' Y') = σ + star σ'` (`TauCeti.IsStationaryPosition.trace_mul_sub_trace_mul_eq`).
The proof splits `μ` into its part `μ₁` on the span `A` of `v₁, …, v_d`, the adjoint of `μ₁` and a
self-adjoint rest that vanishes on `A` and whose image is orthogonal to `A`; the orthogonal
complement of `A` is spanned by the image of `i₀` and the `v_j`, by a dimension count.

For the unitary groups `U(ε)` and `U(η)` of diagonal matrices of signs and the diagonal matrices
of the weights of the lowest `K`-types of two discrete series, these are the positions in which
the two phases of the coefficients agree on the group of the position, used for the periods of
discrete series coefficients with a large gap.

## Main definitions

* `TauCeti.IsUnitaryPosition J J' d v i₀`: a position of `U(J')` in `U(J)` with `d + 1` vectors.
* `TauCeti.LowersFlag v Y σ`: `Y` lowers the flag of the columns of `v`, with sum `σ`.
* `TauCeti.InducesModFlag v i₀ Y Y'`: `Y` acts by `Y'` on the image of `i₀`, modulo `v₁, …, v_d`.
* `TauCeti.IsStationaryPosition J J' μ μ' ι ι' d v i₀`: a stationary position.

## Main results

* `TauCeti.IsUnitaryPosition.exists_eq_mul_of_orthogonal`: a matrix whose columns are orthogonal
  to `v₁, …, v_d` factors through the columns of `i₀` and `v`.
* `TauCeti.LowersFlag.sum_eq_of_linearIndependent`: the sum `σ` is determined by `Y`.
* `TauCeti.IsUnitaryPosition.trace_eq`: `tr Y = tr Y'`.
* `TauCeti.IsStationaryPosition.trace_mul_sub_trace_mul_eq`: `tr (μ Y) - tr (μ' Y') = σ + star σ'`.
* `TauCeti.IsStationaryPosition.pow_mulVec_col_zero`: `μ ^ a v₁ = v_{a+1}`.
* `TauCeti.IsStationaryPosition.star_dotProduct_pow_mulVec`: for `a + b ≤ 2 d`, the product of
  `μ ^ a v₁` and `μ ^ b v₁` is `⟨v_{d+1}, v_{d+1}⟩_J` if `a + b = 2 d` and `0` otherwise.

## References

* H. He, *On the Gan–Gross–Prasad conjecture for `U(p, q)`*, Invent. Math. 209 (2017), 837–884.
* The shorter formal proof of the Riemann hypothesis for Dirichlet `L`-functions,
  <https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh>
  (Apache 2.0): the definitions, the two trace identities and their proofs are adapted from
  `New.DiscreteSeries.IsPosition`, `New.DiscreteSeries.LowersFlag`, `New.DiscreteSeries.InducesOn`,
  `New.DiscreteSeries.IsStationary`, `New.DiscreteSeries.IsPosition.trace_eq` and
  `New.DiscreteSeries.IsStationary.phase_eq` in `src/New/Appendix/DiscreteSeries/Positions.lean`,
  stated here for arbitrary invertible Hermitian Gram matrices and weights.
-/

public section

open Matrix

namespace TauCeti

variable {K : Type*} [Field K] {n m X : Type*} [Fintype n] [Fintype m] {d : ℕ}

/-- The matrix `Y` **lowers the flag** of the columns `v₁, …, v_{d+1}` of `v` with sum `σ`: there
is a strictly upper triangular `N` with `Y v_{b+1} = ∑_{a < b} N_{ab} v_{a+1}`, so that `Y` maps
the span of `v₁, …, v_j` into the span of `v₁, …, v_{j-1}`, and `σ` is the sum of the coefficients
`N_{a,a+1}` of `v_{a+1}` in `Y v_{a+2}`. -/
def LowersFlag (v : Matrix n (Fin (d + 1)) K) (Y : Matrix n n K) (σ : K) : Prop :=
  ∃ N : Matrix (Fin d) (Fin (d + 1)) K, (∀ a b, b.val ≤ a.val → N a b = 0) ∧
    Y * v = v.submatrix id Fin.castSucc * N ∧ ∑ a : Fin d, N a a.succ = σ

/-- Unfolding `LowersFlag`. -/
theorem lowersFlag_iff {v : Matrix n (Fin (d + 1)) K} {Y : Matrix n n K} {σ : K} :
    LowersFlag v Y σ ↔ ∃ N : Matrix (Fin d) (Fin (d + 1)) K, (∀ a b, b.val ≤ a.val → N a b = 0) ∧
      Y * v = v.submatrix id Fin.castSucc * N ∧ ∑ a : Fin d, N a a.succ = σ :=
  Iff.rfl

/-- The matrix `Y` **induces** `Y'` on the image of `i₀`: `Y i₀ = i₀ Y'` modulo the span of the
first `d` columns `v₁, …, v_d` of `v`. -/
def InducesModFlag (v : Matrix n (Fin (d + 1)) K) (i₀ : Matrix n m K) (Y : Matrix n n K)
    (Y' : Matrix m m K) : Prop :=
  ∃ C : Matrix (Fin d) m K, Y * i₀ = i₀ * Y' + v.submatrix id Fin.castSucc * C

/-- Unfolding `InducesModFlag`. -/
theorem inducesModFlag_iff {v : Matrix n (Fin (d + 1)) K} {i₀ : Matrix n m K} {Y : Matrix n n K}
    {Y' : Matrix m m K} :
    InducesModFlag v i₀ Y Y' ↔ ∃ C : Matrix (Fin d) m K,
      Y * i₀ = i₀ * Y' + v.submatrix id Fin.castSucc * C :=
  Iff.rfl

/-- **The sum of a flag-lowering matrix is unique**: if the vectors `v_j` are independent and `Y`
lowers their flag with the sums `σ` and `σ'`, then `σ = σ'`. -/
theorem LowersFlag.sum_eq_of_linearIndependent {v : Matrix n (Fin (d + 1)) K} {Y : Matrix n n K}
    {σ σ' : K} (hv : LinearIndependent K v.col) (hσ : LowersFlag v Y σ)
    (hσ' : LowersFlag v Y σ') : σ = σ' := by
  obtain ⟨N, -, hN, rfl⟩ := hσ
  obtain ⟨N', -, hN', rfl⟩ := hσ'
  obtain ⟨T, hT⟩ := exists_mul_eq_one_of_linearIndependent_col hv
  have hZ : T.submatrix Fin.castSucc id * v.submatrix id Fin.castSucc = 1 := by
    rw [← submatrix_mul _ _ _ _ _ Function.bijective_id, hT,
      submatrix_one _ (Fin.castSucc_injective d)]
  have h_eq : N = N' := by
    rw [← Matrix.one_mul N, ← Matrix.one_mul N', ← hZ, Matrix.mul_assoc, Matrix.mul_assoc, ← hN,
      ← hN']
  rw [h_eq]

/-- If `Z` is a left inverse of the first `d` vectors `v₁, …, v_d` and `Y₀` maps the vectors
`v_j` into their span with matrix `N₀`, then `tr (v_t Z Y₀) = ∑ N₀_{a, t a}` for the vectors
`v_t = (v_{t 1}, …, v_{t d})`. -/
private theorem trace_submatrix_mul_mul_eq_sum {v : Matrix n (Fin (d + 1)) K}
    {Z : Matrix (Fin d) n K} {Y₀ : Matrix n n K} {N₀ : Matrix (Fin d) (Fin (d + 1)) K}
    {t : Fin d → Fin (d + 1)}
    (hZ : Z * v.submatrix id Fin.castSucc = 1) (hN₀ : Y₀ * v = v.submatrix id Fin.castSucc * N₀) :
    (v.submatrix id t * Z * Y₀).trace = ∑ a : Fin d, N₀ a (t a) := by
  have h_cols : Y₀ * v.submatrix id t = v.submatrix id Fin.castSucc * N₀.submatrix id t := by
    simpa only [submatrix_mul _ _ id id t Function.bijective_id, submatrix_id_id] using
      congrArg (·.submatrix id t) hN₀
  calc (v.submatrix id t * Z * Y₀).trace
        = (v.submatrix id Fin.castSucc * N₀.submatrix id t * Z).trace := by
        rw [trace_mul_comm, ← Matrix.mul_assoc, h_cols]
    _ = (N₀.submatrix id t).trace := by rw [trace_mul_cycle, hZ, Matrix.one_mul]
    _ = ∑ a : Fin d, N₀ a (t a) := rfl

variable [StarRing K]

/-- A **position** of `U(J')` in `U(J)` with `d + 1` vectors: the columns `v₁, …, v_{d+1}` of `v`
are independent, their products `⟨v_a, v_b⟩_J = (vᴴ J v)_{ab}` vanish except that
`⟨v_{d+1}, v_{d+1}⟩_J = ±1`, and `i₀` is an isometry from the form of `J'` into their orthogonal
complement for the form of `J`. The ranks satisfy `#n = #m + 2 d + 1`. -/
structure IsUnitaryPosition (J : Matrix n n K) (J' : Matrix m m K) (d : ℕ)
    (v : Matrix n (Fin (d + 1)) K) (i₀ : Matrix n m K) : Prop where
  /-- The ranks differ by `2 d + 1`. -/
  card_eq : Fintype.card n = Fintype.card m + 2 * d + 1
  /-- The vectors `v₁, …, v_{d+1}` are independent. -/
  linearIndependent : LinearIndependent K v.col
  /-- The product of `v_a` and `v_b` vanishes unless `a = b = d + 1`. -/
  gram_eq_zero (a b : Fin (d + 1)) : a ≠ Fin.last d ∨ b ≠ Fin.last d → (vᴴ * J * v) a b = 0
  /-- The product of `v_{d+1}` with itself is `±1`. -/
  gram_last : (vᴴ * J * v) (Fin.last d) (Fin.last d) = 1 ∨
    (vᴴ * J * v) (Fin.last d) (Fin.last d) = -1
  /-- The map `i₀` is an isometry from the form of `J'` to the form of `J`. -/
  isometry : i₀ᴴ * J * i₀ = J'
  /-- The image of `i₀` is orthogonal to `v₁, …, v_{d+1}`. -/
  orthogonal : i₀ᴴ * J * v = 0

namespace IsUnitaryPosition

variable {J : Matrix n n K} {J' : Matrix m m K} {v : Matrix n (Fin (d + 1)) K}
  {i₀ : Matrix n m K}

/-- The vectors `v_j` are orthogonal to the image of `i₀`. -/
theorem conjTranspose_mul_mul (hP : IsUnitaryPosition J J' d v i₀) (hJ : J.IsHermitian) :
    vᴴ * J * i₀ = 0 := by
  simpa [Matrix.mul_assoc, hJ.eq] using congrArg conjTranspose hP.orthogonal

/-- All the vectors `v_j` are orthogonal to the first `d` of them. -/
theorem conjTranspose_mul_mul_submatrix (hP : IsUnitaryPosition J J' d v i₀) :
    vᴴ * J * v.submatrix id Fin.castSucc = 0 :=
  Matrix.ext fun a b ↦ hP.gram_eq_zero a b.castSucc (Or.inr b.castSucc_ne_last)

/-- The first `d` vectors `v₁, …, v_d` are orthogonal to all the `v_j`. -/
theorem submatrix_conjTranspose_mul_mul (hP : IsUnitaryPosition J J' d v i₀) :
    (v.submatrix id Fin.castSucc)ᴴ * J * v = 0 :=
  Matrix.ext fun a b ↦ hP.gram_eq_zero a.castSucc b (Or.inl a.castSucc_ne_last)

variable [DecidableEq m]

/-- The adjoint `i₀† = J'⁻¹ i₀ᴴ J` is a left inverse of the isometry `i₀`. -/
theorem formAdjoint_mul_self (hP : IsUnitaryPosition J J' d v i₀) (hJ' : IsUnit J'.det) :
    formAdjoint J' J i₀ * i₀ = 1 := by
  rw [formAdjoint_def, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc i₀ᴴ, hP.isometry,
    nonsing_inv_mul _ hJ']

/-- The adjoint `i₀†` vanishes on the vectors `v_j`. -/
theorem formAdjoint_mul_eq_zero (hP : IsUnitaryPosition J J' d v i₀) :
    formAdjoint J' J i₀ * v = 0 := by
  rw [formAdjoint_def, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc i₀ᴴ, hP.orthogonal,
    Matrix.mul_zero]

/-- Some matrix `Z` gives the coordinates along the vectors `v_j` and vanishes on the image of
`i₀`: `Z i₀ = 0` and `Z v = 1`. -/
theorem exists_mul_eq_zero_and_mul_eq_one (hP : IsUnitaryPosition J J' d v i₀)
    (hJ' : IsUnit J'.det) : ∃ Z : Matrix (Fin (d + 1)) n K, Z * i₀ = 0 ∧ Z * v = 1 := by
  obtain ⟨T, hT⟩ := exists_mul_eq_one_of_linearIndependent_col hP.linearIndependent
  refine ⟨T - T * i₀ * formAdjoint J' J i₀, ?_, ?_⟩
  · simp [Matrix.mul_assoc, Matrix.sub_mul, hP.formAdjoint_mul_self hJ']
  · simp [Matrix.mul_assoc, Matrix.sub_mul, hP.formAdjoint_mul_eq_zero, hT]

/-- Some matrix `Z` gives the coordinates along the first `d` vectors `v₁, …, v_d` and vanishes
on the image of `i₀`. -/
theorem exists_mul_eq_zero_and_mul_submatrix_eq_one (hP : IsUnitaryPosition J J' d v i₀)
    (hJ' : IsUnit J'.det) :
    ∃ Z : Matrix (Fin d) n K, Z * i₀ = 0 ∧ Z * v.submatrix id Fin.castSucc = 1 := by
  obtain ⟨Z, hZ₀, hZ₁⟩ := hP.exists_mul_eq_zero_and_mul_eq_one hJ'
  refine ⟨Z.submatrix Fin.castSucc id, congrArg (·.submatrix Fin.castSucc id) hZ₀, ?_⟩
  rw [← submatrix_mul _ _ _ _ _ Function.bijective_id, hZ₁,
    submatrix_one _ (Fin.castSucc_injective d)]

/-- The columns of `i₀` together with the vectors `v_j` are independent: `[i₀ v]` has a left
inverse. -/
theorem exists_mul_fromCols_eq_one (hP : IsUnitaryPosition J J' d v i₀) (hJ' : IsUnit J'.det) :
    ∃ W : Matrix (m ⊕ Fin (d + 1)) n K, W * fromCols i₀ v = 1 := by
  obtain ⟨Z, hZ₀, hZ₁⟩ := hP.exists_mul_eq_zero_and_mul_eq_one hJ'
  exact ⟨fromRows (formAdjoint J' J i₀) Z, by
    simp [hP.formAdjoint_mul_self hJ', hP.formAdjoint_mul_eq_zero, hZ₀, hZ₁]⟩

end IsUnitaryPosition

variable [DecidableEq m] [DecidableEq n]

/-- A **stationary position** for the weights `μ` on `n` and `μ'` on `m`, and the maps `ι : X → n`
and `ι' : X → m` of a common set of coordinates: a position in which `μ v_j = v_{j+1}` for
`j ≤ d`, the compression `i₀† μ i₀` of `μ` is `μ'`, and `i₀` is the identity on the coordinates
`X`, sending the basis vector at `ι' x` to the basis vector at `ι x`. -/
structure IsStationaryPosition (J : Matrix n n K) (J' : Matrix m m K) (μ : Matrix n n K)
    (μ' : Matrix m m K) (ι : X → n) (ι' : X → m) (d : ℕ) (v : Matrix n (Fin (d + 1)) K)
    (i₀ : Matrix n m K) : Prop extends IsUnitaryPosition J J' d v i₀ where
  /-- `μ v_j = v_{j+1}` for `j ≤ d`. -/
  mul_submatrix_castSucc : μ * v.submatrix id Fin.castSucc = v.submatrix id Fin.succ
  /-- `i₀† μ i₀ = μ'`. -/
  formAdjoint_mul_mul : formAdjoint J' J i₀ * μ * i₀ = μ'
  /-- `i₀` sends the basis vector at `ι' x` to the basis vector at `ι x`. -/
  col_eq_single (x : X) : i₀.col (ι' x) = Pi.single (ι x) 1

namespace IsUnitaryPosition

variable {J : Matrix n n K} {J' : Matrix m m K} {v : Matrix n (Fin (d + 1)) K}
  {i₀ : Matrix n m K}

/-- **The orthogonal complement of `v₁, …, v_d`.** If the columns of `M` are orthogonal to the
first `d` vectors `v₁, …, v_d`, then they are linear combinations of the columns of `i₀` and of
the vectors `v_j`: the span of these has dimension `#m + d + 1 = #n - d`, the dimension of the
orthogonal complement. -/
theorem exists_eq_mul_of_orthogonal (hP : IsUnitaryPosition J J' d v i₀) (hJ : J.IsHermitian)
    (hJu : IsUnit J.det) (hJ' : IsUnit J'.det) {p : Type*} {M : Matrix n p K}
    (hM : (v.submatrix id Fin.castSucc)ᴴ * J * M = 0) :
    ∃ T : Matrix (m ⊕ Fin (d + 1)) p K, M = fromCols i₀ v * T := by
  obtain ⟨W, hW⟩ := hP.exists_mul_fromCols_eq_one hJ'
  obtain ⟨Z, -, hZ⟩ := hP.exists_mul_eq_zero_and_mul_submatrix_eq_one hJ'
  set combination := (fromCols i₀ v).mulVecLin
  set pairing := ((v.submatrix id Fin.castSucc)ᴴ * J).mulVecLin
  have h_inj : Function.Injective combination := Function.LeftInverse.injective
    (g := W.mulVec) fun x ↦ by rw [mulVecLin_apply, mulVec_mulVec, hW, one_mulVec]
  have h_right : (v.submatrix id Fin.castSucc)ᴴ * J * (J⁻¹ * Zᴴ) = 1 := by
    rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hJu, ← conjTranspose_mul, hZ,
      conjTranspose_one]
  have h_surj : Function.Surjective pairing := Function.RightInverse.surjective
    (g := (J⁻¹ * Zᴴ).mulVec) fun x ↦ by rw [mulVecLin_apply, mulVec_mulVec, h_right, one_mulVec]
  have h_eq : LinearMap.range combination = LinearMap.ker pairing := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [LinearMap.range_le_ker_iff, ← mulVecLin_mul, mul_fromCols]
      have h₁ : (v.submatrix id Fin.castSucc)ᴴ * J * i₀ = 0 := by
        ext a j
        simpa [Matrix.mul_apply] using congrFun₂ (hP.conjTranspose_mul_mul hJ) a.castSucc j
      rw [h₁, hP.submatrix_conjTranspose_mul_mul, fromCols_zero, mulVecLin_zero]
    · have h_range : Module.finrank K (LinearMap.range combination) =
          Fintype.card m + (d + 1) := by
        simp [LinearMap.finrank_range_of_inj h_inj]
      have h_pairing : Module.finrank K (LinearMap.range pairing) = d := by
        rw [LinearMap.range_eq_top.2 h_surj, finrank_top, Module.finrank_fin_fun]
      have h_rank : d + Module.finrank K (LinearMap.ker pairing) = Fintype.card m + 2 * d + 1 := by
        simpa [h_pairing, hP.card_eq] using pairing.finrank_range_add_finrank_ker
      omega
  have h_col (j : p) : ∃ x, combination x = Mᵀ j := by
    rw [← LinearMap.mem_range, h_eq, LinearMap.mem_ker]
    exact funext fun a ↦ congrFun₂ hM a j
  choose T hT using h_col
  exact ⟨(of T)ᵀ, Matrix.ext fun i j ↦ (congrFun (hT j) i).symm⟩

/-- Let `Y` map the vectors `v_j` into the span of `v₁, …, v_d`, with matrix `N`, and induce `Y'`
on the image of `i₀`. If `M` vanishes on `v₁, …, v_d` and its image is orthogonal to them, then
`tr (M Y) = tr (i₀† M i₀ Y')`. -/
theorem trace_mul_eq_of_mul_submatrix_eq_zero (hP : IsUnitaryPosition J J' d v i₀)
    (hJ : J.IsHermitian) (hJu : IsUnit J.det) (hJ' : IsUnit J'.det) {M Y : Matrix n n K}
    {Y' : Matrix m m K} {N : Matrix (Fin d) (Fin (d + 1)) K}
    (hN : Y * v = v.submatrix id Fin.castSucc * N) (hY' : InducesModFlag v i₀ Y Y')
    (h_ker : M * v.submatrix id Fin.castSucc = 0)
    (h_range : (v.submatrix id Fin.castSucc)ᴴ * J * M = 0) :
    (M * Y).trace = (formAdjoint J' J i₀ * M * i₀ * Y').trace := by
  obtain ⟨C, hC⟩ := hY'
  obtain ⟨W, hW⟩ := hP.exists_mul_fromCols_eq_one hJ'
  obtain ⟨T, rfl⟩ := hP.exists_eq_mul_of_orthogonal hJ hJu hJ' h_range
  have hT_ker : T * v.submatrix id Fin.castSucc = 0 := by
    rw [← Matrix.one_mul T, ← hW, Matrix.mul_assoc W, Matrix.mul_assoc W, h_ker, Matrix.mul_zero]
  have hT_top : formAdjoint J' J i₀ * (fromCols i₀ v * T) = toRows₁ T := by
    rw [← Matrix.mul_assoc, mul_fromCols, hP.formAdjoint_mul_self hJ', hP.formAdjoint_mul_eq_zero,
      ← fromRows_toRows T, fromCols_mul_fromRows]
    simp
  have h_blocks : T * (Y * fromCols i₀ v) = fromCols (T * i₀ * Y') 0 := by
    rw [mul_fromCols, hN, hC, mul_fromCols]
    simp [Matrix.mul_add, ← Matrix.mul_assoc, hT_ker]
  calc (fromCols i₀ v * T * Y).trace = (T * (Y * fromCols i₀ v)).trace := by
        rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
    _ = (toRows₁ T * i₀ * Y').trace := by
        rw [h_blocks]
        simp [trace, Fintype.sum_sum_type, Matrix.mul_apply, toRows₁_apply]
    _ = (formAdjoint J' J i₀ * (fromCols i₀ v * T) * i₀ * Y').trace := by rw [hT_top]

/-- **The trace of `μ Y`.** Let `μ` be self-adjoint for `J` and send each `v_j`, `j ≤ d`, to
`v_{t j}`. Let `Y` and its adjoint `Y†` map the vectors `v_j` into the span of `v₁, …, v_d`, with
the matrices `N` and `N'`, and let `Y` induce `Y'` on the image of `i₀`. Then
`tr (μ Y) = tr (i₀† μ i₀ Y') + ∑ N_{a, t a} + star (∑ N'_{a, t a})`. -/
theorem trace_mul_eq_trace_add_sum (hP : IsUnitaryPosition J J' d v i₀) (hJ : J.IsHermitian)
    (hJu : IsUnit J.det) (hJ' : IsUnit J'.det) {μ Y : Matrix n n K} {Y' : Matrix m m K}
    {t : Fin d → Fin (d + 1)} {N N' : Matrix (Fin d) (Fin (d + 1)) K}
    (hμ : formAdjoint J J μ = μ) (ht : μ * v.submatrix id Fin.castSucc = v.submatrix id t)
    (hY' : InducesModFlag v i₀ Y Y') (hN : Y * v = v.submatrix id Fin.castSucc * N)
    (hN' : formAdjoint J J Y * v = v.submatrix id Fin.castSucc * N') :
    (μ * Y).trace = (formAdjoint J' J i₀ * μ * i₀ * Y').trace + ∑ a : Fin d, N a (t a) +
      star (∑ a : Fin d, N' a (t a)) := by
  obtain ⟨Z, hZ₀, hZ₁⟩ := hP.exists_mul_eq_zero_and_mul_submatrix_eq_one hJ'
  -- `μ₁` is `μ` on `A = ⟨v₁, …, v_d⟩` and `0` on a complement containing the image of `i₀`.
  set μ₁ : Matrix n n K := μ * v.submatrix id Fin.castSucc * Z with hμ₁
  have h_flag : μ₁ * v.submatrix id Fin.castSucc = μ * v.submatrix id Fin.castSucc := by
    simp [hμ₁, Matrix.mul_assoc, hZ₁]
  have h_i₀ : μ₁ * i₀ = 0 := by simp [hμ₁, Matrix.mul_assoc, hZ₀]
  -- The image of `μ₁` lies in the span of the `v_j`, so `μ₁†` vanishes on `A` and on `i₀`.
  have h_adj : formAdjoint J J μ₁ = J⁻¹ * Zᴴ * ((v.submatrix id t)ᴴ * J) := by
    rw [formAdjoint_def, hμ₁, ht, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have h_adj_flag : formAdjoint J J μ₁ * v.submatrix id Fin.castSucc = 0 := by
    have h_zero : (v.submatrix id t)ᴴ * J * v.submatrix id Fin.castSucc = 0 := by
      ext a b
      simpa [Matrix.mul_apply] using congrFun₂ hP.conjTranspose_mul_mul_submatrix (t a) b
    rw [h_adj, Matrix.mul_assoc, h_zero, Matrix.mul_zero]
  have h_adj_i₀ : formAdjoint J J μ₁ * i₀ = 0 := by
    have h_zero : (v.submatrix id t)ᴴ * J * i₀ = 0 := by
      ext a j
      simpa [Matrix.mul_apply] using congrFun₂ (hP.conjTranspose_mul_mul hJ) (t a) j
    rw [h_adj, Matrix.mul_assoc, h_zero, Matrix.mul_zero]
  -- The rest `M` is self-adjoint and vanishes on `A`, so its image is orthogonal to `A`.
  set M : Matrix n n K := μ - μ₁ - formAdjoint J J μ₁ with hM
  have hM_adj : formAdjoint J J M = M := by
    rw [hM, formAdjoint_sub, formAdjoint_sub, formAdjoint_formAdjoint hJ hJ hJu hJu, hμ,
      sub_right_comm]
  have hM_ker : M * v.submatrix id Fin.castSucc = 0 := by
    simp [hM, Matrix.sub_mul, h_flag, h_adj_flag]
  have hM_range : (v.submatrix id Fin.castSucc)ᴴ * J * M = 0 := by
    rw [Matrix.mul_assoc, ← hM_adj, mul_formAdjoint hJu, ← Matrix.mul_assoc, ← conjTranspose_mul,
      hM_ker, conjTranspose_zero, Matrix.zero_mul]
  have hM_i₀ : M * i₀ = μ * i₀ := by simp [hM, Matrix.sub_mul, h_i₀, h_adj_i₀]
  have h_middle : (M * Y).trace = (formAdjoint J' J i₀ * μ * i₀ * Y').trace := by
    rw [hP.trace_mul_eq_of_mul_submatrix_eq_zero hJ hJu hJ' hN hY' hM_ker hM_range,
      Matrix.mul_assoc _ M, hM_i₀, ← Matrix.mul_assoc]
  -- `μ₁ Y₀` has trace `∑ N₀_{a, t a}` when `Y₀` maps the `v_j` into `A` with matrix `N₀`.
  have h_trace {Y₀ : Matrix n n K} {N₀ : Matrix (Fin d) (Fin (d + 1)) K}
      (hN₀ : Y₀ * v = v.submatrix id Fin.castSucc * N₀) :
      (μ₁ * Y₀).trace = ∑ a : Fin d, N₀ a (t a) := by
    rw [hμ₁, ht, trace_submatrix_mul_mul_eq_sum hZ₁ hN₀]
  have h_trace_adj : (formAdjoint J J μ₁ * Y).trace = star (∑ a : Fin d, N' a (t a)) := by
    rw [← h_trace hN', ← trace_formAdjoint hJu, formAdjoint_mul hJu,
      formAdjoint_formAdjoint hJ hJ hJu hJu, trace_mul_comm]
  rw [← h_middle, ← h_trace hN, ← h_trace_adj, hM, Matrix.sub_mul, Matrix.sub_mul, trace_sub,
    trace_sub]
  ring

/-- **The two traces agree.** If `Y` and its adjoint `Y†` for the form of `J` lower the flag of
the vectors `v_j`, and `Y` induces `Y'` on the image of `i₀`, then `tr Y = tr Y'`. -/
theorem trace_eq (hP : IsUnitaryPosition J J' d v i₀) (hJ : J.IsHermitian) (hJu : IsUnit J.det)
    (hJ' : IsUnit J'.det) {Y : Matrix n n K} {Y' : Matrix m m K} {σ σ' : K}
    (hY : LowersFlag v Y σ) (hY' : InducesModFlag v i₀ Y Y')
    (hY_adj : LowersFlag v (formAdjoint J J Y) σ') : Y.trace = Y'.trace := by
  obtain ⟨N, hN_tri, hN, -⟩ := hY
  obtain ⟨N', hN'_tri, hN', -⟩ := hY_adj
  have h := hP.trace_mul_eq_trace_add_sum hJ hJu hJ' (formAdjoint_one hJu)
    (Matrix.one_mul (v.submatrix id Fin.castSucc)) hY' hN hN'
  have h₀ (a : Fin d) : N a a.castSucc = 0 := hN_tri a _ (by simp)
  have h₀' (a : Fin d) : N' a a.castSucc = 0 := hN'_tri a _ (by simp)
  simpa [hP.formAdjoint_mul_self hJ', h₀, h₀'] using h

end IsUnitaryPosition

namespace IsStationaryPosition

variable {J : Matrix n n K} {J' : Matrix m m K} {μ : Matrix n n K} {μ' : Matrix m m K}
  {ι : X → n} {ι' : X → m} {v : Matrix n (Fin (d + 1)) K} {i₀ : Matrix n m K}

/-- **The phase identity.** In a stationary position with a `J`-self-adjoint weight `μ`, if `Y`
and its adjoint `Y†` lower the flag of the vectors `v_j`, with sums `σ` and `σ'`, and `Y` induces
`Y'` on the image of `i₀`, then `tr (μ Y) - tr (μ' Y') = σ + star σ'`. -/
theorem trace_mul_sub_trace_mul_eq (hP : IsStationaryPosition J J' μ μ' ι ι' d v i₀)
    (hJ : J.IsHermitian) (hJu : IsUnit J.det) (hJ' : IsUnit J'.det) (hμ : formAdjoint J J μ = μ)
    {Y : Matrix n n K} {Y' : Matrix m m K} {σ σ' : K} (hY : LowersFlag v Y σ)
    (hY' : InducesModFlag v i₀ Y Y') (hY_adj : LowersFlag v (formAdjoint J J Y) σ') :
    (μ * Y).trace - (μ' * Y').trace = σ + star σ' := by
  obtain ⟨N, -, hN, rfl⟩ := hY
  obtain ⟨N', -, hN', rfl⟩ := hY_adj
  rw [hP.trace_mul_eq_trace_add_sum hJ hJu hJ' hμ hP.mul_submatrix_castSucc hY' hN hN',
    hP.formAdjoint_mul_mul]
  ring

/-- In a stationary position, `μ ^ a v₁ = v_{a+1}` for `a ≤ d`. -/
theorem pow_mulVec_col_zero (hP : IsStationaryPosition J J' μ μ' ι ι' d v i₀) (a : Fin (d + 1)) :
    μ ^ a.val *ᵥ v.col 0 = v.col a := by
  induction a using Fin.induction with
  | zero => simp
  | succ a ih =>
    rw [Fin.val_succ, pow_succ', ← mulVec_mulVec, ← Fin.val_castSucc, ih]
    exact congrArg (·.col a) hP.mul_submatrix_castSucc

/-- In a stationary position with a `J`-self-adjoint weight `μ`, for `a + b ≤ 2 d` the product
`⟨μ ^ a v₁, μ ^ b v₁⟩_J` is `⟨v_{d+1}, v_{d+1}⟩_J` if `a + b = 2 d` and `0` otherwise. -/
theorem star_dotProduct_pow_mulVec (hP : IsStationaryPosition J J' μ μ' ι ι' d v i₀)
    (hJu : IsUnit J.det) (hμ : formAdjoint J J μ = μ) {a b : ℕ} (hab : a + b ≤ 2 * d) :
    star (μ ^ a *ᵥ v.col 0) ⬝ᵥ J *ᵥ (μ ^ b *ᵥ v.col 0) =
      if a + b = 2 * d then (vᴴ * J * v) (Fin.last d) (Fin.last d) else 0 := by
  -- As `μ` is self-adjoint, the product depends only on `a + b`.
  have h_adj (c : ℕ) : (μ ^ c)ᴴ * J = J * μ ^ c := by
    induction c with
    | zero => simp
    | succ c ih =>
      have h₁ : μᴴ * J = J * μ := by rw [← mul_formAdjoint hJu, hμ]
      rw [pow_succ, conjTranspose_mul, Matrix.mul_assoc, ih, ← Matrix.mul_assoc, h₁,
        Matrix.mul_assoc, ← pow_succ', pow_succ]
  have h_sum (a b : ℕ) : star (μ ^ a *ᵥ v.col 0) ⬝ᵥ J *ᵥ (μ ^ b *ᵥ v.col 0) =
      star (v.col 0) ⬝ᵥ (J * μ ^ (a + b)) *ᵥ v.col 0 := by
    rw [pow_add, ← Matrix.mul_assoc, ← h_adj]
    conv_rhs => rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  obtain ⟨a', b', h_split⟩ : ∃ a' b' : Fin (d + 1), a + b = a'.val + b'.val :=
    ⟨⟨min (a + b) d, by omega⟩, ⟨a + b - min (a + b) d, by omega⟩, by simp⟩
  have h_gram : star (v.col a') ⬝ᵥ J *ᵥ v.col b' = (vᴴ * J * v) a' b' := by
    rw [dotProduct_mulVec, Matrix.mul_apply']
    rfl
  rw [h_sum, h_split, ← h_sum, hP.pow_mulVec_col_zero, hP.pow_mulVec_col_zero, h_gram]
  split_ifs with h_eq
  · rw [Fin.eq_last_of_not_lt (i := a') (by omega), Fin.eq_last_of_not_lt (i := b') (by omega)]
  · refine hP.gram_eq_zero a' b' ?_
    by_contra h
    simp only [ne_eq, not_or, not_not] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [two_mul] at h_eq

end IsStationaryPosition

end TauCeti
