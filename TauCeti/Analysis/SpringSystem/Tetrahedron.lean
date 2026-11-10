/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RepresentationTheory.Basic

/-!
# The spring tetrahedron: its symmetry, its force matrix and its normal modes

Four unit point masses sit at the vertices `p₀ = (0,0,0)`, `p₁ = (1,1,0)`, `p₂ = (1,0,1)` and
`p₃ = (0,1,1)` of a regular tetrahedron, and each pair is joined by a spring. A displacement of
the system is a vector `u ∈ ℝ¹² = ℝ^(Fin 4 × Fin 3)`, whose block `uᵢ = (u (i, k))ₖ` displaces the
vertex `pᵢ`. The linearized spring forces are encoded by the force matrix
`H = -∑_{i<j} z_{ij} z_{ij}ᵀ`, where `z_{ij}` has block `pᵢ - pⱼ` at `i`, block `pⱼ - pᵢ` at `j`
and zeros elsewhere.

The symmetric group `S₄ = Equiv.Perm (Fin 4)` acts on the centred vertices `qᵢ = pᵢ - c`,
`c = (½,½,½)`, by orthogonal matrices `R_σ` with `R_σ qᵢ = q_{σ i}`, and hence on displacements by
`(σ • u)ᵢ = R_σ u_{σ⁻¹ i}`, which moves the displacement of vertex `i` to vertex `σ i`. This file
constructs these actions, proves that `H` is symmetric, negative semidefinite and `S₄`-equivariant,
and computes its spectrum exactly. The computation goes through the coordinates
`uᵢ = t + A qᵢ`, `t ∈ ℝ³`, `A ∈ M₃(ℝ)`: every displacement is uniquely of this form, and `H` maps
`(t, A)` to `(0, -2(A + Aᵀ) + 2 diag(A) - 2 tr(A) I)`. Hence

* translations and infinitesimal rotations (`Aᵀ = -A`) form the kernel, of dimension `6`;
* diagonal trace-zero `A` give the eigenvalue `-2`, with multiplicity `2`;
* symmetric `A` with zero diagonal give the eigenvalue `-4`, with multiplicity `3`;
* scalar `A` (the breathing mode) give the eigenvalue `-8`, with multiplicity `1`;

and the characteristic polynomial of `H` is `X⁶ (X + 2)² (X + 4)³ (X + 8)`.

The vertices are indexed by `Fin 4`, so `pᵢ` here is the vertex `p_{i+1}` of the handout cited
below.

## Main definitions

* `TauCeti.tetrahedronVertex`, `TauCeti.tetrahedronCenteredVertex`: the vertices `pᵢ`, `qᵢ`.
* `TauCeti.tetrahedronSymmetryMatrix`: the orthogonal representation `σ ↦ R_σ` of `S₄` on `ℝ³`.
* `TauCeti.tetrahedronDisplacementRep`: the representation of `S₄` on displacements.
* `TauCeti.tetrahedronSpringMatrix`: the force matrix `H`.
* `TauCeti.tetrahedronAffineFieldEquiv`: the linear equivalence `(t, A) ↦ (t + A qᵢ)ᵢ`.

## Main results

* `TauCeti.isSymm_tetrahedronSpringMatrix`, `TauCeti.posSemidef_neg_tetrahedronSpringMatrix`:
  `H` is symmetric and `-H` is positive semidefinite.
* `TauCeti.tetrahedronSpringMatrix_mulVec_displacementRep`: `H` commutes with the `S₄`-action.
* `TauCeti.tetrahedronSpringMatrix_mulVec_affineFieldEquiv`: `H` in the coordinates `(t, A)`.
* `TauCeti.charpoly_tetrahedronSpringMatrix`: `charpoly H = X⁶ (X + 2)² (X + 4)³ (X + 8)`.
* `TauCeti.finrank_eigenspace_tetrahedronSpringMatrix`: the eigenspace dimensions.
* `TauCeti.tetrahedronAffineFieldEquiv_mem_eigenspace_zero_iff` and its `neg_two`, `neg_four`,
  `neg_eight` companions: the four eigenspaces in the coordinates `(t, A)`.

## References

* A. Knutson, *Group theory in physics: an example*, tetrahedron handout for Math 261 (Cornell,
  2001), pp. 3–5.
-/

public section

namespace TauCeti

open Matrix

/-! ### The vertices -/

/-- The vertices `(0,0,0)`, `(1,1,0)`, `(1,0,1)`, `(0,1,1)` of a regular tetrahedron with edge
length `√2`. -/
def tetrahedronVertex : Fin 4 → Fin 3 → ℝ := ![![0, 0, 0], ![1, 1, 0], ![1, 0, 1], ![0, 1, 1]]

/-- Distinct vertices are at squared distance `2`. -/
theorem dotProduct_self_tetrahedronVertex_sub {i j : Fin 4} (h : i ≠ j) :
    (tetrahedronVertex i - tetrahedronVertex j) ⬝ᵥ (tetrahedronVertex i - tetrahedronVertex j) =
      2 := by
  fin_cases i <;> fin_cases j <;> simp_all [tetrahedronVertex, dotProduct, Fin.sum_univ_three] <;>
    norm_num

/-- The centroid `(½, ½, ½)` of the tetrahedron. -/
noncomputable def tetrahedronCentroid : Fin 3 → ℝ := ![1 / 2, 1 / 2, 1 / 2]

/-- The centroid is the average of the four vertices. -/
theorem tetrahedronCentroid_eq : tetrahedronCentroid = (4 : ℝ)⁻¹ • ∑ i, tetrahedronVertex i := by
  ext k
  fin_cases k <;> simp [tetrahedronCentroid, tetrahedronVertex, Fin.sum_univ_four] <;> norm_num

/-- The vertices `qᵢ = pᵢ - c` of the tetrahedron centred at its centroid. -/
noncomputable def tetrahedronCenteredVertex (i : Fin 4) : Fin 3 → ℝ :=
  tetrahedronVertex i - tetrahedronCentroid

/-- The centred vertices are `(-½,-½,-½)`, `(½,½,-½)`, `(½,-½,½)` and `(-½,½,½)`. -/
theorem tetrahedronCenteredVertex_eq : tetrahedronCenteredVertex =
    ![![-1 / 2, -1 / 2, -1 / 2], ![1 / 2, 1 / 2, -1 / 2], ![1 / 2, -1 / 2, 1 / 2],
      ![-1 / 2, 1 / 2, 1 / 2]] := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [tetrahedronCenteredVertex, tetrahedronCentroid, tetrahedronVertex] <;> norm_num

/-- The centred vertices sum to zero. -/
theorem sum_tetrahedronCenteredVertex : ∑ i, tetrahedronCenteredVertex i = 0 := by
  ext k
  fin_cases k <;> simp [tetrahedronCenteredVertex_eq, Fin.sum_univ_four] <;> norm_num

/-- The Gram matrix of the centred vertices: `qᵢ ⬝ qᵢ = ¾` and `qᵢ ⬝ qⱼ = -¼` for `i ≠ j`. -/
theorem dotProduct_tetrahedronCenteredVertex (i j : Fin 4) :
    tetrahedronCenteredVertex i ⬝ᵥ tetrahedronCenteredVertex j =
      if i = j then 3 / 4 else -1 / 4 := by
  fin_cases i <;> fin_cases j <;>
    simp [tetrahedronCenteredVertex_eq, dotProduct, Fin.sum_univ_three] <;> norm_num

/-- The centred vertices form a tight frame: `∑ᵢ qᵢ qᵢᵀ = 1`. -/
theorem sum_vecMulVec_tetrahedronCenteredVertex :
    ∑ i, vecMulVec (tetrahedronCenteredVertex i) (tetrahedronCenteredVertex i) = 1 := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [tetrahedronCenteredVertex_eq, Fin.sum_univ_four] <;> norm_num

/-- Every `3 × 3` matrix is recovered from its values on the centred vertices:
`A = ∑ᵢ (A qᵢ) qᵢᵀ`. -/
theorem eq_sum_vecMulVec_mulVec_tetrahedronCenteredVertex (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A = ∑ i, vecMulVec (A *ᵥ tetrahedronCenteredVertex i) (tetrahedronCenteredVertex i) := by
  conv_lhs => rw [← A.mul_one, ← sum_vecMulVec_tetrahedronCenteredVertex]
  simp [Matrix.mul_sum, mul_vecMulVec]

/-- Two `3 × 3` matrices agreeing on the centred vertices are equal. -/
theorem ext_of_mulVec_tetrahedronCenteredVertex {A B : Matrix (Fin 3) (Fin 3) ℝ}
    (h : ∀ i, A *ᵥ tetrahedronCenteredVertex i = B *ᵥ tetrahedronCenteredVertex i) : A = B := by
  rw [eq_sum_vecMulVec_mulVec_tetrahedronCenteredVertex A,
    eq_sum_vecMulVec_mulVec_tetrahedronCenteredVertex B]
  simp [h]

/-- The frame identity `∑ᵢ (qᵢ ⬝ qⱼ) fᵢ = fⱼ - ¼ ∑ᵢ fᵢ`, for any family `f` in a real vector
space. -/
private theorem sum_dotProduct_tetrahedronCenteredVertex_smul {M : Type*} [AddCommGroup M]
    [Module ℝ M] (f : Fin 4 → M) (j : Fin 4) :
    ∑ i, (tetrahedronCenteredVertex i ⬝ᵥ tetrahedronCenteredVertex j) • f i =
      f j - (4 : ℝ)⁻¹ • ∑ i, f i := by
  have (i : Fin 4) : tetrahedronCenteredVertex i ⬝ᵥ tetrahedronCenteredVertex j =
      (if i = j then 1 else 0) - 4⁻¹ := by
    rw [dotProduct_tetrahedronCenteredVertex]; split_ifs <;> norm_num
  simp [this, sub_smul, Finset.sum_sub_distrib, Finset.smul_sum]

/-! ### The symmetry group -/

private theorem sum_vecMulVec_perm_mulVec_tetrahedronCenteredVertex (σ : Equiv.Perm (Fin 4))
    (j : Fin 4) :
    (∑ i, vecMulVec (tetrahedronCenteredVertex (σ i)) (tetrahedronCenteredVertex i)) *ᵥ
      tetrahedronCenteredVertex j = tetrahedronCenteredVertex (σ j) := by
  simp only [Matrix.sum_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  rw [sum_dotProduct_tetrahedronCenteredVertex_smul (fun i ↦ tetrahedronCenteredVertex (σ i)),
    Equiv.sum_comp, sum_tetrahedronCenteredVertex, smul_zero, sub_zero]

/-- The symmetries of the tetrahedron: `σ ∈ S₄` acts on `ℝ³` by the matrix
`R_σ = ∑ᵢ q_{σ i} qᵢᵀ`, the unique linear map with `R_σ qᵢ = q_{σ i}`
(`tetrahedronSymmetryMatrix_mulVec`). These matrices are orthogonal
(`tetrahedronSymmetryMatrix_mem_orthogonalGroup`). Even permutations preserve orientation (the
identity, rotations by `2π/3` about vertex axes and by `π` about edge-midpoint axes); odd ones
reverse it (transpositions act by plane reflections, four-cycles by rotoreflections of order
four). -/
noncomputable def tetrahedronSymmetryMatrix :
    Equiv.Perm (Fin 4) →* Matrix (Fin 3) (Fin 3) ℝ where
  toFun σ := ∑ i, vecMulVec (tetrahedronCenteredVertex (σ i)) (tetrahedronCenteredVertex i)
  map_one' := ext_of_mulVec_tetrahedronCenteredVertex fun i ↦ by
    rw [sum_vecMulVec_perm_mulVec_tetrahedronCenteredVertex, one_mulVec, Equiv.Perm.one_apply]
  map_mul' σ τ := ext_of_mulVec_tetrahedronCenteredVertex fun i ↦ by
    rw [sum_vecMulVec_perm_mulVec_tetrahedronCenteredVertex, ← mulVec_mulVec,
      sum_vecMulVec_perm_mulVec_tetrahedronCenteredVertex,
      sum_vecMulVec_perm_mulVec_tetrahedronCenteredVertex, Equiv.Perm.mul_apply]

/-- The defining formula `R_σ = ∑ᵢ q_{σ i} qᵢᵀ`. -/
theorem tetrahedronSymmetryMatrix_apply (σ : Equiv.Perm (Fin 4)) :
    tetrahedronSymmetryMatrix σ =
      ∑ i, vecMulVec (tetrahedronCenteredVertex (σ i)) (tetrahedronCenteredVertex i) :=
  (rfl)

/-- `R_σ` maps the centred vertex `qⱼ` to `q_{σ j}`. -/
@[simp]
theorem tetrahedronSymmetryMatrix_mulVec (σ : Equiv.Perm (Fin 4)) (j : Fin 4) :
    tetrahedronSymmetryMatrix σ *ᵥ tetrahedronCenteredVertex j =
      tetrahedronCenteredVertex (σ j) :=
  sum_vecMulVec_perm_mulVec_tetrahedronCenteredVertex σ j

/-- `R_σ` maps the edge vector `pᵢ - pⱼ` to `p_{σ i} - p_{σ j}`. -/
theorem tetrahedronSymmetryMatrix_mulVec_sub (σ : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    tetrahedronSymmetryMatrix σ *ᵥ (tetrahedronVertex i - tetrahedronVertex j) =
      tetrahedronVertex (σ i) - tetrahedronVertex (σ j) := by
  have (i j : Fin 4) : tetrahedronVertex i - tetrahedronVertex j =
      tetrahedronCenteredVertex i - tetrahedronCenteredVertex j := by
    simp [tetrahedronCenteredVertex]
  rw [this, this, mulVec_sub, tetrahedronSymmetryMatrix_mulVec, tetrahedronSymmetryMatrix_mulVec]

/-- `R_σᵀ = R_{σ⁻¹}`. -/
@[simp]
theorem transpose_tetrahedronSymmetryMatrix (σ : Equiv.Perm (Fin 4)) :
    (tetrahedronSymmetryMatrix σ)ᵀ = tetrahedronSymmetryMatrix σ⁻¹ := by
  simp only [tetrahedronSymmetryMatrix_apply, transpose_sum, transpose_vecMulVec]
  exact (Equiv.sum_comp σ⁻¹ _).symm.trans (by simp)

/-- Each `R_σ` is an orthogonal matrix. -/
theorem tetrahedronSymmetryMatrix_mem_orthogonalGroup (σ : Equiv.Perm (Fin 4)) :
    tetrahedronSymmetryMatrix σ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff', transpose_tetrahedronSymmetryMatrix, ← map_mul,
    inv_mul_cancel, map_one]

/-! ### Displacements -/

/-- The representation of `S₄` on displacements `u ∈ ℝ^(Fin 4 × Fin 3)`:
`(σ • u)ᵢ = R_σ u_{σ⁻¹ i}`, moving the displacement of vertex `i` to vertex `σ i` and
transforming it by `R_σ` (`curry_tetrahedronDisplacementRep`). -/
noncomputable def tetrahedronDisplacementRep :
    Representation ℝ (Equiv.Perm (Fin 4)) (Fin 4 × Fin 3 → ℝ) where
  toFun σ :=
    { toFun u p := ∑ l, tetrahedronSymmetryMatrix σ p.2 l * u (σ⁻¹ p.1, l)
      map_add' u v := by ext p; simp [mul_add, Finset.sum_add_distrib]
      map_smul' c u := by ext p; simp [Finset.mul_sum, mul_left_comm] }
  map_one' := by ext u p; simp [Matrix.one_apply]
  map_mul' σ τ := by
    refine LinearMap.ext fun u ↦ funext fun p ↦ ?_
    simp only [map_mul, Matrix.mul_apply, Finset.sum_mul, mul_apply_eq_comp, LinearMap.coe_mk,
      AddHom.coe_mk, Finset.mul_sum, _root_.mul_inv_rev, Equiv.Perm.mul_apply]
    rw [Finset.sum_comm]
    simp [mul_assoc]

/-- The block of `σ • u` at vertex `i` is `R_σ u_{σ⁻¹ i}`. -/
@[simp]
theorem curry_tetrahedronDisplacementRep (σ : Equiv.Perm (Fin 4)) (u : Fin 4 × Fin 3 → ℝ)
    (i : Fin 4) :
    Function.curry (tetrahedronDisplacementRep σ u) i =
      tetrahedronSymmetryMatrix σ *ᵥ Function.curry u (σ⁻¹ i) := by
  ext k; rfl

/-- The displacement representation is orthogonal for the standard inner product on `ℝ¹²`. -/
@[simp]
theorem dotProduct_tetrahedronDisplacementRep (σ : Equiv.Perm (Fin 4))
    (u v : Fin 4 × Fin 3 → ℝ) :
    tetrahedronDisplacementRep σ u ⬝ᵥ tetrahedronDisplacementRep σ v = u ⬝ᵥ v := by
  have hblock (w w' : Fin 4 × Fin 3 → ℝ) :
      w ⬝ᵥ w' = ∑ i, Function.curry w i ⬝ᵥ Function.curry w' i := by
    simp [dotProduct, Fintype.sum_prod_type, Function.curry]
  have hR (a b : Fin 3 → ℝ) :
      tetrahedronSymmetryMatrix σ *ᵥ a ⬝ᵥ tetrahedronSymmetryMatrix σ *ᵥ b = a ⬝ᵥ b := by
    rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul,
      (Matrix.mem_orthogonalGroup_iff' _ _).mp (tetrahedronSymmetryMatrix_mem_orthogonalGroup σ),
      vecMul_one]
  rw [hblock, hblock]
  simp only [curry_tetrahedronDisplacementRep, hR]
  exact Equiv.sum_comp σ⁻¹ fun i ↦ Function.curry u i ⬝ᵥ Function.curry v i

/-! ### The force matrix -/

/-- The edge vector `z_{ij} ∈ ℝ¹²`, with block `pᵢ - pⱼ` at vertex `i`, block `pⱼ - pᵢ` at
vertex `j` and zeros elsewhere: the gradient of the stretching `(pᵢ - pⱼ) ⬝ (uᵢ - uⱼ)` of the
edge `ij`. -/
noncomputable def tetrahedronEdgeVector (i j : Fin 4) : Fin 4 × Fin 3 → ℝ :=
  Function.uncurry (Pi.single i (tetrahedronVertex i - tetrahedronVertex j) -
    Pi.single j (tetrahedronVertex i - tetrahedronVertex j))

/-- The blocks of `z_{ij}`: `pᵢ - pⱼ` at `i`, minus the same vector at `j`. -/
theorem curry_tetrahedronEdgeVector (i j : Fin 4) :
    Function.curry (tetrahedronEdgeVector i j) =
      Pi.single i (tetrahedronVertex i - tetrahedronVertex j) -
        Pi.single j (tetrahedronVertex i - tetrahedronVertex j) :=
  Function.curry_uncurry _

/-- `z_{ji} = z_{ij}`: the edge vector depends only on the edge. -/
theorem tetrahedronEdgeVector_comm (i j : Fin 4) :
    tetrahedronEdgeVector j i = tetrahedronEdgeVector i j := by
  ext p
  simp only [tetrahedronEdgeVector, Function.uncurry, Pi.sub_apply,
    ← neg_sub (tetrahedronVertex i), Pi.single_neg]
  simp; abel

/-- `z_{ii} = 0`. -/
@[simp]
theorem tetrahedronEdgeVector_self (i : Fin 4) : tetrahedronEdgeVector i i = 0 := by
  ext p; simp [tetrahedronEdgeVector, Function.uncurry]

/-- The block of `z_{ij}` at `i` is `pᵢ - pⱼ`. -/
@[simp]
theorem curry_tetrahedronEdgeVector_left (i j : Fin 4) :
    Function.curry (tetrahedronEdgeVector i j) i = tetrahedronVertex i - tetrahedronVertex j := by
  rw [curry_tetrahedronEdgeVector]
  by_cases h : i = j <;> simp [h]

/-- The block of `z_{ij}` at `j` is `pⱼ - pᵢ`. -/
@[simp]
theorem curry_tetrahedronEdgeVector_right (i j : Fin 4) :
    Function.curry (tetrahedronEdgeVector i j) j = tetrahedronVertex j - tetrahedronVertex i := by
  rw [tetrahedronEdgeVector_comm, curry_tetrahedronEdgeVector_left]

/-- The blocks of `z_{ij}` away from `i` and `j` vanish. -/
@[simp]
theorem curry_tetrahedronEdgeVector_of_ne (i j : Fin 4) {m : Fin 4} (hi : m ≠ i) (hj : m ≠ j) :
    Function.curry (tetrahedronEdgeVector i j) m = 0 := by
  simp [curry_tetrahedronEdgeVector, hi, hj]

/-- The symmetries permute the edge vectors: `σ • z_{ij} = z_{σ i, σ j}`. -/
@[simp]
theorem tetrahedronDisplacementRep_edgeVector (σ : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    tetrahedronDisplacementRep σ (tetrahedronEdgeVector i j) =
      tetrahedronEdgeVector (σ i) (σ j) := by
  ext ⟨m, k⟩
  have := congrFun (curry_tetrahedronDisplacementRep σ (tetrahedronEdgeVector i j) m) k
  simp only [Function.curry_apply] at this
  rw [this]
  simp only [tetrahedronEdgeVector, Function.curry_uncurry, Pi.sub_apply, Pi.single_apply,
    Equiv.Perm.inv_eq_iff_eq, Function.uncurry_apply_pair]
  split_ifs <;> simp [tetrahedronSymmetryMatrix_mulVec_sub]

/-- The force matrix `H = -∑_{i<j} z_{ij} z_{ij}ᵀ` of the spring tetrahedron: `(H u)ᵢ` is minus
the sum, over the edges `ij` at `i`, of the stretching `(pᵢ - pⱼ) ⬝ (uᵢ - uⱼ)` times `pᵢ - pⱼ`.
For springs of stiffness `κ` along the unit edge directions and masses `m`, this is the operator
of the linearized equation of motion `u'' = (κ / (2m)) H u` of the cited handout, the `2` being
the squared edge length (`dotProduct_self_tetrahedronVertex_sub`); that equation itself is not
derived here. -/
noncomputable def tetrahedronSpringMatrix : Matrix (Fin 4 × Fin 3) (Fin 4 × Fin 3) ℝ :=
  -∑ i, ∑ j ∈ Finset.Ioi i, vecMulVec (tetrahedronEdgeVector i j) (tetrahedronEdgeVector i j)

/-- Summing over ordered pairs counts each edge twice: `2 H = -∑_{i,j} z_{ij} z_{ij}ᵀ`. -/
theorem two_smul_tetrahedronSpringMatrix :
    (2 : ℝ) • tetrahedronSpringMatrix =
      -∑ i, ∑ j, vecMulVec (tetrahedronEdgeVector i j) (tetrahedronEdgeVector i j) := by
  rw [tetrahedronSpringMatrix]
  simp only [Fin.sum_univ_succ, Fin.sum_Ioi_zero, Fin.sum_Ioi_succ, Fin.sum_univ_zero,
    Fin.reduceSucc, tetrahedronEdgeVector_self, vecMulVec_zero, zero_add, add_zero]
  rw [tetrahedronEdgeVector_comm 1 0, tetrahedronEdgeVector_comm 2 0,
    tetrahedronEdgeVector_comm 3 0, tetrahedronEdgeVector_comm 2 1,
    tetrahedronEdgeVector_comm 3 1, tetrahedronEdgeVector_comm 3 2]
  module

/-- The force matrix is symmetric. -/
theorem isSymm_tetrahedronSpringMatrix : tetrahedronSpringMatrix.IsSymm := by
  simp [Matrix.IsSymm, tetrahedronSpringMatrix, transpose_sum, transpose_vecMulVec]

/-- The force matrix is negative semidefinite. -/
theorem posSemidef_neg_tetrahedronSpringMatrix : (-tetrahedronSpringMatrix).PosSemidef := by
  rw [tetrahedronSpringMatrix, neg_neg]
  exact Matrix.posSemidef_sum _ fun i _ ↦ Matrix.posSemidef_sum _ fun j _ ↦ by
    simpa using Matrix.posSemidef_vecMulVec_self_star (tetrahedronEdgeVector i j)

private theorem two_smul_tetrahedronSpringMatrix_mulVec (u : Fin 4 × Fin 3 → ℝ) :
    (2 : ℝ) • (tetrahedronSpringMatrix *ᵥ u) =
      -∑ i, ∑ j, (tetrahedronEdgeVector i j ⬝ᵥ u) • tetrahedronEdgeVector i j := by
  rw [← smul_mulVec, two_smul_tetrahedronSpringMatrix]
  simp [neg_mulVec, sum_mulVec, vecMulVec_mulVec]

/-- The force matrix is `S₄`-equivariant: `H (σ • u) = σ • (H u)`. -/
theorem tetrahedronSpringMatrix_mulVec_displacementRep (σ : Equiv.Perm (Fin 4))
    (u : Fin 4 × Fin 3 → ℝ) :
    tetrahedronSpringMatrix *ᵥ tetrahedronDisplacementRep σ u =
      tetrahedronDisplacementRep σ (tetrahedronSpringMatrix *ᵥ u) := by
  refine smul_right_injective _ (two_ne_zero : (2 : ℝ) ≠ 0) ?_
  simp only
  rw [← map_smul, two_smul_tetrahedronSpringMatrix_mulVec,
    two_smul_tetrahedronSpringMatrix_mulVec, map_neg, map_sum, ← Equiv.sum_comp σ]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_sum, ← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul, ← tetrahedronDisplacementRep_edgeVector, dotProduct_tetrahedronDisplacementRep]

/-! ### Translation and linear coordinates -/

/-- Every displacement is uniquely a translation plus a linear field on the centred vertices:
`(t, A) ↦ (t + A qᵢ)ᵢ` is a linear equivalence `ℝ³ × M₃(ℝ) ≃ ℝ¹²`, with inverse
`u ↦ (¼ ∑ᵢ uᵢ, ∑ᵢ uᵢ qᵢᵀ)`. -/
noncomputable def tetrahedronAffineFieldEquiv :
    ((Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ) ≃ₗ[ℝ] (Fin 4 × Fin 3 → ℝ) where
  toFun x p := x.1 p.2 + (x.2 *ᵥ tetrahedronCenteredVertex p.1) p.2
  map_add' x y := by ext p; simp [add_mulVec]; ring
  map_smul' c x := by ext p; simp [smul_mulVec]; ring
  invFun u := ((4 : ℝ)⁻¹ • ∑ i, Function.curry u i,
    ∑ i, vecMulVec (Function.curry u i) (tetrahedronCenteredVertex i))
  left_inv x := by
    obtain ⟨t, A⟩ := x
    have hc (i : Fin 4) : Function.curry (fun p : Fin 4 × Fin 3 ↦
        t p.2 + (A *ᵥ tetrahedronCenteredVertex p.1) p.2) i =
          t + A *ᵥ tetrahedronCenteredVertex i := rfl
    have ht : ∑ i, vecMulVec t (tetrahedronCenteredVertex i) = 0 := by
      ext k l
      simp only [Matrix.sum_apply, vecMulVec_apply, ← Finset.mul_sum, Matrix.zero_apply]
      rw [← Finset.sum_apply, sum_tetrahedronCenteredVertex, Pi.zero_apply, mul_zero]
    simp only [hc, Finset.sum_add_distrib, add_vecMulVec, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Matrix.mulVec_sum, sum_tetrahedronCenteredVertex, mulVec_zero, add_zero,
      ← eq_sum_vecMulVec_mulVec_tetrahedronCenteredVertex A, ht]
    ext <;> simp
  right_inv u := by
    ext ⟨i, k⟩
    simp only [Matrix.sum_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
      sum_dotProduct_tetrahedronCenteredVertex_smul]
    simp [Function.curry]

/-- The field `(t + A qᵢ)ᵢ`, read off at vertex `i` and coordinate `k`. -/
@[simp]
theorem tetrahedronAffineFieldEquiv_apply (t : Fin 3 → ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (p : Fin 4 × Fin 3) :
    tetrahedronAffineFieldEquiv (t, A) p = t p.2 + (A *ᵥ tetrahedronCenteredVertex p.1) p.2 :=
  (rfl)

/-- The translation part of `u` is the mean `¼ ∑ᵢ uᵢ` and its linear part is `∑ᵢ uᵢ qᵢᵀ`. -/
@[simp]
theorem tetrahedronAffineFieldEquiv_symm_apply (u : Fin 4 × Fin 3 → ℝ) :
    tetrahedronAffineFieldEquiv.symm u = ((4 : ℝ)⁻¹ • ∑ i, Function.curry u i,
      ∑ i, vecMulVec (Function.curry u i) (tetrahedronCenteredVertex i)) :=
  (rfl)

/-- The force matrix in the coordinates `uᵢ = t + A qᵢ`: it kills the translation `t` and maps
`A` to `-2 (A + Aᵀ) + 2 diag(A) - 2 tr(A) I`. -/
theorem tetrahedronSpringMatrix_mulVec_affineFieldEquiv (t : Fin 3 → ℝ)
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    tetrahedronSpringMatrix *ᵥ tetrahedronAffineFieldEquiv (t, A) =
      tetrahedronAffineFieldEquiv
        (0, (-2 : ℝ) • (A + Aᵀ) + (2 : ℝ) • diagonal A.diag - (2 * A.trace) • 1) := by
  ext ⟨m, k⟩
  rw [tetrahedronSpringMatrix]
  simp only [Fin.sum_univ_succ, Fin.sum_Ioi_zero, Fin.sum_Ioi_succ, Fin.sum_univ_zero,
    Fin.reduceSucc]
  fin_cases m <;> fin_cases k <;>
    simp [tetrahedronAffineFieldEquiv_apply, tetrahedronEdgeVector, tetrahedronCenteredVertex_eq,
      tetrahedronVertex, mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_four,
      Fin.sum_univ_three, vecMulVec_apply, Matrix.trace, Function.uncurry, Pi.single_apply,
      Matrix.one_apply, diagonal_apply] <;> ring

/-! ### The spectrum -/

/-- An eigenbasis of the force matrix in the coordinates `(t, A)`: three translations, three
infinitesimal rotations, two diagonal trace-zero matrices, three symmetric matrices with zero
diagonal and the identity. -/
private noncomputable def tetrahedronModeCoord :
    Fin 12 → (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ :=
  ![(![1, 0, 0], 0), (![0, 1, 0], 0), (![0, 0, 1], 0),
    (0, !![0, 1, 0; -1, 0, 0; 0, 0, 0]), (0, !![0, 0, 1; 0, 0, 0; -1, 0, 0]),
    (0, !![0, 0, 0; 0, 0, 1; 0, -1, 0]),
    (0, !![1, 0, 0; 0, -1, 0; 0, 0, 0]), (0, !![0, 0, 0; 0, 1, 0; 0, 0, -1]),
    (0, !![0, 1, 0; 1, 0, 0; 0, 0, 0]), (0, !![0, 0, 1; 0, 0, 0; 1, 0, 0]),
    (0, !![0, 0, 0; 0, 0, 1; 0, 1, 0]), (0, 1)]

/-- The eigenvalues of the modes `tetrahedronModeCoord`. -/
private noncomputable def tetrahedronModeEigenvalue : Fin 12 → ℝ :=
  ![0, 0, 0, 0, 0, 0, -2, -2, -4, -4, -4, -8]

private theorem linearIndependent_tetrahedronModeCoord :
    LinearIndependent ℝ tetrahedronModeCoord := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h1 (k : Fin 3) := congrFun (congrArg Prod.fst hg) k
  have h2 (k l : Fin 3) := congrFun (congrFun (congrArg Prod.snd hg) k) l
  have e0 := h1 0; have e1 := h1 1; have e2 := h1 2
  have e00 := h2 0 0; have e01 := h2 0 1; have e02 := h2 0 2; have e10 := h2 1 0
  have e11 := h2 1 1; have e12 := h2 1 2; have e20 := h2 2 0; have e21 := h2 2 1
  have e22 := h2 2 2
  simp [Fin.sum_univ_succ, tetrahedronModeCoord] at e0 e1 e2 e00 e01 e02 e10 e11 e12 e20 e21 e22
  fin_cases i <;> simp <;> linarith

/-- The normal modes of the spring tetrahedron, as a basis of `ℝ¹²`. -/
private noncomputable def tetrahedronModeBasis : Module.Basis (Fin 12) ℝ (Fin 4 × Fin 3 → ℝ) :=
  (basisOfLinearIndependentOfCardEqFinrank linearIndependent_tetrahedronModeCoord
    (by simp [Module.finrank_matrix])).map tetrahedronAffineFieldEquiv

private theorem tetrahedronSpringMatrix_mulVec_modeBasis (m : Fin 12) :
    tetrahedronSpringMatrix *ᵥ tetrahedronModeBasis m =
      tetrahedronModeEigenvalue m • tetrahedronModeBasis m := by
  simp only [tetrahedronModeBasis, Module.Basis.map_apply,
    coe_basisOfLinearIndependentOfCardEqFinrank]
  have hm : ((0 : Fin 3 → ℝ),
      (-2 : ℝ) • ((tetrahedronModeCoord m).2 + (tetrahedronModeCoord m).2ᵀ) +
        (2 : ℝ) • diagonal (tetrahedronModeCoord m).2.diag -
          (2 * (tetrahedronModeCoord m).2.trace) • 1) =
      tetrahedronModeEigenvalue m • tetrahedronModeCoord m := by
    fin_cases m <;> refine Prod.ext (funext fun i ↦ ?_) (Matrix.ext fun i j ↦ ?_) <;>
      fin_cases i <;> try fin_cases j
    all_goals
      simp [tetrahedronModeCoord, tetrahedronModeEigenvalue, Matrix.trace, Fin.sum_univ_three]
    all_goals norm_num
  rw [← map_smul, ← hm,
    ← tetrahedronSpringMatrix_mulVec_affineFieldEquiv (tetrahedronModeCoord m).1]

private theorem toMatrix_tetrahedronModeBasis :
    LinearMap.toMatrix tetrahedronModeBasis tetrahedronModeBasis tetrahedronSpringMatrix.toLin' =
      diagonal tetrahedronModeEigenvalue := by
  ext i j
  rw [LinearMap.toMatrix_apply, toLin'_apply, tetrahedronSpringMatrix_mulVec_modeBasis, map_smul,
    Module.Basis.repr_self]
  by_cases h : i = j <;> simp [h]

/-- The characteristic polynomial of the force matrix is `X⁶ (X + 2)² (X + 4)³ (X + 8)`. -/
theorem charpoly_tetrahedronSpringMatrix :
    tetrahedronSpringMatrix.charpoly =
      Polynomial.X ^ 6 * (Polynomial.X + 2) ^ 2 * (Polynomial.X + 4) ^ 3 *
        (Polynomial.X + 8) := by
  rw [← charpoly_toLin', ← LinearMap.charpoly_toMatrix _ tetrahedronModeBasis,
    toMatrix_tetrahedronModeBasis, charpoly_diagonal]
  simp [Fin.prod_univ_succ, tetrahedronModeEigenvalue, map_ofNat Polynomial.C]
  ring

/-- The eigenspaces of the force matrix have dimensions `6`, `2`, `3` and `1` for the eigenvalues
`0`, `-2`, `-4` and `-8`, and every other eigenspace is zero. -/
theorem finrank_eigenspace_tetrahedronSpringMatrix (μ : ℝ) :
    Module.finrank ℝ (Module.End.eigenspace tetrahedronSpringMatrix.toLin' μ) =
      (if μ = 0 then 6 else 0) + (if μ = -2 then 2 else 0) + (if μ = -4 then 3 else 0) +
        (if μ = -8 then 1 else 0) := by
  -- In the eigenbasis the eigenspaces are the maximal generalized eigenspaces, whose dimensions
  -- are the multiplicities of the roots of the characteristic polynomial.
  rw [← Matrix.toLin_toMatrix tetrahedronModeBasis tetrahedronModeBasis
      tetrahedronSpringMatrix.toLin', toMatrix_tetrahedronModeBasis,
    ← maxGenEigenspace_toLin_diagonal_eq_eigenspace, LinearMap.finrank_maxGenEigenspace_eq,
    ← toMatrix_tetrahedronModeBasis, Matrix.toLin_toMatrix, charpoly_toLin',
    charpoly_tetrahedronSpringMatrix, ← Polynomial.count_roots]
  have hX : (Polynomial.X ^ 6 * (Polynomial.X + 2) ^ 2 * (Polynomial.X + 4) ^ 3 *
      (Polynomial.X + 8) : Polynomial ℝ) = (Polynomial.X - Polynomial.C 0) ^ 6 *
      (Polynomial.X - Polynomial.C (-2)) ^ 2 * (Polynomial.X - Polynomial.C (-4)) ^ 3 *
      (Polynomial.X - Polynomial.C (-8)) := by
    simp [map_ofNat Polynomial.C]
  have hm (a : ℝ) (n : ℕ) := (Polynomial.monic_X_sub_C a).pow n
  rw [hX, Polynomial.roots_mul (((hm _ _).mul (hm _ _)).mul (hm _ _) |>.mul
      (Polynomial.monic_X_sub_C _)).ne_zero,
    Polynomial.roots_mul (((hm _ _).mul (hm _ _)).mul (hm _ _)).ne_zero,
    Polynomial.roots_mul ((hm _ _).mul (hm _ _)).ne_zero]
  simp only [Polynomial.roots_pow, Polynomial.roots_X_sub_C, Multiset.count_add,
    Multiset.count_nsmul, Multiset.count_singleton]
  split_ifs <;> simp_all

private theorem mem_eigenspace_iff_affineFieldEquiv (μ : ℝ) (t : Fin 3 → ℝ)
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    tetrahedronAffineFieldEquiv (t, A) ∈
        Module.End.eigenspace tetrahedronSpringMatrix.toLin' μ ↔
      μ • t = 0 ∧
        (-2 : ℝ) • (A + Aᵀ) + (2 : ℝ) • diagonal A.diag - (2 * A.trace) • 1 = μ • A := by
  rw [Module.End.mem_eigenspace_iff, toLin'_apply,
    tetrahedronSpringMatrix_mulVec_affineFieldEquiv, ← map_smul,
    tetrahedronAffineFieldEquiv.injective.eq_iff, Prod.smul_mk, Prod.mk.injEq, eq_comm (a := 0)]

/-- The kernel of the force matrix consists of the translations plus the infinitesimal
rotations `uᵢ = t + A qᵢ`, `Aᵀ = -A`. -/
theorem tetrahedronAffineFieldEquiv_mem_eigenspace_zero_iff (t : Fin 3 → ℝ)
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    tetrahedronAffineFieldEquiv (t, A) ∈
        Module.End.eigenspace tetrahedronSpringMatrix.toLin' 0 ↔
      Aᵀ = -A := by
  rw [mem_eigenspace_iff_affineFieldEquiv, ← Matrix.ext_iff.eq, ← Matrix.ext_iff.eq]
  constructor <;> intro h <;>
    simp [Fin.forall_fin_succ, Matrix.trace, Fin.sum_univ_three] at h ⊢ <;> grind

/-- The eigenspace of the force matrix for `-2` consists of the fields `uᵢ = A qᵢ` with `A`
diagonal of trace zero. -/
theorem tetrahedronAffineFieldEquiv_mem_eigenspace_neg_two_iff (t : Fin 3 → ℝ)
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    tetrahedronAffineFieldEquiv (t, A) ∈
        Module.End.eigenspace tetrahedronSpringMatrix.toLin' (-2) ↔
      t = 0 ∧ A.IsDiag ∧ A.trace = 0 := by
  rw [mem_eigenspace_iff_affineFieldEquiv, ← Matrix.ext_iff.eq, Matrix.isDiag_iff_diagonal_diag,
    ← Matrix.ext_iff.eq]
  refine and_congr (by simp) ?_
  constructor <;> intro h <;>
    simp [Fin.forall_fin_succ, Matrix.trace, Fin.sum_univ_three] at h ⊢ <;> grind

/-- The eigenspace of the force matrix for `-4` consists of the fields `uᵢ = A qᵢ` with `A`
symmetric with zero diagonal. -/
theorem tetrahedronAffineFieldEquiv_mem_eigenspace_neg_four_iff (t : Fin 3 → ℝ)
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    tetrahedronAffineFieldEquiv (t, A) ∈
        Module.End.eigenspace tetrahedronSpringMatrix.toLin' (-4) ↔
      t = 0 ∧ A.IsSymm ∧ A.diag = 0 := by
  rw [mem_eigenspace_iff_affineFieldEquiv, ← Matrix.ext_iff.eq, Matrix.IsSymm,
    ← Matrix.ext_iff.eq]
  refine and_congr (by simp) ?_
  constructor <;> intro h <;>
    simp [Fin.forall_fin_succ, Matrix.trace, Fin.sum_univ_three, funext_iff] at h ⊢ <;> grind

/-- The eigenspace of the force matrix for `-8` is the breathing line `uᵢ = a qᵢ`. -/
theorem tetrahedronAffineFieldEquiv_mem_eigenspace_neg_eight_iff (t : Fin 3 → ℝ)
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    tetrahedronAffineFieldEquiv (t, A) ∈
        Module.End.eigenspace tetrahedronSpringMatrix.toLin' (-8) ↔
      t = 0 ∧ ∃ a : ℝ, A = a • 1 := by
  rw [mem_eigenspace_iff_affineFieldEquiv]
  refine and_congr (by simp) ⟨fun h ↦ ⟨A 0 0, ?_⟩, ?_⟩
  · rw [← Matrix.ext_iff] at h ⊢
    simp [Fin.forall_fin_succ, Matrix.trace, Fin.sum_univ_three] at h ⊢
    grind
  · rintro ⟨a, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.trace] <;> ring

end TauCeti
