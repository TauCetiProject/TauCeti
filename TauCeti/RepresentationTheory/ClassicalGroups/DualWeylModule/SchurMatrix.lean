/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import TauCeti.RepresentationTheory.ClassicalGroups.DualWeylModule.FullColumns
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basic
import Mathlib.Topology.Algebra.MvPolynomial
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant

/-!
# Schur matrices

Let `R` be a commutative ring, `μ` a Young diagram and `z` an `N' × N` matrix over `R`. Replacing
the `N' × n` matrix of variables by the `N' × n` matrix `z * y`, `y` the `N × n` matrix of
variables (`Matrix.mvPolynomialMulLeft`), acts on the rows and commutes with the column operations,
so it maps the dual Weyl module `∇_R(d)` in `N'` rows into the one in `N` rows
(`TauCeti.DualWeylModule.mvPolynomialMulLeft_mem_dualWeylModule`).
Expanding the image of a standard bideterminant in the standard basis gives the **Schur matrix**
`TauCeti.DualWeylModule.schurMatrix μ z`, with rows indexed by the semistandard tableaux of shape
`μ` in `N'` letters and columns by those in `N` letters:

`b_T(z * y) = ∑ U, schurMatrix μ z T U • b_U(y)`,

`b_T` the bideterminant of the tableau `T`
(`TauCeti.DualWeylModule.mvPolynomialMulLeft_bideterminant`).
The coefficients are unique, since the standard bideterminants are linearly independent over every
ring, and they do not depend on the number `n ≥ μ.colLen 0` of columns of the matrix of variables.
Uniqueness gives everything else: base change, `S(g * z) = S(g) * S(z)` by substituting twice,
and the action of diagonal matrices, under which the standard bideterminants are weight vectors
(`TauCeti.DualWeylModule.mvPolynomialMulLeft_diagonal_bideterminant`).

For `N' = N` the Schur matrices form a representation of `GL_N(R)` on `R^{BoundedSSYT N μ}`. Read
a vector `v` as the linear functional `λ` on `∇_R(μ)` with `λ(b_U) = v U`. Then `S(g) *ᵥ v` is the
functional `f ↦ λ(f(g * y))`: `S(g)` acts on the linear functionals by precomposition with the
substitution `f ↦ f(g * y)`, a right action on `∇_R(μ)`, so that `g ↦ S(g)` is a left action on
the functionals. For instance `S(g)` moves the evaluation at a matrix `y`, whose vector `ev_y`
holds the values of the standard bideterminants at `y`, to the evaluation at `g * y`:
`S(g) *ᵥ ev_y = ev_{g * y}`. The character of the representation is the Schur polynomial.

A shape may have columns of the full height `N`, and its tableaux in `N` letters hold
`0, …, N - 1` in these columns. Let `ν` be a shape `μ` with `d` columns of height `N` prepended,
both with at most `N` rows. Deleting these columns (`TauCeti.BoundedSSYT.fullColumnsEquiv`, written
`e`) turns the bideterminant of a tableau of shape `ν` into `Δ(y) ^ d` times that of a tableau of
shape `μ`, `Δ(y)` the minor of `y` on all rows and the first `N` columns
(`TauCeti.DualWeylModule.bideterminant_ssytFilling_eq_pow_mul`). So the matrix
`S(z) = (schurMatrix ν z).submatrix id e.symm` is the unique matrix of the expansion
`b_T(z * y) = Δ(y) ^ d * ∑ U, S(z) T U • b_U(y)` over the tableaux `U` of the shape `μ` left after
deleting the first `d` full columns (`TauCeti.DualWeylModule.submatrix_schurMatrix_eq_iff`); `μ`
has no full column only when `d` is the number of full columns of `ν`. Evaluated at a matrix `y`
with leading `N × N` block `y₀`, this reads `det y₀ ^ d • (S(z) *ᵥ ev_y) = ev_{z * y}`, the two
evaluation vectors being those of `μ` and `ν`. For square `g` the Schur matrix of `ν` is
`det g ^ d` times that of `μ` (`TauCeti.DualWeylModule.schurMatrix_eq_det_pow_smul_submatrix`), so
that `S(z * g) = det g ^ d • (S(z) * schurMatrix μ g)`
(`TauCeti.DualWeylModule.submatrix_schurMatrix_mul_eq_det_pow_smul`). A shape with a column taller
than `N` has no tableau in `N` letters, and then `b_T(z * y) = 0`.

## Main definitions

* `TauCeti.DualWeylModule.schurMatrix μ z`: the Schur matrix of `z`.
* `TauCeti.DualWeylModule.evalVector μ hμ y`: the values of the standard bideterminants at a matrix
  `y`.
* `TauCeti.DualWeylModule.schurMatrixHom μ` and `TauCeti.DualWeylModule.schurRep μ e`: the Schur
  matrices of square matrices as a monoid homomorphism, and the representation
  `g ↦ det g ^ e • schurMatrix μ g` of `GL_N(R)`.

## Main results

* `TauCeti.DualWeylModule.schurMatrix_apply`: the entries are the coordinates in the standard
  basis.
* `TauCeti.DualWeylModule.schurMatrix_eq_iff`: the Schur matrix is the unique matrix of
  coefficients of the expansion.
* `TauCeti.DualWeylModule.schurMatrix_map` and
  `TauCeti.DualWeylModule.map_schurMatrix_mvPolynomialX`: base change; the entries are polynomials
  with integer coefficients in the entries of `z`, the same over every ring.
* `TauCeti.DualWeylModule.continuous_schurMatrix`: continuity over a topological ring.
* `TauCeti.DualWeylModule.schurMatrix_one`, `TauCeti.DualWeylModule.schurMatrix_mul` and
  `TauCeti.DualWeylModule.schurMatrix_smul`: `S(1) = 1`, `S(g * z) = S(g) * S(z)` for rectangular
  matrices, and `S(t • z) = t ^ |μ| • S(z)`.
* `TauCeti.DualWeylModule.schurMatrix_mulVec_evalVector`: `S(z) *ᵥ ev_y = ev_{z * y}`.
* `TauCeti.DualWeylModule.schurMatrix_diagonal`: a diagonal matrix acts diagonally, by the monomial
  of the content of each tableau.
* `TauCeti.DualWeylModule.trace_schurMatrix_diagonal` and
  `TauCeti.DualWeylModule.trace_schurMatrix_diagonal_mul_det`: the character is the Schur
  polynomial, and Weyl's character formula in the cross-multiplied form: the character times the
  alternant `det (x_a ^ (N - 1 - b))` is the alternant `det (x_a ^ (λ_b + N - 1 - b))`.
* `TauCeti.DualWeylModule.schurMatrix_eq_det_pow_smul_submatrix`,
  `TauCeti.DualWeylModule.submatrix_schurMatrix_eq_iff`,
  `TauCeti.DualWeylModule.mvPolynomialMulLeft_bideterminant_eq_pow_mul`,
  `TauCeti.DualWeylModule.det_pow_smul_submatrix_schurMatrix_mulVec_evalVector` and
  `TauCeti.DualWeylModule.submatrix_schurMatrix_mul_eq_det_pow_smul`: full columns split off as
  powers of the determinant.

## References

* C. De Concini, D. Eisenbud, C. Procesi, *Young diagrams and determinantal varieties*,
  Invent. Math. **56** (1980), 129-165.
* K. Akin, D. A. Buchsbaum, J. Weyman, *Schur functors and Schur complexes*, Adv. Math. **44**
  (1982), 207-278.

The definition of the Schur matrix as the unique coefficients of the expansion, and the proofs of
its properties from that uniqueness, follow the method of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC),
`src/Lib/GLn/SchurModule/SchurMatrix.lean` (`New.schur`, `New.schur_map`, `New.schur_mul_left`,
`New.schur_diagonal`, `New.weyl_character`), where it is set up for the semi-invariants of a Borel
subgroup and a basis that is not identified with the semistandard tableaux.
-/

public section

namespace TauCeti

open MvPolynomial Matrix Finset

namespace DualWeylModule

/-! ### The Schur matrix -/

section SchurMatrix

variable {R : Type*} [CommRing R] {N N' N'' n : ℕ} (μ : YoungDiagram)

/-- The **Schur matrix** of an `N' × N` matrix `z` for the Young diagram `μ`: the matrix of the
coefficients of the expansion `b_T(z * y) = ∑ U, schurMatrix μ z T U • b_U(y)` of the standard
bideterminant of a tableau `T` in `N'` letters, at `z * y`, in the standard bideterminants of the
tableaux `U` in `N` letters (`TauCeti.DualWeylModule.mvPolynomialMulLeft_bideterminant`). It is
read off in the matrix of variables with `μ.colLen 0` columns; by
`TauCeti.DualWeylModule.schurMatrix_eq_iff` any number `n ≥ μ.colLen 0` of columns gives the same
matrix. -/
noncomputable def schurMatrix (z : Matrix (Fin N') (Fin N) R) :
    Matrix (BoundedSSYT N' μ) (BoundedSSYT N μ) R :=
  Matrix.of fun T U => (standardBasis R N (n := μ.colLen 0) le_rfl).repr
    ⟨mvPolynomialMulLeft z (bideterminant R μ le_rfl (ssytFilling T)),
      mvPolynomialMulLeft_mem_dualWeylModule z (bideterminant_mem_dualWeylModule R μ le_rfl _)⟩ U

/-- **The entries of the Schur matrix are coordinates in the standard basis.** The entry of the
Schur matrix of `z` at the tableaux `T` and `U` is the coordinate at `b_U` of `b_T(z * y)` in the
standard basis of the dual Weyl module of the `N × μ.colLen 0` matrix of variables `y`. -/
theorem schurMatrix_apply (z : Matrix (Fin N') (Fin N) R) (T : BoundedSSYT N' μ)
    (U : BoundedSSYT N μ) :
    schurMatrix μ z T U = (standardBasis R N (n := μ.colLen 0) le_rfl).repr
      ⟨mvPolynomialMulLeft z (bideterminant R μ le_rfl (ssytFilling T)),
        mvPolynomialMulLeft_mem_dualWeylModule z (bideterminant_mem_dualWeylModule R μ le_rfl _)⟩
      U :=
  (rfl)

/-- The expansion that defines the Schur matrix, in the matrix of variables with `μ.colLen 0`
columns. -/
private theorem mvPolynomialMulLeft_bideterminant_colLen (z : Matrix (Fin N') (Fin N) R)
    (T : BoundedSSYT N' μ) :
    mvPolynomialMulLeft z (bideterminant R μ le_rfl (ssytFilling T)) =
      ∑ U, schurMatrix μ z T U • bideterminant R μ (le_refl (μ.colLen 0)) (ssytFilling U) := by
  have h := congrArg Subtype.val ((standardBasis R N (n := μ.colLen 0) le_rfl).sum_repr
    ⟨mvPolynomialMulLeft z (bideterminant R μ le_rfl (ssytFilling T)),
      mvPolynomialMulLeft_mem_dualWeylModule z (bideterminant_mem_dualWeylModule R μ le_rfl _)⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, coe_standardBasis] at h
  simp only [schurMatrix_apply]
  exact h.symm

/-- **The Schur matrix expands the substituted bideterminants.** For a tableau `T` of shape `μ` in
`N'` letters and the `N × n` matrix of variables `y`, `n ≥ μ.colLen 0`:
`b_T(z * y) = ∑ U, schurMatrix μ z T U • b_U(y)`, the sum running over the tableaux of shape `μ`
in `N` letters. -/
theorem mvPolynomialMulLeft_bideterminant (hμ : μ.colLen 0 ≤ n) (z : Matrix (Fin N') (Fin N) R)
    (T : BoundedSSYT N' μ) :
    mvPolynomialMulLeft z (bideterminant R μ hμ (ssytFilling T)) =
      ∑ U, schurMatrix μ z T U • bideterminant R μ hμ (ssytFilling U) := by
  rw [← rename_bideterminant R μ le_rfl hμ, mvPolynomialMulLeft_rename,
    mvPolynomialMulLeft_bideterminant_colLen, map_sum]
  simp only [map_smul, rename_bideterminant]

/-- **Uniqueness of the Schur matrix.** For any number `n ≥ μ.colLen 0` of columns of the matrix of
variables, the Schur matrix of `z` is the only matrix `A` with `b_T(z * y) = ∑ U, A T U • b_U(y)`
for every tableau `T`. -/
theorem schurMatrix_eq_iff (hμ : μ.colLen 0 ≤ n) {z : Matrix (Fin N') (Fin N) R}
    {A : Matrix (BoundedSSYT N' μ) (BoundedSSYT N μ) R} :
    schurMatrix μ z = A ↔ ∀ T, mvPolynomialMulLeft z (bideterminant R μ hμ (ssytFilling T)) =
      ∑ U, A T U • bideterminant R μ hμ (ssytFilling U) := by
  refine ⟨fun h T => h ▸ mvPolynomialMulLeft_bideterminant μ hμ z T, fun h => ?_⟩
  ext T U
  have h_sub : ∑ V, (schurMatrix μ z T V - A T V) • bideterminant R μ hμ (ssytFilling V) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← mvPolynomialMulLeft_bideterminant μ hμ, ← h T,
      sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp
    (linearIndependent_bideterminant_ssytFilling R N μ hμ) _ h_sub U)

/-! ### Base change and continuity -/

/-- **Base change.** The Schur matrix commutes with every homomorphism of commutative rings
`φ : R → S`, applied entrywise. -/
theorem schurMatrix_map {S : Type*} [CommRing S] (φ : R →+* S) (z : Matrix (Fin N') (Fin N) R) :
    schurMatrix μ (z.map φ) = (schurMatrix μ z).map φ := by
  rw [schurMatrix_eq_iff μ le_rfl]
  intro T
  have h := congrArg (MvPolynomial.map φ) (mvPolynomialMulLeft_bideterminant μ le_rfl z T)
  rw [map_mvPolynomialMulLeft, map_bideterminant, map_sum] at h
  simpa only [smul_eq_C_mul, map_mul, map_C, map_bideterminant, Matrix.map_apply] using h

/-- **The entries of a Schur matrix are integer polynomials in the entries of the matrix.** The
Schur matrix of `z` is obtained from the Schur matrix of the generic `N' × N` matrix over
`ℤ[x_{b,a}]` by evaluating its entries at `x_{b,a} = z b a`. -/
theorem map_schurMatrix_mvPolynomialX (z : Matrix (Fin N') (Fin N) R) :
    (schurMatrix μ (mvPolynomialX (Fin N') (Fin N) ℤ)).map (aeval fun p => z p.1 p.2) =
      schurMatrix μ z := by
  have h := schurMatrix_map μ (aeval (R := ℤ) fun p : Fin N' × Fin N => z p.1 p.2).toRingHom
    (mvPolynomialX (Fin N') (Fin N) ℤ)
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  rw [← h]
  congr 1
  ext b a
  simp

/-- **Continuity.** Over a topological ring the Schur matrix depends continuously on the matrix:
its entries are polynomials in the entries of `z`. -/
theorem continuous_schurMatrix [TopologicalSpace R] [IsTopologicalSemiring R] :
    Continuous (schurMatrix (R := R) (N := N) (N' := N') μ) := by
  have h : schurMatrix (R := R) (N := N) (N' := N') μ = fun z =>
      (schurMatrix μ (mvPolynomialX (Fin N') (Fin N) ℤ)).map (aeval fun p => z p.1 p.2) :=
    funext fun z => (map_schurMatrix_mvPolynomialX μ z).symm
  rw [h]
  refine continuous_pi fun T => continuous_pi fun U => ?_
  simp only [Matrix.map_apply, aeval_def, eval₂_eq_eval_map]
  exact (continuous_eval _).comp
    (continuous_pi fun p => continuous_id.matrix_elem p.1 p.2)

/-! ### Multiplicativity -/

/-- The Schur matrix of the identity matrix is the identity matrix. -/
@[simp]
theorem schurMatrix_one [DecidableEq (BoundedSSYT N μ)] :
    schurMatrix μ (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  rw [schurMatrix_eq_iff μ le_rfl]
  intro T
  simp [Matrix.one_apply, ite_smul]

/-- **Multiplicativity.** For rectangular matrices `g` (`N'' × N'`) and `z` (`N' × N`), the Schur
matrix of `g * z` is the product of the Schur matrices: substituting `z * y` into
`b_T(g * y') = ∑ U, S(g) T U • b_U(y')` gives `b_T(g * z * y)`. -/
@[simp]
theorem schurMatrix_mul (g : Matrix (Fin N'') (Fin N') R) (z : Matrix (Fin N') (Fin N) R) :
    schurMatrix μ (g * z) = schurMatrix μ g * schurMatrix μ z := by
  rw [schurMatrix_eq_iff μ le_rfl]
  intro T
  rw [mvPolynomialMulLeft_mul, AlgHom.comp_apply, mvPolynomialMulLeft_bideterminant μ le_rfl g,
    map_sum]
  simp only [map_smul, mvPolynomialMulLeft_bideterminant μ le_rfl z, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [Matrix.mul_apply, Finset.sum_smul]

/-- The Schur matrices of square matrices, as a monoid homomorphism
`Matrix (Fin N) (Fin N) R →* Matrix (BoundedSSYT N μ) (BoundedSSYT N μ) R`. -/
noncomputable def schurMatrixHom [DecidableEq (BoundedSSYT N μ)] :
    Matrix (Fin N) (Fin N) R →* Matrix (BoundedSSYT N μ) (BoundedSSYT N μ) R where
  toFun := schurMatrix μ
  map_one' := schurMatrix_one μ
  map_mul' := schurMatrix_mul μ

@[simp]
theorem schurMatrixHom_apply [DecidableEq (BoundedSSYT N μ)] (g : Matrix (Fin N) (Fin N) R) :
    schurMatrixHom μ g = schurMatrix μ g :=
  (rfl)

/-- The **representation of weight `(μ, e)`** of `GL_N(R)`, `e ∈ ℤ`: the Schur matrices twisted
by a power of the determinant, `g ↦ det g ^ e • schurMatrix μ g`. -/
noncomputable def schurRep [DecidableEq (BoundedSSYT N μ)] (e : ℤ) :
    GL (Fin N) R →* GL (BoundedSSYT N μ) R :=
  MonoidHom.toHomUnits
    { toFun g := ((GeneralLinearGroup.det g ^ e : Rˣ) : R) • schurMatrix μ (g : Matrix _ _ R)
      map_one' := by simp
      map_mul' g h := by
        simp only [map_mul, mul_zpow, Units.val_mul, schurMatrix_mul, smul_mul_smul_comm] }

@[simp]
theorem coe_schurRep_apply [DecidableEq (BoundedSSYT N μ)] (e : ℤ) (g : GL (Fin N) R) :
    (schurRep μ e g : Matrix (BoundedSSYT N μ) (BoundedSSYT N μ) R) =
      ((GeneralLinearGroup.det g ^ e : Rˣ) : R) • schurMatrix μ (g : Matrix (Fin N) (Fin N) R) :=
  (rfl)

/-! ### Evaluation vectors -/

/-- The **evaluation vector** of a matrix `y` with `n ≥ μ.colLen 0` columns: the values at `y` of
the standard bideterminants of the tableaux of shape `μ` in `N` letters. -/
noncomputable def evalVector (hμ : μ.colLen 0 ≤ n) (y : Matrix (Fin N) (Fin n) R) :
    BoundedSSYT N μ → R :=
  fun U => eval (fun p => y p.1 p.2) (bideterminant R μ hμ (ssytFilling U))

@[simp]
theorem evalVector_apply (hμ : μ.colLen 0 ≤ n) (y : Matrix (Fin N) (Fin n) R)
    (U : BoundedSSYT N μ) :
    evalVector μ hμ y U = eval (fun p => y p.1 p.2) (bideterminant R μ hμ (ssytFilling U)) :=
  (rfl)

/-- **The Schur matrix acts on evaluation vectors**: `S(z) *ᵥ ev_y = ev_{z * y}`. -/
theorem schurMatrix_mulVec_evalVector (hμ : μ.colLen 0 ≤ n) (z : Matrix (Fin N') (Fin N) R)
    (y : Matrix (Fin N) (Fin n) R) :
    schurMatrix μ z *ᵥ evalVector μ hμ y = evalVector μ hμ (z * y) := by
  ext T
  rw [evalVector_apply, ← eval_mvPolynomialMulLeft, mvPolynomialMulLeft_bideterminant μ hμ,
    map_sum]
  simp [mulVec, dotProduct, smul_eval]

/-! ### Diagonal matrices and the character -/

/-- **Diagonal matrices act diagonally.** The Schur matrix of `diagonal x` is diagonal, with entry
`∏ a, x a ^ c_a` at the tableau `U`, `c_a` the number of entries of `U` equal to `a`. -/
theorem schurMatrix_diagonal [DecidableEq (BoundedSSYT N μ)] (x : Fin N → R) :
    schurMatrix μ (diagonal x) = diagonal fun U => ∏ a, x a ^ BoundedSSYT.weight U a := by
  rw [schurMatrix_eq_iff μ le_rfl]
  intro T
  rw [mvPolynomialMulLeft_diagonal_bideterminant]
  simp [diagonal_apply, ite_smul, BoundedSSYT.weight_apply]

/-- **Homogeneity.** The Schur matrix of `t • z` is `t ^ |μ|` times that of `z`, `|μ|` the number
of cells of `μ`. -/
@[simp]
theorem schurMatrix_smul (t : R) (z : Matrix (Fin N') (Fin N) R) :
    schurMatrix μ (t • z) = t ^ μ.card • schurMatrix μ z := by
  classical
  rw [smul_eq_diagonal_mul, schurMatrix_mul, schurMatrix_diagonal]
  ext T U
  simp only [diagonal_mul, Finset.prod_pow_eq_pow_sum, BoundedSSYT.sum_weight, Matrix.smul_apply,
    smul_eq_mul]

/-- **The character is the Schur polynomial.** The trace of the Schur matrix of `diagonal x` is the
Schur polynomial of `μ` in `N` variables evaluated at `x`. -/
theorem trace_schurMatrix_diagonal (x : Fin N → R) :
    trace (schurMatrix μ (diagonal x)) = eval x (diagramSchurPoly N R μ) := by
  classical
  rw [schurMatrix_diagonal, trace_diagonal, eval_diagramSchurPoly]

/-- **Weyl's character formula.** For a Young diagram `μ` with at most `N` rows, the trace of the
Schur matrix of `diagonal x` times the alternant `det (x a ^ (N - 1 - b))` is the alternant
`det (x a ^ (μ.rowLen b + N - 1 - b))`. -/
theorem trace_schurMatrix_diagonal_mul_det (hμ : μ.colLen 0 ≤ N) (x : Fin N → R) :
    trace (schurMatrix μ (diagonal x)) * det (of fun a b : Fin N => x a ^ (N - 1 - (b : ℕ))) =
      det (of fun a b : Fin N => x a ^ (μ.rowLen b + (N - 1 - b))) := by
  have h := congrArg (eval x) (diagramSchurPoly_mul_alternant (R := R) N μ hμ)
  rw [map_mul, eval_alternant, eval_alternant] at h
  simp only [YoungDiagram.betaNumber_def] at h
  rw [trace_schurMatrix_diagonal, h]

end SchurMatrix

/-! ### Full columns -/

section FullColumns

variable {R : Type*} [CommRing R] {N N' n d : ℕ} {μ ν : YoungDiagram}

variable (hμ : μ.colLen 0 ≤ N) (hν : ν.colLen 0 ≤ N) (h : ∀ i < N, ν.rowLen i = μ.rowLen i + d)
include hμ hν h

/-- **The full columns of a Schur matrix.** Let `ν` be `μ` with `d` columns of the full height `N`
prepended, both with at most `N` rows. The Schur matrix of an `N × N` matrix `g` for `ν` is
`det g ^ d` times its Schur matrix for `μ`, the tableaux being matched by deleting the full columns
(`TauCeti.BoundedSSYT.fullColumnsEquiv`). -/
theorem schurMatrix_eq_det_pow_smul_submatrix (g : Matrix (Fin N) (Fin N) R) :
    schurMatrix ν g = g.det ^ d • (schurMatrix μ g).submatrix
      (BoundedSSYT.fullColumnsEquiv hμ hν h) (BoundedSSYT.fullColumnsEquiv hμ hν h) := by
  rw [schurMatrix_eq_iff ν (hν.trans le_rfl)]
  intro T
  rw [bideterminant_ssytFilling_eq_pow_mul hμ hν h le_rfl, map_mul, map_pow,
    mvPolynomialMulLeft_mvPolynomialMinor, mvPolynomialMulLeft_bideterminant μ,
    ← (BoundedSSYT.fullColumnsEquiv hμ hν h).sum_comp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [bideterminant_ssytFilling_eq_pow_mul hμ hν h le_rfl, Matrix.smul_apply,
    Matrix.submatrix_apply, smul_eq_mul, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_pow]
  ring

/-- **Uniqueness of the Schur matrix with the full columns split off.** Let `ν` be `μ` with `d`
columns of the full height `N` prepended, both with at most `N` rows, `e` deleting the full
columns, and `N ≤ n`. For an `N' × N` matrix `z`, `(schurMatrix ν z).submatrix id e.symm` is the
only matrix `A` with `b_T(z * y) = Δ(y) ^ d * ∑ U, A T U • b_U(y)` for every tableau `T` of shape
`ν` in `N'` letters, the sum running over the tableaux `U` of shape `μ` in `N` letters and `Δ(y)`
the minor of `y` on all rows and the first `N` columns. -/
theorem submatrix_schurMatrix_eq_iff (hN : N ≤ n) {z : Matrix (Fin N') (Fin N) R}
    {A : Matrix (BoundedSSYT N' ν) (BoundedSSYT N μ) R} :
    (schurMatrix ν z).submatrix id (BoundedSSYT.fullColumnsEquiv hμ hν h).symm = A ↔
      ∀ T, mvPolynomialMulLeft z (bideterminant R ν (hν.trans hN) (ssytFilling T)) =
        mvPolynomialMinor R id (Fin.castLE hN) ^ d *
          ∑ U, A T U • bideterminant R μ (hμ.trans hN) (ssytFilling U) := by
  -- Multiplied by `Δ ^ d`, the standard bideterminants of shape `μ` are those of shape `ν`, so the
  -- expansion is the defining expansion of the Schur matrix of `ν`.
  have hA (T : BoundedSSYT N' ν) : mvPolynomialMinor R id (Fin.castLE hN) ^ d *
      ∑ U, A T U • bideterminant R μ (hμ.trans hN) (ssytFilling U) =
        ∑ V, A.submatrix id (BoundedSSYT.fullColumnsEquiv hμ hν h) T V •
          bideterminant R ν (hν.trans hN) (ssytFilling V) := by
    rw [Finset.mul_sum, ← (BoundedSSYT.fullColumnsEquiv hμ hν h).sum_comp]
    refine Finset.sum_congr rfl fun V _ => ?_
    rw [bideterminant_ssytFilling_eq_pow_mul hμ hν h hN, submatrix_apply, id, mul_smul_comm]
  simp only [hA, ← schurMatrix_eq_iff ν (hν.trans hN)]
  constructor
  · rintro rfl
    ext T V
    simp
  · intro hS
    ext T U
    simp [hS]

/-- **Schur matrices of rectangular matrices with the full columns split off.** Let `ν` be `μ` with
`d` columns of the full height `N` prepended, both with at most `N` rows, and `N ≤ n`. For an
`N' × N` matrix `z` and a tableau `T` of shape `ν` in `N'` letters,
`b_T(z * y) = Δ(y) ^ d * ∑ U, schurMatrix ν z T (e⁻¹ U) • b_U(y)`, the sum running over the tableaux
`U` of shape `μ` in `N` letters, `e` deleting the full columns and `Δ(y)` the minor of `y` on all
rows and the first `N` columns. -/
theorem mvPolynomialMulLeft_bideterminant_eq_pow_mul (hN : N ≤ n) (z : Matrix (Fin N') (Fin N) R)
    (T : BoundedSSYT N' ν) :
    mvPolynomialMulLeft z (bideterminant R ν (hν.trans hN) (ssytFilling T)) =
      mvPolynomialMinor R id (Fin.castLE hN) ^ d *
        ∑ U, schurMatrix ν z T ((BoundedSSYT.fullColumnsEquiv hμ hν h).symm U) •
          bideterminant R μ (hμ.trans hN) (ssytFilling U) := by
  simpa only [submatrix_apply, id] using (submatrix_schurMatrix_eq_iff hμ hν h hN).mp rfl T

/-- **Evaluation vectors with the full columns split off.** Let `ν` be `μ` with `d` columns of the
full height `N` prepended, both with at most `N` rows, `e` deleting the full columns, and
`S(z) = (schurMatrix ν z).submatrix id e.symm`. For `N ≤ n`, an `N' × N` matrix `z` and an
`N × n` matrix `y` with leading `N × N` block `y₀`, `det y₀ ^ d • (S(z) *ᵥ ev_μ(y)) = ev_ν(z * y)`,
`ev_μ` and `ev_ν` the evaluation vectors of the shapes `μ` and `ν`. -/
theorem det_pow_smul_submatrix_schurMatrix_mulVec_evalVector (hN : N ≤ n)
    (z : Matrix (Fin N') (Fin N) R) (y : Matrix (Fin N) (Fin n) R) :
    (y.submatrix id (Fin.castLE hN)).det ^ d •
        ((schurMatrix ν z).submatrix id (BoundedSSYT.fullColumnsEquiv hμ hν h).symm *ᵥ
          evalVector μ (hμ.trans hN) y) =
      evalVector ν (hν.trans hN) (z * y) := by
  have hΔ : eval (fun p => y p.1 p.2) (mvPolynomialMinor R id (Fin.castLE hN)) =
      (y.submatrix id (Fin.castLE hN)).det := by
    rw [← aeval_eq_eval, aeval_mvPolynomialMinor]
  ext T
  rw [evalVector_apply ν, ← eval_mvPolynomialMulLeft,
    mvPolynomialMulLeft_bideterminant_eq_pow_mul hμ hν h hN, map_mul, map_pow, hΔ, map_sum]
  simp [mulVec, dotProduct, smul_eval]

/-- **Multiplicativity with the full columns split off.** Let `ν` be `μ` with `d` columns of the
full height `N` prepended, both with at most `N` rows, and normalise the Schur matrix of an
`N' × N` matrix `z` as `S(z) = (schurMatrix ν z).submatrix id e.symm`, `e` deleting the full
columns. Then `S(z * g) = det g ^ d • S(z) * schurMatrix μ g` for every `N × N` matrix `g`. -/
theorem submatrix_schurMatrix_mul_eq_det_pow_smul (z : Matrix (Fin N') (Fin N) R)
    (g : Matrix (Fin N) (Fin N) R) :
    (schurMatrix ν (z * g)).submatrix id (BoundedSSYT.fullColumnsEquiv hμ hν h).symm =
      g.det ^ d • ((schurMatrix ν z).submatrix id (BoundedSSYT.fullColumnsEquiv hμ hν h).symm *
        schurMatrix μ g) := by
  rw [schurMatrix_mul, schurMatrix_eq_det_pow_smul_submatrix hμ hν h g]
  ext T U
  simp only [submatrix_apply, Matrix.smul_apply, Matrix.mul_apply, id, smul_eq_mul,
    Finset.mul_sum, Equiv.apply_symm_apply]
  rw [← (BoundedSSYT.fullColumnsEquiv hμ hν h).sum_comp]
  refine Finset.sum_congr rfl fun V _ => ?_
  simp only [Equiv.symm_apply_apply]
  ring

end FullColumns

end DualWeylModule

end TauCeti
