/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Combinatorics.Young.FullColumns
public import TauCeti.LinearAlgebra.Matrix.MvPolynomial.Subst
public import TauCeti.RepresentationTheory.ClassicalGroups.DualWeylModule.Basis
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basic
import Mathlib.Topology.Algebra.MvPolynomial
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Schur matrices

Let `R` be a commutative ring, `μ` a Young diagram and `z` an `N' × N` matrix over `R`.
Substituting `z * y` for the `N' × n` matrix of variables (`Matrix.mvPolynomialMulLeft`) acts on
the rows and commutes with the column operations, so it maps the dual Weyl module `∇_R(d)` in `N'`
rows into the one in `N` rows (`TauCeti.DualWeylModule.mvPolynomialMulLeft_mem_dualWeylModule`).
Expanding the image of a standard bideterminant in the standard basis gives the **Schur matrix**
`TauCeti.DualWeylModule.schurMatrix μ z`, with rows indexed by the semistandard tableaux of shape
`μ` in `N'` letters and columns by those in `N` letters:

`b_T(z * y) = ∑ U, schurMatrix μ z T U • b_U(y)`,

`b_T` the bideterminant of the tableau `T`
(`TauCeti.DualWeylModule.mvPolynomialMulLeft_bideterminant`).
The coefficients are unique, since the standard bideterminants are linearly independent over every
ring, and they do not depend on the number `n ≥ μ.colLen 0` of columns of the matrix of variables.
Uniqueness gives everything else: base change, `S(g * z) = S(g) * S(z)` by substituting twice,
and the action of diagonal matrices, under which the standard bideterminants are weight vectors.
For `N' = N` the Schur matrices form a representation of `GL_N(R)` on `R^{BoundedSSYT N μ}`, read
as the dual of `∇_R(μ)` through the standard basis. It moves the vector `ev_y` of the values of the
standard bideterminants at a matrix `y` as `S(g) *ᵥ ev_y = ev_{g * y}`, and its character is the
Schur polynomial.

A shape may have columns of the full height `N`, and its tableaux in `N` letters hold
`0, …, N - 1` in these columns. Let `ν` be a shape `μ` with `d` columns of height `N` prepended,
both with at most `N` rows. Deleting these columns (`TauCeti.BoundedSSYT.fullColumnsEquiv`, written
`e`) turns the bideterminant of a tableau of shape `ν` into `Δ(y) ^ d` times that of a tableau of
shape `μ`, `Δ(y)` the minor of `y` on all rows and the first `N` columns. So the matrix
`(schurMatrix ν z).submatrix id e.symm` is the matrix of the expansion
`b_T(z * y) = Δ(y) ^ d * ∑ U, S T U • b_U(y)` over the tableaux `U` of the shape `μ` without full
columns (`TauCeti.DualWeylModule.mvPolynomialMulLeft_bideterminant_eq_pow_mul`), and for square
`g` the Schur matrix of `ν` is `det g ^ d` times that of `μ`
(`TauCeti.DualWeylModule.schurMatrix_eq_det_pow_smul_submatrix`), so that
`S(z * g) = det g ^ d • S(z) * S(g)` in that normalisation
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
  polynomial, and Weyl's character formula as a quotient of alternants.
* `TauCeti.DualWeylModule.bideterminant_ssytFilling_eq_pow_mul`,
  `TauCeti.DualWeylModule.schurMatrix_eq_det_pow_smul_submatrix`,
  `TauCeti.DualWeylModule.mvPolynomialMulLeft_bideterminant_eq_pow_mul` and
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

/-! ### The row action on the dual Weyl module -/

section RowAction

variable {R : Type*} [CommSemiring R] {N N' n : ℕ}

/-- The column degrees of the monomial `m` are the weight of `m` for the weights `Pi.single s 1`
of the variables `x_{a,s}` of the column `s`. -/
private theorem weight_single_snd (m : Fin N × Fin n →₀ ℕ) (s : Fin n) :
    Finsupp.weight (fun p : Fin N × Fin n => (Pi.single p.2 1 : Fin n → ℕ)) m s =
      ∑ a, m (a, s) := by
  classical
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Finset.sum_apply, Fintype.sum_prod_type,
    Pi.single_apply]

/-- The column degree condition of the dual Weyl module as a weighted homogeneity, for the weights
`Pi.single s 1` of the variables of the column `s`. -/
private theorem isWeightedHomogeneous_iff_sum_eq {d : Fin n → ℕ}
    {f : MvPolynomial (Fin N × Fin n) R} :
    f.IsWeightedHomogeneous (fun p : Fin N × Fin n => (Pi.single p.2 1 : Fin n → ℕ)) d ↔
      ∀ m ∈ f.support, ∀ s, ∑ a, m (a, s) = d s := by
  refine ⟨fun hf m hm s => ?_, fun hf m hm => funext fun s => ?_⟩
  · rw [← weight_single_snd, hf (mem_support_iff.mp hm)]
  · rw [weight_single_snd, hf m (mem_support_iff.mpr hm)]

/-- The substitution of `z * y` commutes with the column operations, which act on the columns:
`columnOperation` of the image is the image of `columnOperation` under the coefficientwise
substitution. -/
theorem columnOperation_mvPolynomialMulLeft (z : Matrix (Fin N') (Fin N) R) (s t : Fin n)
    (f : MvPolynomial (Fin N' × Fin n) R) :
    columnOperation R s t (mvPolynomialMulLeft z f) =
      Polynomial.mapAlgHom (mvPolynomialMulLeft (n := Fin n) z) (columnOperation R s t f) := by
  have h : (columnOperation R s t).comp (mvPolynomialMulLeft (n := Fin n) z) =
      (Polynomial.mapAlgHom (mvPolynomialMulLeft z)).comp (columnOperation (N := N') R s t) :=
    MvPolynomial.algHom_ext fun p => by
      by_cases hp : p.2 = t <;>
        simp [hp, mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
  exact congr($h f)

/-- **The row action preserves the dual Weyl module.** For every `N' × N` matrix `z`, the
substitution `f ↦ f (z * y)` maps the dual Weyl module of column degrees `d` in `N'` rows into the
one in `N` rows: it keeps the column degrees and commutes with the column operations. -/
theorem mvPolynomialMulLeft_mem_dualWeylModule (z : Matrix (Fin N') (Fin N) R) {d : Fin n → ℕ}
    {f : MvPolynomial (Fin N' × Fin n) R} (hf : f ∈ dualWeylModule R N' d) :
    mvPolynomialMulLeft z f ∈ dualWeylModule R N d := by
  rw [mem_dualWeylModule] at hf ⊢
  refine ⟨isWeightedHomogeneous_iff_sum_eq.mp ?_, fun s t hst => ?_⟩
  · rw [mvPolynomialMulLeft_def]
    refine (isWeightedHomogeneous_iff_sum_eq.mpr hf.1).aeval fun p => ?_
    simp only [Matrix.mul_apply, Matrix.map_apply, mvPolynomialX_apply]
    exact IsWeightedHomogeneous.sum _ _ _ fun a _ => by
      simpa using (isWeightedHomogeneous_C _ (z p.1 a)).mul (isWeightedHomogeneous_X R _ (a, p.2))
  · rw [columnOperation_mvPolynomialMulLeft, hf.2 s t hst, Polynomial.coe_mapAlgHom,
      Polynomial.map_C, AlgHom.coe_toRingHom]

end RowAction

/-! ### The Schur matrix -/

section SchurMatrix

variable {R : Type*} [CommRing R] {N N' N'' n : ℕ} (μ : YoungDiagram)

/-- The **Schur matrix** of an `N' × N` matrix `z` for the Young diagram `μ`: the matrix of the
coefficients of the expansion `b_T(z * y) = ∑ U, schurMatrix μ z T U • b_U(y)` of the standard
bideterminant of a tableau `T` in `N'` letters, at `z * y`, in the standard bideterminants of the
tableaux `U` in `N` letters (`TauCeti.DualWeylModule.mvPolynomialMulLeft_bideterminant`). It is
read off in the matrix of variables with `μ.colLen 0` columns; by
`TauCeti.DualWeylModule.schurMatrix_eq_iff` any number of columns gives the same matrix. -/
noncomputable def schurMatrix (z : Matrix (Fin N') (Fin N) R) :
    Matrix (BoundedSSYT N' μ) (BoundedSSYT N μ) R :=
  Matrix.of fun T U => (standardBasis R N (n := μ.colLen 0) le_rfl).repr
    ⟨mvPolynomialMulLeft z (bideterminant R μ le_rfl (ssytFilling T)),
      mvPolynomialMulLeft_mem_dualWeylModule z (bideterminant_mem_dualWeylModule R μ le_rfl _)⟩ U

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

/-- **The torus acts on standard bideterminants by their content.** Substituting `diagonal x * y`,
that is, rescaling the row `a` of the matrix of variables by `x a`, multiplies the bideterminant of
a tableau `T` by `∏ a, x a ^ c_a`, `c_a` the number of entries of `T` equal to `a`. -/
theorem mvPolynomialMulLeft_diagonal_bideterminant (hμ : μ.colLen 0 ≤ n) (T : BoundedSSYT N μ)
    (x : Fin N → R) :
    mvPolynomialMulLeft (diagonal x) (bideterminant R μ hμ (ssytFilling T)) =
      (∏ a, x a ^ BoundedSSYT.weight T a) • bideterminant R μ hμ (ssytFilling T) := by
  rw [mvPolynomialMulLeft_diagonal]
  ext m
  rw [coeff_rescale, smul_eq_C_mul, coeff_C_mul]
  by_cases hm : (bideterminant R μ hμ (ssytFilling T)).coeff m = 0
  · rw [hm, mul_zero, mul_zero]
  congr 1
  -- The degree of `m` in the row `a` is the number of entries `a` of `T`.
  have h_row (a : Fin N) : ∑ s, m (a, s) = BoundedSSYT.weight T a := by
    rw [BoundedSSYT.weight_apply, ← isWeightedHomogeneous_bideterminant hμ T a hm]
    simp only [Finsupp.weight_apply, rowWeight_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type,
      Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
    simp
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun a _ => by simp only [Finset.prod_pow_eq_pow_sum, h_row]

/-- **Diagonal matrices act diagonally.** The Schur matrix of `diagonal x` is diagonal, with entry
`∏ a, x a ^ c_a` at the tableau `U`, `c_a` the number of entries of `U` equal to `a`. -/
theorem schurMatrix_diagonal [DecidableEq (BoundedSSYT N μ)] (x : Fin N → R) :
    schurMatrix μ (diagonal x) = diagonal fun U => ∏ a, x a ^ BoundedSSYT.weight U a := by
  rw [schurMatrix_eq_iff μ le_rfl]
  intro T
  rw [mvPolynomialMulLeft_diagonal_bideterminant]
  simp [diagonal_apply, ite_smul]

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
  rw [map_mul, alternant_def, alternant_def, RingHom.map_det, RingHom.map_det] at h
  rw [trace_schurMatrix_diagonal]
  convert h using 3 <;> ext a b <;> simp [YoungDiagram.betaNumber_def]

end SchurMatrix

/-! ### Full columns -/

section FullColumns

variable {R : Type*} [CommRing R] {N N' n d : ℕ} {μ ν : YoungDiagram}

/-- Minors on the first columns agree when their lists of rows agree. -/
private theorem mvPolynomialMinor_castLE_congr {k k' : ℕ} (hk : k = k') {r : Fin k → Fin N}
    {r' : Fin k' → Fin N} (hr : ∀ a : Fin k, r a = r' (Fin.cast hk a)) (h₁ : k ≤ n)
    (h₂ : k' ≤ n) :
    mvPolynomialMinor R r (Fin.castLE h₁) = mvPolynomialMinor R r' (Fin.castLE h₂) := by
  subst hk
  congr 1
  exact funext fun a => by simpa using hr a

variable (hμ : μ.colLen 0 ≤ N) (hν : ν.colLen 0 ≤ N) (h : ∀ i < N, ν.rowLen i = μ.rowLen i + d)
include hμ hν h

/-- **Full columns split off as a power of the leading minor.** Let `ν` be `μ` with `d` columns of
the full height `N` prepended, both with at most `N` rows, and `N ≤ n`. The bideterminant of a
tableau `T` of shape `ν` with entries smaller than `N` is `Δ ^ d` times the bideterminant of the
tableau of shape `μ` obtained by deleting these columns, `Δ` the minor of the `N × n` matrix of
variables on all rows and the first `N` columns. -/
theorem bideterminant_ssytFilling_eq_pow_mul (hN : N ≤ n) (T : BoundedSSYT N ν) :
    bideterminant R ν (hν.trans hN) (ssytFilling T) =
      mvPolynomialMinor R id (Fin.castLE hN) ^ d *
        bideterminant R μ (hμ.trans hN)
          (ssytFilling (BoundedSSYT.fullColumnsEquiv hμ hν h T)) := by
  have hK : ν.rowLen 0 ≤ d + μ.rowLen 0 := by
    rcases Nat.eq_zero_or_pos N with rfl | hN0
    · rw [YoungDiagram.rowLen_eq_zero_iff.mpr hν]
      exact Nat.zero_le _
    · rw [h 0 hN0]
      omega
  rw [bideterminant_eq_prod_range R ν _ _ hK, Finset.prod_range_add,
    bideterminant_eq_prod_range R μ _ _ le_rfl]
  congr 1
  · -- The first `d` columns are full, and the tableau holds `0, …, N - 1` in each of them.
    calc ∏ j ∈ range d, columnMinor R ν (hν.trans hN) (ssytFilling T) j
        = ∏ _j ∈ range d, mvPolynomialMinor R id (Fin.castLE hN) := by
          refine Finset.prod_congr rfl fun j hj => ?_
          have hc := YoungDiagram.colLen_eq_of_rowLen_eq_add hν h (Finset.mem_range.mp hj)
          rw [columnMinor_def]
          refine mvPolynomialMinor_castLE_congr hc (fun a => Fin.ext ?_) _ _
          have ha : (a : ℕ) < N := hc ▸ a.isLt
          have hc' : (N - 1, j) ∈ ν := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
          simpa using BoundedSSYT.val_eq_of_mem_of_lt T hc' ha
      _ = _ := by rw [Finset.prod_const, Finset.card_range]
  · -- The remaining columns are those of `μ`.
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [columnMinor_def, columnMinor_def]
    refine mvPolynomialMinor_castLE_congr
      (by rw [add_comm]; exact YoungDiagram.colLen_add_of_rowLen_eq_add hμ hν h j)
      (fun a => Fin.ext ?_) _ _
    simp [add_comm]

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
  rw [mvPolynomialMulLeft_bideterminant ν, ← (BoundedSSYT.fullColumnsEquiv hμ hν h).symm.sum_comp,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [bideterminant_ssytFilling_eq_pow_mul hμ hν h hN, Equiv.apply_symm_apply, mul_smul_comm]

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
