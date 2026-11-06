/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.LDU
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Regular coordinates for block LDU factorization

The inverse to block LDU multiplication is defined over the localization of the integral
matrix polynomial ring at the product of the leading block minors. Thus the three factors
are regular functions on this principal open, not merely factorizations chosen separately
over each field. They specialize to the unique block LDU factors over every commutative ring,
including rings with nilpotents.

`Matrix.BlockLDU` bundles a factorization with invertible middle factor. Its uniqueness makes
it a subsingleton, and `Matrix.BlockLDU.map` changes coefficients. The universal factorization
`Matrix.BlockLDU.universal` lives over `Matrix.BlockLDU.CoordinateRing`; its evaluation equations
identify all three factors after any specialization. The denominator theorem
`Matrix.BlockLDU.exists_polynomial_coordinate` expresses every element of this ring as a
polynomial with a power of the leading-minor product as denominator.

For an integral representation with an ordered weight basis, these are the ambient matrix
coordinates used to construct the inverse of big-cell multiplication. Identifying these
matrix factors with the root-subgroup and torus factors is a separate assertion.

The matrix existence and uniqueness inputs are `Matrix.exists_blockLDU_iff` and
`Matrix.eq_of_blockLDU_eq`. No formula obtained by division in a field is used.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, §3.5.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 5, Theorem 7.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace Matrix

open OrderDual

variable {m α R S : Type*} [Fintype m] [DecidableEq m] [LinearOrder α]
  [CommRing R] [CommRing S]

/-- The product of the leading block minors for the ranking `b`. Repeated blocks may occur;
inverting this product still inverts precisely all the leading block minors. -/
noncomputable def leadingBlockMinorProduct (b : m → α) (M : Matrix m m R) : R :=
  ∏ i, (M.toSquareBlockProp fun j => b j ≤ b i).det

/-- The defining product formula for the leading block minors. -/
theorem leadingBlockMinorProduct_def (b : m → α) (M : Matrix m m R) :
    leadingBlockMinorProduct b M = ∏ i, (M.toSquareBlockProp fun j => b j ≤ b i).det := (rfl)

/-- The product of the leading block minors commutes with a change of coefficients. -/
@[simp]
theorem leadingBlockMinorProduct_map (b : m → α) (M : Matrix m m R) (f : R →+* S) :
    leadingBlockMinorProduct b (M.map f) = f (leadingBlockMinorProduct b M) := by
  classical
  simp only [leadingBlockMinorProduct, map_prod]
  congr 1
  funext i
  exact (f.map_det_submatrix M Subtype.val Subtype.val).symm

/-- Substituting a matrix into the generic leading-minor product recovers its leading-minor
product. -/
theorem leadingBlockMinorProduct_mvPolynomialX_eval₂ (b : m → α) (M : Matrix m m R) :
    MvPolynomial.eval₂ (Int.castRingHom R) (fun p : m × m => M p.1 p.2)
      (leadingBlockMinorProduct b (mvPolynomialX m m ℤ)) = leadingBlockMinorProduct b M := by
  have hmap := leadingBlockMinorProduct_map b (mvPolynomialX m m ℤ)
    (MvPolynomial.eval₂Hom (Int.castRingHom R) fun p : m × m => M p.1 p.2)
  simpa only [MvPolynomial.coe_eval₂Hom, mvPolynomialX_map_eval₂] using hmap.symm

/-- Inverting the product of the leading block minors inverts every one of them. -/
@[simp]
theorem isUnit_leadingBlockMinorProduct_iff (b : m → α) (M : Matrix m m R) :
    IsUnit (leadingBlockMinorProduct b M) ↔
      ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det := by
  classical
  exact IsUnit.prod_univ_iff

/-- A block LDU factorization with invertible middle factor. All fields are determined by the
matrix being factored, by uniqueness of block LDU factorization. -/
structure BlockLDU (b : m → α) (M : Matrix m m R) where
  /-- The lower block unitriangular factor. -/
  lower : Matrix m m R
  /-- The invertible block diagonal factor. -/
  diagonal : Matrix m m R
  /-- The upper block unitriangular factor. -/
  upper : Matrix m m R
  lower_unitriangular : lower.BlockUnitriangular (toDual ∘ b)
  diagonal_triangular : diagonal.BlockTriangular b
  diagonal_triangular_toDual : diagonal.BlockTriangular (toDual ∘ b)
  upper_unitriangular : upper.BlockUnitriangular b
  isUnit_det_diagonal : IsUnit diagonal.det
  mul_eq : lower * diagonal * upper = M

namespace BlockLDU

variable {b : m → α} {M : Matrix m m R}

instance : Subsingleton (BlockLDU b M) where
  allEq F G := by
    obtain ⟨hL, hD, hU⟩ := eq_of_blockLDU_eq F.lower_unitriangular F.diagonal_triangular
      F.diagonal_triangular_toDual F.upper_unitriangular G.lower_unitriangular
      G.diagonal_triangular G.diagonal_triangular_toDual G.upper_unitriangular
      F.isUnit_det_diagonal (F.mul_eq.trans G.mul_eq.symm)
    cases F
    cases G
    cases hL
    cases hD
    cases hU
    rfl

/-- Construct the unique block LDU factorization on the leading-minor unit locus. -/
noncomputable def ofIsUnitLeadingMinors
    (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det) : BlockLDU b M := by
  apply Classical.choice
  obtain ⟨L, D, U, hL, hD, hD', hU, hdet, h⟩ := (exists_blockLDU_iff M).mp hM
  exact ⟨⟨L, D, U, hL, hD, hD', hU, hdet, h.symm⟩⟩

/-- The leading block minors of a matrix admitting a block LDU factorization are units. -/
theorem isUnit_leadingMinors (F : BlockLDU b M) (i : m) :
    IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det :=
  (exists_blockLDU_iff M).mpr ⟨F.lower, F.diagonal, F.upper, F.lower_unitriangular,
    F.diagonal_triangular, F.diagonal_triangular_toDual, F.upper_unitriangular,
    F.isUnit_det_diagonal, F.mul_eq.symm⟩ i

/-- Change coefficients in a block LDU factorization. Uniqueness ensures that these are the
factors of the specialized matrix, even when the coefficient map is not injective. -/
def map (F : BlockLDU b M) (f : R →+* S) : BlockLDU b (M.map f) where
  lower := F.lower.map f
  diagonal := F.diagonal.map f
  upper := F.upper.map f
  lower_unitriangular := F.lower_unitriangular.map f
  diagonal_triangular := F.diagonal_triangular.map f
  diagonal_triangular_toDual := F.diagonal_triangular_toDual.map f
  upper_unitriangular := F.upper_unitriangular.map f
  isUnit_det_diagonal := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact F.isUnit_det_diagonal.map f
  mul_eq := by rw [← Matrix.map_mul, ← Matrix.map_mul, F.mul_eq]

@[simp] theorem map_lower (F : BlockLDU b M) (f : R →+* S) :
    (F.map f).lower = F.lower.map f := (rfl)

@[simp] theorem map_diagonal (F : BlockLDU b M) (f : R →+* S) :
    (F.map f).diagonal = F.diagonal.map f := (rfl)

@[simp] theorem map_upper (F : BlockLDU b M) (f : R →+* S) :
    (F.map f).upper = F.upper.map f := (rfl)

variable (b : m → α)

/-- The coordinate ring of the principal open of matrices whose leading block minors are units.
It is an integral polynomial ring with just the leading-minor product inverted. -/
noncomputable abbrev CoordinateRing :=
  Localization.Away (leadingBlockMinorProduct b (mvPolynomialX m m ℤ))

/-- The generic matrix on the leading-minor principal open. -/
noncomputable def universalMatrix : Matrix m m (CoordinateRing b) :=
  (mvPolynomialX m m ℤ).map (algebraMap (MvPolynomial (m × m) ℤ) (CoordinateRing b))

/-- The entries of the universal matrix are the images of the polynomial variables. -/
@[simp]
theorem universalMatrix_apply (i j : m) :
    universalMatrix b i j = algebraMap (MvPolynomial (m × m) ℤ) (CoordinateRing b)
      (MvPolynomial.X (i, j)) := by
  simp [universalMatrix, mvPolynomialX_apply]

/-- The universal matrix has unit leading block minors. -/
theorem isUnit_leadingMinors_universalMatrix (i : m) :
    IsUnit ((universalMatrix b).toSquareBlockProp fun j => b j ≤ b i).det := by
  apply (isUnit_leadingBlockMinorProduct_iff b _).mp _ i
  rw [universalMatrix, leadingBlockMinorProduct_map]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The universal block LDU factorization, with entries regular on the leading-minor open. -/
noncomputable def universal : BlockLDU b (universalMatrix b) :=
  ofIsUnitLeadingMinors (isUnit_leadingMinors_universalMatrix b)

variable {b}

/-- Evaluate the leading-minor coordinate ring at any block LDU factorization. -/
noncomputable def eval (F : BlockLDU b M) : CoordinateRing b →+* R :=
  IsLocalization.Away.lift (leadingBlockMinorProduct b (mvPolynomialX m m ℤ))
    (g := MvPolynomial.eval₂Hom (Int.castRingHom R) fun p : m × m => M p.1 p.2) (by
      rw [MvPolynomial.coe_eval₂Hom, leadingBlockMinorProduct_mvPolynomialX_eval₂]
      exact (isUnit_leadingBlockMinorProduct_iff b M).mpr F.isUnit_leadingMinors)

/-- Evaluation on polynomial coordinates is ordinary matrix substitution. -/
@[simp]
theorem eval_algebraMap (F : BlockLDU b M) (P : MvPolynomial (m × m) ℤ) :
    F.eval (algebraMap (MvPolynomial (m × m) ℤ) (CoordinateRing b) P) =
      MvPolynomial.eval₂ (Int.castRingHom R) (fun p : m × m => M p.1 p.2) P :=
  IsLocalization.Away.lift_eq _ _ P

/-- The inverted polynomial specializes to the product of the leading block minors. -/
theorem eval_leadingBlockMinorProduct (F : BlockLDU b M) :
    F.eval (algebraMap (MvPolynomial (m × m) ℤ) (CoordinateRing b)
      (leadingBlockMinorProduct b (mvPolynomialX m m ℤ))) = leadingBlockMinorProduct b M := by
  rw [eval_algebraMap, leadingBlockMinorProduct_mvPolynomialX_eval₂]

/-- Specializing the universal matrix recovers the matrix being factored. -/
@[simp]
theorem universalMatrix_map_eval (F : BlockLDU b M) :
    (universalMatrix b).map F.eval = M := by
  ext i j
  simp

/-- Evaluation is the unique ring homomorphism specializing the universal matrix to `M`. -/
theorem eval_unique (F : BlockLDU b M) (g : CoordinateRing b →+* R)
    (hg : (universalMatrix b).map g = M) : g = F.eval := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (leadingBlockMinorProduct b (mvPolynomialX m m ℤ)))
  apply MvPolynomial.ringHom_ext' (Subsingleton.elim _ _)
  rintro ⟨i, j⟩
  simp only [RingHom.comp_apply, ← universalMatrix_apply]
  simpa only [map_apply] using congrArg (fun N => N i j)
    (hg.trans (universalMatrix_map_eval F).symm)

/-- Evaluation commutes with arbitrary changes of coefficients. -/
@[simp]
theorem eval_map (F : BlockLDU b M) (f : R →+* S) :
    (F.map f).eval = f.comp F.eval := by
  symm
  apply eval_unique (F.map f)
  ext i j
  simpa only [map_apply, RingHom.comp_apply] using
    congrArg f (congrArg (fun N => N i j) (universalMatrix_map_eval F))

private theorem universal_factors_map_eval (F : BlockLDU b M) :
    (universal b).lower.map F.eval = F.lower ∧
      (universal b).diagonal.map F.eval = F.diagonal ∧
      (universal b).upper.map F.eval = F.upper := by
  let G := (universal b).map F.eval
  apply eq_of_blockLDU_eq G.lower_unitriangular G.diagonal_triangular
    G.diagonal_triangular_toDual G.upper_unitriangular F.lower_unitriangular
    F.diagonal_triangular F.diagonal_triangular_toDual F.upper_unitriangular
    G.isUnit_det_diagonal
  exact G.mul_eq.trans ((universalMatrix_map_eval F).trans F.mul_eq.symm)

/-- The universal lower factor specializes to the unique lower factor. -/
@[simp]
theorem universal_lower_map_eval (F : BlockLDU b M) :
    (universal b).lower.map F.eval = F.lower :=
  (universal_factors_map_eval F).1

/-- The universal diagonal factor specializes to the unique diagonal factor. -/
@[simp]
theorem universal_diagonal_map_eval (F : BlockLDU b M) :
    (universal b).diagonal.map F.eval = F.diagonal :=
  (universal_factors_map_eval F).2.1

/-- The universal upper factor specializes to the unique upper factor. -/
@[simp]
theorem universal_upper_map_eval (F : BlockLDU b M) :
    (universal b).upper.map F.eval = F.upper :=
  (universal_factors_map_eval F).2.2

/-- Every regular coordinate has a polynomial numerator and a power of the leading-minor
product as denominator, uniformly over all commutative value rings and all factorizations.
In particular this applies to every entry of each of the three universal factors. -/
theorem exists_polynomial_coordinate (z : CoordinateRing b) :
    ∃ (n : ℕ) (P : MvPolynomial (m × m) ℤ),
      ∀ (A : Type*) [CommRing A] (N : Matrix m m A) (F : BlockLDU b N),
        F.eval z * leadingBlockMinorProduct b N ^ n =
          MvPolynomial.eval₂ (Int.castRingHom A) (fun p : m × m => N p.1 p.2) P := by
  obtain ⟨n, P, hP⟩ := IsLocalization.Away.surj
    (leadingBlockMinorProduct b (mvPolynomialX m m ℤ)) z
  refine ⟨n, P, fun A _ N F => ?_⟩
  have h := congrArg F.eval hP
  rw [map_mul, map_pow, eval_leadingBlockMinorProduct, eval_algebraMap] at h
  exact h

end BlockLDU

end Matrix
