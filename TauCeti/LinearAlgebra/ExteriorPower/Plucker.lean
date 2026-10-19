/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Plücker coordinates

For a family `x : Fin p → ι → R` of `p` vectors with coordinates in a linearly ordered type `ι`,
its Plücker coordinates are its maximal minors: for each `p`-element subset `s` of `ι`, the
determinant of the `p × p` matrix whose rows are the vectors `x i` restricted to the coordinates
in `s`, listed in increasing order. The subsets are indexed by Mathlib's `Set.powersetCard ι p`,
the index type of the induced basis of the exterior power.

The coordinates are those of the exterior product `x 0 ∧ ⋯ ∧ x (p - 1)` in the basis of
`⋀[R]^p (ι → R)` induced by the standard basis. Consequently a change of the family by a square
matrix multiplies all coordinates by its determinant, and over a field they vanish identically
exactly when the family is linearly dependent. Plücker coordinates are the coordinates of the
point in projective space attached to a subspace of `K^ι`, and heights of subspaces are heights
of these points.

The Cauchy–Binet formula expresses the determinant of the `p × p` product of two such families
as the sum of products of their Plücker coordinates. Over a commutative star ring, for instance
`ℂ`, applying it to a family and its conjugate writes the Hermitian Gram determinant of the
family as the sum of the squared absolute values of its Plücker coordinates.

All results hold over an arbitrary commutative ring except the comparison with linear
independence, which is over a field. The empty family has a single Plücker coordinate, equal to
`1`, and a family of more than `#ι` vectors has none.

## Main definitions

* `TauCeti.plucker x`: the Plücker coordinates of a family `x : Fin p → ι → R`.

## Main results

* `TauCeti.plucker_eq_repr_ιMulti`: the Plücker coordinates are the coordinates of
  `exteriorPower.ιMulti R p x` in the exterior-power basis induced by `Pi.basisFun R ι`.
* `TauCeti.plucker_sum_smul`: replacing the family by its product with a square matrix
  multiplies the Plücker coordinates by the determinant of that matrix.
* `TauCeti.det_mul_transpose_eq_sum_plucker_mul`: the Cauchy–Binet formula.
* `TauCeti.det_mul_conjTranspose_eq_sum_plucker_mul_star`: its Hermitian form.
* `TauCeti.plucker_ne_zero_iff`: over a field, the Plücker coordinates of a family are not all
  zero exactly when the family is linearly independent.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §2.8.

The proofs use Mathlib's exterior-power basis `Module.Basis.exteriorPower` and its coordinate
formula `exteriorPower.ιMultiDual_apply_ιMulti`, by Sophie Morel and Daniel Morrison.
-/

public section

open Set Set.powersetCard exteriorPower

namespace TauCeti

variable {R S ι : Type*} [CommRing R] [CommRing S] [LinearOrder ι] {p : ℕ}

/-- The Plücker coordinates of a family `x` of `p` vectors in `ι → R`: at a `p`-element subset `s`
of `ι`, the `p × p` minor of the matrix with rows `x i` on the columns in `s`, taken in increasing
order. -/
def plucker (x : Fin p → ι → R) (s : powersetCard ι p) : R :=
  (Matrix.of fun i j ↦ x i (ofFinEmbEquiv.symm s j)).det

/-- The Plücker coordinate at `s` is the minor on the columns in `s`. -/
theorem plucker_apply (x : Fin p → ι → R) (s : powersetCard ι p) :
    plucker x s = (Matrix.of fun i j ↦ x i (ofFinEmbEquiv.symm s j)).det := (rfl)

/-- The empty family has Plücker coordinate `1`. -/
@[simp]
theorem plucker_of_isEmpty (x : Fin 0 → ι → R) (s : powersetCard ι 0) : plucker x s = 1 :=
  Matrix.det_isEmpty

/-- The Plücker coordinate of a single vector at the singleton `{i}` is its `i`-th coordinate. -/
@[simp]
theorem plucker_ofSingleton (x : Fin 1 → ι → R) (i : ι) : plucker x (ofSingleton i) = x 0 i := by
  -- The only element of the singleton `{i}`, listed in increasing order, is `i`.
  have hi : ofFinEmbEquiv.symm (ofSingleton i) 0 = i :=
    Finset.mem_singleton.1 <| mem_coe_iff.2 <|
      (mem_range_ofFinEmbEquiv_symm_iff_mem (ofSingleton i) _).1 ⟨0, rfl⟩
  simp [plucker_apply, Matrix.det_unique, hi]

/-- Plücker coordinates commute with ring homomorphisms applied to all coordinates. -/
theorem plucker_map (f : R →+* S) (x : Fin p → ι → R) (s : powersetCard ι p) :
    plucker (fun i k ↦ f (x i k)) s = f (plucker x s) := by
  rw [plucker_apply, plucker_apply, f.map_det]
  refine congrArg Matrix.det (Matrix.ext fun i j ↦ ?_)
  simp

/-- Replacing a family by its product with a square matrix `A` multiplies its Plücker
coordinates by `det A`. -/
theorem plucker_sum_smul (A : Matrix (Fin p) (Fin p) R) (x : Fin p → ι → R)
    (s : powersetCard ι p) :
    plucker (fun i ↦ ∑ k, A i k • x k) s = A.det * plucker x s := by
  rw [plucker_apply, plucker_apply, ← Matrix.det_mul]
  congr 1
  ext i j
  simp [Matrix.mul_apply]

/-- The Plücker coordinates of `x` are the coordinates of the exterior product of `x` in the basis
of `⋀[R]^p (ι → R)` induced by the standard basis of `ι → R`. -/
theorem plucker_eq_repr_ιMulti [Finite ι] (x : Fin p → ι → R) (s : powersetCard ι p) :
    plucker x s = ((Pi.basisFun R ι).exteriorPower p).repr (ιMulti R p x) s := by
  rw [basis_repr_apply, ιMultiDual_apply_ιMulti, plucker_apply]
  simp

/-- The basis vector of `⋀[R]^p (ι → R)` at `s` pairs with the exterior product of `p` linear
forms to give the minor of their coefficient matrix on the coordinates in `s`. -/
private theorem pairingDual_ιMulti_exteriorPower_basisFun [Fintype ι]
    (y : Fin p → ι → R) (s : powersetCard ι p) :
    pairingDual R (ι → R) p (ιMulti R p fun j ↦ Fintype.linearCombination R (y j))
        ((Pi.basisFun R ι).exteriorPower p s) = plucker y s := by
  classical
  rw [basis_apply, ιMulti_family, pairingDual_ιMulti_ιMulti, plucker_apply,
    ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [Fintype.linearCombination_apply, Pi.single_apply]

/-- **The Cauchy–Binet formula.** The determinant of the `p × p` matrix of pairwise products
`∑ₖ x i k * y j k` is the sum over the `p`-element subsets `s` of `ι` of the products of the
Plücker coordinates of `x` and `y` at `s`. For `p > #ι` both sides vanish. -/
theorem det_mul_transpose_eq_sum_plucker_mul [Fintype ι] (x y : Fin p → ι → R) :
    (Matrix.of x * (Matrix.of y).transpose).det = ∑ s, plucker x s * plucker y s := by
  classical
  set b := (Pi.basisFun R ι).exteriorPower p
  set φ := pairingDual R (ι → R) p (ιMulti R p fun j ↦ Fintype.linearCombination R (y j))
  have h : (Matrix.of x * (Matrix.of y).transpose).det = φ (ιMulti R p x) := by
    rw [pairingDual_ιMulti_ιMulti]
    refine congrArg Matrix.det (Matrix.ext fun i j ↦ ?_)
    simp [Matrix.mul_apply, Fintype.linearCombination_apply]
  rw [h, ← b.sum_repr (ιMulti R p x), map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [map_smul, pairingDual_ιMulti_exteriorPower_basisFun, ← plucker_eq_repr_ιMulti, smul_eq_mul]

/-- **The Cauchy–Binet formula, Hermitian form.** Over a commutative star ring, the determinant
of the Hermitian Gram matrix `∑ₖ x i k * star (x j k)` of a family is the sum of the products of
its Plücker coordinates with their conjugates. -/
theorem det_mul_conjTranspose_eq_sum_plucker_mul_star [StarRing R] [Fintype ι]
    (x : Fin p → ι → R) :
    (Matrix.of x * (Matrix.of x).conjTranspose).det = ∑ s, plucker x s * star (plucker x s) := by
  have hx : (Matrix.of x).conjTranspose =
      (Matrix.of fun i k ↦ starRingEnd R (x i k)).transpose := by
    ext
    simp [starRingEnd_apply]
  rw [hx, det_mul_transpose_eq_sum_plucker_mul]
  simp_rw [plucker_map, starRingEnd_apply]

section Field

variable {K : Type*} [Field K]

/-- Over a field, the Plücker coordinates of a family are not all zero exactly when the family is
linearly independent. -/
theorem plucker_ne_zero_iff [Finite ι] (x : Fin p → ι → K) :
    plucker x ≠ 0 ↔ LinearIndependent K x := by
  rw [← ιMulti_ne_zero_iff, not_iff_not]
  have h : plucker x = ((Pi.basisFun K ι).exteriorPower p).repr (ιMulti K p x) := by
    ext s
    exact plucker_eq_repr_ιMulti x s
  rw [h, Finsupp.coe_eq_zero, LinearEquiv.map_eq_zero_iff]

end Field

end TauCeti
