/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import TauCeti.LinearAlgebra.ExteriorPower.Basic

import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.LinearAlgebra.Matrix.Determinant.SumElim
import TauCeti.LinearAlgebra.Matrix.Gram
import TauCeti.LinearAlgebra.Submodule.Primitive

/-!
# Plücker coordinates

For a family `x : Fin p → ι → R` of `p` vectors with coordinates in a linearly ordered type `ι`,
its Plücker coordinates are its maximal minors: for each `p`-element subset `s` of `ι`, the
determinant of the `p × p` matrix whose rows are the vectors `x i` restricted to the coordinates
in `s`, listed in increasing order. The subsets are indexed by Mathlib's `Set.powersetCard ι p`,
the index type of the induced basis of the exterior power.

The coordinates are those of the exterior product `x 0 ∧ ⋯ ∧ x (p - 1)` in the basis of
`⋀[R]^p (ι → R)` induced by the standard basis. Consequently a change of the family by a square
matrix multiplies all coordinates by its determinant, and over an integral domain they vanish
identically exactly when the family is linearly dependent. Plücker coordinates give the point in
projective space attached to a subspace of `K^ι`, and heights of subspaces are heights of these
points.

The Cauchy–Binet formula expresses the determinant of the `p × p` product of two such families
as the sum of products of their Plücker coordinates. Over a commutative star ring, for instance
`ℂ`, applying it to a family and its conjugate writes the Hermitian Gram determinant of the
family as the sum of the squared absolute values of its Plücker coordinates.

Over a field, the Plücker coordinates of complementary orthogonal families are complementary
minors: if `x` and `y` are linearly independent families of `p` and `q` vectors with
`p + q = #ι`, and every `x i` has dot product zero with every `y j`, then, up to a common nonzero
factor and signs, the coordinate of `y` at a `q`-element subset `t` is the coordinate of `x` at
the complement of `t`. This is what makes the height of a subspace equal to the height of its
orthogonal complement.

The determinant identities hold over an arbitrary commutative ring. The comparison with linear
independence holds over an integral domain and the complementary minors over a field, while the
coprimality theorem for saturated submodules holds over a principal ideal domain with a normalized
gcd. The empty family has a single Plücker coordinate, equal to `1`, and a family of more than
`#ι` vectors has none.

## Main definitions

* `TauCeti.plucker x`: the Plücker coordinates of a family `x : Fin p → ι → R`.

## Main results

* `TauCeti.plucker_eq_repr_ιMulti`: the Plücker coordinates are the coordinates of
  `exteriorPower.ιMulti R p x` in the exterior-power basis induced by `Pi.basisFun R ι`.
* `TauCeti.plucker_sum_smul`: replacing the family by its product with a square matrix
  multiplies the Plücker coordinates by the determinant of that matrix.
* `TauCeti.det_mul_transpose_eq_sum_plucker_mul`: the Cauchy–Binet formula.
* `Matrix.det_mul_transpose_eq_sum_plucker_sq`: its Gram-determinant form for a matrix.
* `Matrix.det_mul_transpose_nonneg` and `Matrix.det_mul_transpose_pos_iff`: over a linearly
  ordered commutative ring, the Gram determinant of a matrix is nonnegative, and positive exactly
  when the rows are linearly independent.
* `TauCeti.det_mul_conjTranspose_eq_sum_plucker_mul_star`: its Hermitian form.
* `TauCeti.plucker_ne_zero_iff`: over an integral domain, the Plücker coordinates of a family are
  not all zero exactly when the family is linearly independent.
* `TauCeti.exists_plucker_eq_mul_plucker_compl_or_eq_neg`: the Plücker coordinates of
  complementary orthogonal families are complementary minors, up to a common nonzero factor and
  signs.
* `TauCeti.gcd_plucker_eq_one`: the Plücker coordinates of a basis of a saturated submodule of
  `R^ι` over a principal ideal domain are coprime.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §2.8.
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace
  Theorem*, Ann. of Math. 177 (2013), §6.1, (6.13).

The proofs use Mathlib's exterior-power basis `Module.Basis.exteriorPower` and its coordinate
formula `exteriorPower.ιMultiDual_apply_ιMulti`, by Sophie Morel and Daniel Morrison. The
statement of `TauCeti.gcd_plucker_eq_one` is adapted from Ralf Stephan's
`Submodule.gcd_plucker_eq_one` in `ArithmeticHeights/RationalLattice.lean` of
[`rwst/Subspace-Theorems`](https://github.com/rwst/Subspace-Theorems/blob/9894a1c4baf805296b249e95575f0e16e8e1afa3/ArithmeticHeights/RationalLattice.lean),
commit `9894a1c4baf805296b249e95575f0e16e8e1afa3` (Apache 2.0); the proof here instead uses a
projection onto the saturated submodule and the Cauchy–Binet formula, so it works over any
principal ideal domain with a normalized gcd.
-/

public section

open Set Set.powersetCard exteriorPower

open scoped Matrix

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

/-- A maximal minor on any enumeration of its columns is the Plücker coordinate on its sorted
range, multiplied by a permutation sign. -/
theorem _root_.Matrix.exists_det_submatrix_eq_sign_mul_plucker (A : Matrix (Fin p) ι R)
    (e : Fin p ↪ ι) :
    ∃ σ : Equiv.Perm (Fin p), (A.submatrix id e).det =
      (σ.sign : R) * plucker A.row (ofFinEmb p ι e) := by
  set s := ofFinEmb p ι e
  set t := ofFinEmbEquiv.symm s
  have hrange : Set.range t = Set.range e := Set.ext fun i ↦ by
    rw [mem_range_ofFinEmbEquiv_symm_iff_mem, mem_ofFinEmb_iff_mem_range]
  let σ : Equiv.Perm (Fin p) := (Equiv.ofInjective e e.injective).trans
    ((Set.equivOfEq hrange.symm).trans (Equiv.ofInjective t t.injective).symm)
  have he : A.submatrix id e = (A.submatrix id t).submatrix id σ := by
    ext i j
    simp [σ, Equiv.apply_ofInjective_symm]
  have hp : (A.submatrix id t).det = plucker A.row s :=
    (plucker_apply A.row s).symm
  exact ⟨σ, by rw [he, Matrix.det_permute', hp]⟩

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

/-- The maximal minors of a matrix with a ring homomorphism applied to all entries are the
images of the maximal minors of the matrix. -/
theorem _root_.Matrix.plucker_row_map (f : R →+* S) (A : Matrix (Fin p) ι R) :
    plucker (A.map f).row = f ∘ plucker A.row := by
  have h : (A.map f).row = fun i k ↦ f (A.row i k) := by
    ext i k
    simp
  ext s
  rw [h, plucker_map, Function.comp_apply]

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

/-- **The Cauchy–Binet formula for a Gram determinant.** The determinant of `A Aᵀ` is the sum of
the squares of the maximal minors of `A`, the Plücker coordinates of its rows. -/
theorem _root_.Matrix.det_mul_transpose_eq_sum_plucker_sq [Fintype ι] (A : Matrix (Fin p) ι R) :
    (A * A.transpose).det = ∑ s, plucker A.row s ^ 2 := by
  simpa [sq, Matrix.row_eq_self] using det_mul_transpose_eq_sum_plucker_mul A.row A.row

/-- Over a linearly ordered commutative ring, the Gram determinant `det (A * Aᵀ)` of the rows of a
matrix is nonnegative: by the Cauchy–Binet formula it is a sum of squares. -/
theorem _root_.Matrix.det_mul_transpose_nonneg {R m n : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] [Fintype m] [DecidableEq m] [Fintype n] (A : Matrix m n R) :
    0 ≤ (A * A.transpose).det := by
  -- Reindex the rows and columns by `Fin`, where the Cauchy–Binet formula applies.
  set e := Fintype.equivFin m
  set f := Fintype.equivFin n
  set B := A.submatrix e.symm f.symm
  have h : A * A.transpose = (B * B.transpose).submatrix e e := by
    simp [B, Matrix.transpose_submatrix]
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_mul_transpose_eq_sum_plucker_sq]
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Over a linearly ordered commutative ring, the Gram determinant `det (A * Aᵀ)` of the rows of a
matrix is positive exactly when the rows are linearly independent. -/
theorem _root_.Matrix.det_mul_transpose_pos_iff {R m n : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] [Fintype m] [DecidableEq m] [Fintype n] {A : Matrix m n R} :
    0 < (A * A.transpose).det ↔ LinearIndependent R A.row := by
  rw [← Matrix.det_mul_transpose_ne_zero_iff, (Matrix.det_mul_transpose_nonneg A).lt_iff_ne',
    ne_eq]

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

/-- Over an integral domain, the Plücker coordinates of a family are not all zero exactly when
it is linearly independent. -/
theorem plucker_ne_zero_iff [IsDomain R] [Finite ι] (x : Fin p → ι → R) :
    plucker x ≠ 0 ↔ LinearIndependent R x := by
  classical
  constructor
  · intro h
    obtain ⟨s, hs⟩ := Function.ne_iff.1 h
    exact (Matrix.linearIndependent_row_iff_exists_det_submatrix_ne_zero
      (A := Matrix.of x)).2 ⟨(ofFinEmbEquiv.symm s).toEmbedding, hs⟩
  · intro hx
    obtain ⟨e, he⟩ := (Matrix.linearIndependent_row_iff_exists_det_submatrix_ne_zero
      (A := Matrix.of x)).1 hx
    obtain ⟨σ, hσ⟩ := (Matrix.of x).exists_det_submatrix_eq_sign_mul_plucker e
    refine Function.ne_iff.2 ⟨ofFinEmb p ι e, ?_⟩
    intro h
    exact he (by simp [hσ, h])

section Field

variable {K : Type*} [Field K]

/-! ### Complementary minors -/

variable [Fintype ι] {q : ℕ}

/-- The Plücker coordinate of `y` at `t` is the determinant of the pairings of `y` with the
standard basis vectors at the elements of `t`. -/
private theorem plucker_eq_det_mul_transpose_single (y : Fin q → ι → K) (t : powersetCard ι q) :
    plucker y t = (Matrix.of y *
      (Matrix.of fun j ↦ Pi.single (ofFinEmbEquiv.symm t j) (1 : K)).transpose).det := by
  rw [plucker_apply]
  congr 1
  ext i j
  simp [Matrix.mul_apply, Pi.single_apply]

/-- Against any identification `e` of the index types, the determinant of `x` followed by the
standard basis vectors at the elements of `t` is, up to sign, the Plücker coordinate of `x` at the
complement of `t`. -/
private theorem exists_det_sumElim_single_eq (hm : p + q = Fintype.card ι)
    (e : Fin p ⊕ Fin q ≃ ι) (x : Fin p → ι → K) (t : powersetCard ι q) :
    ∃ ε : ℤˣ, (Matrix.of fun a b ↦
        Sum.elim x (fun j ↦ Pi.single (ofFinEmbEquiv.symm t j) (1 : K)) a (e b)).det =
      ((ε : ℤ) : K) * plucker x (compl hm t) := by
  set f := ofFinEmbEquiv.symm (compl hm t)
  set g := ofFinEmbEquiv.symm t
  have hfg : ∀ i j, f i ≠ g j := fun i j h ↦ by
    have h₁ := (mem_range_ofFinEmbEquiv_symm_iff_mem (compl hm t) (f i)).1 ⟨i, rfl⟩
    have h₂ := (mem_range_ofFinEmbEquiv_symm_iff_mem t (g j)).1 ⟨j, rfl⟩
    exact mem_compl.1 h₁ (h ▸ h₂)
  have hσ : Function.Bijective (Sum.elim f g) :=
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨f.injective.sumElim g.injective hfg, by simp [hm]⟩
  set σ := Equiv.ofBijective _ hσ
  -- Listing the columns as the complement of `t` followed by `t` gives a block triangular matrix.
  have hN : (Matrix.of fun a b ↦ Sum.elim x (fun j ↦ Pi.single (g j) (1 : K)) a (σ b)) =
      Matrix.fromBlocks (Matrix.of fun i j ↦ x i (f j)) (Matrix.of fun i j ↦ x i (g j)) 0 1 := by
    ext a b
    rcases a with i | j <;> rcases b with i' | j'
    · simp [σ]
    · simp [σ]
    · simp [σ, (hfg i' j).symm]
    · simp [σ, Pi.single_apply, Matrix.one_apply, g.injective.eq_iff, eq_comm]
  refine ⟨Equiv.Perm.sign (e.trans σ.symm), ?_⟩
  have h : (Matrix.of fun a b ↦ Sum.elim x (fun j ↦ Pi.single (g j) (1 : K)) a (e b)) =
      (Matrix.of fun a b ↦ Sum.elim x (fun j ↦ Pi.single (g j) (1 : K)) a (σ b)).submatrix id
        (e.trans σ.symm) := by
    ext a b
    simp
  rw [h, Matrix.det_permute', hN, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
    plucker_apply]

/-- **Complementary minors.** Let `x` and `y` be linearly independent families of `p` and `q`
vectors in `K^ι`, with `p + q = #ι`, such that every `x i` has dot product zero with every `y j`;
so `y` is a basis of the orthogonal complement of the span of `x`. Then, up to a common nonzero
factor `c` and signs, the Plücker coordinate of `y` at a `q`-element subset `t` of `ι` is the
Plücker coordinate of `x` at the complement of `t`. -/
theorem exists_plucker_eq_mul_plucker_compl_or_eq_neg (hm : p + q = Fintype.card ι)
    {x : Fin p → ι → K} {y : Fin q → ι → K} (hx : LinearIndependent K x)
    (hy : LinearIndependent K y) (hxy : ∀ i j, x i ⬝ᵥ y j = 0) :
    ∃ c : K, c ≠ 0 ∧ ∀ t : powersetCard ι q,
      plucker y t = c * plucker x (compl hm t) ∨ plucker y t = -(c * plucker x (compl hm t)) := by
  have hsurj : Function.Surjective (Matrix.of y).mulVec := hy.mulVec_surjective
  choose w hw using fun j ↦ hsurj (Pi.single j 1)
  -- The vectors orthogonal to every `y j` are the span of `x`, by counting dimensions.
  have hker : LinearMap.ker (Matrix.of y).mulVecLin ≤ Submodule.span K (range x) := by
    have hle : Submodule.span K (range x) ≤ LinearMap.ker (Matrix.of y).mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      ext j
      simp [Matrix.mulVec, dotProduct_comm, hxy]
    refine (Submodule.eq_of_le_of_finrank_eq hle ?_).ge
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.of y).mulVecLin
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fin_fun,
      Module.finrank_fintype_fun_eq_card] at h
    rw [finrank_span_eq_card hx, Fintype.card_fin]
    omega
  obtain ⟨e⟩ : Nonempty (Fin p ⊕ Fin q ≃ ι) := ⟨Fintype.equivOfCardEq (by simp [hm])⟩
  set D := (Matrix.of fun a b ↦ Sum.elim x w a (e b)).det
  have key : ∀ t, ∃ ε : ℤˣ, plucker y t * D = ((ε : ℤ) : K) * plucker x (compl hm t) := by
    intro t
    obtain ⟨ε, hε⟩ := exists_det_sumElim_single_eq hm e x t
    exact ⟨ε, by
      rw [plucker_eq_det_mul_transpose_single, ← Matrix.det_sumElim_eq_det_mul e hker hw, hε]⟩
  -- Some Plücker coordinate of `x` is nonzero, so `D` is nonzero.
  have hD : D ≠ 0 := by
    obtain ⟨s, hs⟩ : ∃ s, plucker x s ≠ 0 := Function.ne_iff.1 ((plucker_ne_zero_iff x).2 hx)
    obtain ⟨ε, hε⟩ := key ((compl hm).symm s)
    rw [Equiv.apply_symm_apply] at hε
    rintro h
    rw [h, mul_zero, eq_comm, mul_eq_zero] at hε
    exact hε.elim (by rcases Int.units_eq_one_or ε with rfl | rfl <;> simp) hs
  refine ⟨D⁻¹, inv_ne_zero hD, fun t ↦ ?_⟩
  obtain ⟨ε, hε⟩ := key t
  rw [← eq_mul_inv_iff_mul_eq₀ hD] at hε
  rcases Int.units_eq_one_or ε with rfl | rfl
  · left
    rw [hε]
    simp [mul_comm]
  · right
    rw [hε]
    simp [mul_comm]

end Field

/-- **The Plücker coordinates of a saturated basis over a PID are coprime.** Let `N` be a
saturated submodule of `R^ι`: it contains every `z` of which it contains a nonzero multiple. Then
the Plücker coordinates of any basis of `N` have normalized greatest common divisor `1`. -/
theorem gcd_plucker_eq_one [IsDomain R] [IsPrincipalIdealRing R] [NormalizedGCDMonoid R]
    [Fintype ι] {N : Submodule R (ι → R)}
    (hN : ∀ (c : R) (z : ι → R), c ≠ 0 → c • z ∈ N → z ∈ N) (b : Module.Basis (Fin p) R N) :
    Finset.univ.gcd (plucker fun i ↦ (b i : ι → R)) = 1 := by
  classical
  -- Saturation makes the finitely generated quotient torsion-free, hence free over the PID.
  have : Module.IsTorsionFree R ((ι → R) ⧸ N) := N.isTorsionFree_quotient_of_smul_mem hN
  obtain ⟨P, hP⟩ := N.exists_isCompl_iff_isTorsionFree_quotient.mpr inferInstance
  let π := b.repr.toLinearMap ∘ₗ N.projectionOnto P hP
  let y : Fin p → ι → R := fun i j ↦ π (Pi.single j 1) i
  have hπ (v : ι → R) (i : Fin p) : π v i = ∑ j, v j * y i j := by
    conv_lhs => rw [← (Pi.basisFun R ι).sum_repr v]
    simp [y]
  -- The projected basis coordinates give a right inverse to the matrix of basis vectors.
  have hxy : Matrix.of (fun i ↦ (b i : ι → R)) * (Matrix.of y).transpose = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    simpa [π, Matrix.one_apply, Finsupp.single_apply, eq_comm] using (hπ (b i) j).symm
  -- Cauchy–Binet expresses 1 as a linear combination of the maximal minors.
  have hdvd : Finset.univ.gcd (plucker fun i ↦ (b i : ι → R)) ∣ (1 : R) := by
    rw [← Matrix.det_one (n := Fin p), ← hxy, det_mul_transpose_eq_sum_plucker_mul]
    exact Finset.dvd_sum fun s hs ↦ dvd_mul_of_dvd_left (Finset.gcd_dvd hs) _
  simpa only [Finset.normalize_gcd] using normalize_eq_one.mpr (isUnit_of_dvd_one hdvd)

end TauCeti
