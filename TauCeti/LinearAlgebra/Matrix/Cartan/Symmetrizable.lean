/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

import Mathlib.Tactic

/-!
# Symmetrizable generalized Cartan matrices

A *generalized Cartan matrix* on an index type `I` is an integral matrix `A = (a i j)` with
`a i i = 2`, `a i j ≤ 0` for `i ≠ j`, and `a i j = 0 ↔ a j i = 0`. We use the row convention
`a i j = α_j(h_i)`: rows are indexed by simple coroots and columns by simple roots. A
*symmetrizer* is a family of positive integers `d i` with `d i * a i j = d j * a j i`, so that
the *symmetrized matrix* `B = (d i * a i j)` is symmetric and `A = D⁻¹ B` for `D = diag(d i)`.
A symmetrizable generalized Cartan matrix together with a chosen symmetrizer is the input datum
of a symmetrizable Kac–Moody algebra and of its Drinfeld–Jimbo quantization, where the
symmetrizer fixes the parameters `q_i = q ^ d i`.

Borcherds matrices, whose diagonal entries may be nonpositive, are different data: they are not
obtained by allowing `d i = 0`, which the positivity of the symmetrizer excludes.

## Main definitions

* `TauCeti.SymmetrizableDatum I`: a generalized Cartan matrix on `I` with a symmetrizer.
* `TauCeti.SymmetrizableDatum.symmetrizedMatrix`: the symmetric matrix `(d i * a i j)`.
* `TauCeti.SymmetrizableDatum.restrict`: restriction along an embedding `J ↪ I`; for the
  inclusion of a subset this is the Levi datum.
* `TauCeti.SymmetrizableDatum.reindex`: transport along a bijection `I ≃ I'`.
* `TauCeti.SymmetrizableDatum.sum`: the direct sum of two data, on `I ⊕ J`.
* `TauCeti.SymmetrizableDatum.normalizeSymmetrizer`: the same matrix with the symmetrizer
  divided by the greatest common divisor of its entries.
* `Matrix.IsFiniteCartan.toSymmetrizableDatum`: a finite-type Cartan matrix with a symmetrizer
  extracted from its positive-definite symmetrization.

## Main results

* `TauCeti.SymmetrizableDatum.isSymm_symmetrizedMatrix`: the symmetrized matrix is symmetric.
* `TauCeti.SymmetrizableDatum.cartan_map_eq_diagonal_inv_mul`: `A = D⁻¹ B` over any division
  ring of characteristic zero.
* `TauCeti.SymmetrizableDatum.mul_symmetrizer_eq_mul_symmetrizer_of_isIndecomposable`: for an
  indecomposable matrix, every solution `x` of the symmetrizing equations
  `x i * a i j = x j * a j i`, with values in a characteristic-zero domain, is proportional to
  the symmetrizer.
* `TauCeti.SymmetrizableDatum.exists_pos_symmetrizer_eq_mul_of_isIndecomposable`: two
  symmetrizers of an indecomposable matrix differ by a positive rational factor.
* `TauCeti.SymmetrizableDatum.normalizeSymmetrizer_eq_of_isIndecomposable`: an
  indecomposable matrix has a unique symmetrizer with coprime entries, and every symmetrizer is
  a positive integer multiple of it (`symmetrizer_eq_gcd_mul_normalizeSymmetrizer`).

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press,
  1990, §1.1 and §2.1.
-/

public section

open Matrix

namespace TauCeti

/-- A symmetrizable generalized Cartan matrix on the index type `I`, with a chosen symmetrizer.

The matrix `cartan` has diagonal entries `2`, nonpositive off-diagonal entries, and vanishing
entries in symmetric positions, with the row convention `cartan i j = α_j(h_i)`. The symmetrizer
consists of positive integers `d i` with `d i * cartan i j = d j * cartan j i`. -/
@[ext]
structure SymmetrizableDatum (I : Type*) where
  /-- The generalized Cartan matrix, with `cartan i j = α_j(h_i)`. -/
  cartan : Matrix I I ℤ
  /-- The diagonal entries of the generalized Cartan matrix are `2`. -/
  diag : ∀ i, cartan i i = 2
  /-- The off-diagonal entries of the generalized Cartan matrix are nonpositive. -/
  offDiag_nonpos : ∀ i j, i ≠ j → cartan i j ≤ 0
  /-- An entry vanishes exactly when the entry in the transposed position does. -/
  zero_comm : ∀ i j, cartan i j = 0 ↔ cartan j i = 0
  /-- The symmetrizer `d i`. -/
  symmetrizer : I → ℕ
  /-- The symmetrizer is positive. -/
  symmetrizer_pos : ∀ i, 0 < symmetrizer i
  /-- The symmetrizer symmetrizes the matrix: `d i * a i j = d j * a j i`. -/
  symmetrizes : ∀ i j, (symmetrizer i : ℤ) * cartan i j = symmetrizer j * cartan j i

namespace SymmetrizableDatum

variable {I J K I' I'' : Type*} (A : SymmetrizableDatum I)

/-- The symmetrizer is nonzero. -/
theorem symmetrizer_ne_zero (i : I) : A.symmetrizer i ≠ 0 :=
  (A.symmetrizer_pos i).ne'

/-! ### The symmetrized matrix -/

/-- The symmetrized matrix `B = (d i * a i j)` of a symmetrizable datum. -/
def symmetrizedMatrix : Matrix I I ℤ :=
  Matrix.of fun i j => (A.symmetrizer i : ℤ) * A.cartan i j

@[simp]
theorem symmetrizedMatrix_apply (i j : I) :
    A.symmetrizedMatrix i j = A.symmetrizer i * A.cartan i j :=
  (rfl)

/-- The diagonal entries of the symmetrized matrix are `2 * d i`. -/
theorem symmetrizedMatrix_apply_self (i : I) :
    A.symmetrizedMatrix i i = 2 * A.symmetrizer i := by
  rw [symmetrizedMatrix_apply, A.diag, mul_comm]

/-- The symmetrized matrix is symmetric. -/
theorem isSymm_symmetrizedMatrix : A.symmetrizedMatrix.IsSymm :=
  IsSymm.ext fun i j => by simp only [symmetrizedMatrix_apply, A.symmetrizes j i]

/-- The symmetrized matrix is `D * A` for the diagonal matrix `D = diag(d i)`. -/
theorem symmetrizedMatrix_eq_diagonal_mul [Fintype I] [DecidableEq I] :
    A.symmetrizedMatrix = diagonal (fun i => (A.symmetrizer i : ℤ)) * A.cartan := by
  ext i j
  simp

/-- Over a division ring of characteristic zero, the generalized Cartan matrix is `D⁻¹ * B`,
for `D = diag(d i)` and `B` the symmetrized matrix. -/
theorem cartan_map_eq_diagonal_inv_mul [Fintype I] [DecidableEq I] {R : Type*}
    [DivisionRing R] [CharZero R] :
    A.cartan.map (Int.cast : ℤ → R) =
      diagonal (fun i => ((A.symmetrizer i : R))⁻¹) * A.symmetrizedMatrix.map Int.cast := by
  ext i j
  have hd : (A.symmetrizer i : R) ≠ 0 := Nat.cast_ne_zero.mpr (A.symmetrizer_ne_zero i)
  simp [hd]

/-! ### Restriction, reindexing and direct sums -/

/-- The restriction of a datum along an embedding `f : J ↪ I`: the matrix `a (f i) (f j)` with
the symmetrizer `d (f i)`. For the inclusion of a subset `J ⊆ I` this is the Levi datum of
`J`. -/
def restrict (f : J ↪ I) : SymmetrizableDatum J where
  cartan := A.cartan.submatrix f f
  diag i := A.diag (f i)
  offDiag_nonpos i j hij := A.offDiag_nonpos (f i) (f j) (f.injective.ne hij)
  zero_comm i j := A.zero_comm (f i) (f j)
  symmetrizer := A.symmetrizer ∘ f
  symmetrizer_pos i := A.symmetrizer_pos (f i)
  symmetrizes i j := A.symmetrizes (f i) (f j)

@[simp]
theorem restrict_cartan (f : J ↪ I) : (A.restrict f).cartan = A.cartan.submatrix f f :=
  (rfl)

@[simp]
theorem restrict_symmetrizer (f : J ↪ I) : (A.restrict f).symmetrizer = A.symmetrizer ∘ f :=
  (rfl)

/-- Restriction commutes with symmetrization. -/
@[simp]
theorem symmetrizedMatrix_restrict (f : J ↪ I) :
    (A.restrict f).symmetrizedMatrix = A.symmetrizedMatrix.submatrix f f := by
  ext i j
  simp

@[simp]
theorem restrict_refl : A.restrict (Function.Embedding.refl I) = A := by
  ext <;> simp

@[simp]
theorem restrict_restrict (f : J ↪ I) (g : K ↪ J) :
    (A.restrict f).restrict g = A.restrict (g.trans f) := by
  ext <;> simp

/-- The transport of a datum along a bijection `e : I ≃ I'` of index types. -/
def reindex (e : I ≃ I') : SymmetrizableDatum I' :=
  A.restrict e.symm.toEmbedding

@[simp]
theorem reindex_cartan (e : I ≃ I') : (A.reindex e).cartan = A.cartan.reindex e e := by
  ext i j
  simp [reindex]

@[simp]
theorem reindex_symmetrizer (e : I ≃ I') :
    (A.reindex e).symmetrizer = A.symmetrizer ∘ e.symm :=
  (rfl)

/-- Reindexing commutes with symmetrization. -/
@[simp]
theorem symmetrizedMatrix_reindex (e : I ≃ I') :
    (A.reindex e).symmetrizedMatrix = A.symmetrizedMatrix.reindex e e := by
  ext i j
  simp

@[simp]
theorem reindex_refl : A.reindex (Equiv.refl I) = A := by
  ext <;> simp

@[simp]
theorem reindex_reindex (e : I ≃ I') (e' : I' ≃ I'') :
    (A.reindex e).reindex e' = A.reindex (e.trans e') := by
  ext <;> simp

/-- The direct sum of two data on the disjoint union `I ⊕ J` of the index types: the
block-diagonal matrix of the two matrices, with the two symmetrizers side by side. -/
def sum (A' : SymmetrizableDatum J) : SymmetrizableDatum (I ⊕ J) where
  cartan := fromBlocks A.cartan 0 0 A'.cartan
  diag := by rintro (i | i) <;> simp [A.diag, A'.diag]
  offDiag_nonpos := by
    rintro (i | i) (j | j) hij
    · simpa using A.offDiag_nonpos i j fun h => hij (congrArg Sum.inl h)
    · simp
    · simp
    · simpa using A'.offDiag_nonpos i j fun h => hij (congrArg Sum.inr h)
  zero_comm := by rintro (i | i) (j | j) <;> simp [A.zero_comm, A'.zero_comm]
  symmetrizer := Sum.elim A.symmetrizer A'.symmetrizer
  symmetrizer_pos := by rintro (i | i) <;> simp [A.symmetrizer_pos, A'.symmetrizer_pos]
  symmetrizes := by rintro (i | i) (j | j) <;> simp [A.symmetrizes, A'.symmetrizes]

variable (A' : SymmetrizableDatum J)

@[simp]
theorem sum_cartan : (A.sum A').cartan = fromBlocks A.cartan 0 0 A'.cartan :=
  (rfl)

@[simp]
theorem sum_symmetrizer : (A.sum A').symmetrizer = Sum.elim A.symmetrizer A'.symmetrizer :=
  (rfl)

/-- The direct sum commutes with symmetrization. -/
@[simp]
theorem symmetrizedMatrix_sum :
    (A.sum A').symmetrizedMatrix = fromBlocks A.symmetrizedMatrix 0 0 A'.symmetrizedMatrix := by
  ext (i | i) (j | j) <;> simp

/-- Restricting a direct sum to the first summand recovers the first datum. -/
@[simp]
theorem sum_restrict_inl : (A.sum A').restrict Function.Embedding.inl = A := by
  ext <;> simp

/-- Restricting a direct sum to the second summand recovers the second datum. -/
@[simp]
theorem sum_restrict_inr : (A.sum A').restrict Function.Embedding.inr = A' := by
  ext <;> simp

/-! ### Uniqueness of the symmetrizer of an indecomposable matrix -/

/-- If `a i j ≠ 0`, the symmetrizing equations force `x i * d j = x j * d i`. -/
private theorem mul_symmetrizer_eq_of_cartan_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] {x : I → R} (hx : ∀ i j, x i * A.cartan i j = x j * A.cartan j i) {i j : I}
    (hij : A.cartan i j ≠ 0) :
    x i * A.symmetrizer j = x j * A.symmetrizer i := by
  have hji : (A.cartan j i : R) ≠ 0 := Int.cast_ne_zero.mpr ((A.zero_comm i j).not.mp hij)
  have hd : (A.symmetrizer i : R) * A.cartan i j = A.symmetrizer j * A.cartan j i := by
    exact_mod_cast A.symmetrizes i j
  apply mul_right_cancel₀ hji
  linear_combination (A.symmetrizer i : R) * hx i j - x i * hd

/-- For an indecomposable generalized Cartan matrix, every solution `x` of the symmetrizing
equations `x i * a i j = x j * a j i`, with values in a domain of characteristic zero, is
proportional to the symmetrizer: `x i * d j = x j * d i` for all `i` and `j`. -/
theorem mul_symmetrizer_eq_mul_symmetrizer_of_isIndecomposable [Finite I] {R : Type*}
    [CommRing R] [IsDomain R] [CharZero R] (hA : A.cartan.IsIndecomposable) {x : I → R}
    (hx : ∀ i j, x i * A.cartan i j = x j * A.cartan j i) (i j : I) :
    x i * A.symmetrizer j = x j * A.symmetrizer i := by
  -- Propagate the relation from `i` along a chain of nonzero entries reaching `j`.
  induction (isIndecomposable_iff_reflTransGen _).mp hA i j with
  | refl => rfl
  | @tail k l _ hkl ih =>
    have hkl' := A.mul_symmetrizer_eq_of_cartan_ne_zero hx hkl
    have hk : (A.symmetrizer k : R) ≠ 0 := Nat.cast_ne_zero.mpr (A.symmetrizer_ne_zero k)
    apply mul_left_cancel₀ hk
    linear_combination (A.symmetrizer l : R) * ih + (A.symmetrizer i : R) * hkl'

/-- Two symmetrizers of an indecomposable generalized Cartan matrix differ by a positive
rational factor. -/
theorem exists_pos_symmetrizer_eq_mul_of_isIndecomposable [Finite I]
    (hA : A.cartan.IsIndecomposable) {A' : SymmetrizableDatum I} (h : A'.cartan = A.cartan) :
    ∃ c : ℚ, 0 < c ∧ ∀ i, (A'.symmetrizer i : ℚ) = c * A.symmetrizer i := by
  rcases isEmpty_or_nonempty I with hI | ⟨⟨i₀⟩⟩
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  have hd₀ : (0 : ℚ) < A.symmetrizer i₀ := Nat.cast_pos.mpr (A.symmetrizer_pos i₀)
  have hd₀' : (0 : ℚ) < A'.symmetrizer i₀ := Nat.cast_pos.mpr (A'.symmetrizer_pos i₀)
  refine ⟨A'.symmetrizer i₀ / A.symmetrizer i₀, div_pos hd₀' hd₀, fun i => ?_⟩
  have hx : ∀ i j, (A'.symmetrizer i : ℚ) * A.cartan i j = A'.symmetrizer j * A.cartan j i := by
    intro i j
    rw [← h]
    exact_mod_cast A'.symmetrizes i j
  have key := A.mul_symmetrizer_eq_mul_symmetrizer_of_isIndecomposable hA hx i₀ i
  rw [div_mul_eq_mul_div, eq_div_iff hd₀.ne']
  linear_combination -key

/-! ### The normalized symmetrizer -/

variable [Fintype I]

/-- The datum with the same generalized Cartan matrix and the symmetrizer divided by the
greatest common divisor of its entries. -/
def normalizeSymmetrizer : SymmetrizableDatum I where
  cartan := A.cartan
  diag := A.diag
  offDiag_nonpos := A.offDiag_nonpos
  zero_comm := A.zero_comm
  symmetrizer i := A.symmetrizer i / Finset.univ.gcd A.symmetrizer
  symmetrizer_pos i := by
    have hdvd := Finset.gcd_dvd (f := A.symmetrizer) (Finset.mem_univ i)
    exact Nat.div_pos (Nat.le_of_dvd (A.symmetrizer_pos i) hdvd)
      (Nat.pos_of_dvd_of_pos hdvd (A.symmetrizer_pos i))
  symmetrizes i j := by
    obtain ⟨a, ha⟩ := Finset.gcd_dvd (f := A.symmetrizer) (Finset.mem_univ i)
    obtain ⟨b, hb⟩ := Finset.gcd_dvd (f := A.symmetrizer) (Finset.mem_univ j)
    have hg : Finset.univ.gcd A.symmetrizer ≠ 0 := fun h0 => A.symmetrizer_ne_zero i <| by
      rw [ha, h0, zero_mul]
    have hs := A.symmetrizes i j
    rw [ha, hb, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hg),
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hg)]
    rw [ha, hb] at hs
    push_cast at hs
    exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hg) (by linear_combination hs)

@[simp]
theorem normalizeSymmetrizer_cartan : A.normalizeSymmetrizer.cartan = A.cartan :=
  (rfl)

@[simp]
theorem normalizeSymmetrizer_symmetrizer (i : I) :
    A.normalizeSymmetrizer.symmetrizer i = A.symmetrizer i / Finset.univ.gcd A.symmetrizer :=
  (rfl)

/-- Every symmetrizer is the greatest common divisor of its entries times the normalized
symmetrizer. -/
theorem symmetrizer_eq_gcd_mul_normalizeSymmetrizer (i : I) :
    A.symmetrizer i = Finset.univ.gcd A.symmetrizer * A.normalizeSymmetrizer.symmetrizer i :=
  (Nat.mul_div_cancel' (Finset.gcd_dvd (Finset.mem_univ i))).symm

/-- The entries of the normalized symmetrizer are coprime. -/
theorem gcd_normalizeSymmetrizer_symmetrizer [Nonempty I] :
    Finset.univ.gcd A.normalizeSymmetrizer.symmetrizer = 1 := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  rw [Finset.gcd_congr rfl fun i _ => A.normalizeSymmetrizer_symmetrizer i]
  exact Finset.gcd_div_eq_one (Finset.mem_univ i₀) (A.symmetrizer_ne_zero i₀)

/-- An indecomposable generalized Cartan matrix has a unique symmetrizer with coprime entries:
any two symmetrizers have the same normalization. -/
theorem normalizeSymmetrizer_eq_of_isIndecomposable (hA : A.cartan.IsIndecomposable)
    {A' : SymmetrizableDatum I} (h : A'.cartan = A.cartan) :
    A'.normalizeSymmetrizer = A.normalizeSymmetrizer := by
  rcases isEmpty_or_nonempty I with hI | hI
  · ext i j
    · simp [h]
    · exact isEmptyElim i
  set p := A.normalizeSymmetrizer.symmetrizer
  set p' := A'.normalizeSymmetrizer.symmetrizer
  have hx : ∀ i j, (p' i : ℤ) * A.normalizeSymmetrizer.cartan i j =
      p' j * A.normalizeSymmetrizer.cartan j i := by
    intro i j
    rw [normalizeSymmetrizer_cartan, ← h, ← normalizeSymmetrizer_cartan]
    exact A'.normalizeSymmetrizer.symmetrizes i j
  have key (i j : I) : p' i * p j = p' j * p i := by
    exact_mod_cast A.normalizeSymmetrizer.mul_symmetrizer_eq_mul_symmetrizer_of_isIndecomposable
      hA hx i j
  ext j : 2
  · simp [h]
  -- Take the greatest common divisor over `i` of both sides of `p' i * p j = p' j * p i`.
  calc p' j = p' j * Finset.univ.gcd p := by
        rw [A.gcd_normalizeSymmetrizer_symmetrizer, mul_one]
    _ = Finset.univ.gcd fun i => p' j * p i := by rw [Finset.gcd_mul_left, normalize_eq]
    _ = Finset.univ.gcd fun i => p' i * p j := Finset.gcd_congr rfl fun i _ => (key i j).symm
    _ = Finset.univ.gcd p' * p j := by rw [Finset.gcd_mul_right, normalize_eq]
    _ = p j := by rw [A'.gcd_normalizeSymmetrizer_symmetrizer, one_mul]

end SymmetrizableDatum

end TauCeti

namespace Matrix.IsFiniteCartan

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℤ}

/-- A finite-type Cartan matrix as a symmetrizable datum, with the symmetrizer chosen from the
positive diagonal matrix `D` for which `D * M` is positive definite. -/
noncomputable def toSymmetrizableDatum (hM : M.IsFiniteCartan) : TauCeti.SymmetrizableDatum ι where
  cartan := M
  diag := hM.diag
  offDiag_nonpos := hM.offDiag_nonpos
  zero_comm := hM.zero_comm
  symmetrizer i := (hM.exists_posDef.choose i).toNat
  symmetrizer_pos i := Int.pos_iff_toNat_pos.mp (hM.exists_posDef.choose_spec.1 i)
  symmetrizes i j := by
    obtain ⟨hpos, hdef⟩ := hM.exists_posDef.choose_spec
    rw [Int.toNat_of_nonneg (hpos i).le, Int.toNat_of_nonneg (hpos j).le]
    simpa using hdef.isHermitian.apply j i

@[simp]
theorem toSymmetrizableDatum_cartan (hM : M.IsFiniteCartan) :
    hM.toSymmetrizableDatum.cartan = M :=
  (rfl)

end Matrix.IsFiniteCartan

/-! ### Examples -/

/-- The symmetrizer `(1, 2)` symmetrizes the Cartan matrix of type `B₂`, `[[2, -2], [-1, 2]]`. -/
example :
    ∀ i j : Fin 2, (![1, 2] i : ℤ) * CartanMatrix.B 2 i j = ![1, 2] j * CartanMatrix.B 2 j i := by
  decide

/-- The constant family `(1, 1)` does not symmetrize the Cartan matrix of type `B₂`. -/
example : ¬ ∀ i j : Fin 2, (1 : ℤ) * CartanMatrix.B 2 i j = 1 * CartanMatrix.B 2 j i := by
  decide

/-- The matrix `[[2, -1], [0, 2]]` violates the zero-symmetry axiom. -/
example :
    ¬ ∀ i j : Fin 2, ![![(2 : ℤ), -1], ![0, 2]] i j = 0 ↔ ![![(2 : ℤ), -1], ![0, 2]] j i = 0 := by
  decide
