/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import TauCeti.Algebra.Polynomial.Reverse
public import TauCeti.GroupTheory.Perm.Cycle.Power
public import TauCeti.GroupTheory.Perm.Partition
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse

/-!
# The characteristic polynomial of a permutation matrix

A permutation `σ` of a finite set `n` acts on the free module `R^n` by permuting the coordinates.
Its characteristic polynomial is determined by the cycle lengths of `σ`, fixed points included:

`charpoly (σ.permMatrix R) = ∏_{d ∈ σ.fullCycleType} (X ^ d - 1)`,

and dually the reversed characteristic polynomial `det (1 - X P_σ)` is `∏_d (1 - X ^ d)`. Here
`Equiv.Perm.fullCycleType` is the multiset of all cycle lengths, one part for each fixed point,
so repeated lengths contribute repeated factors.

The proof splits into two steps. A cycle of length `d` contributes `X ^ d - 1`: the permutation
matrix `P` of a permutation with a single orbit satisfies `P ^ d = 1`, while the basis vectors
`P ^ i e` for `i < d` are distinct, so no nonzero polynomial of degree less than `d` kills `P`; by
Cayley–Hamilton the monic degree-`d` characteristic polynomial is therefore `X ^ d - 1`. In
general, labelling the cycles makes the permutation matrix block triangular (indeed block
diagonal), with one diagonal block for each cycle, and the characteristic polynomial is the
product over the blocks.

Over a field `k` the reversed form is the polynomial identity read off from a Frobenius element
acting on a permutation representation: if `π` permutes the finite set `S`, the action of `π` on
`k[S]` has `det (1 - Z π) = ∏ (1 - Z ^ d)` over the cycle lengths `d`. That is the identity which
turns the factorization type of a prime in a Gassmann triple into an equality of local factors of
zeta functions. It is recorded here for the linear map `Finsupp.lmapDomain R R σ` on `n →₀ R`,
the permutation action on the standard basis; the version for the permutation representation
`Representation.ofMulAction` is `TauCeti.reverse_charpoly_ofMulAction`.

## Main results

* `Matrix.blockTriangular_permMatrix`, `Matrix.toSquareBlock_permMatrix`: a labelling of the
  coordinates that is constant along the cycles makes a permutation matrix block triangular, and
  its diagonal blocks are the permutation matrices of the restrictions.
* `Equiv.Perm.eq_zero_of_aeval_permMatrix_eq_zero`: if `σ` has a single orbit on `n`, no nonzero
  polynomial of degree less than `card n` kills its permutation matrix; together with
  `Equiv.Perm.pow_card_eq_one_of_forall_sameCycle` (`σ ^ card n = 1`) this pins down the
  characteristic polynomial of a single cycle.
* `Equiv.Perm.charpoly_permMatrix_of_forall_sameCycle`: a permutation with a single orbit on a
  nonempty set of size `d` has characteristic polynomial `X ^ d - 1`.
* `Equiv.Perm.charpoly_permMatrix`: the characteristic polynomial of a permutation matrix is the
  product of `X ^ d - 1` over the full cycle type.
* `Equiv.Perm.charpolyRev_permMatrix`: `det (1 - X P_σ)` is the product of `1 - X ^ d` over the
  full cycle type; the passage from the first product uses
  `Polynomial.reflect_sum_prod_X_pow_sub_one`.
* `Equiv.Perm.charpoly_lmapDomain`, `Equiv.Perm.reverse_charpoly_lmapDomain`: the same identities
  for the permutation action `Finsupp.lmapDomain R R σ` on `n →₀ R`, whose matrix in the standard
  basis is the transposed permutation matrix (`Equiv.Perm.toMatrix_lmapDomain`).

## References

* R. Perlis, *On the equation `ζ_K(s) = ζ_K'(s)`*, J. Number Theory **9** (1977), 342–360, where the
  local factors of the Dedekind zeta function are read off from cycle types in this way.
-/

public section

open Polynomial Matrix

namespace Matrix

variable {n R : Type*} [DecidableEq n]

/-- The permutation matrix of a power of `σ` is the power of the permutation matrix of `σ`. -/
@[simp]
theorem permMatrix_pow [Fintype n] [Semiring R] (σ : Equiv.Perm n) (k : ℕ) :
    (σ ^ k).permMatrix R = σ.permMatrix R ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, permMatrix_mul, ih, pow_succ']

variable [Zero R] [One R]

/-- A permutation matrix is block triangular for any labelling of the coordinates that is
constant along the cycles of the permutation. -/
theorem blockTriangular_permMatrix {α : Type*} [Preorder α] (σ : Equiv.Perm n) {b : n → α}
    (hb : ∀ x, b (σ x) = b x) : (σ.permMatrix R).BlockTriangular b := by
  intro i j hij
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply]
  refine Pi.single_eq_of_ne (fun h => ?_) _
  rw [h, hb] at hij
  exact lt_irrefl _ hij

/-- The diagonal block of a permutation matrix over a fibre of a labelling preserved by `σ` is the
permutation matrix of the restriction of `σ` to that fibre. -/
theorem toSquareBlock_permMatrix {α : Type*} (σ : Equiv.Perm n) {b : n → α}
    (hb : ∀ x, b (σ x) = b x) (a : α) :
    (σ.permMatrix R).toSquareBlock b a =
      (σ.subtypePerm (p := fun x => b x = a) fun x => by rw [hb]).permMatrix R := by
  ext x y
  simp [toSquareBlock_def, Subtype.ext_iff]

end Matrix

namespace Equiv.Perm

variable {n R : Type*} [Fintype n] [DecidableEq n]

/-- If `σ` has a single orbit on `n`, then no nonzero polynomial of degree less than `card n` kills
the permutation matrix of `σ`. -/
theorem eq_zero_of_aeval_permMatrix_eq_zero [CommRing R] {σ : Perm n}
    (hσ : ∀ x y, σ.SameCycle x y) {p : R[X]} (hp : p.natDegree < Fintype.card n)
    (hA : aeval (σ.permMatrix R) p = 0) : p = 0 := by
  have hf := isCycleOn_univ_of_forall_sameCycle hσ
  obtain ⟨x₀⟩ : Nonempty n := Fintype.card_pos_iff.mp (p.natDegree.zero_le.trans_lt hp)
  -- The entry of `aeval P p` in row `x₀` and column `σ ^ j x₀` is the coefficient of `X ^ j`.
  ext j
  rw [coeff_zero]
  rcases lt_or_ge j (Fintype.card n) with hj | hj
  · have hentry := congrFun (congrFun hA x₀) ((σ ^ j) x₀)
    rw [aeval_eq_sum_range' hp, Matrix.sum_apply, Finset.sum_eq_single j] at hentry
    · simpa [← permMatrix_pow] using hentry
    · intro i hi hij
      have hne : (σ ^ i) x₀ ≠ (σ ^ j) x₀ := fun h =>
        hij (hf.injOn_pow_apply (Finset.mem_univ x₀) (by simpa using Finset.mem_range.mp hi)
          (by simpa using hj) h)
      simp [← permMatrix_pow, hne]
    · intro hj'
      exact absurd (Finset.mem_range.mpr hj) hj'
  · exact coeff_eq_zero_of_natDegree_lt (hp.trans_le hj)

/-- A permutation with a single orbit on a nonempty finite set of size `d` has characteristic
polynomial `X ^ d - 1`. -/
theorem charpoly_permMatrix_of_forall_sameCycle [CommRing R] [Nonempty n] (σ : Perm n)
    (hσ : ∀ x y, σ.SameCycle x y) :
    (σ.permMatrix R).charpoly = X ^ Fintype.card n - 1 := by
  nontriviality R
  -- By Cayley–Hamilton, the difference of the two monic polynomials of degree `card n` kills the
  -- permutation matrix, but has smaller degree.
  have hd : Fintype.card n ≠ 0 := Fintype.card_ne_zero
  have hmonic : IsMonicOfDegree (σ.permMatrix R).charpoly (Fintype.card n) :=
    ⟨charpoly_natDegree_eq_dim _, charpoly_monic _⟩
  have hmonic' : IsMonicOfDegree (X ^ Fintype.card n - 1 : R[X]) (Fintype.card n) :=
    (isMonicOfDegree_X_pow R _).sub (by rw [natDegree_one]; exact Nat.pos_of_ne_zero hd)
  rw [← sub_eq_zero]
  refine eq_zero_of_aeval_permMatrix_eq_zero hσ (hmonic.natDegree_sub_lt hd hmonic') ?_
  rw [map_sub, aeval_self_charpoly, map_sub, map_pow, aeval_X, map_one, ← permMatrix_pow,
    pow_card_eq_one_of_forall_sameCycle hσ, permMatrix_one, sub_self, sub_self]

variable [CommRing R]

/-- The characteristic polynomial of a permutation matrix is the product of `X ^ d - 1` over the
cycle lengths `d` of the permutation, fixed points included. -/
theorem charpoly_permMatrix (σ : Perm n) :
    (σ.permMatrix R).charpoly = (σ.fullCycleType.map fun d => X ^ d - 1).prod := by
  -- Label the cycles of `σ` by natural numbers, so that the labelling has ordered values.
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin (Quotient (SameCycle.setoid σ))
  set b : n → ℕ := fun x => e (Quotient.mk _ x)
  -- `Quotient.eq` produces the relation of `SameCycle.setoid σ`, which is `σ.SameCycle` by
  -- definition, whence the `Iff.rfl`.
  have hb : ∀ x y, σ.SameCycle x y ↔ b x = b y := fun x y => by
    rw [Fin.val_inj, e.injective.eq_iff, Quotient.eq]
    exact Iff.rfl
  have hσb : ∀ x, b (σ x) = b x := fun x => (hb _ _).mp (sameCycle_apply_left.mpr (.refl σ x))
  rw [(blockTriangular_permMatrix σ hσb).charpoly, fullCycleType_eq_map_card_filter σ b hb,
    Multiset.map_map, Finset.prod_map_val]
  refine Finset.prod_congr (by congr!) fun a ha => ?_
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha
  obtain ⟨x, rfl⟩ := ha
  have : Nonempty {y // b y = b x} := ⟨⟨x, rfl⟩⟩
  rw [toSquareBlock_permMatrix σ hσb, charpoly_permMatrix_of_forall_sameCycle, Fintype.card_subtype]
  · -- `fullCycleType_eq_map_card_filter` counts the fibre with a classical decidability instance.
    simp only [Function.comp_apply]
    congr
  · rintro ⟨y, hy⟩ ⟨z, hz⟩
    rw [sameCycle_subtypePerm, hb]
    exact hy.trans hz.symm

/-- The reversed characteristic polynomial `det (1 - X P_σ)` of a permutation matrix is the
product of `1 - X ^ d` over the cycle lengths `d` of the permutation, fixed points included. -/
theorem charpolyRev_permMatrix (σ : Perm n) :
    (σ.permMatrix R).charpolyRev = (σ.fullCycleType.map fun d => 1 - X ^ d).prod := by
  rw [charpolyRev_eq_reflect, charpoly_permMatrix, ← sum_fullCycleType σ,
    reflect_sum_prod_X_pow_sub_one]

/-- In the standard basis of `n →₀ R`, the permutation action `Finsupp.lmapDomain R R σ` has the
transpose of the permutation matrix of `σ` as its matrix. -/
theorem toMatrix_lmapDomain (σ : Perm n) :
    LinearMap.toMatrix (Finsupp.basisSingleOne : Module.Basis n R (n →₀ R)) Finsupp.basisSingleOne
      (Finsupp.lmapDomain R R σ) = (σ.permMatrix R)ᵀ := by
  ext i j
  simp [LinearMap.toMatrix_apply, Finsupp.single_apply, eq_comm]

/-- The characteristic polynomial of the permutation action of `σ` on `n →₀ R` is the product of
`X ^ d - 1` over the cycle lengths `d` of `σ`, fixed points included. -/
theorem charpoly_lmapDomain (σ : Perm n) :
    (Finsupp.lmapDomain R R σ).charpoly = (σ.fullCycleType.map fun d => X ^ d - 1).prod := by
  rw [← LinearMap.charpoly_toMatrix _ Finsupp.basisSingleOne, toMatrix_lmapDomain,
    charpoly_transpose, charpoly_permMatrix]

/-- The reversed characteristic polynomial of the permutation action of `σ` on `n →₀ R` is the
product of `1 - X ^ d` over the cycle lengths `d` of `σ`, fixed points included. -/
theorem reverse_charpoly_lmapDomain (σ : Perm n) :
    (Finsupp.lmapDomain R R σ).charpoly.reverse =
      (σ.fullCycleType.map fun d => 1 - X ^ d).prod := by
  rw [← LinearMap.charpoly_toMatrix _ Finsupp.basisSingleOne, toMatrix_lmapDomain,
    reverse_charpoly, charpolyRev_transpose, charpolyRev_permMatrix]

end Equiv.Perm
