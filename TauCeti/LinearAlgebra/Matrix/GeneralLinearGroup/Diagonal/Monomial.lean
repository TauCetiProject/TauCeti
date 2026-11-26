/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer

/-!
# The monomial subgroup of `GLₙ`

The *monomial subgroup* `TauCeti.monomialGL k n` of `GLₙ(k)` consists of the products
`diagGL d * permutationGL σ` of a diagonal matrix of units and a permutation matrix: the invertible
matrices with exactly one nonzero entry, a unit, in every row and column. It contains the diagonal
torus and always normalizes it (`TauCeti.monomialGL_le_normalizer`). When `kˣ` is nontrivial (and
`k` is commutative without zero divisors) it is the normalizer of the diagonal torus
(`TauCeti.normalizer_diagonalTorus_eq_monomialGL`), but over `𝔽₂` the diagonal torus is trivial
and its normalizer is all of `GLₙ(𝔽₂)`, while the monomial subgroup is the group of permutation
matrices.

Over a nontrivial semiring the factorization `g = diagGL d * permutationGL σ` is unique
(`TauCeti.diagGL_mul_permutationGL_injective`), so over a division semiring with `q` elements the
monomial subgroup has `n! (q - 1)ⁿ` elements (`TauCeti.natCard_monomialGL`) and contains the
diagonal torus with index `n!` (`TauCeti.relIndex_diagonalTorus_monomialGL`).

In rank two the diagonal torus is the split Cartan subgroup `C_s` of `GL₂(𝔽_q)` and the monomial
subgroup, the matrices that are diagonal or antidiagonal, is the subgroup `C_s⁺` stabilizing the
pair of coordinate lines. They have indices `q(q + 1)` and `q(q + 1) / 2`
(`TauCeti.index_diagonalTorus_two`, `TauCeti.two_mul_index_monomialGL_two`), both contain `-1`,
and the determinant is surjective on both (`TauCeti.map_det_diagonalTorus`,
`TauCeti.map_det_monomialGL`).

## Main declarations

* `TauCeti.monomialGL k n`: the monomial subgroup, with `TauCeti.mem_monomialGL_iff` and the
  entrywise criterion `TauCeti.mem_monomialGL_iff_exists_perm`.
* `TauCeti.diagonalTorus_le_monomialGL`, `TauCeti.permutationGL_mem_monomialGL`,
  `TauCeti.monomialGL_le_normalizer`, `TauCeti.normalizer_diagonalTorus_eq_monomialGL`.
* `TauCeti.natCard_monomialGL`, `TauCeti.relIndex_diagonalTorus_monomialGL`.
* `TauCeti.index_diagonalTorus_two`, `TauCeti.two_mul_index_monomialGL_two`,
  `TauCeti.neg_one_mem_monomialGL`,
  `TauCeti.map_det_monomialGL`.

## References

* D. Zywina, *On the possible images of the mod `ℓ` representations associated to elliptic curves
  over `ℚ`*, arXiv:1508.07660, §1 (Notation) and §3.2.
-/

public section

open Matrix

namespace TauCeti

universe u

noncomputable section

variable {k : Type u} {n : ℕ}

section Semiring

variable [Semiring k]

variable (k n) in
/-- **The monomial subgroup** of `GLₙ(k)`: the products `diagGL d * permutationGL σ` of a diagonal
matrix of units and a permutation matrix. -/
def monomialGL : Subgroup (GL (Fin n) k) where
  carrier := {g | ∃ d : Fin n → kˣ, ∃ σ : Equiv.Perm (Fin n), g = diagGL d * permutationGL σ}
  one_mem' := ⟨1, 1, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨d, σ, rfl⟩ ⟨d', σ', rfl⟩
    refine ⟨d * fun i ↦ d' (σ⁻¹ i), σ * σ', ?_⟩
    rw [map_mul, map_mul, ← permutationGL_mul_diagGL_mul_inv σ d']
    group
  inv_mem' := by
    rintro _ ⟨d, σ, rfl⟩
    refine ⟨(fun i ↦ d (σ i))⁻¹, σ⁻¹, ?_⟩
    rw [diagGL_mul_permutationGL, _root_.mul_inv_rev, ← map_inv, ← map_inv]

/-- Membership in the monomial subgroup. -/
theorem mem_monomialGL_iff {g : GL (Fin n) k} :
    g ∈ monomialGL k n ↔
      ∃ d : Fin n → kˣ, ∃ σ : Equiv.Perm (Fin n), g = diagGL d * permutationGL σ :=
  Iff.rfl

/-- A diagonal matrix followed by a permutation matrix is monomial. -/
@[simp]
theorem diagGL_mul_permutationGL_mem_monomialGL (d : Fin n → kˣ) (σ : Equiv.Perm (Fin n)) :
    diagGL d * permutationGL σ ∈ monomialGL k n :=
  ⟨d, σ, rfl⟩

/-- Diagonal matrices of units are monomial. -/
@[simp]
theorem diagGL_mem_monomialGL (d : Fin n → kˣ) : diagGL d ∈ monomialGL k n :=
  ⟨d, 1, by simp⟩

/-- Permutation matrices are monomial. -/
@[simp]
theorem permutationGL_mem_monomialGL (σ : Equiv.Perm (Fin n)) :
    permutationGL σ ∈ monomialGL k n :=
  ⟨1, σ, by simp⟩

/-- The diagonal torus is contained in the monomial subgroup. -/
theorem diagonalTorus_le_monomialGL : diagonalTorus k n ≤ monomialGL k n := fun _ hg ↦ by
  obtain ⟨d, rfl⟩ := mem_diagonalTorus_iff_exists_diagGL.1 hg
  exact diagGL_mem_monomialGL d

/-- The monomial subgroup normalizes the diagonal torus. -/
theorem monomialGL_le_normalizer :
    monomialGL k n ≤ Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)) := by
  rintro _ ⟨d, σ, rfl⟩
  exact mul_mem (Subgroup.le_normalizer (mem_diagonalTorus_iff_exists_diagGL.2 ⟨d, rfl⟩))
    (permutationGL_mem_normalizer σ)

/-- **The entrywise membership criterion**: an invertible matrix is monomial exactly when, for
some permutation `σ`, its `(i, j)` entry vanishes unless `i = σ j`. -/
theorem mem_monomialGL_iff_exists_perm {g : GL (Fin n) k} :
    g ∈ monomialGL k n ↔
      ∃ σ : Equiv.Perm (Fin n), ∀ i j, i ≠ σ j → (g : Matrix (Fin n) (Fin n) k) i j = 0 := by
  constructor
  · rintro ⟨d, σ, rfl⟩
    exact ⟨σ, fun i j hij ↦ by simp [hij]⟩
  · rintro ⟨σ, hσ⟩
    refine exists_eq_diagGL_mul_permutationGL_of_forall_eq_of_ne_zero_of_ne_zero
      fun i j l hj hl ↦ σ.injective ?_
    rw [← not_ne_iff.1 (mt (hσ i j) hj), ← not_ne_iff.1 (mt (hσ i l) hl)]

end Semiring

section Normalizer

variable [CommSemiring k] [IsCancelMulZero k] [Nontrivial kˣ]

/-- **The normalizer of the diagonal torus is the monomial subgroup** when `kˣ` is nontrivial. Over
`𝔽₂` this fails for `n ≥ 2`: the diagonal torus is trivial. -/
theorem normalizer_diagonalTorus_eq_monomialGL :
    Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)) = monomialGL k n := by
  ext g
  exact mem_normalizer_diagonalTorus_iff_exists

end Normalizer

section DivisionSemiring

variable (k n) [DivisionSemiring k]

/-- **The order of the monomial subgroup**: over a division semiring with `q` elements it has
`n! (q - 1)ⁿ` elements. -/
theorem natCard_monomialGL :
    Nat.card (monomialGL k n) = n.factorial * (Nat.card k - 1) ^ n := by
  let e : (Fin n → kˣ) × Equiv.Perm (Fin n) ≃ monomialGL k n :=
    Equiv.ofBijective (fun p ↦ ⟨diagGL p.1 * permutationGL p.2, p.1, p.2, rfl⟩)
      ⟨fun p q h ↦ diagGL_mul_permutationGL_injective (congrArg Subtype.val h),
        fun ⟨_, d, σ, h⟩ ↦ ⟨(d, σ), Subtype.ext h.symm⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_fun, Nat.card_units, Nat.card_perm,
    Nat.card_fin]
  exact mul_comm _ _

/-- **The index of the diagonal torus in the monomial subgroup** is `n!`, the number of
permutation matrices, over a finite division semiring. -/
theorem relIndex_diagonalTorus_monomialGL [Finite k] :
    (diagonalTorus k n).relIndex (monomialGL k n) = n.factorial := by
  have hq : 0 < (Nat.card k - 1) ^ n := pow_pos (Nat.sub_pos_of_lt Finite.one_lt_card) n
  have h := (diagonalTorus k n).relIndex_mul_card (monomialGL k n)
  rw [inf_of_le_left diagonalTorus_le_monomialGL, natCard_diagonalTorus, natCard_monomialGL] at h
  exact Nat.eq_of_mul_eq_mul_right hq h

end DivisionSemiring

section Field

variable (k) [Field k]

/-! ### Rank two: the split Cartan subgroups `C_s` and `C_s⁺` -/

/-- **The index of the split Cartan subgroup** `C_s` of `GL₂(𝔽_q)` is `q(q + 1)`. -/
theorem index_diagonalTorus_two [Finite k] :
    (diagonalTorus k 2).index = Nat.card k * (Nat.card k + 1) := by
  have hq : 0 < (Nat.card k - 1) ^ 2 := pow_pos (Nat.sub_pos_of_lt Finite.one_lt_card) 2
  have h := (diagonalTorus k 2).card_mul_index
  rw [natCard_diagonalTorus, natCard_GL_fin_two] at h
  exact Nat.eq_of_mul_eq_mul_left hq h

/-- **The index of the monomial subgroup** `C_s⁺` of `GL₂(𝔽_q)` is `q(q + 1) / 2`. -/
theorem two_mul_index_monomialGL_two [Finite k] :
    2 * (monomialGL k 2).index = Nat.card k * (Nat.card k + 1) := by
  rw [← index_diagonalTorus_two, ← Subgroup.relIndex_mul_index diagonalTorus_le_monomialGL,
    relIndex_diagonalTorus_monomialGL, Nat.factorial_two]

end Field

section Ring

variable [Ring k]

/-- `-1` lies in the monomial subgroup. -/
@[simp]
theorem neg_one_mem_monomialGL : (-1 : GL (Fin n) k) ∈ monomialGL k n :=
  diagonalTorus_le_monomialGL neg_one_mem_diagonalTorus

end Ring

section CommRing

variable [CommRing k]

/-- **The determinant is surjective on the monomial subgroup** of `GLₙ` for `n ≥ 1`. -/
theorem map_det_monomialGL [NeZero n] :
    (monomialGL k n).map Matrix.GeneralLinearGroup.det = ⊤ :=
  eq_top_iff.2 ((map_det_diagonalTorus (k := k) (n := n)).ge.trans
    (Subgroup.map_mono diagonalTorus_le_monomialGL))

end CommRing

end

end TauCeti
