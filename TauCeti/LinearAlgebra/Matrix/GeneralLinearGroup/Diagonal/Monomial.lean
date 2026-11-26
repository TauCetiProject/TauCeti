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
(`TauCeti.diagGL_mul_permutationGL_injective`), so over a field with `q` elements the monomial
subgroup has `n! (q - 1)ⁿ` elements (`TauCeti.natCard_monomialGL`).

In rank two the diagonal torus is the split Cartan subgroup `C_s` of `GL₂(𝔽_q)` and the monomial
subgroup, the matrices that are diagonal or antidiagonal, is the subgroup `C_s⁺` stabilizing the
pair of coordinate lines. They have indices `q(q + 1)` and `q(q + 1) / 2`
(`TauCeti.index_diagonalTorus_two`, `TauCeti.two_mul_index_monomialGL_two`), both contain `-1`,
and the determinant is surjective on both (`TauCeti.map_det_diagonalTorus`,
`TauCeti.map_det_monomialGL`).

## Main declarations

* `TauCeti.monomialGL k n`: the monomial subgroup, with `TauCeti.mem_monomialGL_iff`.
* `TauCeti.diagonalTorus_le_monomialGL`, `TauCeti.permutationGL_mem_monomialGL`,
  `TauCeti.monomialGL_le_normalizer`, `TauCeti.normalizer_diagonalTorus_eq_monomialGL`.
* `TauCeti.diagGL_mul_permutationGL_injective`, `TauCeti.natCard_monomialGL`.
* `TauCeti.index_diagonalTorus_two`, `TauCeti.two_mul_index_monomialGL_two`,
  `TauCeti.relIndex_diagonalTorus_monomialGL_two`, `TauCeti.neg_one_mem_diagonalTorus`,
  `TauCeti.neg_one_mem_monomialGL`, `TauCeti.map_det_diagonalTorus`, `TauCeti.map_det_monomialGL`.

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
    refine ⟨fun i ↦ (d (σ i))⁻¹, σ⁻¹, ?_⟩
    rw [diagGL_mul_permutationGL, _root_.mul_inv_rev, ← map_inv, ← map_inv]
    rfl

/-- Membership in the monomial subgroup. -/
theorem mem_monomialGL_iff {g : GL (Fin n) k} :
    g ∈ monomialGL k n ↔
      ∃ d : Fin n → kˣ, ∃ σ : Equiv.Perm (Fin n), g = diagGL d * permutationGL σ :=
  Iff.rfl

/-- A diagonal matrix followed by a permutation matrix is monomial. -/
theorem diagGL_mul_permutationGL_mem_monomialGL (d : Fin n → kˣ) (σ : Equiv.Perm (Fin n)) :
    diagGL d * permutationGL σ ∈ monomialGL k n :=
  ⟨d, σ, rfl⟩

/-- Diagonal matrices of units are monomial. -/
theorem diagGL_mem_monomialGL (d : Fin n → kˣ) : diagGL d ∈ monomialGL k n :=
  ⟨d, 1, by simp⟩

/-- Permutation matrices are monomial. -/
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

/-- The entries of `diagGL d * permutationGL σ`: the `(i, j)` entry is `d i` if `i = σ j` and `0`
otherwise. -/
theorem coe_diagGL_mul_permutationGL_apply (d : Fin n → kˣ) (σ : Equiv.Perm (Fin n))
    (i j : Fin n) :
    ((diagGL d * permutationGL σ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      if i = σ j then (d i : k) else 0 := by
  rw [coe_mul_permutationGL_apply, diagGL_coe, Matrix.diagonal_apply]

/-- **Uniqueness of the monomial factorization** over a nontrivial semiring. -/
theorem diagGL_mul_permutationGL_injective [Nontrivial k] :
    Function.Injective fun p : (Fin n → kˣ) × Equiv.Perm (Fin n) ↦
      (diagGL p.1 * permutationGL p.2 : GL (Fin n) k) := by
  rintro ⟨d, σ⟩ ⟨d', σ'⟩ h
  have h' (i j : Fin n) := congrArg (fun g : GL (Fin n) k ↦ (g : Matrix (Fin n) (Fin n) k) i j) h
  simp only [coe_diagGL_mul_permutationGL_apply] at h'
  have hσ : σ = σ' := by
    ext j
    by_contra hne
    have := h' (σ j) j
    rw [ite_eq_left (rfl : σ j = σ j), ite_eq_right (fun h ↦ hne (congrArg Fin.val h))] at this
    exact (d (σ j)).ne_zero this
  subst hσ
  refine Prod.ext (funext fun i ↦ Units.ext ?_) rfl
  simpa using h' i (σ⁻¹ i)

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

section Field

variable (k n) [Field k]

/-- **The order of the monomial subgroup**: over a field with `q` elements it has `n! (q - 1)ⁿ`
elements. -/
theorem natCard_monomialGL :
    Nat.card (monomialGL k n) = n.factorial * (Nat.card k - 1) ^ n := by
  let e : (Fin n → kˣ) × Equiv.Perm (Fin n) ≃ monomialGL k n :=
    Equiv.ofBijective (fun p ↦ ⟨diagGL p.1 * permutationGL p.2, p.1, p.2, rfl⟩)
      ⟨fun p q h ↦ diagGL_mul_permutationGL_injective (congrArg Subtype.val h),
        fun ⟨_, d, σ, h⟩ ↦ ⟨(d, σ), Subtype.ext h.symm⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_fun, Nat.card_units, Nat.card_perm,
    Nat.card_fin]
  exact mul_comm _ _

/-! ### Rank two: the split Cartan subgroup and its normalizer -/

/-- **The index of the split Cartan subgroup** of `GL₂(𝔽_q)` is `q(q + 1)`. -/
theorem index_diagonalTorus_two [Finite k] :
    (diagonalTorus k 2).index = Nat.card k * (Nat.card k + 1) := by
  have hq : 0 < (Nat.card k - 1) ^ 2 := pow_pos (Nat.sub_pos_of_lt Finite.one_lt_card) 2
  have h := (diagonalTorus k 2).card_mul_index
  rw [natCard_diagonalTorus, natCard_GL_fin_two] at h
  exact Nat.eq_of_mul_eq_mul_left hq h

/-- **The index of the monomial subgroup** `C_s⁺` of `GL₂(𝔽_q)` is `q(q + 1) / 2`. -/
theorem two_mul_index_monomialGL_two [Finite k] :
    2 * (monomialGL k 2).index = Nat.card k * (Nat.card k + 1) := by
  have hq : 0 < (Nat.card k - 1) ^ 2 := pow_pos (Nat.sub_pos_of_lt Finite.one_lt_card) 2
  have h := (monomialGL k 2).card_mul_index
  rw [natCard_monomialGL, natCard_GL_fin_two] at h
  refine Nat.eq_of_mul_eq_mul_left hq ?_
  rw [← h]
  simp only [Nat.factorial_two]
  ring

/-- The split Cartan subgroup has index two in the monomial subgroup of `GL₂(𝔽_q)`. -/
theorem relIndex_diagonalTorus_monomialGL_two [Finite k] :
    (diagonalTorus k 2).relIndex (monomialGL k 2) = 2 := by
  have hpos : 0 < (monomialGL k 2).index := Subgroup.index_pos
  have h := Subgroup.relIndex_mul_index (diagonalTorus_le_monomialGL (k := k) (n := 2))
  rw [index_diagonalTorus_two, ← two_mul_index_monomialGL_two, mul_comm 2] at h
  exact Nat.eq_of_mul_eq_mul_right hpos (h.trans (mul_comm _ _))

end Field

section CommRing

variable [CommRing k]

/-- `-1` lies in the diagonal torus. -/
theorem neg_one_mem_diagonalTorus : (-1 : GL (Fin n) k) ∈ diagonalTorus k n :=
  mem_diagonalTorus_iff_exists_diagGL.2 ⟨fun _ ↦ -1, by
    ext i j
    by_cases h : i = j <;> simp [h]⟩

/-- `-1` lies in the monomial subgroup. -/
theorem neg_one_mem_monomialGL : (-1 : GL (Fin n) k) ∈ monomialGL k n :=
  diagonalTorus_le_monomialGL neg_one_mem_diagonalTorus

/-- **The determinant is surjective on the diagonal torus** of `GLₙ` for `n ≥ 1`. -/
theorem map_det_diagonalTorus [NeZero n] :
    (diagonalTorus k n).map Matrix.GeneralLinearGroup.det = ⊤ := by
  refine eq_top_iff.2 fun u _ ↦ ⟨diagGL (Function.update 1 0 u), ?_, ?_⟩
  · exact mem_diagonalTorus_iff_exists_diagGL.2 ⟨_, rfl⟩
  · simp [det_diagGL, Finset.prod_update_of_mem]

/-- **The determinant is surjective on the monomial subgroup** of `GLₙ` for `n ≥ 1`. -/
theorem map_det_monomialGL [NeZero n] :
    (monomialGL k n).map Matrix.GeneralLinearGroup.det = ⊤ :=
  eq_top_iff.2 ((map_det_diagonalTorus (k := k) (n := n)).ge.trans
    (Subgroup.map_mono diagonalTorus_le_monomialGL))

end CommRing

end

end TauCeti
