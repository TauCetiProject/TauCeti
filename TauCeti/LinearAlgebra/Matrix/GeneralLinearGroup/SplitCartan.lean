/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.diagonalTorus` occurs in the statements below, and this module re-exports the `GL`
-- notation and `Matrix.GeneralLinearGroup.det`.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
-- `Subgroup.index`, `Subgroup.relIndex` and `Subgroup.normalizer` occur in the statements below.
public import Mathlib.GroupTheory.Index
-- `TauCeti.mem_normalizer_diagonalTorus_iff_exists`: the normalizer of the diagonal torus is the
-- group of monomial matrices.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
-- `TauCeti.natCard_GL_fin_two`: the order of `GL₂` over a finite field.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card
-- `TauCeti.index_eq_of_natCard_eq_mul`: an index from the orders of a subgroup and its group.
import TauCeti.GroupTheory.Index.Basic

/-!
# The split Cartan subgroup of `GL₂` and its normalizer

The **split Cartan subgroup** `C_s` of `GL₂(R)` is the subgroup of invertible diagonal matrices,
the diagonal torus `TauCeti.diagonalTorus R 2`. Its **monomial** extension
`C_s⁺ = TauCeti.GL2SplitCartanNormalizer R` consists of the invertible matrices that are diagonal
or antidiagonal: under the right action `(P, Q) • !![a, b; c, d] = (a P + c Q, b P + d Q)` on
ordered bases, these are the matrices that preserve the unordered pair of coordinate lines. Over
`𝔽_ℓ` these are the levels of the modular curves `X_s(ℓ)` and `X_s⁺(ℓ)`.

The split Cartan subgroup has index `2` in the monomial subgroup over every nontrivial
commutative ring (`TauCeti.relIndex_diagonalTorus_GL2SplitCartanNormalizer`). When `R` has no
zero divisors (`IsCancelMulZero R`) and a unit other than `1`, the monomial subgroup is the
normalizer of the split Cartan subgroup
(`TauCeti.GL2SplitCartanNormalizer.eq_normalizer`). Over `𝔽₂` this fails: there the split Cartan
subgroup is trivial, so its normalizer is all of `GL₂(𝔽₂)`, of order `6`
(`TauCeti.normalizer_diagonalTorus_eq_top`), while the monomial subgroup has order `2` and index
`3` (`TauCeti.GL2SplitCartanNormalizer.natCard_of_card_eq_two`). The level of `X_s⁺(2)` is the
monomial subgroup, so `C_s⁺` is defined as the monomial subgroup rather than as a normalizer.

Over a finite field with `q` elements, `|C_s| = (q - 1)²` (`TauCeti.natCard_diagonalTorus`) and
`[GL₂(𝔽_q) : C_s] = q (q + 1)`, while `|C_s⁺| = 2 (q - 1)²` and `2 [GL₂(𝔽_q) : C_s⁺] = q (q + 1)`.

## Main definitions

* `TauCeti.GL2SplitCartanNormalizer R`: the subgroup of diagonal or antidiagonal matrices.

## Main results

* `TauCeti.mem_diagonalTorus_two_iff`, `TauCeti.GL2SplitCartanNormalizer.mem_iff`: membership in
  terms of matrix entries.
* `TauCeti.relIndex_diagonalTorus_GL2SplitCartanNormalizer`: `[C_s⁺ : C_s] = 2`.
* `TauCeti.GL2SplitCartanNormalizer.eq_normalizer`: if `R` has no zero divisors and a unit other
  than `1`, the monomial subgroup is the normalizer of the split Cartan subgroup.
* `TauCeti.index_diagonalTorus_two`, `TauCeti.GL2SplitCartanNormalizer.natCard`,
  `TauCeti.GL2SplitCartanNormalizer.two_mul_index`: orders and indices over a finite field.
* `TauCeti.GL2SplitCartanNormalizer.map_det`: the determinant maps `C_s⁺` onto the units.

## References

* D. Zywina, *On the possible images of the mod `ℓ` representations associated to elliptic curves
  over `ℚ`*, arXiv:1508.07660, §1 (Notation) and §3.2.
* K. Česnavičius, *A modular description of `X₀(n)`*, Algebra Number Theory 11 (2017), §4.4.
-/

public section

namespace TauCeti

open Matrix

universe u

section CommRing

variable {R : Type u} [CommRing R]

/-- An invertible `2 × 2` matrix lies in the diagonal torus exactly when both off-diagonal entries
vanish. -/
theorem mem_diagonalTorus_two_iff {g : GL (Fin 2) R} :
    g ∈ diagonalTorus R 2 ↔
      (g : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
  rw [mem_diagonalTorus_iff, Matrix.IsDiag]
  refine ⟨fun h ↦ ⟨h (by decide), h (by decide)⟩, fun ⟨h₁, h₂⟩ i j hij ↦ ?_⟩
  fin_cases i <;> fin_cases j <;> simp_all

variable (R)

/-- **The monomial subgroup** `C_s⁺` of `GL₂(R)`: the invertible matrices that are diagonal or
antidiagonal, which preserve the unordered pair of coordinate lines. It is the normalizer of the
split Cartan subgroup `TauCeti.diagonalTorus R 2` when `R` has no zero divisors and a unit other
than `1` (`TauCeti.GL2SplitCartanNormalizer.eq_normalizer`), but not over `𝔽₂`. -/
def GL2SplitCartanNormalizer : Subgroup (GL (Fin 2) R) where
  carrier := {g | ((g : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0)
    ∨ ((g : Matrix (Fin 2) (Fin 2) R) 0 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 0)}
  mul_mem' := by
    rintro g h (⟨hg₁, hg₂⟩ | ⟨hg₁, hg₂⟩) (⟨hh₁, hh₂⟩ | ⟨hh₁, hh₂⟩) <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, *]
  one_mem' := Or.inl (by simp)
  inv_mem' := by
    rintro g (⟨hg₁, hg₂⟩ | ⟨hg₁, hg₂⟩) <;> simp [Matrix.inv_def, Matrix.adjugate_fin_two, *]

variable {R}

namespace GL2SplitCartanNormalizer

@[simp]
theorem mem_iff {g : GL (Fin 2) R} :
    g ∈ GL2SplitCartanNormalizer R ↔
      ((g : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) ∨
        ((g : Matrix (Fin 2) (Fin 2) R) 0 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 0) :=
  Iff.rfl

theorem diagonalTorus_le : diagonalTorus R 2 ≤ GL2SplitCartanNormalizer R :=
  fun _ hg ↦ Or.inl (mem_diagonalTorus_two_iff.mp hg)

/-- `-1` is monomial. -/
theorem neg_one_mem : (-1 : GL (Fin 2) R) ∈ GL2SplitCartanNormalizer R :=
  diagonalTorus_le neg_one_mem_diagonalTorus

/-- The determinant maps the monomial subgroup onto the units. -/
theorem map_det : (GL2SplitCartanNormalizer R).map GeneralLinearGroup.det = ⊤ :=
  top_le_iff.mp (map_det_diagonalTorus.symm.le.trans (Subgroup.map_mono diagonalTorus_le))

/-- **`[C_s⁺ : C_s] = 2`** over a nontrivial commutative ring: right multiplication by the
antidiagonal matrix `!![0, 1; 1, 0]` exchanges diagonal and antidiagonal matrices. -/
theorem _root_.TauCeti.relIndex_diagonalTorus_GL2SplitCartanNormalizer [Nontrivial R] :
    (diagonalTorus R 2).relIndex (GL2SplitCartanNormalizer R) = 2 := by
  let w : GL (Fin 2) R := ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by simp [one_fin_two],
    by simp [one_fin_two]⟩
  refine Subgroup.relIndex_eq_two_iff.mpr ⟨w, Or.inr (by simp [w]), fun b hb ↦ ?_⟩
  rw [mem_diagonalTorus_two_iff, mem_diagonalTorus_two_iff]
  -- A diagonal or antidiagonal invertible matrix has its two nonzero entries units, hence nonzero.
  have hne : ∀ i j, (b : Matrix (Fin 2) (Fin 2) R) i j = 0 →
      (b : Matrix (Fin 2) (Fin 2) R) i (1 - j) ≠ 0 := by
    intro i j hij hij'
    have h := congrFun (congrFun b.mul_inv i) i
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.mul_apply, Fin.sum_univ_two]
  rcases hb with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have := hne 0 1 h₁
    simp_all [w, Matrix.mul_apply, Fin.sum_univ_two]
  · have := hne 0 0 h₁
    simp_all [w, Matrix.mul_apply, Fin.sum_univ_two]

/-- Conjugating a diagonal matrix by a monomial one gives a diagonal matrix. -/
theorem mul_mul_inv_mem {g h : GL (Fin 2) R} (hg : g ∈ GL2SplitCartanNormalizer R)
    (hh : h ∈ diagonalTorus R 2) : g * h * g⁻¹ ∈ diagonalTorus R 2 := by
  rw [mem_diagonalTorus_two_iff] at hh ⊢
  rcases hg with ⟨hg₁, hg₂⟩ | ⟨hg₁, hg₂⟩ <;>
    simp [Matrix.inv_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hg₁, hg₂,
      hh.1, hh.2]

/-- The monomial subgroup normalizes the split Cartan subgroup, over every commutative ring. -/
theorem le_normalizer :
    GL2SplitCartanNormalizer R ≤ Subgroup.normalizer (diagonalTorus R 2 : Set (GL (Fin 2) R)) := by
  refine fun g hg ↦ Subgroup.mem_normalizer_iff.mpr fun h ↦ ⟨mul_mul_inv_mem hg, fun hh ↦ ?_⟩
  simpa [mul_assoc] using mul_mul_inv_mem (inv_mem hg) hh

/-- **The monomial subgroup is the normalizer of the split Cartan subgroup** when `R` has no zero
divisors (`IsCancelMulZero R`) and a unit other than `1`, for instance over `𝔽_ℓ` for an odd prime
`ℓ`. Over `𝔽₂` the normalizer is all of
`GL₂(𝔽₂)` (`TauCeti.normalizer_diagonalTorus_eq_top`). -/
theorem eq_normalizer [IsCancelMulZero R] [Nontrivial Rˣ] :
    GL2SplitCartanNormalizer R = Subgroup.normalizer (diagonalTorus R 2 : Set (GL (Fin 2) R)) := by
  refine le_antisymm le_normalizer fun g hg ↦ ?_
  obtain ⟨d, σ, rfl⟩ := mem_normalizer_diagonalTorus_iff_exists.mp hg
  have hσ : ∀ σ : Equiv.Perm (Fin 2), σ = 1 ∨ σ = Equiv.swap 0 1 := by decide
  rcases hσ σ with rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inr (by simp)

end GL2SplitCartanNormalizer

end CommRing

section FiniteField

variable {F : Type u} [Field F]

/-- **`[GL₂(𝔽_q) : C_s] = q (q + 1)`** for the split Cartan subgroup
`C_s = TauCeti.diagonalTorus F 2`: the degree of `X_s(ℓ)` over the `j`-line for `q = ℓ`. Its order
`(q - 1)²` is `TauCeti.natCard_diagonalTorus`. -/
theorem index_diagonalTorus_two [Finite F] :
    (diagonalTorus F 2).index = Nat.card F * (Nat.card F + 1) := by
  have := Finite.one_lt_card (α := F)
  exact index_eq_of_natCard_eq_mul (pow_pos (by omega) 2) (natCard_diagonalTorus F 2)
    (natCard_GL_fin_two F)

namespace GL2SplitCartanNormalizer

/-- **`|C_s⁺| = 2 (q - 1)²`** over a field with `q` elements. -/
theorem natCard :
    Nat.card (GL2SplitCartanNormalizer F) = 2 * (Nat.card F - 1) ^ 2 := by
  have h := (diagonalTorus F 2).relIndex_mul_card (GL2SplitCartanNormalizer F)
  rwa [inf_of_le_left diagonalTorus_le, relIndex_diagonalTorus_GL2SplitCartanNormalizer,
    natCard_diagonalTorus, eq_comm] at h

/-- **`2 [GL₂(𝔽_q) : C_s⁺] = q (q + 1)`**: the degree of `X_s⁺(ℓ)` over the `j`-line is
`ℓ (ℓ + 1) / 2`. -/
theorem two_mul_index [Finite F] :
    2 * (GL2SplitCartanNormalizer F).index = Nat.card F * (Nat.card F + 1) := by
  rw [← index_diagonalTorus_two, ← Subgroup.relIndex_mul_index diagonalTorus_le,
    relIndex_diagonalTorus_GL2SplitCartanNormalizer]

/-- **Over `𝔽₂` the monomial subgroup has order `2` and index `3`**, while the normalizer of the
trivial split Cartan subgroup is all of `GL₂(𝔽₂)`, of order `6`. -/
theorem natCard_of_card_eq_two (hF : Nat.card F = 2) :
    Nat.card (GL2SplitCartanNormalizer F) = 2 ∧ (GL2SplitCartanNormalizer F).index = 3 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  refine ⟨by rw [natCard, hF]; norm_num, ?_⟩
  have := two_mul_index (F := F)
  rw [hF] at this
  omega

end GL2SplitCartanNormalizer

end FiniteField

end TauCeti
