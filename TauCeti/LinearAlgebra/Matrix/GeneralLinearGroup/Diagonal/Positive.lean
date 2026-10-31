/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# The positive diagonal subgroup of the general linear group

Over a linearly ordered field `𝕜`, the invertible diagonal matrices whose diagonal entries are all
positive form a subgroup `TauCeti.posDiagonalSubgroup ι 𝕜` of `GL ι 𝕜`: products and inverses of
positive diagonal matrices are computed entrywise, and products and inverses of positive scalars
are positive. It lies inside the diagonal torus (`TauCeti.posDiagonalSubgroup_le_diagonalTorus`).

Over `𝕜 = ℝ` this is the factor `A` of the Iwasawa decomposition `GL n ℝ = K A N`.

## Main definitions

* `TauCeti.posDiagonalSubgroup ι 𝕜`: the diagonal matrices with positive diagonal entries, as a
  subgroup of `GL ι 𝕜`.

## Main results

* `TauCeti.mem_posDiagonalSubgroup_iff`: membership means being the diagonal matrix of a family
  of positive scalars.
* `TauCeti.coe_inv_of_mem_posDiagonalSubgroup`: the inverse of a positive diagonal matrix is the
  diagonal matrix of the inverse entries.
* `TauCeti.diagGL_mem_posDiagonalSubgroup_iff`: `diagGL t` is positive diagonal exactly when every
  `t i` is positive.
* `TauCeti.centralizer_posDiagonalSubgroup`: the centralizer of the positive diagonal subgroup in
  `GL n 𝕜` is the diagonal torus, since positive diagonal matrices separate the coordinates.
-/

public section

open Matrix

namespace TauCeti

variable (ι : Type*) [Fintype ι] [DecidableEq ι] (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]

/-- **The positive diagonal subgroup** of `GL ι 𝕜`: the invertible matrices that are diagonal with
positive diagonal entries. -/
def posDiagonalSubgroup : Subgroup (GL ι 𝕜) where
  carrier := {g | ∃ d : ι → 𝕜, (∀ i, 0 < d i) ∧ (g : Matrix ι ι 𝕜) = diagonal d}
  one_mem' := ⟨1, fun _ => one_pos, by simp⟩
  mul_mem' := by
    rintro g h ⟨d, hd, hg⟩ ⟨e, he, hh⟩
    exact ⟨d * e, fun i => mul_pos (hd i) (he i), by simp [hg, hh]⟩
  inv_mem' := by
    rintro g ⟨d, hd, hg⟩
    exact ⟨d⁻¹, fun i => inv_pos.2 (hd i),
      coe_inv_of_coe_eq_diagonal hg⟩

variable {ι 𝕜}

/-- An invertible matrix lies in the positive diagonal subgroup exactly when it is the diagonal
matrix of a family of positive scalars. -/
theorem mem_posDiagonalSubgroup_iff {g : GL ι 𝕜} :
    g ∈ posDiagonalSubgroup ι 𝕜 ↔ ∃ d : ι → 𝕜, (∀ i, 0 < d i) ∧ (g : Matrix ι ι 𝕜) = diagonal d :=
  Iff.rfl

/-- An element of the positive diagonal subgroup is the diagonal matrix of its diagonal entries. -/
theorem coe_eq_diagonal_of_mem_posDiagonalSubgroup {g : GL ι 𝕜}
    (hg : g ∈ posDiagonalSubgroup ι 𝕜) :
    (g : Matrix ι ι 𝕜) = diagonal fun i => (g : Matrix ι ι 𝕜) i i := by
  obtain ⟨d, -, hd⟩ := hg
  simp [hd]

/-- The diagonal entries of an element of the positive diagonal subgroup are positive. -/
theorem apply_diag_pos_of_mem_posDiagonalSubgroup {g : GL ι 𝕜}
    (hg : g ∈ posDiagonalSubgroup ι 𝕜) (i : ι) : 0 < (g : Matrix ι ι 𝕜) i i := by
  obtain ⟨d, hd, hgd⟩ := hg
  simpa [hgd] using hd i

/-- The inverse of an element of the positive diagonal subgroup is the diagonal matrix of the
inverses of its diagonal entries. -/
theorem coe_inv_of_mem_posDiagonalSubgroup {g : GL ι 𝕜} (hg : g ∈ posDiagonalSubgroup ι 𝕜) :
    ((g⁻¹ : GL ι 𝕜) : Matrix ι ι 𝕜) = diagonal fun i => ((g : Matrix ι ι 𝕜) i i)⁻¹ :=
  coe_inv_of_coe_eq_diagonal (coe_eq_diagonal_of_mem_posDiagonalSubgroup hg)

/-- The diagonal element `diagGL t` lies in the positive diagonal subgroup exactly when every
unit `t i` is positive. -/
@[simp]
theorem diagGL_mem_posDiagonalSubgroup_iff {t : ι → 𝕜ˣ} :
    diagGL t ∈ posDiagonalSubgroup ι 𝕜 ↔ ∀ i, 0 < (t i : 𝕜) := by
  rw [mem_posDiagonalSubgroup_iff, diagGL_coe]
  refine ⟨fun ⟨d, hd, h⟩ => ?_, fun h => ⟨_, h, rfl⟩⟩
  obtain rfl := diagonal_injective h
  exact hd

variable (𝕜) in
/-- The positive diagonal subgroup lies in the diagonal torus. -/
theorem posDiagonalSubgroup_le_diagonalTorus (n : ℕ) :
    posDiagonalSubgroup (Fin n) 𝕜 ≤ diagonalTorus 𝕜 n := by
  rintro g ⟨d, -, hg⟩
  rw [mem_diagonalTorus_iff, hg]
  exact isDiag_diagonal d

variable (𝕜) in
/-- **The centralizer of the positive diagonal subgroup is the diagonal torus.** The positive
diagonal matrices already separate any two coordinates, so an invertible matrix commuting with all
of them is diagonal. -/
theorem centralizer_posDiagonalSubgroup (n : ℕ) :
    Subgroup.centralizer (posDiagonalSubgroup (Fin n) 𝕜 : Set (GL (Fin n) 𝕜)) =
      diagonalTorus 𝕜 n := by
  refine le_antisymm (fun g hg => mem_diagonalTorus_iff.mpr fun i j hij => ?_)
    ((Subgroup.le_centralizer _).trans
      (Subgroup.centralizer_le (posDiagonalSubgroup_le_diagonalTorus 𝕜 n)))
  -- The positive diagonal matrix with `2` at `i` and `1` elsewhere separates `i` from `j`.
  let t : Fin n → 𝕜ˣ := Pi.mulSingle i (Units.mk0 2 two_ne_zero)
  have ht : diagGL t ∈ posDiagonalSubgroup (Fin n) 𝕜 :=
    diagGL_mem_posDiagonalSubgroup_iff.mpr fun m => by
      rcases eq_or_ne m i with rfl | hm <;> simp [t, *]
  have hcomm := congrArg Units.val (Subgroup.mem_centralizer_iff.mp hg _ ht)
  rw [Units.val_mul, Units.val_mul, diagGL_coe] at hcomm
  exact apply_eq_zero_of_commute_diagonal hcomm (by simp [t, Pi.mulSingle_eq_of_ne hij.symm])

end TauCeti
