/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.CharacterTwist
public import TauCeti.RepresentationTheory.Symmetric.Symmetrizer

/-!
# The sign automorphism and the transposed tableau

Transposing a `μ`-tableau `t` (`TauCeti.YoungTableau.transpose`) exchanges its rows and its
columns, so it exchanges the row group and the column group of `t`. In the group algebra
`R[Sₙ]` the **sign automorphism** `ε`, `σ ↦ sgn(σ) σ`, turns the sum over a group into the signed
sum over the same group and back. Together these give the identities

`ε(a_t) = b_(tᵗ)`, `ε(b_t) = a_(tᵗ)`, hence `ε(c_t) = b_(tᵗ) a_(tᵗ)`,

between the row symmetrizer `a_t`, the column antisymmetrizer `b_t` and the Young symmetrizer
`c_t = a_t b_t` of `t` and the corresponding elements of `tᵗ`. The last one is the Young
symmetrizer of `tᵗ` with its two factors in the opposite order. These identities are the starting
point of the comparison of the Specht module of `λ`, twisted by the sign representation, with the
Specht module of the transposed shape.

The labels of `tᵗ` are `Fin μᵗ.card`, not `Fin μ.card`; the two symmetric groups are identified
by `Equiv.permCongrHom` along `finCongr (YoungDiagram.card_transpose μ)`, and the group algebras
by `MonoidAlgebra.domCongr` of that isomorphism.

## Main definitions and results

* `TauCeti.YoungTableau.rowSubgroup_transpose`, `TauCeti.YoungTableau.colSubgroup_transpose`: the
  row group of `tᵗ` is the column group of `t`, and the column group of `tᵗ` is the row group of
  `t`.
* `TauCeti.signTwist R α`: the sign automorphism `ε` of `R[Perm α]`, the twist of the group
  algebra by the sign character; it is an involution (`TauCeti.signTwist_signTwist`).
* `TauCeti.YoungTableau.signTwist_rowSymmetrizer`,
  `TauCeti.YoungTableau.signTwist_columnAntisymmetrizer` and
  `TauCeti.YoungTableau.signTwist_youngSymmetrizer`: `ε(a_t) = b_(tᵗ)`, `ε(b_t) = a_(tᵗ)` and
  `ε(c_t) = b_(tᵗ) a_(tᵗ)`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 4, §4.1.
-/

public section

namespace TauCeti

/-! ## The sign automorphism -/

section SignTwist

variable (R : Type*) [CommRing R] (α : Type*) [DecidableEq α] [Fintype α]

/-- The **sign automorphism** `ε` of the group algebra `R[Perm α]`, which multiplies each
permutation `σ` by its sign: the twist of the group algebra by the sign character. -/
noncomputable def signTwist :
    MonoidAlgebra R (Equiv.Perm α) ≃ₐ[R] MonoidAlgebra R (Equiv.Perm α) :=
  MonoidAlgebra.charTwist (signLinearCharacter R α)

variable {R α}

/-- The sign automorphism multiplies `single σ r` by the sign of `σ`. -/
@[simp]
theorem signTwist_single (σ : Equiv.Perm α) (r : R) :
    signTwist R α (MonoidAlgebra.single σ r) =
      MonoidAlgebra.single σ (((Equiv.Perm.sign σ : ℤ) : R) * r) := by
  rw [signTwist, MonoidAlgebra.charTwist_single, coe_signLinearCharacter_apply]

/-- The coefficients of `ε(x)` are those of `x` multiplied by the sign. -/
@[simp]
theorem coeff_signTwist (x : MonoidAlgebra R (Equiv.Perm α)) (σ : Equiv.Perm α) :
    (signTwist R α x).coeff σ = ((Equiv.Perm.sign σ : ℤ) : R) * x.coeff σ := by
  rw [signTwist, MonoidAlgebra.coeff_charTwist, coe_signLinearCharacter_apply]

/-- The sign automorphism is an involution. -/
@[simp]
theorem signTwist_signTwist (x : MonoidAlgebra R (Equiv.Perm α)) :
    signTwist R α (signTwist R α x) = x :=
  MonoidAlgebra.charTwist_involutive signLinearCharacter_mul_self x

/-- The sign automorphism is its own inverse. -/
@[simp]
theorem signTwist_symm : (signTwist R α).symm = signTwist R α :=
  AlgEquiv.ext fun x ↦ (AlgEquiv.symm_apply_eq _).mpr (signTwist_signTwist x).symm

end SignTwist

namespace YoungTableau

variable {R : Type*} [CommRing R] {μ : YoungDiagram}

/-! ## The row and column groups of the transposed tableau -/

/-- A permutation of the labels of `tᵗ` preserves its rows exactly when, read on the labels of
`t`, it preserves the columns of `t`.

Not a `simp` lemma: `mem_rowSubgroup` and `rowIndex_transpose` already simplify the left-hand side
to the pointwise condition on the columns of `t`. -/
theorem mem_rowSubgroup_transpose {t : YoungTableau μ} {σ : Equiv.Perm (Fin μ.transpose.card)} :
    σ ∈ rowSubgroup (transpose t) ↔
      (finCongr (YoungDiagram.card_transpose μ)).permCongr σ ∈ colSubgroup t := by
  simp only [mem_rowSubgroup, mem_colSubgroup, rowIndex_transpose, Equiv.permCongr_apply,
    finCongr_apply, finCongr_symm]
  exact ⟨fun h k ↦ by simpa using h (Fin.cast (YoungDiagram.card_transpose μ).symm k),
    fun h k ↦ by simpa using h (Fin.cast (YoungDiagram.card_transpose μ) k)⟩

/-- A permutation of the labels of `tᵗ` preserves its columns exactly when, read on the labels of
`t`, it preserves the rows of `t`. As for `mem_rowSubgroup_transpose`, this is not a `simp`
lemma. -/
theorem mem_colSubgroup_transpose {t : YoungTableau μ} {σ : Equiv.Perm (Fin μ.transpose.card)} :
    σ ∈ colSubgroup (transpose t) ↔
      (finCongr (YoungDiagram.card_transpose μ)).permCongr σ ∈ rowSubgroup t := by
  simp only [mem_rowSubgroup, mem_colSubgroup, colIndex_transpose, Equiv.permCongr_apply,
    finCongr_apply, finCongr_symm]
  exact ⟨fun h k ↦ by simpa using h (Fin.cast (YoungDiagram.card_transpose μ).symm k),
    fun h k ↦ by simpa using h (Fin.cast (YoungDiagram.card_transpose μ) k)⟩

/-- **Transposition turns the column group into the row group.** -/
theorem rowSubgroup_transpose (t : YoungTableau μ) :
    rowSubgroup (transpose t) = (colSubgroup t).map
      (finCongr (YoungDiagram.card_transpose μ)).symm.permCongrHom.toMonoidHom := by
  ext σ
  rw [mem_rowSubgroup_transpose, Subgroup.mem_map_equiv, Equiv.permCongrHom_symm,
    Equiv.symm_symm, Equiv.permCongrHom_coe]

/-- **Transposition turns the row group into the column group.** -/
theorem colSubgroup_transpose (t : YoungTableau μ) :
    colSubgroup (transpose t) = (rowSubgroup t).map
      (finCongr (YoungDiagram.card_transpose μ)).symm.permCongrHom.toMonoidHom := by
  ext σ
  rw [mem_colSubgroup_transpose, Subgroup.mem_map_equiv, Equiv.permCongrHom_symm,
    Equiv.symm_symm, Equiv.permCongrHom_coe]

/-! ## The sign automorphism on the symmetrizers -/

/-- **The sign automorphism sends the row symmetrizer of `t` to the column antisymmetrizer of
`tᵗ`**: `ε(a_t) = b_(tᵗ)`, the labels of `tᵗ` being read in `Fin μ.card`. -/
@[simp]
theorem signTwist_rowSymmetrizer (t : YoungTableau μ) :
    signTwist R _ (rowSymmetrizer t) =
      MonoidAlgebra.domCongr R R (finCongr (YoungDiagram.card_transpose μ)).permCongrHom
        (columnAntisymmetrizer (transpose t)) := by
  ext τ
  obtain ⟨σ, rfl⟩ := (finCongr (YoungDiagram.card_transpose μ)).permCongrHom.surjective τ
  rw [MonoidAlgebra.coeff_domCongr, MulEquiv.symm_apply_apply]
  simp only [coeff_signTwist, rowSymmetrizer_coeff, columnAntisymmetrizer_coeff,
    Equiv.permCongrHom_coe, Equiv.Perm.sign_permCongr]
  by_cases h : σ ∈ colSubgroup (transpose t)
  · simp [h, mem_colSubgroup_transpose.mp h]
  · simp [h, mt mem_colSubgroup_transpose.mpr h]

/-- **The sign automorphism sends the column antisymmetrizer of `t` to the row symmetrizer of
`tᵗ`**: `ε(b_t) = a_(tᵗ)`, the labels of `tᵗ` being read in `Fin μ.card`. -/
@[simp]
theorem signTwist_columnAntisymmetrizer (t : YoungTableau μ) :
    signTwist R _ (columnAntisymmetrizer t) =
      MonoidAlgebra.domCongr R R (finCongr (YoungDiagram.card_transpose μ)).permCongrHom
        (rowSymmetrizer (transpose t)) := by
  ext τ
  obtain ⟨σ, rfl⟩ := (finCongr (YoungDiagram.card_transpose μ)).permCongrHom.surjective τ
  rw [MonoidAlgebra.coeff_domCongr, MulEquiv.symm_apply_apply]
  simp only [coeff_signTwist, columnAntisymmetrizer_coeff, rowSymmetrizer_coeff,
    Equiv.permCongrHom_coe, Equiv.Perm.sign_permCongr]
  by_cases h : σ ∈ rowSubgroup (transpose t)
  · simp [h, mem_rowSubgroup_transpose.mp h, ← Int.cast_mul]
  · simp [h, mt mem_rowSubgroup_transpose.mpr h]

/-- **The sign automorphism sends the Young symmetrizer of `t` to the Young symmetrizer of `tᵗ`
with its factors in the opposite order**: `ε(c_t) = b_(tᵗ) a_(tᵗ)`, the labels of `tᵗ` being
read in `Fin μ.card`. -/
@[simp]
theorem signTwist_youngSymmetrizer (t : YoungTableau μ) :
    signTwist R _ (youngSymmetrizer t) =
      MonoidAlgebra.domCongr R R (finCongr (YoungDiagram.card_transpose μ)).permCongrHom
        (columnAntisymmetrizer (transpose t) * rowSymmetrizer (transpose t)) := by
  rw [youngSymmetrizer_def, map_mul, signTwist_rowSymmetrizer, signTwist_columnAntisymmetrizer,
    map_mul]

end YoungTableau

end TauCeti
