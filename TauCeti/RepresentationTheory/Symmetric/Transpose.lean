/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Symmetrizer

/-!
# The sign automorphism and the transposed tableau

Transposing a `μ`-tableau `t` (`TauCeti.YoungTableau.transpose`) exchanges its rows and its
columns, so it exchanges the row group and the column group of `t`
(`TauCeti.YoungTableau.rowSubgroup_transpose`, `TauCeti.YoungTableau.colSubgroup_transpose`). In
the group algebra `R[Sₙ]` the **sign automorphism** `ε = TauCeti.signTwist`, `σ ↦ sgn(σ) σ`, turns
the sum over a group into the signed sum over the same group and back. Together these give the
identities

`ε(a_t) = b_(tᵗ)`, `ε(b_t) = a_(tᵗ)`, hence `ε(c_t) = b_(tᵗ) a_(tᵗ)`,

between the row symmetrizer `a_t`, the column antisymmetrizer `b_t` and the Young symmetrizer
`c_t = a_t b_t` of `t` and the corresponding elements of `tᵗ`. The last one is the Young
symmetrizer of `tᵗ` with its two factors in the opposite order. These identities are the starting
point of the comparison of the Specht module of `λ`, twisted by the sign representation, with the
Specht module of the transposed shape.

The labels of `tᵗ` are `Fin μᵗ.card`, not `Fin μ.card`; the two symmetric groups are identified
by `Equiv.permCongrHom` along `finCongr (YoungDiagram.card_transpose μ)`, and the group algebras
by `MonoidAlgebra.domCongr` of that isomorphism.

## Main results

* `TauCeti.YoungTableau.signTwist_rowSymmetrizer`,
  `TauCeti.YoungTableau.signTwist_columnAntisymmetrizer` and
  `TauCeti.YoungTableau.signTwist_youngSymmetrizer`: `ε(a_t) = b_(tᵗ)`, `ε(b_t) = a_(tᵗ)` and
  `ε(c_t) = b_(tᵗ) a_(tᵗ)`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 4, §4.1.
-/

public section

namespace TauCeti

namespace YoungTableau

variable {R : Type*} [CommRing R] {μ : YoungDiagram}

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
