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
* `TauCeti.YoungTableau.signTransposeAlgEquiv`: the same identities read as an isomorphism
  `ψ` of group algebras from the labels of `μ` to those of `μᵗ`, which is free of transports:
  `ψ(a_t) = b_(tᵗ)`, `ψ(b_t) = a_(tᵗ)`, and `ψ ∘ ψ` is the relabelling from `μ` to `μᵗᵗ`.

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

/-! ## The sign-transpose isomorphism of group algebras -/

variable (R) in
/-- The **sign-transpose isomorphism** `ψ` from `R[Sₙ]` on the labels of `μ` to `R[Sₙ]` on the
labels of `μᵗ`: the sign automorphism followed by the identification of the two label sets, so
that `ψ(σ) = sgn(σ) σ`.  It exchanges row symmetrizers and column antisymmetrizers. -/
noncomputable def signTransposeAlgEquiv (μ : YoungDiagram) :
    MonoidAlgebra R (Equiv.Perm (Fin μ.card)) ≃ₐ[R]
      MonoidAlgebra R (Equiv.Perm (Fin μ.transpose.card)) :=
  (signTwist R _).trans
    (MonoidAlgebra.domCongr R R (finCongr (YoungDiagram.card_transpose μ)).permCongrHom).symm

/-- The sign-transpose isomorphism multiplies `σ` by its sign and reads it on the labels of
`μᵗ`. -/
@[simp]
theorem signTransposeAlgEquiv_single (σ : Equiv.Perm (Fin μ.card)) (r : R) :
    signTransposeAlgEquiv R μ (MonoidAlgebra.single σ r) =
      MonoidAlgebra.single ((finCongr (YoungDiagram.card_transpose μ).symm).permCongrHom σ)
        (((Equiv.Perm.sign σ : ℤ) : R) * r) := by
  rw [signTransposeAlgEquiv, AlgEquiv.trans_apply, signTwist_single, MonoidAlgebra.domCongr_symm,
    MonoidAlgebra.domCongr_single]
  -- the inverse of conjugation along `finCongr h` is conjugation along `finCongr h.symm`
  rfl

/-- The sign-transpose isomorphism carries `sgn(g) g` to `g`, read on the labels of `μᵗ`. -/
theorem signTransposeAlgEquiv_sign_smul_single (g : Equiv.Perm (Fin μ.card)) :
    signTransposeAlgEquiv R μ (((Equiv.Perm.sign g : ℤ) : R) • MonoidAlgebra.single g 1) =
      MonoidAlgebra.single ((finCongr (YoungDiagram.card_transpose μ).symm).permCongrHom g) 1 := by
  rw [map_smul, signTransposeAlgEquiv_single, MonoidAlgebra.smul_single, smul_eq_mul, mul_one,
    ← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]

/-- **The sign-transpose isomorphism sends the row symmetrizer of `t` to the column antisymmetrizer
of `tᵗ`**: `ψ(a_t) = b_(tᵗ)`. -/
@[simp]
theorem signTransposeAlgEquiv_rowSymmetrizer (t : YoungTableau μ) :
    signTransposeAlgEquiv R μ (rowSymmetrizer t) = columnAntisymmetrizer (transpose t) := by
  rw [signTransposeAlgEquiv, AlgEquiv.trans_apply, signTwist_rowSymmetrizer,
    AlgEquiv.symm_apply_apply]

/-- **The sign-transpose isomorphism sends the column antisymmetrizer of `t` to the row symmetrizer
of `tᵗ`**: `ψ(b_t) = a_(tᵗ)`. -/
@[simp]
theorem signTransposeAlgEquiv_columnAntisymmetrizer (t : YoungTableau μ) :
    signTransposeAlgEquiv R μ (columnAntisymmetrizer t) = rowSymmetrizer (transpose t) := by
  rw [signTransposeAlgEquiv, AlgEquiv.trans_apply, signTwist_columnAntisymmetrizer,
    AlgEquiv.symm_apply_apply]

/-- **The sign-transpose isomorphism sends the Young symmetrizer of `t` to the Young symmetrizer of
`tᵗ` with its factors in the opposite order**: `ψ(c_t) = b_(tᵗ) a_(tᵗ)`. -/
@[simp]
theorem signTransposeAlgEquiv_youngSymmetrizer (t : YoungTableau μ) :
    signTransposeAlgEquiv R μ (youngSymmetrizer t) =
      columnAntisymmetrizer (transpose t) * rowSymmetrizer (transpose t) := by
  rw [youngSymmetrizer_def, map_mul, signTransposeAlgEquiv_rowSymmetrizer,
    signTransposeAlgEquiv_columnAntisymmetrizer]

/-- **Applying the sign-transpose isomorphism twice cancels the signs**, leaving the identification
of the labels of `μ` with those of `μᵗᵗ`. -/
theorem signTransposeAlgEquiv_transpose_apply (x : MonoidAlgebra R (Equiv.Perm (Fin μ.card))) :
    signTransposeAlgEquiv R μ.transpose (signTransposeAlgEquiv R μ x) =
      MonoidAlgebra.domCongr R R
        (finCongr ((YoungDiagram.card_transpose μ).symm.trans
          (YoungDiagram.card_transpose μ.transpose).symm)).permCongrHom x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single σ r =>
    simp only [signTransposeAlgEquiv_single, MonoidAlgebra.domCongr_single,
      Equiv.permCongrHom_coe, Equiv.Perm.sign_permCongr, ← mul_assoc, ← Int.cast_mul,
      Int.units_coe_mul_self, Int.cast_one, one_mul]
    -- conjugating along two casts in turn is conjugating along their composite
    congr 1

end YoungTableau

end TauCeti
