/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.GeneralLinearGroup.nonzeroVectors` is the set permuted below, and its count is what
-- makes the permutation representation surjective here.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NonzeroVectors
-- `MulAction.toPermHom` occurs in the bijectivity statement below.
public import Mathlib.Algebra.Group.Action.End
-- `Equiv.permCongrHom` numbers the three nonzero vectors, in the final isomorphism.
public import Mathlib.Algebra.Group.End
-- Non-public: `TauCeti.natCard_GL_fin_two_of_card_eq_two` gives the order `6`, in one proof only.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card
-- Non-public: `Nat.card_perm` counts the permutations of a finite type, in one proof only.
import Mathlib.Data.Finite.Perm
-- Non-public: `Nat.card_units` gives the order of the unit group of a field, in one proof only.
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# `GL₂` over a field with two elements is the symmetric group on three letters

A plane over a field `F` with two elements has exactly three nonzero vectors, and `GL (Fin 2) F`
permutes them faithfully, by `Matrix.GeneralLinearGroup.faithfulSMulNonzeroVectors`. The
permutation representation is therefore an embedding into a group of order `3! = 6`, and it is an
isomorphism because `TauCeti.natCard_GL_fin_two` gives `|GL₂(F)| = (2 - 1)² · 2 · 3 = 6` as well.
Numbering the three vectors turns this into `GL₂(F) ≃* Equiv.Perm (Fin 3)`, that is `GL₂(𝔽₂) ≅ S₃`.

Recorded alongside it are the order `6` and the three conjugacy classes — the central class, the
unipotent class of the transvections and the elliptic class of the elements of order `3` — and the
triviality of `Fˣ`. The last is what makes this case of `GL₂` over a finite field small: with `Fˣ`
a single point there is no pair of distinct eigenvalues, so the regular split semisimple classes
and the irreducible principal series, both indexed by such pairs, are empty.

The character degrees `1, 1, 2` of the resulting character table are a statement about complex
representations and are not proved here; what is proved is the group isomorphism they are read
off, together with the order and the class count.

## Main definitions

* `TauCeti.gl2MulEquivPermNonzeroVectors`: over a field with two elements, `GL (Fin 2) F` is the
  symmetric group on the three nonzero vectors of the plane.
* `TauCeti.nonzeroVectorsEquivFinThree`: a numbering of those three nonzero vectors.
* `TauCeti.gl2MulEquivPermFinThree`: the resulting isomorphism `GL₂(𝔽₂) ≅ S₃`.

## Main results

* `TauCeti.subsingleton_units_of_card_eq_two`: a field with two elements has a trivial unit group.
* `TauCeti.natCard_nonzeroVectors_fin_two_of_card_eq_two`: the plane has three nonzero vectors.
* `TauCeti.toPermHom_nonzeroVectors_bijective_of_card_eq_two`: the permutation representation on
  them is bijective.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §5.
-/

public section

open Matrix

namespace TauCeti

open Matrix.GeneralLinearGroup

variable {F : Type*} [Field F] [Fintype F]

/-- **A field with two elements has a trivial unit group.** -/
theorem subsingleton_units_of_card_eq_two (hF : Fintype.card F = 2) : Subsingleton Fˣ := by
  have h : Nat.card Fˣ = 1 := by rw [Nat.card_units, Nat.card_eq_fintype_card, hF]
  exact (Nat.card_eq_one_iff_unique.1 h).1

/-- **A plane over a field with two elements has three nonzero vectors.** -/
theorem natCard_nonzeroVectors_fin_two_of_card_eq_two (hF : Fintype.card F = 2) :
    Nat.card (nonzeroVectors (Fin 2) F) = 3 := by
  rw [natCard_nonzeroVectors, Nat.card_eq_fintype_card, hF, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num

/-- **`GL₂` over a field with two elements permutes the three nonzero vectors of the plane
bijectively.** -/
theorem toPermHom_nonzeroVectors_bijective_of_card_eq_two (hF : Fintype.card F = 2) :
    Function.Bijective
      (MulAction.toPermHom (GL (Fin 2) F) (nonzeroVectors (Fin 2) F)) := by
  -- Injectivity is faithfulness; surjectivity is the coincidence `6 = 3!` of the two orders.
  refine (Nat.bijective_iff_injective_and_card _).2 ⟨MulAction.toPerm_injective, ?_⟩
  rw [natCard_GL_fin_two_of_card_eq_two hF, Nat.card_perm,
    natCard_nonzeroVectors_fin_two_of_card_eq_two hF]
  decide

/-- **`GL₂(𝔽₂)` is the symmetric group on the three nonzero vectors of `𝔽₂²`.** -/
noncomputable def gl2MulEquivPermNonzeroVectors (hF : Fintype.card F = 2) :
    GL (Fin 2) F ≃* Equiv.Perm (nonzeroVectors (Fin 2) F) :=
  MulEquiv.ofBijective _ (toPermHom_nonzeroVectors_bijective_of_card_eq_two hF)

@[simp]
theorem val_gl2MulEquivPermNonzeroVectors_apply (hF : Fintype.card F = 2) (g : GL (Fin 2) F)
    (v : nonzeroVectors (Fin 2) F) :
    ((gl2MulEquivPermNonzeroVectors hF g v : nonzeroVectors (Fin 2) F) : Fin 2 → F)
      = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ (v : Fin 2 → F) := by
  rw [gl2MulEquivPermNonzeroVectors, MulEquiv.ofBijective_apply, MulAction.toPermHom_apply,
    MulAction.toPerm_apply, SubMulAction.val_smul, Units.smul_def, Matrix.smul_eq_mulVec]

/-- **A numbering of the three nonzero vectors of a plane over a field with two elements.** The
numbering is an arbitrary choice; it is named so that the action of
`TauCeti.gl2MulEquivPermFinThree` can be stated. -/
noncomputable def nonzeroVectorsEquivFinThree (hF : Fintype.card F = 2) :
    nonzeroVectors (Fin 2) F ≃ Fin 3 :=
  Finite.equivFinOfCardEq (natCard_nonzeroVectors_fin_two_of_card_eq_two hF)

/-- **`GL₂(𝔽₂) ≅ S₃`.** Over a field with two elements the general linear group in size two is
the symmetric group on three letters, obtained from `TauCeti.gl2MulEquivPermNonzeroVectors` by
numbering the three nonzero vectors along `TauCeti.nonzeroVectorsEquivFinThree`. -/
noncomputable def gl2MulEquivPermFinThree (hF : Fintype.card F = 2) :
    GL (Fin 2) F ≃* Equiv.Perm (Fin 3) :=
  (gl2MulEquivPermNonzeroVectors hF).trans
    (Equiv.permCongrHom (nonzeroVectorsEquivFinThree hF))

@[simp]
theorem gl2MulEquivPermFinThree_apply (hF : Fintype.card F = 2) (g : GL (Fin 2) F) (i : Fin 3) :
    gl2MulEquivPermFinThree hF g i =
      nonzeroVectorsEquivFinThree hF
        (gl2MulEquivPermNonzeroVectors hF g ((nonzeroVectorsEquivFinThree hF).symm i)) := by
  rw [gl2MulEquivPermFinThree, MulEquiv.trans_apply, Equiv.permCongrHom_coe,
    Equiv.permCongr_apply]

end TauCeti
