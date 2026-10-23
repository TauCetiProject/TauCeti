/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.nonzeroVectors` is the set permuted below, and its count is what makes the permutation
-- representation surjective here.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NonzeroVectors
-- `MulAction.toPermHom` occurs in the bijectivity statement below.
public import Mathlib.Algebra.Group.Action.End
-- `Equiv.permCongrHom` numbers the three nonzero vectors, in the final isomorphism.
public import Mathlib.Algebra.Group.End
-- Non-public: `TauCeti.natCard_GL_fin_two_of_card_eq_two` gives the order `6`, in one proof only.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card
-- Non-public: `Nat.card_perm` counts the permutations of a finite type, in one proof only.
import Mathlib.Data.Finite.Perm

/-!
# `GL₂` over a field with two elements is the symmetric group on three letters

A plane over a field `F` with two elements has exactly three nonzero vectors, and `GL (Fin 2) F`
permutes them faithfully, by `TauCeti.faithfulSMulNonzeroVectors`. The permutation representation
is therefore an embedding into a group of order `3! = 6`, and it is an isomorphism because
`TauCeti.natCard_GL_fin_two` gives `|GL₂(F)| = (2 - 1)² · 2 · 3 = 6` as well. Numbering the three
vectors turns this into `GL₂(F) ≃* Equiv.Perm (Fin 3)`, that is `GL₂(𝔽₂) ≅ S₃`.

Declared here are the bijectivity of the permutation representation, the isomorphism it gives and
the resulting isomorphism onto `Equiv.Perm (Fin 3)`. The count and numbering of the three nonzero
vectors are in `TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/NonzeroVectors.lean` and hold over
any semiring with two elements. Three further facts about this degenerate case are stated
with the general results they specialize rather than here: the order `6` is
`TauCeti.natCard_GL_fin_two_of_card_eq_two` in
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean`, the three conjugacy classes — the
central class, the unipotent class of the transvections and the elliptic class of the elements of
order `3` — are counted by `TauCeti.natCard_conjClasses_GL_fin_two_of_card_eq_two` in
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/ConjugacyClasses.lean`, and the triviality of
`Fˣ` is `TauCeti.subsingleton_units_of_natCard_eq_two` in
`TauCeti/Algebra/GroupWithZero/Units/Basic.lean`. The last is what makes this case of `GL₂` over a
finite field small: with `Fˣ` a single point there is no pair of distinct eigenvalues, so the
regular split semisimple classes and the irreducible principal series, both indexed by such pairs,
are empty.

The character degrees `1, 1, 2` of the resulting character table are a statement about complex
representations and are not proved here; what is proved is the group isomorphism they are read
off, together with the order and the class count cited above.

## Main definitions

* `TauCeti.gl2MulEquivPermNonzeroVectors`: over a field with two elements, `GL (Fin 2) F` is the
  symmetric group on the three nonzero vectors of the plane.
* `TauCeti.gl2MulEquivPermFinThree`: the resulting isomorphism `GL₂(𝔽₂) ≅ S₃`.

## Main results

* `TauCeti.toPermHom_nonzeroVectors_bijective_of_card_eq_two`: the permutation representation on
  them is bijective.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §5.
-/

public section

open Matrix

namespace TauCeti

variable {F : Type*} [Field F]

/-- **Over a field with two elements, `MulAction.toPermHom` is a bijection of `GL₂` onto the whole
permutation group of the three nonzero vectors of the plane.** Every one of the six permutations of
those vectors is the action of exactly one matrix: the homomorphism is injective because the action
is faithful, and surjective because the two groups both have order `6`. -/
theorem toPermHom_nonzeroVectors_bijective_of_card_eq_two (hF : Nat.card F = 2) :
    Function.Bijective
      (MulAction.toPermHom (GL (Fin 2) F) (nonzeroVectors (Fin 2) F)) := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  -- Injectivity is faithfulness; surjectivity is the coincidence `6 = 3!` of the two orders.
  refine (Nat.bijective_iff_injective_and_card _).2 ⟨MulAction.toPerm_injective, ?_⟩
  rw [natCard_GL_fin_two_of_card_eq_two hF, Nat.card_perm,
    natCard_nonzeroVectors_fin_two_of_card_eq_two hF]
  decide

/-- **`GL₂(𝔽₂)` is the symmetric group on the three nonzero vectors of `𝔽₂²`.** -/
noncomputable def gl2MulEquivPermNonzeroVectors (hF : Nat.card F = 2) :
    GL (Fin 2) F ≃* Equiv.Perm (nonzeroVectors (Fin 2) F) :=
  MulEquiv.ofBijective _ (toPermHom_nonzeroVectors_bijective_of_card_eq_two hF)

/-- **The action identified by `TauCeti.gl2MulEquivPermNonzeroVectors`**: the permutation attached
to `g` carries a nonzero vector `v` to `g *ᵥ v`. -/
@[simp]
theorem val_gl2MulEquivPermNonzeroVectors_apply (hF : Nat.card F = 2) (g : GL (Fin 2) F)
    (v : nonzeroVectors (Fin 2) F) :
    ((gl2MulEquivPermNonzeroVectors hF g v : nonzeroVectors (Fin 2) F) : Fin 2 → F)
      = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ (v : Fin 2 → F) := by
  simp [gl2MulEquivPermNonzeroVectors, Units.smul_def, Matrix.smul_eq_mulVec]

/-- **`GL₂(𝔽₂) ≅ S₃`.** Over a field with two elements the general linear group in size two is
the symmetric group on three letters, obtained from `TauCeti.gl2MulEquivPermNonzeroVectors` by
numbering the three nonzero vectors along `TauCeti.nonzeroVectorsEquivFinThree`. -/
noncomputable def gl2MulEquivPermFinThree (hF : Nat.card F = 2) :
    GL (Fin 2) F ≃* Equiv.Perm (Fin 3) :=
  (gl2MulEquivPermNonzeroVectors hF).trans
    (Equiv.permCongrHom (nonzeroVectorsEquivFinThree hF))

/-- **The action identified by `TauCeti.gl2MulEquivPermFinThree`**: on `Fin 3` it is the
permutation of the nonzero vectors attached to `g`, conjugated along the numbering
`TauCeti.nonzeroVectorsEquivFinThree`. -/
@[simp]
theorem gl2MulEquivPermFinThree_apply (hF : Nat.card F = 2) (g : GL (Fin 2) F) (i : Fin 3) :
    gl2MulEquivPermFinThree hF g i =
      nonzeroVectorsEquivFinThree hF
        (gl2MulEquivPermNonzeroVectors hF g ((nonzeroVectorsEquivFinThree hF).symm i)) := by
  simp [gl2MulEquivPermFinThree, Equiv.permCongr_apply]

end TauCeti
