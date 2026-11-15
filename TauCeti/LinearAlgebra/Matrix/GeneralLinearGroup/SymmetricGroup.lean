/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `OnePoint F` with the Möbius action of `GL (Fin 2) F` is the model of the projective line used
-- here, and `OnePoint.smul_infty_eq_self_iff` and `OnePoint.smul_some_eq_ite` compute that action.
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
-- `TauCeti.ker_toPermHom_onePoint_eq_center`, the kernel of the permutation representation, is what
-- the counts below specialize to the field with two elements.
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine
-- `Matrix.GeneralLinearGroup.scalar` occurs in the statements below, and
-- `Matrix.GeneralLinearGroup.center_eq_range_scalar` identifies the centre with its range.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
-- Non-public: `TauCeti.natCard_GL_fin_two` and `TauCeti.natCard_onePoint` are the two orders
-- compared in the proof that the permutation representation is surjective.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import TauCeti.Topology.Compactification.OnePoint.Card

/-!
# `GL₂` as a symmetric group on the projective line

`GL₂(F)` permutes the projective line `OnePoint F` by Möbius transformations
(`OnePoint.instGLAction`), and a matrix acts trivially exactly when it is scalar, so the kernel of
the permutation representation is the centre; that is
`TauCeti.ker_toPermHom_onePoint_eq_center`, with the rest of the projective-line API in
`TauCeti.Topology.Compactification.OnePoint.ProjectiveLine`.

Over the field with two elements the only unit is `1`, so the centre is trivial and the action is
faithful. The projective line then has three points and `GL₂(F)` has order `6`, so the
representation is also surjective: `GL₂(𝔽₂)` *is* the symmetric group on the three points of the
projective line (`TauCeti.glFinTwoMulEquivPermOnePoint`), and in particular is isomorphic to `S₃`
(`TauCeti.nonempty_mulEquiv_permFinThree`). The isomorphism with the permutations of `OnePoint F`
is canonical; an isomorphism with `Equiv.Perm (Fin 3)` instead depends on an enumeration of the
three points, so of that one only the existence is stated.

The fixed points of a single element of `GL₂(F)` on the projective line, which is the other half of
this picture, are counted in
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/ProjectiveLine.lean`.

## Main results

* `TauCeti.glFinTwoMulEquivPermOnePoint`: over a field with two elements, `GL₂(F)` is the full
  symmetric group on the projective line.
* `TauCeti.nonempty_mulEquiv_permFinThree`: `GL₂(𝔽₂) ≅ S₃`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Springer GTM 7 (1973), Chapter VII, for the action of
  `GL₂` on the projective line.
-/

public section

namespace TauCeti

open Matrix OnePoint

variable {F : Type*} [Field F] [DecidableEq F]

variable [Fintype F]

/-- **Over the field with two elements the Möbius action is faithful**: the only unit of `F` is
`1`, so the centre of `GL₂(F)` is trivial. -/
theorem injective_toPermHom_onePoint_of_card_eq_two (hF : Fintype.card F = 2) :
    Function.Injective (MulAction.toPermHom (GL (Fin 2) F) (OnePoint F)) := by
  have hunit : Subsingleton Fˣ := by
    rw [← Finite.card_le_one_iff_subsingleton, Nat.card_eq_fintype_card, Fintype.card_units, hF]
  rw [← MonoidHom.ker_eq_bot_iff, ker_toPermHom_onePoint_eq_center, eq_bot_iff]
  intro g hg
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range] at hg
  obtain ⟨u, rfl⟩ := hg
  rw [Subgroup.mem_bot, Subsingleton.elim u 1, map_one]

/-- **`GL₂` over the field with two elements is the full symmetric group on the projective line.**
The action is faithful because the centre is trivial, and surjective because both groups have
order `6`. -/
noncomputable def glFinTwoMulEquivPermOnePoint (hF : Fintype.card F = 2) :
    GL (Fin 2) F ≃* Equiv.Perm (OnePoint F) :=
  MulEquiv.ofBijective (MulAction.toPermHom (GL (Fin 2) F) (OnePoint F)) <|
    (Nat.bijective_iff_injective_and_card _).2 ⟨injective_toPermHom_onePoint_of_card_eq_two hF, by
      rw [natCard_GL_fin_two, Nat.card_perm, natCard_onePoint, Nat.card_eq_fintype_card, hF]
      norm_num [Nat.factorial]⟩

/-- The isomorphism acts by the Möbius action. -/
@[simp]
theorem glFinTwoMulEquivPermOnePoint_apply (hF : Fintype.card F = 2) (g : GL (Fin 2) F)
    (x : OnePoint F) : glFinTwoMulEquivPermOnePoint hF g x = g • x :=
  (rfl)

omit [DecidableEq F] in
/-- **`GL₂(𝔽₂) ≅ S₃`.** The projective line over a field with two elements has three points, so
the symmetric group on it is `S₃`; an isomorphism depends on an enumeration of those points, so
only its existence is stated. The canonical isomorphism is
`TauCeti.glFinTwoMulEquivPermOnePoint`. -/
theorem nonempty_mulEquiv_permFinThree (hF : Fintype.card F = 2) :
    Nonempty (GL (Fin 2) F ≃* Equiv.Perm (Fin 3)) := by
  classical
  exact ⟨(glFinTwoMulEquivPermOnePoint hF).trans (Equiv.permCongrHom
    (Fintype.equivFinOfCardEq (α := OnePoint F) (by
      rw [← Nat.card_eq_fintype_card, natCard_onePoint, Nat.card_eq_fintype_card, hF])))⟩

end TauCeti
