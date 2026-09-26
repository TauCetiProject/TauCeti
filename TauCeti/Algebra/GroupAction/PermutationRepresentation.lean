/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Ker
public import TauCeti.GroupTheory.Perm.PermCongr

/-!
# The permutation representation of a group action on an enumerated set

A group `G` acting on a set `α` with `n` elements permutes them, and choosing an enumeration
`e : α ≃ Fin n` turns that into a homomorphism `G →* Equiv.Perm (Fin n)`. This file is that
transport and the price of the choice.

The action on `α` is the intrinsic object and needs no choices. A symmetric group does not
appear until `e` is chosen, and the point is that the choice costs exactly one conjugation and
no more:

* the representation `permutationRepresentation e` depends on `e`;
* but `permutationRepresentation e'` is conjugate to it inside `Equiv.Perm (Fin n)`, by the
  re-indexing permutation `e.symm.trans e'` (`permutationRepresentation_eq_conj`), and the same
  holds of the images (`map_permutationRepresentation_range_conj`).

So the action is canonical, while the resulting subgroup of a particular symmetric group is
canonical only up to conjugacy. This is the same phenomenon as Mathlib's
`Polynomial.Gal.galActionHom`, which acts on `p.rootSet E` rather than on `Fin p.natDegree` for
the same reason.

`permutationRepresentation` needs no hypothesis. When the action is faithful it is injective,
and `permutationEmbedding` bundles that as the injection `G ↪ S_n` into the ambient symmetric
group; the isomorphism onto the image is `MonoidHom.ofInjective
(permutationRepresentation_injective e)`, which needs no wrapper here.

The motivating case is a Galois group permuting the embeddings of a field: `G = M ≃ₐ[F] M`
acting on `L →ₐ[F] M` by postcomposition (`TauCeti/Algebra/GroupAction/AlgHom.lean`), where
`TauCeti/FieldTheory/Normal/Embeddings.lean` supplies faithfulness from the generation
hypothesis as `faithfulSMul_of_normalClosure_eq_top`.

## Main results

* `Equiv.permutationRepresentation`: the representation `G →* Equiv.Perm (Fin n)` attached to an
  enumeration `e` of `α`.
* `Equiv.permutationRepresentation_apply`: it acts by `i ↦ e (g • e.symm i)`.
* `Equiv.permutationRepresentation_injective`: it is injective when the action is faithful.
* `Equiv.permutationEmbedding`: the injection `G ↪ Equiv.Perm (Fin n)`, with
  `Equiv.permutationEmbedding_apply` identifying its values.
* `Equiv.permutationRepresentation_eq_conj` and
  `Equiv.map_permutationRepresentation_range_conj`: replacing the enumeration conjugates the
  representation, and its image.

-/

public section

namespace Equiv

variable {G α : Type*} [Group G] [MulAction G α]
variable {n : ℕ}

/-- **The permutation representation of a group action, read through an enumeration `e`.** The
action on `α` is canonical; `e` only names the points. -/
def permutationRepresentation (e : α ≃ Fin n) : G →* Equiv.Perm (Fin n) :=
  (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom G α)

/-- **The transported permutation sends an index to the index of its translate**: `i` names the
point `e.symm i`, and its image names `g • e.symm i`. -/
@[simp]
theorem permutationRepresentation_apply (e : α ≃ Fin n) (g : G) (i : Fin n) :
    permutationRepresentation e g i = e (g • e.symm i) := by
  simp only [permutationRepresentation, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Equiv.permCongrHom_coe, Equiv.permCongr_apply, MulAction.toPermHom_apply,
    MulAction.toPerm_apply]

/-- **`G` embeds in `S_n`** when the action is faithful: an element acting trivially on the
enumerated points fixes every point, hence is the identity. -/
theorem permutationRepresentation_injective [FaithfulSMul G α] (e : α ≃ Fin n) :
    Function.Injective (permutationRepresentation (G := G) e) :=
  (e.permCongrHom.toEquiv.comp_injective _).2 MulAction.toPerm_injective

/-- **`G` injects into `S_n`**, for an enumeration `e` of the points and a faithful action on
them. A consumer wanting the isomorphism onto the image instead writes
`MonoidHom.ofInjective (permutationRepresentation_injective e)`. -/
def permutationEmbedding [FaithfulSMul G α] (e : α ≃ Fin n) : G ↪ Equiv.Perm (Fin n) :=
  ⟨permutationRepresentation e, permutationRepresentation_injective e⟩

/-- **The embedding acts as the representation.** -/
@[simp]
theorem permutationEmbedding_apply [FaithfulSMul G α] (e : α ≃ Fin n) (g : G) :
    permutationEmbedding e g = permutationRepresentation e g :=
  (rfl)

/-- **Replacing the enumeration conjugates the representation inside `S_n`**, by the re-indexing
permutation `e.symm.trans e'`. The subgroup of `Equiv.Perm (Fin n)` is therefore well defined
only up to conjugacy, while the action on `α` itself is canonical. -/
theorem permutationRepresentation_eq_conj (e e' : α ≃ Fin n) (g : G) :
    permutationRepresentation e' g =
      (e.symm.trans e') * permutationRepresentation e g * (e.symm.trans e')⁻¹ := by
  ext i
  simp [Equiv.Perm.mul_apply]

/-- **The represented subgroups of `S_n` are conjugate**, by the same re-indexing permutation.
This is the subgroup-level form of `permutationRepresentation_eq_conj`, and it is what makes
"canonical up to conjugacy" a statement about the image rather than about individual elements. -/
theorem map_permutationRepresentation_range_conj (e e' : α ≃ Fin n) :
    Subgroup.map (MulAut.conj (e.symm.trans e' : Equiv.Perm (Fin n)))
        (permutationRepresentation (G := G) e).range =
      (permutationRepresentation (G := G) e').range := by
  simp only [permutationRepresentation, ← MonoidHom.map_range]
  exact (Equiv.map_permCongrHom_eq_map_conj e e' _).symm

end Equiv

end
