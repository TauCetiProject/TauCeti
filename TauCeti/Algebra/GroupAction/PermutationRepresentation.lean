/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.GroupTheory.Perm.PermCongr

/-!
# Transporting a group action to a permutation representation

A group `G` acting on a set `α` gives a homomorphism `G →* Equiv.Perm α`. Choosing an
equivalence `e : α ≃ β` transports this homomorphism to `G →* Equiv.Perm β`. In particular,
an enumeration by `Fin n` gives the usual representation in the symmetric group on `n` points.

The action on `α` is the intrinsic object and needs no choices. Renaming its points by `e`
changes the transported representation by exactly one conjugation:

* the representation `permutationRepresentation e` depends on `e`;
* but `permutationRepresentation e'` is conjugate to it inside `Equiv.Perm β`, by the
  re-indexing permutation `e.symm.trans e'` (`permutationRepresentation_eq_conj`), and the same
  holds of the images (`map_permutationRepresentation_range_conj`).

So the action is canonical, while the resulting subgroup of a particular symmetric group is
canonical only up to conjugacy. This is the same phenomenon as Mathlib's
`Polynomial.Gal.galActionHom`, which acts on `p.rootSet E` rather than on `Fin p.natDegree` for
the same reason.

`permutationRepresentation` needs no hypothesis. When the action is faithful it is injective,
and `permutationEmbedding` bundles that as the injection into the ambient
symmetric group `G ↪ Equiv.Perm β`; the isomorphism onto the image is `MonoidHom.ofInjective
(permutationRepresentation_injective e)`, which needs no wrapper here.

The motivating case is a Galois group permuting the embeddings of a field: `G = M ≃ₐ[F] M`
acting on `L →ₐ[F] M` by postcomposition (`TauCeti/Algebra/GroupAction/AlgHom.lean`), where
`TauCeti/FieldTheory/Normal/Embeddings.lean` supplies faithfulness from the generation
hypothesis as `faithfulSMul_of_normalClosure_eq_top`.

## Main results

* `Equiv.permutationRepresentation`: the representation `G →* Equiv.Perm β` attached to an
  equivalence `e : α ≃ β`.
* `Equiv.permutationRepresentation_apply`: it acts by `i ↦ e (g • e.symm i)`.
* `Equiv.permutationRepresentation_injective`: it is injective when the action is faithful.
* `Equiv.natCard_permutationRepresentation_range`: a faithful action has an image with the
  cardinality of the acting group.
* `Equiv.permutationEmbedding`: the injection `G ↪ Equiv.Perm β`, with
  `Equiv.permutationEmbedding_apply` identifying its values.
* `Equiv.permutationRepresentation_eq_conj` and
  `Equiv.map_permutationRepresentation_range_conj`: replacing the equivalence conjugates the
  representation, and its image.
* `Equiv.permutationRepresentation_eq_of_map_smul`: an equivalence carrying the action to a
  given homomorphism `ρ : G →* Equiv.Perm β` recovers `ρ`.
* `Equiv.ker_permutationRepresentation`, `Equiv.comap_stabilizer_permutationRepresentation` and
  `Equiv.isPretransitive_range_permutationRepresentation_iff`: the kernel, the point stabilisers
  and the transitivity of the representation are those of the action.

-/

public section

namespace Equiv

variable {G α β : Type*} [Group G] [MulAction G α]

/-- **The permutation representation of a group action, read through an equivalence `e`.** The
action on `α` is canonical; `e` only names the points. -/
def permutationRepresentation (e : α ≃ β) : G →* Equiv.Perm β :=
  (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom G α)

/-- **The transported permutation sends an index to the index of its translate**: `i` names the
point `e.symm i`, and its image names `g • e.symm i`. -/
@[simp]
theorem permutationRepresentation_apply (e : α ≃ β) (g : G) (i : β) :
    permutationRepresentation e g i = e (g • e.symm i) := by
  simp only [permutationRepresentation, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Equiv.permCongrHom_coe, Equiv.permCongr_apply, MulAction.toPermHom_apply,
    MulAction.toPerm_apply]

/-- **`G` embeds in `Equiv.Perm β`** when the action is faithful: an element acting trivially on the
enumerated points fixes every point, hence is the identity. -/
theorem permutationRepresentation_injective [FaithfulSMul G α] (e : α ≃ β) :
    Function.Injective (permutationRepresentation (G := G) e) :=
  (e.permCongrHom.toEquiv.comp_injective _).2 MulAction.toPerm_injective

/-- A faithful action has an image with the same cardinality as the acting group. -/
@[simp]
theorem natCard_permutationRepresentation_range [FaithfulSMul G α] (e : α ≃ β) :
    Nat.card (permutationRepresentation (G := G) e).range = Nat.card G :=
  (Nat.card_congr
    (MonoidHom.ofInjective (permutationRepresentation_injective (G := G) e)).toEquiv).symm

/-- **`G` injects into `Equiv.Perm β`**, for an equivalence `e` of the points and a faithful
action on them. A consumer wanting the isomorphism onto the image instead writes
`MonoidHom.ofInjective (permutationRepresentation_injective e)`. -/
def permutationEmbedding [FaithfulSMul G α] (e : α ≃ β) : G ↪ Equiv.Perm β :=
  ⟨permutationRepresentation e, permutationRepresentation_injective e⟩

/-- **The embedding acts as the representation.** -/
@[simp]
theorem permutationEmbedding_apply [FaithfulSMul G α] (e : α ≃ β) (g : G) :
    permutationEmbedding e g = permutationRepresentation e g :=
  (rfl)

/-- **Replacing the equivalence conjugates the representation**, by the re-indexing permutation
`e.symm.trans e'`. The subgroup of `Equiv.Perm β` is therefore well defined only up to conjugacy, while the action on `α` itself is canonical. -/
theorem permutationRepresentation_eq_conj (e e' : α ≃ β) (g : G) :
    permutationRepresentation e' g =
      (e.symm.trans e') * permutationRepresentation e g * (e.symm.trans e')⁻¹ := by
  ext i
  simp [Equiv.Perm.mul_apply]

/-- **The represented subgroups of `Equiv.Perm β` are conjugate**, by the same re-indexing
permutation.
This is the subgroup-level form of `permutationRepresentation_eq_conj`, and it is what makes
"canonical up to conjugacy" a statement about the image rather than about individual elements. -/
theorem map_permutationRepresentation_range_conj (e e' : α ≃ β) :
    Subgroup.map (MulAut.conj (e.symm.trans e' : Equiv.Perm β))
        (permutationRepresentation (G := G) e).range =
      (permutationRepresentation (G := G) e').range := by
  simp only [permutationRepresentation, ← MonoidHom.map_range]
  exact (Equiv.map_permCongrHom_eq_map_conj e e' _).symm

/-- **An equivariant enumeration recovers the representation.** If `e` carries the action of `G`
on `α` to the action of `G` on `β` through `ρ`, then `ρ` is the permutation representation
read through `e`. -/
theorem permutationRepresentation_eq_of_map_smul (e : α ≃ β) {ρ : G →* Equiv.Perm β}
    (he : ∀ (g : G) (x : α), e (g • x) = ρ g (e x)) : permutationRepresentation e = ρ := by
  ext g i
  simp [he]

/-- **The kernel does not depend on the equivalence**: it is the kernel of the action. -/
@[simp]
theorem ker_permutationRepresentation (e : α ≃ β) :
    (permutationRepresentation (G := G) e).ker = (MulAction.toPermHom G α).ker :=
  MonoidHom.ker_comp_of_injective _ _ (Equiv.permCongrHom e).injective

/-- **The point stabilisers of the representation are those of the action**: the stabiliser of
the index `e x` pulls back to the stabiliser of `x`. -/
@[simp]
theorem comap_stabilizer_permutationRepresentation (e : α ≃ β) (x : α) :
    (MulAction.stabilizer (Equiv.Perm β) (e x)).comap
        (permutationRepresentation (G := G) e) =
      MulAction.stabilizer G x := by
  ext g
  simp [MulAction.mem_stabilizer_iff]

/-- **The representation is transitive exactly when the action is.** -/
@[simp]
theorem isPretransitive_range_permutationRepresentation_iff (e : α ≃ β) :
    MulAction.IsPretransitive (permutationRepresentation (G := G) e).range (β) ↔
      MulAction.IsPretransitive G α := by
  rw [permutationRepresentation, MonoidHom.range_comp, Equiv.isPretransitive_map_permCongrHom_iff,
    MulAction.isPretransitive_range_toPermHom_iff]

end Equiv

end
