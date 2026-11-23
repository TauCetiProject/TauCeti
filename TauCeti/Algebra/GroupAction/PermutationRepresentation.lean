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

Nothing in the construction uses that the target is `Fin n`, so it is stated for any bijection
`e : α ≃ β`; the enumerations `e : α ≃ Fin n` are the motivating case.

`permutationRepresentation` needs no hypothesis. When the action is faithful it is injective,
and `permutationEmbedding` bundles that as the injection `G ↪ S_n` into the ambient symmetric
group; the isomorphism onto the image is `MonoidHom.ofInjective
(permutationRepresentation_injective e)`, which needs no wrapper here.

The motivating case is a Galois group permuting the embeddings of a field: `G = M ≃ₐ[F] M`
acting on `L →ₐ[F] M` by postcomposition (`TauCeti/Algebra/GroupAction/AlgHom.lean`), where
`TauCeti/FieldTheory/Normal/Embeddings.lean` supplies faithfulness from the generation
hypothesis as `faithfulSMul_of_normalClosure_eq_top`.

## Main results

* `Equiv.permutationRepresentation`: the representation `G →* Equiv.Perm β` attached to a
  bijection `e : α ≃ β`, such as an enumeration of `α`.
* `Equiv.permutationRepresentation_apply`: it acts by `i ↦ e (g • e.symm i)`.
* `Equiv.permutationRepresentation_injective`: it is injective when the action is faithful.
* `Equiv.permutationEmbedding`: the injection `G ↪ Equiv.Perm β`, with
  `Equiv.permutationEmbedding_apply` identifying its values.
* `Equiv.permutationRepresentation_eq_conj` and
  `Equiv.map_permutationRepresentation_range_conj`: replacing the enumeration conjugates the
  representation, and its image.
* `Equiv.permutationRepresentation_eq_of_map_smul`: an enumeration carrying the action to a
  given homomorphism `ρ : G →* Equiv.Perm β` recovers `ρ`.
* `Equiv.ker_permutationRepresentation`, `Equiv.comap_stabilizer_permutationRepresentation` and
  `Equiv.isPretransitive_range_permutationRepresentation_iff`: the kernel, the point stabilisers
  and the transitivity of the representation are those of the action.
* `Equiv.natCard_range_permutationRepresentation`: a faithful representation has as many elements
  as `G`.
* `Equiv.not_exists_map_conj_range_permutationRepresentation_eq`: faithful representations of a
  commutative and a non-commutative group have non-conjugate images.

-/

public section

namespace Equiv

variable {G α : Type*} [Group G] [MulAction G α]
variable {β : Type*}

/-- **The permutation representation of a group action, read through an enumeration `e`.** The
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

/-- **`G` embeds in `Equiv.Perm β`** when the action is faithful: an element acting trivially on
the enumerated points fixes every point, hence is the identity. -/
theorem permutationRepresentation_injective [FaithfulSMul G α] (e : α ≃ β) :
    Function.Injective (permutationRepresentation (G := G) e) :=
  (e.permCongrHom.toEquiv.comp_injective _).2 MulAction.toPerm_injective

/-- **`G` injects into `Equiv.Perm β`**, for an enumeration `e` of the points and a faithful
action on them. A consumer wanting the isomorphism onto the image instead writes
`MonoidHom.ofInjective (permutationRepresentation_injective e)`. -/
def permutationEmbedding [FaithfulSMul G α] (e : α ≃ β) : G ↪ Equiv.Perm β :=
  ⟨permutationRepresentation e, permutationRepresentation_injective e⟩

/-- **The embedding acts as the representation.** -/
@[simp]
theorem permutationEmbedding_apply [FaithfulSMul G α] (e : α ≃ β) (g : G) :
    permutationEmbedding e g = permutationRepresentation e g :=
  (rfl)

/-- **Replacing the enumeration conjugates the representation inside `Equiv.Perm β`**, by the
re-indexing permutation `e.symm.trans e'`. The subgroup of `Equiv.Perm β` is therefore well
defined only up to conjugacy, while the action on `α` itself is canonical. -/
theorem permutationRepresentation_eq_conj (e e' : α ≃ β) (g : G) :
    permutationRepresentation e' g =
      (e.symm.trans e') * permutationRepresentation e g * (e.symm.trans e')⁻¹ := by
  ext i
  simp [Equiv.Perm.mul_apply]

/-- **The represented subgroups of `Equiv.Perm β` are conjugate**, by the same re-indexing
permutation. This is the subgroup-level form of `permutationRepresentation_eq_conj`, and it is
what makes "canonical up to conjugacy" a statement about the image rather than about individual
elements. -/
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

/-- **The kernel does not depend on the enumeration**: it is the kernel of the action. -/
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

/-- **A faithful representation has as many elements as `G`**, since it is injective. -/
theorem natCard_range_permutationRepresentation [FaithfulSMul G α] (e : α ≃ β) :
    Nat.card (permutationRepresentation (G := G) e).range = Nat.card G :=
  (Nat.card_congr (MonoidHom.ofInjective (permutationRepresentation_injective e)).toEquiv).symm

/-- **Faithful representations of a commutative and a non-commutative group are not conjugate.** A
conjugate of the image of the commutative group `G` is commutative, while the image of `Γ` is
isomorphic to `Γ`. -/
theorem not_exists_map_conj_range_permutationRepresentation_eq {Γ α' : Type*} [Group Γ]
    [MulAction Γ α'] [FaithfulSMul Γ α'] [IsMulCommutative G] (e : α ≃ β) (f : α' ≃ β)
    (hΓ : ¬ IsMulCommutative Γ) :
    ¬ ∃ σ : Perm β, (permutationRepresentation (G := G) e).range.map (MulAut.conj σ) =
      (permutationRepresentation (G := Γ) f).range := by
  rintro ⟨σ, hσ⟩
  have hK : IsMulCommutative (permutationRepresentation (G := Γ) f).range := by
    rw [← hσ]
    infer_instance
  refine hΓ (isMulCommutative_iff.mpr fun a b ↦ permutationRepresentation_injective f ?_)
  simpa only [map_mul, Subgroup.coe_mul] using congrArg Subtype.val
    (isMulCommutative_iff.mp hK ⟨_, a, rfl⟩ ⟨_, b, rfl⟩)

end Equiv

end
