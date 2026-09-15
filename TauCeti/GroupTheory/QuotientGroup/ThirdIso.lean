/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The third isomorphism theorem for coset spaces

For a normal subgroup `N` of `G` and an **arbitrary** subgroup `H`, the cosets of the image
`H·N/N` in `G ⧸ N` are the cosets of `H ⊔ N` in `G`. This is Noether's third isomorphism
theorem with the normality of the upper subgroup dropped: `H` is unconstrained, so neither
`(G ⧸ N) ⧸ H·N/N` nor `G ⧸ (H ⊔ N)` need carry a group structure, and what remains is a
bijection of coset spaces. Mathlib's `QuotientGroup.quotientQuotientEquivQuotient` is the
group isomorphism this generalises, stated for `N ≤ M` with `M` normal.

The bijection is what a family or a sum indexed by cosets needs. The corresponding index
equality, `Subgroup.index_map_mk'_eq_index_sup`, records only that the two coset spaces have
equal `Nat.card` — the same finite cardinality when they are finite, and jointly `0` when they
are infinite, whatever their cardinalities. It supplies no correspondence between the cosets
themselves, so it cannot reindex a family.

## Main results

* `QuotientGroup.quotientQuotientEquivQuotientSup`: the bijection
  `(G ⧸ N) ⧸ H.map (mk' N) ≃ G ⧸ (H ⊔ N)`, sending the class of `g` to the class of `g`.
-/

public section

namespace QuotientGroup

variable {G : Type*} [Group G]

/-- The relation defining `(G ⧸ N) ⧸ H.map (mk' N)`, read on representatives: two classes modulo
`N` are congruent modulo the image of `H` exactly when their representatives are congruent modulo
`H ⊔ N`. Both halves of `quotientQuotientEquivQuotientSup` are this statement, in opposite
directions, so it is stated once here rather than rewritten twice. -/
@[to_additive /-- The relation defining `(G ⧸ N) ⧸ H.map (mk' N)`, read on representatives: two
classes modulo `N` are congruent modulo the image of `H` exactly when their representatives are
congruent modulo `H ⊔ N`. -/]
private theorem mk_inv_mul_mk_mem_map_iff (H N : Subgroup G) [N.Normal] (x y : G) :
    ((x : G ⧸ N))⁻¹ * (y : G ⧸ N) ∈ H.map (QuotientGroup.mk' N) ↔ x⁻¹ * y ∈ H ⊔ N := by
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk'_apply,
    ← Subgroup.mem_comap, QuotientGroup.comap_map_mk', sup_comm]

/-- **The third isomorphism theorem for coset spaces.** For a normal `N` and an *arbitrary*
subgroup `H`, the cosets of the image of `H` in `G ⧸ N` are the cosets of `H ⊔ N` in `G`, both
directions sending the class of `g` to the class of `g`.

Mathlib's `QuotientGroup.quotientQuotientEquivQuotient` is the group isomorphism this
generalises: it asks for `N ≤ M` with `M` normal, so that both sides are groups and the map is a
homomorphism. Here neither side need be a group — `H` is unconstrained — and what survives is the
bijection of coset spaces, which is what a coset-indexed sum or family needs. -/
@[to_additive /-- **The third isomorphism theorem for coset spaces**, additive version: for a
normal `N` and an arbitrary subgroup `H`, the cosets of the image of `H` in `G ⧸ N` are the
cosets of `H ⊔ N` in `G`. -/]
def quotientQuotientEquivQuotientSup (H N : Subgroup G) [N.Normal] :
    (G ⧸ N) ⧸ H.map (QuotientGroup.mk' N) ≃ G ⧸ (H ⊔ N) where
  toFun := Quotient.lift (Subgroup.quotientMapOfLE (le_sup_right : N ≤ H ⊔ N)) <| by
    refine Quotient.ind fun x ↦ Quotient.ind fun y hxy ↦ ?_
    exact QuotientGroup.eq.mpr
      ((mk_inv_mul_mk_mem_map_iff H N x y).mp (QuotientGroup.leftRel_apply.mp hxy))
  invFun := Quotient.lift (fun g : G ↦ ((g : G ⧸ N) : (G ⧸ N) ⧸ H.map (QuotientGroup.mk' N)))
    fun x y hxy ↦ QuotientGroup.eq.mpr
      ((mk_inv_mul_mk_mem_map_iff H N x y).mpr (QuotientGroup.leftRel_apply.mp hxy))
  left_inv := Quotient.ind fun x ↦ QuotientGroup.induction_on x fun _ ↦ rfl
  right_inv := fun q ↦ QuotientGroup.induction_on q fun _ ↦ rfl

/-- The equivalence sends the nested class of `g` to the class of `g`. -/
@[to_additive (attr := simp) /-- The equivalence sends the nested class of `g` to the class of
`g`. -/, simp]
theorem quotientQuotientEquivQuotientSup_mk_mk (H N : Subgroup G) [N.Normal] (g : G) :
    quotientQuotientEquivQuotientSup H N
      ((g : G ⧸ N) : (G ⧸ N) ⧸ H.map (QuotientGroup.mk' N)) = (g : G ⧸ (H ⊔ N)) := (rfl)

/-- The inverse equivalence sends the class of `g` to the nested class of `g`. -/
@[to_additive (attr := simp) /-- The inverse equivalence sends the class of `g` to the nested
class of `g`. -/, simp]
theorem quotientQuotientEquivQuotientSup_symm_mk (H N : Subgroup G) [N.Normal] (g : G) :
    (quotientQuotientEquivQuotientSup H N).symm (g : G ⧸ (H ⊔ N)) =
      ((g : G ⧸ N) : (G ⧸ N) ⧸ H.map (QuotientGroup.mk' N)) := (rfl)

end QuotientGroup
