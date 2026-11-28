/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.GroupAction.FixedPoints

/-!
# Jordan's covering lemma

A proper subgroup of finite index misses a whole conjugacy class: if every element of a group `G`
is conjugate to an element of a finite-index subgroup `H`, then `H = G`. In Mathlib's language, the
union of the conjugates of `H`, `Group.conjugatesOfSet (H : Set G)`, is all of `G` exactly when
`H = ⊤`. No normality of `H` is assumed.

The proof is Burnside's count for the action of `G` on `G ⧸ H`: an element conjugate into `H`
fixes a coset, the identity fixes all `[G : H]` cosets, and the action is transitive, so the
average number of fixed cosets is one. This forces `[G : H] = 1`. For an infinite group `G`, the
argument runs in the finite quotient of `G` by the normal core of `H`.

This is the group-theoretic input of the Chebotarev arguments that recognise a number field
from its local behaviour: if the Frobenius class of almost every prime meets the subgroup fixing
a subfield, Chebotarev makes every class meet it, and the lemma makes the subgroup everything.

Finite index is needed: every element of `GL₂(ℂ)` is conjugate into the proper subgroup of upper
triangular matrices, which has infinite index.

## Main results

* `Subgroup.conjugatesOfSet_eq_univ_iff`: the conjugates of a finite-index subgroup `H` cover
  the group if and only if `H = ⊤`.
* `Group.mem_conjugatesOfSet_smul_iff`: the conjugates of a coset `a • K` are the conjugates of
  the elements `a * u`, `u ∈ K`.

## References

* C. Jordan, *Recherches sur les substitutions*, J. Math. Pures Appl. 17 (1872), 351–367.
* J.-P. Serre, *On a theorem of Jordan*, Bull. Amer. Math. Soc. 40 (2003), 429–440, Theorem 1.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- The finite-group case of `Subgroup.conjugatesOfSet_eq_univ_iff`, by Burnside's count. -/
private theorem eq_top_of_conjugatesOfSet_eq_univ [Finite G] {H : Subgroup G}
    (h : Group.conjugatesOfSet (H : Set G) = Set.univ) : H = ⊤ := by
  classical
  have := Fintype.ofFinite G
  -- An element `c x c⁻¹` with `x ∈ H` fixes the coset `c H`.
  have hfix (g : G) : 1 ≤ Fintype.card (MulAction.fixedBy (G ⧸ H) g) := by
    obtain ⟨x, hx, hxg⟩ := Group.mem_conjugatesOfSet_iff.mp (h ▸ Set.mem_univ g)
    obtain ⟨c, rfl⟩ := isConj_iff.mp hxg
    refine Fintype.card_pos_iff.mpr ⟨⟨(c : G ⧸ H), ?_⟩⟩
    rw [MulAction.mem_fixedBy, MulAction.Quotient.smul_mk, QuotientGroup.eq]
    simpa [mul_assoc] using H.inv_mem hx
  -- Burnside's count for the transitive action on `G ⧸ H`: `∑ g, |fix g| = |G|`.
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (G ⧸ H)
  have horb : Fintype.card (Quotient (MulAction.orbitRel G (G ⧸ H))) = 1 :=
    Fintype.card_eq_one_iff_nonempty_unique.mpr
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty G (G ⧸ H)).mp inferInstance)
  have h1 : Fintype.card (MulAction.fixedBy (G ⧸ H) (1 : G)) = H.index := by
    rw [← Nat.card_eq_fintype_card, MulAction.fixedBy_one_eq_univ, Nat.card_univ, index_eq_card]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 1), horb, one_mul, h1] at hB
  -- Every nonidentity element fixes at least one coset, so `[G : H] + (|G| - 1) ≤ |G|`.
  have hle : ∑ _g ∈ Finset.univ.erase (1 : G), 1 ≤
      ∑ g ∈ Finset.univ.erase (1 : G), Fintype.card (MulAction.fixedBy (G ⧸ H) g) :=
    Finset.sum_le_sum fun g _ ↦ hfix g
  rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ 1),
    Finset.card_univ] at hle
  have := Fintype.card_pos (α := G)
  have := H.index_ne_zero_of_finite
  exact index_eq_one.mp (by omega)

/-- **Jordan's covering lemma.** The conjugates of a finite-index subgroup `H` of a group `G`
cover `G` if and only if `H = ⊤`: a proper subgroup of finite index misses some conjugacy class.
Finite index is needed. -/
@[simp]
theorem conjugatesOfSet_eq_univ_iff {H : Subgroup G} [H.FiniteIndex] :
    Group.conjugatesOfSet (H : Set G) = Set.univ ↔ H = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ Set.eq_univ_of_univ_subset (h ▸ Group.subset_conjugatesOfSet)⟩
  -- The image of `H` in the finite quotient `G ⧸ H.normalCore` still meets every class.
  let f := QuotientGroup.mk' H.normalCore
  have hmap : H.map f = ⊤ := eq_top_of_conjugatesOfSet_eq_univ <| Set.eq_univ_of_forall fun q ↦ by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H.normalCore q
    obtain ⟨x, hx, hxg⟩ := Group.mem_conjugatesOfSet_iff.mp (h ▸ Set.mem_univ g)
    exact Group.mem_conjugatesOfSet_iff.mpr ⟨f x, mem_map_of_mem f hx, f.map_isConj hxg⟩
  -- Pull back along the quotient map, whose kernel `H.normalCore` lies in `H`.
  have := congrArg (comap f) hmap
  rwa [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr H.normalCore_le, comap_top] at this

end Subgroup

namespace Group

open scoped Pointwise

variable {G : Type*} [Group G]

/-- An element of the conjugates of a coset `a • K` is a conjugate of some `a * u`, `u ∈ K`. -/
theorem mem_conjugatesOfSet_smul_iff {a x : G} {K : Subgroup G} :
    x ∈ conjugatesOfSet (a • (K : Set G)) ↔ ∃ u ∈ K, IsConj (a * u) x := by
  simp [mem_conjugatesOfSet_iff, Set.mem_smul_set]

end Group
