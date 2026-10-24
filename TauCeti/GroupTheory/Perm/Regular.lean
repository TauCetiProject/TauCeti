/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.PermutationRepresentation
public import TauCeti.GroupTheory.AlmostConjugate
public import TauCeti.GroupTheory.GroupAction.Orbit.CycleType

/-!
# Regular permutation groups

Cayley's theorem embeds a group `G` in `Equiv.Perm G` through its left-regular action
`MulAction.toPermHom G G`. An equivalence `e : G ≃ α` transports this action to `α`; its
image is the *regular image* of `G` in `Equiv.Perm α`. This file compares the regular images
of two groups identified with the same type `α`. Cycle-type comparisons require `α` to be
finite; conjugacy of the images is equivalent to isomorphism of the groups without finiteness.

Left multiplication by an element of order `d` in a group of order `m` is a product of `m / d`
disjoint `d`-cycles (`MulAction.fullCycleType_toPerm_self`), so the cycle type of an element of a
regular image only records its order. Since permutations are conjugate exactly when they have the
same cycle type, the regular images of `G` and `G'` are almost conjugate exactly when `G` and `G'`
have the same number of elements of each order. They are conjugate exactly when `G` and `G'` are
isomorphic. Groups with the same order statistics which are not isomorphic therefore give
almost-conjugate subgroups of a symmetric group that are not conjugate, a Gassmann pair.

## Main results

* `Equiv.fullCycleType_permutationRepresentation`: the full cycle type of the regular image of `g`.
* `Equiv.almostConjugate_permutationRepresentation_range_iff`: two regular images are almost
  conjugate exactly when there is an order-preserving bijection between the groups.
* `Equiv.exists_map_conj_permutationRepresentation_range_eq_iff`: two regular images are conjugate
  exactly when the groups are isomorphic.

## References

* F. Gassmann, *Bemerkungen zur vorstehenden Arbeit von Hurwitz*, Math. Z. **25** (1926), 665–675.
* R. Perlis, *On the equation `ζ_K(s) = ζ_K'(s)`*, J. Number Theory **9** (1977), 342–360.
-/

public section

open MulAction

namespace Equiv

variable {G G' α : Type*} [Group G] [Group G']

/-- The regular image of `g` on a finite type `α` is a product of `card α / d` disjoint
`d`-cycles, where `d` is the order of `g`. -/
@[simp]
theorem fullCycleType_permutationRepresentation [Fintype α] [DecidableEq α]
    (e : G ≃ α) (g : G) :
    (permutationRepresentation e g).fullCycleType =
      Multiset.replicate (Fintype.card α / orderOf g) (orderOf g) := by
  classical
  let := Fintype.ofEquiv α e.symm
  have hperm : permutationRepresentation e g = e.permCongr (toPerm g) := by
    ext i
    simp only [permutationRepresentation_apply, Equiv.permCongr_apply, toPerm_apply]
  rw [hperm, Perm.fullCycleType_permCongr, fullCycleType_toPerm_self, Fintype.card_congr e]

/-- **Almost-conjugacy of regular images.** Identify two groups `G` and `G'` with a finite type
`α`. Their regular images in `Equiv.Perm α` are almost conjugate exactly when there is a bijection
`G ≃ G'` preserving the orders of elements, that is, when `G` and `G'` have the same number of
elements of each order. -/
theorem almostConjugate_permutationRepresentation_range_iff [Finite α]
    (e : G ≃ α) (e' : G' ≃ α) :
    (permutationRepresentation (G := G) e).range.AlmostConjugate
        (permutationRepresentation (G := G') e').range ↔
      ∃ f : G ≃ G', ∀ g, orderOf (f g) = orderOf g := by
  classical
  letI := Fintype.ofFinite α
  have hφ := permutationRepresentation_injective (G := G) e
  have hψ := permutationRepresentation_injective (G := G') e'
  set φ := permutationRepresentation (G := G) e
  set ψ := permutationRepresentation (G := G') e'
  rw [Subgroup.almostConjugate_iff_exists_equiv_isConj]
  -- Identify each regular image with its group and compare class-preserving bijections with
  -- order-preserving ones: a regular permutation's cycle type is determined by its order.
  set E := MonoidHom.ofInjective hφ
  set E' := MonoidHom.ofInjective hψ
  constructor
  · rintro ⟨F, hF⟩
    refine ⟨E.toEquiv.trans (F.trans E'.symm.toEquiv), fun g ↦ ?_⟩
    obtain ⟨c, hc⟩ := hF (E g)
    have hψf : ψ ((E'.symm (F (E g)))) = F (E g) := by
      rw [← MonoidHom.ofInjective_apply hψ, MulEquiv.apply_symm_apply]
    calc orderOf (E'.symm (F (E g))) = orderOf (F (E g) : Perm α) := by
          rw [← orderOf_injective ψ hψ, hψf]
      _ = orderOf (E g : Perm α) := (hc.orderOf_eq (c : Perm α)).symm
      _ = orderOf g := by rw [MonoidHom.ofInjective_apply, orderOf_injective φ hφ]
  · rintro ⟨f, hf⟩
    refine ⟨E.symm.toEquiv.trans (f.trans E'.toEquiv), fun h ↦ ?_⟩
    obtain ⟨g, rfl⟩ := E.surjective h
    simp only [Equiv.trans_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
      MulEquiv.symm_apply_apply, E, E', MonoidHom.ofInjective_apply]
    rw [Perm.isConj_iff_cycleType_eq, ← Perm.filter_fullCycleType_eq_cycleType,
      ← Perm.filter_fullCycleType_eq_cycleType]
    simp only [φ, ψ, fullCycleType_permutationRepresentation, hf]

/-- **Conjugacy of regular images.** Identify two groups `G` and `G'` with the same type `α`.
Their regular images in `Equiv.Perm α` are conjugate exactly when `G` and `G'` are isomorphic. -/
theorem exists_map_conj_permutationRepresentation_range_eq_iff
    (e : G ≃ α) (e' : G' ≃ α) :
    (∃ σ : Perm α, (permutationRepresentation (G := G) e).range.map
        (MulAut.conj σ : Perm α →* Perm α) =
          (permutationRepresentation (G := G') e').range) ↔
      Nonempty (G ≃* G') := by
  have hφ := permutationRepresentation_injective (G := G) e
  have hψ := permutationRepresentation_injective (G := G') e'
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨(MonoidHom.ofInjective hφ).trans <|
      ((Subgroup.equivMapOfInjective _ _ (MulAut.conj σ).injective).trans
        (MulEquiv.subgroupCongr hσ)).trans (MonoidHom.ofInjective hψ).symm⟩
  · rintro ⟨i⟩
    -- Conjugating by the renumbering `e⁻¹ ∘ i ∘ e'` turns left multiplication by `g` into left
    -- multiplication by `i g`.
    refine ⟨e.symm.trans (i.toEquiv.trans e'), ?_⟩
    have hcomp :
        (MulAut.conj (e.symm.trans (i.toEquiv.trans e')) : Perm α →* Perm α).comp
          (permutationRepresentation (G := G) e) =
            (permutationRepresentation (G := G') e').comp i.toMonoidHom := by
      ext g x
      simp [MulAut.conj_apply, permutationRepresentation_apply, smul_eq_mul, map_mul]
    rw [MonoidHom.map_range, hcomp, ← MonoidHom.map_range,
      MonoidHom.range_eq_top_of_surjective _ i.surjective, ← MonoidHom.range_eq_map]

end Equiv
