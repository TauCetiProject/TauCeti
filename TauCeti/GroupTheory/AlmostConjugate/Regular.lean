/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.AlmostConjugate
public import TauCeti.Algebra.GroupAction.PermutationRepresentation
public import TauCeti.GroupTheory.GroupAction.Orbit.CycleType

/-!
# Almost-conjugate regular representations

Let `G` be a finite group of order `m`, with its left-regular action on itself. An element of
order `d` acts on `G` with `m / d` cycles, all of length `d`
(`MulAction.fullCycleType_toPerm_eq_replicate`). Reading the regular representation inside the
symmetric group of an `m`-element set `α` through a numbering `e : G ≃ α`
(`Equiv.permutationRepresentation e`), the cycle type of the image of `g` therefore depends
only on `orderOf g`. Since two permutations are conjugate exactly when they have the same cycle
type, two groups of order `m` with the same number of elements of each order have
almost-conjugate regular images in `Equiv.Perm α`. If one of the groups is commutative and the
other is not, the images are not conjugate, because conjugate subgroups are isomorphic
(`Equiv.not_exists_map_conj_range_permutationRepresentation_eq`, in
`TauCeti.Algebra.GroupAction.PermutationRepresentation`).

The concrete Gassmann pair in `S₁₆` built from these results is in
`TauCeti.GroupTheory.AlmostConjugate.GassmannPair`.

## Main statements

* `Equiv.natCard_cycleType_eq_and_mem_range_permutationRepresentation`: the number of
  permutations of a given cycle type in a regular image, as a count of group elements by their
  order.
* `Equiv.almostConjugate_range_permutationRepresentation`: groups with the same number of
  elements of each order have almost-conjugate regular images.
* `Equiv.fullCycleType_permutationRepresentation`: the full cycle type of a regular image.
* `Equiv.almostConjugate_permutationRepresentation_range_iff`: almost conjugacy of regular
  images is equivalent to an order-preserving bijection.
* `Equiv.exists_map_conj_permutationRepresentation_range_eq_iff`: conjugacy of regular images
  is equivalent to isomorphism of their groups.

## References

* F. Gassmann, *Bemerkungen zur vorstehenden Arbeit von Hurwitz*, Math. Z. **25** (1926), 665–675.
* R. Perlis, *On the equation `ζ_K(s) = ζ_K'(s)`*, J. Number Theory **9** (1977), 342–360.
-/

public section

open MulAction

namespace Equiv

variable {G Γ α : Type*} [Group G] [Group Γ]

/-- **Cycle types in a regular representation.** The regular representation of `G`, read in
`Equiv.Perm α` through `e : G ≃ α`, contains as many permutations of cycle type `m` as `G` has
elements `g` for which `Nat.card α / orderOf g` copies of `orderOf g`, with the parts equal to `1`
(the fixed points) discarded, form the multiset `m`. -/
theorem natCard_cycleType_eq_and_mem_range_permutationRepresentation [Fintype α] [DecidableEq α]
    (e : G ≃ α) (m : Multiset ℕ) :
    Nat.card {σ : Equiv.Perm α //
        σ.cycleType = m ∧ σ ∈ (permutationRepresentation (G := G) e).range} =
      Nat.card {g : G //
        (Multiset.replicate (Nat.card α / orderOf g) (orderOf g)).filter (2 ≤ ·) = m} := by
  classical
  have : Fintype G := Fintype.ofEquiv α e.symm
  have hcyc (g : G) : (permutationRepresentation e g).cycleType =
      (Multiset.replicate (Nat.card α / orderOf g) (orderOf g)).filter (2 ≤ ·) := by
    have hg : permutationRepresentation e g = e.permCongr (toPerm g) := by
      ext
      simp [Equiv.permCongr_apply]
    -- Transport keeps the full cycle type, which for the regular action is read off `orderOf g`.
    rw [← Perm.filter_fullCycleType_eq_cycleType, hg, Perm.fullCycleType_permCongr,
      fullCycleType_toPerm_eq_replicate, Nat.card_congr e]
  refine (Nat.card_congr ?_).symm
  exact ((Equiv.ofInjective _ (permutationRepresentation_injective e)).subtypeEquiv fun g ↦ by
      rw [Equiv.ofInjective_apply, hcyc]).trans <|
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ (permutationRepresentation e).range)
      (·.cycleType = m)).trans <|
      Equiv.subtypeEquivRight fun _ ↦ and_comm

/-- **Regular representations of groups with the same order statistics are almost conjugate.** If
two groups have the same number of elements of each order, their regular representations, read in
the symmetric group of a finite set through numberings `e` and `f`, are almost conjugate. -/
theorem almostConjugate_range_permutationRepresentation [Finite α] (e : G ≃ α) (f : Γ ≃ α)
    (h : ∀ n : ℕ, Nat.card {g : G // orderOf g = n} = Nat.card {γ : Γ // orderOf γ = n}) :
    (permutationRepresentation (G := G) e).range.AlmostConjugate
      (permutationRepresentation (G := Γ) f).range := by
  classical
  have := Fintype.ofFinite α
  have : Finite G := .of_equiv α e.symm
  have : Finite Γ := .of_equiv α f.symm
  -- A bijection `G ≃ Γ` preserving orders matches the cycle-type counts of the two images.
  let ψ : G ≃ Γ := Equiv.ofFiberEquiv fun n ↦ (Finite.card_eq.mp (h n)).some
  have hψ (g : G) : orderOf (ψ g) = orderOf g := Equiv.ofFiberEquiv_map _ g
  rw [Subgroup.almostConjugate_iff_forall_natCard_cycleType_eq]
  intro m
  rw [natCard_cycleType_eq_and_mem_range_permutationRepresentation,
    natCard_cycleType_eq_and_mem_range_permutationRepresentation]
  exact Nat.card_congr (ψ.subtypeEquiv fun g ↦ by rw [hψ])

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
  rw [hperm, Perm.fullCycleType_permCongr, fullCycleType_toPerm_eq_replicate,
    Nat.card_eq_fintype_card, Fintype.card_congr e]

/-- **Almost-conjugacy of regular images.** Identify two groups `G` and `Γ` with a finite type
`α`. Their regular images in `Equiv.Perm α` are almost conjugate exactly when there is a bijection
`G ≃ Γ` preserving the orders of elements, that is, when `G` and `Γ` have the same number of
elements of each order. -/
theorem almostConjugate_permutationRepresentation_range_iff [Finite α]
    (e : G ≃ α) (e' : Γ ≃ α) :
    (permutationRepresentation (G := G) e).range.AlmostConjugate
        (permutationRepresentation (G := Γ) e').range ↔
      ∃ f : G ≃ Γ, ∀ g, orderOf (f g) = orderOf g := by
  classical
  let := Fintype.ofFinite α
  have hφ := permutationRepresentation_injective (G := G) e
  have hψ := permutationRepresentation_injective (G := Γ) e'
  set φ := permutationRepresentation (G := G) e
  set ψ := permutationRepresentation (G := Γ) e'
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

/-- **Conjugacy of regular images.** Identify two groups `G` and `Γ` with the same type `α`.
Their regular images in `Equiv.Perm α` are conjugate exactly when `G` and `Γ` are isomorphic. -/
theorem exists_map_conj_permutationRepresentation_range_eq_iff
    (e : G ≃ α) (e' : Γ ≃ α) :
    (∃ σ : Perm α, (permutationRepresentation (G := G) e).range.map
        (MulAut.conj σ : Perm α →* Perm α) =
          (permutationRepresentation (G := Γ) e').range) ↔
      Nonempty (G ≃* Γ) := by
  have hφ := permutationRepresentation_injective (G := G) e
  have hψ := permutationRepresentation_injective (G := Γ) e'
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
            (permutationRepresentation (G := Γ) e').comp i.toMonoidHom := by
      ext g x
      simp [MulAut.conj_apply, permutationRepresentation_apply, smul_eq_mul, map_mul]
    rw [MonoidHom.map_range, hcomp, ← MonoidHom.map_range,
      MonoidHom.range_eq_top_of_surjective _ i.surjective, ← MonoidHom.range_eq_map]

end Equiv
