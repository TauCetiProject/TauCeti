/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.CSA
public import TauCeti.GroupTheory.FreeGroup.Discrimination
public import TauCeti.GroupTheory.GroupAlgGeom.Discrimination

/-!
# Residually free and fully residually free groups

A group `G` is *residually free* when every nonidentity element survives under some homomorphism
from `G` to a free group, and *fully residually free* (freely discriminated, `ω`-residually free)
when every finite family of nonidentity elements survives simultaneously under one such
homomorphism. By a theorem of Sela and of Champetier and Guirardel, the finitely generated fully
residually free groups are exactly the limit groups; this file develops only the definitions and
their elementary properties.

The free target in the definitions is a `FreeGroup ι` with `ι` in the universe of `G`. By
`FreeGroup.exists_monoidHom_fin_two_forall_ne_one` the free group of rank two always suffices, so
both properties are separation, respectively discrimination, by `FreeGroup (Fin 2)` with trivial
coefficients in the sense of `TauCeti.GroupAlgGeom`. This makes both properties independent of
universes and gives their inheritance by subgroups.

Free groups are fully residually free, and residually free groups are torsion-free; in particular
a nontrivial finite group is not residually free. Fully residually free groups are commutative
transitive, since one homomorphism to a free group can keep both a nonidentity element and a
commutator nontrivial, and commutation is transitive on the nontrivial elements of a free group.
Residual freeness passes to products, so `FreeGroup (Fin 2) × Multiplicative ℤ` is residually
free; it is not commutative transitive, hence not fully residually free. Thus the two notions
differ.

## Main definitions

* `TauCeti.LimitGroup.IsResiduallyFree`: residually free groups.
* `TauCeti.LimitGroup.IsFullyResiduallyFree`: fully residually free groups.

## Main results

* `TauCeti.LimitGroup.isFullyResiduallyFree_iff_isDiscriminatedBy`: full residual freeness is
  discrimination by `FreeGroup (Fin 2)` with trivial coefficients.
* `TauCeti.LimitGroup.IsFullyResiduallyFree.of_injective`: subgroups of fully residually free
  groups are fully residually free.
* `TauCeti.LimitGroup.IsResiduallyFree.isMulTorsionFree`: residually free groups are
  torsion-free.
* `TauCeti.LimitGroup.IsFullyResiduallyFree.isCommTransitive`: fully residually free groups are
  commutative transitive.
* `TauCeti.LimitGroup.not_isFullyResiduallyFree_freeGroup_prod_int`: `F₂ × ℤ` is residually free
  but not fully residually free.

## References

* C. Champetier, V. Guirardel, *Limit groups as limits of free groups*, Israel J. Math. 146
  (2005), §2.3 (Definition 2.5) and Proposition 3.1.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.6.
-/

public section

open Group
open scoped commutatorElement

universe u v

namespace TauCeti.LimitGroup

open GroupAlgGeom

variable {G : Type u} [Group G] {H : Type v} [Group H]

variable (G) in
/-- A group is *residually free* when every nonidentity element survives under some homomorphism
to a free group `FreeGroup ι`, with `ι` in the universe of the group. -/
def IsResiduallyFree : Prop :=
  ∀ g : G, g ≠ 1 → ∃ (ι : Type u) (φ : G →* FreeGroup ι), φ g ≠ 1

variable (G) in
/-- A group is *fully residually free* when every finite family of nonidentity elements survives
simultaneously under one homomorphism to a free group `FreeGroup ι`, with `ι` in the universe of
the group. -/
def IsFullyResiduallyFree : Prop :=
  ∀ s : Finset G, (∀ g ∈ s, g ≠ 1) → ∃ (ι : Type u) (φ : G →* FreeGroup ι), ∀ g ∈ s, φ g ≠ 1

/-- A group is fully residually free if and only if every finite family of nonidentity elements
survives under one homomorphism to the free group of rank two. -/
theorem isFullyResiduallyFree_iff_fin_two :
    IsFullyResiduallyFree G ↔
      ∀ s : Finset G, (∀ g ∈ s, g ≠ 1) → ∃ φ : G →* FreeGroup (Fin 2), ∀ g ∈ s, φ g ≠ 1 := by
  classical
  refine ⟨fun h s hs => ?_, fun h s hs => ?_⟩
  · obtain ⟨ι, φ, hφ⟩ := h s hs
    obtain ⟨ψ, hψ⟩ := FreeGroup.exists_monoidHom_fin_two_forall_ne_one (s.image φ)
      (by simpa using hφ)
    exact ⟨ψ.comp φ, fun g hg => hψ (φ g) (Finset.mem_image_of_mem φ hg)⟩
  · obtain ⟨φ, hφ⟩ := h s hs
    let e := FreeGroup.freeGroupCongr (Equiv.ulift.{u}.symm : Fin 2 ≃ ULift.{u} (Fin 2))
    exact ⟨ULift.{u} (Fin 2), e.toMonoidHom.comp φ, fun g hg => by simpa using hφ g hg⟩

/-- A group is residually free if and only if every nonidentity element survives under some
homomorphism to the free group of rank two. -/
theorem isResiduallyFree_iff_fin_two :
    IsResiduallyFree G ↔ ∀ g : G, g ≠ 1 → ∃ φ : G →* FreeGroup (Fin 2), φ g ≠ 1 := by
  classical
  refine ⟨fun h g hg => ?_, fun h g hg => ?_⟩
  · obtain ⟨ι, φ, hφ⟩ := h g hg
    obtain ⟨ψ, hψ⟩ := FreeGroup.exists_monoidHom_fin_two_forall_ne_one {φ g} (by simpa using hφ)
    exact ⟨ψ.comp φ, hψ (φ g) (Finset.mem_singleton_self _)⟩
  · obtain ⟨φ, hφ⟩ := h g hg
    let e := FreeGroup.freeGroupCongr (Equiv.ulift.{u}.symm : Fin 2 ≃ ULift.{u} (Fin 2))
    exact ⟨ULift.{u} (Fin 2), e.toMonoidHom.comp φ, by simpa using hφ⟩

/-- Full residual freeness is discrimination by the free group of rank two, with trivial
coefficients. -/
theorem isFullyResiduallyFree_iff_isDiscriminatedBy :
    IsFullyResiduallyFree G ↔
      IsDiscriminatedBy (1 : Unit →* G) (1 : Unit →* FreeGroup (Fin 2)) := by
  rw [isFullyResiduallyFree_iff_fin_two, isDiscriminatedBy_def]
  exact forall₂_congr fun s _ =>
    ⟨fun ⟨φ, hφ⟩ => ⟨⟨φ, fun _ => by simp⟩, hφ⟩, fun ⟨φ, hφ⟩ => ⟨φ, hφ⟩⟩

/-- Residual freeness is separation by the free group of rank two, with trivial coefficients. -/
theorem isResiduallyFree_iff_isSeparatedBy :
    IsResiduallyFree G ↔ IsSeparatedBy (1 : Unit →* G) (1 : Unit →* FreeGroup (Fin 2)) := by
  rw [isResiduallyFree_iff_fin_two, isSeparatedBy_def]
  exact forall₂_congr fun g _ =>
    ⟨fun ⟨φ, hφ⟩ => ⟨⟨φ, fun _ => by simp⟩, hφ⟩, fun ⟨φ, hφ⟩ => ⟨φ, hφ⟩⟩

/-- A fully residually free group is residually free. -/
theorem IsFullyResiduallyFree.isResiduallyFree (h : IsFullyResiduallyFree G) :
    IsResiduallyFree G := fun g hg => by
  classical
  obtain ⟨ι, φ, hφ⟩ := h {g} (by simpa using hg)
  exact ⟨ι, φ, hφ g (Finset.mem_singleton_self g)⟩

/-- A group with an injective homomorphism to a residually free group is residually free. In
particular subgroups of residually free groups are residually free. -/
theorem IsResiduallyFree.of_injective (h : IsResiduallyFree G) {f : H →* G}
    (hf : Function.Injective f) : IsResiduallyFree H := by
  rw [isResiduallyFree_iff_fin_two] at h ⊢
  intro x hx
  obtain ⟨φ, hφ⟩ := h (f x) ((map_ne_one_iff f hf).2 hx)
  exact ⟨φ.comp f, hφ⟩

/-- A group with an injective homomorphism to a fully residually free group is fully residually
free. In particular subgroups of fully residually free groups are fully residually free. -/
theorem IsFullyResiduallyFree.of_injective (h : IsFullyResiduallyFree G) {f : H →* G}
    (hf : Function.Injective f) : IsFullyResiduallyFree H := by
  classical
  rw [isFullyResiduallyFree_iff_fin_two] at h ⊢
  intro s hs
  obtain ⟨φ, hφ⟩ := h (s.image f) (by simpa [map_ne_one_iff f hf] using hs)
  exact ⟨φ.comp f, fun x hx => hφ (f x) (Finset.mem_image_of_mem f hx)⟩

/-- A free group is fully residually free. -/
theorem isFullyResiduallyFree_of_isFreeGroup [IsFreeGroup G] : IsFullyResiduallyFree G :=
  fun s hs => ⟨IsFreeGroup.Generators G, (IsFreeGroup.toFreeGroup G).toMonoidHom,
    fun g hg => by simpa using hs g hg⟩

/-- A trivial group is fully residually free: there are no nonidentity elements to keep. -/
theorem isFullyResiduallyFree_of_subsingleton [Subsingleton G] : IsFullyResiduallyFree G :=
  fun _ hs => ⟨PEmpty, 1, fun g hg => (hs g hg (Subsingleton.elim g 1)).elim⟩

/-- A product of residually free groups is residually free, through the two projections. -/
theorem IsResiduallyFree.prod (hG : IsResiduallyFree G) (hH : IsResiduallyFree H) :
    IsResiduallyFree (G × H) := by
  rw [isResiduallyFree_iff_fin_two] at hG hH ⊢
  rintro ⟨g, h⟩ hgh
  by_cases hg : g = 1
  · obtain ⟨φ, hφ⟩ := hH h fun hh => hgh (by simp [hg, hh])
    exact ⟨φ.comp (MonoidHom.snd G H), hφ⟩
  · obtain ⟨φ, hφ⟩ := hG g hg
    exact ⟨φ.comp (MonoidHom.fst G H), hφ⟩

/-- A residually free group is torsion-free, since free groups are. -/
theorem IsResiduallyFree.isMulTorsionFree (h : IsResiduallyFree G) : IsMulTorsionFree G := by
  rw [isMulTorsionFree_iff_not_isOfFinOrder]
  intro g hg hfin
  obtain ⟨ι, φ, hφ⟩ := h g hg
  exact not_isOfFinOrder_of_isMulTorsionFree hφ (φ.isOfFinOrder hfin)

/-- A nontrivial finite group, such as `ℤ/2`, is not residually free. -/
theorem not_isResiduallyFree_of_finite [Finite G] [Nontrivial G] : ¬IsResiduallyFree G := by
  intro h
  have := h.isMulTorsionFree
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  exact not_isOfFinOrder_of_isMulTorsionFree hg (isOfFinOrder_of_finite g)

/-- A fully residually free group is commutative transitive: if `y ≠ 1` commutes with `x` and with
`z`, a homomorphism to a free group keeping both `y` and the commutator of `x` and `z` nontrivial
would contradict commutation transitivity in the free group. -/
theorem IsFullyResiduallyFree.isCommTransitive (h : IsFullyResiduallyFree G) :
    IsCommTransitive G := by
  classical
  rw [isCommTransitive_iff]
  intro x y z hy hxy hyz
  rw [← commutatorElement_eq_one_iff_commute]
  by_contra hxz
  obtain ⟨ι, φ, hφ⟩ := h ({y, ⁅x, z⁆} : Finset G) (by simp [hy, hxz])
  have hφxz : Commute (φ x) (φ z) := (isCommTransitive_iff _).1 IsFreeGroup.isCommTransitive
    _ _ _ (hφ y (by simp)) (hxy.map φ) (hyz.map φ)
  apply hφ ⁅x, z⁆ (by simp)
  rwa [map_commutatorElement, commutatorElement_eq_one_iff_commute]

/-- `F₂ × ℤ` is residually free, through its projections to the factors. -/
theorem isResiduallyFree_freeGroup_prod_int :
    IsResiduallyFree (FreeGroup (Fin 2) × Multiplicative ℤ) :=
  isFullyResiduallyFree_of_isFreeGroup.isResiduallyFree.prod
    ((isFullyResiduallyFree_of_isFreeGroup (G := FreeGroup Unit)).isResiduallyFree.of_injective
      (f := FreeGroup.mulEquivIntOfUnique.symm.toMonoidHom)
      FreeGroup.mulEquivIntOfUnique.symm.injective)

/-- `F₂ × ℤ` is not fully residually free, since it is not commutative transitive. Together with
`isResiduallyFree_freeGroup_prod_int` this separates the two notions. -/
theorem not_isFullyResiduallyFree_freeGroup_prod_int :
    ¬IsFullyResiduallyFree (FreeGroup (Fin 2) × Multiplicative ℤ) := fun h =>
  not_isCommTransitive_prod_of_nontrivial
    (fun hcomm => not_subsingleton (Fin 2) (FreeGroup.isMulCommutative_iff_subsingleton.mp hcomm))
    h.isCommTransitive

end TauCeti.LimitGroup
