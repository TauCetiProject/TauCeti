/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.BigPowers
public import TauCeti.GroupTheory.FreeGroup.CSA
public import TauCeti.GroupTheory.FreeGroup.Discrimination
public import TauCeti.GroupTheory.GroupAlgGeom.Discrimination
public import TauCeti.GroupTheory.GroupAlgGeom.Domain

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
a nontrivial finite group is not residually free. Fully residually free groups are CSA, hence
commutative transitive with abelian centralizers of nonidentity elements: one homomorphism to a
free group can keep any two nonidentity elements nontrivial, and the CSA property is witnessed by
pairs of elements. Consequently a nonabelian fully residually free group is a domain in the sense
of algebraic geometry over groups.
Residual freeness passes to products, so `FreeGroup (Fin 2) × Multiplicative ℤ` is residually
free; it is not commutative transitive, hence not fully residually free. Thus the two notions
differ. Fully residually free groups also inherit the big powers property from free groups,
since one homomorphism to a free group can keep every entry of a tuple and every commutator of
consecutive entries nontrivial.

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
* `TauCeti.LimitGroup.IsFullyResiduallyFree.isCSA`: fully residually free groups are CSA.
* `TauCeti.LimitGroup.IsFullyResiduallyFree.isCommTransitive`: fully residually free groups are
  commutative transitive.
* `TauCeti.LimitGroup.IsFullyResiduallyFree.isGDomain_id`: nonabelian fully residually free
  groups are domains.
* `TauCeti.LimitGroup.IsFullyResiduallyFree.isBP`: fully residually free groups have the big
  powers property.
* `TauCeti.LimitGroup.not_isFullyResiduallyFree_freeGroup_prod_int`: `F₂ × ℤ` is residually free
  but not fully residually free.

## References

* C. Champetier, V. Guirardel, *Limit groups as limits of free groups*, Israel J. Math. 146
  (2005), §2.3 (Definition 2.5) and Proposition 3.1.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.6.
* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §2.1.
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

/-- Characterization of residual freeness by homomorphisms to free groups `FreeGroup ι`, with `ι`
in the universe of the group. -/
theorem isResiduallyFree_def :
    IsResiduallyFree G ↔ ∀ g : G, g ≠ 1 → ∃ (ι : Type u) (φ : G →* FreeGroup ι), φ g ≠ 1 :=
  Iff.rfl

/-- Characterization of full residual freeness by homomorphisms to free groups `FreeGroup ι`, with
`ι` in the universe of the group. -/
theorem isFullyResiduallyFree_def :
    IsFullyResiduallyFree G ↔
      ∀ s : Finset G, (∀ g ∈ s, g ≠ 1) →
        ∃ (ι : Type u) (φ : G →* FreeGroup ι), ∀ g ∈ s, φ g ≠ 1 :=
  Iff.rfl

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
    IsResiduallyFree G :=
  isResiduallyFree_iff_isSeparatedBy.2
    (isFullyResiduallyFree_iff_isDiscriminatedBy.1 h).isSeparatedBy

/-- A group with an injective homomorphism to a residually free group is residually free. In
particular subgroups of residually free groups are residually free. -/
theorem IsResiduallyFree.of_injective (h : IsResiduallyFree G) {f : H →* G}
    (hf : Function.Injective f) : IsResiduallyFree H :=
  isResiduallyFree_iff_isSeparatedBy.2 <|
    (isResiduallyFree_iff_isSeparatedBy.1 h).of_injective ⟨f, fun _ => by simp⟩ hf

/-- A group with an injective homomorphism to a fully residually free group is fully residually
free. In particular subgroups of fully residually free groups are fully residually free. -/
theorem IsFullyResiduallyFree.of_injective (h : IsFullyResiduallyFree G) {f : H →* G}
    (hf : Function.Injective f) : IsFullyResiduallyFree H :=
  isFullyResiduallyFree_iff_isDiscriminatedBy.2 <|
    (isFullyResiduallyFree_iff_isDiscriminatedBy.1 h).of_injective ⟨f, fun _ => by simp⟩ hf

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

/-- A fully residually free group is CSA: its maximal abelian subgroups are malnormal. -/
theorem IsFullyResiduallyFree.isCSA (h : IsFullyResiduallyFree G) : IsCSA G := by
  classical
  refine IsFreeGroup.isCSA.of_forall_exists_monoidHom (H := FreeGroup (Fin 2))
    fun a b ha hb => ?_
  obtain ⟨φ, hφ⟩ := isFullyResiduallyFree_iff_fin_two.1 h {a, b} (by simp [ha, hb])
  exact ⟨φ, hφ a (by simp), hφ b (by simp)⟩

/-- A fully residually free group is commutative transitive: if `y ≠ 1`, `Commute x y`, and
`Commute y z`, then `Commute x z`. -/
theorem IsFullyResiduallyFree.isCommTransitive (h : IsFullyResiduallyFree G) :
    IsCommTransitive G :=
  h.isCSA.isCommTransitive

/-- A nonabelian fully residually free group is a domain: for any two nonidentity elements `x`
and `y`, some conjugate of `y` does not commute with `x`. -/
theorem IsFullyResiduallyFree.isGDomain_id (h : IsFullyResiduallyFree G)
    (hG : ¬IsMulCommutative G) : IsGDomain (MonoidHom.id G) :=
  IsGDomain.of_isCSA_of_injective h.isCSA Function.injective_id hG

/-- A fully residually free group has the big powers property, inherited from the free group of
rank two through one homomorphism keeping the entries of a tuple and the commutators of
consecutive entries nontrivial. -/
theorem IsFullyResiduallyFree.isBP (h : IsFullyResiduallyFree G) : IsBP G :=
  FreeGroup.isBP.of_forall_finset_exists_monoidHom (isFullyResiduallyFree_iff_fin_two.1 h)

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
