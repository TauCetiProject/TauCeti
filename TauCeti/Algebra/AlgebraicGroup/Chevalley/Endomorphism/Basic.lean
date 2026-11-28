/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap

/-!
# Standard and based endomorphisms of Chevalley groups

An endomorphism `F` of the points of a Chevalley datum `D` over a commutative ring `A` is
**standard** (`ChevalleyDatum.IsStandardEndomorphism`) if it maps every root subgroup onto a
root subgroup, and **based** (`ChevalleyDatum.IsBasedEndomorphism`) if in addition it maps
every positive root subgroup onto a positive root subgroup. Over a nontrivial ring, a standard
endomorphism sending `D.torusPoints A` into `D.borelSubgroup A` is based if and only if it maps
`D.borelSubgroup A` into itself (`ChevalleyDatum.isBasedEndomorphism_iff_map_borelSubgroup_le`).
Every standard endomorphism admitting a character map preserves `D.rootTorusSubgroup A`
(`ChevalleyDatum.IsStandardEndomorphism.map_rootTorusSubgroup_le`).

Concrete Weyl and Frobenius examples live in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Endomorphism.Weyl` and
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Endomorphism.Frobenius`.

## Main definitions

* `TauCeti.DynkinType.ChevalleyDatum.IsStandardEndomorphism`: maps every root subgroup onto a
  root subgroup.
* `TauCeti.DynkinType.ChevalleyDatum.IsBasedEndomorphism`: standard and maps positive root
  subgroups onto positive root subgroups.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.IsStandardEndomorphism.map_rootTorusSubgroup_le`: every
  standard endomorphism with a character map preserves `D.rootTorusSubgroup A`.
* `TauCeti.DynkinType.ChevalleyDatum.isBasedEndomorphism_iff_map_borelSubgroup_le`: over a
  nontrivial ring, a standard endomorphism sending `D.torusPoints A` into `D.borelSubgroup A` is
  based if and only if it maps `D.borelSubgroup A` into itself.

## References

* R. Steinberg, *Endomorphisms of Linear Algebraic Groups*, Mem. Amer. Math. Soc. **80** (1968),
  §§10–11.
* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 10.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*,
  §§1.15–1.17.
-/

public section

open Multiplicative

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-! ## Standard and based endomorphisms -/

section Defs

variable (A : Type v) [CommRing A]

/-- An endomorphism of `D.points A` is **standard** if it maps every root subgroup onto a root
subgroup. -/
def IsStandardEndomorphism (F : D.points A →* D.points A) : Prop :=
  ∀ α : Fin t.numRoots, ∃ β : Fin t.numRoots,
    (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints β A).range

/-- An endomorphism of `D.points A` is **based** if it is standard and maps every positive root
subgroup onto a positive root subgroup. -/
def IsBasedEndomorphism (F : D.points A →* D.points A) : Prop :=
  D.IsStandardEndomorphism A F ∧
    ∀ α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
      ∃ β ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
        (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints β A).range

variable {D A}

/-- Unfolding `IsStandardEndomorphism`. -/
theorem isStandardEndomorphism_iff {F : D.points A →* D.points A} :
    D.IsStandardEndomorphism A F ↔
      ∀ α : Fin t.numRoots, ∃ β : Fin t.numRoots,
        (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints β A).range :=
  Iff.rfl

/-- Unfolding `IsBasedEndomorphism`. -/
theorem isBasedEndomorphism_iff {F : D.points A →* D.points A} :
    D.IsBasedEndomorphism A F ↔
      D.IsStandardEndomorphism A F ∧
        ∀ α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
          ∃ β ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
            (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints β A).range :=
  Iff.rfl

/-- Every based endomorphism is standard. -/
theorem IsBasedEndomorphism.isStandardEndomorphism {F : D.points A →* D.points A}
    (h : D.IsBasedEndomorphism A F) : D.IsStandardEndomorphism A F :=
  h.1

/-- Every standard endomorphism with a character map preserves the root–torus subgroup
`D.rootTorusSubgroup A`. -/
theorem IsStandardEndomorphism.map_rootTorusSubgroup_le {F : D.points A →* D.points A}
    {φ : Module.End ℤ (Fin t.rank → ℤ)} (hstd : D.IsStandardEndomorphism A F)
    (hφ : IsCharacterMap (D.torusPoints A) F φ) :
    (D.rootTorusSubgroup A).map F ≤ D.rootTorusSubgroup A := by
  rw [Subgroup.map_le_iff_le_comap, D.rootTorusSubgroup_le_iff]
  refine ⟨fun α u => ?_, fun s => ?_⟩
  · obtain ⟨β, hβ⟩ := hstd α
    have hmem : F (D.rootSubgroupPoints α A u) ∈ (D.rootSubgroupPoints β A).range :=
      hβ ▸ ⟨D.rootSubgroupPoints α A u, ⟨u, rfl⟩, rfl⟩
    obtain ⟨v, hv⟩ := hmem
    rw [Subgroup.mem_comap, ← hv]
    exact D.rootSubgroupPoints_mem_rootTorusSubgroup β A v
  · rw [Subgroup.mem_comap, hφ.map_apply s]
    exact D.torusPoints_mem_rootTorusSubgroup A (torusPointMap φ s)

/-- Every based endomorphism maps the positive subgroup into itself. -/
theorem IsBasedEndomorphism.map_positivePoints_le {F : D.points A →* D.points A}
    (h : D.IsBasedEndomorphism A F) :
    (D.positivePoints A).map F ≤ D.positivePoints A := by
  rw [D.positivePoints_eq_iSup, Subgroup.map_iSup]
  refine iSup_le fun α => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hα => ?_
  obtain ⟨β, hβ, hmap⟩ := h.2 α hα
  exact hmap ▸ le_iSup₂ (f := fun γ _ => (D.rootSubgroupPoints γ A).range) β hβ

variable (D A) in
/-- The identity endomorphism is standard. -/
theorem isStandardEndomorphism_id :
    D.IsStandardEndomorphism A (MonoidHom.id (D.points A)) :=
  fun α => ⟨α, Subgroup.map_id _⟩

variable (D A) in
/-- The identity endomorphism is based. -/
theorem isBasedEndomorphism_id :
    D.IsBasedEndomorphism A (MonoidHom.id (D.points A)) :=
  ⟨D.isStandardEndomorphism_id A, fun α hα => ⟨α, hα, Subgroup.map_id _⟩⟩

/-- Standard endomorphisms are closed under composition. -/
theorem IsStandardEndomorphism.comp {F G : D.points A →* D.points A}
    (hF : D.IsStandardEndomorphism A F) (hG : D.IsStandardEndomorphism A G) :
    D.IsStandardEndomorphism A (F.comp G) := fun α => by
  obtain ⟨β, hβ⟩ := hG α
  obtain ⟨γ, hγ⟩ := hF β
  exact ⟨γ, by rw [← Subgroup.map_map, hβ, hγ]⟩

/-- Based endomorphisms are closed under composition. -/
theorem IsBasedEndomorphism.comp {F G : D.points A →* D.points A}
    (hF : D.IsBasedEndomorphism A F) (hG : D.IsBasedEndomorphism A G) :
    D.IsBasedEndomorphism A (F.comp G) :=
  ⟨hF.isStandardEndomorphism.comp hG.isStandardEndomorphism, fun α hα => by
    obtain ⟨β, hβ, hmapG⟩ := hG.2 α hα
    obtain ⟨γ, hγ, hmapF⟩ := hF.2 β hβ
    exact ⟨γ, hγ, by rw [← Subgroup.map_map, hmapG, hmapF]⟩⟩

/-- Powers of a standard endomorphism are standard. -/
theorem IsStandardEndomorphism.pow {F : _root_.Monoid.End (D.points A)}
    (hF : D.IsStandardEndomorphism A F) (n : ℕ) :
    D.IsStandardEndomorphism A (HPow.hPow (α := _root_.Monoid.End (D.points A)) F n) := by
  induction n with
  | zero => exact D.isStandardEndomorphism_id A
  | succ n ih =>
      rw [pow_succ']
      exact hF.comp ih

/-- Powers of a based endomorphism are based. -/
theorem IsBasedEndomorphism.pow {F : _root_.Monoid.End (D.points A)}
    (hF : D.IsBasedEndomorphism A F) (n : ℕ) :
    D.IsBasedEndomorphism A (HPow.hPow (α := _root_.Monoid.End (D.points A)) F n) := by
  induction n with
  | zero => exact D.isBasedEndomorphism_id A
  | succ n ih =>
      rw [pow_succ']
      exact hF.comp ih

/-- Over a nontrivial ring, a standard endomorphism sending `D.torusPoints A` into
`D.borelSubgroup A` is based if and only if it maps `D.borelSubgroup A` into itself. -/
theorem isBasedEndomorphism_iff_map_borelSubgroup_le [Nontrivial A]
    {F : D.points A →* D.points A} (hstd : D.IsStandardEndomorphism A F)
    (hT : (D.torusPoints A).range.map F ≤ D.borelSubgroup A) :
    D.IsBasedEndomorphism A F ↔ (D.borelSubgroup A).map F ≤ D.borelSubgroup A := by
  constructor
  · intro hbased
    conv_lhs => rw [D.borelSubgroup_def, Subgroup.map_sup]
    exact sup_le (hbased.map_positivePoints_le.trans (D.positivePoints_le_borelSubgroup A)) hT
  · refine fun hB => ⟨hstd, fun α hα => ?_⟩
    obtain ⟨β, hβ⟩ := hstd α
    refine ⟨β, by_contra fun hnotpos => ?_, hβ⟩
    have hβneg := (not_mem_posRoots_iff_mem_negRoots _ _ β).mp hnotpos
    obtain ⟨_, ⟨u, rfl⟩, hFx⟩ :
        D.rootSubgroupPoints β A (ofAdd 1) ∈ (D.rootSubgroupPoints α A).range.map F :=
      hβ.symm ▸ ⟨ofAdd 1, rfl⟩
    have hmem : D.rootSubgroupPoints β A (ofAdd 1) ∈ D.borelSubgroup A :=
      hFx ▸ hB ⟨_, D.positivePoints_le_borelSubgroup A
        (D.rootSubgroupPoints_mem_positivePoints A hα u), rfl⟩
    exact D.rootSubgroupPoints_ofAdd_one_ne_one A β
      ((D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots A hβneg _).mp hmem)

/-- For a standard endomorphism with a character map over a nontrivial ring, being based is
equivalent to mapping `D.borelSubgroup A` into itself. -/
theorem isBasedEndomorphism_iff_map_borelSubgroup_le_of_isCharacterMap [Nontrivial A]
    {F : D.points A →* D.points A} {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hstd : D.IsStandardEndomorphism A F) (hφ : IsCharacterMap (D.torusPoints A) F φ) :
    D.IsBasedEndomorphism A F ↔ (D.borelSubgroup A).map F ≤ D.borelSubgroup A :=
  isBasedEndomorphism_iff_map_borelSubgroup_le hstd <| by
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    exact hφ.map_apply s ▸ D.range_torusPoints_le_borelSubgroup A ⟨torusPointMap φ s, rfl⟩

end Defs

end TauCeti.DynkinType.ChevalleyDatum
