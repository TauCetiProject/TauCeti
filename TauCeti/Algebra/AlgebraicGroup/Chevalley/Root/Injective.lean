/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Basic
import TauCeti.FieldTheory.IsAlgClosed.Units
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Injectivity and separation of Chevalley root subgroups over integral domains

For an arbitrary Chevalley datum `D`, every root element with additive parameter one is
nonidentity over every nontrivial commutative ring
(`ChevalleyDatum.rootSubgroupPoints_ofAdd_one_ne_one`). Over any integral domain `A` — including
`ℤ`, `𝔽₂`, and fields of small characteristic — every root subgroup `D.rootSubgroupPoints γ A` is
injective, and root subgroups attached to distinct roots have trivial intersection; distinct
roots have distinct root-subgroup images over every nontrivial commutative ring
(`ChevalleyDatum.range_rootSubgroupPoints_eq_iff`).

The argument reduces to an algebraically closed field by passing to
`AlgebraicClosure (FractionRing A)`, where the units are divisible and the field is infinite:

* Over a field with divisible units, every nonzero root character is surjective on torus points
  (`TauCeti.torusCharacter_surjective`), so the pinning equation scales any nonzero parameter to
  `1`, where nontriviality already holds.
* If two distinct roots share a nontrivial element over an infinite field, conjugating by the
  annihilator of the first root character forces the second root character to be proportional to it
  (`TauCeti.smul_eq_smul_of_torusCharacter_eq_one`). Reducedness of the pinned root datum leaves
  only the opposite root, which is ruled out by the opposite-intersection theorem via
  `ChevalleyDatum.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.rootSubgroupPoints_injective`: every root subgroup of a
  Chevalley datum is injective over every integral domain.
* `TauCeti.DynkinType.ChevalleyDatum.eq_zero_of_rootSubgroupPoints_eq`: equal root elements at
  distinct roots over an integral domain must both have parameter zero.
* `TauCeti.DynkinType.ChevalleyDatum.disjoint_range_rootSubgroupPoints`: distinct roots give
  disjoint root subgroups over every integral domain.
* `TauCeti.DynkinType.ChevalleyDatum.range_rootSubgroupPoints_eq_iff`: distinct roots have
  distinct root-subgroup images over every nontrivial commutative ring.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 3, Lemmas 17–19 and Theorem 4.
* R. W. Carter, *Simple Groups of Lie Type*, §§5.3 and 7.1.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open Multiplicative

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

private theorem rootSubgroupPoints_injective_of_rootable (γ : Fin t.numRoots)
    (K : Type v) [Field K] [RootableBy Kˣ ℕ] :
    Function.Injective (D.rootSubgroupPoints γ K) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  by_contra hne
  have ha : toAdd u ≠ 0 := fun h0 => hne (by simpa [h0] using (ofAdd_toAdd u).symm)
  obtain ⟨s, hs⟩ := torusCharacter_surjective (R := K) (D.coordinateRoot_ne_zero γ)
    (Units.mk0 (toAdd u) ha)⁻¹
  dsimp only at hs
  have hconj := D.torusPoints_conj_rootSubgroupPoints γ K s (toAdd u)
  rw [ofAdd_toAdd, hu, mul_one, mul_inv_cancel, hs, Units.val_inv_eq_inv_val,
    Units.val_mk0, inv_mul_cancel₀ ha] at hconj
  exact D.rootSubgroupPoints_ofAdd_one_ne_one K γ hconj.symm

/-- **Every root subgroup of a Chevalley datum is injective over every integral domain.** -/
theorem rootSubgroupPoints_injective (γ : Fin t.numRoots) (A : Type v) [CommRing A] [IsDomain A] :
    Function.Injective (D.rootSubgroupPoints γ A) := by
  intro u v huv
  let K := AlgebraicClosure (FractionRing A)
  let f : A →+* K := (algebraMap (FractionRing A) K).comp (algebraMap A (FractionRing A))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing A) K).injective.comp (IsFractionRing.injective A (FractionRing A))
  have hmap := congrArg ((D.pointsPresentation A).map (D.pointsPresentation K) f) huv
  simp only [D.map_rootSubgroupPoints] at hmap
  exact toAdd.injective (hf (congrArg toAdd (D.rootSubgroupPoints_injective_of_rootable γ K hmap)))

private theorem eq_zero_of_rootSubgroupPoints_eq_infinite {K : Type v} [Field K] [Infinite K]
    {α β : Fin t.numRoots} (hαβ : α ≠ β) {a b : K}
    (h : D.rootSubgroupPoints α K (ofAdd a) = D.rootSubgroupPoints β K (ofAdd b)) :
    a = 0 ∧ b = 0 := by
  suffices ha : a = 0 by
    refine ⟨ha, ?_⟩
    rw [ha, ofAdd_zero, map_one] at h
    simpa using congrArg toAdd (D.rootSubgroupPoints_injective β K (h.symm.trans (map_one _).symm))
  by_contra ha
  have hb : b ≠ 0 := by
    rintro rfl
    rw [ofAdd_zero, map_one] at h
    exact ha <| by
      simpa using congrArg toAdd (D.rootSubgroupPoints_injective α K (h.trans (map_one _).symm))
  have hker : ∀ s : Fin t.rank → Kˣ,
      torusCharacter s (D.coordinateRoot α) = 1 → torusCharacter s (D.coordinateRoot β) = 1 := by
    intro s hsα
    have hconj := congrArg (fun g => D.torusPoints K s * g * (D.torusPoints K s)⁻¹) h
    rw [D.torusPoints_conj_rootSubgroupPoints, D.torusPoints_conj_rootSubgroupPoints,
      hsα, Units.val_one, one_mul, h] at hconj
    have heq : b = (torusCharacter s (D.coordinateRoot β) : K) * b := by
      simpa using congrArg toAdd (D.rootSubgroupPoints_injective β K hconj)
    exact Units.ext ((mul_right_cancel₀ hb (by simpa using heq.symm)).trans rfl)
  obtain ⟨i, hi⟩ : ∃ i, D.coordinateRoot α i ≠ 0 := Function.ne_iff.mp (D.coordinateRoot_ne_zero α)
  rcases D.eq_or_eq_neg_of_smul_coordinateRoot_eq hi
      (smul_eq_smul_of_torusCharacter_eq_one hker i) with heq | hneg
  · exact hαβ ((t.simplyConnectedRootDatum ht).root.injective heq)
  · have hβ : β = (t.simplyConnectedRootDatum ht).reflectionPerm α α :=
      (t.simplyConnectedRootDatum ht).root.injective <| by
        rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, hneg, neg_neg]
    have hcontra {γ δ : Fin t.numRoots} {x y : K} (hy : y ≠ 0)
        (hγ : γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
        (hδ : δ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht))
        (heq' : D.rootSubgroupPoints γ K (ofAdd x) = D.rootSubgroupPoints δ K (ofAdd y)) :
        False := by
      have hmem : D.rootSubgroupPoints δ K (ofAdd y) ∈ D.borelSubgroup K :=
        heq' ▸ D.positivePoints_le_borelSubgroup K (D.rootSubgroupPoints_mem_positivePoints K hγ _)
      have h1 := (D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots K hδ _).mp hmem
      exact hy <| by
        simpa using congrArg toAdd (D.rootSubgroupPoints_injective δ K (h1.trans (map_one _).symm))
    rcases mem_posRoots_or_mem_negRoots (t.rationalRootSystem ht) (t.rationalBase ht) α with
        hpos | hneg'
    · exact hcontra hb hpos
        (by rw [hβ, ← t.reflectionPerm_rationalRootSystem ht]
            exact (reflectionPerm_self_mem_negRoots_iff_mem_posRoots _ _ _).mpr hpos) h
    · exact hcontra ha
        (by rw [hβ, ← t.reflectionPerm_rationalRootSystem ht]
            exact (reflectionPerm_self_mem_posRoots_iff_mem_negRoots _ _ _).mpr hneg') hneg' h.symm

/-- Over an integral domain, if two root elements at distinct roots are equal then both
additive parameters are zero. -/
theorem eq_zero_of_rootSubgroupPoints_eq {A : Type v} [CommRing A] [IsDomain A]
    {α β : Fin t.numRoots} (hαβ : α ≠ β) {a b : A}
    (h : D.rootSubgroupPoints α A (ofAdd a) = D.rootSubgroupPoints β A (ofAdd b)) :
    a = 0 ∧ b = 0 := by
  let K := AlgebraicClosure (FractionRing A)
  let f : A →+* K := (algebraMap (FractionRing A) K).comp (algebraMap A (FractionRing A))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing A) K).injective.comp (IsFractionRing.injective A (FractionRing A))
  have hmap := congrArg ((D.pointsPresentation A).map (D.pointsPresentation K) f) h
  simp only [D.map_rootSubgroupPoints, toAdd_ofAdd] at hmap
  obtain ⟨ha, hb⟩ := D.eq_zero_of_rootSubgroupPoints_eq_infinite hαβ hmap
  exact ⟨hf (ha.trans (map_zero f).symm), hf (hb.trans (map_zero f).symm)⟩

/-- **Distinct roots have disjoint root subgroups** over every integral domain. -/
theorem disjoint_range_rootSubgroupPoints (A : Type v) [CommRing A] [IsDomain A]
    {α β : Fin t.numRoots} (hαβ : α ≠ β) :
    Disjoint (D.rootSubgroupPoints α A).range (D.rootSubgroupPoints β A).range := by
  rw [Subgroup.disjoint_def]
  rintro g ⟨u, rfl⟩ ⟨v, hv⟩
  have h := (D.eq_zero_of_rootSubgroupPoints_eq hαβ (a := toAdd u) (b := toAdd v) <| by
    simpa only [ofAdd_toAdd] using hv.symm).1
  rw [toAdd.injective (h.trans (toAdd_one (α := A)).symm), map_one]

/-- **Distinct roots give distinct root-subgroup images** over every nontrivial commutative
ring. -/
@[simp]
theorem range_rootSubgroupPoints_eq_iff (A : Type v) [CommRing A] [Nontrivial A]
    (α β : Fin t.numRoots) :
    (D.rootSubgroupPoints α A).range = (D.rootSubgroupPoints β A).range ↔ α = β := by
  refine ⟨fun h => by_contra fun hne => ?_, fun h => h ▸ rfl⟩
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  let _ : M.IsMaximal := hM
  obtain ⟨u, hu⟩ : D.rootSubgroupPoints α A (ofAdd 1) ∈ (D.rootSubgroupPoints β A).range :=
    h ▸ ⟨ofAdd 1, rfl⟩
  have hmap := congrArg ((D.pointsPresentation A).map (D.pointsPresentation (A ⧸ M))
    (Ideal.Quotient.mk M)) hu
  simp only [D.map_rootSubgroupPoints, toAdd_ofAdd, map_one] at hmap
  have ha := (D.eq_zero_of_rootSubgroupPoints_eq hne hmap.symm).1
  exact one_ne_zero (α := A ⧸ M) ha

end TauCeti.DynkinType.ChevalleyDatum
