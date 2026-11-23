/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Frobenius.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
public import Mathlib.FieldTheory.Perfect
import TauCeti.Algebra.AlgebraicGroup.Chevalley.HomExt
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Standard and based endomorphisms of Chevalley groups

An endomorphism `F` of the points of a Chevalley datum `D` over a commutative ring `A` is
**standard** (`ChevalleyDatum.IsStandardEndomorphism`) if it maps every root subgroup onto a
root subgroup, and **based** (`ChevalleyDatum.IsBasedEndomorphism`) if in addition it maps
every positive root subgroup onto a positive root subgroup. Over a nontrivial ring, a standard
endomorphism sending `D.torusPoints A` into `D.borelSubgroup A` is based if and only if it maps
`D.borelSubgroup A` into itself (`ChevalleyDatum.isBasedEndomorphism_iff_map_borelSubgroup_le`).

Standard examples arise from Weyl conjugation (`isStandardEndomorphism_conj_weylElement`,
`isStandardEndomorphism_conj_weylSubgroup`) and Frobenius over rings where the iterated Frobenius
is surjective (`isBasedEndomorphism_frobenius_of_surjective`, `isBasedEndomorphism_frobenius`).
Composing Frobenius with conjugation by a pinned simple Weyl representative yields a composite
that is standard whenever the iterated Frobenius on `A` is surjective
(`isStandardEndomorphism_conj_weylElement_comp_frobenius`) and is not based whenever `A` is
nontrivial (`not_isBasedEndomorphism_conj_weylElement_comp_frobenius`). For every Chevalley datum,
its square equals `Int(nᵢ²) ∘ Frob_{p^(2k)}` on all points
(`conj_weylElement_comp_frobenius_comp_self`); in type `A₁`, its character map is `-(p ^ k) • 1`
and its square agrees with `frobenius p (2 * k)` on `D.rootTorusSubgroup A`.

## Main definitions

* `TauCeti.DynkinType.ChevalleyDatum.IsStandardEndomorphism`: maps every root subgroup onto a
  root subgroup.
* `TauCeti.DynkinType.ChevalleyDatum.IsBasedEndomorphism`: standard and maps positive root
  subgroups onto positive root subgroups.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.isBasedEndomorphism_iff_map_borelSubgroup_le`: over a
  nontrivial ring, a standard endomorphism sending `D.torusPoints A` into `D.borelSubgroup A` is
  based if and only if it maps `D.borelSubgroup A` into itself.
* `TauCeti.DynkinType.ChevalleyDatum.isBasedEndomorphism_frobenius` and
  `TauCeti.DynkinType.ChevalleyDatum.not_isBasedEndomorphism_conj_weylElement_comp_frobenius`:
  concrete based and non-based standard endomorphisms.
* `TauCeti.DynkinType.ChevalleyDatum.conj_weylElement_comp_frobenius_comp_self` and
  `ChevalleyDatum.conj_weylElement_comp_frobenius_comp_self_eq_on_rootTorusSubgroup_typeA1`:
  the general square formula for `Int(nᵢ) ∘ Frob_{p^k}` and its specialization to
  `D.rootTorusSubgroup A` in type `A₁`.

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
theorem IsBasedEndomorphism.isStandard {F : D.points A →* D.points A}
    (h : D.IsBasedEndomorphism A F) : D.IsStandardEndomorphism A F :=
  h.1

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
  ⟨hF.isStandard.comp hG.isStandard, fun α hα => by
    obtain ⟨β, hβ, hmapG⟩ := hG.2 α hα
    obtain ⟨γ, hγ, hmapF⟩ := hF.2 β hβ
    exact ⟨γ, hγ, by rw [← Subgroup.map_map, hmapG, hmapF]⟩⟩

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

/-! ## Concrete standard and based endomorphisms -/

section Examples

variable (A : Type v) [CommRing A]

/-- Conjugation by a pinned simple Weyl representative is a standard endomorphism over every
commutative ring. -/
theorem isStandardEndomorphism_conj_weylElement (i : Fin t.rank) :
    D.IsStandardEndomorphism A
      (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom := fun α => by
  refine ⟨(t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) α, ?_⟩
  let ε : Aˣ := Units.map (Int.castRingHom A).toMonoidHom
    (t.chevalleyWeylSign ht (t.simpleIndex ht i) α)
  refine MonoidHom.map_range_eq_of_surjective _ _ _
    ((ofAdd.surjective.comp (Units.mulLeft_bijective ε).surjective).comp toAdd.surjective)
    fun u => ?_
  simpa [ε, MulAut.conj_apply] using D.weylElement_conj_rootSubgroupPoints i α A (toAdd u)

/-- Conjugation by any element of the Weyl subgroup is a standard endomorphism over every field. -/
theorem isStandardEndomorphism_conj_weylSubgroup (K : Type v) [Field K] (g : D.weylSubgroup K) :
    D.IsStandardEndomorphism K (MulAut.conj (g : D.points K)).toMonoidHom :=
  fun α => ⟨(t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K g) α,
    D.map_range_rootSubgroupPoints_conj K g α⟩

/-- Frobenius is a based endomorphism whenever the iterated Frobenius on `A` is surjective. -/
theorem isBasedEndomorphism_frobenius_of_surjective (p k : ℕ) [ExpChar A p]
    (hsurj : Function.Surjective (iterateFrobenius A p k)) :
    D.IsBasedEndomorphism A (D.frobenius p k A) := by
  have hmap (α : Fin t.numRoots) :
      (D.rootSubgroupPoints α A).range.map (D.frobenius p k A) =
        (D.rootSubgroupPoints α A).range :=
    MonoidHom.map_range_eq_of_surjective _ _ _
      ((ofAdd.surjective.comp hsurj).comp toAdd.surjective) fun u => by
        rw [← ofAdd_toAdd u, D.frobenius_rootSubgroupPoints, Function.comp_apply,
          Function.comp_apply, toAdd_ofAdd, iterateFrobenius_def]
  exact ⟨fun α => ⟨α, hmap α⟩, fun α hα => ⟨α, hα, hmap α⟩⟩

/-- Over a perfect ring of exponential characteristic `p`, every Frobenius endomorphism of a
Chevalley datum is based. -/
theorem isBasedEndomorphism_frobenius (p k : ℕ) [ExpChar A p] [PerfectRing A p] :
    D.IsBasedEndomorphism A (D.frobenius p k A) :=
  D.isBasedEndomorphism_frobenius_of_surjective A p k (bijective_iterateFrobenius A p k).surjective

/-- Composing Frobenius with conjugation by a pinned simple Weyl representative is standard
whenever the iterated Frobenius on `A` is surjective. -/
theorem isStandardEndomorphism_conj_weylElement_comp_frobenius (i : Fin t.rank) (p k : ℕ)
    [ExpChar A p] (hsurj : Function.Surjective (iterateFrobenius A p k)) :
    D.IsStandardEndomorphism A
      ((MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom.comp
        (D.frobenius p k A)) :=
  (D.isStandardEndomorphism_conj_weylElement A i).comp
    (D.isBasedEndomorphism_frobenius_of_surjective A p k hsurj).isStandard

/-- Conjugation by a pinned simple Weyl representative is never based over a nontrivial ring:
it sends the `i`-th positive simple root subgroup to its opposite negative root subgroup. -/
theorem not_isBasedEndomorphism_conj_weylElement [Nontrivial A] (i : Fin t.rank) :
    ¬ D.IsBasedEndomorphism A
      (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom := fun hbased => by
  have hB := (isBasedEndomorphism_iff_map_borelSubgroup_le_of_isCharacterMap
    (D.isStandardEndomorphism_conj_weylElement A i)
    (D.isCharacterMap_conj_weylElement i A)).mp hbased
  obtain ⟨b, hb⟩ := D.exists_weylElement_conj_notMem_borelSubgroup A i
  exact hb (hB ⟨b.val, b.property, rfl⟩)

/-- Composing Frobenius with conjugation by a pinned simple Weyl representative is never based over
a nontrivial ring. -/
theorem not_isBasedEndomorphism_conj_weylElement_comp_frobenius [Nontrivial A] (i : Fin t.rank)
    (p k : ℕ) [ExpChar A p] :
    ¬ D.IsBasedEndomorphism A
      ((MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom.comp
        (D.frobenius p k A)) := fun hbased => by
  have hmem :
      ((MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom.comp
          (D.frobenius p k A))
        (D.rootSubgroupPoints (t.simpleIndex ht i) A (ofAdd 1)) ∈ D.borelSubgroup A :=
    D.positivePoints_le_borelSubgroup A <| hbased.map_positivePoints_le
      ⟨_, D.rootSubgroupPoints_mem_positivePoints A
        (support_subset_posRoots _ _ (t.simpleIndex_mem_support i)) (ofAdd 1), rfl⟩
  simp only [MonoidHom.comp_apply, D.frobenius_rootSubgroupPoints, one_pow,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    D.weylElement_conj_rootSubgroupPoints_simpleIndex_mem_borelSubgroup_iff] at hmem
  exact D.rootSubgroupPoints_ofAdd_one_ne_one A (t.simpleIndex ht i) hmem

/-- The character map of `Int(nᵢ) ∘ Frob_{p^k}` is `(p ^ k) • sᵢ` on the actual character
lattice. -/
theorem isCharacterMap_conj_weylElement_comp_frobenius (i : Fin t.rank) (p k : ℕ) [ExpChar A p] :
    IsCharacterMap (D.torusPoints A)
      ((MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom.comp
        (D.frobenius p k A))
      ((p ^ k : ℕ) •
        (D.weylCharacterAut
          (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht)
            (t.simpleIndex ht i))).toLinearMap) := by
  simpa only [smul_mul_assoc, one_mul] using
    (D.isCharacterMap_conj_weylElement i A).comp (D.isCharacterMap_frobenius p k A)

private theorem frobenius_weylElement_one (i : Fin t.rank) (p k : ℕ) [ExpChar A p] :
    D.frobenius p k A (D.weylElement (t.simpleIndex ht i) A 1) =
      D.weylElement (t.simpleIndex ht i) A 1 := by
  have hneg : (-1 : A) ^ (p ^ k) = -1 := by rw [← iterateFrobenius_def, map_neg, map_one]
  simp only [weylElement_def, inv_one, Units.val_one, map_mul,
    D.frobenius_rootSubgroupPoints, one_pow, hneg]

private theorem map_frobenius_rootTorusSubgroup_le (p k : ℕ) [ExpChar A p] :
    (D.rootTorusSubgroup A).map (D.frobenius p k A) ≤ D.rootTorusSubgroup A := by
  rw [Subgroup.map_le_iff_le_comap, D.rootTorusSubgroup_le_iff]
  refine ⟨fun γ u => ?_, fun s => ?_⟩
  · rw [Subgroup.mem_comap, ← ofAdd_toAdd u, D.frobenius_rootSubgroupPoints]
    exact D.rootSubgroupPoints_mem_rootTorusSubgroup γ A _
  · rw [Subgroup.mem_comap, D.frobenius_torusPoints]
    exact D.torusPoints_mem_rootTorusSubgroup A _

/-- For every Chevalley datum and every ring `A` of exponential characteristic `p`, squaring
`Int(nᵢ) ∘ Frob_{p^k}` equals `Int(nᵢ²) ∘ Frob_{p^(2k)}` on all of `D.points A`. -/
theorem conj_weylElement_comp_frobenius_comp_self (i : Fin t.rank) (p k : ℕ) [ExpChar A p] :
    let F := (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom.comp
      (D.frobenius p k A)
    F.comp F =
      (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1 *
        D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom.comp
        (D.frobenius p (2 * k) A) := by
  intro F
  ext1 y
  have hadd : D.frobenius p (2 * k) A y = D.frobenius p k A (D.frobenius p k A y) := by
    have h := D.frobenius_add p k A k
    rw [← two_mul] at h
    exact DFunLike.congr_fun h y
  dsimp only [F, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    D.frobenius_weylElement_one A i p k, ← hadd, mul_inv_rev]
  simp only [mul_assoc]

/-! ### Regression example in type `A₁` -/

section TypeA1

/-- In type `A₁`, the composite `Int(n₀) ∘ Frob_{p^k}` has character map `-(p ^ k : ℤ) • 1`. -/
theorem isCharacterMap_conj_weylElement_comp_frobenius_typeA1 {h1 : (DynkinType.A 1).Valid}
    (D : ChevalleyDatum (DynkinType.A 1) h1) (i : Fin (DynkinType.A 1).rank)
    (p k : ℕ) [ExpChar A p] :
    IsCharacterMap (D.torusPoints A)
      ((MulAut.conj (D.weylElement ((DynkinType.A 1).simpleIndex h1 i) A 1)).toMonoidHom.comp
        (D.frobenius p k A))
      (-(p ^ k : ℤ) • 1) := by
  have h := D.isCharacterMap_conj_weylElement_comp_frobenius A i p k
  rw [D.weylCharacterAut_simpleIndex_typeA1 i, smul_neg, ← natCast_zsmul, Nat.cast_pow,
    ← neg_smul] at h
  exact h

private theorem torusCharacter_simpleCorootParameter_neg_one_typeA1 {h1 : (DynkinType.A 1).Valid}
    (D : ChevalleyDatum (DynkinType.A 1) h1) (i : Fin (DynkinType.A 1).rank) :
    torusCharacter (D.simpleCorootParameter i A (-1))
      (D.coordinateRoot ((DynkinType.A 1).simpleIndex h1 i)) = 1 := by
  have h := D.torusCharacter_simpleCorootParameter i A (-1)
    ⟨_, D.root_mem_weightLattice ((DynkinType.A 1).simpleIndex h1 i)⟩
  have hp : ((DynkinType.A 1).simplyConnectedRootDatum h1).root
      ((DynkinType.A 1).simpleIndex h1 i) i = 2 := by
    rw [DynkinType.root_simpleIndex]
    exact (DynkinType.pairing_simpleIndex (DynkinType.A 1) h1 i i).symm.trans
      (RootPairing.pairing_same ((DynkinType.A 1).simplyConnectedRootDatum h1) _)
  simpa only [← D.coordinateRoot_def, Submodule.coe_mk, hp, zpow_ofNat, neg_one_sq] using h

private theorem conj_weylElement_sq_eq_on_rootTorusSubgroup_typeA1 {h1 : (DynkinType.A 1).Valid}
    (D : ChevalleyDatum (DynkinType.A 1) h1) (i : Fin (DynkinType.A 1).rank) :
    let n := D.weylElement ((DynkinType.A 1).simpleIndex h1 i) A 1
    (MulAut.conj (n * n)).toMonoidHom.comp (D.rootTorusSubgroup A).subtype =
      (D.rootTorusSubgroup A).subtype := by
  intro n
  have hch := torusCharacter_simpleCorootParameter_neg_one_typeA1 A D i
  refine D.rootTorusSubgroup_hom_ext _ _ (fun j u => ?_) (fun j u => ?_) (fun s => ?_)
  · obtain rfl : j = i := (Fin.eq_zero j).trans (Fin.eq_zero i).symm
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, n, D.weylElement_mul_self, D.simpleCorootPoints_eq_torusPoints]
    rw [← ofAdd_toAdd u, D.torusPoints_conj_rootSubgroupPoints, hch, Units.val_one, one_mul]
  · obtain rfl : j = i := (Fin.eq_zero j).trans (Fin.eq_zero i).symm
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, n, D.weylElement_mul_self, D.simpleCorootPoints_eq_torusPoints]
    rw [← ofAdd_toAdd u, D.torusPoints_conj_rootSubgroupPoints,
      D.coordinateRoot_reflectionPerm_self, torusCharacter_neg, hch, inv_one, Units.val_one,
      one_mul]
  · simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, n, D.weylElement_mul_self, D.simpleCorootPoints_eq_torusPoints]
    exact ((Commute.all (D.simpleCorootParameter i A (-1)) s).map
      (D.torusPoints A)).mul_inv_cancel

/-- In type `A₁`, the square of the composite `Int(n₀) ∘ Frob_{p^k}` agrees with
`D.frobenius p (2 * k) A` on `D.rootTorusSubgroup A`, because `n₀² = h₀(-1)` is central on every
root subgroup and on the torus. -/
theorem conj_weylElement_comp_frobenius_comp_self_eq_on_rootTorusSubgroup_typeA1
    {h1 : (DynkinType.A 1).Valid} (D : ChevalleyDatum (DynkinType.A 1) h1)
    (i : Fin (DynkinType.A 1).rank) (p k : ℕ) [ExpChar A p]
    {x : D.points A} (hx : x ∈ D.rootTorusSubgroup A) :
    let F := (MulAut.conj (D.weylElement ((DynkinType.A 1).simpleIndex h1 i) A 1)).toMonoidHom.comp
      (D.frobenius p k A)
    F (F x) = D.frobenius p (2 * k) A x := by
  intro F
  have hsq := DFunLike.congr_fun (D.conj_weylElement_comp_frobenius_comp_self A i p k) x
  have hmem := D.map_frobenius_rootTorusSubgroup_le A p (2 * k) ⟨x, hx, rfl⟩
  have hcent := DFunLike.congr_fun
    (conj_weylElement_sq_eq_on_rootTorusSubgroup_typeA1 A D i)
    ⟨D.frobenius p (2 * k) A x, hmem⟩
  simpa only [F, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply] using hsq.trans hcent

end TypeA1

end Examples

end TauCeti.DynkinType.ChevalleyDatum
