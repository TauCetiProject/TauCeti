/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Frobenius
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.SimplyConnected
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.DiagramAutomorphism
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.Root.Basic
public import Mathlib.FieldTheory.Perfect
import TauCeti.Algebra.AlgebraicGroup.Chevalley.HomExt
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.CharacterMap
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.Root.Subgroup

/-!
# Standard and based endomorphisms of Chevalley groups

An endomorphism `F` of the points of a Chevalley datum `D` over a commutative ring `A` is
**standard** (`ChevalleyDatum.IsStandardEndomorphism`) if it maps every root subgroup onto a
root subgroup, and **based** (`ChevalleyDatum.IsBasedEndomorphism`) if in addition it maps
every positive root subgroup onto a positive root subgroup. When `F` preserves the Borel-type
subgroup's torus part over a nontrivial ring, basedness is equivalent to preserving the
Borel-type subgroup (`ChevalleyDatum.isBasedEndomorphism_iff_map_borelSubgroup_le`).

Standard examples arise from Weyl conjugation (`isStandardEndomorphism_conj_weylElement`,
`isStandardEndomorphism_conj_weylSubgroup`), Frobenius over rings where the iterated Frobenius
is surjective (`isBasedEndomorphism_frobenius_of_surjective`, `isBasedEndomorphism_frobenius`),
and diagram automorphisms of the simply connected Chevalley datum
(`DynkinType.scChevalleyDatumDiagramAut`, `isBasedEndomorphism_scChevalleyDatumDiagramAut`).
By contrast, composing Frobenius with conjugation by a pinned simple Weyl representative yields
a standard endomorphism that is not based; in type `A₁` its character map is `-(p ^ k) • 1`
and its square agrees with `frobenius p (2 * k)` on `D.rootTorusSubgroup A`.

## Main definitions

* `TauCeti.DynkinType.ChevalleyDatum.IsStandardEndomorphism`: maps every root subgroup onto a
  root subgroup.
* `TauCeti.DynkinType.ChevalleyDatum.IsBasedEndomorphism`: standard and maps positive root
  subgroups onto positive root subgroups.
* `TauCeti.DynkinType.scChevalleyDatumDiagramAut`: the diagram automorphism on the points of
  `scChevalleyDatum`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.isBasedEndomorphism_iff_map_borelSubgroup_le`: basedness
  is equivalent to preserving `borelSubgroup` for a standard endomorphism preserving the torus.
* `TauCeti.DynkinType.ChevalleyDatum.isBasedEndomorphism_frobenius`,
  `TauCeti.DynkinType.isBasedEndomorphism_scChevalleyDatumDiagramAut`, and
  `TauCeti.DynkinType.ChevalleyDatum.not_isBasedEndomorphism_conj_weylElement_comp_frobenius`:
  concrete based and non-based standard endomorphisms.
* `TauCeti.DynkinType.ChevalleyDatum.isCharacterMap_conj_weylSubgroup_hom` and
  `TauCeti.DynkinType.isCharacterMap_conj_scChevalleyDatumDiagramAut`: how Weyl conjugation and
  diagram-automorphism conjugation transform character maps.

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
open TauCeti.UniversalEnvelopingAlgebra

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

/-- An endomorphism sending each root element `x_α(u)` to `x_{β α}(g_α(u))` with each `g_α`
surjective maps the root subgroup of `α` onto that of `β α`. -/
theorem map_range_rootSubgroupPoints_eq_of_surjective {F : D.points A →* D.points A}
    {α β : Fin t.numRoots} {g : A → A} (hg : Function.Surjective g)
    (hF : ∀ u : A, F (D.rootSubgroupPoints α A (ofAdd u)) =
      D.rootSubgroupPoints β A (ofAdd (g u))) :
    (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints β A).range := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨ofAdd (g (toAdd u)), by rw [← hF (toAdd u), ofAdd_toAdd]⟩
  · rintro _ ⟨v, rfl⟩
    obtain ⟨u, hu⟩ := hg (toAdd v)
    exact ⟨D.rootSubgroupPoints α A (ofAdd u), ⟨ofAdd u, rfl⟩, by rw [hF u, hu, ofAdd_toAdd]⟩

/-- Over a nontrivial ring, a standard endomorphism preserving the torus part of the Borel-type
subgroup is based if and only if it maps `D.borelSubgroup A` into itself. -/
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
  refine map_range_rootSubgroupPoints_eq_of_surjective (g := fun u : A => (ε : A) * u)
    (fun v => ⟨((ε⁻¹ : Aˣ) : A) * v, by simp [← mul_assoc]⟩) fun u => ?_
  simpa [ε, MulAut.conj_apply] using D.weylElement_conj_rootSubgroupPoints i α A u

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
    map_range_rootSubgroupPoints_eq_of_surjective (g := iterateFrobenius A p k) hsurj fun u => by
      rw [D.frobenius_rootSubgroupPoints, iterateFrobenius_def]
  exact ⟨fun α => ⟨α, hmap α⟩, fun α hα => ⟨α, hα, hmap α⟩⟩

/-- Over a perfect ring of exponential characteristic `p`, every Frobenius endomorphism of a
Chevalley datum is based. -/
theorem isBasedEndomorphism_frobenius (p k : ℕ) [ExpChar A p] [PerfectRing A p] :
    D.IsBasedEndomorphism A (D.frobenius p k A) :=
  D.isBasedEndomorphism_frobenius_of_surjective A p k fun a => by
    obtain ⟨b, hb⟩ := (PerfectRing.bijective_frobenius (R := A) (p := p ^ k)).surjective a
    exact ⟨b, by simpa only [iterateFrobenius_def] using hb⟩

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

/-- Composing Frobenius with conjugation by a pinned simple Weyl representative is standard yet
not based over any nontrivial ring with surjective iterated Frobenius. -/
theorem not_isBasedEndomorphism_conj_weylElement_comp_frobenius [Nontrivial A] (i : Fin t.rank)
    (p k : ℕ) [ExpChar A p] (hsurj : Function.Surjective (iterateFrobenius A p k)) :
    ¬ D.IsBasedEndomorphism A
      ((MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom.comp
        (D.frobenius p k A)) := fun hbased => by
  have hB := (isBasedEndomorphism_iff_map_borelSubgroup_le_of_isCharacterMap
    (D.isStandardEndomorphism_conj_weylElement_comp_frobenius A i p k hsurj)
    ((D.isCharacterMap_conj_weylElement i A).comp (D.isCharacterMap_frobenius p k A))).mp hbased
  have hmem := hB ⟨_, D.positivePoints_le_borelSubgroup A
    (D.rootSubgroupPoints_mem_positivePoints A
      (support_subset_posRoots _ _ (t.simpleIndex_mem_support i)) (ofAdd 1)), rfl⟩
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

/-! ### Regression example in type `A₁` -/

section TypeA1

private theorem eq_of_fin_rank_typeA1 (i j : Fin (DynkinType.A 1).rank) : i = j := by
  have hi := i.isLt; have hj := j.isLt
  simp [DynkinType.rank] at hi hj
  exact Fin.ext (by omega)

/-- In type `A₁`, the unique simple reflection acts as negation on the actual character lattice
of every Chevalley datum. -/
theorem weylCharacterAut_simpleIndex_typeA1 {h1 : (DynkinType.A 1).Valid}
    (D : ChevalleyDatum (DynkinType.A 1) h1) (i : Fin (DynkinType.A 1).rank) :
    (D.weylCharacterAut
      (RootPairing.weylGroup.ofIdx ((DynkinType.A 1).simplyConnectedRootDatum h1)
        ((DynkinType.A 1).simpleIndex h1 i))).toLinearMap = -1 := by
  refine LinearMap.ext fun χ => D.weightLatticeEmbedding_injective ?_
  rw [LinearEquiv.coe_coe, D.weightLatticeEmbedding_weylCharacterAut,
    RootPairing.weylGroup.ofIdx_smul, RootPairing.Equiv.reflection_smul,
    RootPairing.reflection_apply, (DynkinType.A 1).coroot'_simpleIndex_apply h1]
  ext j
  obtain rfl : j = i := eq_of_fin_rank_typeA1 j i
  have hroot : ((DynkinType.A 1).simplyConnectedRootDatum h1).root
      ((DynkinType.A 1).simpleIndex h1 j) j = 2 := by
    rw [DynkinType.root_simpleIndex]
    exact (DynkinType.pairing_simpleIndex (DynkinType.A 1) h1 j j).symm.trans
      (RootPairing.pairing_same ((DynkinType.A 1).simplyConnectedRootDatum h1) _)
  simp only [LinearMap.neg_apply, one_apply_eq_self, map_neg, Pi.sub_apply, Pi.smul_apply,
    Pi.neg_apply, smul_eq_mul, hroot]
  ring

/-- In type `A₁`, the non-based standard endomorphism `Int(n₀) ∘ Frob_{p^k}` has character map
`-(p ^ k : ℤ) • 1`. -/
theorem isCharacterMap_conj_weylElement_comp_frobenius_typeA1 {h1 : (DynkinType.A 1).Valid}
    (D : ChevalleyDatum (DynkinType.A 1) h1) (i : Fin (DynkinType.A 1).rank)
    (p k : ℕ) [ExpChar A p] :
    IsCharacterMap (D.torusPoints A)
      ((MulAut.conj (D.weylElement ((DynkinType.A 1).simpleIndex h1 i) A 1)).toMonoidHom.comp
        (D.frobenius p k A))
      (-(p ^ k : ℤ) • 1) := by
  have h := D.isCharacterMap_conj_weylElement_comp_frobenius A i p k
  rw [weylCharacterAut_simpleIndex_typeA1 D i, smul_neg, ← natCast_zsmul, Nat.cast_pow,
    ← neg_smul] at h
  exact h

/-- In type `A₁`, the square of the non-based standard endomorphism `Int(n₀) ∘ Frob_{p^k}` agrees
with `D.frobenius p (2 * k) A` on `D.rootTorusSubgroup A`, because `n₀² = h₀(-1)` is central on
every root subgroup and on the torus. -/
theorem conj_weylElement_comp_frobenius_self_eq_typeA1 {h1 : (DynkinType.A 1).Valid}
    (D : ChevalleyDatum (DynkinType.A 1) h1) (i : Fin (DynkinType.A 1).rank)
    (p k : ℕ) [ExpChar A p] {x : D.points A} (hx : x ∈ D.rootTorusSubgroup A) :
    let F := (MulAut.conj (D.weylElement ((DynkinType.A 1).simpleIndex h1 i) A 1)).toMonoidHom.comp
      (D.frobenius p k A)
    F (F x) = D.frobenius p (2 * k) A x := by
  intro F
  let n := D.weylElement ((DynkinType.A 1).simpleIndex h1 i) A 1
  have hcomm_n : D.frobenius p k A n = n := by
    have hneg : (-1 : A) ^ (p ^ k) = -1 := by rw [← iterateFrobenius_def, map_neg, map_one]
    simp only [n, weylElement_def, inv_one, Units.val_one, map_mul,
      D.frobenius_rootSubgroupPoints, one_pow, hneg]
  have hF2 (y : D.points A) : F (F y) = n * n * D.frobenius p (2 * k) A y * (n * n)⁻¹ := by
    have hadd : D.frobenius p (2 * k) A y = D.frobenius p k A (D.frobenius p k A y) := by
      have h := D.frobenius_add p k A k
      rw [← two_mul] at h
      exact DFunLike.congr_fun h y
    change n * D.frobenius p k A (n * D.frobenius p k A y * n⁻¹) * n⁻¹ = _
    rw [map_mul, map_mul, map_inv, hcomm_n, ← hadd]; group
  have hch : torusCharacter (D.simpleCorootParameter i A (-1))
      (D.coordinateRoot ((DynkinType.A 1).simpleIndex h1 i)) = 1 := by
    have h := D.torusCharacter_simpleCorootParameter i A (-1)
      ⟨_, D.root_mem_weightLattice ((DynkinType.A 1).simpleIndex h1 i)⟩
    have hp : ((DynkinType.A 1).simplyConnectedRootDatum h1).root
        ((DynkinType.A 1).simpleIndex h1 i) i = 2 := by
      rw [DynkinType.root_simpleIndex]
      exact (DynkinType.pairing_simpleIndex (DynkinType.A 1) h1 i i).symm.trans
        (RootPairing.pairing_same ((DynkinType.A 1).simplyConnectedRootDatum h1) _)
    simpa only [← D.coordinateRoot_def, Submodule.coe_mk, hp, zpow_ofNat, neg_one_sq] using h
  have hcentral : ((MulAut.conj (n * n)).toMonoidHom.comp (D.rootTorusSubgroup A).subtype) =
      (D.rootTorusSubgroup A).subtype := by
    refine D.rootTorusSubgroup_hom_ext _ _ (fun j u => ?_) (fun j u => ?_) (fun s => ?_)
    · obtain rfl := eq_of_fin_rank_typeA1 j i
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, n, D.weylElement_mul_self, D.simpleCorootPoints_eq_torusPoints]
      rw [← ofAdd_toAdd u, D.torusPoints_conj_rootSubgroupPoints, hch, Units.val_one, one_mul]
    · obtain rfl := eq_of_fin_rank_typeA1 j i
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, n, D.weylElement_mul_self, D.simpleCorootPoints_eq_torusPoints]
      rw [← ofAdd_toAdd u, D.torusPoints_conj_rootSubgroupPoints,
        D.coordinateRoot_reflectionPerm_self, torusCharacter_neg, hch, inv_one, Units.val_one,
        one_mul]
    · simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, n, D.weylElement_mul_self, D.simpleCorootPoints_eq_torusPoints]
      exact ((Commute.all (D.simpleCorootParameter i A (-1)) s).map
        (D.torusPoints A)).mul_inv_cancel
  have hmem : D.frobenius p (2 * k) A x ∈ D.rootTorusSubgroup A := by
    have hmap : (D.rootTorusSubgroup A).map (D.frobenius p (2 * k) A) ≤ D.rootTorusSubgroup A := by
      rw [Subgroup.map_le_iff_le_comap, D.rootTorusSubgroup_le_iff]
      refine ⟨fun γ u => ?_, fun s => ?_⟩
      · rw [Subgroup.mem_comap, ← ofAdd_toAdd u, D.frobenius_rootSubgroupPoints]
        exact D.rootSubgroupPoints_mem_rootTorusSubgroup γ A _
      · rw [Subgroup.mem_comap, D.frobenius_torusPoints]
        exact D.torusPoints_mem_rootTorusSubgroup A _
    exact hmap ⟨x, hx, rfl⟩
  rw [hF2 x]
  simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply] using DFunLike.congr_fun hcentral ⟨D.frobenius p (2 * k) A x, hmem⟩

end TypeA1

end Examples

/-! ## Weyl conjugation of character maps -/

section WeylConj

variable (K : Type v) [Field K]

/-- Left-composing an endomorphism with conjugation by `g ∈ D.weylSubgroup K` right-multiplies
its character map by `weylCharacterAut (weylProjection K g)⁻¹`. -/
theorem isCharacterMap_conj_weylSubgroup_comp (g : D.weylSubgroup K)
    {F : D.points K →* D.points K} {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hφ : IsCharacterMap (D.torusPoints K) F φ) :
    IsCharacterMap (D.torusPoints K)
      ((MulAut.conj (g : D.points K)).toMonoidHom.comp F)
      (φ * (D.weylCharacterAut (D.weylProjection K g)⁻¹).toLinearMap) :=
  (D.isCharacterMap_conj_weylSubgroup K g).comp hφ

/-- Right-composing an endomorphism with conjugation by `g ∈ D.weylSubgroup K` left-multiplies
its character map by `weylCharacterAut (weylProjection K g)⁻¹`. -/
theorem isCharacterMap_comp_conj_weylSubgroup (g : D.weylSubgroup K)
    {F : D.points K →* D.points K} {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hφ : IsCharacterMap (D.torusPoints K) F φ) :
    IsCharacterMap (D.torusPoints K)
      (F.comp (MulAut.conj (g : D.points K)).toMonoidHom)
      ((D.weylCharacterAut (D.weylProjection K g)⁻¹).toLinearMap * φ) :=
  hφ.comp (D.isCharacterMap_conj_weylSubgroup K g)

/-- Conjugating an endomorphism `F` by `g ∈ D.weylSubgroup K` conjugates its character map by
`weylCharacterAut (weylProjection K g)`. -/
theorem isCharacterMap_conj_weylSubgroup_hom (g : D.weylSubgroup K)
    {F : D.points K →* D.points K} {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hφ : IsCharacterMap (D.torusPoints K) F φ) :
    IsCharacterMap (D.torusPoints K)
      (((MulAut.conj (g : D.points K)).toMonoidHom.comp F).comp
        (MulAut.conj (g : D.points K)⁻¹).toMonoidHom)
      ((D.weylCharacterAut (D.weylProjection K g)).toLinearMap * φ *
        (D.weylCharacterAut (D.weylProjection K g)⁻¹).toLinearMap) := by
  have hinv := D.isCharacterMap_conj_weylSubgroup K g⁻¹
  rw [Subgroup.coe_inv, MonoidHom.map_inv (D.weylProjection K), inv_inv] at hinv
  simpa only [mul_assoc] using (D.isCharacterMap_conj_weylSubgroup_comp K g hφ).comp hinv

end WeylConj

end TauCeti.DynkinType.ChevalleyDatum

namespace TauCeti.DynkinType

open Multiplicative
open TauCeti.UniversalEnvelopingAlgebra

universe v

attribute [local instance high] Algebra.toModule

variable {t : DynkinType} (ht : t.Valid) {σ τ : Equiv.Perm (Fin t.rank)}

/-! ## Diagram automorphisms on `scChevalleyDatum` -/

private noncomputable def scPointsEquiv (A : Type v) [CommRing A] :
    (t.scChevalleyDatum ht).points A ≃*
      kostantToralPointsSubgroup (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) A :=
  MulEquiv.subgroupCongr (t.chevalleyGroup_eq_kostantToralPointsSubgroup ht A)

/-- The diagram automorphism of the points of `t.scChevalleyDatum ht`, obtained by transporting
`t.scToralDiagramAutPoints ht hσ A` along `chevalleyGroup_eq_kostantToralPointsSubgroup`. -/
noncomputable def scChevalleyDatumDiagramAut (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] :
    MulAut ((t.scChevalleyDatum ht).points A) :=
  MulAut.congr (t.scPointsEquiv ht A).symm (t.scToralDiagramAutPoints ht hσ A)

private theorem scPointsEquiv_scChevalleyDatumDiagramAut (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] (g : (t.scChevalleyDatum ht).points A) :
    t.scPointsEquiv ht A (t.scChevalleyDatumDiagramAut ht hσ A g) =
      t.scToralDiagramAutPoints ht hσ A (t.scPointsEquiv ht A g) :=
  (t.scPointsEquiv ht A).apply_symm_apply _

/-- The identity diagram symmetry acts as the identity on `(t.scChevalleyDatum ht).points A`. -/
@[simp]
theorem scChevalleyDatumDiagramAut_one (A : Type v) [CommRing A] :
    t.scChevalleyDatumDiagramAut ht t.diagramSymmetry.one_mem A = 1 :=
  (congrArg (MulAut.congr (t.scPointsEquiv ht A).symm) (t.scToralDiagramAutPoints_one ht A)).trans
    (map_one _)

/-- Diagram automorphisms on `(t.scChevalleyDatum ht).points A` compose multiplicatively. -/
@[simp]
theorem scChevalleyDatumDiagramAut_mul (hσ : σ ∈ t.diagramSymmetry) (hτ : τ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] :
    t.scChevalleyDatumDiagramAut ht (t.diagramSymmetry.mul_mem hσ hτ) A =
      t.scChevalleyDatumDiagramAut ht hσ A * t.scChevalleyDatumDiagramAut ht hτ A :=
  (congrArg (MulAut.congr (t.scPointsEquiv ht A).symm)
    (t.scToralDiagramAutPoints_mul ht hσ hτ A)).trans (map_mul _ _ _)

/-- Inverting a diagram symmetry inverts its automorphism on `(t.scChevalleyDatum ht).points A`. -/
@[simp]
theorem scChevalleyDatumDiagramAut_inv (hσ : σ ∈ t.diagramSymmetry) (A : Type v) [CommRing A] :
    t.scChevalleyDatumDiagramAut ht (t.diagramSymmetry.inv_mem hσ) A =
      (t.scChevalleyDatumDiagramAut ht hσ A)⁻¹ :=
  (congrArg (MulAut.congr (t.scPointsEquiv ht A).symm)
    (t.scToralDiagramAutPoints_inv ht hσ A)).trans (map_inv _ _)

/-- Every order relation of a diagram symmetry holds on `(t.scChevalleyDatum ht).points A`. -/
theorem scChevalleyDatumDiagramAut_pow_eq_one (hσ : σ ∈ t.diagramSymmetry) (A : Type v)
    [CommRing A] {m : ℕ} (hm : σ ^ m = 1) :
    t.scChevalleyDatumDiagramAut ht hσ A ^ m = 1 :=
  ((map_pow (MulAut.congr (t.scPointsEquiv ht A).symm) _ m).symm.trans
    (congrArg (MulAut.congr (t.scPointsEquiv ht A).symm)
      (t.scToralDiagramAutPoints_pow_eq_one ht hσ A hm))).trans (map_one _)

/-- On every root subgroup of `scChevalleyDatum`, the diagram automorphism permutes the root
index by `diagramRootPerm` and multiplies the additive parameter by `chevalleyDiagramSign`. -/
@[simp]
theorem scChevalleyDatumDiagramAut_rootSubgroupPoints (hσ : σ ∈ t.diagramSymmetry)
    (α : Fin t.numRoots) (A : Type v) [CommRing A] (u : A) :
    t.scChevalleyDatumDiagramAut ht hσ A
        ((t.scChevalleyDatum ht).rootSubgroupPoints α A (ofAdd u)) =
      (t.scChevalleyDatum ht).rootSubgroupPoints (t.diagramRootPerm ht hσ α) A
        (ofAdd (((t.chevalleyDiagramSign ht hσ α : ℤ) : A) * u)) := by
  have hroot (γ : Fin t.numRoots) (v : A) :
      t.scPointsEquiv ht A ((t.scChevalleyDatum ht).rootSubgroupPoints γ A (ofAdd v)) =
        chevalleyToralRootSubgroupPoints (t := t) (ht := ht)
          (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
          (t.kostantForm_apply_mem_scLattice ht)
          (t.isNilpotent_representation_scModule_rootGenerator ht)
          (t.scWeightBasis ht) (t.scWeight ht) γ A (ofAdd v) :=
    Subtype.ext <| (MulEquiv.subgroupCongr_apply _ _).trans <|
      ((t.scChevalleyDatum ht).coe_rootSubgroupPoints γ A (ofAdd v)).trans
        (coe_chevalleyToralRootSubgroupPoints (t := t) (ht := ht) _ _ _ _ _ _ γ A (ofAdd v)).symm
  exact (t.scPointsEquiv ht A).injective <|
    (t.scPointsEquiv_scChevalleyDatumDiagramAut ht hσ A _).trans <|
      (congrArg _ (hroot α u)).trans <|
        (t.scToralDiagramAutPoints_chevalleyToralRootSubgroupPoints ht hσ α A u).trans
          (hroot _ _).symm

private theorem scPointsEquiv_torusPoints (A : Type v) [CommRing A] (r : Fin t.rank → Aˣ) :
    t.scPointsEquiv ht A ((t.scChevalleyDatum ht).torusPoints A r) =
      kostantToralWeightTorusPoints (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) A r := by
  apply Subtype.ext
  have h1 := (t.scChevalleyDatum ht).coe_torusPoints A r
  rw [t.scChevalleyDatum_coordinateWeight ht] at h1
  exact (MulEquiv.subgroupCongr_apply _ _).trans <|
    h1.trans (coe_kostantToralWeightTorusPoints _ _ _ _ _ _ _ _ A r).symm

/-- On the torus of `scChevalleyDatum`, the diagram automorphism relabels parameters by `σ⁻¹`. -/
@[simp]
theorem scChevalleyDatumDiagramAut_torusPoints (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) :
    t.scChevalleyDatumDiagramAut ht hσ A ((t.scChevalleyDatum ht).torusPoints A s) =
      (t.scChevalleyDatum ht).torusPoints A (fun k => s (σ⁻¹ k)) :=
  (t.scPointsEquiv ht A).injective <|
    (t.scPointsEquiv_scChevalleyDatumDiagramAut ht hσ A _).trans <|
      (congrArg _ (t.scPointsEquiv_torusPoints ht A s)).trans <|
        (t.scToralDiagramAutPoints_kostantToralWeightTorusPoints ht hσ A s).trans
          (t.scPointsEquiv_torusPoints ht A _).symm

/-- The diagram automorphism on `scChevalleyDatum` has character map equal to the weight map of
the inverse root-datum diagram automorphism, over every commutative ring. -/
theorem isCharacterMap_scChevalleyDatumDiagramAut (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] :
    IsCharacterMap ((t.scChevalleyDatum ht).torusPoints A)
      (t.scChevalleyDatumDiagramAut ht hσ A).toMonoidHom
      (diagramAut ht hσ)⁻¹.toHom.weightMap :=
  isCharacterMap_iff.mpr fun s => (t.scPointsEquiv ht A).injective <|
    (t.scPointsEquiv_scChevalleyDatumDiagramAut ht hσ A _).trans <|
      (congrArg _ (t.scPointsEquiv_torusPoints ht A s)).trans <|
        ((t.isCharacterMap_scToralDiagramAutPoints ht hσ A).map_apply s).trans
          (t.scPointsEquiv_torusPoints ht A _).symm

private theorem diagramRootPerm_mem_posRoots_iff (hσ : σ ∈ t.diagramSymmetry)
    (α : Fin t.numRoots) :
    t.diagramRootPerm ht hσ α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) ↔
      α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
  have hbase : (t.rationalBase ht).map (t.rationalDiagramAut ht hσ) = t.rationalBase ht := by
    classical
    refine RootPairing.Base.ext ?_
    rw [(t.rationalBase ht).support_map_eq]
    ext j
    simp only [Finset.mem_image, rationalDiagramAut_indexEquiv]
    refine ⟨?_, fun hj => ?_⟩
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hk
      exact t.diagramRootPerm_simpleIndex ht hσ i ▸ simpleIndex_mem_support (σ i)
    · obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hj
      exact ⟨t.simpleIndex ht (σ⁻¹ i), simpleIndex_mem_support _, by
        rw [t.diagramRootPerm_simpleIndex ht hσ, Equiv.Perm.inv_def, Equiv.apply_symm_apply]⟩
  have himg := posRoots_map (t.rationalRootSystem ht) (t.rationalBase ht)
    (t.rationalDiagramAut ht hσ)
  rw [hbase, rationalDiagramAut_indexEquiv] at himg
  refine ⟨fun h => ?_, fun h => himg.symm ▸ ⟨α, h, rfl⟩⟩
  obtain ⟨γ, hγ, hγeq⟩ := himg ▸ h
  rwa [← (t.diagramRootPerm ht hσ).injective hγeq]

/-- Every diagram automorphism of `scChevalleyDatum` is a based endomorphism over every
commutative ring. -/
theorem isBasedEndomorphism_scChevalleyDatumDiagramAut (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] :
    (t.scChevalleyDatum ht).IsBasedEndomorphism A
      (t.scChevalleyDatumDiagramAut ht hσ A).toMonoidHom := by
  have hmap (α : Fin t.numRoots) :
      ((t.scChevalleyDatum ht).rootSubgroupPoints α A).range.map
          (t.scChevalleyDatumDiagramAut ht hσ A).toMonoidHom =
        ((t.scChevalleyDatum ht).rootSubgroupPoints (t.diagramRootPerm ht hσ α) A).range := by
    let ε : Aˣ := Units.map (Int.castRingHom A).toMonoidHom (t.chevalleyDiagramSign ht hσ α)
    exact ChevalleyDatum.map_range_rootSubgroupPoints_eq_of_surjective
      (g := fun u : A => (ε : A) * u)
      (fun v => ⟨((ε⁻¹ : Aˣ) : A) * v, by simp [← mul_assoc]⟩) (fun u => by simp [ε])
  exact ⟨fun α => ⟨t.diagramRootPerm ht hσ α, hmap α⟩,
    fun α hα => ⟨t.diagramRootPerm ht hσ α,
      (t.diagramRootPerm_mem_posRoots_iff ht hσ α).mpr hα, hmap α⟩⟩

/-- Conjugating an endomorphism `F` of `(t.scChevalleyDatum ht).points A` by the diagram
automorphism `γ_σ` conjugates its character map by `(diagramAut ht hσ).toHom.weightMap`. -/
theorem isCharacterMap_conj_scChevalleyDatumDiagramAut (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A]
    {F : (t.scChevalleyDatum ht).points A →* (t.scChevalleyDatum ht).points A}
    {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hφ : IsCharacterMap ((t.scChevalleyDatum ht).torusPoints A) F φ) :
    IsCharacterMap ((t.scChevalleyDatum ht).torusPoints A)
      (((t.scChevalleyDatumDiagramAut ht hσ A).toMonoidHom.comp F).comp
        (t.scChevalleyDatumDiagramAut ht hσ A)⁻¹.toMonoidHom)
      ((diagramAut ht hσ).toHom.weightMap * φ * (diagramAut ht hσ)⁻¹.toHom.weightMap) := by
  have hinv := t.isCharacterMap_scChevalleyDatumDiagramAut ht (t.diagramSymmetry.inv_mem hσ) A
  rw [scChevalleyDatumDiagramAut_inv ht hσ A, diagramAut_inv ht hσ, inv_inv] at hinv
  simpa only [mul_assoc] using
    ((t.isCharacterMap_scChevalleyDatumDiagramAut ht hσ A).comp hφ).comp hinv

end TauCeti.DynkinType
