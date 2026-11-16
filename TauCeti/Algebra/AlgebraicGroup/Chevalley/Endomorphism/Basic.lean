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
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Injective
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Quotient
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.CharacterMap
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.Root.Subgroup
import Mathlib.RingTheory.RootsOfUnity.Basic

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

Over an infinite field with divisible units (in particular an algebraically closed field), a
standard endomorphism `F` with an injective character map `φ` acts on each root subgroup by
`F (x_α(u)) = x_{π α}(c_α · g_α(u))` for a permutation `π` of the roots, units `c_α`, and
field automorphisms `g_α : K ≃+* K` satisfying `g_α(α(s)) = (φ (π α))(s)` and rational
proportionality between `φ (π α)` and `α`. Both the target root `π α` and the field
endomorphism `g_α` are uniquely determined by `(α, φ)` alone over any infinite field, even
without divisible units (`ChevalleyDatum.eq_of_ringHom_torusCharacter_eq`); in particular `π`
commutes with root negation and `g_{-α} = g_α`.

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
* `TauCeti.DynkinType.ChevalleyDatum.eq_of_ringHom_torusCharacter_eq`: an injective character
  map uniquely determines both the target root (including sign) and the field endomorphism.
* `TauCeti.DynkinType.ChevalleyDatum.exists_rootPerm_of_isStandardEndomorphism`: every standard
  endomorphism with an injective character map induces a negation-preserving permutation of the
  roots and compatible field automorphisms on every root subgroup.

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
  rw [hmap]
  exact le_iSup₂ (f := fun γ _ => (D.rootSubgroupPoints γ A).range) β hβ

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
    D.IsStandardEndomorphism A (F.comp G) := by
  intro α
  obtain ⟨β, hβ⟩ := hG α
  obtain ⟨γ, hγ⟩ := hF β
  refine ⟨γ, ?_⟩
  rw [← Subgroup.map_map, hβ, hγ]

/-- Based endomorphisms are closed under composition. -/
theorem IsBasedEndomorphism.comp {F G : D.points A →* D.points A}
    (hF : D.IsBasedEndomorphism A F) (hG : D.IsBasedEndomorphism A G) :
    D.IsBasedEndomorphism A (F.comp G) := by
  refine ⟨hF.isStandard.comp hG.isStandard, fun α hα => ?_⟩
  obtain ⟨β, hβ, hmapG⟩ := hG.2 α hα
  obtain ⟨γ, hγ, hmapF⟩ := hF.2 β hβ
  refine ⟨γ, hγ, ?_⟩
  rw [← Subgroup.map_map, hmapG, hmapF]

/-- An endomorphism sending each root element `x_α(u)` to `x_{β α}(g_α(u))` with each `g_α`
surjective maps the root subgroup of `α` onto that of `β α`. -/
theorem map_range_rootSubgroupPoints_eq_of_surjective {F : D.points A →* D.points A}
    {α β : Fin t.numRoots} {g : A → A} (hg : Function.Surjective g)
    (hF : ∀ u : A, F (D.rootSubgroupPoints α A (ofAdd u)) =
      D.rootSubgroupPoints β A (ofAdd (g u))) :
    (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints β A).range := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    refine ⟨ofAdd (g (toAdd u)), ?_⟩
    rw [← hF (toAdd u), ofAdd_toAdd]
  · rintro _ ⟨v, rfl⟩
    obtain ⟨u, hu⟩ := hg (toAdd v)
    refine ⟨D.rootSubgroupPoints α A (ofAdd u), ⟨ofAdd u, rfl⟩, ?_⟩
    rw [hF u, hu, ofAdd_toAdd]

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
  · intro hB
    refine ⟨hstd, fun α hα => ?_⟩
    obtain ⟨β, hβ⟩ := hstd α
    refine ⟨β, ?_, hβ⟩
    by_contra hnotpos
    have hβneg : β ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht) :=
      (not_mem_posRoots_iff_mem_negRoots _ _ β).mp hnotpos
    have hmem : D.rootSubgroupPoints β A (ofAdd 1) ∈ D.borelSubgroup A := by
      have h1 : D.rootSubgroupPoints β A (ofAdd 1) ∈ (D.rootSubgroupPoints α A).range.map F :=
        hβ.symm ▸ ⟨ofAdd 1, rfl⟩
      obtain ⟨x, ⟨u, rfl⟩, hFx⟩ := h1
      rw [← hFx]
      exact hB ⟨_, D.positivePoints_le_borelSubgroup A
        (D.rootSubgroupPoints_mem_positivePoints A hα u), rfl⟩
    have htriv := (D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots A hβneg _).mp hmem
    exact D.rootSubgroupPoints_ofAdd_one_ne_one A β htriv

/-- For a standard endomorphism with a character map over a nontrivial ring, being based is
equivalent to mapping `D.borelSubgroup A` into itself. -/
theorem isBasedEndomorphism_iff_map_borelSubgroup_le_of_isCharacterMap [Nontrivial A]
    {F : D.points A →* D.points A} {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hstd : D.IsStandardEndomorphism A F) (hφ : IsCharacterMap (D.torusPoints A) F φ) :
    D.IsBasedEndomorphism A F ↔ (D.borelSubgroup A).map F ≤ D.borelSubgroup A := by
  refine isBasedEndomorphism_iff_map_borelSubgroup_le hstd ?_
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  rw [hφ.map_apply s]
  exact D.range_torusPoints_le_borelSubgroup A ⟨torusPointMap φ s, rfl⟩

end Defs

/-! ## Concrete standard and based endomorphisms -/

section Examples

variable (A : Type v) [CommRing A]

/-- Conjugation by a pinned simple Weyl representative is a standard endomorphism over every
commutative ring. -/
theorem isStandardEndomorphism_conj_weylElement (i : Fin t.rank) :
    D.IsStandardEndomorphism A
      (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom := by
  intro α
  refine ⟨(t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) α, ?_⟩
  let ε : Aˣ := Units.map (Int.castRingHom A).toMonoidHom
    (t.chevalleyWeylSign ht (t.simpleIndex ht i) α)
  refine map_range_rootSubgroupPoints_eq_of_surjective (g := fun u : A => (ε : A) * u)
    (fun v => ⟨((ε⁻¹ : Aˣ) : A) * v, by simp [← mul_assoc]⟩) (fun u => ?_)
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
  D.isBasedEndomorphism_frobenius_of_surjective A p k (fun a => by
    obtain ⟨b, hb⟩ := (PerfectRing.bijective_frobenius (R := A) (p := p ^ k)).surjective a
    exact ⟨b, by simpa only [iterateFrobenius_def] using hb⟩)

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
      (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom := by
  intro hbased
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
        (D.frobenius p k A)) := by
  intro hbased
  have hchar : IsCharacterMap (D.torusPoints A)
      ((MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom.comp
        (D.frobenius p k A))
      (((p ^ k : ℕ) • 1) *
        (D.weylCharacterAut
          (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht)
            (t.simpleIndex ht i))).toLinearMap) :=
    (D.isCharacterMap_conj_weylElement i A).comp (D.isCharacterMap_frobenius p k A)
  have hB := (isBasedEndomorphism_iff_map_borelSubgroup_le_of_isCharacterMap
    (D.isStandardEndomorphism_conj_weylElement_comp_frobenius A i p k hsurj) hchar).mp hbased
  have hpos : t.simpleIndex ht i ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) :=
    support_subset_posRoots _ _ (t.simpleIndex_mem_support i)
  have hmem :
      ((MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom.comp
          (D.frobenius p k A))
        (D.rootSubgroupPoints (t.simpleIndex ht i) A (ofAdd 1)) ∈ D.borelSubgroup A :=
    hB ⟨_, D.positivePoints_le_borelSubgroup A
      (D.rootSubgroupPoints_mem_positivePoints A hpos _), rfl⟩
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
  have h := (D.isCharacterMap_conj_weylElement i A).comp (D.isCharacterMap_frobenius p k A)
  simpa only [smul_mul_assoc, one_mul] using h

/-! ### Regression example in type `A₁` -/

section TypeA1

private theorem eq_of_fin_rank_typeA1 (i j : Fin (DynkinType.A 1).rank) : i = j := by
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  simp [DynkinType.rank] at hi hj
  omega

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
  have hj : j = i := eq_of_fin_rank_typeA1 j i
  subst hj
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
  rw [weylCharacterAut_simpleIndex_typeA1 D i] at h
  have hsmul : (p ^ k : ℕ) • (-1 : Module.End ℤ (Fin (DynkinType.A 1).rank → ℤ)) =
      (-(p ^ k : ℤ)) • (1 : Module.End ℤ (Fin (DynkinType.A 1).rank → ℤ)) := by
    rw [smul_neg, ← natCast_zsmul, Nat.cast_pow, neg_smul]
  rwa [hsmul] at h

private theorem frobenius_weylElement_one (γ : Fin t.numRoots) (p k : ℕ) [ExpChar A p] :
    D.frobenius p k A (D.weylElement γ A 1) = D.weylElement γ A 1 := by
  have hneg : (-1 : A) ^ (p ^ k) = -1 := by
    rw [← iterateFrobenius_def, map_neg, map_one]
  simp only [weylElement_def, inv_one, Units.val_one, map_mul, D.frobenius_rootSubgroupPoints,
    one_pow, hneg]

private theorem weylElement_one_mul_self (i : Fin t.rank) :
    D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht i) A 1 =
      D.torusPoints A (D.simpleCorootParameter i A (-1)) := by
  have hcoroot : D.weylElement (t.simpleIndex ht i) A (-1) =
      D.torusPoints A (D.simpleCorootParameter i A (-1)) *
        D.weylElement (t.simpleIndex ht i) A 1 := by
    apply Subtype.ext
    have h := D.coe_simpleCorootPoints_eq_root_word i A (-1)
    simpa only [coe_torusPoints, coe_simpleCorootPoints_eq_kostantTorusMatrix, weylElement_def,
      Subgroup.coe_mul, coe_rootSubgroupPoints_simpleIndex,
      coe_rootSubgroupPoints_reflectionPerm_simpleIndex, Subgroup.coe_inv, inv_neg, inv_one,
      Units.val_neg, Units.val_one, neg_neg] using (eq_mul_inv_iff_mul_eq.mp h).symm
  have hinv : (D.weylElement (t.simpleIndex ht i) A 1)⁻¹ =
      D.weylElement (t.simpleIndex ht i) A (-1) := by
    simp only [weylElement_def, mul_inv_rev, ← map_inv, ofAdd_neg, inv_inv, inv_neg, inv_one,
      Units.val_neg, Units.val_one, neg_neg, mul_assoc]
  have hsq := congrArg (fun x => (D.torusPoints A (D.simpleCorootParameter i A (-1)))⁻¹ * x)
    (hinv.trans hcoroot)
  simp only [inv_mul_cancel_left] at hsq
  have h2 : D.torusPoints A (D.simpleCorootParameter i A (-1)) =
      (D.torusPoints A (D.simpleCorootParameter i A (-1)))⁻¹ := by
    rw [← map_inv, ← map_inv, inv_neg, inv_one]
  rw [← h2] at hsq
  calc
    D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht i) A 1
        = D.torusPoints A (D.simpleCorootParameter i A (-1)) *
            (D.weylElement (t.simpleIndex ht i) A 1)⁻¹ *
            D.weylElement (t.simpleIndex ht i) A 1 := by rw [hsq]
    _ = D.torusPoints A (D.simpleCorootParameter i A (-1)) := inv_mul_cancel_right _ _

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
  have hcomm_n : D.frobenius p k A n = n :=
    D.frobenius_weylElement_one A ((DynkinType.A 1).simpleIndex h1 i) p k
  have hF2 (y : D.points A) : F (F y) = n * n * D.frobenius p (2 * k) A y * (n * n)⁻¹ := by
    have hadd : D.frobenius p (2 * k) A y = D.frobenius p k A (D.frobenius p k A y) := by
      have h := D.frobenius_add p k A k
      rw [← two_mul] at h
      exact DFunLike.congr_fun h y
    have hstep1 : F y = n * D.frobenius p k A y * n⁻¹ := rfl
    have hstep2 : F (F y) = n * D.frobenius p k A (n * D.frobenius p k A y * n⁻¹) * n⁻¹ := by
      rw [hstep1]; rfl
    rw [hstep2, map_mul, map_mul, map_inv, hcomm_n, ← hadd]
    group
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
  -- `n * n = hᵢ(-1)` acts trivially by conjugation on every element of `D.rootTorusSubgroup A`.
  have hcentral :
      ((MulAut.conj (n * n)).toMonoidHom.comp (D.rootTorusSubgroup A).subtype) =
        (D.rootTorusSubgroup A).subtype := by
    refine D.rootTorusSubgroup_hom_ext _ _ (fun j u => ?_) (fun j u => ?_) (fun s => ?_)
    · have hj : j = i := eq_of_fin_rank_typeA1 j i
      subst hj
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, n, D.weylElement_one_mul_self A j]
      rw [← ofAdd_toAdd u, D.torusPoints_conj_rootSubgroupPoints, hch, Units.val_one, one_mul]
    · have hj : j = i := eq_of_fin_rank_typeA1 j i
      subst hj
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, n, D.weylElement_one_mul_self A j]
      rw [← ofAdd_toAdd u, D.torusPoints_conj_rootSubgroupPoints,
        D.coordinateRoot_reflectionPerm_self, torusCharacter_neg, hch, inv_one, Units.val_one,
        one_mul]
    · simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, n, D.weylElement_one_mul_self A i]
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
  have h := (D.isCharacterMap_conj_weylSubgroup_comp K g hφ).comp hinv
  simpa only [mul_assoc] using h

end WeylConj

/-! ## Root parameters and field automorphisms from a character map -/

section Extraction

private theorem finite_rootsOfUnity_set {K : Type*} [Field K] {N : ℕ} (hN : N ≠ 0) :
    {ζ : K | ζ ^ N = 1}.Finite := by
  have : NeZero N := ⟨hN⟩
  let f : {ζ : K | ζ ^ N = 1} → rootsOfUnity N K := fun ζ =>
    ⟨Units.mk0 ζ.1 fun h0 => by
        have h : (ζ : K) ^ N = 1 := ζ.2
        rw [h0, zero_pow hN] at h
        exact zero_ne_one h,
      by
        rw [mem_rootsOfUnity]
        exact Units.ext (by
          have h : (ζ : K) ^ N = 1 := ζ.2
          simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] using h)⟩
  have hf : Function.Injective f := fun a b hab => Subtype.ext <| by
    have h := congrArg (fun u : rootsOfUnity N K => (u.1 : K)) hab
    simpa [f] using h
  exact Set.finite_coe_iff.mp (Finite.of_injective f hf)

private theorem false_of_pow_mul_eq_one {K : Type*} [Field K] [Infinite K]
    (g₁ g₂ : K →+* K) {N : ℕ} (hN : N ≠ 0)
    (h : ∀ x : K, x ≠ 0 → (g₁ x * g₂ x) ^ N = 1) : False := by
  let R : Set K := {ζ : K | ζ ^ N = 1}
  have hR : R.Finite := finite_rootsOfUnity_set hN
  let Q : K × K → Set K := fun p => {y : K | y ^ 2 - (p.2 - 1 - p.1) * y + p.1 = 0}
  have hQ (p : K × K) : (Q p).Finite := by
    by_cases hne : (Q p).Nonempty
    · obtain ⟨y₀, hy₀⟩ := hne
      refine (Set.toFinite ({y₀, (p.2 - 1 - p.1) - y₀} : Set K)).subset fun y hy => ?_
      have hfac : (y - y₀) * (y + y₀ - (p.2 - 1 - p.1)) = 0 := by
        have h1 : y ^ 2 - (p.2 - 1 - p.1) * y + p.1 = 0 := hy
        have h2 : y₀ ^ 2 - (p.2 - 1 - p.1) * y₀ + p.1 = 0 := hy₀
        linear_combination h1 - h2
      rcases mul_eq_zero.mp hfac with hsub | hadd
      · exact Or.inl (sub_eq_zero.mp hsub)
      · exact Or.inr (eq_of_sub_eq_zero (by linear_combination hadd))
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact Set.finite_empty
  have hU : (⋃ p ∈ R ×ˢ R, Q p).Finite := (hR.prod hR).biUnion fun p _ => hQ p
  let T : Set K := Set.univ \ ({0, -1} : Set K)
  have hT : T.Infinite := Set.infinite_univ.sdiff (Set.toFinite _)
  have hsub : g₁ '' T ⊆ ⋃ p ∈ R ×ˢ R, Q p := by
    rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
    have hx0 : x ≠ 0 := fun h0 => hx (Or.inl h0)
    have hx1 : 1 + x ≠ 0 := fun h1 =>
      hx (Or.inr (eq_of_sub_eq_zero (by linear_combination h1)))
    have hp : (g₁ x * g₂ x, g₁ (1 + x) * g₂ (1 + x)) ∈ R ×ˢ R :=
      ⟨h x hx0, h (1 + x) hx1⟩
    refine Set.mem_biUnion hp ?_
    change (g₁ x) ^ 2 - (g₁ (1 + x) * g₂ (1 + x) - 1 - g₁ x * g₂ x) * g₁ x + g₁ x * g₂ x = 0
    rw [map_add, map_one, map_add, map_one]
    ring
  exact (hT.image g₁.injective.injOn) (hU.subset hsub)

private theorem eq_of_pow_eq_pow {K : Type*} [Field K] [Infinite K]
    (g₁ g₂ : K →+* K) {N : ℕ} (hN : N ≠ 0)
    (h : ∀ x : K, x ≠ 0 → (g₁ x) ^ N = (g₂ x) ^ N) : g₁ = g₂ := by
  let R : Set K := {ζ : K | ζ ^ N = 1}
  have hR : R.Finite := finite_rootsOfUnity_set hN
  let E : K × K → Set K := fun p => {y : K | p.1 ≠ p.2 ∧ (p.1 - p.2) * y = p.2 - 1}
  have hE (p : K × K) : (E p).Finite := by
    refine Set.Subsingleton.finite fun y₁ hy₁ y₂ hy₂ => ?_
    have hdiff : (p.1 - p.2) * (y₁ - y₂) = 0 := by
      have h1 : (p.1 - p.2) * y₁ = p.2 - 1 := hy₁.2
      have h2 : (p.1 - p.2) * y₂ = p.2 - 1 := hy₂.2
      linear_combination h1 - h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hy₁.1))
  let B : Set K := ⋃ p ∈ R ×ˢ R, E p
  have hB : B.Finite := (hR.prod hR).biUnion fun p _ => hE p
  let bad : Set K := {x : K | g₁ x ≠ g₂ x}
  have hbad_sub : bad ⊆ ({0, -1} : Set K) ∪ g₂ ⁻¹' B := by
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inl (Or.inl hx0)
    by_cases hx1 : x = -1
    · exact Or.inl (Or.inr hx1)
    right
    have hx1' : 1 + x ≠ 0 := fun h1 => hx1 (eq_of_sub_eq_zero (by linear_combination h1))
    have hg2x : g₂ x ≠ 0 := fun h0 => hx0 (g₂.injective (h0.trans (map_zero g₂).symm))
    have hg21x : g₂ (1 + x) ≠ 0 := fun h0 => hx1' (g₂.injective (h0.trans (map_zero g₂).symm))
    let ζ₁ : K := g₁ x * (g₂ x)⁻¹
    let ζ₂ : K := g₁ (1 + x) * (g₂ (1 + x))⁻¹
    have hζ₁ : ζ₁ ∈ R := by
      change (g₁ x * (g₂ x)⁻¹) ^ N = 1
      rw [mul_pow, inv_pow, h x hx0, mul_inv_cancel₀ (pow_ne_zero N hg2x)]
    have hζ₂ : ζ₂ ∈ R := by
      change (g₁ (1 + x) * (g₂ (1 + x))⁻¹) ^ N = 1
      rw [mul_pow, inv_pow, h (1 + x) hx1', mul_inv_cancel₀ (pow_ne_zero N hg21x)]
    have h1 : g₁ x = ζ₁ * g₂ x := (inv_mul_cancel_right₀ hg2x (g₁ x)).symm
    have h2 : 1 + g₁ x = ζ₂ * (1 + g₂ x) := by
      have h2' : g₁ (1 + x) = ζ₂ * g₂ (1 + x) := (inv_mul_cancel_right₀ hg21x (g₁ (1 + x))).symm
      simpa only [map_add, map_one] using h2'
    have heq : (ζ₁ - ζ₂) * g₂ x = ζ₂ - 1 := by linear_combination h2 - h1
    have hne : ζ₁ ≠ ζ₂ := by
      intro h12
      rw [h12, sub_self, zero_mul] at heq
      have hζ2_one : ζ₂ = 1 := eq_of_sub_eq_zero heq.symm
      have hζ1_one : ζ₁ = 1 := h12.trans hζ2_one
      rw [hζ1_one, one_mul] at h1
      exact hx h1
    have hp : (ζ₁, ζ₂) ∈ R ×ˢ R := ⟨hζ₁, hζ₂⟩
    exact Set.mem_biUnion hp ⟨hne, heq⟩
  have hbad : bad.Finite :=
    ((Set.toFinite _).union (hB.preimage g₂.injective.injOn)).subset hbad_sub
  refine RingHom.ext fun x => ?_
  have hfin : (bad ∪ (fun z => z - x) '' bad).Finite := hbad.union (hbad.image _)
  obtain ⟨y, hy⟩ := (Set.infinite_univ.sdiff hfin).nonempty
  have hy_not_bad : y ∉ bad := fun hmem => hy.2 (Or.inl hmem)
  have hxy_not_bad : x + y ∉ bad := fun hmem =>
    hy.2 (Or.inr ⟨x + y, hmem, by ring⟩)
  have hgy : g₁ y = g₂ y := not_not.mp hy_not_bad
  have hgxy : g₁ (x + y) = g₂ (x + y) := not_not.mp hxy_not_bad
  rw [map_add, map_add, hgy] at hgxy
  exact add_right_cancel hgxy

/-- **Uniqueness of the target root and field endomorphism from the character map.** Over any
infinite field, an injective character map `φ` and source root `α` uniquely determine both the
target root `β` (including its sign) and the field endomorphism `g : K →+* K` satisfying
`g (α(s)) = (φ β)(s)` for all torus parameters `s`. Divisibility of `Kˣ` is not required. -/
theorem eq_of_ringHom_torusCharacter_eq {K : Type*} [Field K] [Infinite K]
    {φ : Module.End ℤ (Fin t.rank → ℤ)} (hinj : Function.Injective φ)
    {α β₁ β₂ : Fin t.numRoots} {g₁ g₂ : K →+* K}
    (h₁ : ∀ s : Fin t.rank → Kˣ,
      g₁ (torusCharacter s (D.coordinateRoot α)) =
        torusCharacter s (φ (D.coordinateRoot β₁)))
    (h₂ : ∀ s : Fin t.rank → Kˣ,
      g₂ (torusCharacter s (D.coordinateRoot α)) =
        torusCharacter s (φ (D.coordinateRoot β₂))) :
    β₁ = β₂ ∧ g₁ = g₂ := by
  obtain ⟨i, hi⟩ : ∃ i, D.coordinateRoot α i ≠ 0 := Function.ne_iff.mp (D.coordinateRoot_ne_zero α)
  have hker₁ : ∀ s : Fin t.rank → Kˣ,
      torusCharacter s (D.coordinateRoot α) = 1 →
        torusCharacter s (φ (D.coordinateRoot β₁)) = 1 := by
    intro s hs
    apply Units.ext
    simpa only [hs, Units.val_one, map_one] using (h₁ s).symm
  have hker₂ : ∀ s : Fin t.rank → Kˣ,
      torusCharacter s (D.coordinateRoot α) = 1 →
        torusCharacter s (φ (D.coordinateRoot β₂)) = 1 := by
    intro s hs
    apply Units.ext
    simpa only [hs, Units.val_one, map_one] using (h₂ s).symm
  have hp₁ := smul_eq_smul_of_torusCharacter_eq_one hker₁ i
  have hp₂ := smul_eq_smul_of_torusCharacter_eq_one hker₂ i
  have hm₁ : φ (D.coordinateRoot β₁) i ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hp₁
    have hφ0 : φ (D.coordinateRoot β₁) = 0 := (smul_eq_zero.mp hp₁).resolve_left hi
    exact D.coordinateRoot_ne_zero β₁ (hinj (hφ0.trans (map_zero φ).symm))
  have hm₂ : φ (D.coordinateRoot β₂) i ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hp₂
    have hφ0 : φ (D.coordinateRoot β₂) = 0 := (smul_eq_zero.mp hp₂).resolve_left hi
    exact D.coordinateRoot_ne_zero β₂ (hinj (hφ0.trans (map_zero φ).symm))
  have hpropβ :
      φ (D.coordinateRoot β₂) i • D.coordinateRoot β₁ =
        φ (D.coordinateRoot β₁) i • D.coordinateRoot β₂ := by
    apply hinj
    rw [map_zsmul, map_zsmul]
    have hcomb :
        D.coordinateRoot α i • (φ (D.coordinateRoot β₂) i • φ (D.coordinateRoot β₁)) =
          D.coordinateRoot α i • (φ (D.coordinateRoot β₁) i • φ (D.coordinateRoot β₂)) := by
      calc
        _ = φ (D.coordinateRoot β₂) i • (D.coordinateRoot α i • φ (D.coordinateRoot β₁)) :=
          smul_comm _ _ _
        _ = φ (D.coordinateRoot β₂) i • (φ (D.coordinateRoot β₁) i • D.coordinateRoot α) := by
          rw [hp₁]
        _ = φ (D.coordinateRoot β₁) i • (φ (D.coordinateRoot β₂) i • D.coordinateRoot α) :=
          smul_comm _ _ _
        _ = φ (D.coordinateRoot β₁) i • (D.coordinateRoot α i • φ (D.coordinateRoot β₂)) := by
          rw [← hp₂]
        _ = _ := smul_comm _ _ _
    exact smul_right_injective _ hi hcomb
  have hrootprop :
      φ (D.coordinateRoot β₂) i • (t.simplyConnectedRootDatum ht).root β₁ =
        φ (D.coordinateRoot β₁) i • (t.simplyConnectedRootDatum ht).root β₂ := by
    have h := congrArg D.weightLatticeEmbedding hpropβ
    rw [map_zsmul, map_zsmul] at h
    simpa only [coordinateRoot_def, D.weightLatticeEmbedding_repr, Submodule.coe_mk] using h
  have hnotlin : ¬ LinearIndependent ℤ
      ![(t.simplyConnectedRootDatum ht).root β₁, (t.simplyConnectedRootDatum ht).root β₂] := by
    intro hlin
    have hzero : (-φ (D.coordinateRoot β₂) i) • (t.simplyConnectedRootDatum ht).root β₁ +
        φ (D.coordinateRoot β₁) i • (t.simplyConnectedRootDatum ht).root β₂ = 0 := by
      rw [neg_smul, hrootprop, neg_add_cancel]
    exact hm₁ (hlin.eq_zero_of_pair hzero).2
  have hN : (D.coordinateRoot α i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hi
  let _ := t.isReduced_simplyConnectedRootDatum ht
  have hβ : β₁ = β₂ := by
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := t.simplyConnectedRootDatum ht) β₁ β₂ hnotlin
      with heq | hneg
    · exact (t.simplyConnectedRootDatum ht).root.injective heq
    · have hcoord_neg : D.coordinateRoot β₂ = -D.coordinateRoot β₁ := by
        apply D.weightLatticeEmbedding_injective
        rw [map_neg]
        simpa only [coordinateRoot_def, D.weightLatticeEmbedding_repr, Submodule.coe_mk] using
          neg_eq_iff_eq_neg.mp hneg.symm
      exfalso
      apply false_of_pow_mul_eq_one g₁ g₂ hN
      intro x hx
      let u : Kˣ := Units.mk0 x hx
      have hprod : g₁ (u ^ D.coordinateRoot α i : K) * g₂ (u ^ D.coordinateRoot α i : K) = 1 := by
        have hs₁ := h₁ (Pi.mulSingle i u)
        have hs₂ := h₂ (Pi.mulSingle i u)
        simp only [torusCharacter_mulSingle, Units.val_zpow_eq_zpow_val] at hs₁ hs₂
        rw [hs₁, hs₂, hcoord_neg, map_neg, Pi.neg_apply, zpow_neg,
          mul_inv_cancel₀ (zpow_ne_zero _ (Units.ne_zero u))]
      have hpow : (g₁ x * g₂ x) ^ D.coordinateRoot α i = 1 := by
        have h1 : g₁ (x ^ D.coordinateRoot α i) = (g₁ x) ^ D.coordinateRoot α i :=
          map_zpow₀ g₁ x (D.coordinateRoot α i)
        have h2 : g₂ (x ^ D.coordinateRoot α i) = (g₂ x) ^ D.coordinateRoot α i :=
          map_zpow₀ g₂ x (D.coordinateRoot α i)
        rw [mul_zpow, ← h1, ← h2]
        simpa only [u, Units.val_zpow_eq_zpow_val, Units.val_mk0] using hprod
      rcases Int.natAbs_eq (D.coordinateRoot α i) with hpos | hneg'
      · rw [hpos, zpow_natCast] at hpow
        exact hpow
      · rw [hneg', zpow_neg, zpow_natCast] at hpow
        exact inv_eq_one.mp hpow
  subst hβ
  refine ⟨rfl, eq_of_pow_eq_pow g₁ g₂ hN fun x hx => ?_⟩
  let u : Kˣ := Units.mk0 x hx
  have heq_zpow : (g₁ x) ^ D.coordinateRoot α i = (g₂ x) ^ D.coordinateRoot α i := by
    have hs₁ := h₁ (Pi.mulSingle i u)
    have hs₂ := h₂ (Pi.mulSingle i u)
    simp only [torusCharacter_mulSingle, Units.val_zpow_eq_zpow_val, Units.val_mk0, u] at hs₁ hs₂
    have h1 : g₁ (x ^ D.coordinateRoot α i) = (g₁ x) ^ D.coordinateRoot α i :=
      map_zpow₀ g₁ x (D.coordinateRoot α i)
    have h2 : g₂ (x ^ D.coordinateRoot α i) = (g₂ x) ^ D.coordinateRoot α i :=
      map_zpow₀ g₂ x (D.coordinateRoot α i)
    exact h1.symm.trans (hs₁.trans (hs₂.symm.trans h2))
  rcases Int.natAbs_eq (D.coordinateRoot α i) with hpos | hneg'
  · rw [hpos, zpow_natCast, zpow_natCast] at heq_zpow
    exact heq_zpow
  · rw [hneg', zpow_neg, zpow_neg, zpow_natCast, zpow_natCast] at heq_zpow
    exact inv_injective heq_zpow

/-- **Root-subgroup structure of a standard endomorphism.** Over an infinite field with divisible
units, a standard endomorphism `F` with injective character map `φ` sends each root subgroup `x_α`
to `u ↦ x_β(c · g(u))` for a root `β`, a unit `c`, and a field automorphism `g : K ≃+* K`
intertwining `α` with `φ β`, which is rationally proportional to `α`. -/
theorem exists_root_and_ringEquiv_of_isStandardEndomorphism {K : Type v} [Field K] [Infinite K]
    [RootableBy Kˣ ℕ] {F : D.points K →* D.points K} {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hstd : D.IsStandardEndomorphism K F) (hφ : IsCharacterMap (D.torusPoints K) F φ)
    (hinj : Function.Injective φ) (α : Fin t.numRoots) :
    ∃ (β : Fin t.numRoots) (c : Kˣ) (g : K ≃+* K),
      (∀ u : K, F (D.rootSubgroupPoints α K (ofAdd u)) =
        D.rootSubgroupPoints β K (ofAdd ((c : K) * g u))) ∧
      (∀ s : Fin t.rank → Kˣ,
        g (torusCharacter s (D.coordinateRoot α)) =
          torusCharacter s (φ (D.coordinateRoot β))) ∧
      (∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧
        n • φ (D.coordinateRoot β) = m • D.coordinateRoot α) := by
  obtain ⟨β, hβ⟩ := hstd α
  -- Transport `F` across the injective root maps `x_α` and `x_β` to a bijection `f` of `K`.
  have hex (u : K) : ∃ v : K, F (D.rootSubgroupPoints α K (ofAdd u)) =
      D.rootSubgroupPoints β K (ofAdd v) := by
    have hmem : F (D.rootSubgroupPoints α K (ofAdd u)) ∈ (D.rootSubgroupPoints β K).range :=
      hβ ▸ ⟨D.rootSubgroupPoints α K (ofAdd u), ⟨ofAdd u, rfl⟩, rfl⟩
    obtain ⟨w, hw⟩ := hmem
    exact ⟨toAdd w, by simpa only [ofAdd_toAdd] using hw.symm⟩
  choose f hf using hex
  have hf_add (u v : K) : f (u + v) = f u + f v := by
    have h : ofAdd (f (u + v)) = ofAdd (f u + f v) := D.rootSubgroupPoints_injective β K (by
      rw [← hf (u + v), ofAdd_add, map_mul, map_mul, hf u, hf v, ← map_mul, ← ofAdd_add])
    exact ofAdd.injective h
  have hf_zero : f 0 = 0 := by
    have h : ofAdd (f 0) = ofAdd (0 : K) := D.rootSubgroupPoints_injective β K (by
      rw [← hf 0, ofAdd_zero, map_one, map_one, map_one])
    exact ofAdd.injective h
  have hf_scale (s : Fin t.rank → Kˣ) (u : K) :
      f ((torusCharacter s (D.coordinateRoot α) : K) * u) =
        (torusCharacter s (φ (D.coordinateRoot β)) : K) * f u := by
    have hconj := congrArg F (D.torusPoints_conj_rootSubgroupPoints α K s u)
    rw [map_mul, map_mul, map_inv, hφ.map_apply s, hf u,
      D.torusPoints_conj_rootSubgroupPoints, torusCharacter_torusPointMap, hf] at hconj
    exact ofAdd.injective (D.rootSubgroupPoints_injective β K hconj.symm)
  have hf_surj : Function.Surjective f := by
    intro v
    have hmem : D.rootSubgroupPoints β K (ofAdd v) ∈ (D.rootSubgroupPoints α K).range.map F :=
      hβ.symm ▸ ⟨ofAdd v, rfl⟩
    obtain ⟨_, ⟨u, rfl⟩, hu⟩ := hmem
    refine ⟨toAdd u, ?_⟩
    have h : ofAdd (f (toAdd u)) = ofAdd v := D.rootSubgroupPoints_injective β K (by
      rw [← hf (toAdd u), ofAdd_toAdd, hu])
    exact ofAdd.injective h
  have hf1_ne : f 1 ≠ 0 := by
    intro h0
    obtain ⟨u, hu⟩ := hf_surj 1
    have hf_all : ∀ a : K, f a = 0 := by
      intro a
      by_cases ha : a = 0
      · rw [ha, hf_zero]
      · obtain ⟨s, hs⟩ := torusCharacter_surjective (R := K) (D.coordinateRoot_ne_zero α)
          (Units.mk0 a ha)
        dsimp only at hs
        have h := hf_scale s 1
        rw [hs, Units.val_mk0, mul_one, h0, mul_zero] at h
        exact h
    exact one_ne_zero (hu.symm.trans (hf_all u))
  let c : Kˣ := Units.mk0 (f 1) hf1_ne
  have hg_fn (u : K) : (c : K) * (((c⁻¹ : Kˣ) : K) * f u) = f u := by
    simp
  have hg_one : ((c⁻¹ : Kˣ) : K) * f 1 = 1 := by
    simp [c, hf1_ne]
  have hg_scale (s : Fin t.rank → Kˣ) (u : K) :
      ((c⁻¹ : Kˣ) : K) * f ((torusCharacter s (D.coordinateRoot α) : K) * u) =
        (torusCharacter s (φ (D.coordinateRoot β)) : K) * (((c⁻¹ : Kˣ) : K) * f u) := by
    rw [hf_scale s u]
    ring
  have hg_char (s : Fin t.rank → Kˣ) :
      ((c⁻¹ : Kˣ) : K) * f (torusCharacter s (D.coordinateRoot α)) =
        torusCharacter s (φ (D.coordinateRoot β)) := by
    have h := hg_scale s 1
    rw [mul_one, hg_one, mul_one] at h
    exact h
  let gHom : K →+* K :=
    { toFun := fun u => ((c⁻¹ : Kˣ) : K) * f u
      map_one' := hg_one
      map_mul' := fun a b => by
        by_cases ha : a = 0
        · simp [ha, hf_zero]
        · obtain ⟨s, hs⟩ := torusCharacter_surjective (R := K) (D.coordinateRoot_ne_zero α)
            (Units.mk0 a ha)
          dsimp only at hs
          have h1 := hg_scale s b
          have h2 := hg_char s
          rw [hs, Units.val_mk0] at h1 h2
          rw [h1, h2]
      map_zero' := by simp [hf_zero]
      map_add' := fun a b => by rw [hf_add, mul_add] }
  have hg_bij : Function.Bijective gHom := by
    refine ⟨gHom.injective, fun v => ?_⟩
    obtain ⟨u, hu⟩ := hf_surj ((c : K) * v)
    refine ⟨u, ?_⟩
    change ((c⁻¹ : Kˣ) : K) * f u = v
    rw [hu, ← mul_assoc, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero c), one_mul]
  let g : K ≃+* K := RingEquiv.ofBijective gHom hg_bij
  refine ⟨β, c, g, fun u => ?_, fun s => hg_char s, ?_⟩
  · rw [hf u]
    congr 2
    exact (hg_fn u).symm
  · obtain ⟨i, hi⟩ : ∃ i, D.coordinateRoot α i ≠ 0 :=
      Function.ne_iff.mp (D.coordinateRoot_ne_zero α)
    have hker : ∀ s : Fin t.rank → Kˣ,
        torusCharacter s (D.coordinateRoot α) = 1 →
          torusCharacter s (φ (D.coordinateRoot β)) = 1 := by
      intro s hs
      apply Units.ext
      simpa only [hs, Units.val_one, hg_one] using (hg_char s).symm
    have hp := smul_eq_smul_of_torusCharacter_eq_one hker i
    have hm : φ (D.coordinateRoot β) i ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hp
      have hφ0 : φ (D.coordinateRoot β) = 0 := (smul_eq_zero.mp hp).resolve_left hi
      exact D.coordinateRoot_ne_zero β (hinj (hφ0.trans (map_zero φ).symm))
    exact ⟨φ (D.coordinateRoot β) i, D.coordinateRoot α i, hm, hi, hp⟩

/-- **A standard endomorphism with an injective character map induces a negation-preserving root
permutation** together with compatible units and field automorphisms on every root subgroup, over
every infinite field with divisible units. -/
theorem exists_rootPerm_of_isStandardEndomorphism {K : Type v} [Field K] [Infinite K]
    [RootableBy Kˣ ℕ] {F : D.points K →* D.points K} {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hstd : D.IsStandardEndomorphism K F) (hφ : IsCharacterMap (D.torusPoints K) F φ)
    (hinj : Function.Injective φ) :
    ∃ (π : Equiv.Perm (Fin t.numRoots)) (c : Fin t.numRoots → Kˣ)
      (g : Fin t.numRoots → (K ≃+* K)),
      (∀ α u, F (D.rootSubgroupPoints α K (ofAdd u)) =
        D.rootSubgroupPoints (π α) K (ofAdd ((c α : K) * g α u))) ∧
      (∀ α (s : Fin t.rank → Kˣ),
        g α (torusCharacter s (D.coordinateRoot α)) =
          torusCharacter s (φ (D.coordinateRoot (π α)))) ∧
      (∀ α, π ((t.simplyConnectedRootDatum ht).reflectionPerm α α) =
        (t.simplyConnectedRootDatum ht).reflectionPerm (π α) (π α)) ∧
      (∀ α, g ((t.simplyConnectedRootDatum ht).reflectionPerm α α) = g α) ∧
      (∀ α, ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧
        n • φ (D.coordinateRoot (π α)) = m • D.coordinateRoot α) := by
  choose β c g hF hchar hprop using
    fun α => D.exists_root_and_ringEquiv_of_isStandardEndomorphism hstd hφ hinj α
  have hβ_inj : Function.Injective β := by
    intro α₁ α₂ hβeq
    obtain ⟨m₁, n₁, _, hn₁, hp₁⟩ := hprop α₁
    obtain ⟨m₂, n₂, hm₂, hn₂, hp₂⟩ := hprop α₂
    rw [hβeq] at hp₁
    have hcoord : (n₂ * m₁) • D.coordinateRoot α₁ = (n₁ * m₂) • D.coordinateRoot α₂ := by
      calc
        (n₂ * m₁) • D.coordinateRoot α₁ = n₂ • (m₁ • D.coordinateRoot α₁) := mul_smul _ _ _
        _ = n₂ • (n₁ • φ (D.coordinateRoot (β α₂))) := by rw [← hp₁]
        _ = n₁ • (n₂ • φ (D.coordinateRoot (β α₂))) := smul_comm _ _ _
        _ = n₁ • (m₂ • D.coordinateRoot α₂) := by rw [hp₂]
        _ = (n₁ * m₂) • D.coordinateRoot α₂ := (mul_smul _ _ _).symm
    have hroot : (n₂ * m₁) • (t.simplyConnectedRootDatum ht).root α₁ =
        (n₁ * m₂) • (t.simplyConnectedRootDatum ht).root α₂ := by
      have h := congrArg D.weightLatticeEmbedding hcoord
      rw [map_zsmul, map_zsmul] at h
      simpa only [coordinateRoot_def, D.weightLatticeEmbedding_repr, Submodule.coe_mk] using h
    have hnotlin : ¬ LinearIndependent ℤ
        ![(t.simplyConnectedRootDatum ht).root α₁, (t.simplyConnectedRootDatum ht).root α₂] := by
      intro hlin
      have hzero : (-(n₂ * m₁)) • (t.simplyConnectedRootDatum ht).root α₁ +
          (n₁ * m₂) • (t.simplyConnectedRootDatum ht).root α₂ = 0 := by
        rw [neg_smul, hroot, neg_add_cancel]
      exact mul_ne_zero hn₁ hm₂ (hlin.eq_zero_of_pair hzero).2
    let _ := t.isReduced_simplyConnectedRootDatum ht
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := t.simplyConnectedRootDatum ht) α₁ α₂ hnotlin
      with heq | hneg
    · exact (t.simplyConnectedRootDatum ht).root.injective heq
    · exfalso
      have hcoord_neg : D.coordinateRoot α₂ = -D.coordinateRoot α₁ := by
        apply D.weightLatticeEmbedding_injective
        rw [map_neg]
        simpa only [coordinateRoot_def, D.weightLatticeEmbedding_repr, Submodule.coe_mk] using
          neg_eq_iff_eq_neg.mp hneg.symm
      obtain ⟨i, hi⟩ : ∃ i, D.coordinateRoot α₁ i ≠ 0 :=
        Function.ne_iff.mp (D.coordinateRoot_ne_zero α₁)
      have hN : (D.coordinateRoot α₁ i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hi
      apply false_of_pow_mul_eq_one (g α₁).toRingHom (g α₂).toRingHom hN
      intro x hx
      let u : Kˣ := Units.mk0 x hx
      have hs₁ := hchar α₁ (Pi.mulSingle i u)
      have hs₂ := hchar α₂ (Pi.mulSingle i u)
      rw [hβeq] at hs₁
      rw [hcoord_neg, torusCharacter_neg, torusCharacter_mulSingle] at hs₂
      rw [torusCharacter_mulSingle] at hs₁
      have hprod : (g α₁) (x ^ D.coordinateRoot α₁ i) * (g α₂) (x ^ D.coordinateRoot α₁ i) = 1 := by
        have hinv : (g α₂) ((x ^ D.coordinateRoot α₁ i)⁻¹) =
            ((g α₂) (x ^ D.coordinateRoot α₁ i))⁻¹ := map_inv₀ (g α₂) _
        have hs₂' : ((g α₂) (x ^ D.coordinateRoot α₁ i))⁻¹ =
            (torusCharacter (Pi.mulSingle i u) (φ (D.coordinateRoot (β α₂))) : K) := by
          simpa only [u, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, Units.val_mk0,
            hinv] using hs₂
        have hs₁' : (g α₁) (x ^ D.coordinateRoot α₁ i) =
            (torusCharacter (Pi.mulSingle i u) (φ (D.coordinateRoot (β α₂))) : K) := by
          simpa only [u, Units.val_zpow_eq_zpow_val, Units.val_mk0] using hs₁
        rw [hs₁', ← hs₂', inv_mul_cancel₀]
        intro h0
        exact zpow_ne_zero _ hx ((g α₂).injective (h0.trans (map_zero _).symm))
      have hpow : ((g α₁).toRingHom x * (g α₂).toRingHom x) ^ D.coordinateRoot α₁ i = 1 := by
        rw [mul_zpow, ← map_zpow₀ (g α₁).toRingHom, ← map_zpow₀ (g α₂).toRingHom]
        exact hprod
      rcases Int.natAbs_eq (D.coordinateRoot α₁ i) with hpos | hneg'
      · rw [hpos, zpow_natCast] at hpow
        exact hpow
      · rw [hneg', zpow_neg, zpow_natCast] at hpow
        exact inv_eq_one.mp hpow
  let π : Equiv.Perm (Fin t.numRoots) :=
    Equiv.ofBijective β (Finite.injective_iff_bijective.mp hβ_inj)
  have hπ (α : Fin t.numRoots) : π α = β α := rfl
  have hneg_and_g (α : Fin t.numRoots) :
      π ((t.simplyConnectedRootDatum ht).reflectionPerm α α) =
        (t.simplyConnectedRootDatum ht).reflectionPerm (π α) (π α) ∧
      g ((t.simplyConnectedRootDatum ht).reflectionPerm α α) = g α := by
    let α' := (t.simplyConnectedRootDatum ht).reflectionPerm α α
    let β' := (t.simplyConnectedRootDatum ht).reflectionPerm (β α') (β α')
    have h₂ : ∀ s : Fin t.rank → Kˣ,
        (g α').toRingHom (torusCharacter s (D.coordinateRoot α)) =
          torusCharacter s (φ (D.coordinateRoot β')) := by
      intro s
      have hs := hchar α' s
      rw [D.coordinateRoot_reflectionPerm_self α, torusCharacter_neg, Units.val_inv_eq_inv_val,
        map_inv₀] at hs
      have hinv := congrArg Inv.inv hs
      rw [inv_inv, ← Units.val_inv_eq_inv_val, ← torusCharacter_neg, ← map_neg,
        ← D.coordinateRoot_reflectionPerm_self (β α')] at hinv
      exact hinv
    obtain ⟨hβeq, hgeq⟩ := D.eq_of_ringHom_torusCharacter_eq hinj
      (g₁ := (g α).toRingHom) (g₂ := (g α').toRingHom) (hchar α) h₂
    refine ⟨?_, RingEquiv.ext fun x => DFunLike.congr_fun hgeq.symm x⟩
    simp only [hπ]
    rw [hβeq]
    exact (reflectionPerm_self_involutive (t.simplyConnectedRootDatum ht) (β α')).symm
  exact ⟨π, c, g, fun α u => hF α u, fun α s => hchar α s,
    fun α => (hneg_and_g α).1, fun α => (hneg_and_g α).2, fun α => hprop α⟩

/-- If a based endomorphism maps `x_α` onto `x_{π α}` over an integral domain, then `π` preserves
the set of positive roots. -/
theorem mem_posRoots_iff_of_isBasedEndomorphism {A : Type v} [CommRing A] [IsDomain A]
    {F : D.points A →* D.points A} (hbased : D.IsBasedEndomorphism A F)
    {π : Equiv.Perm (Fin t.numRoots)}
    (hπ : ∀ α, (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints (π α) A).range)
    (α : Fin t.numRoots) :
    π α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) ↔
      α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
  have hfwd : Set.MapsTo π (posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
      (posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) := by
    intro γ hγ
    obtain ⟨β, hβ, hmap⟩ := hbased.2 γ hγ
    have heq : π γ = β := (D.range_rootSubgroupPoints_eq_iff A (π γ) β).mp ((hπ γ).symm.trans hmap)
    rwa [heq]
  have hbij : Set.BijOn π (posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
      (posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :=
    ((posRoots_finite _ _).injOn_iff_bijOn_of_mapsTo hfwd).mp π.injective.injOn
  constructor
  · intro hπα
    obtain ⟨γ, hγ, hπγ⟩ := hbij.surjOn hπα
    rwa [← π.injective hπγ]
  · exact fun hα => hfwd hα

end Extraction

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

private theorem coe_scPointsEquiv (A : Type v) [CommRing A]
    (g : (t.scChevalleyDatum ht).points A) :
    ((t.scPointsEquiv ht A g : _) : Matrix.GeneralLinearGroup (Fin (t.scWeightBasisCard ht)) A) =
      (g : Matrix.GeneralLinearGroup (Fin (t.scChevalleyDatum ht).dim) A) :=
  MulEquiv.subgroupCongr_apply _ g

/-- The diagram automorphism of the points of `t.scChevalleyDatum ht`, obtained by transporting
`t.scToralDiagramAutPoints ht hσ A` along `chevalleyGroup_eq_kostantToralPointsSubgroup`. -/
noncomputable def scChevalleyDatumDiagramAut (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] :
    MulAut ((t.scChevalleyDatum ht).points A) :=
  MulAut.congr (t.scPointsEquiv ht A).symm (t.scToralDiagramAutPoints ht hσ A)

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
          (t.scWeightBasis ht) (t.scWeight ht) γ A (ofAdd v) := by
    apply Subtype.ext
    refine (t.coe_scPointsEquiv ht A _).trans ?_
    exact ((t.scChevalleyDatum ht).coe_rootSubgroupPoints γ A (ofAdd v)).trans
      (coe_chevalleyToralRootSubgroupPoints (t := t) (ht := ht)
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) γ A (ofAdd v)).symm
  apply (t.scPointsEquiv ht A).injective
  have h1 : t.scPointsEquiv ht A (t.scChevalleyDatumDiagramAut ht hσ A
      ((t.scChevalleyDatum ht).rootSubgroupPoints α A (ofAdd u))) =
      t.scToralDiagramAutPoints ht hσ A
        (t.scPointsEquiv ht A ((t.scChevalleyDatum ht).rootSubgroupPoints α A (ofAdd u))) :=
    (t.scPointsEquiv ht A).apply_symm_apply _
  exact h1.trans ((congrArg (t.scToralDiagramAutPoints ht hσ A) (hroot α u)).trans
    ((t.scToralDiagramAutPoints_chevalleyToralRootSubgroupPoints ht hσ α A u).trans
      (hroot _ _).symm))

private theorem scPointsEquiv_torusPoints (A : Type v) [CommRing A] (r : Fin t.rank → Aˣ) :
    t.scPointsEquiv ht A ((t.scChevalleyDatum ht).torusPoints A r) =
      kostantToralWeightTorusPoints (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) A r := by
  apply Subtype.ext
  refine (t.coe_scPointsEquiv ht A _).trans ?_
  have h1 := (t.scChevalleyDatum ht).coe_torusPoints A r
  rw [t.scChevalleyDatum_coordinateWeight ht] at h1
  exact h1.trans (coe_kostantToralWeightTorusPoints (t.lieBasis ht).rootGenerator
    (t.lieBasis ht).h (representation ℚ (t.lieAlgebra ht) (t.scModule ht))
    (t.scLattice ht).toAddSubgroup (t.kostantForm_apply_mem_scLattice ht)
    (t.isNilpotent_representation_scModule_rootGenerator ht)
    (t.scWeightBasis ht) (t.scWeight ht) A r).symm

/-- On the torus of `scChevalleyDatum`, the diagram automorphism relabels parameters by `σ⁻¹`. -/
@[simp]
theorem scChevalleyDatumDiagramAut_torusPoints (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) :
    t.scChevalleyDatumDiagramAut ht hσ A ((t.scChevalleyDatum ht).torusPoints A s) =
      (t.scChevalleyDatum ht).torusPoints A (fun k => s (σ⁻¹ k)) := by
  apply (t.scPointsEquiv ht A).injective
  have h1 : t.scPointsEquiv ht A (t.scChevalleyDatumDiagramAut ht hσ A
      ((t.scChevalleyDatum ht).torusPoints A s)) =
      t.scToralDiagramAutPoints ht hσ A
        (t.scPointsEquiv ht A ((t.scChevalleyDatum ht).torusPoints A s)) :=
    (t.scPointsEquiv ht A).apply_symm_apply _
  exact h1.trans ((congrArg (t.scToralDiagramAutPoints ht hσ A)
    (t.scPointsEquiv_torusPoints ht A s)).trans
    ((t.scToralDiagramAutPoints_kostantToralWeightTorusPoints ht hσ A s).trans
      (t.scPointsEquiv_torusPoints ht A _).symm))

/-- The diagram automorphism on `scChevalleyDatum` has character map equal to the weight map of
the inverse root-datum diagram automorphism, over every commutative ring. -/
theorem isCharacterMap_scChevalleyDatumDiagramAut (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] :
    IsCharacterMap ((t.scChevalleyDatum ht).torusPoints A)
      (t.scChevalleyDatumDiagramAut ht hσ A).toMonoidHom
      (diagramAut ht hσ)⁻¹.toHom.weightMap := by
  refine isCharacterMap_iff.mpr fun s => ?_
  apply (t.scPointsEquiv ht A).injective
  have h1 : t.scPointsEquiv ht A (t.scChevalleyDatumDiagramAut ht hσ A
      ((t.scChevalleyDatum ht).torusPoints A s)) =
      t.scToralDiagramAutPoints ht hσ A
        (t.scPointsEquiv ht A ((t.scChevalleyDatum ht).torusPoints A s)) :=
    (t.scPointsEquiv ht A).apply_symm_apply _
  exact h1.trans ((congrArg (t.scToralDiagramAutPoints ht hσ A)
    (t.scPointsEquiv_torusPoints ht A s)).trans
    (((t.isCharacterMap_scToralDiagramAutPoints ht hσ A).map_apply s).trans
      (t.scPointsEquiv_torusPoints ht A _).symm))

private theorem diagramRootPerm_mem_posRoots_iff (hσ : σ ∈ t.diagramSymmetry)
    (α : Fin t.numRoots) :
    t.diagramRootPerm ht hσ α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) ↔
      α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
  have hbase : (t.rationalBase ht).map (t.rationalDiagramAut ht hσ) = t.rationalBase ht := by
    classical
    apply RootPairing.Base.ext
    rw [(t.rationalBase ht).support_map_eq]
    ext j
    simp only [Finset.mem_image, rationalDiagramAut_indexEquiv]
    constructor
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hk
      rw [t.diagramRootPerm_simpleIndex ht hσ i]
      exact simpleIndex_mem_support (σ i)
    · intro hj
      obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hj
      refine ⟨t.simpleIndex ht (σ⁻¹ i), simpleIndex_mem_support _, ?_⟩
      rw [t.diagramRootPerm_simpleIndex ht hσ, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  have himg := posRoots_map (t.rationalRootSystem ht) (t.rationalBase ht)
    (t.rationalDiagramAut ht hσ)
  rw [hbase, rationalDiagramAut_indexEquiv] at himg
  constructor
  · intro h
    rw [himg] at h
    obtain ⟨γ, hγ, hγeq⟩ := h
    rwa [← (t.diagramRootPerm ht hσ).injective hγeq]
  · intro h
    rw [himg]
    exact ⟨α, h, rfl⟩

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
    refine ChevalleyDatum.map_range_rootSubgroupPoints_eq_of_surjective
      (g := fun u : A => (ε : A) * u)
      (fun v => ⟨((ε⁻¹ : Aˣ) : A) * v, by simp [← mul_assoc]⟩) fun u => ?_
    simp [ε]
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
  have h := ((t.isCharacterMap_scChevalleyDatumDiagramAut ht hσ A).comp hφ).comp hinv
  simpa only [mul_assoc] using h

end TauCeti.DynkinType
