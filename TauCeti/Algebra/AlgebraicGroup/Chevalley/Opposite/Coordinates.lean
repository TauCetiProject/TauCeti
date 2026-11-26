/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Opposite.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Subsystem.Coordinates
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Coordinates
import TauCeti.LinearAlgebra.RootSystem.LongestElement
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# Negative-root coordinates in Chevalley groups

For every Chevalley datum `D` of every valid Dynkin type, multiplication of the negative root
subgroups in any fixed duplicate-free enumeration `l` of the negative roots is a bijection onto the
negative point subgroup `D.negativePoints A` over every commutative ring `A` — including nonreduced
rings and fields of bad characteristic. Parameters are indexed only by the negative-root subtype
`{γ // γ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht)}`. The resulting equivalence
`ChevalleyDatum.negativeRootEquiv` and its inverse commute with arbitrary ring homomorphisms,
including noninjective ones.

Existence of ordered negative-root parameters transports
`ChevalleyDatum.positiveRootProduct_surjective` along a conjugating point in `D.weylSubgroup A`
realizing the longest Weyl-group element `w₀`, via
`ChevalleyDatum.rootSetProduct_surjective_of_weylGroup`. Uniqueness specializes
`ChevalleyDatum.rootSetProduct_injective_of_degree_pos` to `-DynkinType.weightDegree`.
Together they furnish unique coordinates for any fixed duplicate-free ordering `l` of the negative
roots on the opposite unipotent factor `U⁻` in big-cell decompositions, without asserting a
scheme-theoretic isomorphism or generation of all scheme points.

## Main declarations

* `TauCeti.DynkinType.ChevalleyDatum.negativeRootProduct`: ordered multiplication of negative-root
  parameters into `D.negativePoints A`.
* `TauCeti.DynkinType.ChevalleyDatum.negativeRootProduct_surjective` and
  `TauCeti.DynkinType.ChevalleyDatum.negativeRootProduct_injective`: surjectivity and injectivity
  for any duplicate-free enumeration of the negative roots over any commutative ring.
* `TauCeti.DynkinType.ChevalleyDatum.mem_negativePoints_iff_existsUnique_prod`: membership in
  `D.negativePoints A` is equivalent to a unique ordered negative-root factorization.
* `TauCeti.DynkinType.ChevalleyDatum.negativeRootEquiv`: the coordinate bijection
  `({γ // γ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht)} → A) ≃ D.negativePoints A`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 17, 19, and 22.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.3.3 and §7.2.
-/

public section

open Multiplicative

namespace TauCeti.DynkinType.ChevalleyDatum

universe v w

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

local notation "NegativeRoot" =>
  {γ // γ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht)}

/-- Multiply negative-root parameters in the order of `l`, as an element of the negative
point subgroup. This is a map of sets, not an assertion that coordinates add under multiplication.
-/
noncomputable def negativeRootProduct (l : List NegativeRoot) (A : Type v) [CommRing A]
    (u : NegativeRoot → A) : D.negativePoints A :=
  D.rootSetProduct (D.negativePoints A)
    (fun _ hγ a => D.rootSubgroupPoints_mem_negativePoints A hγ a) l u

/-- The negative-root product has the stated ordered factors in the datum point group. -/
@[simp]
theorem coe_negativeRootProduct (l : List NegativeRoot) (A : Type v) [CommRing A]
    (u : NegativeRoot → A) :
    (D.negativeRootProduct l A u : D.points A) =
      (l.map fun γ => D.rootSubgroupPoints γ.val A (ofAdd (u γ))).prod :=
  D.coe_rootSetProduct (D.negativePoints A)
    (fun _ hγ a => D.rootSubgroupPoints_mem_negativePoints A hγ a) l u

/-- Changing the value ring applies the ring map to each negative-root coordinate. -/
theorem map_negativeRootProduct (l : List NegativeRoot)
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (u : NegativeRoot → A) :
    (D.pointsPresentation A).map (D.pointsPresentation B) f
        (D.negativeRootProduct l A u : D.points A) =
      (D.negativeRootProduct l B (fun γ => f (u γ)) : D.points B) :=
  D.map_rootSetProduct (D.negativePoints A) _ (D.negativePoints B) _ l f u

/-- Restricted scalar change on `D.negativePoints` acts coordinatewise on ordered products. -/
@[simp]
theorem mapNegativePoints_negativeRootProduct (l : List NegativeRoot)
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (u : NegativeRoot → A) :
    D.mapNegativePoints f (D.negativeRootProduct l A u) =
      D.negativeRootProduct l B (fun γ => f (u γ)) :=
  Subtype.ext ((D.coe_mapNegativePoints_apply f _).trans (D.map_negativeRootProduct l f u))

/-- Evaluating `negativeRootProduct` at the zero tuple gives the identity negative point. -/
@[simp]
theorem negativeRootProduct_zero (l : List NegativeRoot) (A : Type v) [CommRing A] :
    D.negativeRootProduct l A 0 = 1 :=
  D.rootSetProduct_zero (D.negativePoints A) _ l

/-- Evaluating a duplicate-free `negativeRootProduct` on `Pi.single γ a` for `γ ∈ l` recovers the
single negative root generator. -/
@[simp]
theorem negativeRootProduct_single {l : List NegativeRoot} (hl : l.Nodup)
    {γ : NegativeRoot} (hγ : γ ∈ l) (A : Type v) [CommRing A] (a : A) :
    D.negativeRootProduct l A (Pi.single γ a) =
      ⟨D.rootSubgroupPoints γ.val A (ofAdd a),
        D.rootSubgroupPoints_mem_negativePoints A γ.property _⟩ :=
  D.rootSetProduct_single (D.negativePoints A) _ hl hγ a

/-- Every negative point of any Chevalley datum has coordinates in any duplicate-free enumeration
of all negative roots, over any commutative ring. -/
theorem negativeRootProduct_surjective (l : List NegativeRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    Function.Surjective (D.negativeRootProduct l A) := by
  let P := t.simplyConnectedRootDatum ht
  let b := t.simplyConnectedBase ht
  let := t.isReduced_simplyConnectedRootDatum ht
  have hneg_eq : negRoots (t.rationalRootSystem ht) (t.rationalBase ht) = negRoots P b := by
    ext γ
    simp only [mem_negRoots, RootPairing.Base.isPos_iff, height_rationalBase, P, b]
  have hw : ∀ γ, γ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht) ↔
      P.weylGroupToPerm (longestElement P b) γ ∈
        posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    intro γ
    rw [hneg_eq, posRoots_rationalRootSystem]
    exact ⟨fun hneg => mapsTo_negRoots_posRoots_longestElement P b hneg, fun hpos => by
      have h := mapsTo_posRoots_negRoots_longestElement P b hpos
      rwa [weylGroupToPerm_longestElement_involutive P b γ] at h⟩
  let e := (P.weylGroupToPerm (longestElement P b)).subtypeEquiv hw
  refine D.rootSetProduct_surjective_of_weylGroup
    (D.positivePoints A) (fun _ hγ a => D.rootSubgroupPoints_mem_positivePoints A hγ a)
    (D.negativePoints A) (fun _ hγ a => D.rootSubgroupPoints_mem_negativePoints A hγ a)
    (fun Q hQ => D.negativePoints_le_iff.mpr hQ)
    (longestElement P b) hw l fun x => ?_
  obtain ⟨u, hu⟩ := D.positiveRootProduct_surjective (l.map e) (hl.map e.injective)
    (fun δ => List.mem_map.mpr ⟨e.symm δ, hcover _, e.apply_symm_apply δ⟩) A x
  refine ⟨u, Subtype.ext ?_⟩
  exact (D.coe_rootSetProduct (D.positivePoints A) _ (l.map e) u).trans
    ((D.coe_positiveRootProduct (l.map e) A u).symm.trans (congrArg Subtype.val hu))

/-- A datum point is negative exactly when it is a product of its negative root
subgroups, in any order containing every negative root exactly once. Existence holds for every
Chevalley datum and every commutative value ring. -/
theorem mem_negativePoints_iff_exists_prod
    (A : Type v) [CommRing A] {l : List NegativeRoot}
    (hl : l.Nodup) (hall : ∀ γ, γ ∈ l) (g : D.points A) :
    g ∈ D.negativePoints A ↔
      ∃ u : NegativeRoot → A,
        (l.map fun γ => D.rootSubgroupPoints γ.val A (ofAdd (u γ))).prod = g := by
  constructor
  · intro hg
    obtain ⟨u, hu⟩ := D.negativeRootProduct_surjective l hl hall A ⟨g, hg⟩
    exact ⟨u, (D.coe_negativeRootProduct l A u).symm.trans (congrArg Subtype.val hu)⟩
  · rintro ⟨u, rfl⟩
    rw [← D.coe_negativeRootProduct l A u]
    exact (D.negativeRootProduct l A u).property

/-- For every Chevalley datum, an ordered enumeration of all negative roots without repetitions
gives an injective parameter map over any commutative ring. -/
theorem negativeRootProduct_injective (l : List NegativeRoot) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    Function.Injective (D.negativeRootProduct l A) :=
  D.rootSetProduct_injective_of_degree_pos (D.negativePoints A)
    (fun _ hγ a => D.rootSubgroupPoints_mem_negativePoints A hγ a) (-t.weightDegree ht)
    (fun _ hγ => neg_pos.mpr (t.weightDegree_root_neg ht hγ)) l hl hcover

/-- For every Chevalley datum, a datum point belongs to `D.negativePoints A` if and only if it
admits a unique expression as an ordered product of negative-root elements in the prescribed
duplicate-free order `l`, over any commutative ring. -/
theorem mem_negativePoints_iff_existsUnique_prod
    (A : Type v) [CommRing A] {l : List NegativeRoot}
    (hl : l.Nodup) (hall : ∀ γ, γ ∈ l) (g : D.points A) :
    g ∈ D.negativePoints A ↔
      ∃! u : NegativeRoot → A,
        (l.map fun γ => D.rootSubgroupPoints γ.val A (ofAdd (u γ))).prod = g :=
  D.mem_iff_existsUnique_rootSetProduct (D.negativePoints A)
    (fun _ hγ a => D.rootSubgroupPoints_mem_negativePoints A hγ a)
    (D.negativeRootProduct_injective l hl hall A)
    (D.negativeRootProduct_surjective l hl hall A) g

/-- Negative-root coordinates for any Chevalley datum over an arbitrary commutative ring.
The list enumerates all negative roots in any fixed order without repetitions. -/
noncomputable def negativeRootEquiv (l : List NegativeRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    (NegativeRoot → A) ≃ D.negativePoints A :=
  D.rootSetEquiv (D.negativePoints A)
    (fun _ hγ a => D.rootSubgroupPoints_mem_negativePoints A hγ a) l
    (D.negativeRootProduct_injective l hl hcover A)
    (D.negativeRootProduct_surjective l hl hcover A)

/-- The coordinate equivalence multiplies the given negative-root parameters in the specified
order. -/
@[simp]
theorem negativeRootEquiv_apply (l : List NegativeRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A]
    (u : NegativeRoot → A) :
    D.negativeRootEquiv l hl hcover A u = D.negativeRootProduct l A u :=
  D.rootSetEquiv_apply (D.negativePoints A)
    (fun _ hγ a => D.rootSubgroupPoints_mem_negativePoints A hγ a) l
    (D.negativeRootProduct_injective l hl hcover A)
    (D.negativeRootProduct_surjective l hl hcover A) u

/-- Extracting coordinates from an ordered negative-root product recovers its parameters. -/
@[simp]
theorem negativeRootEquiv_symm_negativeRootProduct
    (l : List NegativeRoot) (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    (A : Type v) [CommRing A] (u : NegativeRoot → A) :
    (D.negativeRootEquiv l hl hcover A).symm (D.negativeRootProduct l A u) = u := by
  rw [← D.negativeRootEquiv_apply l hl hcover A u]
  exact (D.negativeRootEquiv l hl hcover A).symm_apply_apply u

/-- Multiplying the extracted negative-root coordinates reproduces the original negative point. -/
@[simp]
theorem negativeRootProduct_negativeRootEquiv_symm
    (l : List NegativeRoot) (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    (A : Type v) [CommRing A] (g : D.negativePoints A) :
    D.negativeRootProduct l A ((D.negativeRootEquiv l hl hcover A).symm g) = g := by
  rw [← D.negativeRootEquiv_apply l hl hcover A]
  exact (D.negativeRootEquiv l hl hcover A).apply_symm_apply g

/-- The identity negative point has zero coordinates. -/
@[simp]
theorem negativeRootEquiv_symm_one (l : List NegativeRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    (D.negativeRootEquiv l hl hcover A).symm 1 = 0 :=
  D.rootSetEquiv_symm_one (D.negativePoints A)
    (fun _ hγ a => D.rootSubgroupPoints_mem_negativePoints A hγ a) l _ _

/-- Extracting coordinates from a single negative-root generator recovers `Pi.single γ a`. -/
@[simp]
theorem negativeRootEquiv_symm_rootSubgroupPoints (l : List NegativeRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A]
    (γ : NegativeRoot) (a : A) :
    (D.negativeRootEquiv l hl hcover A).symm
        ⟨D.rootSubgroupPoints γ.val A (ofAdd a),
          D.rootSubgroupPoints_mem_negativePoints A γ.property _⟩ =
      Pi.single γ a :=
  D.rootSetEquiv_symm_rootSubgroupPoints (D.negativePoints A)
    (fun _ hγ a => D.rootSubgroupPoints_mem_negativePoints A hγ a) hl (hcover γ) _ _ a

/-- Extracting negative-root coordinates after scalar change applies the ring map coordinatewise,
even when the ring map is not injective. -/
@[simp]
theorem negativeRootEquiv_symm_mapNegativePoints (l : List NegativeRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (g : D.negativePoints A) :
    (D.negativeRootEquiv l hl hcover B).symm (D.mapNegativePoints f g) =
      fun γ => f ((D.negativeRootEquiv l hl hcover A).symm g γ) :=
  D.rootSetEquiv_symm_map (D.negativePoints A)
    (fun _ hγ a => D.rootSubgroupPoints_mem_negativePoints A hγ a)
    (D.negativePoints B)
    (fun _ hγ b => D.rootSubgroupPoints_mem_negativePoints B hγ b) l f
    (D.mapNegativePoints f) (D.mapNegativePoints_negativeRootProduct l f) _ _ _ _ g

end TauCeti.DynkinType.ChevalleyDatum
