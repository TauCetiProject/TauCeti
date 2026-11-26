/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Subsystem.Coordinates
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.Basic
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# Positive-root coordinates in Chevalley groups

For every Chevalley datum `D` of every valid Dynkin type, multiplication of the positive root
subgroups in any fixed duplicate-free enumeration `l` of the positive roots is a bijection onto the
positive point subgroup `D.positivePoints A` over every commutative ring `A` — including nonreduced
rings and fields of bad characteristic. Parameters are indexed only by the positive-root subtype
`{γ // γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)}`: there are no unused
coordinates at negative roots. The resulting equivalence `ChevalleyDatum.positiveRootEquiv` and its
inverse commute with arbitrary ring homomorphisms, including noninjective ones.

Existence of ordered-product parameters combines the uniform collection theorem
`DynkinType.mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_prod` with
`ChevalleyDatum.positiveSubgroupMulEquivPoints`. Uniqueness specializes
`ChevalleyDatum.rootSetProduct_injective_of_degree_pos` to `DynkinType.weightDegree`. Together
they give unique coordinates for any fixed duplicate-free ordering `l` of the positive roots on the
positive unipotent factor in Bruhat and big-cell decompositions, without identifying the ambient
point group with its elementary subgroup or asserting a scheme-theoretic isomorphism.

## Main declarations

* `TauCeti.DynkinType.ChevalleyDatum.positiveRootProduct`: ordered multiplication of positive-root
  parameters into `D.positivePoints A`.
* `TauCeti.DynkinType.ChevalleyDatum.positiveRootProduct_surjective` and
  `TauCeti.DynkinType.ChevalleyDatum.positiveRootProduct_injective`: surjectivity and injectivity
  for any duplicate-free enumeration of the positive roots over any commutative ring.
* `TauCeti.DynkinType.ChevalleyDatum.mem_positivePoints_iff_existsUnique_prod`: membership in
  `D.positivePoints A` is equivalent to a unique ordered positive-root factorization.
* `TauCeti.DynkinType.ChevalleyDatum.positiveRootEquiv`: the coordinate bijection
  `({γ // γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)} → A) ≃ D.positivePoints A`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 15 and 17.
* R. W. Carter, *Simple Groups of Lie Type*, Theorems 5.2.2 and 5.3.3.
-/

public section

open Multiplicative TensorProduct TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v w

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

local notation "PositiveRoot" =>
  {γ // γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)}

attribute [local instance high] Algebra.toModule

/-- Multiply positive-root parameters in the order of `l`, as an element of the positive
point subgroup. This is a map of sets, not an assertion that coordinates add under multiplication.
-/
noncomputable def positiveRootProduct (l : List PositiveRoot) (A : Type v) [CommRing A]
    (u : PositiveRoot → A) : D.positivePoints A :=
  D.rootSetProduct (D.positivePoints A)
    (fun _ hγ a => D.rootSubgroupPoints_mem_positivePoints A hγ a) l u

/-- The positive-root product has the stated ordered factors in the datum point group. -/
@[simp]
theorem coe_positiveRootProduct (l : List PositiveRoot) (A : Type v) [CommRing A]
    (u : PositiveRoot → A) :
    (D.positiveRootProduct l A u : D.points A) =
      (l.map fun γ => D.rootSubgroupPoints γ.val A (ofAdd (u γ))).prod :=
  D.coe_rootSetProduct (D.positivePoints A)
    (fun _ hγ a => D.rootSubgroupPoints_mem_positivePoints A hγ a) l u

/-- Changing the value ring applies the ring map to each root coordinate. -/
theorem map_positiveRootProduct (l : List PositiveRoot)
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (u : PositiveRoot → A) :
    (D.pointsPresentation A).map (D.pointsPresentation B) f
        (D.positiveRootProduct l A u : D.points A) =
      (D.positiveRootProduct l B (fun γ => f (u γ)) : D.points B) :=
  D.map_rootSetProduct (D.positivePoints A) _ (D.positivePoints B) _ l f u

/-- Restricted scalar change on `D.positivePoints` acts coordinatewise on ordered products. -/
@[simp]
theorem mapPositivePoints_positiveRootProduct (l : List PositiveRoot)
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (u : PositiveRoot → A) :
    D.mapPositivePoints f (D.positiveRootProduct l A u) =
      D.positiveRootProduct l B (fun γ => f (u γ)) :=
  Subtype.ext ((D.coe_mapPositivePoints_apply f _).trans (D.map_positiveRootProduct l f u))

/-- Evaluating `positiveRootProduct` at the zero tuple gives the identity positive point. -/
@[simp]
theorem positiveRootProduct_zero (l : List PositiveRoot) (A : Type v) [CommRing A] :
    D.positiveRootProduct l A 0 = 1 :=
  D.rootSetProduct_zero (D.positivePoints A) _ l

/-- Evaluating a duplicate-free `positiveRootProduct` on `Pi.single γ a` for `γ ∈ l` recovers the
single positive root generator. -/
@[simp]
theorem positiveRootProduct_single {l : List PositiveRoot} (hl : l.Nodup)
    {γ : PositiveRoot} (hγ : γ ∈ l) (A : Type v) [CommRing A] (a : A) :
    D.positiveRootProduct l A (Pi.single γ a) =
      ⟨D.rootSubgroupPoints γ.val A (ofAdd a),
        D.rootSubgroupPoints_mem_positivePoints A γ.property _⟩ :=
  D.rootSetProduct_single (D.positivePoints A) _ hl hγ a

/-- Every positive point of any Chevalley datum has coordinates in any duplicate-free enumeration
of all positive roots, over any commutative ring. -/
theorem positiveRootProduct_surjective (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    Function.Surjective (D.positiveRootProduct l A) := by
  intro g
  let q := (D.positiveSubgroupMulEquivPoints A).symm g
  have hq : q.val ∈ ⨆ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
      (chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
        D.isNilpotent_representation_rootGenerator γ (CommAlgCat.of ℤ A)).range := by
    rw [← D.positiveSubgroup_eq_iSup]
    exact q.property
  obtain ⟨u, hu⟩ := (mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_prod
    D.representation D.lattice D.representation_mem_lattice
    D.isNilpotent_representation_rootGenerator (CommAlgCat.of ℤ A) l hl hcover q.val).mp hq
  refine ⟨u, ?_⟩
  have hq_eq : (l.map fun γ => (⟨chevalleyRootSubgroup D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ.val
        (CommAlgCat.of ℤ A) (ofAdd (u γ)),
      D.chevalleyRootSubgroup_mem_positiveSubgroup (CommAlgCat.of ℤ A) γ.property _⟩ :
        D.positiveSubgroup (CommAlgCat.of ℤ A))).prod = q := by
    apply Subtype.ext
    simpa only [SubmonoidClass.coe_list_prod, List.map_map, Function.comp_def] using hu
  have hmap := congrArg (D.positiveSubgroupMulEquivPoints A) hq_eq
  rw [MulEquiv.apply_symm_apply, map_list_prod] at hmap
  refine Subtype.ext ((D.coe_positiveRootProduct l A u).trans ?_)
  rw [← hmap, SubmonoidClass.coe_list_prod, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro γ _
  exact (congrArg Subtype.val
    (D.positiveSubgroupMulEquivPoints_chevalleyRootSubgroup A γ.property (ofAdd (u γ)))).symm

/-- A datum point is positive exactly when it is a product of its positive root
subgroups, in any order containing every positive root exactly once. Existence holds for every
Chevalley datum and every commutative value ring. -/
theorem mem_positivePoints_iff_exists_prod
    (A : Type v) [CommRing A] {l : List PositiveRoot}
    (hl : l.Nodup) (hall : ∀ γ, γ ∈ l) (g : D.points A) :
    g ∈ D.positivePoints A ↔
      ∃ u : PositiveRoot → A,
        (l.map fun γ => D.rootSubgroupPoints γ.val A (ofAdd (u γ))).prod = g := by
  constructor
  · intro hg
    obtain ⟨u, hu⟩ := D.positiveRootProduct_surjective l hl hall A ⟨g, hg⟩
    exact ⟨u, (D.coe_positiveRootProduct l A u).symm.trans (congrArg Subtype.val hu)⟩
  · rintro ⟨u, rfl⟩
    rw [← D.coe_positiveRootProduct l A u]
    exact (D.positiveRootProduct l A u).property

/-- For every Chevalley datum, an ordered enumeration of all positive roots without repetitions
gives an injective parameter map over any commutative ring. -/
theorem positiveRootProduct_injective (l : List PositiveRoot) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    Function.Injective (D.positiveRootProduct l A) :=
  D.rootSetProduct_injective_of_degree_pos (D.positivePoints A)
    (fun _ hγ a => D.rootSubgroupPoints_mem_positivePoints A hγ a) (t.weightDegree ht)
    (fun _ hγ => t.weightDegree_root_pos ht hγ) l hl hcover

/-- For every Chevalley datum, a datum point belongs to `D.positivePoints A` if and only if it
admits a unique expression as an ordered product of positive-root elements in the prescribed
duplicate-free order `l`, over any commutative ring. -/
theorem mem_positivePoints_iff_existsUnique_prod
    (A : Type v) [CommRing A] {l : List PositiveRoot}
    (hl : l.Nodup) (hall : ∀ γ, γ ∈ l) (g : D.points A) :
    g ∈ D.positivePoints A ↔
      ∃! u : PositiveRoot → A,
        (l.map fun γ => D.rootSubgroupPoints γ.val A (ofAdd (u γ))).prod = g :=
  D.mem_iff_existsUnique_rootSetProduct (D.positivePoints A)
    (fun _ hγ a => D.rootSubgroupPoints_mem_positivePoints A hγ a)
    (D.positiveRootProduct_injective l hl hall A)
    (D.positiveRootProduct_surjective l hl hall A) g

/-- Positive-root coordinates for any Chevalley datum over an arbitrary commutative ring.
The list enumerates all positive roots in any fixed order without repetitions. -/
noncomputable def positiveRootEquiv (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    (PositiveRoot → A) ≃ D.positivePoints A :=
  D.rootSetEquiv (D.positivePoints A)
    (fun _ hγ a => D.rootSubgroupPoints_mem_positivePoints A hγ a) l
    (D.positiveRootProduct_injective l hl hcover A)
    (D.positiveRootProduct_surjective l hl hcover A)

/-- The coordinate equivalence multiplies the given root parameters in the specified order. -/
@[simp]
theorem positiveRootEquiv_apply (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A]
    (u : PositiveRoot → A) :
    D.positiveRootEquiv l hl hcover A u = D.positiveRootProduct l A u :=
  D.rootSetEquiv_apply (D.positivePoints A)
    (fun _ hγ a => D.rootSubgroupPoints_mem_positivePoints A hγ a) l
    (D.positiveRootProduct_injective l hl hcover A)
    (D.positiveRootProduct_surjective l hl hcover A) u

/-- Extracting coordinates from an ordered positive-root product recovers its parameters. -/
@[simp]
theorem positiveRootEquiv_symm_positiveRootProduct
    (l : List PositiveRoot) (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    (A : Type v) [CommRing A] (u : PositiveRoot → A) :
    (D.positiveRootEquiv l hl hcover A).symm (D.positiveRootProduct l A u) = u := by
  rw [← D.positiveRootEquiv_apply l hl hcover A u]
  exact (D.positiveRootEquiv l hl hcover A).symm_apply_apply u

/-- Multiplying the extracted positive-root coordinates reproduces the original positive point. -/
@[simp]
theorem positiveRootProduct_positiveRootEquiv_symm
    (l : List PositiveRoot) (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    (A : Type v) [CommRing A] (g : D.positivePoints A) :
    D.positiveRootProduct l A ((D.positiveRootEquiv l hl hcover A).symm g) = g := by
  rw [← D.positiveRootEquiv_apply l hl hcover A]
  exact (D.positiveRootEquiv l hl hcover A).apply_symm_apply g

/-- The identity positive point has zero coordinates. -/
@[simp]
theorem positiveRootEquiv_symm_one (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    (D.positiveRootEquiv l hl hcover A).symm 1 = 0 :=
  D.rootSetEquiv_symm_one (D.positivePoints A)
    (fun _ hγ a => D.rootSubgroupPoints_mem_positivePoints A hγ a) l _ _

/-- Extracting coordinates from a single positive-root generator recovers `Pi.single γ a`. -/
@[simp]
theorem positiveRootEquiv_symm_rootSubgroupPoints (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A]
    (γ : PositiveRoot) (a : A) :
    (D.positiveRootEquiv l hl hcover A).symm
        ⟨D.rootSubgroupPoints γ.val A (ofAdd a),
          D.rootSubgroupPoints_mem_positivePoints A γ.property _⟩ =
      Pi.single γ a :=
  D.rootSetEquiv_symm_rootSubgroupPoints (D.positivePoints A)
    (fun _ hγ a => D.rootSubgroupPoints_mem_positivePoints A hγ a) hl (hcover γ) _ _ a

/-- Extracting positive-root coordinates after scalar change applies the ring map coordinatewise,
even when the ring map is not injective. -/
@[simp]
theorem positiveRootEquiv_symm_mapPositivePoints (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (g : D.positivePoints A) :
    (D.positiveRootEquiv l hl hcover B).symm (D.mapPositivePoints f g) =
      fun γ => f ((D.positiveRootEquiv l hl hcover A).symm g γ) :=
  D.rootSetEquiv_symm_map (D.positivePoints A)
    (fun _ hγ a => D.rootSubgroupPoints_mem_positivePoints A hγ a)
    (D.positivePoints B)
    (fun _ hγ b => D.rootSubgroupPoints_mem_positivePoints B hγ b) l f
    (D.mapPositivePoints f) (D.mapPositivePoints_positiveRootProduct l f) _ _ _ _ g

end TauCeti.DynkinType.ChevalleyDatum
