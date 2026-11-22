/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.Basic

/-!
# Positive-root coordinates in Chevalley groups

Every positive point of any Chevalley datum has an ordered positive-root product expression.
For the full-weight simply connected datum the parameters are unique.

For the full-weight Chevalley datum of any valid Dynkin type, multiplication of the positive
root subgroups in any order without repetitions is a bijection onto the positive point
subgroup over every commutative ring. The parameters are indexed only by positive roots:
there are no unused coordinates at negative roots. The resulting equivalence and its inverse
commute with changes of the value ring, including noninjective ring maps.

This combines the collection theorem
`mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_prod` with the integral
uniqueness theorem `DynkinType.list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj`.
It gives coordinates for the positive factor in Bruhat and big-cell factorizations. It does
not identify the entire point group with its elementary subgroup, or assert a
scheme-theoretic factorization.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.3.3.
-/

public section

open Multiplicative TensorProduct TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v w

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

local notation "PositiveRoot" =>
  {γ // γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)}

/-- Multiply positive-root parameters in the order of `l`, as an element of the positive
point subgroup. This is a map of sets, not an assertion that coordinates add under multiplication.
-/
noncomputable def positiveRootProduct (l : List PositiveRoot) (A : Type v) [CommRing A]
    (u : PositiveRoot → A) : D.positivePoints A :=
  ⟨(l.map fun γ => D.rootSubgroupPoints γ.val A (ofAdd (u γ))).prod,
    Subgroup.list_prod_mem _ fun _ hg => by
      obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hg
      exact D.rootSubgroupPoints_mem_positivePoints A γ.property _⟩

/-- The positive-root product has the stated ordered factors in the datum point group. -/
@[simp]
theorem coe_positiveRootProduct (l : List PositiveRoot) (A : Type v) [CommRing A]
    (u : PositiveRoot → A) :
    (D.positiveRootProduct l A u : D.points A) =
      (l.map fun γ => D.rootSubgroupPoints γ.val A (ofAdd (u γ))).prod :=
  (rfl)

/-- Changing the value ring applies the ring map to each root coordinate. -/
theorem map_positiveRootProduct (l : List PositiveRoot)
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (u : PositiveRoot → A) :
    (D.pointsPresentation A).map (D.pointsPresentation B) f
        (D.positiveRootProduct l A u : D.points A) =
      (D.positiveRootProduct l B (fun γ => f (u γ)) : D.points B) := by
  simp only [coe_positiveRootProduct, map_list_prod, List.map_map, Function.comp_def,
    D.map_rootSubgroupPoints, toAdd_ofAdd]

attribute [local instance high] Algebra.toModule

/-- Every positive point has coordinates in any enumeration of the positive roots.
No field or reducedness hypothesis is required. -/
theorem positiveRootProduct_surjective (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    Function.Surjective (D.positiveRootProduct l A) := by
  intro g
  have hg := (D.mem_positivePoints_iff).mp g.property
  obtain ⟨q, hq, hmatrix⟩ := hg
  rw [D.positiveSubgroup_eq_iSup] at hq
  obtain ⟨u, hu⟩ := (mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_prod
    D.representation D.lattice D.representation_mem_lattice
    D.isNilpotent_representation_rootGenerator (CommAlgCat.of ℤ A) l hl hcover q).mp hq
  refine ⟨u, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have h := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom) hu
  simpa only [map_list_prod, List.map_map, Function.comp_def,
    coe_positiveRootProduct, SubmonoidClass.coe_list_prod,
    coe_rootSubgroupPoints, MulEquiv.toMonoidHom_eq_coe, hmatrix] using h

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
    exact ⟨u, congrArg Subtype.val hu⟩
  · rintro ⟨u, rfl⟩
    exact (D.positiveRootProduct l A u).property

/-- **Splitting positive points along an arbitrary subset of positive roots.** For any subset
`S ⊆ posRoots`, every positive point factors as `u₁ * u₂` with `u₁` in the subgroup
generated by the root subgroups of `S` and `u₂` in that of `posRoots \ S`. -/
theorem mem_positivePoints_iff_exists_mul_of_subset
    {S : Set (Fin t.numRoots)}
    (hS : S ⊆ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type v) [CommRing A] (g : D.points A) :
    g ∈ D.positivePoints A ↔
      ∃ u₁ ∈ (⨆ γ ∈ S, (D.rootSubgroupPoints γ A).range : Subgroup (D.points A)),
        ∃ u₂ ∈ (⨆ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) \ S,
          (D.rootSubgroupPoints γ A).range : Subgroup (D.points A)),
          u₁ * u₂ = g := by
  classical
  constructor
  · -- Enumerate `S` before `posRoots \ S` so ordered collection splits the product.
    intro hg
    let p : PositiveRoot → Bool := fun γ => decide (γ.val ∈ S)
    let l₁ := (Finset.univ : Finset PositiveRoot).toList.filter p
    let l₂ := (Finset.univ : Finset PositiveRoot).toList.filter (fun γ => !p γ)
    have hperm := List.filter_append_perm p (Finset.univ : Finset PositiveRoot).toList
    have hl : (l₁ ++ l₂).Nodup := hperm.nodup_iff.mpr Finset.univ.nodup_toList
    have hcover : ∀ γ : PositiveRoot, γ ∈ l₁ ++ l₂ :=
      fun γ => hperm.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ γ))
    obtain ⟨u, rfl⟩ := (D.mem_positivePoints_iff_exists_prod A hl hcover g).mp hg
    rw [List.map_append, List.prod_append]
    refine ⟨_, Subgroup.list_prod_mem _ ?_, _, Subgroup.list_prod_mem _ ?_, rfl⟩
    · intro x hx
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hx
      have hγS : γ.val ∈ S := of_decide_eq_true (List.mem_filter.mp hγ).2
      exact le_iSup₂ (f := fun γ _ => (D.rootSubgroupPoints γ A).range)
        γ.val hγS ⟨ofAdd (u γ), rfl⟩
    · intro x hx
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hx
      have hγS : γ.val ∉ S := of_decide_eq_false (by simpa [p] using (List.mem_filter.mp hγ).2)
      exact le_iSup₂ (f := fun γ _ => (D.rootSubgroupPoints γ A).range)
        γ.val ⟨γ.property, hγS⟩ ⟨ofAdd (u γ), rfl⟩
  · -- Conversely, both root-subgroup joins lie inside `positivePoints`.
    rintro ⟨u₁, hu₁, u₂, hu₂, rfl⟩
    rw [D.positivePoints_eq_iSup A]
    exact Subgroup.mul_mem _
      (IsConcreteLE.le_iff.mp (biSup_mono hS) hu₁)
      (IsConcreteLE.le_iff.mp (biSup_mono Set.sdiff_subset) hu₂)

end TauCeti.DynkinType.ChevalleyDatum

namespace TauCeti.DynkinType

universe v w

variable (t : DynkinType) (ht : t.Valid)

local notation "D" => t.scChevalleyDatum ht
local notation "PositiveRoot" =>
  {γ // γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)}

/-- In the full-weight model, an ordered enumeration of all positive roots without repetitions
gives an injective parameter map. The value ring is arbitrary. -/
theorem scChevalleyDatum_positiveRootProduct_injective (l : List PositiveRoot) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    Function.Injective ((D).positiveRootProduct l A) := by
  classical
  intro u v huv
  let extend := fun (u : PositiveRoot → A) (γ : Fin t.numRoots) =>
    if h : γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) then u ⟨γ, h⟩ else 0
  have heq := congrArg (fun g : (D).positivePoints A => (g : (D).points A)) huv
  have hprod (u : PositiveRoot → A) :
      ((l.map Subtype.val).map fun γ => (D).rootSubgroupPoints γ A
        (ofAdd (extend u γ))).prod = ((D).positiveRootProduct l A u : (D).points A) := by
    simp only [ChevalleyDatum.coe_positiveRootProduct, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro γ _
    simp only [extend, dite_eq_left γ.property]
  have hparams := (t.list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj ht A
    (hl.map Subtype.val_injective)
    (by rintro γ hγ; obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hγ; exact γ.property)).mp
      ((hprod u).trans (heq.trans (hprod v).symm))
  funext γ
  simpa only [extend, dite_eq_left γ.property] using
    hparams γ.val (List.mem_map.mpr ⟨γ, hcover γ, rfl⟩)

/-- In the full-weight simply connected datum, every positive point has exactly one
positive-root parameter tuple in any prescribed duplicate-free order. No characteristic or
reducedness hypothesis is needed. -/
theorem mem_scChevalleyDatum_positivePoints_iff_existsUnique_prod
    (A : Type v) [CommRing A]
    {l : List PositiveRoot} (hl : l.Nodup) (hall : ∀ γ, γ ∈ l) (g : (D).points A) :
    g ∈ (D).positivePoints A ↔
      ∃! u : PositiveRoot → A,
        (l.map fun γ => (D).rootSubgroupPoints γ.val A (ofAdd (u γ))).prod = g := by
  have hinj : Function.Injective (fun u : PositiveRoot → A =>
      (l.map fun γ => (D).rootSubgroupPoints γ.val A (ofAdd (u γ))).prod) := by
    intro u v huv
    exact t.scChevalleyDatum_positiveRootProduct_injective ht l hl hall A
      (Subtype.ext huv)
  rw [(D).mem_positivePoints_iff_exists_prod A hl hall g]
  exact hinj.existsUnique_iff_exists.symm

/-- Positive-root coordinates for a full-weight Chevalley datum over an arbitrary
commutative ring. The list enumerates all positive roots, in any order without repetitions. -/
noncomputable def scPositiveRootEquiv (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    (PositiveRoot → A) ≃ (D).positivePoints A :=
  Equiv.ofBijective ((D).positiveRootProduct l A)
    ⟨t.scChevalleyDatum_positiveRootProduct_injective ht l hl hcover A,
      (D).positiveRootProduct_surjective l hl hcover A⟩

/-- The coordinate equivalence multiplies the given root parameters in the specified order. -/
@[simp]
theorem scPositiveRootEquiv_apply (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A]
    (u : PositiveRoot → A) :
    t.scPositiveRootEquiv ht l hl hcover A u = (D).positiveRootProduct l A u :=
  (rfl)

/-- Extracting coordinates from an ordered positive-root product recovers its parameters. -/
@[simp]
theorem scPositiveRootEquiv_symm_positiveRootProduct
    (l : List PositiveRoot) (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    (A : Type v) [CommRing A] (u : PositiveRoot → A) :
    (t.scPositiveRootEquiv ht l hl hcover A).symm ((D).positiveRootProduct l A u) = u :=
  (t.scPositiveRootEquiv ht l hl hcover A).symm_apply_apply u

/-- Multiplying the extracted positive-root coordinates reproduces the original positive point. -/
@[simp]
theorem positiveRootProduct_scPositiveRootEquiv_symm
    (l : List PositiveRoot) (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    (A : Type v) [CommRing A] (g : (D).positivePoints A) :
    (D).positiveRootProduct l A ((t.scPositiveRootEquiv ht l hl hcover A).symm g) = g :=
  (t.scPositiveRootEquiv ht l hl hcover A).apply_symm_apply g

/-- Extracting coordinates after scalar change applies the ring map coordinatewise. In
particular, coordinates are natural even under reduction modulo a prime. -/
@[simp]
theorem scPositiveRootEquiv_symm_map (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (g : (D).positivePoints A) :
    (t.scPositiveRootEquiv ht l hl hcover B).symm
        ⟨((D).pointsPresentation A).map ((D).pointsPresentation B) f (g : (D).points A),
          (D).map_positivePoints_le f (Subgroup.mem_map.mpr ⟨g, g.property, rfl⟩)⟩ =
      fun γ => f ((t.scPositiveRootEquiv ht l hl hcover A).symm g γ) := by
  apply (t.scPositiveRootEquiv ht l hl hcover B).injective
  simp only [Equiv.apply_symm_apply, scPositiveRootEquiv_apply]
  apply Subtype.ext
  rw [← (D).map_positiveRootProduct l f]
  exact congrArg (((D).pointsPresentation A).map ((D).pointsPresentation B) f)
    (congrArg Subtype.val
      ((t.scPositiveRootEquiv ht l hl hcover A).apply_symm_apply g).symm)

end TauCeti.DynkinType
