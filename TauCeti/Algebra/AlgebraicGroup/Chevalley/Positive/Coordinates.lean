/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Positive-root coordinates in Chevalley groups

For **any** Chevalley datum `D` of **any** valid Dynkin type and **any** commutative ring `A`,
multiplication of the positive root subgroups in any order without repetitions is a bijection onto
the positive point subgroup `D.positivePoints A` (`ChevalleyDatum.positiveRootEquiv`). The
parameters are indexed only by positive roots: there are no unused coordinates at negative roots.
The resulting equivalence and its inverse commute with changes of the value ring, including
noninjective ring maps.

In particular, every element of `D.positivePoints A` admits a **unique** ordered product
representation along `l`, the positive point subgroup over a finite commutative ring `A` is finite,
and `Nat.card (D.positivePoints A) = Nat.card A ^ (posRoots ...).ncard` unconditionally.

This combines the collection theorem
`mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_prod` with the integral
uniqueness theorem `ChevalleyDatum.list_prod_map_rootSubgroupPoints_inj`.
It gives coordinates for the positive factor in Bruhat and big-cell factorizations. It does
not identify the entire point group with its elementary subgroup, or assert a
scheme-theoretic factorization.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17 and Corollary.
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

/-- The empty positive-root product is the identity element of `D.positivePoints A`. -/
@[simp]
theorem positiveRootProduct_nil (A : Type v) [CommRing A] (u : PositiveRoot → A) :
    D.positiveRootProduct [] A u = 1 := by
  ext1
  simp

/-- Prepending a positive root multiplies its root-subgroup element on the left inside
`D.positivePoints A`. -/
@[simp]
theorem positiveRootProduct_cons (γ : PositiveRoot) (l : List PositiveRoot)
    (A : Type v) [CommRing A] (u : PositiveRoot → A) :
    D.positiveRootProduct (γ :: l) A u =
      ⟨D.rootSubgroupPoints γ.val A (ofAdd (u γ)),
        D.rootSubgroupPoints_mem_positivePoints A γ.property _⟩ *
        D.positiveRootProduct l A u := by
  ext1
  simp

/-- Concatenating lists of positive roots multiplies the corresponding positive-root products in
`D.positivePoints A`. -/
theorem positiveRootProduct_append (l₁ l₂ : List PositiveRoot)
    (A : Type v) [CommRing A] (u : PositiveRoot → A) :
    D.positiveRootProduct (l₁ ++ l₂) A u =
      D.positiveRootProduct l₁ A u * D.positiveRootProduct l₂ A u := by
  ext1
  simp

/-- Zero coordinates evaluate to the identity element of `D.positivePoints A`. -/
@[simp]
theorem positiveRootProduct_zero (l : List PositiveRoot) (A : Type v) [CommRing A] :
    D.positiveRootProduct l A 0 = 1 := by
  ext1
  rw [coe_positiveRootProduct, Subgroup.coe_one]
  exact List.prod_eq_one fun _ hx => by
    obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hx
    simp

/-- Changing the value ring applies the ring map to each root coordinate. -/
@[simp]
theorem map_positiveRootProduct (l : List PositiveRoot)
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (u : PositiveRoot → A) :
    D.mapPositivePoints f (D.positiveRootProduct l A u) =
      D.positiveRootProduct l B (f ∘ u) := by
  ext1
  simp only [coe_mapPositivePoints_apply, coe_positiveRootProduct, map_list_prod,
    List.map_map, Function.comp_def, D.map_rootSubgroupPoints, toAdd_ofAdd]

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

/-- For any Chevalley datum, an ordered product along any duplicate-free list of positive roots
determines all coordinates occurring in the list. The value ring is arbitrary. -/
theorem positiveRootProduct_inj (l : List PositiveRoot) (hl : l.Nodup)
    (A : Type v) [CommRing A] {u v : PositiveRoot → A} :
    D.positiveRootProduct l A u = D.positiveRootProduct l A v ↔
      ∀ γ ∈ l, u γ = v γ := by
  classical
  constructor
  · intro huv
    let extend := fun (u : PositiveRoot → A) (γ : Fin t.numRoots) =>
      if h : γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) then u ⟨γ, h⟩ else 0
    have heq := congrArg (fun g : D.positivePoints A => (g : D.points A)) huv
    have hprod (w : PositiveRoot → A) :
        ((l.map Subtype.val).map fun γ => D.rootSubgroupPoints γ A
          (ofAdd (extend w γ))).prod = (D.positiveRootProduct l A w : D.points A) := by
      simp only [coe_positiveRootProduct, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro γ _
      simp only [extend, dite_eq_left γ.property]
    have hparams := (D.list_prod_map_rootSubgroupPoints_inj A
      (hl.map Subtype.val_injective)
      (by rintro γ hγ; obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hγ; exact γ.property)).mp
        ((hprod u).trans (heq.trans (hprod v).symm))
    intro γ hγ
    simpa only [extend, dite_eq_left γ.property] using
      hparams γ.val (List.mem_map.mpr ⟨γ, hγ, rfl⟩)
  · intro huv
    ext1
    simp only [coe_positiveRootProduct]
    exact congrArg List.prod (List.map_congr_left fun γ hγ => by rw [huv γ hγ])

/-- For any Chevalley datum, an ordered enumeration of all positive roots without repetitions
gives an injective parameter map. The value ring is arbitrary. -/
theorem positiveRootProduct_injective (l : List PositiveRoot) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    Function.Injective (D.positiveRootProduct l A) :=
  fun _ _ huv => funext fun γ => (D.positiveRootProduct_inj l hl A).mp huv γ (hcover γ)

/-- For any Chevalley datum, every positive point has exactly one positive-root parameter tuple in
any prescribed duplicate-free order. No characteristic or reducedness hypothesis is needed. -/
theorem mem_positivePoints_iff_existsUnique_prod
    (A : Type v) [CommRing A]
    {l : List PositiveRoot} (hl : l.Nodup) (hall : ∀ γ, γ ∈ l) (g : D.points A) :
    g ∈ D.positivePoints A ↔
      ∃! u : PositiveRoot → A,
        (l.map fun γ => D.rootSubgroupPoints γ.val A (ofAdd (u γ))).prod = g := by
  have hinj : Function.Injective (fun u : PositiveRoot → A =>
      (l.map fun γ => D.rootSubgroupPoints γ.val A (ofAdd (u γ))).prod) := by
    intro u v huv
    exact D.positiveRootProduct_injective l hl hall A (Subtype.ext huv)
  rw [D.mem_positivePoints_iff_exists_prod A hl hall g]
  exact hinj.existsUnique_iff_exists.symm

/-- Positive-root coordinates for any Chevalley datum over an arbitrary commutative ring. The list
enumerates all positive roots, in any order without repetitions. -/
noncomputable def positiveRootEquiv (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    (PositiveRoot → A) ≃ D.positivePoints A :=
  Equiv.ofBijective (D.positiveRootProduct l A)
    ⟨D.positiveRootProduct_injective l hl hcover A,
      D.positiveRootProduct_surjective l hl hcover A⟩

/-- The coordinate equivalence multiplies the given root parameters in the specified order. -/
theorem positiveRootEquiv_apply (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A]
    (u : PositiveRoot → A) :
    D.positiveRootEquiv l hl hcover A u = D.positiveRootProduct l A u :=
  (rfl)

/-- Coercing the coordinate equivalence to `D.points A` yields the ordered root-subgroup product.
-/
@[simp]
theorem coe_positiveRootEquiv_apply (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A]
    (u : PositiveRoot → A) :
    (D.positiveRootEquiv l hl hcover A u : D.points A) =
      (l.map fun γ => D.rootSubgroupPoints γ.val A (ofAdd (u γ))).prod :=
  (rfl)

/-- Extracting coordinates from an ordered positive-root product recovers its parameters. -/
@[simp]
theorem positiveRootEquiv_symm_positiveRootProduct
    (l : List PositiveRoot) (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    (A : Type v) [CommRing A] (u : PositiveRoot → A) :
    (D.positiveRootEquiv l hl hcover A).symm (D.positiveRootProduct l A u) = u :=
  (D.positiveRootEquiv l hl hcover A).symm_apply_apply u

/-- Multiplying the extracted positive-root coordinates reproduces the original positive point. -/
@[simp]
theorem positiveRootProduct_positiveRootEquiv_symm
    (l : List PositiveRoot) (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    (A : Type v) [CommRing A] (g : D.positivePoints A) :
    D.positiveRootProduct l A ((D.positiveRootEquiv l hl hcover A).symm g) = g :=
  (D.positiveRootEquiv l hl hcover A).apply_symm_apply g

/-- Ring homomorphisms commute with `positiveRootEquiv` on positive datum points. -/
@[simp]
theorem map_positiveRootEquiv (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (u : PositiveRoot → A) :
    D.mapPositivePoints f (D.positiveRootEquiv l hl hcover A u) =
      D.positiveRootEquiv l hl hcover B (f ∘ u) :=
  D.map_positiveRootProduct l f u

/-- Extracting coordinates after scalar change applies the ring map coordinatewise. In
particular, coordinates are natural even under reduction modulo a prime. -/
@[simp]
theorem positiveRootEquiv_symm_map (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (g : D.positivePoints A) :
    (D.positiveRootEquiv l hl hcover B).symm (D.mapPositivePoints f g) =
      fun γ => f ((D.positiveRootEquiv l hl hcover A).symm g γ) := by
  rw [(D.positiveRootEquiv l hl hcover B).symm_apply_eq]
  exact (congrArg (D.mapPositivePoints f)
    ((D.positiveRootEquiv l hl hcover A).apply_symm_apply g)).symm.trans
    (D.map_positiveRootEquiv l hl hcover f ((D.positiveRootEquiv l hl hcover A).symm g))

/-- Zero positive-root coordinates map to the identity element of `D.positivePoints A`. -/
@[simp]
theorem positiveRootEquiv_zero (l : List PositiveRoot) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    D.positiveRootEquiv l hl hcover A 0 = 1 :=
  D.positiveRootProduct_zero l A

/-- The identity element of `D.positivePoints A` has all positive-root coordinates equal to zero.
-/
@[simp]
theorem positiveRootEquiv_symm_one (l : List PositiveRoot) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    (D.positiveRootEquiv l hl hcover A).symm 1 = 0 :=
  (D.positiveRootEquiv l hl hcover A).symm_apply_eq.mpr
    (D.positiveRootEquiv_zero l hl hcover A).symm

/-- Over a finite commutative ring, the positive point subgroup of a Chevalley datum is finite. -/
instance finite_positivePoints (A : Type v) [CommRing A] [Finite A] :
    Finite (D.positivePoints A) := by
  classical
  let l : List PositiveRoot := (Finset.univ : Finset PositiveRoot).toList
  have hl : l.Nodup := Finset.nodup_toList _
  have hcover : ∀ γ, γ ∈ l := fun γ => Finset.mem_toList.mpr (Finset.mem_univ γ)
  exact Finite.of_equiv _ (D.positiveRootEquiv l hl hcover A)

/-- The cardinality of the positive point subgroup of a Chevalley datum is `|A| ^ |Φ⁺|` over every
commutative ring `A`. -/
theorem card_positivePoints (A : Type v) [CommRing A] :
    Nat.card (D.positivePoints A) =
      Nat.card A ^ (posRoots (t.rationalRootSystem ht) (t.rationalBase ht)).ncard := by
  classical
  let l : List PositiveRoot := (Finset.univ : Finset PositiveRoot).toList
  have hl : l.Nodup := Finset.nodup_toList _
  have hcover : ∀ γ, γ ∈ l := fun γ => Finset.mem_toList.mpr (Finset.mem_univ γ)
  rw [Nat.card_congr (D.positiveRootEquiv l hl hcover A).symm, Nat.card_fun, Nat.card_coe_set_eq]

end TauCeti.DynkinType.ChevalleyDatum
