/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Collection
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct

/-!
# Positive-root coordinates in simply laced full-weight Chevalley groups

For the full-weight Chevalley datum of a simply laced type, multiplication of the positive
root subgroups in any order without repetitions is a bijection onto the positive point
subgroup over every commutative ring. The parameters are indexed only by positive roots:
there are no unused coordinates at negative roots. The resulting equivalence and its inverse
commute with changes of the value ring, including noninjective ring maps.

This combines the collection theorem
`ChevalleyDatum.mem_positiveSubgroup_iff_exists_prod_of_isSimplyLaced` with the integral
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
  ⟨(l.map fun γ => D.rootSubgroupPoints γ.1 A (ofAdd (u γ))).prod,
    Subgroup.list_prod_mem _ fun _ hg => by
      obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hg
      exact D.rootSubgroupPoints_mem_positivePoints A γ.2 _⟩

/-- The positive-root product has the stated ordered factors in the datum point group. -/
@[simp]
theorem coe_positiveRootProduct (l : List PositiveRoot) (A : Type v) [CommRing A]
    (u : PositiveRoot → A) :
    (D.positiveRootProduct l A u : D.points A) =
      (l.map fun γ => D.rootSubgroupPoints γ.1 A (ofAdd (u γ))).prod :=
  (rfl)

/-- The empty positive-root product is the identity. -/
@[simp]
theorem positiveRootProduct_nil (A : Type v) [CommRing A] (u : PositiveRoot → A) :
    D.positiveRootProduct [] A u = 1 := by
  apply Subtype.ext
  simp

/-- Zero parameters give the identity positive point. -/
@[simp]
theorem positiveRootProduct_zero (l : List PositiveRoot) (A : Type v) [CommRing A] :
    D.positiveRootProduct l A 0 = 1 := by
  apply Subtype.ext
  simp

/-- Prepending a root prepends its root-subgroup factor. -/
theorem positiveRootProduct_cons (γ : PositiveRoot) (l : List PositiveRoot)
    (A : Type v) [CommRing A] (u : PositiveRoot → A) :
    D.positiveRootProduct (γ :: l) A u =
      ⟨D.rootSubgroupPoints γ.1 A (ofAdd (u γ)),
        D.rootSubgroupPoints_mem_positivePoints A γ.2 _⟩ * D.positiveRootProduct l A u := by
  apply Subtype.ext
  simp

/-- Concatenating lists multiplies their positive-root products in the same order. -/
theorem positiveRootProduct_append (l₁ l₂ : List PositiveRoot)
    (A : Type v) [CommRing A] (u : PositiveRoot → A) :
    D.positiveRootProduct (l₁ ++ l₂) A u =
      D.positiveRootProduct l₁ A u * D.positiveRootProduct l₂ A u := by
  apply Subtype.ext
  simp

/-- Only parameters at roots occurring in the list affect the product. -/
theorem positiveRootProduct_congr (l : List PositiveRoot) (A : Type v) [CommRing A]
    {u v : PositiveRoot → A} (h : ∀ γ ∈ l, u γ = v γ) :
    D.positiveRootProduct l A u = D.positiveRootProduct l A v := by
  apply Subtype.ext
  simp only [coe_positiveRootProduct]
  exact congrArg List.prod (List.map_congr_left fun γ hγ => by rw [h γ hγ])

/-- A parameter supported at one root in a duplicate-free list gives that root element. -/
theorem positiveRootProduct_single (l : List PositiveRoot) (hl : l.Nodup)
    (A : Type v) [CommRing A] (γ : PositiveRoot) (hγ : γ ∈ l) (u : A) :
    D.positiveRootProduct l A (Pi.single γ u) =
      ⟨D.rootSubgroupPoints γ.1 A (ofAdd u),
        D.rootSubgroupPoints_mem_positivePoints A γ.2 _⟩ := by
  classical
  apply Subtype.ext
  simp only [coe_positiveRootProduct]
  rw [List.prod_map_eq_pow_single γ _ (fun δ hδ _ => by simp [Pi.single_eq_of_ne hδ])]
  rw [@List.count_eq_one_of_mem _ instBEqOfDecidableEq _ γ l hl hγ]
  simp

/-- Changing the value ring applies the ring map to each root coordinate. -/
theorem map_positiveRootProduct (l : List PositiveRoot)
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (u : PositiveRoot → A) :
    (D.pointsPresentation A).map (D.pointsPresentation B) f
        (D.positiveRootProduct l A u : D.points A) =
      (D.positiveRootProduct l B (fun γ => f (u γ)) : D.points B) := by
  simp only [coe_positiveRootProduct, map_list_prod, List.map_map, Function.comp_def,
    D.map_rootSubgroupPoints, toAdd_ofAdd]

/-- Scalar change on positive points applies the ring map to each root coordinate. -/
@[simp]
theorem mapPositivePoints_positiveRootProduct (l : List PositiveRoot)
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (u : PositiveRoot → A) :
    D.mapPositivePoints f (D.positiveRootProduct l A u) =
      D.positiveRootProduct l B (fun γ => f (u γ)) := by
  apply Subtype.ext
  rw [D.coe_mapPositivePoints]
  exact D.map_positiveRootProduct l f u

attribute [local instance high] Algebra.toModule

/-- In a simply laced type, every positive point has coordinates in any enumeration of the
positive roots. No field or reducedness hypothesis is required. -/
theorem positiveRootProduct_surjective (hs : t.IsSimplyLaced) (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    Function.Surjective (D.positiveRootProduct l A) := by
  intro g
  have hg := (D.mem_positivePoints_iff).mp g.2
  obtain ⟨q, hq, hmatrix⟩ := hg
  have hroots : ∀ γ, γ ∈ l.map Subtype.val ↔
      γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    intro γ
    constructor
    · rintro hγ
      obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hγ
      exact γ.2
    · intro hγ
      exact List.mem_map.mpr ⟨⟨γ, hγ⟩, hcover _, rfl⟩
  obtain ⟨u, hu⟩ := (D.mem_positiveSubgroup_iff_exists_prod_of_isSimplyLaced hs
    (l.map Subtype.val) (hl.map Subtype.val_injective) hroots (CommAlgCat.of ℤ A) q).mp hq
  refine ⟨fun γ => (u γ.1).toAdd, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have h := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom) hu
  simpa only [map_list_prod, List.map_map, Function.comp_def,
    coe_positiveRootProduct, SubmonoidClass.coe_list_prod,
    coe_rootSubgroupPoints, ofAdd_toAdd, MulEquiv.toMonoidHom_eq_coe, hmatrix] using h

end TauCeti.DynkinType.ChevalleyDatum

namespace TauCeti.DynkinType

universe v w

variable (t : DynkinType) (ht : t.Valid)

local notation "D" => t.scChevalleyDatum ht
local notation "PositiveRoot" =>
  {γ // γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)}

/-- A duplicate-free positive-root product in the full-weight model determines exactly
its on-list parameters, over an arbitrary commutative ring. -/
theorem scChevalleyDatum_positiveRootProduct_eq_iff (l : List PositiveRoot) (hl : l.Nodup)
    (A : Type v) [CommRing A] {u v : PositiveRoot → A} :
    (D).positiveRootProduct l A u = (D).positiveRootProduct l A v ↔
      ∀ γ ∈ l, u γ = v γ := by
  classical
  constructor
  swap
  · exact (D).positiveRootProduct_congr l A
  intro huv
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
    simp only [extend, dite_eq_left γ.2]
  have hparams := (t.list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj ht A
    (hl.map Subtype.val_injective)
    (by rintro γ hγ; obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hγ; exact γ.2)).mp
      ((hprod u).trans (heq.trans (hprod v).symm))
  intro γ hγ
  simpa only [extend, dite_eq_left γ.2] using
    hparams γ.1 (List.mem_map.mpr ⟨γ, hγ, rfl⟩)

/-- In the full-weight model, an ordered enumeration of all positive roots without repetitions
gives an injective parameter map. The value ring is arbitrary. -/
theorem scChevalleyDatum_positiveRootProduct_injective (l : List PositiveRoot) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    Function.Injective ((D).positiveRootProduct l A) := by
  intro u v huv
  funext γ
  exact (t.scChevalleyDatum_positiveRootProduct_eq_iff ht l hl A).mp huv γ (hcover γ)

/-- Positive-root coordinates for a simply laced full-weight Chevalley datum over an arbitrary
commutative ring. The list enumerates all positive roots, in any order without repetitions. -/
noncomputable def scPositiveRootEquiv (hs : t.IsSimplyLaced) (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    (PositiveRoot → A) ≃ (D).positivePoints A :=
  Equiv.ofBijective ((D).positiveRootProduct l A)
    ⟨t.scChevalleyDatum_positiveRootProduct_injective ht l hl hcover A,
      (D).positiveRootProduct_surjective hs l hl hcover A⟩

/-- The coordinate equivalence multiplies the given root parameters in the specified order. -/
@[simp]
theorem scPositiveRootEquiv_apply (hs : t.IsSimplyLaced) (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A]
    (u : PositiveRoot → A) :
    t.scPositiveRootEquiv ht hs l hl hcover A u = (D).positiveRootProduct l A u :=
  (rfl)

/-- Extracting coordinates from an ordered positive-root product recovers its parameters. -/
@[simp]
theorem scPositiveRootEquiv_symm_positiveRootProduct (hs : t.IsSimplyLaced)
    (l : List PositiveRoot) (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    (A : Type v) [CommRing A] (u : PositiveRoot → A) :
    (t.scPositiveRootEquiv ht hs l hl hcover A).symm ((D).positiveRootProduct l A u) = u :=
  (t.scPositiveRootEquiv ht hs l hl hcover A).symm_apply_apply u

/-- Multiplying the extracted positive-root coordinates reproduces the original positive point. -/
@[simp]
theorem positiveRootProduct_scPositiveRootEquiv_symm (hs : t.IsSimplyLaced)
    (l : List PositiveRoot) (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    (A : Type v) [CommRing A] (g : (D).positivePoints A) :
    (D).positiveRootProduct l A ((t.scPositiveRootEquiv ht hs l hl hcover A).symm g) = g :=
  (t.scPositiveRootEquiv ht hs l hl hcover A).apply_symm_apply g

/-- The identity positive point has zero coordinates. -/
@[simp]
theorem scPositiveRootEquiv_symm_one (hs : t.IsSimplyLaced) (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    (t.scPositiveRootEquiv ht hs l hl hcover A).symm 1 = 0 := by
  rw [← ChevalleyDatum.positiveRootProduct_zero (D) l A,
    scPositiveRootEquiv_symm_positiveRootProduct]

/-- A positive root element has just its one nonzero root coordinate. -/
@[simp]
theorem scPositiveRootEquiv_symm_rootSubgroupPoints (hs : t.IsSimplyLaced)
    (l : List PositiveRoot) (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    (A : Type v) [CommRing A] (γ : PositiveRoot) (u : Multiplicative A) :
    (t.scPositiveRootEquiv ht hs l hl hcover A).symm
        ⟨(D).rootSubgroupPoints γ.1 A u,
          (D).rootSubgroupPoints_mem_positivePoints A γ.2 u⟩ = Pi.single γ u.toAdd := by
  rw [Equiv.symm_apply_eq, scPositiveRootEquiv_apply]
  simpa only [ofAdd_toAdd] using
    ((D).positiveRootProduct_single l hl A γ (hcover γ) u.toAdd).symm

/-- Extracting coordinates after scalar change applies the ring map coordinatewise. In
particular, coordinates are natural even under reduction modulo a prime. -/
-- Simplify before `map_mul` or `map_inv` can split the scalar-change map.
@[simp↓]
theorem scPositiveRootEquiv_symm_mapPositivePoints (hs : t.IsSimplyLaced)
    (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (g : (D).positivePoints A) :
    (t.scPositiveRootEquiv ht hs l hl hcover B).symm
        ((D).mapPositivePoints f g) =
      fun γ => f ((t.scPositiveRootEquiv ht hs l hl hcover A).symm g γ) := by
  apply (t.scPositiveRootEquiv ht hs l hl hcover B).injective
  simp only [Equiv.apply_symm_apply, scPositiveRootEquiv_apply]
  rw [← ChevalleyDatum.mapPositivePoints_positiveRootProduct]
  exact congrArg ((D).mapPositivePoints f)
    ((t.scPositiveRootEquiv ht hs l hl hcover A).apply_symm_apply g).symm

end TauCeti.DynkinType
