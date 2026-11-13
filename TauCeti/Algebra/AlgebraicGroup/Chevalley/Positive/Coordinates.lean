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
    simp only [extend, dite_eq_left γ.2]
  have hparams := (t.list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj ht A
    (hl.map Subtype.val_injective)
    (by rintro γ hγ; obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hγ; exact γ.2)).mp
      ((hprod u).trans (heq.trans (hprod v).symm))
  funext γ
  simpa only [extend, dite_eq_left γ.2] using
    hparams γ.1 (List.mem_map.mpr ⟨γ, hcover γ, rfl⟩)

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

/-- Extracting coordinates after scalar change applies the ring map coordinatewise. In
particular, coordinates are natural even under reduction modulo a prime. -/
@[simp]
theorem scPositiveRootEquiv_symm_map (hs : t.IsSimplyLaced) (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (g : (D).positivePoints A) :
    (t.scPositiveRootEquiv ht hs l hl hcover B).symm
        ⟨((D).pointsPresentation A).map ((D).pointsPresentation B) f (g : (D).points A),
          (D).map_positivePoints_le f (Subgroup.mem_map.mpr ⟨g, g.2, rfl⟩)⟩ =
      fun γ => f ((t.scPositiveRootEquiv ht hs l hl hcover A).symm g γ) := by
  apply (t.scPositiveRootEquiv ht hs l hl hcover B).injective
  simp only [Equiv.apply_symm_apply, scPositiveRootEquiv_apply]
  apply Subtype.ext
  rw [← (D).map_positiveRootProduct l f]
  exact congrArg (((D).pointsPresentation A).map ((D).pointsPresentation B) f)
    (congrArg Subtype.val
      ((t.scPositiveRootEquiv ht hs l hl hcover A).apply_symm_apply g).symm)

end TauCeti.DynkinType
