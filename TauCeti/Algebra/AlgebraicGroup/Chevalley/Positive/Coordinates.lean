/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Collection
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct

/-!
# Positive-root coordinates in Chevalley groups

For every Chevalley datum `D` of every valid Dynkin type, multiplication of the positive root
subgroups in any order without repetitions is a bijection onto the positive point subgroup
`D.positivePoints A` over every commutative ring `A` — including nonreduced rings and fields of
bad characteristic. The parameters are indexed only by positive roots: there are no unused
coordinates at negative roots. The resulting equivalence `ChevalleyDatum.positiveRootEquiv` and its
inverse commute with arbitrary ring homomorphisms, including noninjective ones.

Existence of ordered-product parameters combines the uniform collection theorem
`ChevalleyDatum.mem_positiveSubgroup_iff_exists_prod` across all Dynkin types with the matrix
realization of `D.positivePoints A`. Uniqueness uses the integral ordered-product theorem
`ChevalleyDatum.list_prod_map_rootSubgroupPoints_inj`. Together they furnish canonical coordinates
on the positive unipotent factor in Bruhat and big-cell decompositions, without identifying the
ambient point group with its elementary subgroup or asserting a scheme-theoretic isomorphism.

## Main declarations

* `TauCeti.DynkinType.ChevalleyDatum.positiveRootProduct`: ordered multiplication of positive-root
  parameters into `D.positivePoints A`.
* `TauCeti.DynkinType.ChevalleyDatum.positiveRootProduct_surjective` and
  `TauCeti.DynkinType.ChevalleyDatum.positiveRootProduct_injective`: surjectivity and injectivity
  for any duplicate-free enumeration of the positive roots over any commutative ring.
* `TauCeti.DynkinType.ChevalleyDatum.mem_positivePoints_iff_existsUnique_prod`: membership in
  `D.positivePoints A` is equivalent to a unique ordered positive-root factorization.
* `TauCeti.DynkinType.ChevalleyDatum.positiveRootEquiv`: the coordinate bijection
  `(PositiveRoot → A) ≃ D.positivePoints A`, natural under ring maps via
  `TauCeti.DynkinType.ChevalleyDatum.positiveRootEquiv_symm_map`.

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

/-- Every positive point of any Chevalley datum has coordinates in any duplicate-free enumeration
of all positive roots, over any commutative ring. -/
theorem positiveRootProduct_surjective (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    Function.Surjective (D.positiveRootProduct l A) := by
  intro g
  obtain ⟨q, hq, hmatrix⟩ := (D.mem_positivePoints_iff).mp g.2
  have hroots : ∀ γ, γ ∈ l.map Subtype.val ↔
      γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    intro γ
    constructor
    · rintro hγ
      obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hγ
      exact γ.2
    · intro hγ
      exact List.mem_map.mpr ⟨⟨γ, hγ⟩, hcover _, rfl⟩
  obtain ⟨u, hu⟩ := (D.mem_positiveSubgroup_iff_exists_prod
    (l.map Subtype.val) (hl.map Subtype.val_injective) hroots (CommAlgCat.of ℤ A) q).mp hq
  refine ⟨fun γ => (u γ.1).toAdd, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have h := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom) hu
  simpa only [map_list_prod, List.map_map, Function.comp_def,
    coe_positiveRootProduct, SubmonoidClass.coe_list_prod,
    coe_rootSubgroupPoints, ofAdd_toAdd, MulEquiv.toMonoidHom_eq_coe, hmatrix] using h

/-- For every Chevalley datum, an ordered enumeration of all positive roots without repetitions
gives an injective parameter map over any commutative ring. -/
theorem positiveRootProduct_injective (l : List PositiveRoot) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    Function.Injective (D.positiveRootProduct l A) := by
  classical
  intro u v huv
  let extend := fun (u : PositiveRoot → A) (γ : Fin t.numRoots) =>
    if h : γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) then u ⟨γ, h⟩ else 0
  have heq := congrArg (fun g : D.positivePoints A => (g : D.points A)) huv
  have hprod (u : PositiveRoot → A) :
      ((l.map Subtype.val).map fun γ => D.rootSubgroupPoints γ A
        (ofAdd (extend u γ))).prod = (D.positiveRootProduct l A u : D.points A) := by
    simp only [coe_positiveRootProduct, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro γ _
    simp only [extend, dite_eq_left γ.2]
  have hparams := (D.list_prod_map_rootSubgroupPoints_inj A
    (hl.map Subtype.val_injective)
    (by rintro γ hγ; obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hγ; exact γ.2)).mp
      ((hprod u).trans (heq.trans (hprod v).symm))
  funext γ
  simpa only [extend, dite_eq_left γ.2] using
    hparams γ.1 (List.mem_map.mpr ⟨γ, hcover γ, rfl⟩)

/-- A datum point belongs to `D.positivePoints A` if and only if it admits a unique expression as
an ordered product of positive-root elements in the prescribed order `l`. -/
theorem mem_positivePoints_iff_existsUnique_prod (l : List PositiveRoot) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] (g : D.points A) :
    g ∈ D.positivePoints A ↔ ∃! u : PositiveRoot → A,
      (l.map fun γ => D.rootSubgroupPoints γ.1 A (ofAdd (u γ))).prod = g := by
  constructor
  · intro hg
    obtain ⟨u, hu⟩ := D.positiveRootProduct_surjective l hl hcover A ⟨g, hg⟩
    refine ⟨u, congrArg Subtype.val hu, fun v hv => ?_⟩
    exact D.positiveRootProduct_injective l hl hcover A
      (Subtype.ext (hv.trans (congrArg Subtype.val hu).symm))
  · rintro ⟨u, rfl, _⟩
    exact (D.positiveRootProduct l A u).2

/-- Positive-root coordinates for any Chevalley datum over an arbitrary commutative ring.
The list enumerates all positive roots in any fixed order without repetitions. -/
noncomputable def positiveRootEquiv (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    (PositiveRoot → A) ≃ D.positivePoints A :=
  Equiv.ofBijective (D.positiveRootProduct l A)
    ⟨D.positiveRootProduct_injective l hl hcover A,
      D.positiveRootProduct_surjective l hl hcover A⟩

/-- The coordinate equivalence multiplies the given root parameters in the specified order. -/
@[simp]
theorem positiveRootEquiv_apply (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A]
    (u : PositiveRoot → A) :
    D.positiveRootEquiv l hl hcover A u = D.positiveRootProduct l A u :=
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

/-- Extracting coordinates after scalar change applies the ring map coordinatewise, even when the
ring map is not injective. -/
@[simp]
theorem positiveRootEquiv_symm_map (l : List PositiveRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (g : D.positivePoints A) :
    (D.positiveRootEquiv l hl hcover B).symm
        ⟨(D.pointsPresentation A).map (D.pointsPresentation B) f (g : D.points A),
          D.map_positivePoints_le f (Subgroup.mem_map.mpr ⟨g, g.2, rfl⟩)⟩ =
      fun γ => f ((D.positiveRootEquiv l hl hcover A).symm g γ) := by
  apply (D.positiveRootEquiv l hl hcover B).injective
  simp only [Equiv.apply_symm_apply, positiveRootEquiv_apply]
  apply Subtype.ext
  rw [← D.map_positiveRootProduct l f]
  exact congrArg ((D.pointsPresentation A).map (D.pointsPresentation B) f)
    (congrArg Subtype.val ((D.positiveRootEquiv l hl hcover A).apply_symm_apply g).symm)

end TauCeti.DynkinType.ChevalleyDatum
