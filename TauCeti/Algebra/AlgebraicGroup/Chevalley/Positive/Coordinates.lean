/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.NotG2
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.NotG2

/-!
# Positive-root coordinates outside G₂

Every positive point of a Chevalley datum whose rational root system satisfies `IsNotG2`
has a product expression with one additive parameter per positive root, in any prescribed
order without repetitions. For the full-weight simply connected datum these parameters are
unique over every commutative ring, including characteristic two and nonreduced rings.
Parameters are indexed only by the positive roots; no unused negative-root coordinates are carried.

These are coordinates on the positive subgroup, as needed for Bruhat normal forms and the
unipotent factors of the big cell. They assert neither generation of all scheme points nor
a scheme-theoretic product isomorphism. Existence uses the integral collection theorem
`mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_list_prod`; uniqueness uses
`list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.3.3.
-/

public section

namespace TauCeti.DynkinType

open TensorProduct TauCeti.UniversalEnvelopingAlgebra

attribute [local instance high] Algebra.toModule

variable {t : DynkinType} {ht : t.Valid} [(t.rationalRootSystem ht).IsNotG2]

namespace ChevalleyDatum

variable (D : ChevalleyDatum t ht)

/-- Outside G₂, a datum point is positive exactly when it is a product of its positive root
subgroups, in any order containing every positive root exactly once. Existence holds for every
Chevalley datum and every commutative value ring. -/
theorem mem_positivePoints_iff_exists_prod (A : Type*) [CommRing A]
    {l : List (posRoots (t.rationalRootSystem ht) (t.rationalBase ht))}
    (hl : l.Nodup) (hall : ∀ γ, γ ∈ l) (g : D.points A) :
    g ∈ D.positivePoints A ↔
      ∃ u : posRoots (t.rationalRootSystem ht) (t.rationalBase ht) → A,
        (l.map fun γ => D.rootSubgroupPoints γ.1 A (Multiplicative.ofAdd (u γ))).prod = g := by
  constructor
  · intro hg
    obtain ⟨x, hx, hxg⟩ := (D.mem_positivePoints_iff.mp hg)
    rw [D.positiveSubgroup_eq_iSup] at hx
    have hcover : ∀ γ, γ ∈ l.map Subtype.val ↔
        γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
      intro γ
      constructor
      · rintro hγ
        obtain ⟨δ, _, rfl⟩ := List.mem_map.mp hγ
        exact δ.property
      · intro hγ
        exact List.mem_map.mpr ⟨⟨γ, hγ⟩, hall ⟨γ, hγ⟩, rfl⟩
    obtain ⟨u, hu⟩ := (mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_list_prod
      D.representation D.lattice D.representation_mem_lattice
      D.isNilpotent_representation_rootGenerator (CommAlgCat.of ℤ A)
      (l.map Subtype.val) (hl.map Subtype.val_injective) hcover x).mp hx
    refine ⟨fun γ => u γ.1, ?_⟩
    apply (D.points A).subtype_injective
    have hmatrix := congrArg
      (Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMulEquiv.toMonoidHom) hu
    simp only [map_list_prod, List.map_map, Function.comp_def]
    calc
      _ = (l.map fun γ => Units.map
          (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMulEquiv.toMonoidHom
          (chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
            D.isNilpotent_representation_rootGenerator γ.1
            (CommAlgCat.of ℤ A) (Multiplicative.ofAdd (u γ.1)))).prod :=
        congrArg List.prod (List.map_congr_left fun γ _ => D.coe_rootSubgroupPoints _ A _)
      _ = _ := by
        simp only [map_list_prod, List.map_map, Function.comp_def] at hmatrix
        -- Reconcile the ring and endomorphism monoid instances on lattice automorphisms.
        convert hmatrix.trans hxg using 1
        rfl
  · rintro ⟨u, rfl⟩
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hx
    exact D.rootSubgroupPoints_mem_positivePoints A γ.property _

end ChevalleyDatum

/-- Outside G₂, in the full-weight simply connected datum, every positive point has exactly one
positive-root parameter tuple in any prescribed duplicate-free order. No characteristic or
reducedness hypothesis is needed. -/
theorem mem_scChevalleyDatum_positivePoints_iff_existsUnique_prod (A : Type*) [CommRing A]
    {l : List (posRoots (t.rationalRootSystem ht) (t.rationalBase ht))}
    (hl : l.Nodup) (hall : ∀ γ, γ ∈ l) (g : (t.scChevalleyDatum ht).points A) :
    g ∈ (t.scChevalleyDatum ht).positivePoints A ↔
      ∃! u : posRoots (t.rationalRootSystem ht) (t.rationalBase ht) → A,
        (l.map fun γ => (t.scChevalleyDatum ht).rootSubgroupPoints γ.1 A
          (Multiplicative.ofAdd (u γ))).prod = g := by
  classical
  have hinj : Function.Injective
      (fun u : posRoots (t.rationalRootSystem ht) (t.rationalBase ht) → A =>
        (l.map fun γ => (t.scChevalleyDatum ht).rootSubgroupPoints γ.1 A
          (Multiplicative.ofAdd (u γ))).prod) := by
    intro u v huv
    let U := Function.extend Subtype.val u (fun _ => (0 : A))
    let V := Function.extend Subtype.val v (fun _ => (0 : A))
    have hprod : ((l.map Subtype.val).map fun γ => (t.scChevalleyDatum ht).rootSubgroupPoints
        γ A (Multiplicative.ofAdd (U γ))).prod =
        ((l.map Subtype.val).map fun γ => (t.scChevalleyDatum ht).rootSubgroupPoints
          γ A (Multiplicative.ofAdd (V γ))).prod := by
      simpa only [List.map_map, Function.comp_def, U, V, Subtype.val_injective.extend_apply]
        using huv
    have hparams := (t.list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj ht A
      (hl.map Subtype.val_injective) (by
        intro γ hγ
        obtain ⟨δ, _, rfl⟩ := List.mem_map.mp hγ
        exact δ.property)).mp hprod
    funext γ
    simpa only [U, V, Subtype.val_injective.extend_apply] using
      hparams γ.1 (List.mem_map.mpr ⟨γ, hall γ, rfl⟩)
  rw [(t.scChevalleyDatum ht).mem_positivePoints_iff_exists_prod A hl hall g]
  exact hinj.existsUnique_iff_exists.symm

end TauCeti.DynkinType
