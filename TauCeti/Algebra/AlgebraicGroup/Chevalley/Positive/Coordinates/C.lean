/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.NotG2
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.NotG2

/-!
# Positive-root coordinates in type C

For a type-C Chevalley datum in any valid rank, every positive point is an ordered product
of positive root elements. For the simply connected full-weight datum these coordinates are
unique. The ordering may be any list enumerating the positive roots without repetitions.
Parameters are indexed only by positive roots, with no unused coordinates at negative roots.

These are coordinates on the positive subgroup, not a generation theorem for the entire
point group or an identification of the positive subgroup scheme with affine space.
Both results hold over arbitrary commutative rings, including characteristic two and
nonreduced rings.

Existence uses `mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_list_prod`, the integral
collection theorem outside G₂, and the native type-C Cartan bound. Uniqueness uses
`list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj`, whose integral root-operator
faithfulness comes from the fundamental modules rather than an assumption on the value ring.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.3.3.
-/

public section

open TensorProduct TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType

variable {n : ℕ} {hn : (C n).Valid}

attribute [local instance high] Algebra.toModule

/-- Over every commutative ring, a positive point of a type-C Chevalley datum is a product
of positive root elements in any prescribed order without repetitions. -/
theorem ChevalleyDatum.mem_positivePoints_iff_exists_prod_typeC
    (D : ChevalleyDatum (C n) hn)
    (l : List (posRoots ((C n).rationalRootSystem hn) ((C n).rationalBase hn)))
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    (A : Type*) [CommRing A] (g : D.points A) :
    g ∈ D.positivePoints A ↔ ∃ u : posRoots ((C n).rationalRootSystem hn)
        ((C n).rationalBase hn) → A,
      (l.map fun γ => D.rootSubgroupPoints γ.val A (Multiplicative.ofAdd (u γ))).prod = g := by
  classical
  constructor
  · intro hg
    obtain ⟨q, hq, hqg⟩ := Subgroup.mem_map.mp (D.mem_positivePoints_iff.mp hg)
    have hq' : q ∈ ⨆ γ ∈ posRoots ((C n).rationalRootSystem hn) ((C n).rationalBase hn),
        (chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
          D.isNilpotent_representation_rootGenerator γ (CommAlgCat.of ℤ A)).range := by
      let X := fun γ => chevalleyRootSubgroup D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ
          (CommAlgCat.of ℤ A)
      have hjoin : (⨆ γ ∈ posRoots ((C n).rationalRootSystem hn) ((C n).rationalBase hn),
          (X γ).range) = Subgroup.closure
          (⋃ γ ∈ posRoots ((C n).rationalRootSystem hn) ((C n).rationalBase hn),
            Set.range (X γ)) := by
        simp only [← MonoidHom.coe_range, Subgroup.closure_iUnion, Subgroup.closure_eq]
      rw [hjoin]
      convert hq using 1
      rw [D.positiveSubgroup_eq_closure]
      congr 1
      ext x
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_ofPred_eq, exists_prop, X]
    have hlist : ∀ γ, γ ∈ l.map Subtype.val ↔
        γ ∈ posRoots ((C n).rationalRootSystem hn) ((C n).rationalBase hn) := by
      intro γ
      simp only [List.mem_map]
      exact ⟨fun ⟨δ, _, hδ⟩ => hδ ▸ δ.property,
        fun hγ => ⟨⟨γ, hγ⟩, hcover _, rfl⟩⟩
    obtain ⟨u, hu⟩ := (mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_list_prod
      D.representation D.lattice D.representation_mem_lattice
      D.isNilpotent_representation_rootGenerator (CommAlgCat.of ℤ A)
      (l.map Subtype.val) (hl.map Subtype.val_injective) hlist q).mp hq'
    refine ⟨fun γ => u γ.val, Subtype.ext ?_⟩
    have hmatrix := congrArg
      (Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom) hu
    simpa only [map_list_prod, List.map_map, Function.comp_def, Subgroup.val_list_prod,
      D.coe_rootSubgroupPoints, MulEquiv.toMonoidHom_eq_coe] using hmatrix.trans hqg
  · rintro ⟨u, rfl⟩
    exact Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hx
      exact D.rootSubgroupPoints_mem_positivePoints A γ.property _

/-- In the simply connected type-C model, every positive point has exactly one tuple of
positive-root parameters, in any prescribed order without repetitions. No field or
characteristic restriction is required. -/
theorem existsUnique_prod_scChevalleyDatum_rootSubgroupPoints_typeC
    (l : List (posRoots ((C n).rationalRootSystem hn) ((C n).rationalBase hn)))
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    (A : Type*) [CommRing A] (g : ((C n).scChevalleyDatum hn).points A)
    (hg : g ∈ ((C n).scChevalleyDatum hn).positivePoints A) :
    ∃! u : posRoots ((C n).rationalRootSystem hn) ((C n).rationalBase hn) → A,
      (l.map fun γ => ((C n).scChevalleyDatum hn).rootSubgroupPoints γ.val A
        (Multiplicative.ofAdd (u γ))).prod = g := by
  classical
  have hinj : Function.Injective (fun u : posRoots ((C n).rationalRootSystem hn)
      ((C n).rationalBase hn) → A =>
      (l.map fun γ => ((C n).scChevalleyDatum hn).rootSubgroupPoints γ.val A
        (Multiplicative.ofAdd (u γ))).prod) := by
    intro u v huv
    let u' := Function.extend Subtype.val u (fun _ => 0)
    let v' := Function.extend Subtype.val v (fun _ => 0)
    have hprod : ((l.map Subtype.val).map fun γ =>
        ((C n).scChevalleyDatum hn).rootSubgroupPoints γ A
          (Multiplicative.ofAdd (u' γ))).prod =
      ((l.map Subtype.val).map fun γ =>
        ((C n).scChevalleyDatum hn).rootSubgroupPoints γ A
          (Multiplicative.ofAdd (v' γ))).prod := by
      simpa only [List.map_map, Function.comp_def, u', v', Subtype.val_injective.extend_apply]
        using huv
    have heq := ((C n).list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj hn A
      (hl.map Subtype.val_injective)
      (fun γ hγ => by
        obtain ⟨δ, _, rfl⟩ := List.mem_map.mp hγ
        exact δ.property)).mp hprod
    funext γ
    simpa only [u', v', Subtype.val_injective.extend_apply] using
      heq γ.val (List.mem_map.mpr ⟨γ, hcover γ, rfl⟩)
  exact hinj.existsUnique_iff_exists.mpr
    ((((C n).scChevalleyDatum hn).mem_positivePoints_iff_exists_prod_typeC
      l hl hcover A g).mp hg)

end TauCeti.DynkinType
