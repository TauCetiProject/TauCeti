/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Basic
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.Basic

/-!
# Positive-root products

For every Chevalley datum, every element of the positive-root subgroup is a product
with one factor from each positive root subgroup, in any enumeration without repetition.
This works on the admissible lattice over every commutative value ring. It is the existence
part of positive-root coordinates, not their uniqueness or a point-generation theorem for the
whole Chevalley group.

The proof uses the lattice-level collection theorem
`mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_prod`, which does not require any
structure constant to be invertible.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* R. W. Carter, *Simple Groups of Lie Type*, §5.3.
-/

public section

open TensorProduct TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

attribute [local instance high] Algebra.toModule

/-- Every element of the positive subgroup has a root-product expression.
The list enumerates all positive roots without repetition, in any order; no field or
characteristic restriction is needed. -/
theorem mem_positiveSubgroup_iff_exists_prod
    (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : CommAlgCat.{v} ℤ)
    (g : LinearMap.GeneralLinearGroup A (A ⊗[ℤ] D.lattice)) :
    g ∈ D.positiveSubgroup A ↔ ∃ u : Fin t.numRoots → A,
      (l.map fun γ => chevalleyRootSubgroup D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ A
          (Multiplicative.ofAdd (u γ))).prod = g := by
  classical
  let lpos := l.attachWith _ fun γ hγ => (hcover γ).mp hγ
  have hval : lpos.map Subtype.val = l := List.attachWith_map_subtype_val _
  have hnodup : lpos.Nodup := List.Nodup.of_map Subtype.val (hval.symm ▸ hl)
  have hall (γ : posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) : γ ∈ lpos :=
    (List.mem_attachWith _ γ).mpr ((hcover γ.val).mpr γ.property)
  rw [D.positiveSubgroup_eq_iSup, mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_prod
    D.representation D.lattice D.representation_mem_lattice
    D.isNilpotent_representation_rootGenerator A lpos hnodup hall g]
  constructor
  · rintro ⟨u, hu⟩
    let extend (γ : Fin t.numRoots) :=
      if h : γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) then u ⟨γ, h⟩ else 0
    refine ⟨extend, ?_⟩
    rw [← hval, List.map_map]
    refine (congrArg List.prod (List.map_congr_left fun γ _ => ?_)).trans hu
    simp only [Function.comp_def, extend, dite_eq_left γ.property]
  · rintro ⟨u, hu⟩
    rw [← hval, List.map_map] at hu
    exact ⟨fun γ => u γ.val, hu⟩

end TauCeti.DynkinType.ChevalleyDatum
