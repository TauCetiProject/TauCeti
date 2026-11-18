/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Basic
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.NotG2
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.G2

/-!
# Positive-root products

For every Chevalley datum, every element of the positive-root subgroup is a product
with one factor from each positive root subgroup, in any enumeration without repetition.
This works on the admissible lattice over every commutative value ring. It is the existence
part of positive-root coordinates, not their uniqueness or a point-generation theorem for the
whole Chevalley group.

The proof combines the general collection theorem outside G₂ with the native six-root
collection theorem in G₂. Neither case requires any structure constant to be invertible.

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
  rw [D.positiveSubgroup_eq_iSup]
  by_cases htG2 : t = G2
  · subst t
    let f (γ : Fin G2.numRoots) : Fin 6 := if h : γ.val < 6 then ⟨γ.val, h⟩ else 0
    have hf (γ : Fin G2.numRoots) (hγ : γ ∈ l) : Fin.castAdd 6 (f γ) = γ := by
      have h := (mem_posRoots_rational_g2_iff ht γ).mp ((hcover γ).mp hγ)
      simp only [f, dite_eq_left h]
      -- G2.numRoots unfolds to 6 + 6; the cast preserves the underlying value.
      exact Fin.ext rfl
    have hnodup : (l.map f).Nodup := hl.map_on fun γ hγ δ hδ heq =>
      (hf γ hγ).symm.trans ((congrArg (Fin.castAdd 6) heq).trans (hf δ hδ))
    have hall (i : Fin 6) : i ∈ l.map f := by
      have hi : Fin.castAdd 6 i ∈ l := (hcover _).mpr
        ((mem_posRoots_rational_g2_iff ht _).mpr i.isLt)
      exact List.mem_map.mpr ⟨_, hi, Fin.castAdd_injective 6 6 (hf _ hi)⟩
    rw [mem_biSup_posRoots_g2_iff_exists_list_prod_map D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator A
      (l.map f) hnodup hall g]
    have hprod (u : Fin 6 → A) (w : Fin G2.numRoots → A)
        (hw : ∀ γ ∈ l, u (f γ) = w γ) :
        ((l.map f).map fun i => chevalleyRootSubgroup D.representation D.lattice
          D.representation_mem_lattice D.isNilpotent_representation_rootGenerator
            (Fin.castAdd 6 i) A (Multiplicative.ofAdd (u i))).prod =
        (l.map fun γ => chevalleyRootSubgroup D.representation D.lattice
          D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ A
            (Multiplicative.ofAdd (w γ))).prod := by
      simp only [List.map_map, Function.comp_def]
      congr 1
      exact List.map_congr_left fun γ hγ => by rw [hf γ hγ, hw γ hγ]
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨fun γ => u (f γ), (hprod u _ (fun _ _ => rfl)).symm.trans hu⟩
    · rintro ⟨u, hu⟩
      exact ⟨fun i => u (Fin.castAdd 6 i),
        (hprod _ u (fun γ hγ => congrArg u (hf γ hγ))).trans hu⟩
  · have := isNotG2_rationalRootSystem_of_ne_G2 (ht := ht) htG2
    exact mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_list_prod
      D.representation D.lattice D.representation_mem_lattice
      D.isNilpotent_representation_rootGenerator A l hl hcover g

end TauCeti.DynkinType.ChevalleyDatum
