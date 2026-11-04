/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.GraphAutomorphism
public import TauCeti.LinearAlgebra.RootSystem.Positive
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Basic
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Hom

/-!
# Positive-root order on type-D spin weights

A path of positive simple-root moves joins two spin weights exactly when their difference
lies in the integral positive root cone. The full spin weight family has two reflection
orbits. Lengths agree within each orbit by reflection invariance, and between the orbits
by the fork-exchange automorphism. Thus the equal-length raising-path criterion applies
to the full family without assuming a parity condition on the endpoints.

These paths propagate weight lines in representations of the positive spin subgroup and
constrain invariant flags of its connected solvable overgroups.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* W. Fulton and J. Harris, *Representation Theory*, §20.2.

The path argument follows
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.MinusculeWeight.Positive`;
the two half-spin orbits require the additional graph-automorphism comparison here.
-/

public section

namespace TauCeti.DynkinType

open scoped BigOperators

variable {n : ℕ} (hn : 4 ≤ n)

local notation "P" => typeDSimplyConnectedRootDatum n hn
local notation "μ" => typeDSpinWeight (n := n)

/-- A positive simple-root move on the sign sets indexing the full type-D spin module. -/
def TypeDSpinRaisingStep (s t : Finset (Fin n)) : Prop :=
  ∃ i : Fin n, μ s i = -1 ∧ typeDSpinReflection i s = t

/-- A raising move is simple reflection at a coroot value of minus one. -/
theorem typeDSpinRaisingStep_iff (s t : Finset (Fin n)) :
    TypeDSpinRaisingStep s t ↔
      ∃ i : Fin n, μ s i = -1 ∧ typeDSpinReflection i s = t := Iff.rfl

/-- The positive root cone in the numbered simple-root coordinates of type D. -/
theorem mem_typeD_posRootCone_iff {x : Fin n → ℤ} :
    x ∈ posRootCone P (typeDSimplyConnectedBase n hn) ↔
      ∃ c : Fin n → ℕ, x = ∑ i, c i • (P).root (typeDSimpleIndex n hn i) := by
  have he : Set.BijOn (typeDSimpleIndex n hn) Set.univ
      (typeDSimplyConnectedBase n hn).support :=
    ⟨fun i _ ↦ by simp, (typeDSimpleIndex_injective hn).injOn, fun j hj ↦ by
      refine ⟨⟨j, (mem_typeDSimplyConnectedBase_support hn).mp hj⟩, trivial, ?_⟩
      exact Fin.ext (by simp [typeDSimpleIndex_val])⟩
  exact mem_posRootCone_iff_exists_nat_of_bijOn P (typeDSimplyConnectedBase n hn) he

private theorem rootForm_eq_of_parity (s t : Finset (Fin n))
    (hpar : Even s.card ↔ Even t.card) :
    (P).RootForm (μ s) (μ s) = (P).RootForm (μ t) (μ t) := by
  obtain ⟨l, rfl⟩ := (exists_typeDSpinReflections_eq_iff (by omega) s t).mpr hpar
  suffices ∀ (l : List (Fin n)) (s : Finset (Fin n)),
      (P).RootForm (μ (l.foldl (fun u i ↦ typeDSpinReflection i u) s))
        (μ (l.foldl (fun u i ↦ typeDSpinReflection i u) s)) = (P).RootForm (μ s) (μ s) from
    (this l s).symm
  intro l
  induction l with
  | nil => intro s; rfl
  | cons i l ih =>
    intro s
    rw [List.foldl_cons, ih, ← typeDSimplyConnectedRootDatum_reflection_typeDSpinWeight hn]
    exact (P).rootForm_reflection_reflection_apply _ _ _

/-- All full-spin weights have the same canonical root-form length, including weights in
opposite half-spin parity classes. -/
theorem rootForm_typeDSpinWeight_eq (s t : Finset (Fin n)) :
    (P).RootForm (μ s) (μ s) = (P).RootForm (μ t) (μ t) := by
  by_cases hpar : Even s.card ↔ Even t.card
  · exact rootForm_eq_of_parity hn s t hpar
  · have hpar' : Even s.card ↔ Even (typeDSpinGraphPerm n (by omega) t).card := by
      rw [even_card_typeDSpinGraphPerm_iff, ← Nat.not_even_iff_odd]
      tauto
    calc
      _ = (P).RootForm (μ (typeDSpinGraphPerm n (by omega) t))
          (μ (typeDSpinGraphPerm n (by omega) t)) := rootForm_eq_of_parity hn _ _ hpar'
      _ = _ := by
        rw [← typeDGraphAut_weightMap_typeDSpinWeight hn]
        exact (typeDGraphAut n hn).toHom.rootForm_weightMap _ _

/-- Positive simple-root paths are exactly positive integral differences of full-spin weights.
No parity assumption is needed: membership in the cone already forces the appropriate orbit. -/
theorem typeDSpin_raisingPath_iff_mem_posRootCone (s t : Finset (Fin n)) :
    Relation.ReflTransGen TypeDSpinRaisingStep s t ↔
      μ t - μ s ∈ posRootCone P (typeDSimplyConnectedBase n hn) := by
  constructor
  · intro h
    induction h with
    | refl => simp
    | @tail t u _ htu ih =>
      obtain ⟨i, hi, rfl⟩ := (typeDSpinRaisingStep_iff _ _).mp htu
      have hroot : (P).root (typeDSimpleIndex n hn i) ∈
          posRootCone P (typeDSimplyConnectedBase n hn) := by
        exact root_mem_posRootCone_of_mem_posRoots P (typeDSimplyConnectedBase n hn)
          (support_subset_posRoots P (typeDSimplyConnectedBase n hn) (by simp))
      have heq : μ (typeDSpinReflection i t) - μ s =
          (μ t - μ s) + (P).root (typeDSimpleIndex n hn i) := by
        rw [typeDSpinWeight_typeDSpinReflection hn, hi, root_typeDSimpleIndex hn]
        simp only [neg_smul, one_smul, sub_neg_eq_add]
        abel
      rw [heq]
      exact (posRootCone P (typeDSimplyConnectedBase n hn)).add_mem ih hroot
  · intro h
    obtain ⟨c, hc⟩ := (mem_typeD_posRootCone_iff hn).mp h
    refine (P).toInvariantForm.reflTransGen_of_sub_eq_sum
      (fun _ hv hne ↦ (P).rootForm_pos_of_ne_zero hv hne)
      typeDSpinWeight_injective (rootForm_typeDSpinWeight_eq hn)
      (f := typeDSimpleIndex n hn) (fun s i hi ↦ ?_) hc
    have hai : μ s i = -1 := by
      have hpair : (P).coroot' (typeDSimpleIndex n hn i) (μ s) = μ s i := by
        simp [RootPairing.coroot', toLinearMap_typeDSimplyConnectedRootDatum]
      rw [hpair] at hi
      rcases typeDSpinWeight_apply_eq_neg_one_or_eq_zero_or_eq_one s i with h | h | h <;> omega
    refine ⟨typeDSpinReflection i s, ⟨i, hai, rfl⟩, ?_⟩
    rw [typeDSpinWeight_typeDSpinReflection hn, hai, root_typeDSimpleIndex hn]
    simp

end TauCeti.DynkinType
