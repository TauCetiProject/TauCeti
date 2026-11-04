/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.TripledWeight.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.Positive
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Basic
-- The equal-length certificate computes the explicit classical root enumeration and its
-- signed-pair indexing rather than introducing a second invariant form.
import all TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD
import all TauCeti.Data.Fin.DistinctPairs

/-!
# Positive-root order on the tripled D₄ weight diagram

A path of positive simple-root moves joins two tripled weights exactly when their difference
lies in the integral positive root cone. The integrality condition matters: weights in different
minuscule summands must not be compared using the rational root cone alone.

The three summands have the same canonical root-form length, so the invariant-form raising-path
criterion applies to the full table. These paths let raising-stable coordinate flags exclude all
negative root directions, not just negative simple-root directions.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §13.4.

The path argument follows `TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.Positive`.
-/

public section

namespace TauCeti.DynkinType

local notation "P" => typeDSimplyConnectedRootDatum 4 le_rfl
local notation "μ" => d4TripledWeight

/-- A positive simple-root move on the twenty-four tripled D₄ weights. -/
def D4TripledRaisingStep (a b : Fin 24) : Prop :=
  ∃ i : Fin 4, μ a i = -1 ∧ d4TripledReflection i a = b

/-- A raising move is simple reflection at a coroot value of minus one. -/
theorem d4TripledRaisingStep_iff (a b : Fin 24) :
    D4TripledRaisingStep a b ↔
      ∃ i : Fin 4, μ a i = -1 ∧ d4TripledReflection i a = b := Iff.rfl

private theorem rootForm_eq (a b : Fin 24) :
    (P).RootForm (μ a) (μ a) = (P).RootForm (μ b) (μ b) := by
  suffices ∀ a b : Fin 24, (P).RootForm (μ a) (μ a) = (P).RootForm (μ b) (μ b) from
    this a b
  simp only [RootPairing.rootForm_apply_apply, RootPairing.coroot', LinearMap.flip_apply,
    toLinearMap_typeDSimplyConnectedRootDatum, coroot_typeDSimplyConnectedRootDatum]
  decide +kernel

/-- Positive simple-root paths are exactly positive integral differences of tripled D₄ weights.
Membership in the cone already forces the endpoints to lie in the same minuscule summand. -/
theorem d4Tripled_raisingPath_iff_mem_posRootCone (a b : Fin 24) :
    Relation.ReflTransGen D4TripledRaisingStep a b ↔
      μ b - μ a ∈ posRootCone P (typeDSimplyConnectedBase 4 le_rfl) := by
  constructor
  · intro h
    induction h with
    | refl => simp
    | @tail b c h hbc ih =>
      obtain ⟨i, hi, rfl⟩ := (d4TripledRaisingStep_iff _ _).mp hbc
      have heq : μ (d4TripledReflection i b) - μ a =
          (μ b - μ a) + (P).root (typeDSimpleIndex 4 le_rfl i) := by
        rw [d4TripledWeight_reflection, hi, root_typeDSimpleIndex]
        simp only [neg_smul, one_smul, sub_neg_eq_add]
        abel
      rw [heq]
      exact (posRootCone P (typeDSimplyConnectedBase 4 le_rfl)).add_mem ih
        (root_typeDSimpleIndex_mem_posRootCone le_rfl i)
  · intro h
    obtain ⟨c, hc⟩ := (mem_typeD_posRootCone_iff le_rfl).mp h
    refine (P).toInvariantForm.reflTransGen_of_sub_eq_sum
      (fun _ hv hne ↦ (P).rootForm_pos_of_ne_zero hv hne)
      d4TripledWeight_injective rootForm_eq
      (f := typeDSimpleIndex 4 le_rfl) (fun a i hi ↦ ?_) hc
    have hai : μ a i = -1 := by
      rw [coroot'_typeDSimpleIndex_apply le_rfl] at hi
      rcases d4TripledWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a i with h | h | h <;> omega
    refine ⟨d4TripledReflection i a, (d4TripledRaisingStep_iff _ _).mpr ⟨i, hai, rfl⟩, ?_⟩
    rw [d4TripledWeight_reflection, hai, root_typeDSimpleIndex]
    simp

end TauCeti.DynkinType
