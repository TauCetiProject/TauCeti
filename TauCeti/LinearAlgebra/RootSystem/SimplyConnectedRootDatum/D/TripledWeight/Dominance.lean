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

private theorem reflection_d4TripledWeight (i : Fin 4) (a : Fin 24) :
    (P).reflection (typeDSimpleIndex 4 le_rfl i) (μ a) = μ (d4TripledReflection i a) := by
  rw [RootPairing.reflection_apply, coroot'_typeDSimpleIndex_apply le_rfl,
    root_typeDSimpleIndex, d4TripledWeight_reflection]

/-- Positive simple-root paths are exactly positive integral differences of tripled D₄ weights.
Membership in the cone already forces the endpoints to lie in the same minuscule summand. -/
theorem d4Tripled_raisingPath_iff_mem_posRootCone (a b : Fin 24) :
    Relation.ReflTransGen D4TripledRaisingStep a b ↔
      μ b - μ a ∈ posRootCone P (typeDSimplyConnectedBase 4 le_rfl) :=
  (P).toInvariantForm.reflTransGen_iff_sub_mem_posRootCone
    (fun _ hv hne ↦ (P).rootForm_pos_of_ne_zero hv hne) d4TripledWeight_injective rootForm_eq
    (typeDSimpleIndex_bijOn le_rfl) reflection_d4TripledWeight
    (fun x i hi ↦ by
      rw [coroot'_typeDSimpleIndex_apply le_rfl] at hi ⊢
      rcases d4TripledWeight_apply_eq_neg_one_or_eq_zero_or_eq_one x i with h | h | h <;> omega)
    fun _ _ ↦ by simp only [coroot'_typeDSimpleIndex_apply le_rfl, D4TripledRaisingStep]

end TauCeti.DynkinType
