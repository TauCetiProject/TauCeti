/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
public import TauCeti.LinearAlgebra.RootSystem.Positive
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.MinusculeWeight
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Basic

/-!
# Raising paths in the E7 minuscule weight diagram

A raising step adds a numbered simple root to a minuscule weight. A path of such steps exists
exactly when the difference of its endpoints lies in the integral positive root cone. The
empty path accounts for equal endpoints.

The proof uses the reflection-invariant root form and the existing weight table: all minuscule
weights have the same length, so `RootPairing.InvariantForm.reflTransGen_of_sub_eq_sum` builds
a raising path from the lower endpoint, by induction on the simple-root coefficients.
Positivity is used only on a nonzero difference in the root lattice; the roots need not span the
full fundamental-weight lattice over the integers.
-/

public section

namespace TauCeti.DynkinType

open scoped BigOperators

local notation "P" => e7SimplyConnectedRootDatum
local notation "μ" => e7MinusculeWeight
local notation "α" => fun i : Fin 7 ↦ e7Root (e7SimpleIndex i)

/-- A positive simple-root step in the minuscule weight diagram. -/
def E7MinusculeRaisingStep (a b : Fin 56) : Prop :=
  ∃ i : Fin 7, μ a i = -1 ∧ e7MinusculeReflection i a = b

/-- A raising step is reflection in a simple root at which the source has weight minus one. -/
theorem e7MinusculeRaisingStep_iff (a b : Fin 56) :
    E7MinusculeRaisingStep a b ↔
      ∃ i : Fin 7, μ a i = -1 ∧ e7MinusculeReflection i a = b := Iff.rfl

private theorem e7SimpleIndex_bijOn :
    Set.BijOn e7SimpleIndex Set.univ e7SimplyConnectedBase.support :=
  ⟨fun i _ ↦ mem_support_e7SimplyConnectedBase.mpr (by simp), e7SimpleIndex_injective.injOn,
    fun j hj ↦ ⟨⟨j, mem_support_e7SimplyConnectedBase.mp hj⟩, trivial, Fin.ext (by simp)⟩⟩

/-- The integral positive root cone in the seven numbered simple-root coordinates. -/
theorem mem_e7_posRootCone_iff {x : Fin 7 → ℤ} :
    x ∈ posRootCone P e7SimplyConnectedBase ↔
      ∃ c : Fin 7 → ℕ, x = ∑ i, c i • α i := by
  simpa only [e7SimplyConnectedRootDatum_root] using
    mem_posRootCone_iff_exists_nat_of_bijOn P e7SimplyConnectedBase e7SimpleIndex_bijOn

private theorem coroot'_e7SimpleIndex_e7MinusculeWeight (i : Fin 7) (a : Fin 56) :
    e7SimplyConnectedRootDatum.coroot' (e7SimpleIndex i) (μ a) = μ a i := by
  simp

/-- Raising paths are exactly the positive integral differences of minuscule weights. -/
theorem e7Minuscule_raisingPath_iff_mem_posRootCone (a b : Fin 56) :
    Relation.ReflTransGen E7MinusculeRaisingStep a b ↔
      μ b - μ a ∈ posRootCone P e7SimplyConnectedBase :=
  e7SimplyConnectedRootDatum.toInvariantForm.reflTransGen_iff_sub_mem_posRootCone
    (fun _ hv hne ↦ e7SimplyConnectedRootDatum.rootForm_pos_of_ne_zero hv hne)
    e7MinusculeWeight_injective
    (e7SimplyConnectedRootDatum.toInvariantForm.apply_self_eq_of_forall_exists_foldl
      e7SimplyConnectedRootDatum_reflection_e7MinusculeWeight exists_e7MinusculeReflections_eq)
    e7SimpleIndex_bijOn e7SimplyConnectedRootDatum_reflection_e7MinusculeWeight
    (fun x i hi ↦ by
      rw [coroot'_e7SimpleIndex_e7MinusculeWeight] at hi ⊢
      rcases e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one x i with h | h | h <;> omega)
    fun _ _ ↦ by simp only [coroot'_e7SimpleIndex_e7MinusculeWeight, E7MinusculeRaisingStep]

/-- The raising-path criterion in the numbered seven-simple-root coordinates. -/
theorem e7Minuscule_raisingPath_iff_exists_nat_coefficients (a b : Fin 56) :
    Relation.ReflTransGen E7MinusculeRaisingStep a b ↔
      ∃ c : Fin 7 → ℕ, μ b - μ a = ∑ i, c i • α i := by
  rw [e7Minuscule_raisingPath_iff_mem_posRootCone, mem_e7_posRootCone_iff]

end TauCeti.DynkinType
