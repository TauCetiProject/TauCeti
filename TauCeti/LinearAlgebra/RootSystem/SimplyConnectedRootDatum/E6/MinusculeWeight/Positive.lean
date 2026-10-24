/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
public import TauCeti.LinearAlgebra.RootSystem.Positive
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.MinusculeWeight
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Basic

/-!
# Raising paths in the E₆ minuscule weight diagram

A raising step adds a numbered simple root to a minuscule weight: it is the simple reflection at
a node where the weight has coordinate `-1`. A path of such steps exists exactly when the
difference of its endpoints lies in the integral positive root cone. The empty path accounts for
equal endpoints. This is the combinatorial input describing which matrix entries a positive
subgroup of the twenty-seven-dimensional minuscule representation can reach.

All minuscule weights have the same length for the reflection-invariant root form, so
`RootPairing.InvariantForm.reflTransGen_of_sub_eq_sum` builds the path: it takes raising steps
from the lower endpoint, by induction along the order of the weight table.
Positivity is used only on a nonzero difference in the root lattice; the roots need not span the
full fundamental-weight lattice over the integers.

The construction follows the type-`E₇` one in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.MinusculeWeight.Positive`.
-/

public section

namespace TauCeti.DynkinType

open scoped BigOperators

local notation "P" => e6SimplyConnectedRootDatum
local notation "B" => e6SimplyConnectedRootDatum.RootForm
local notation "μ" => e6MinusculeWeight
local notation "α" => fun i : Fin 6 ↦ e6Root (e6SimpleIndex i)

/-- A positive simple-root step in the minuscule weight diagram. -/
def E6MinusculeRaisingStep (a b : Fin 27) : Prop :=
  ∃ i : Fin 6, μ a i = -1 ∧ e6MinusculeReflection i a = b

/-- A raising step is reflection in a simple root at which the source has weight minus one. -/
theorem e6MinusculeRaisingStep_iff (a b : Fin 27) :
    E6MinusculeRaisingStep a b ↔
      ∃ i : Fin 6, μ a i = -1 ∧ e6MinusculeReflection i a = b := Iff.rfl

/-- The integral positive root cone in the six numbered simple-root coordinates. -/
theorem mem_e6_posRootCone_iff {x : Fin 6 → ℤ} :
    x ∈ posRootCone P e6SimplyConnectedBase ↔
      ∃ c : Fin 6 → ℕ, x = ∑ i, c i • α i := by
  classical
  constructor
  · intro hx
    obtain ⟨f, hf⟩ := (mem_posRootCone P e6SimplyConnectedBase).mp hx
    refine ⟨fun i ↦ f (e6SimpleIndex i), hf.trans ?_⟩
    symm
    refine Finset.sum_bij (fun i _ ↦ e6SimpleIndex i) ?_ ?_ ?_ ?_
    · intro i _
      simp only [mem_e6SimplyConnectedBase_support, e6SimpleIndex_val]
      exact i.isLt
    · intro i _ j _ h
      exact e6SimpleIndex_injective h
    · intro j hj
      refine ⟨⟨j.val, mem_e6SimplyConnectedBase_support.mp hj⟩, Finset.mem_univ _, ?_⟩
      exact Fin.ext (by simp only [e6SimpleIndex_val])
    · intro i _
      simp
  · rintro ⟨c, rfl⟩
    refine (posRootCone P e6SimplyConnectedBase).sum_mem fun i _ ↦ ?_
    apply (posRootCone P e6SimplyConnectedBase).nsmul_mem
    simpa only [e6SimplyConnectedRootDatum_root] using
      root_mem_posRootCone_of_mem_posRoots P e6SimplyConnectedBase
        (i := e6SimpleIndex i)
        (support_subset_posRoots P e6SimplyConnectedBase (by simp))

private theorem rootForm_minuscule_reflection (i : Fin 6) (a : Fin 27) :
    B (μ (e6MinusculeReflection i a)) (μ (e6MinusculeReflection i a)) =
      B (μ a) (μ a) := by
  rw [← e6SimplyConnectedRootDatum_reflection_e6MinusculeWeight]
  exact e6SimplyConnectedRootDatum.rootForm_reflection_reflection_apply _ _ _

private theorem rootForm_minuscule_eq (a b : Fin 27) :
    B (μ a) (μ a) = B (μ b) (μ b) := by
  suffices h : ∀ a, B (μ a) (μ a) = B (μ 0) (μ 0) from
    (h a).trans (h b).symm
  intro a
  obtain ⟨l, hl⟩ := exists_e6MinusculeReflections_eq a
  rw [← hl]
  clear a hl
  induction l using List.reverseRecOn with
  | nil => simp only [List.foldl_nil]
  | append_singleton l i ih =>
    rw [List.foldl_append]
    simpa only [List.foldl_cons, List.foldl_nil, rootForm_minuscule_reflection] using ih

/-- Raising paths are exactly the positive integral differences of minuscule weights. -/
theorem e6Minuscule_raisingPath_iff_mem_posRootCone (a b : Fin 27) :
    Relation.ReflTransGen E6MinusculeRaisingStep a b ↔
      μ b - μ a ∈ posRootCone P e6SimplyConnectedBase := by
  constructor
  · intro h
    induction h with
    | refl => simp
    | @tail b c h hbc ih =>
      obtain ⟨i, hi, rfl⟩ := (e6MinusculeRaisingStep_iff _ _).mp hbc
      have hroot : α i ∈ posRootCone P e6SimplyConnectedBase := by
        simpa only [e6SimplyConnectedRootDatum_root] using
          root_mem_posRootCone_of_mem_posRoots P e6SimplyConnectedBase
            (i := e6SimpleIndex i)
            (support_subset_posRoots P e6SimplyConnectedBase (by simp))
      have heq : μ (e6MinusculeReflection i b) - μ a = (μ b - μ a) + α i := by
        rw [e6MinusculeWeight_reflection, hi]
        simp only [neg_smul, one_smul, sub_neg_eq_add]
        abel
      rw [heq]
      exact (posRootCone P e6SimplyConnectedBase).add_mem ih hroot
  · intro h
    obtain ⟨c, hc⟩ := mem_e6_posRootCone_iff.mp h
    refine e6SimplyConnectedRootDatum.toInvariantForm.reflTransGen_of_sub_eq_sum
      (fun _ ↦ e6SimplyConnectedRootDatum.zero_le_rootForm _)
      (fun _ hv hne ↦ e6SimplyConnectedRootDatum.rootForm_pos_of_ne_zero hv hne)
      e6MinusculeWeight_injective rootForm_minuscule_eq (f := e6SimpleIndex)
      (fun x i hi ↦ ?_) (by simpa only [e6SimplyConnectedRootDatum_root] using hc)
    -- A negative coroot value on a minuscule weight is `-1`, where the simple reflection raises.
    have hpair : e6SimplyConnectedRootDatum.coroot' (e6SimpleIndex i) (μ x) = μ x i := by
      simp
    have hai : μ x i = -1 := by
      rw [hpair] at hi
      rcases e6MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one x i with h | h | h <;> omega
    refine ⟨e6MinusculeReflection i x, (e6MinusculeReflection_lt_iff i x).mpr hai,
      (e6MinusculeRaisingStep_iff _ _).mpr ⟨i, hai, rfl⟩, ?_⟩
    rw [e6MinusculeWeight_reflection, hai]
    simp

/-- The raising-path criterion in the numbered six-simple-root coordinates. -/
theorem e6Minuscule_raisingPath_iff_exists_nat_coefficients (a b : Fin 27) :
    Relation.ReflTransGen E6MinusculeRaisingStep a b ↔
      ∃ c : Fin 6 → ℕ, μ b - μ a = ∑ i, c i • α i := by
  rw [e6Minuscule_raisingPath_iff_mem_posRootCone, mem_e6_posRootCone_iff]

end TauCeti.DynkinType
