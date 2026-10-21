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
a raising path from the lower endpoint, by induction along the order of the weight table.
Positivity is used only on a nonzero difference in the root lattice; the roots need not span the
full fundamental-weight lattice over the integers.
-/

public section

namespace TauCeti.DynkinType

open scoped BigOperators

local notation "P" => e7SimplyConnectedRootDatum
local notation "B" => e7SimplyConnectedRootDatum.RootForm
local notation "μ" => e7MinusculeWeight
local notation "α" => fun i : Fin 7 ↦ e7Root (e7SimpleIndex i)

/-- A positive simple-root step in the minuscule weight diagram. -/
def E7MinusculeRaisingStep (a b : Fin 56) : Prop :=
  ∃ i : Fin 7, μ a i = -1 ∧ e7MinusculeReflection i a = b

/-- A raising step is reflection in a simple root at which the source has weight minus one. -/
theorem e7MinusculeRaisingStep_iff (a b : Fin 56) :
    E7MinusculeRaisingStep a b ↔
      ∃ i : Fin 7, μ a i = -1 ∧ e7MinusculeReflection i a = b := Iff.rfl

/-- The integral positive root cone in the seven numbered simple-root coordinates. -/
theorem mem_e7_posRootCone_iff {x : Fin 7 → ℤ} :
    x ∈ posRootCone P e7SimplyConnectedBase ↔
      ∃ c : Fin 7 → ℕ, x = ∑ i, c i • α i := by
  classical
  constructor
  · intro hx
    obtain ⟨f, hf⟩ := (mem_posRootCone P e7SimplyConnectedBase).mp hx
    refine ⟨fun i ↦ f (e7SimpleIndex i), hf.trans ?_⟩
    symm
    refine Finset.sum_bij (fun i _ ↦ e7SimpleIndex i) ?_ ?_ ?_ ?_
    · intro i _
      simp only [mem_support_e7SimplyConnectedBase, e7SimpleIndex_val]
      exact i.isLt
    · intro i _ j _ h
      exact e7SimpleIndex_injective h
    · intro j hj
      refine ⟨⟨j.val, mem_support_e7SimplyConnectedBase.mp hj⟩, Finset.mem_univ _, ?_⟩
      exact Fin.ext (by simp only [e7SimpleIndex_val])
    · intro i _
      simp
  · rintro ⟨c, rfl⟩
    refine (posRootCone P e7SimplyConnectedBase).sum_mem fun i _ ↦ ?_
    apply (posRootCone P e7SimplyConnectedBase).nsmul_mem
    simpa only [e7SimplyConnectedRootDatum_root] using
      root_mem_posRootCone_of_mem_posRoots P e7SimplyConnectedBase
        (i := e7SimpleIndex i)
        (support_subset_posRoots P e7SimplyConnectedBase (by simp))

private theorem rootForm_minuscule_reflection (i : Fin 7) (a : Fin 56) :
    B (μ (e7MinusculeReflection i a)) (μ (e7MinusculeReflection i a)) =
      B (μ a) (μ a) := by
  rw [← e7SimplyConnectedRootDatum_reflection_e7MinusculeWeight]
  exact e7SimplyConnectedRootDatum.rootForm_reflection_reflection_apply _ _ _

private theorem rootForm_minuscule_eq (a b : Fin 56) :
    B (μ a) (μ a) = B (μ b) (μ b) := by
  suffices h : ∀ a, B (μ a) (μ a) = B (μ 0) (μ 0) from
    (h a).trans (h b).symm
  intro a
  obtain ⟨l, hl⟩ := exists_e7MinusculeReflections_eq a
  rw [← hl]
  clear a hl
  induction l using List.reverseRecOn with
  | nil => simp only [List.foldl_nil]
  | append_singleton l i ih =>
    rw [List.foldl_append]
    simpa only [List.foldl_cons, List.foldl_nil, rootForm_minuscule_reflection] using ih

/-- Raising paths are exactly the positive integral differences of minuscule weights. -/
theorem e7Minuscule_raisingPath_iff_mem_posRootCone (a b : Fin 56) :
    Relation.ReflTransGen E7MinusculeRaisingStep a b ↔
      μ b - μ a ∈ posRootCone P e7SimplyConnectedBase := by
  constructor
  · intro h
    induction h with
    | refl => simp
    | @tail b c h hbc ih =>
      obtain ⟨i, hi, rfl⟩ := (e7MinusculeRaisingStep_iff _ _).mp hbc
      have hroot : α i ∈ posRootCone P e7SimplyConnectedBase := by
        simpa only [e7SimplyConnectedRootDatum_root] using
          root_mem_posRootCone_of_mem_posRoots P e7SimplyConnectedBase
            (i := e7SimpleIndex i)
            (support_subset_posRoots P e7SimplyConnectedBase (by simp))
      have heq : μ (e7MinusculeReflection i b) - μ a = (μ b - μ a) + α i := by
        rw [e7MinusculeWeight_reflection, hi]
        simp only [neg_smul, one_smul, sub_neg_eq_add]
        abel
      rw [heq]
      exact (posRootCone P e7SimplyConnectedBase).add_mem ih hroot
  · intro h
    obtain ⟨c, hc⟩ := mem_e7_posRootCone_iff.mp h
    refine e7SimplyConnectedRootDatum.toInvariantForm.reflTransGen_of_sub_eq_sum
      (fun _ ↦ e7SimplyConnectedRootDatum.zero_le_rootForm _)
      (fun _ hv hne ↦ e7SimplyConnectedRootDatum.rootForm_pos_of_ne_zero hv hne)
      e7MinusculeWeight_injective rootForm_minuscule_eq (f := e7SimpleIndex)
      (fun x i hi ↦ ?_) (by simpa only [e7SimplyConnectedRootDatum_root] using hc)
    -- A negative coroot value on a minuscule weight is `-1`, where the simple reflection raises.
    have hpair : e7SimplyConnectedRootDatum.coroot' (e7SimpleIndex i) (μ x) = μ x i := by
      simp
    have hai : μ x i = -1 := by
      rw [hpair] at hi
      rcases e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one x i with h | h | h <;> omega
    refine ⟨e7MinusculeReflection i x, (e7MinusculeReflection_lt_iff i x).mpr hai,
      (e7MinusculeRaisingStep_iff _ _).mpr ⟨i, hai, rfl⟩, ?_⟩
    rw [e7MinusculeWeight_reflection, hai]
    simp

/-- The raising-path criterion in the numbered seven-simple-root coordinates. -/
theorem e7Minuscule_raisingPath_iff_exists_nat_coefficients (a b : Fin 56) :
    Relation.ReflTransGen E7MinusculeRaisingStep a b ↔
      ∃ c : Fin 7 → ℕ, μ b - μ a = ∑ i, c i • α i := by
  rw [e7Minuscule_raisingPath_iff_mem_posRootCone, mem_e7_posRootCone_iff]

end TauCeti.DynkinType
