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
`RootPairing.InvariantForm.exists_pos_and_coroot'_neg_of_apply_self_eq` provides a raising step
from the lower endpoint, and induction along the order of the weight table completes the path.
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

private theorem exists_raising_step_of_sum {a b : Fin 27} (hab : a ≠ b)
    (c : Fin 6 → ℕ) (hc : μ b - μ a = ∑ i, c i • α i) :
    ∃ i, 0 < c i ∧ μ a i = -1 := by
  have hne : μ b - μ a ≠ 0 := by
    intro h
    exact hab (e6MinusculeWeight_injective (sub_eq_zero.mp h)).symm
  have hspan : μ b - μ a ∈ e6SimplyConnectedRootDatum.rootSpan ℤ := by
    rw [hc]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have hroot : e6SimplyConnectedRootDatum.root (e6SimpleIndex i) ∈
        e6SimplyConnectedRootDatum.rootSpan ℤ :=
      (e6SimplyConnectedRootDatum.rootSpanMem ℤ (e6SimpleIndex i)).property
    simpa only [e6SimplyConnectedRootDatum_root] using
      (e6SimplyConnectedRootDatum.rootSpan ℤ).smul_of_tower_mem (c i) hroot
  obtain ⟨i, -, hci, hi⟩ :=
    e6SimplyConnectedRootDatum.toInvariantForm.exists_pos_and_coroot'_neg_of_apply_self_eq
      (fun _ ↦ e6SimplyConnectedRootDatum.zero_le_rootForm _) (rootForm_minuscule_eq a b)
      (e6SimplyConnectedRootDatum.rootForm_pos_of_ne_zero hspan hne) (f := e6SimpleIndex)
      (by simpa only [e6SimplyConnectedRootDatum_root] using hc)
  refine ⟨i, hci, ?_⟩
  have hpair : e6SimplyConnectedRootDatum.coroot' (e6SimpleIndex i) (μ a) = μ a i := by
    simp
  rw [hpair] at hi
  rcases e6MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a i with h | h | h <;> omega

private theorem raisingPath_of_sum (a : Fin 27) :
    ∀ b : Fin 27, (∃ c : Fin 6 → ℕ, μ b - μ a = ∑ i, c i • α i) →
      Relation.ReflTransGen E6MinusculeRaisingStep a b := by
  classical
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    intro b hc
    by_cases hab : a = b
    · subst b
      exact .refl
    obtain ⟨c, hc⟩ := hc
    obtain ⟨i, hci, hi⟩ := exists_raising_step_of_sum hab c hc
    let c' : Fin 6 → ℕ := Function.update c i (c i - 1)
    have hcoeff (j : Fin 6) : c j = c' j + if j = i then 1 else 0 := by
      by_cases hji : j = i
      · subst j
        simp only [c', Function.update_self, ↓reduceIte]
        omega
      · simp [c', hji]
    have hsum : ∑ j, c j • α j = (∑ j, c' j • α j) + α i := by
      simp_rw [hcoeff, add_nsmul]
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single i]
      · simp only [↓reduceIte, one_nsmul]
      · intro j _ hji
        simp only [hji, ↓reduceIte, zero_nsmul]
      · simp
    have hreflection : μ (e6MinusculeReflection i a) = μ a + α i := by
      rw [e6MinusculeWeight_reflection, hi]
      simp
    have hremaining : μ b - μ (e6MinusculeReflection i a) = ∑ j, c' j • α j := by
      rw [hreflection]
      rw [hsum] at hc
      exact sub_eq_iff_eq_add.mpr (by linear_combination hc)
    have hpath := ih (e6MinusculeReflection i a)
      ((e6MinusculeReflection_lt_iff i a).mpr hi) b ⟨c', hremaining⟩
    exact (Relation.ReflTransGen.single ((e6MinusculeRaisingStep_iff _ _).mpr
      ⟨i, hi, rfl⟩)).trans hpath

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
    exact raisingPath_of_sum a b (mem_e6_posRootCone_iff.mp h)

/-- The raising-path criterion in the numbered six-simple-root coordinates. -/
theorem e6Minuscule_raisingPath_iff_exists_nat_coefficients (a b : Fin 27) :
    Relation.ReflTransGen E6MinusculeRaisingStep a b ↔
      ∃ c : Fin 6 → ℕ, μ b - μ a = ∑ i, c i • α i := by
  rw [e6Minuscule_raisingPath_iff_mem_posRootCone, mem_e6_posRootCone_iff]

end TauCeti.DynkinType
