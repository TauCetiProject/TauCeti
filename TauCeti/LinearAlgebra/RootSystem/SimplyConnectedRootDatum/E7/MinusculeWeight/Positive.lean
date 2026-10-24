/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
public import TauCeti.LinearAlgebra.RootSystem.Positive
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.MinusculeWeight

/-!
# Raising paths in the E7 minuscule weight diagram

A raising step adds a numbered simple root to a minuscule weight. A path of such steps exists
exactly when the difference of its endpoints lies in the integral positive root cone. The
empty path accounts for equal endpoints.

The proof uses the reflection-invariant root form and the existing weight table. Positivity
is used only on a nonzero difference in the root lattice; the roots need not span the full
fundamental-weight lattice over the integers.
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

private theorem two_mul_rootForm_simple (x : Fin 7 → ℤ) (i : Fin 7) :
    2 * B x (α i) = x i * B (α i) (α i) := by
  have h := congrArg (e7SimplyConnectedRootDatum.toLinearMap x)
    (e7SimplyConnectedRootDatum.rootForm_self_smul_coroot (e7SimpleIndex i))
  rw [map_smul, LinearMap.map_smul_of_tower,
    e7SimplyConnectedRootDatum.toLinearMap_apply_apply_Polarization] at h
  have hpair :
      e7SimplyConnectedRootDatum.toLinearMap x
        (e7SimplyConnectedRootDatum.coroot (e7SimpleIndex i)) = x i := by
    simp
  rw [hpair] at h
  have hsym : B (α i) x = B x (α i) := by
    simpa using e7SimplyConnectedRootDatum.rootForm_symmetric.eq (α i) x
  simpa only [e7SimplyConnectedRootDatum_root, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat, hsym, mul_comm] using h.symm

private theorem exists_raising_step_of_sum {a b : Fin 56} (hab : a ≠ b)
    (c : Fin 7 → ℕ) (hc : μ b - μ a = ∑ i, c i • α i) :
    ∃ i, 0 < c i ∧ μ a i = -1 := by
  have hne : μ b - μ a ≠ 0 := by
    intro h
    exact hab (e7MinusculeWeight_injective (sub_eq_zero.mp h)).symm
  have hspan : μ b - μ a ∈ e7SimplyConnectedRootDatum.rootSpan ℤ := by
    rw [hc]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have hroot : e7SimplyConnectedRootDatum.root (e7SimpleIndex i) ∈
        e7SimplyConnectedRootDatum.rootSpan ℤ :=
      (e7SimplyConnectedRootDatum.rootSpanMem ℤ (e7SimpleIndex i)).property
    simpa only [e7SimplyConnectedRootDatum_root] using
      (e7SimplyConnectedRootDatum.rootSpan ℤ).smul_of_tower_mem (c i) hroot
  have hpos := e7SimplyConnectedRootDatum.rootForm_pos_of_ne_zero hspan hne
  have heq := rootForm_minuscule_eq a b
  have hsym : B (μ a) (μ b) = B (μ b) (μ a) := by
    simpa using e7SimplyConnectedRootDatum.rootForm_symmetric.eq (μ a) (μ b)
  have hnegative : 2 * B (μ a) (μ b - μ a) < 0 := by
    simp only [map_sub, LinearMap.sub_apply] at hpos ⊢
    linarith
  have hsum : 2 * B (μ a) (μ b - μ a) =
      ∑ i, (c i : ℤ) * (μ a i * B (α i) (α i)) := by
    rw [hc, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_nsmul, nsmul_eq_mul]
    calc
      2 * ((c i : ℤ) * B (μ a) (α i)) =
          (c i : ℤ) * (2 * B (μ a) (α i)) := by ring
      _ = _ := by rw [two_mul_rootForm_simple]
  rw [hsum] at hnegative
  by_contra! h
  have hnonneg : 0 ≤ ∑ i, (c i : ℤ) * (μ a i * B (α i) (α i)) := by
    refine Finset.sum_nonneg fun i _ ↦ ?_
    by_cases hci : c i = 0
    · simp [hci]
    have hcoord : 0 ≤ μ a i := by
      rcases e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a i with hi | hi | hi
      · exact False.elim (h i (Nat.pos_of_ne_zero hci) hi)
      · simp [hi]
      · simp [hi]
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg hcoord (e7SimplyConnectedRootDatum.zero_le_rootForm _))
  exact hnegative.not_ge hnonneg

private theorem raisingPath_of_sum (a : Fin 56) :
    ∀ b : Fin 56, (∃ c : Fin 7 → ℕ, μ b - μ a = ∑ i, c i • α i) →
      Relation.ReflTransGen E7MinusculeRaisingStep a b := by
  classical
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    intro b hc
    by_cases hab : a = b
    · subst b
      exact .refl
    obtain ⟨c, hc⟩ := hc
    obtain ⟨i, hci, hi⟩ := exists_raising_step_of_sum hab c hc
    let c' : Fin 7 → ℕ := Function.update c i (c i - 1)
    have hcoeff (j : Fin 7) : c j = c' j + if j = i then 1 else 0 := by
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
    have hreflection : μ (e7MinusculeReflection i a) = μ a + α i := by
      rw [e7MinusculeWeight_reflection, hi]
      simp
    have hremaining : μ b - μ (e7MinusculeReflection i a) = ∑ j, c' j • α j := by
      rw [hreflection]
      rw [hsum] at hc
      exact sub_eq_iff_eq_add.mpr (by linear_combination hc)
    have hpath := ih (e7MinusculeReflection i a)
      ((e7MinusculeReflection_lt_iff i a).mpr hi) b ⟨c', hremaining⟩
    exact (Relation.ReflTransGen.single ((e7MinusculeRaisingStep_iff _ _).mpr
      ⟨i, hi, rfl⟩)).trans hpath

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
    exact raisingPath_of_sum a b (mem_e7_posRootCone_iff.mp h)

/-- The raising-path criterion in the numbered seven-simple-root coordinates. -/
theorem e7Minuscule_raisingPath_iff_exists_nat_coefficients (a b : Fin 56) :
    Relation.ReflTransGen E7MinusculeRaisingStep a b ↔
      ∃ c : Fin 7 → ℕ, μ b - μ a = ∑ i, c i • α i := by
  rw [e7Minuscule_raisingPath_iff_mem_posRootCone, mem_e7_posRootCone_iff]

end TauCeti.DynkinType
