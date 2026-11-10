/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.FinCases
public import TauCeti.Combinatorics.Network.Menger.SetToSet

/-!
# Examples of vertex-capacitated Menger's theorem

These examples exercise two features that distinguish vertex-capacitated path packings from
ordinary families of disjoint paths.

First, a two-arrow path through a vertex of capacity two can occur twice in an optimal packing.
The singleton containing that vertex is a separator of weight two, certifying optimality.

Second, capacities constrain the endpoints of set-to-set paths. Two copies of a direct path use
capacity two at each endpoint, while an overlapping terminal contributes zero-length paths up to
its own capacity. The terminal overlap belongs to every separator even when its capacity is zero.
-/

namespace TauCeti.Examples.VertexCapacitatedMenger

open Finset TauCeti

public section

/-! ## A repeated path through a capacity-two vertex -/

private inductive BottleneckHom : Fin 3 → Fin 3 → Type
  | first : BottleneckHom 0 1
  | second : BottleneckHom 1 2

private def bottleneckPath : ArrowWalk BottleneckHom 0 2 :=
  ((ArrowWalk.nil 0).cons BottleneckHom.first).cons BottleneckHom.second

private theorem bottleneckPath_isPath : bottleneckPath.IsPath := by
  simp [bottleneckPath, ArrowWalk.isPath_def, Quiver.Path.vertices_cons]

private theorem not_reachableAvoiding_bottleneck :
    ¬ReachableAvoiding BottleneckHom ({1} : Finset (Fin 3)) 0 2 := by
  intro h
  obtain ⟨p, hp⟩ := reachableAvoiding_def.mp h
  have hadj : IsEmpty (BottleneckHom 0 2) := ⟨fun e ↦ by cases e⟩
  obtain ⟨v, hv, hv0, hv2⟩ :=
    p.exists_mem_vertices_ne_ne (by decide) hadj
  fin_cases v
  · exact hv0 rfl
  · exact hp 1 hv (by simp)
  · exact hv2 rfl

/-- A vertex of capacity two supports two copies of the same path, and its singleton separator
has the same weight. This is an optimal packing by weak duality. -/
theorem exists_capacity_two_bottleneck :
    let c : Fin 3 → ℕ := fun v ↦ if v = 1 then 2 else 0
    let X : Finset (Fin 3) := {1}
    ∃ (Q : Fin 3 → Fin 3 → Type) (P : Fin 2 → ArrowWalk Q 0 2),
    (∀ i, (P i).IsPath) ∧ P 0 = P 1 ∧
      #{i | (1 : Fin 3) ∈ (P i).vertices} = 2 ∧
      (∀ v, v ≠ 0 → v ≠ 2 → #{i | v ∈ (P i).vertices} ≤ c v) ∧
      ¬ReachableAvoiding Q (X : Set (Fin 3)) 0 2 ∧
      ∑ v ∈ X, c v = 2 ∧
      Fintype.card (Fin 2) ≤ ∑ v ∈ X, c v := by
  dsimp only
  refine ⟨BottleneckHom, fun _ ↦ bottleneckPath,
    fun _ ↦ bottleneckPath_isPath, rfl, ?_, ?_,
    not_reachableAvoiding_bottleneck, ?_, ?_⟩
  · simp [bottleneckPath]
  · intro v hv0 hv2
    fin_cases v <;> simp_all [bottleneckPath]
  · simp
  · exact card_le_sum_of_not_reachableAvoiding
      (P := fun _ : Fin 2 ↦ bottleneckPath)
      (c := fun v : Fin 3 ↦ if v = 1 then 2 else 0)
      (by
        intro v hv0 hv2
        fin_cases v <;> simp_all [bottleneckPath])
      (by simp) (by simp) not_reachableAvoiding_bottleneck

/-! ## Endpoint usage and an overlapping terminal -/

private inductive OverlapHom : Fin 3 → Fin 3 → Type
  | direct : OverlapHom 0 2

private def directPath : ArrowWalk OverlapHom 0 2 :=
  (ArrowWalk.nil 0).cons OverlapHom.direct

@[simp]
private theorem directPath_vertices : directPath.vertices = [0, 2] :=
  (rfl)

private def overlapSource {m : ℕ} : Fin 2 ⊕ Fin m → Fin 3
  | .inl _ => 0
  | .inr _ => 1

private def overlapTarget {m : ℕ} : Fin 2 ⊕ Fin m → Fin 3
  | .inl _ => 2
  | .inr _ => 1

private def overlapPath {m : ℕ} :
    ∀ i : Fin 2 ⊕ Fin m, ArrowWalk OverlapHom (overlapSource i) (overlapTarget i)
  | .inl _ => directPath
  | .inr _ => ArrowWalk.nil 1

@[simp]
private theorem overlapPath_inl_vertices {m : ℕ} (i : Fin 2) :
    (overlapPath (Sum.inl i : Fin 2 ⊕ Fin m)).vertices = [0, 2] :=
  (rfl)

@[simp]
private theorem overlapPath_inr_vertices {m : ℕ} (i : Fin m) :
    (overlapPath (Sum.inr i : Fin 2 ⊕ Fin m)).vertices = [1] :=
  (rfl)

private def overlapCapacity (m : ℕ) : Fin 3 → ℕ
  | 0 => 2
  | 1 => m
  | 2 => 2

private theorem overlapPath_isPath {m : ℕ} (i : Fin 2 ⊕ Fin m) :
    (overlapPath i).IsPath := by
  cases i
  · rw [ArrowWalk.isPath_def, overlapPath_inl_vertices]
    simp
  · rw [ArrowWalk.isPath_def, overlapPath_inr_vertices]
    simp

private theorem overlapPath_interior {m : ℕ} (i : Fin 2 ⊕ Fin m) (v : Fin 3)
    (hv : v ∈ (overlapPath i).vertices) (hvs : v ≠ overlapSource i)
    (hvt : v ≠ overlapTarget i) : v ∉ ({0, 1} : Finset (Fin 3)) ∧
      v ∉ ({1, 2} : Finset (Fin 3)) := by
  cases i <;> simp_all [overlapPath, overlapSource, overlapTarget, directPath]

private theorem overlapPath_usage (m : ℕ) (v : Fin 3) :
    #{i : Fin 2 ⊕ Fin m | v ∈ (overlapPath i).vertices} = overlapCapacity m v := by
  classical
  fin_cases v <;>
    rw [card_filter, Fintype.sum_sum_type] <;>
    simp [overlapCapacity]

private theorem overlapSeparator (a b : Fin 3) (ha : a ∈ ({0, 1} : Finset (Fin 3))) :
    ¬ReachableAvoiding OverlapHom (({0, 1} : Finset (Fin 3)) : Set (Fin 3)) a b := by
  intro h
  exact h.source_notMem (by simpa using ha)

private theorem overlapPacking (m : ℕ) :
    let A : Finset (Fin 3) := {0, 1}
    let B : Finset (Fin 3) := {1, 2}
    let X : Finset (Fin 3) := {0, 1}
    (∀ i : Fin 2 ⊕ Fin m, overlapSource i ∈ A) ∧
      (∀ i : Fin 2 ⊕ Fin m, overlapTarget i ∈ B) ∧
      (∀ i : Fin 2 ⊕ Fin m, (overlapPath i).IsPath) ∧
      (∀ i : Fin 2 ⊕ Fin m, ∀ v ∈ (overlapPath i).vertices,
        v ≠ overlapSource i → v ≠ overlapTarget i → v ∉ A ∧ v ∉ B) ∧
      (∀ v, #{i : Fin 2 ⊕ Fin m | v ∈ (overlapPath i).vertices} = overlapCapacity m v) ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬ReachableAvoiding OverlapHom (X : Set (Fin 3)) a b) ∧
      Fintype.card (Fin 2 ⊕ Fin m) = ∑ v ∈ X, overlapCapacity m v := by
  dsimp only
  refine ⟨?_, ?_, overlapPath_isPath, overlapPath_interior, ?_,
    fun a ha b _ ↦ overlapSeparator a b ha, ?_⟩
  · rintro (i | i) <;> simp [overlapSource]
  · rintro (i | i) <;> simp [overlapTarget]
  · exact overlapPath_usage m
  · simp [overlapCapacity]

/-- For every `m`, two direct paths and `m` zero-length paths saturate endpoint capacity two and
overlap capacity `m`; the source terminal set is a separator of the same total weight. -/
theorem exists_overlap_packing (m : ℕ) :
    let c : Fin 3 → ℕ := fun | 0 => 2 | 1 => m | 2 => 2
    let A : Finset (Fin 3) := {0, 1}
    let B : Finset (Fin 3) := {1, 2}
    let X : Finset (Fin 3) := {0, 1}
    ∃ (Q : Fin 3 → Fin 3 → Type) (a b : Fin 2 ⊕ Fin m → Fin 3)
      (P : ∀ i, ArrowWalk Q (a i) (b i)),
      (∀ i : Fin 2, a (.inl i) = 0 ∧ b (.inl i) = 2) ∧
      (∀ i : Fin m, a (.inr i) = 1 ∧ b (.inr i) = 1 ∧ (P (.inr i)).length = 0) ∧
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ v ∈ (P i).vertices, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
      (∀ v, #{i | v ∈ (P i).vertices} = c v) ∧
      (∀ x ∈ A, ∀ y ∈ B, ¬ReachableAvoiding Q (X : Set (Fin 3)) x y) ∧
      Fintype.card (Fin 2 ⊕ Fin m) = ∑ v ∈ X, c v := by
  dsimp only
  refine ⟨OverlapHom, overlapSource, overlapTarget, overlapPath, ?_, ?_, overlapPacking m⟩
  · intro i
    simp [overlapSource, overlapTarget]
  · intro i
    simp [overlapSource, overlapTarget, overlapPath]

/-- With overlap capacity zero, the two direct paths saturate both endpoints. The common terminal
still belongs to the displayed separator, but contributes zero to its weight. -/
example :
    Fintype.card (Fin 2 ⊕ Fin 0) =
      ∑ v ∈ ({0, 1} : Finset (Fin 3)), overlapCapacity 0 v ∧
      #{i : Fin 2 ⊕ Fin 0 | (0 : Fin 3) ∈ (overlapPath i).vertices} = 2 := by
  refine ⟨(overlapPacking 0).2.2.2.2.2.2, ?_⟩
  rw [overlapPath_usage]
  rfl

/-- With overlap capacity two, the optimal packing additionally contains two copies of the
zero-length path at the common terminal. -/
example :
    Fintype.card (Fin 2 ⊕ Fin 2) =
      ∑ v ∈ ({0, 1} : Finset (Fin 3)), overlapCapacity 2 v ∧
      (overlapPath (Sum.inr 0 : Fin 2 ⊕ Fin 2)).length = 0 ∧
      overlapPath (Sum.inr 0 : Fin 2 ⊕ Fin 2) =
        overlapPath (Sum.inr (1 : Fin 2)) ∧
      #{i : Fin 2 ⊕ Fin 2 | (1 : Fin 3) ∈ (overlapPath i).vertices} = 2 := by
  refine ⟨(overlapPacking 2).2.2.2.2.2.2, rfl, rfl, ?_⟩
  rw [overlapPath_usage]
  rfl

end

end TauCeti.Examples.VertexCapacitatedMenger
