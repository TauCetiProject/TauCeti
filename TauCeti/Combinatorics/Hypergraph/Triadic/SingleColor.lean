/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Const
public import TauCeti.Combinatorics.Hypergraph.Triadic.RegularApproximation
import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise

/-!
# Triadic complexes with a single pair color

`TriadicComplex3.ofFinpartition P` is the coarsest triadic complex over a vertex partition `P`:
its pair palette has a single color, which every ordered distinct pair receives
(`PairColorSystem.const`), and it selects all its polyads. With `t` vertex cells it has exactly
`t³` polyads, one for each choice of three cells, so its complexity is `t + 1 + t³`.

These complexes calibrate the strong regular approximation `IsStrongRegularApproximation3`.

* Its lower skeleton is regular at the value `f > 0` of the schedule at `t + 1` exactly when
  every cell has one vertex or more than `1 / f` vertices
  (`TriadicComplex3.lowerSkeletonRegular_ofFinpartition_iff`). The cells are tested against
  themselves; a test of the pairs of distinct cells alone would accept every partition.
* A constant coloring, approximated by itself over this complex, is a strong regular approximation
  exactly when the lower skeleton is regular
  (`Colored3Graph.isStrongRegularApproximation3_const_ofFinpartition_iff`): the edit, the polyad
  decomposition, top regularity and the complexity bound hold automatically.
* When the schedule is at least one, the regularity conditions are void, and every coloring is
  approximated by itself over an equipartition into `t₀` cells, at the complexity bound
  `t₀³ + t₀ + 1` (`Colored3Graph.exists_strong_regular_approximation3_of_one_le`). The bound
  obtained this way is cubic in the number of cells, because the complexity of
  `ofFinpartition P` counts its `t³` polyads.

## Main definitions

* `TauCeti.TriadicComplex3.ofFinpartition`: the complex with cells `P`, one pair color and all
  polyads.

## Main results

* `TauCeti.TriadicComplex3.card_polyad3_ofFinpartition`: it has `t³` polyads.
* `TauCeti.TriadicComplex3.complexity_ofFinpartition`: its complexity is `t + 1 + t³`.
* `TauCeti.TriadicComplex3.isPolyadDecomposition_ofFinpartition`: its polyads decompose the
  injective triples.
* `TauCeti.TriadicComplex3.isRegularPair_ofFinpartition_of_ne`: its distinct cells form regular
  pairs.
* `TauCeti.TriadicComplex3.lowerSkeletonRegular_ofFinpartition_iff`: the regularity criterion
  for its lower skeleton.
* `TauCeti.Colored3Graph.isStrongRegularApproximation3_ofFinpartition_of_one_le`: at schedule
  values at least one, every coloring approximates itself over it.
* `TauCeti.Colored3Graph.isStrongRegularApproximation3_const_ofFinpartition_iff`: the criterion
  for a constant coloring.
* `TauCeti.Colored3Graph.exists_strong_regular_approximation3_of_one_le`: the strong regular
  approximation at schedule values at least one, with `t₀` equitable cells and complexity bound
  `t₀³ + t₀ + 1`.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset

namespace TauCeti

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TriadicComplex3

/-- The triadic complex with vertex cells `P`, a single pair color carried by every ordered
distinct pair, and all its polyads selected. -/
noncomputable def ofFinpartition (P : Finpartition (univ : Finset V)) : TriadicComplex3 V where
  pairColorCount := 1
  skeleton := ⟨P, .const 0⟩
  polyads := univ

variable (P : Finpartition (univ : Finset V))

@[simp]
theorem ofFinpartition_pairColorCount : (ofFinpartition P).pairColorCount = 1 :=
  (rfl)

@[simp]
theorem ofFinpartition_vertexPart : (ofFinpartition P).skeleton.vertexPart = P :=
  (rfl)

@[simp]
theorem ofFinpartition_polyads : (ofFinpartition P).polyads = univ :=
  (rfl)

/-- Every ordered distinct pair has the single pair color: the pair coloring is
`PairColorSystem.const`. -/
@[simp]
theorem ofFinpartition_pairColors :
    (ofFinpartition P).skeleton.pairColors = .const ⟨0, by simp⟩ :=
  (rfl)

/-- Over a partition into `t` cells with one pair color there are `t³` polyads, one for each
choice of three cells. -/
@[simp]
theorem card_polyad3_ofFinpartition :
    Fintype.card (Polyad3 (ofFinpartition P).skeleton) = #P.parts ^ 3 := by
  rw [card_polyad3, ofFinpartition_vertexPart, Fintype.card_fin, ofFinpartition_pairColorCount,
    one_pow, mul_one]

/-- The complex over a partition into `t` cells has `t` cells, one pair color and `t³` polyads,
so its complexity is `t + 1 + t³`. -/
@[simp]
theorem complexity_ofFinpartition :
    (ofFinpartition P).complexity = #P.parts + 1 + #P.parts ^ 3 := by
  rw [complexity_def, ofFinpartition_polyads, card_univ, card_polyad3_ofFinpartition,
    ofFinpartition_vertexPart, ofFinpartition_pairColorCount]

/-- The polyads of the complex over a partition decompose the injective triples. -/
theorem isPolyadDecomposition_ofFinpartition : (ofFinpartition P).IsPolyadDecomposition :=
  isPolyadDecomposition_of_polyads_eq_univ _ (ofFinpartition_polyads P)

/-- The cells of the complex over a partition are controlled at `t₀` exactly when the partition
is an equipartition into at least `t₀` cells. -/
@[simp]
theorem vertexCellsControlled_ofFinpartition_iff {t₀ : ℕ} :
    (ofFinpartition P).VertexCellsControlled t₀ ↔ P.IsEquipartition ∧ t₀ ≤ #P.parts := by
  rw [vertexCellsControlled_iff, ofFinpartition_vertexPart]

/-- Two distinct cells of the complex over a partition form an `ε`-regular pair of its pair
coloring for every `ε > 0`. -/
theorem isRegularPair_ofFinpartition_of_ne {ε : ℝ} (hε : 0 < ε) {A B : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B) :
    (ofFinpartition P).skeleton.pairColors.IsRegularPair ε A B :=
  PairColorSystem.isRegularPair_const_of_disjoint hε (P.disjoint hA hB hAB) _

/-- **Regularity of the lower skeleton.** Let `f = F (t + 1)` for the number `t` of cells of `P`,
with `f > 0`. The lower skeleton of the complex over `P` is regular for the schedule `F`
exactly when every cell has at most one vertex or more than `1 / f` vertices. -/
theorem lowerSkeletonRegular_ofFinpartition_iff {F : ℕ → ℝ} (hF : 0 < F (#P.parts + 1)) :
    (ofFinpartition P).skeleton.LowerSkeletonRegular F ↔
      ∀ A ∈ P.parts, #A ≤ 1 ∨ 1 < F (#P.parts + 1) * #A := by
  rw [PairSkeleton3.lowerSkeletonRegular_iff, ofFinpartition_vertexPart, Fintype.card_fin]
  -- The skeleton of `ofFinpartition P` is `⟨P, PairColorSystem.const 0⟩` by definition, over the
  -- palette `Fin 1`.
  exact PairSkeleton3.isPairColorRegular_const_iff (κ := Fin 1) P 0 hF

end TriadicComplex3

namespace Colored3Graph

open TriadicComplex3

variable {κ : Type*} [DecidableEq κ] {P : Finpartition (univ : Finset V)} {ε : ℝ} {F : ℕ → ℝ}
  {b : ℕ}

/-- **Schedules at least one.** Let `t` be the number of cells of `P`. If the schedule `F` is at
least one at `t + 1` and at `t + 1 + t³`, then every coloring approximates itself over the complex
with cells `P` and one pair color, at every `ε ≥ 0`, every rank schedule and every bound `b` on
the complexity `t + 1 + t³`. -/
theorem isStrongRegularApproximation3_ofFinpartition_of_one_le (H : Colored3Graph κ V)
    (hε : 0 ≤ ε) (hF : 1 ≤ F (#P.parts + 1)) (hFc : 1 ≤ F (#P.parts + 1 + #P.parts ^ 3))
    (R : ℕ → ℕ) (hb : #P.parts + 1 + #P.parts ^ 3 ≤ b) :
    H.IsStrongRegularApproximation3 H (ofFinpartition P) ε F R b where
  approximates3 := approximates3_self H hε
  isPolyadDecomposition := isPolyadDecomposition_ofFinpartition P
  lowerSkeletonRegular := by
    rw [PairSkeleton3.lowerSkeletonRegular_iff, ofFinpartition_vertexPart, Fintype.card_fin]
    exact PairSkeleton3.isPairColorRegular_of_one_le hF
  topRegularOverMostPolyads := topRegularOverMostPolyads_of_forall
    (fun Q _ ↦ isTopRegularOverPolyad_of_one_le Q H _ (complexity_ofFinpartition P ▸ hFc)) hε
  complexity_le := (complexity_ofFinpartition P).trans_le hb

/-- **A constant coloring over a single pair color.** Let `t` be the number of cells of `P`, let
`f = F (t + 1)` with `f > 0`, and let `F` be positive at `t + 1 + t³`. A constant coloring,
approximated by itself over the complex with cells `P` and one pair color, is a strong regular
approximation at every `ε ≥ 0`, every rank schedule and every bound `b ≥ t + 1 + t³` exactly when
every cell has at most one vertex or more than `1 / f` vertices. All conditions but the regularity
of the lower skeleton hold automatically. -/
theorem isStrongRegularApproximation3_const_ofFinpartition_iff (c₀ : κ) (hε : 0 ≤ ε)
    (hF : 0 < F (#P.parts + 1)) (hFc : 0 < F (#P.parts + 1 + #P.parts ^ 3)) (R : ℕ → ℕ)
    (hb : #P.parts + 1 + #P.parts ^ 3 ≤ b) :
    (const c₀ : Colored3Graph κ V).IsStrongRegularApproximation3 (const c₀) (ofFinpartition P) ε
        F R b ↔
      ∀ A ∈ P.parts, #A ≤ 1 ∨ 1 < F (#P.parts + 1) * #A := by
  rw [← lowerSkeletonRegular_ofFinpartition_iff P hF]
  refine ⟨fun h ↦ h.lowerSkeletonRegular, fun h ↦ ⟨approximates3_self _ hε,
    isPolyadDecomposition_ofFinpartition P, h, ?_, (complexity_ofFinpartition P).trans_le hb⟩⟩
  exact topRegularOverMostPolyads_const _ _ c₀ (complexity_ofFinpartition P ▸ hFc) hε

/-- **Strong regular approximation at schedules at least one.** If the schedule `F` is at least
one at `t₀ + 1` and at `t₀ + 1 + t₀³`, then every coloring of the triples of a host with at least
`t₀ > 0` vertices approximates itself over a complex with at least `t₀` equitable cells, at every
`ε ≥ 0`, every rank schedule and the complexity bound `t₀³ + t₀ + 1`. -/
theorem exists_strong_regular_approximation3_of_one_le (H : Colored3Graph κ V) {t₀ : ℕ}
    (hε : 0 ≤ ε) (hF : 1 ≤ F (t₀ + 1)) (hFc : 1 ≤ F (t₀ + 1 + t₀ ^ 3)) (R : ℕ → ℕ)
    (ht₀ : 0 < t₀) (hV : t₀ ≤ Fintype.card V) :
    ∃ C : TriadicComplex3 V, C.VertexCellsControlled t₀ ∧
      H.IsStrongRegularApproximation3 H C ε F R (t₀ ^ 3 + t₀ + 1) := by
  obtain ⟨P, hP, rfl⟩ := Finpartition.exists_equipartition_card_eq (s := (univ : Finset V))
    ht₀.ne' (by rwa [card_univ])
  exact ⟨ofFinpartition P, (vertexCellsControlled_ofFinpartition_iff P).2 ⟨hP, le_rfl⟩,
    H.isStrongRegularApproximation3_ofFinpartition_of_one_le hε hF hFc R (by omega)⟩

end Colored3Graph

end TauCeti
