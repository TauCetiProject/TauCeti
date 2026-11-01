/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Regularity.Graph.InducedCount
public import TauCeti.Combinatorics.Regularity.Graph.SeededRegularity
public import TauCeti.Combinatorics.Regularity.Partition.Energy
public import Mathlib.Order.PartialSups
import Mathlib.Tactic.Linarith
import TauCeti.Combinatorics.Regularity.Graph.SteppedInducedCount

/-!
# Strong graph regularity

A *strong regularity witness* for a finite graph `G` is a pair of equipartitions `Q ≤ P` (so `Q`
refines `P`) such that the coarse partition `P` is `ε`-uniform, the fine partition `Q` is uniform
at the scale `F #P.parts` prescribed by a positive schedule `F : ℕ → ℝ`, and passing from `P` to
`Q` raises the size-weighted energy `SimpleGraph.weightedEnergy` by at most `ε`. Choosing `F`
sufficiently small makes the fine partition as regular as a counting argument requires. The energy
gap controls how far the fine densities deviate from the coarse ones
(`SimpleGraph.weightedDensityDeviation_abs_le`), so counts computed on the fine partition transfer
to the coarse partition, where the number of parts is small. This is the input of the induced
counting lemma for strong regularity.

The existence theorem iterates `SimpleGraph.exists_regular_exact_refining_equipartition`. Starting
from an `ε`-uniform equipartition `P` given by `SimpleGraph.exists_regular_almostRefines_le_card`,
refine it exactly to an equipartition `Q` that is uniform at `min ε (F #P.parts)`. If the energy
rises by at most `ε`, then `(P, Q)` is a witness. Otherwise replace `P` by `Q` and repeat. The
weighted energy lies in `[0, 1]` and every unsuccessful round raises it by more than `ε`, so the
iteration stops within `⌊1 / ε⌋₊ + 1` rounds. Since every round refines exactly, the coarse
partition keeps almost refining the starting partition, and its number of parts never drops below
the requested minimum.

A strong regularity witness predicts every labelled induced three-vertex pattern from the densities
of its coarse partition (`SimpleGraph.StrongRegular.inducedGraphCount3_estimate`). With
`τ = F #P.parts`, the error is at most `(15 τ + 3 √ε) (card α) ^ 3 + 6 m (card α) ^ 2` when every
coarse part has at most `m` vertices. The fine partition counts the copies with vertices in three
distinct fine parts up to `15 τ (card α) ^ 3`, by the counting lemma for a uniform equipartition.
Passing through the stepped predictions of the fine and coarse partitions, which include the
assignments with a repeated part, the energy gap costs `3 √ε (card α) ^ 3`
(`SimpleGraph.abs_steppedInducedGraphCount3_sub_le`). The copies and assignments meeting some part
twice cost `3 m (card α) ^ 2` once for each partition.

The number of parts is bounded independently of the graph. As the schedule `F` is arbitrary, the
bound for one round is a maximum over all smaller partition sizes
(`TauCeti.strongRegularityStepBound`), which makes it monotone, and the final bound
`TauCeti.strongGraphRegularityBound` iterates it.

## Main declarations

* `TauCeti.strongRegularityStepBound`: the complexity bound for one refinement round.
* `TauCeti.strongGraphRegularityBound`: the complexity bound for the fine partition.
* `SimpleGraph.StrongRegular`: strong regularity witnesses.
* `SimpleGraph.exists_strong_regular`: every equipartition `P₀` is almost refined by the coarse
  partition of a strong regularity witness with at least a requested number of parts.
* `SimpleGraph.StrongRegular.inducedGraphCount3_estimate`: the induced counting lemma for strong
  regularity witnesses.

## References

* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006).
* Y. Zhao, *Graph Theory and Additive Combinatorics*, Cambridge University Press (2023),
  Chapter 2 (the strong regularity lemma).
-/

public section

open Finset Fintype Finpartition Function

namespace TauCeti

/-- The complexity bound for one round of strong regularity, from a partition with at most `m`
parts: the largest of the bounds `nestedRefinementBound (min ε (F j)) j` for exactly refining
regularity, over all `j ≤ m`. Taking the maximum makes the bound monotone in `m` for every
schedule `F`. -/
noncomputable def strongRegularityStepBound (ε : ℝ) (F : ℕ → ℝ) (m : ℕ) : ℕ :=
  partialSups (fun j ↦ nestedRefinementBound (min ε (F j)) j) m

/-- The bound for one round is the partial supremum of the exact-refinement bounds. -/
theorem strongRegularityStepBound_def (ε : ℝ) (F : ℕ → ℝ) (m : ℕ) :
    strongRegularityStepBound ε F m =
      partialSups (fun j ↦ nestedRefinementBound (min ε (F j)) j) m := (rfl)

/-- The bound for one round is the largest exact-refinement bound over smaller sizes. -/
theorem strongRegularityStepBound_eq_sup_range (ε : ℝ) (F : ℕ → ℝ) (m : ℕ) :
    strongRegularityStepBound ε F m =
      (range (m + 1)).sup fun j ↦ nestedRefinementBound (min ε (F j)) j :=
  partialSups_eq_sup_range _ m

variable {ε : ℝ} {F : ℕ → ℝ}

/-- The bound for one round dominates the bound for exactly refining regularity from any
partition with at most `m` parts. -/
theorem nestedRefinementBound_le_strongRegularityStepBound {j m : ℕ} (h : j ≤ m) :
    nestedRefinementBound (min ε (F j)) j ≤ strongRegularityStepBound ε F m :=
  le_partialSups_of_le (fun j ↦ nestedRefinementBound (min ε (F j)) j) h

/-- One round never needs fewer parts than it starts from. -/
theorem le_strongRegularityStepBound (m : ℕ) : m ≤ strongRegularityStepBound ε F m :=
  (le_nestedRefinementBound _ m).trans (nestedRefinementBound_le_strongRegularityStepBound le_rfl)

/-- The bound for one round is monotone in the starting number of parts. -/
theorem strongRegularityStepBound_mono : Monotone (strongRegularityStepBound ε F) :=
  (partialSups fun j ↦ nestedRefinementBound (min ε (F j)) j).monotone

/-- The complexity bound for strong graph regularity, in terms of the starting complexity `l₀`:
`⌊1 / ε⌋₊ + 1` rounds of `strongRegularityStepBound ε F`, started from the bound
`nestedRefinementBound ε (max l₀ ⌈2 * l₀ / ε⌉₊)` for a uniform equipartition with at least `l₀`
parts almost refining a partition with at most `l₀` parts. It does not depend on the graph. -/
noncomputable def strongGraphRegularityBound (ε : ℝ) (F : ℕ → ℝ) (l₀ : ℕ) : ℕ :=
  (strongRegularityStepBound ε F)^[⌊1 / ε⌋₊ + 1]
    (nestedRefinementBound ε (max l₀ ⌈2 * l₀ / ε⌉₊))

/-- The complexity bound for strong regularity iterates the bound for one round. -/
theorem strongGraphRegularityBound_def (ε : ℝ) (F : ℕ → ℝ) (l₀ : ℕ) :
    strongGraphRegularityBound ε F l₀ = (strongRegularityStepBound ε F)^[⌊1 / ε⌋₊ + 1]
      (nestedRefinementBound ε (max l₀ ⌈2 * l₀ / ε⌉₊)) := (rfl)

/-- The complexity bound for strong graph regularity is at least the starting complexity. -/
theorem le_strongGraphRegularityBound (l₀ : ℕ) : l₀ ≤ strongGraphRegularityBound ε F l₀ :=
  (le_max_left _ _).trans <| (le_nestedRefinementBound _ _).trans <|
    id_le_iterate_of_id_le le_strongRegularityStepBound _ _

end TauCeti

namespace SimpleGraph

open TauCeti

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]

/-- A **strong regularity witness** for `G`: equipartitions `Q ≤ P` (`Q` refines `P`) with `P`
`ε`-uniform, `Q` uniform at the scale `F #P.parts`, a weighted-energy gap of at most `ε` between
them, and at most `strongGraphRegularityBound ε F l₀` fine parts, a bound independent of the
graph. -/
structure StrongRegular (P Q : Finpartition (univ : Finset α)) (ε : ℝ) (F : ℕ → ℝ) (l₀ : ℕ) :
    Prop where
  /-- The fine partition refines the coarse one. -/
  refines : Q ≤ P
  /-- The coarse partition is an equipartition. -/
  equitP : P.IsEquipartition
  /-- The fine partition is an equipartition. -/
  equitQ : Q.IsEquipartition
  /-- The coarse partition is `ε`-uniform. -/
  regP : P.IsUniform G ε
  /-- The fine partition is uniform at the scale the schedule assigns to the coarse size. -/
  regQ : Q.IsUniform G (F #P.parts)
  /-- Refining the coarse partition to the fine one raises the weighted energy by at most `ε`. -/
  energyClose : G.weightedEnergy Q - G.weightedEnergy P ≤ ε
  /-- The number of fine parts is bounded independently of the graph. -/
  boundedFine : #Q.parts ≤ strongGraphRegularityBound ε F l₀

/-- **Strong graph regularity.** Let `ε > 0` and let `F : ℕ → ℝ` be a positive schedule. Every
equipartition `P₀` of a finite graph `G` is almost refined, up to `ε`, by the coarse partition `P`
of a strong regularity witness `(P, Q)`, where `P` has at least `l` parts for any requested
`l ≤ card α`, and `Q` has at most `strongGraphRegularityBound ε F (max l #P₀.parts)` parts. -/
theorem exists_strong_regular (P₀ : Finpartition (univ : Finset α)) (hP₀ : P₀.IsEquipartition)
    {l : ℕ} (hl : l ≤ card α) {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) :
    ∃ P Q : Finpartition (univ : Finset α), G.StrongRegular P Q ε F (max l #P₀.parts) ∧
      P.AlmostRefines P₀ ε ∧ l ≤ #P.parts := by
  set L := nestedRefinementBound ε (max (max l #P₀.parts) ⌈2 * (max l #P₀.parts : ℕ) / ε⌉₊)
  set g := strongRegularityStepBound ε F
  obtain ⟨P₁, hP₁, hP₁G, hP₁P₀, hlP₁, hP₁card⟩ :=
    G.exists_regular_almostRefines_le_card P₀ hP₀ hl hε
  -- One round refines an equipartition `P` exactly to a `min ε (F #P.parts)`-uniform one.
  have step (P : Finpartition (univ : Finset α)) (hP : P.IsEquipartition) :
      ∃ Q : Finpartition (univ : Finset α), Q ≤ P ∧ Q.IsEquipartition ∧
        Q.IsUniform G (min ε (F #P.parts)) ∧ #Q.parts ≤ g #P.parts := by
    obtain ⟨Q, hQP, hQ, hQG, hQcard⟩ :=
      G.exists_regular_exact_refining_equipartition P hP (lt_min hε (hF _))
    exact ⟨Q, hQP, hQ, hQG,
      hQcard.trans (nestedRefinementBound_le_strongRegularityStepBound le_rfl)⟩
  -- After `i + 1` rounds there is a candidate pair `(P, Q)` whose energy gap is at most `ε`, or
  -- whose fine energy exceeds `ε * (i + 1)`.
  have key (i : ℕ) : ∃ P Q : Finpartition (univ : Finset α), Q ≤ P ∧ P.IsEquipartition ∧
      Q.IsEquipartition ∧ P.IsUniform G ε ∧ Q.IsUniform G (min ε (F #P.parts)) ∧
      P.AlmostRefines P₀ ε ∧ l ≤ #P.parts ∧ #Q.parts ≤ g^[i + 1] L ∧
      (G.weightedEnergy Q - G.weightedEnergy P ≤ ε ∨ ε * (i + 1) < G.weightedEnergy Q) := by
    induction i with
    | zero =>
      obtain ⟨Q, hQP, hQ, hQG, hQcard⟩ := step P₁ hP₁
      refine ⟨P₁, Q, hQP, hP₁, hQ, hP₁G, hQG, hP₁P₀, hlP₁,
        hQcard.trans (strongRegularityStepBound_mono hP₁card), (le_or_gt _ ε).imp id fun h ↦ ?_⟩
      have := G.weightedEnergy_nonneg P₁
      push_cast
      linarith
    | succ i ih =>
      obtain ⟨P, Q, hQP, hP, hQ, hPG, hQG, hPP₀, hlP, hQcard, hgap⟩ := ih
      have hgi : g^[i + 1] L ≤ g^[i + 1 + 1] L := by
        rw [iterate_succ_apply' g (i + 1)]
        exact le_strongRegularityStepBound _
      -- A pair with a small energy gap is kept; otherwise its fine partition becomes coarse.
      by_cases hclose : G.weightedEnergy Q - G.weightedEnergy P ≤ ε
      · exact ⟨P, Q, hQP, hP, hQ, hPG, hQG, hPP₀, hlP, hQcard.trans hgi, Or.inl hclose⟩
      replace hgap := hgap.resolve_left hclose
      obtain ⟨R, hRQ, hR, hRG, hRcard⟩ := step Q hQ
      refine ⟨Q, R, hRQ, hQ, hR, hQG.mono (min_le_left _ _), hRG, hPP₀.mono_left hQP,
        hlP.trans (card_mono hQP), ?_, (le_or_gt _ ε).imp id fun h ↦ ?_⟩
      · rw [iterate_succ_apply' g (i + 1)]
        exact hRcard.trans (strongRegularityStepBound_mono hQcard)
      · push_cast
        linarith
  -- Energies are at most `1`, so after `⌊1 / ε⌋₊ + 1` rounds the energy gap is at most `ε`.
  obtain ⟨P, Q, hQP, hP, hQ, hPG, hQG, hPP₀, hlP, hQcard, hgap⟩ := key ⌊1 / ε⌋₊
  have hclose : G.weightedEnergy Q - G.weightedEnergy P ≤ ε := hgap.resolve_right fun h ↦ by
    have hN : 1 / ε < ⌊1 / ε⌋₊ + 1 := Nat.lt_floor_add_one _
    have h1 : 1 < ε * (⌊1 / ε⌋₊ + 1) := by
      rwa [div_lt_iff₀ hε, mul_comm] at hN
    linarith [G.weightedEnergy_le_one Q]
  exact ⟨P, Q, ⟨hQP, hP, hQ, hPG, hQG.mono (min_le_right _ _), hclose, hQcard⟩, hPP₀, hlP⟩

variable {G} in
/-- **Induced counting lemma for strong regularity.** Let `(P, Q)` be a strong regularity witness
for `G` with `τ = F #P.parts > 0`, and suppose every part of `P` has at most `m` vertices. Then for
every graph `J` on `Fin 3`, the number of labelled induced copies of `J` in `G` differs from the
coarse prediction `J.coarseInducedGraphEstimate G P` by at most
`(15 τ + 3 √ε) (card α) ^ 3 + 6 m (card α) ^ 2`. Only the refinement, the equitability and
uniformity of `Q`, and the energy gap are used. -/
theorem StrongRegular.inducedGraphCount3_estimate (J : SimpleGraph (Fin 3)) [DecidableRel J.Adj]
    {P Q : Finpartition (univ : Finset α)} {ε : ℝ} {F : ℕ → ℝ} {l₀ : ℕ}
    (h : G.StrongRegular P Q ε F l₀) (hF : 0 < F #P.parts) {m : ℕ}
    (hm : ∀ A ∈ P.parts, #A ≤ m) :
    |(J.inducedGraphCount3 G : ℝ) - J.coarseInducedGraphEstimate G P| ≤
      (15 * F #P.parts + 3 * √ε) * card α ^ 3 + 6 * m * card α ^ 2 := by
  have hmQ : ∀ B ∈ Q.parts, #B ≤ m := fun B hB ↦ by
    obtain ⟨A, hA, hBA⟩ := h.refines hB
    exact (card_le_card hBA).trans (hm A hA)
  -- Compare the count with the coarse prediction of `Q`, then pass through the stepped
  -- predictions of `Q` and `P` to the coarse prediction of `P`.
  have h₁ := J.inducedGraphCount3_le_coarseInducedGraphEstimate_add G h.equitQ hF h.regQ hmQ
  have h₂ := J.coarseInducedGraphEstimate_sub_le_inducedGraphCount3 G h.equitQ hF h.regQ
  have h₃ := J.coarseInducedGraphEstimate_le_steppedInducedGraphCount3 G Q
  have h₄ := J.steppedInducedGraphCount3_le_coarseInducedGraphEstimate_add G Q hmQ
  have h₅ := abs_le.1 (J.abs_steppedInducedGraphCount3_sub_le G h.refines h.energyClose)
  have h₆ := J.coarseInducedGraphEstimate_le_steppedInducedGraphCount3 G P
  have h₇ := J.steppedInducedGraphCount3_le_coarseInducedGraphEstimate_add G P hm
  rw [abs_le]
  constructor <;> linarith [h₅.1, h₅.2]

end SimpleGraph
