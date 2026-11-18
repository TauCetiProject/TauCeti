/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PartialSups
public import TauCeti.Combinatorics.Hypergraph.PairColor.SeededRegularization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Strong pair-color regularity preserving a seed

Iterating `PairColorSystem.exists_refining_equipartition_sum_irregularPairs_le` produces a nested
pair of equipartitions `Q ≤ P ≤ P₀` refining any seed equipartition `P₀` such that the
irregular cell pairs of `Q` are controlled at the scale `F #P.parts` prescribed by an arbitrary
positive schedule `F : ℕ → ℝ` while the pair-color energy rises by at most `ε` from `P` to `Q`.

Because each round refines the previous equipartition *exact*ly (`Q ≤ P`), the coarse partition
`P` remains an exact refinement of `P₀`. Since `S.energy` lies in `[0, 1]` and is monotone under
refinement, at most `⌊1 / ε⌋₊` energy-increment rounds of size `> ε` can occur before a
witness pair `(P, Q)` is found. Taking the partial supremum `strongPairColorStepBound F` makes
one round's part-count bound monotone even when `F` is not monotone.

## Main definitions

* `TauCeti.strongPairColorStepBound`: monotone part-count bound for one round of strong pair-color
  regularization under a schedule `F`.
* `TauCeti.strongPairColorRegularityBound`: part-count bound for the coarse equipartition `P` in
  seeded strong pair-color regularity.

## Main results

* `TauCeti.PairColorSystem.exists_strong_refining_equipartitions`: every equipartition `P₀` admits
  nested equipartition refinements `Q ≤ P ≤ P₀` with bounded irregular pairs on `Q` at scale
  `F #P.parts` and energy gap `S.energy Q - S.energy P ≤ ε`.

## References

* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), Lemma 4.1.
* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006).
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset Finpartition Function

namespace TauCeti

/-- The part-count bound for one round of strong pair-color regularization from at most `m` cells:
the partial supremum of `equitablePairColorRegularityBound (F j) j` over `j ≤ m`. Taking the
partial supremum makes the bound monotone in `m` for every schedule `F`. -/
noncomputable def strongPairColorStepBound (F : ℕ → ℝ) (m : ℕ) : ℕ :=
  partialSups (fun j ↦ equitablePairColorRegularityBound (F j) j) m

/-- Unfolding lemma for `TauCeti.strongPairColorStepBound`. -/
theorem strongPairColorStepBound_def (F : ℕ → ℝ) (m : ℕ) :
    strongPairColorStepBound F m =
      partialSups (fun j ↦ equitablePairColorRegularityBound (F j) j) m :=
  (rfl)

/-- `strongPairColorStepBound` as a supremum over `Finset.range (m + 1)`. -/
theorem strongPairColorStepBound_eq_sup_range (F : ℕ → ℝ) (m : ℕ) :
    strongPairColorStepBound F m =
      (range (m + 1)).sup fun j ↦ equitablePairColorRegularityBound (F j) j :=
  partialSups_eq_sup_range _ m

/-- One round of `strongPairColorStepBound` dominates seeded pair-color regularization from any
`j ≤ m` cells. -/
theorem equitablePairColorRegularityBound_le_strongPairColorStepBound {F : ℕ → ℝ} {j m : ℕ}
    (h : j ≤ m) :
    equitablePairColorRegularityBound (F j) j ≤ strongPairColorStepBound F m :=
  le_partialSups_of_le (fun j ↦ equitablePairColorRegularityBound (F j) j) h

/-- `strongPairColorStepBound` is monotone in the starting part count. -/
theorem strongPairColorStepBound_mono (F : ℕ → ℝ) : Monotone (strongPairColorStepBound F) :=
  (partialSups fun j ↦ equitablePairColorRegularityBound (F j) j).monotone

/-- For a positive schedule `F`, `strongPairColorStepBound F` does not decrease the part count. -/
theorem le_strongPairColorStepBound {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (m : ℕ) :
    m ≤ strongPairColorStepBound F m := by
  have hm : m ≤ equitablePairColorRegularityBound (F m) m := by
    rw [equitablePairColorRegularityBound_def]
    exact (le_max_left m 1).trans
      (id_le_iterate_of_id_le (le_ceil_mul_mul_four_pow_sq (hF m)) _ _)
  exact hm.trans (equitablePairColorRegularityBound_le_strongPairColorStepBound le_rfl)

/-- Upper bound on the number of cells of the coarse equipartition in seeded strong pair-color
regularity, starting from `l₀` cells: `⌊1 / ε⌋₊` iterations of `strongPairColorStepBound F`. -/
noncomputable def strongPairColorRegularityBound (ε : ℝ) (F : ℕ → ℝ) (l₀ : ℕ) : ℕ :=
  (strongPairColorStepBound F)^[⌊1 / ε⌋₊] l₀

/-- Unfolding lemma for `TauCeti.strongPairColorRegularityBound`. -/
theorem strongPairColorRegularityBound_def (ε : ℝ) (F : ℕ → ℝ) (l₀ : ℕ) :
    strongPairColorRegularityBound ε F l₀ =
      (strongPairColorStepBound F)^[⌊1 / ε⌋₊] l₀ :=
  (rfl)

/-- `strongPairColorRegularityBound` is monotone in the starting cell count `l₀`. -/
theorem strongPairColorRegularityBound_mono (ε : ℝ) (F : ℕ → ℝ) :
    Monotone (strongPairColorRegularityBound ε F) :=
  (strongPairColorStepBound_mono F).iterate _

/-- For a positive schedule `F`, `strongPairColorRegularityBound` is at least `l₀`. -/
theorem le_strongPairColorRegularityBound (ε : ℝ) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (l₀ : ℕ) :
    l₀ ≤ strongPairColorRegularityBound ε F l₀ :=
  id_le_iterate_of_id_le (le_strongPairColorStepBound hF) _ _

namespace PairColorSystem

variable {κ V : Type*} [Fintype V] [DecidableEq V] (S : PairColorSystem κ V)

/-- **Seeded strong pair-color regularity.** For any `ε > 0`, any positive tolerance schedule
`F : ℕ → ℝ`, and any equipartition `P₀` of `V`, there exist nested equipartitions `Q ≤ P ≤ P₀`
such that `P` has at most `strongPairColorRegularityBound ε F #P₀.parts` cells, `Q` has at most
`strongPairColorStepBound F #P.parts` cells, the `F #P.parts`-irregular cell pairs of `Q` cover
at most `F #P.parts * |V|²` ordered vertex pairs, and `S.energy Q - S.energy P ≤ ε`. -/
theorem exists_strong_refining_equipartitions [Fintype κ]
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition) {ε : ℝ} (hε : 0 < ε)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) :
    ∃ P Q : Finpartition (univ : Finset V),
      Q ≤ P ∧ P ≤ P₀ ∧ P.IsEquipartition ∧ Q.IsEquipartition ∧
      #P.parts ≤ strongPairColorRegularityBound ε F #P₀.parts ∧
      #Q.parts ≤ strongPairColorStepBound F #P.parts ∧
      ∑ AB ∈ S.irregularPairs (F #P.parts) Q, (#AB.1 * #AB.2 : ℝ) ≤
        F #P.parts * (Fintype.card V : ℝ) ^ 2 ∧
      S.energy Q - S.energy P ≤ ε := by
  set step := strongPairColorStepBound F
  let Good (P : Finpartition (univ : Finset V)) : Prop :=
    ∃ Q : Finpartition (univ : Finset V), Q ≤ P ∧ Q.IsEquipartition ∧
      #Q.parts ≤ step #P.parts ∧
      ∑ AB ∈ S.irregularPairs (F #P.parts) Q, (#AB.1 * #AB.2 : ℝ) ≤
        F #P.parts * (Fintype.card V : ℝ) ^ 2 ∧
      S.energy Q - S.energy P ≤ ε
  -- One round either witnesses `Good P` or raises `S.energy` by more than `ε`.
  have advance (M : ℕ) (P : Finpartition (univ : Finset V)) (hP : P.IsEquipartition)
      (hPM : #P.parts ≤ M) :
      Good P ∨ ∃ Q : Finpartition (univ : Finset V), Q ≤ P ∧ Q.IsEquipartition ∧
        #Q.parts ≤ step M ∧ S.energy P + ε < S.energy Q := by
    obtain ⟨Q, hQP, hQ, hQcard, hQreg⟩ :=
      S.exists_refining_equipartition_sum_irregularPairs_le P hP (hF #P.parts)
    have hQstep : #Q.parts ≤ step #P.parts :=
      hQcard.trans (equitablePairColorRegularityBound_le_strongPairColorStepBound le_rfl)
    by_cases hgap : S.energy Q - S.energy P ≤ ε
    · exact Or.inl ⟨Q, hQP, hQ, hQstep, hQreg, hgap⟩
    · exact Or.inr
        ⟨Q, hQP, hQ, hQstep.trans (strongPairColorStepBound_mono F hPM), by linarith⟩
  -- After `j` rounds, either `Good` holds on a refinement of size `≤ step^[j] #P₀.parts`, or
  -- `j * ε ≤ S.energy P`.
  have key (j : ℕ) :
      (∃ P, P ≤ P₀ ∧ P.IsEquipartition ∧ #P.parts ≤ step^[j] #P₀.parts ∧ Good P) ∨
      ∃ P, P ≤ P₀ ∧ P.IsEquipartition ∧ #P.parts ≤ step^[j] #P₀.parts ∧
        j * ε ≤ S.energy P := by
    induction j with
    | zero => exact Or.inr ⟨P₀, le_rfl, hP₀, le_rfl, by simpa using S.energy_nonneg P₀⟩
    | succ j ih =>
      have hle : step^[j] #P₀.parts ≤ step^[j + 1] #P₀.parts := by
        rw [iterate_succ_apply']
        exact le_strongPairColorStepBound hF _
      obtain ⟨P, hPP₀, hP, hPcard, hgood⟩ | ⟨P, hPP₀, hP, hPcard, hE⟩ := ih
      · exact Or.inl ⟨P, hPP₀, hP, hPcard.trans hle, hgood⟩
      obtain hgood | ⟨Q, hQP, hQ, hQcard, hE'⟩ := advance _ P hP hPcard
      · exact Or.inl ⟨P, hPP₀, hP, hPcard.trans hle, hgood⟩
      refine Or.inr ⟨Q, hQP.trans hPP₀, hQ, ?_, ?_⟩
      · rwa [iterate_succ_apply']
      · push_cast; linarith
  -- Since `S.energy Q ≤ 1 < (⌊1 / ε⌋₊ + 1) * ε`, round `⌊1 / ε⌋₊` must yield a witness.
  have hK : 1 < (⌊1 / ε⌋₊ + 1 : ℕ) * ε := by
    rw [← div_lt_iff₀ hε, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  obtain ⟨P, hPP₀, hP, hPcard, Q, hQP, hQ, hQcard, hQirreg, hgap⟩ :
      ∃ P, P ≤ P₀ ∧ P.IsEquipartition ∧
        #P.parts ≤ step^[⌊1 / ε⌋₊] #P₀.parts ∧ Good P := by
    obtain hgood | ⟨P, hPP₀, hP, hPcard, hE⟩ := key ⌊1 / ε⌋₊
    · exact hgood
    obtain hgood | ⟨Q, -, -, -, hE'⟩ := advance _ P hP hPcard
    · exact ⟨P, hPP₀, hP, hPcard, hgood⟩
    push_cast at hK
    linarith [S.energy_le_one Q]
  exact ⟨P, Q, hQP, hPP₀, hP, hQ, hPcard, hQcard, hQirreg, hgap⟩

end PairColorSystem

end TauCeti
