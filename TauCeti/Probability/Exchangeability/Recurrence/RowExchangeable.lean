/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.DiaconisFreedman
public import TauCeti.Probability.Exchangeability.Recurrence.LastExit
-- Non-public: finite-dimensional determinacy of a law is used only inside the proofs below.
import Mathlib.Probability.Process.FiniteDimensionalLaws
-- Non-public: the convergence of masses of eventually coinciding events is used only in a proof.
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# The successor array of a Markov exchangeable process is row exchangeable

Diaconis and Freedman represent a recurrent Markov exchangeable process as a mixture of Markov
chains by passing to its **successor array**, whose `(a, k)`-entry is the state reached right after
the `k`-th visit to `a`. `TauCeti/Probability/Exchangeability/DiaconisFreedman.lean` supplies the
change of variables that turns a row exchangeable array recording those successors back into a
mixture of Markov chains. This file supplies the missing hypothesis of that change of variables:
for a recurrent Markov exchangeable process, the **visited successor array**
`TauCeti.Probability.visitedSuccessorProcess`, whose rows at unvisited states are constant, is row
exchangeable, and the Diaconis--Freedman representation follows.

## The argument

Permuting the entries of each row and following the reordered rows rebuilds a finite path with the
same initial state and the same transition counts, provided the permutations obey the last-exit
condition — that is what `TauCeti.pathOfReindexedSuccessors` and the finite reconstruction lemmas
of `TauCeti/Combinatorics/Enumerative/LastExit.lean` establish. Markov exchangeability equates the
masses of two such words, so a prefix law is invariant under a last-exit-admissible reindexing
(`TauCeti.Probability.MarkovExchangeable.measure_setOf_eqOn_pathOfReindexedSuccessors`).

Row exchangeability is the limit of that finite statement. Fix a finitely supported family of row
permutations and a finite family of cells. Over a horizon at which every relevant row the prefix
visits has consumed its relevant cells, a last-exit reindexing is legitimate, and the
reconstruction pairs the prefixes realizing the reindexed cell values with those realizing the
original ones. Along a recurrent path each relevant row is either never visited or visited
infinitely often, so every long enough prefix is such a horizon and reads the visited successor
array at those cells correctly; the masses of the prefix events therefore converge to the mass of
the array event.

## Why the unvisited rows are reset

`TauCeti/Probability/Exchangeability/Recurrence/UnvisitedRow.lean` exhibits a recurrent Markov
exchangeable process whose plain successor array is *not* row exchangeable: an unattained state
has junk visit times, so its whole row is tied to the cell `(x 0, 0)`, and permuting the row of
`x 0` breaks the tie. Recurrence constrains only the states a process does attain, so for the plain
array one needs every state to be attained
(`TauCeti.Probability.MarkovExchangeable.rowExchangeable_successorProcess`). The visited successor
array agrees with the successor array on every visited row, which is all the change of variables
reads, and carries no such tie.

## Main results

* `TauCeti.Probability.MarkovExchangeable.measure_setOf_eqOn_pathOfReindexedSuccessors` — a finite
  path and its last-exit reconstruction are equally likely.
* `TauCeti.Probability.MarkovExchangeable.rowExchangeable_visitedSuccessorProcess` — **the visited
  successor array of a recurrent Markov exchangeable process is row exchangeable.**
* `TauCeti.Probability.MarkovExchangeable.rowExchangeable_successorProcess` — the plain successor
  array is row exchangeable when every state is almost surely attained.
* `TauCeti.Probability.MarkovExchangeable.mixedMarkovChain` — **the Diaconis--Freedman
  representation**: a recurrent Markov exchangeable process started at a fixed state is a mixture
  of Markov chains.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115--130.
* S. Fortini, L. Ladelli, G. Petris, and E. Regazzini, "On mixtures of distributions of Markov
  chains", *Stochastic Processes and their Applications* 100 (2002), 147--165, Lemma 1(b).
-/

public section

noncomputable section

open Filter MeasureTheory Topology

namespace TauCeti

namespace Probability

section Words

variable {α : Type*} {m : ℕ}

/-- A finite path word read as a sequence, by repeating its last letter forever. -/
private def wordSeq (u : Fin (m + 1) → α) : ℕ → α :=
  fun j => u (Fin.clamp j m)

private theorem wordSeq_apply (u : Fin (m + 1) → α) (j : ℕ) :
    wordSeq u j = u (Fin.clamp j m) :=
  rfl

private theorem wordSeq_of_le (u : Fin (m + 1) → α) {i : ℕ} (hi : i ≤ m) :
    wordSeq u i = u ⟨i, Nat.lt_succ_of_le hi⟩ := by
  rw [wordSeq_apply]
  exact congrArg u (Fin.ext ((Fin.coe_clamp i m).trans (Nat.min_eq_left hi)))

private theorem wordSeq_val (u : Fin (m + 1) → α) (i : Fin (m + 1)) : wordSeq u i.val = u i := by
  rw [wordSeq_of_le u (Nat.lt_succ_iff.1 i.isLt)]

private theorem wordSeq_comp (u : Fin (m + 1) → α) :
    (fun i : Fin (m + 1) => wordSeq u i.val) = u :=
  funext (wordSeq_val u)

/-- A finite path word rebuilt after reindexing each row of its successor array. -/
private def reindexWord (π : α → Equiv.Perm ℕ) (m : ℕ) (u : Fin (m + 1) → α) : Fin (m + 1) → α :=
  fun i => pathOfReindexedSuccessors π (wordSeq u) i.val

private theorem reindexWord_apply (π : α → Equiv.Perm ℕ) (u : Fin (m + 1) → α)
    (i : Fin (m + 1)) :
    reindexWord π m u i = pathOfReindexedSuccessors π (wordSeq u) i.val :=
  rfl

private theorem wordSeq_reindexWord (π : α → Equiv.Perm ℕ) (u : Fin (m + 1) → α) {i : ℕ}
    (hi : i ≤ m) : wordSeq (reindexWord π m u) i = pathOfReindexedSuccessors π (wordSeq u) i := by
  rw [wordSeq_of_le _ hi, reindexWord_apply]

private theorem visitCount_wordSeq_reindexWord {π : α → Equiv.Perm ℕ} {u : Fin (m + 1) → α}
    (h : LastExitAdmissible π (wordSeq u) m) (a : α) :
    visitCount (wordSeq (reindexWord π m u)) a m = visitCount (wordSeq u) a m := by
  rw [visitCount_congr (y := pathOfReindexedSuccessors π (wordSeq u))
      fun _ hj => wordSeq_reindexWord π u hj.le]
  exact visitCount_pathOfReindexedSuccessors π (wordSeq u) m h a

private theorem reindexWord_symm_reindexWord {π : α → Equiv.Perm ℕ} {u : Fin (m + 1) → α}
    (h : LastExitAdmissible π (wordSeq u) m) :
    reindexWord (fun a => (π a).symm) m (reindexWord π m u) = u := by
  funext i
  have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.1 i.isLt
  have hcongr := pathOfReindexedSuccessors_congr (π := fun a => (π a).symm)
    h.symm_pathOfReindexedSuccessors (fun j hj => (wordSeq_reindexWord π u hj).symm) i.val hi
  rw [reindexWord_apply, ← hcongr, pathOfReindexedSuccessors_symm_apply_apply h hi, wordSeq_val]

private theorem reindexWord_zero (π : α → Equiv.Perm ℕ) (u : Fin (m + 1) → α) :
    reindexWord π m u 0 = u 0 := by
  rw [reindexWord_apply, Fin.val_zero, pathOfReindexedSuccessors_zero]
  exact wordSeq_of_le u (Nat.zero_le m)

private theorem transitionCount_reindexWord {π : α → Equiv.Perm ℕ} {u : Fin (m + 1) → α}
    (h : LastExitAdmissible π (wordSeq u) m) (a b : α) :
    transitionCount (reindexWord π m u) a b = transitionCount u a b := by
  have hmain := transitionCount_pathOfReindexedSuccessors π (wordSeq u) m h a b
  rwa [wordSeq_comp u] at hmain

private theorem successorArray_wordSeq_reindexWord {π : α → Equiv.Perm ℕ} {u : Fin (m + 1) → α}
    (h : LastExitAdmissible π (wordSeq u) m) {a : α} {k : ℕ}
    (hk : k < visitCount (wordSeq u) a m) :
    successorArray (wordSeq (reindexWord π m u)) a k = successorArray (wordSeq u) a (π a k) := by
  have hk' : k < visitCount (pathOfReindexedSuccessors π (wordSeq u)) a m := by
    rwa [visitCount_pathOfReindexedSuccessors π (wordSeq u) m h a]
  have hshift : successorArray (pathOfReindexedSuccessors π (wordSeq u)) a k
      = successorArray (wordSeq (reindexWord π m u)) a k :=
    successorArray_congr (m := m) (fun j hj => (wordSeq_reindexWord π u hj).symm) hk'
  rw [← hshift]
  exact successorArray_pathOfReindexedSuccessors_of_lt_visitCount π (wordSeq u) a hk'

/-- A word visits a letter exactly when its visit count through its last letter is positive. -/
private theorem exists_wordSeq_eq_iff (u : Fin (m + 1) → α) (a : α) :
    (∃ n, wordSeq u n = a) ↔ 0 < visitCount (wordSeq u) a (m + 1) :=
  Iff.trans ⟨fun ⟨n, hn⟩ => ⟨Fin.clamp n m, (Fin.clamp n m).isLt, (wordSeq_val u _).trans hn⟩,
    fun ⟨i, _, hi⟩ => ⟨i, hi⟩⟩ visitCount_pos_iff.symm

/-- A last-exit reindexing keeps the visit counts of a word through its last letter, since it keeps
both the counts before the last letter and the last letter itself. -/
private theorem visitCount_succ_wordSeq_reindexWord {π : α → Equiv.Perm ℕ} {u : Fin (m + 1) → α}
    (h : LastExitAdmissible π (wordSeq u) m) (a : α) :
    visitCount (wordSeq (reindexWord π m u)) a (m + 1) = visitCount (wordSeq u) a (m + 1) := by
  classical
  have hlast : wordSeq (reindexWord π m u) m = wordSeq u m := by
    rw [wordSeq_reindexWord π u le_rfl, pathOfReindexedSuccessors_eq π (wordSeq u) m h]
  rw [visitCount_succ, visitCount_succ, hlast, visitCount_wordSeq_reindexWord h]

private theorem visitedSuccessorArray_wordSeq_reindexWord {π : α → Equiv.Perm ℕ}
    {u : Fin (m + 1) → α} (h : LastExitAdmissible π (wordSeq u) m) {a : α} {k : ℕ}
    (hk : k < visitCount (wordSeq u) a m) :
    visitedSuccessorArray (wordSeq (reindexWord π m u)) a k =
      visitedSuccessorArray (wordSeq u) a (π a k) := by
  have hpos : 0 < visitCount (wordSeq u) a (m + 1) :=
    (Nat.zero_lt_of_lt hk).trans_le (visitCount_monotone _ a (Nat.le_succ m))
  rw [visitedSuccessorArray_of_exists ((exists_wordSeq_eq_iff _ a).2
      ((visitCount_succ_wordSeq_reindexWord h a).symm ▸ hpos)),
    visitedSuccessorArray_of_exists ((exists_wordSeq_eq_iff u a).2 hpos)]
  exact successorArray_wordSeq_reindexWord h hk

/-- The words over which a last-exit reindexing by `π` is legitimate and the entries of the visited
successor array at the cells of `F` are determined: every row that the word visits and that
carries a cell moved by `π` or a cell of `F` has already consumed that cell and its `π`-image. -/
private def HorizonWords (π : α → Equiv.Perm ℕ) (F : Finset (α × ℕ)) (m : ℕ) :
    Set (Fin (m + 1) → α) :=
  {u | ∀ p : α × ℕ, π p.1 p.2 ≠ p.2 ∨ p ∈ F →
    visitCount (wordSeq u) p.1 (m + 1) = 0 ∨
      (p.2 + 1 < visitCount (wordSeq u) p.1 m ∧ π p.1 p.2 + 1 < visitCount (wordSeq u) p.1 m)}

/-- The words whose visited successor array takes the values `g` at the cells of `F` reindexed by
`ρ`. -/
private def CellWords (ρ : α → ℕ → ℕ) (F : Finset (α × ℕ)) (m : ℕ) (g : F → α) :
    Set (Fin (m + 1) → α) :=
  {u | ∀ p : F,
    visitedSuccessorArray (wordSeq u) (p : α × ℕ).1 (ρ (p : α × ℕ).1 (p : α × ℕ).2) = g p}

variable {π : α → Equiv.Perm ℕ} {F : Finset (α × ℕ)} {g : F → α} {u : Fin (m + 1) → α}

/-- On a horizon word, a row with a visit before the last letter has consumed its relevant cells. -/
private theorem lt_visitCount_of_mem_horizonWords (hu : u ∈ HorizonWords π F m) {p : α × ℕ}
    (hp : π p.1 p.2 ≠ p.2 ∨ p ∈ F) (hpos : 0 < visitCount (wordSeq u) p.1 m) :
    p.2 + 1 < visitCount (wordSeq u) p.1 m ∧ π p.1 p.2 + 1 < visitCount (wordSeq u) p.1 m := by
  refine (hu p hp).resolve_left fun h0 => ?_
  have := visitCount_monotone (wordSeq u) p.1 (Nat.le_add_right m 1)
  omega

private theorem lastExitAdmissible_of_mem_horizonWords (hu : u ∈ HorizonWords π F m) :
    LastExitAdmissible π (wordSeq u) m :=
  lastExitAdmissible_of_support_lt_visitCount fun a ha k hk =>
    (lt_visitCount_of_mem_horizonWords hu (p := (a, k)) (Or.inl hk) ha).1

private theorem lastExitAdmissible_symm_of_mem_horizonWords (hu : u ∈ HorizonWords π F m) :
    LastExitAdmissible (fun a => (π a).symm) (wordSeq u) m := by
  refine lastExitAdmissible_of_support_lt_visitCount fun a ha k hk =>
    (lt_visitCount_of_mem_horizonWords hu (p := (a, k)) (Or.inl ?_) ha).1
  exact fun hfix => hk ((Equiv.symm_apply_eq _).2 hfix.symm)

private theorem reindexWord_mem_horizonWords {ρ : α → Equiv.Perm ℕ}
    (hu : u ∈ HorizonWords π F m) (hρ : LastExitAdmissible ρ (wordSeq u) m) :
    reindexWord ρ m u ∈ HorizonWords π F m := by
  intro p hp
  rw [visitCount_wordSeq_reindexWord hρ, visitCount_succ_wordSeq_reindexWord hρ]
  exact hu p hp

private theorem visitedSuccessorArray_reindexWord_cell (hu : u ∈ HorizonWords π F m) (p : F) :
    visitedSuccessorArray (wordSeq (reindexWord π m u)) (p : α × ℕ).1 (p : α × ℕ).2
      = visitedSuccessorArray (wordSeq u) (p : α × ℕ).1 (π (p : α × ℕ).1 (p : α × ℕ).2) := by
  have hadm := lastExitAdmissible_of_mem_horizonWords hu
  rcases Nat.eq_zero_or_pos (visitCount (wordSeq u) (p : α × ℕ).1 m) with h0 | hpos
  · -- A row not visited before the last letter holds no consumed cell of `F`, so it is unvisited.
    have hunv : visitCount (wordSeq u) (p : α × ℕ).1 (m + 1) = 0 := by
      refine (hu (p : α × ℕ) (Or.inr p.2)).resolve_right fun h => ?_
      omega
    have hne : ∀ v : Fin (m + 1) → α, visitCount (wordSeq v) (p : α × ℕ).1 (m + 1) = 0 →
        ∀ n, wordSeq v n ≠ (p : α × ℕ).1 := fun v hv n hn => by
      have := (exists_wordSeq_eq_iff v _).1 ⟨n, hn⟩
      omega
    rw [visitedSuccessorArray_of_forall_ne (hne u hunv),
      visitedSuccessorArray_of_forall_ne (hne _ ((visitCount_succ_wordSeq_reindexWord hadm _).trans
        hunv))]
  · exact visitedSuccessorArray_wordSeq_reindexWord hadm
      (by have := (lt_visitCount_of_mem_horizonWords hu (Or.inr p.2) hpos).1; omega)

private theorem reindexWord_reindexWord_symm (hu : u ∈ HorizonWords π F m) :
    reindexWord π m (reindexWord (fun a => (π a).symm) m u) = u := by
  have hmain := reindexWord_symm_reindexWord (π := fun a => (π a).symm)
    (lastExitAdmissible_symm_of_mem_horizonWords hu)
  simpa only [Equiv.symm_symm] using hmain

/-- **The last-exit reconstruction pairs the words realizing the reindexed cell values with those
realizing the original ones.** -/
private def reindexEquiv (π : α → Equiv.Perm ℕ) (F : Finset (α × ℕ)) (m : ℕ) (g : F → α) :
    (HorizonWords π F m ∩ CellWords (fun a k => π a k) F m g : Set (Fin (m + 1) → α)) ≃
      (HorizonWords π F m ∩ CellWords (fun _ k => k) F m g : Set (Fin (m + 1) → α)) where
  toFun u := ⟨reindexWord π m u.1,
    reindexWord_mem_horizonWords u.2.1 (lastExitAdmissible_of_mem_horizonWords u.2.1),
    fun p => (visitedSuccessorArray_reindexWord_cell u.2.1 p).trans (u.2.2 p)⟩
  invFun v := ⟨reindexWord (fun a => (π a).symm) m v.1,
    reindexWord_mem_horizonWords v.2.1 (lastExitAdmissible_symm_of_mem_horizonWords v.2.1),
    fun p => by
      have hmem := reindexWord_mem_horizonWords (ρ := fun a => (π a).symm) v.2.1
        (lastExitAdmissible_symm_of_mem_horizonWords v.2.1)
      have hcell := visitedSuccessorArray_reindexWord_cell hmem p
      rw [reindexWord_reindexWord_symm v.2.1] at hcell
      exact hcell.symm.trans (v.2.2 p)⟩
  left_inv u :=
    Subtype.ext (reindexWord_symm_reindexWord (lastExitAdmissible_of_mem_horizonWords u.2.1))
  right_inv v := Subtype.ext (reindexWord_reindexWord_symm v.2.1)

/-- **Along a recurrent sequence, the horizon cell words of its prefixes eventually describe the
visited successor array itself.** Each relevant row is either never visited, and then no prefix
visits it, or visited infinitely often, and then every long enough prefix has consumed its relevant
cells; either way the prefix reads the visited successor array at the cells of `F` correctly. -/
private theorem eventually_prefix_mem_iff {x : ℕ → α} (hio : ∀ k, {n | x n = x k}.Infinite)
    (hπ : {p : α × ℕ | π p.1 p.2 ≠ p.2}.Finite) {ρ : α → ℕ → ℕ}
    (hρ : ∀ p : F, ρ (p : α × ℕ).1 (p : α × ℕ).2 = (p : α × ℕ).2 ∨
      ρ (p : α × ℕ).1 (p : α × ℕ).2 = π (p : α × ℕ).1 (p : α × ℕ).2) :
    ∀ᶠ m in atTop, (fun i : Fin (m + 1) => x i.val) ∈ HorizonWords π F m ∩ CellWords ρ F m g ↔
      ∀ p : F, visitedSuccessorArray x (p : α × ℕ).1 (ρ (p : α × ℕ).1 (p : α × ℕ).2) = g p := by
  have hfin : {p : α × ℕ | π p.1 p.2 ≠ p.2 ∨ p ∈ F}.Finite :=
    (hπ.union F.finite_toSet).subset fun _ hp => hp
  have hev : ∀ᶠ m : ℕ in atTop, ∀ p ∈ {p : α × ℕ | π p.1 p.2 ≠ p.2 ∨ p ∈ F},
      (∀ n, x n ≠ p.1) ∨ (p.2 + 1 < visitCount x p.1 m ∧ π p.1 p.2 + 1 < visitCount x p.1 m) := by
    refine hfin.eventually_all.2 fun p _ => ?_
    by_cases hvis : ∃ n, x n = p.1
    · obtain ⟨n, hn⟩ := hvis
      obtain ⟨j, -, hj⟩ := exists_visitCount_of_infinite (hn ▸ hio n)
        (max (p.2 + 2) (π p.1 p.2 + 2))
      refine eventually_atTop.2 ⟨j, fun m hjm => Or.inr ?_⟩
      have := visitCount_monotone x p.1 hjm
      omega
    · exact Eventually.of_forall fun _ => Or.inl (not_exists.1 hvis)
  filter_upwards [hev] with m hm
  set u : Fin (m + 1) → α := fun i => x i.val
  have hxu : ∀ i ≤ m, x i = wordSeq u i := fun i hi => (wordSeq_of_le u hi).symm
  have hvc : ∀ a : α, visitCount (wordSeq u) a m = visitCount x a m :=
    fun a => visitCount_congr fun i hi => (hxu i hi.le).symm
  have hunv : ∀ a : α, (∀ n, x n ≠ a) → ∀ n, wordSeq u n ≠ a :=
    fun a ha n => by rw [wordSeq_apply]; exact ha _
  have hhor : u ∈ HorizonWords π F m := by
    intro p hp
    rcases hm p hp with ha | ha
    · exact Or.inl (visitCount_eq_zero_of_forall_ne fun i _ => hunv p.1 ha i)
    · exact Or.inr (by rw [hvc]; exact ha)
  have hcell : ∀ p : F,
      visitedSuccessorArray (wordSeq u) (p : α × ℕ).1 (ρ (p : α × ℕ).1 (p : α × ℕ).2) =
        visitedSuccessorArray x (p : α × ℕ).1 (ρ (p : α × ℕ).1 (p : α × ℕ).2) := by
    intro p
    rcases hm (p : α × ℕ) (Or.inr p.2) with ha | ha
    · rw [visitedSuccessorArray_of_forall_ne ha, visitedSuccessorArray_of_forall_ne (hunv _ ha)]
    · refine (visitedSuccessorArray_congr hxu ?_).symm
      rcases hρ p with hr | hr <;> rw [hr] <;> omega
  simp only [Set.mem_inter_iff, CellWords, Set.mem_ofPred_eq, hcell]
  exact and_iff_right hhor

end Words

section Prefix

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω} {X : ℕ → Ω → α}

/-- A finite path event of the process is a prefix-law singleton: the bounded-`ℕ` reading of
`TauCeti.Probability.prefixLaw_singleton_eq_measure`. -/
private theorem measure_setOf_eqOn [MeasurableSingletonClass α]
    (hX : ∀ i, AEMeasurable (X i) μ) (w : ℕ → α) (m : ℕ) :
    μ {ω | ∀ i ≤ m, X i ω = w i} = prefixLaw μ X (m + 1) {fun i : Fin (m + 1) => w i.val} := by
  rw [prefixLaw_singleton_eq_measure hX]
  exact congrArg μ (Set.ext fun ω =>
    ⟨fun hω i => hω i.val (Nat.lt_succ_iff.1 i.isLt),
      fun hω i hi => hω ⟨i, Nat.lt_succ_of_le hi⟩⟩)

/-- **A finite path and its last-exit reconstruction are equally likely under a Markov
exchangeable process.** Rebuilding a prefix from row-permuted successor entries preserves the
initial state and every transition count, so Markov exchangeability equates the two masses.

This is the probabilistic half of the successor-array argument; the finite reconstruction itself
is `TauCeti.pathOfReindexedSuccessors`. -/
theorem MarkovExchangeable.measure_setOf_eqOn_pathOfReindexedSuccessors
    (h : MarkovExchangeable μ X) {π : α → Equiv.Perm ℕ} {w : ℕ → α} {m : ℕ}
    (hadm : LastExitAdmissible π w m) :
    μ {ω | ∀ i ≤ m, X i ω = pathOfReindexedSuccessors π w i} = μ {ω | ∀ i ≤ m, X i ω = w i} := by
  have := h.countable
  have := h.measurableSingletonClass
  set u : Fin (m + 1) → α := fun i : Fin (m + 1) => w i.val
  have hws : ∀ i ≤ m, w i = wordSeq u i := fun i hi => (wordSeq_of_le u hi).symm
  have hadm' : LastExitAdmissible π (wordSeq u) m := hadm.congr hws
  have hre : (fun i : Fin (m + 1) => pathOfReindexedSuccessors π w i.val) = reindexWord π m u :=
    funext fun i =>
      pathOfReindexedSuccessors_congr hadm hws i.val (Nat.lt_succ_iff.1 i.isLt)
  rw [measure_setOf_eqOn h.aemeasurable _ m, measure_setOf_eqOn h.aemeasurable _ m, hre]
  exact h.prefixLaw_singleton_eq m _ u (reindexWord_zero π u)
    (transitionCount_reindexWord hadm')

end Prefix

section Representation

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω} {X : ℕ → Ω → α}

/-- Over each horizon, the words realizing the reindexed cell values and those realizing the
original ones have the same prefix-law mass: the last-exit reconstruction pairs them. -/
private theorem prefixLaw_horizonWords_inter_cellWords (h : MarkovExchangeable μ X)
    (π : α → Equiv.Perm ℕ) (F : Finset (α × ℕ)) (m : ℕ) (g : F → α) :
    prefixLaw μ X (m + 1) (HorizonWords π F m ∩ CellWords (fun a k => π a k) F m g)
      = prefixLaw μ X (m + 1) (HorizonWords π F m ∩ CellWords (fun _ k => k) F m g) :=
  h.prefixLaw_apply_eq_of_equiv m (reindexEquiv π F m g)
    (fun w => reindexWord_zero π w.1)
    (fun w => transitionCount_reindexWord (lastExitAdmissible_of_mem_horizonWords w.2.1))

/-- **The mass of an event of the visited successor array is the limit of the masses of its
horizon prefix events**, because along almost every path of a recurrent process those events
eventually coincide with it. -/
private theorem tendsto_prefixLaw_horizonWords_inter_cellWords [IsFiniteMeasure μ]
    (h : MarkovExchangeable μ X) (hrec : Recurrent μ X) {π : α → Equiv.Perm ℕ}
    (hπ : {p : α × ℕ | π p.1 p.2 ≠ p.2}.Finite) {F : Finset (α × ℕ)} {g : F → α}
    {ρ : α → ℕ → ℕ} (hρ : ∀ p : F, ρ (p : α × ℕ).1 (p : α × ℕ).2 = (p : α × ℕ).2 ∨
      ρ (p : α × ℕ).1 (p : α × ℕ).2 = π (p : α × ℕ).1 (p : α × ℕ).2) :
    Tendsto (fun m => prefixLaw μ X (m + 1) (HorizonWords π F m ∩ CellWords ρ F m g)) atTop
      (𝓝 (μ {ω | ∀ p : F, visitedSuccessorArray (fun n => X n ω) (p : α × ℕ).1
        (ρ (p : α × ℕ).1 (p : α × ℕ).2) = g p})) := by
  have := h.countable
  have := h.measurableSingletonClass
  have hΦ : AEMeasurable (fun ω n => X n ω) μ := AEMeasurable.of_eval h.aemeasurable
  -- Almost every path of the process revisits each of its states infinitely often.
  have hio : ∀ᵐ x ∂(μ.map fun ω n => X n ω), ∀ k, {n | x n = x k}.Infinite := by
    have hpath := ((recurrent_pathLaw_iff h.aemeasurable).2 hrec).ae_infinite_setOf_eq
    rwa [pathLaw_def] at hpath
  have hcell : MeasurableSet {x : ℕ → α | ∀ p : F,
      visitedSuccessorArray x (p : α × ℕ).1 (ρ (p : α × ℕ).1 (p : α × ℕ).2) = g p} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun p => measurable_visitedSuccessorArray_apply _ _
      (measurableSet_singleton _) (measurableSet_singleton _)
  have hpre : ∀ m, MeasurableSet ((fun (x : ℕ → α) (i : Fin (m + 1)) => x i.val) ⁻¹'
      (HorizonWords π F m ∩ CellWords ρ F m g)) := fun m =>
    (Measurable.of_eval fun i => measurable_pi_apply _) MeasurableSet.of_discrete
  have hlim := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop hcell hpre
    (hio.mono fun x hx => eventually_prefix_mem_iff hx hπ hρ)
  rw [Measure.map_apply_of_aemeasurable hΦ hcell] at hlim
  refine hlim.congr fun m => ?_
  rw [Measure.map_apply_of_aemeasurable hΦ (hpre m), prefixLaw_def,
    blockLaw_apply_of_measurable _ _ _ (fun i : Fin (m + 1) => h.aemeasurable i.val)
      MeasurableSet.of_discrete]
  rfl

/-- **The visited successor array of a recurrent Markov exchangeable process is row
exchangeable.** Its law is unchanged when the entries of each row are permuted, with a permutation
chosen separately for each row.

Together with `TauCeti.Probability.mixedMarkovChain_of_rowExchangeable` this is the
Diaconis--Freedman representation. No state needs to be attained: the rows of the states the
process never visits are constant, so the obstruction exhibited by
`TauCeti.Probability.spareStateProcess_not_rowExchangeable_successorProcess` for the plain
successor array does not arise. -/
-- The `haveI` in the statement supplies the `Countable α` that `RowExchangeable` takes as an
-- instance from `h` itself, so that a caller holding `h` needs no ambient discrete-state instance.
theorem MarkovExchangeable.rowExchangeable_visitedSuccessorProcess [IsFiniteMeasure μ]
    (h : MarkovExchangeable μ X) (hrec : Recurrent μ X) :
    haveI := h.countable
    RowExchangeable μ (visitedSuccessorProcess X) := by
  have := h.countable
  have := h.measurableSingletonClass
  have hSA : ∀ p, AEMeasurable (visitedSuccessorProcess X p) μ :=
    aemeasurable_visitedSuccessorProcess h.aemeasurable
  rw [rowExchangeable_iff_forall_prodCongrRight_mem_finitary (AEMeasurable.of_eval hSA)]
  intro π hπ
  have hsupp : {p : α × ℕ | π p.1 p.2 ≠ p.2}.Finite := by
    rw [← Equiv.Perm.compl_fixedBy_prodCongrRight]
    exact Equiv.Perm.mem_finitary.1 hπ
  rw [ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq
    (AEMeasurable.of_eval fun p : α × ℕ => hSA (p.1, π p.1 p.2)) (AEMeasurable.of_eval hSA)]
  intro F
  refine Measure.ext_of_singleton fun g => ?_
  have hm₁ : AEMeasurable (fun ω => F.restrict fun p : α × ℕ =>
      visitedSuccessorProcess X (p.1, π p.1 p.2) ω) μ :=
    AEMeasurable.of_eval fun p => hSA ((p : α × ℕ).1, π (p : α × ℕ).1 (p : α × ℕ).2)
  have hm₂ : AEMeasurable (fun ω => F.restrict fun p : α × ℕ => visitedSuccessorProcess X p ω) μ :=
    AEMeasurable.of_eval fun p => hSA (p : α × ℕ)
  rw [Measure.map_apply_of_aemeasurable hm₁ MeasurableSet.of_discrete,
    Measure.map_apply_of_aemeasurable hm₂ MeasurableSet.of_discrete]
  have hcellπ : (fun ω => F.restrict fun p : α × ℕ =>
      visitedSuccessorProcess X (p.1, π p.1 p.2) ω) ⁻¹' {g} = {ω | ∀ p : F,
        visitedSuccessorArray (fun n => X n ω) (p : α × ℕ).1 (π (p : α × ℕ).1 (p : α × ℕ).2)
          = g p} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Finset.restrict_def,
      visitedSuccessorProcess_apply, Set.mem_ofPred_eq]
  have hcellid : (fun ω => F.restrict fun p : α × ℕ => visitedSuccessorProcess X p ω) ⁻¹' {g}
      = {ω | ∀ p : F, visitedSuccessorArray (fun n => X n ω) (p : α × ℕ).1 (p : α × ℕ).2
          = g p} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Finset.restrict_def,
      visitedSuccessorProcess_apply, Set.mem_ofPred_eq]
  rw [hcellπ, hcellid]
  -- Both masses are limits of horizon prefix masses, and those agree term by term.
  exact tendsto_nhds_unique
    ((tendsto_prefixLaw_horizonWords_inter_cellWords h hrec hsupp fun _ => Or.inr rfl).congr
      fun m => prefixLaw_horizonWords_inter_cellWords h π F m g)
    (tendsto_prefixLaw_horizonWords_inter_cellWords h hrec hsupp fun _ => Or.inl rfl)

/-- **The successor array of a recurrent Markov exchangeable process that almost surely attains
every state is row exchangeable.** Almost surely it coincides with the visited successor array.

The hypothesis that every state is almost surely attained is not decorative:
`TauCeti.Probability.spareStateProcess_not_rowExchangeable_successorProcess` is a recurrent Markov
exchangeable process without it whose successor array is not row exchangeable. -/
theorem MarkovExchangeable.rowExchangeable_successorProcess [IsFiniteMeasure μ]
    (h : MarkovExchangeable μ X) (hrec : Recurrent μ X)
    (hvis : ∀ᵐ ω ∂μ, ∀ a : α, ∃ n, X n ω = a) :
    haveI := h.countable
    RowExchangeable μ (successorProcess X) := by
  have := h.countable
  have hae : ∀ᵐ ω ∂μ, ∀ p : α × ℕ, visitedSuccessorProcess X p ω = successorProcess X p ω := by
    filter_upwards [hvis] with ω hω p
    rw [visitedSuccessorProcess_apply, successorProcess_apply]
    exact visitedSuccessorArray_of_exists (hω p.1)
  refine rowExchangeable_def.2 fun π => ?_
  refine (Measure.map_congr ?_).trans
    ((rowExchangeable_def.1 (h.rowExchangeable_visitedSuccessorProcess hrec) π).trans
      (Measure.map_congr ?_))
  · filter_upwards [hae] with ω hω
    exact funext fun p => (hω _).symm
  · filter_upwards [hae] with ω hω
    exact funext hω

/-- **The Diaconis--Freedman representation theorem.** A recurrent Markov exchangeable process that
starts almost surely at a fixed state is a mixture of Markov chains. -/
theorem MarkovExchangeable.mixedMarkovChain [IsProbabilityMeasure μ] {a₀ : α}
    (h : MarkovExchangeable μ X) (hrec : Recurrent μ X) (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀) :
    MixedMarkovChain μ X := by
  have := h.countable
  have := h.measurableSingletonClass
  exact mixedMarkovChain_of_rowExchangeable h.aemeasurable h0
    (aemeasurable_visitedSuccessorProcess h.aemeasurable)
    (ae_of_all _ fun _ n _ => by
      rw [visitedSuccessorProcess_apply, successorProcess_apply]
      exact visitedSuccessorArray_of_exists ⟨n, rfl⟩)
    (h.rowExchangeable_visitedSuccessorProcess hrec)

end Representation

end Probability

end TauCeti

end

end
