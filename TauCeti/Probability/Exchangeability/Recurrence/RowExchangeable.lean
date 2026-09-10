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

/-!
# The successor array of a Markov exchangeable process is row exchangeable

Diaconis and Freedman represent a recurrent Markov exchangeable process as a mixture of Markov
chains by passing to its **successor array**, whose `(a, k)`-entry is the state reached right after
the `k`-th visit to `a`. `TauCeti/Probability/Exchangeability/DiaconisFreedman.lean` supplies the
change of variables that turns a row exchangeable successor array back into a mixture of Markov
chains. This file supplies the missing hypothesis of that change of variables: for a process that
almost surely visits every state infinitely often, Markov exchangeability makes the successor
array row exchangeable, and the Diaconis--Freedman representation follows.

## The argument

Permuting the entries of each row and following the reordered rows rebuilds a finite path with the
same initial state and the same transition counts, provided the permutations obey the last-exit
condition — that is what `TauCeti.pathOfReindexedSuccessors` and the finite reconstruction lemmas
of `TauCeti/Combinatorics/Enumerative/LastExit.lean` establish. Markov exchangeability equates the
masses of two such words, so a prefix law is invariant under a last-exit-admissible reindexing
(`TauCeti.Probability.MarkovExchangeable.measure_setOf_eqOn_pathOfReindexedSuccessors`).

Row exchangeability is the limit of that finite statement. A finitely supported family of row
permutations is last-exit admissible over every long enough horizon, and any finite family of
cells is consumed by every long enough prefix, so the array event at those cells is a prefix event
there; the reconstruction pairs the prefixes realizing the reindexed event with those realizing
the original one, and the horizons exhaust the space.

## Why every state has to be attained

`TauCeti/Probability/Exchangeability/Recurrence/UnvisitedRow.lean` exhibits a recurrent Markov
exchangeable process whose successor array is *not* row exchangeable: an unattained state has junk
visit times, so its whole row is tied to the cell `(x 0, 0)`, and permuting the row of `x 0` breaks
the tie. Recurrence constrains only the states a process does attain, so the hypothesis that every
state is attained is what rules that degeneracy out; it holds for instance for an irreducible
recurrent chain on its own state space.

## Main results

* `TauCeti.Probability.MarkovExchangeable.measure_setOf_eqOn_pathOfReindexedSuccessors` — a finite
  path and its last-exit reconstruction are equally likely.
* `TauCeti.Probability.MarkovExchangeable.rowExchangeable_successorProcess` — **the successor array
  of a Markov exchangeable process that almost surely attains every state and is recurrent is row
  exchangeable.**
* `TauCeti.Probability.MarkovExchangeable.mixedMarkovChain` — **the Diaconis--Freedman
  representation**: such a process started at a fixed state is a mixture of Markov chains.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115--130.
* S. Fortini, L. Ladelli, G. Petris, and E. Regazzini, "On mixtures of distributions of Markov
  chains", *Stochastic Processes and their Applications* 100 (2002), 147--165, Lemma 1(b).
-/

public section

noncomputable section

open Filter MeasureTheory

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

/-- The words whose visit counts before `m` already exhaust every cell moved by `π` and every cell
of `F`, together with its `π`-image. On such a word a last-exit reindexing by `π` is legitimate
and the successor entries at the cells of `F` are determined. -/
private def HorizonWords (π : α → Equiv.Perm ℕ) (F : Finset (α × ℕ)) (m : ℕ) :
    Set (Fin (m + 1) → α) :=
  {u | ∀ p : α × ℕ, π p.1 p.2 ≠ p.2 ∨ p ∈ F →
    p.2 + 1 < visitCount (wordSeq u) p.1 m ∧ π p.1 p.2 + 1 < visitCount (wordSeq u) p.1 m}

/-- The words whose successor array takes the values `g` at the cells of `F` reindexed by `ρ`. -/
private def CellWords (ρ : α → ℕ → ℕ) (F : Finset (α × ℕ)) (m : ℕ) (g : F → α) :
    Set (Fin (m + 1) → α) :=
  {u | ∀ p : F, successorArray (wordSeq u) (p : α × ℕ).1 (ρ (p : α × ℕ).1 (p : α × ℕ).2) = g p}

variable {π : α → Equiv.Perm ℕ} {F : Finset (α × ℕ)} {g : F → α} {u : Fin (m + 1) → α}

private theorem lastExitAdmissible_of_mem_horizonWords (hu : u ∈ HorizonWords π F m) :
    LastExitAdmissible π (wordSeq u) m :=
  lastExitAdmissible_of_support_lt_visitCount fun a _ k hk => (hu (a, k) (Or.inl hk)).1

private theorem lastExitAdmissible_symm_of_mem_horizonWords (hu : u ∈ HorizonWords π F m) :
    LastExitAdmissible (fun a => (π a).symm) (wordSeq u) m := by
  refine lastExitAdmissible_of_support_lt_visitCount fun a _ k hk => (hu (a, k) (Or.inl ?_)).1
  exact fun hfix => hk ((Equiv.symm_apply_eq _).2 hfix.symm)

private theorem reindexWord_mem_horizonWords {ρ : α → Equiv.Perm ℕ}
    (hu : u ∈ HorizonWords π F m) (hρ : LastExitAdmissible ρ (wordSeq u) m) :
    reindexWord ρ m u ∈ HorizonWords π F m := by
  intro p hp
  rw [visitCount_wordSeq_reindexWord hρ]
  exact hu p hp

private theorem successorArray_reindexWord_cell (hu : u ∈ HorizonWords π F m) (p : F) :
    successorArray (wordSeq (reindexWord π m u)) (p : α × ℕ).1 (p : α × ℕ).2
      = successorArray (wordSeq u) (p : α × ℕ).1 (π (p : α × ℕ).1 (p : α × ℕ).2) :=
  successorArray_wordSeq_reindexWord (lastExitAdmissible_of_mem_horizonWords hu)
    (by have := (hu (p : α × ℕ) (Or.inr p.2)).1; omega)

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
    fun p => (successorArray_reindexWord_cell u.2.1 p).trans (u.2.2 p)⟩
  invFun v := ⟨reindexWord (fun a => (π a).symm) m v.1,
    reindexWord_mem_horizonWords v.2.1 (lastExitAdmissible_symm_of_mem_horizonWords v.2.1),
    fun p => by
      have hmem := reindexWord_mem_horizonWords (ρ := fun a => (π a).symm) v.2.1
        (lastExitAdmissible_symm_of_mem_horizonWords v.2.1)
      have hcell := successorArray_reindexWord_cell hmem p
      rw [reindexWord_reindexWord_symm v.2.1] at hcell
      exact hcell.symm.trans (v.2.2 p)⟩
  left_inv u :=
    Subtype.ext (reindexWord_symm_reindexWord (lastExitAdmissible_of_mem_horizonWords u.2.1))
  right_inv v := Subtype.ext (reindexWord_reindexWord_symm v.2.1)

end Words

section Prefix

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω} {X : ℕ → Ω → α}

/-- A finite path event of the process is a prefix-law singleton. -/
private theorem measure_setOf_eqOn [Countable α] [MeasurableSingletonClass α]
    (hX : ∀ i, AEMeasurable (X i) μ) (w : ℕ → α) (m : ℕ) :
    μ {ω | ∀ i ≤ m, X i ω = w i} = prefixLaw μ X (m + 1) {fun i : Fin (m + 1) => w i.val} := by
  rw [prefixLaw_def, blockLaw_apply_of_measurable _ _ _ (fun i : Fin (m + 1) => hX i.val)
    MeasurableSet.of_discrete]
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
  exact ⟨fun hω i => hω i.val (Nat.lt_succ_iff.1 i.isLt),
    fun hω i hi => hω ⟨i, Nat.lt_succ_of_le hi⟩⟩

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

section Horizon

variable {Ω α : Type*} {X : ℕ → Ω → α}

/-- The paths whose visit counts before `m` already exhaust every cell moved by `π` and every cell
of `F`, together with its `π`-image. -/
private def Horizon (X : ℕ → Ω → α) (π : α → Equiv.Perm ℕ) (F : Finset (α × ℕ)) (m : ℕ) :
    Set Ω :=
  {ω | ∀ p : α × ℕ, π p.1 p.2 ≠ p.2 ∨ p ∈ F →
    p.2 + 1 < visitCount (fun n => X n ω) p.1 m ∧
      π p.1 p.2 + 1 < visitCount (fun n => X n ω) p.1 m}

/-- The event that the successor array takes the values `g` at the cells of `F` reindexed by
`ρ`. -/
private def CellEvent (X : ℕ → Ω → α) (ρ : α → ℕ → ℕ) (F : Finset (α × ℕ)) (g : F → α) :
    Set Ω :=
  {ω | ∀ p : F, successorArray (fun n => X n ω) (p : α × ℕ).1 (ρ (p : α × ℕ).1 (p : α × ℕ).2)
    = g p}

variable {π : α → Equiv.Perm ℕ} {F : Finset (α × ℕ)} {m m' : ℕ} {g : F → α} {ρ : α → ℕ → ℕ}

private theorem horizon_mono (hm : m ≤ m') : Horizon X π F m ⊆ Horizon X π F m' := by
  intro ω hω p hp
  have h₁ := (hω p hp).1
  have h₂ := (hω p hp).2
  have := visitCount_monotone (fun n => X n ω) p.1 hm
  omega

/-- Over its horizon, the array event at the cells of `F` is an event of the length-`m` prefix. -/
private theorem horizon_inter_cellEvent (hcell : ∀ p : F,
      ρ (p : α × ℕ).1 (p : α × ℕ).2 = (p : α × ℕ).2 ∨
        ρ (p : α × ℕ).1 (p : α × ℕ).2 = π (p : α × ℕ).1 (p : α × ℕ).2) :
    Horizon X π F m ∩ CellEvent X ρ F g
      = (fun ω (i : Fin (m + 1)) => X i.val ω) ⁻¹' (HorizonWords π F m ∩ CellWords ρ F m g) := by
  ext ω
  have hws : ∀ i ≤ m, X i ω = wordSeq (fun i : Fin (m + 1) => X i.val ω) i :=
    fun i hi => (wordSeq_of_le (fun i : Fin (m + 1) => X i.val ω) hi).symm
  have hvc : ∀ a : α, visitCount (wordSeq fun i : Fin (m + 1) => X i.val ω) a m
      = visitCount (fun n => X n ω) a m :=
    fun a => visitCount_congr fun i hi => (hws i hi.le).symm
  have hhor : ω ∈ Horizon X π F m ↔
      (fun i : Fin (m + 1) => X i.val ω) ∈ HorizonWords π F m := by
    simp only [Horizon, HorizonWords, Set.mem_ofPred_eq, hvc]
  refine ⟨fun hω => ⟨hhor.1 hω.1, fun p => ?_⟩, fun hω => ⟨hhor.2 hω.1, fun p => ?_⟩⟩
  · have hb : ρ (p : α × ℕ).1 (p : α × ℕ).2 < visitCount (fun n => X n ω) (p : α × ℕ).1 m := by
      have h₁ := hω.1 (p : α × ℕ) (Or.inr p.2)
      rcases hcell p with hr | hr <;> rw [hr] <;> omega
    rw [← successorArray_congr hws hb]
    exact hω.2 p
  · have hb : ρ (p : α × ℕ).1 (p : α × ℕ).2 < visitCount (fun n => X n ω) (p : α × ℕ).1 m := by
      have h₁ := hhor.2 hω.1 (p : α × ℕ) (Or.inr p.2)
      rcases hcell p with hr | hr <;> rw [hr] <;> omega
    rw [successorArray_congr hws hb]
    exact hω.2 p

private theorem exists_mem_horizon {α : Type*} {x : ℕ → α}
    (hio : ∀ a : α, {n | x n = a}.Infinite) (π : α → Equiv.Perm ℕ)
    (hπ : {p : α × ℕ | π p.1 p.2 ≠ p.2}.Finite) (F : Finset (α × ℕ)) :
    ∃ m, ∀ p : α × ℕ, π p.1 p.2 ≠ p.2 ∨ p ∈ F →
      p.2 + 1 < visitCount x p.1 m ∧ π p.1 p.2 + 1 < visitCount x p.1 m := by
  have hcount : ∀ a : α, Tendsto (visitCount x a) atTop atTop := by
    intro a
    refine tendsto_atTop_atTop.2 fun b => ?_
    obtain ⟨n, -, hn⟩ := exists_visitCount_of_infinite (hio a) b
    exact ⟨n, fun j hnj => hn ▸ visitCount_monotone x a hnj⟩
  have hfin : {p : α × ℕ | π p.1 p.2 ≠ p.2 ∨ p ∈ F}.Finite :=
    (hπ.union F.finite_toSet).subset fun _ hp => hp
  have hev : ∀ᶠ j : ℕ in atTop, ∀ p ∈ {p : α × ℕ | π p.1 p.2 ≠ p.2 ∨ p ∈ F},
      p.2 + 1 < visitCount x p.1 j ∧ π p.1 p.2 + 1 < visitCount x p.1 j := by
    refine hfin.eventually_all.2 fun p _ => ?_
    obtain ⟨N, hN⟩ := tendsto_atTop_atTop.1 (hcount p.1) (max (p.2 + 2) (π p.1 p.2 + 2))
    exact eventually_atTop.2 ⟨N, fun j hj => by have := hN j hj; omega⟩
  obtain ⟨j, hj⟩ := hev.exists
  exact ⟨j, fun p hp => hj p hp⟩

end Horizon

section Representation

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω} {X : ℕ → Ω → α}

/-- Over its horizon, the array event at the cells of `F` is a prefix event, and the last-exit
reconstruction pairs the reindexed prefixes with the original ones. -/
private theorem measure_horizon_inter_cellEvent (h : MarkovExchangeable μ X)
    (π : α → Equiv.Perm ℕ) (F : Finset (α × ℕ)) (m : ℕ) (g : F → α) :
    μ (Horizon X π F m ∩ CellEvent X (fun a k => π a k) F g)
      = μ (Horizon X π F m ∩ CellEvent X (fun _ k => k) F g) := by
  have := h.countable
  have := h.measurableSingletonClass
  have hpre : ∀ S : Set (Fin (m + 1) → α),
      μ ((fun ω (i : Fin (m + 1)) => X i.val ω) ⁻¹' S) = prefixLaw μ X (m + 1) S := fun S => by
    rw [prefixLaw_def, blockLaw_apply_of_measurable _ _ _
      (fun i : Fin (m + 1) => h.aemeasurable i.val) MeasurableSet.of_discrete]
  rw [horizon_inter_cellEvent (ρ := fun a k => π a k) fun _ => Or.inr rfl,
    horizon_inter_cellEvent (ρ := fun _ k => k) fun _ => Or.inl rfl, hpre, hpre]
  exact h.prefixLaw_apply_eq_of_equiv m (reindexEquiv π F m g)
    (fun w => reindexWord_zero π w.1)
    (fun w => transitionCount_reindexWord (lastExitAdmissible_of_mem_horizonWords w.2.1))

/-- **The successor array of a recurrent Markov exchangeable process that almost surely attains
every state is row exchangeable.** Its law is unchanged when the entries of each row are permuted,
with a permutation chosen separately for each row.

Together with `TauCeti.Probability.mixedMarkovChain_of_rowExchangeable_successorProcess` this is
the Diaconis--Freedman representation. The hypothesis that every state is almost surely attained
is not decorative: `TauCeti.Probability.spareStateProcess_not_rowExchangeable_successorProcess`
is a recurrent Markov exchangeable process without it whose successor array is not row
exchangeable. -/
-- The `haveI` in the statement supplies the `Countable α` that `RowExchangeable` takes as an
-- instance from `h` itself, so that a caller holding `h` needs no ambient discrete-state instance.
theorem MarkovExchangeable.rowExchangeable_successorProcess [IsFiniteMeasure μ]
    (h : MarkovExchangeable μ X) (hrec : Recurrent μ X)
    (hvis : ∀ᵐ ω ∂μ, ∀ a : α, ∃ n, X n ω = a) :
    haveI := h.countable
    RowExchangeable μ (successorProcess X) := by
  have := h.countable
  have := h.measurableSingletonClass
  have hSA : ∀ p, AEMeasurable (successorProcess X p) μ :=
    aemeasurable_successorProcess h.aemeasurable
  have hio : ∀ᵐ ω ∂μ, ∀ a : α, {n | X n ω = a}.Infinite := by
    filter_upwards [hrec.ae_infinite_setOf_eq, hvis] with ω hinf hatt a
    obtain ⟨n, hn⟩ := hatt a
    simpa only [hn] using hinf n
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
      successorProcess X (p.1, π p.1 p.2) ω) μ :=
    AEMeasurable.of_eval fun p => hSA ((p : α × ℕ).1, π (p : α × ℕ).1 (p : α × ℕ).2)
  have hm₂ : AEMeasurable (fun ω => F.restrict fun p : α × ℕ => successorProcess X p ω) μ :=
    AEMeasurable.of_eval fun p => hSA (p : α × ℕ)
  rw [Measure.map_apply_of_aemeasurable hm₁ MeasurableSet.of_discrete,
    Measure.map_apply_of_aemeasurable hm₂ MeasurableSet.of_discrete]
  have hcellπ : (fun ω => F.restrict fun p : α × ℕ => successorProcess X (p.1, π p.1 p.2) ω)
      ⁻¹' {g} = CellEvent X (fun a k => π a k) F g := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Finset.restrict_def,
      successorProcess_apply, CellEvent, Set.mem_ofPred_eq]
  have hcellid : (fun ω => F.restrict fun p : α × ℕ => successorProcess X p ω) ⁻¹' {g}
      = CellEvent X (fun _ k => k) F g := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Finset.restrict_def,
      successorProcess_apply, CellEvent, Set.mem_ofPred_eq]
  have hfull : ∀ᵐ ω ∂μ, ∃ m, ω ∈ Horizon X π F m := by
    filter_upwards [hio] with ω hω
    exact exists_mem_horizon hω π hsupp F
  have key : ∀ ρ : α → ℕ → ℕ,
      μ (CellEvent X ρ F g) = ⨆ m, μ (Horizon X π F m ∩ CellEvent X ρ F g) := by
    intro ρ
    have hmono : Monotone fun m => Horizon X π F m ∩ CellEvent X ρ F g :=
      fun _ _ hm => Set.inter_subset_inter_left _ (horizon_mono hm)
    rw [← hmono.measure_iUnion]
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hfull] with ω hω
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun hc => hω.imp fun _ hm => ⟨hm, hc⟩, fun hc => hc.choose_spec.2⟩
  rw [hcellπ, hcellid, key (fun a k => π a k), key (fun _ k => k)]
  exact iSup_congr fun m => measure_horizon_inter_cellEvent h π F m g

/-- **The Diaconis--Freedman representation theorem.** A Markov exchangeable process that starts
almost surely at a fixed state, is recurrent, and almost surely attains every state, is a mixture
of Markov chains. -/
theorem MarkovExchangeable.mixedMarkovChain [IsProbabilityMeasure μ] {a₀ : α}
    (h : MarkovExchangeable μ X) (hrec : Recurrent μ X)
    (hvis : ∀ᵐ ω ∂μ, ∀ a : α, ∃ n, X n ω = a) (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀) :
    MixedMarkovChain μ X := by
  have := h.countable
  have := h.measurableSingletonClass
  exact mixedMarkovChain_of_rowExchangeable_successorProcess h.aemeasurable h0
    (h.rowExchangeable_successorProcess hrec hvis)

end Representation

end Probability

end TauCeti

end

end
