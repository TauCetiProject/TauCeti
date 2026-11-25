/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy
public import Mathlib.Topology.UniformSpace.DiscreteUniformity
public import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Analysis.Asymptotics.ExpGrowth

/-!
# Topological entropy of the full shift

For a finite nonempty alphabet `α` with the discrete uniformity, the one-sided full shift on
`ℕ → α` and the two-sided full shift on `ℤ → α` (Mathlib's `SymbolicDynamics.FullShift.shift 1`,
`x ↦ (h ↦ x (1 + h))`) have topological entropy `log (card α)`.

The entourages of the product uniformity are refined by the relations "agree on a finite set `S`
of coordinates". For the shift, agreeing on `S` for `n` steps is agreeing on the `n` translates
`k + S`, `k < n`. If `S` sits in a window of `c` consecutive coordinates, these translates sit in
a window of `n + c` coordinates, and one point for each word on that window gives a dynamical
cover with at most `card α ^ (n + c)` points; agreeing at the coordinate `0` for `n` steps is
agreeing on `0, …, n - 1`, which needs at least `card α ^ n` points. Both bounds grow like
`card α ^ n`.

## Main results

* `TauCeti.coverEntropy_shift_nat`, `TauCeti.coverEntropyInf_shift_nat`: the one-sided full shift
  has entropy `log (card α)`.
* `TauCeti.coverEntropy_shift_int`, `TauCeti.coverEntropyInf_shift_int`: the two-sided full shift
  has entropy `log (card α)`.
-/

public section

namespace TauCeti

open Dynamics Set Filter ExpGrowth SymbolicDynamics.FullShift
open scoped Uniformity ENNReal

variable {α G : Type*}

/-- Configurations agreeing on the coordinates of `S`. -/
private def agreeOn (S : Set G) : SetRel (G → α) (G → α) := {p | ∀ i ∈ S, p.1 i = p.2 i}

private lemma agreeOn_anti {S S' : Set G} (h : S ⊆ S') :
    (agreeOn S' : SetRel (G → α) (G → α)) ⊆ agreeOn S :=
  fun _ hp i hi ↦ hp i (h hi)

section Uniformity

variable [UniformSpace α] [DiscreteUniformity α]

private lemma agreeOn_mem_uniformity {S : Set G} (hS : S.Finite) :
    (agreeOn S : SetRel (G → α) (G → α)) ∈ 𝓤 (G → α) := by
  have : (agreeOn S : SetRel (G → α) (G → α)) =
      ⋂ i ∈ S, {p : (G → α) × (G → α) | (p.1 i, p.2 i) ∈ (SetRel.id : SetRel α α)} := by
    ext p; simp [agreeOn]
  rw [this]
  exact (biInter_mem hS).2 fun i _ ↦ uniformContinuous_def.1 (Pi.uniformContinuous_proj _ i) _
    (DiscreteUniformity.relId_mem_uniformity α)

private lemma exists_agreeOn_subset {U : SetRel (G → α) (G → α)} (hU : U ∈ 𝓤 (G → α)) :
    ∃ S : Set G, S.Finite ∧ agreeOn S ⊆ U := by
  rw [Pi.uniformity, DiscreteUniformity.eq_principal_setRelId] at hU
  obtain ⟨I, hI, V, hV, rfl⟩ := mem_iInf.1 hU
  refine ⟨I, hI, fun p hp ↦ mem_iInter.2 fun i ↦ ?_⟩
  obtain ⟨t, ht, htV⟩ := mem_comap.1 (hV i)
  exact htV (ht (show p.1 i = p.2 i from hp i i.property))

end Uniformity

section Counting

variable [Fintype α]

/-- One configuration for each word on `S` gives a cover for agreement on `S`. -/
private lemma exists_finset_agreeOn [Nonempty α] (S : Finset G) :
    ∃ s : Finset (G → α), s.card ≤ Fintype.card α ^ S.card ∧
      ∀ x, ∃ y ∈ s, (x, y) ∈ (agreeOn (S : Set G) : SetRel (G → α) (G → α)) := by
  classical
  let ext : (S → α) → G → α := fun w i ↦
    if h : i ∈ S then w ⟨i, h⟩ else Classical.arbitrary α
  refine ⟨Finset.univ.image ext, ?_, fun x ↦ ⟨ext fun i ↦ x i, Finset.mem_image_of_mem _
    (Finset.mem_univ _), fun i hi ↦ by simp [ext, Finset.mem_coe.1 hi]⟩⟩
  refine Finset.card_image_le.trans_eq ?_
  simp

/-- A cover for agreement on `S` has at least one point for each word on `S`. -/
private lemma card_le_of_agreeOn [Nonempty α] (S : Finset G) (s : Finset (G → α))
    (hs : ∀ x, ∃ y ∈ s, (x, y) ∈ (agreeOn (S : Set G) : SetRel (G → α) (G → α))) :
    Fintype.card α ^ S.card ≤ s.card := by
  classical
  let r : (G → α) → (S → α) := fun y i ↦ y i
  have hsurj : (Finset.univ : Finset (S → α)) ⊆ s.image r := by
    intro w _
    obtain ⟨y, hy, hxy⟩ := hs fun i ↦ if h : i ∈ S then w ⟨i, h⟩ else
      Classical.arbitrary α
    refine Finset.mem_image.2 ⟨y, hy, funext fun i ↦ ?_⟩
    have := hxy i i.property
    simp only [i.property, dite_true] at this
    exact this.symm
  calc Fintype.card α ^ S.card = (Finset.univ : Finset (S → α)).card := by
        simp
    _ ≤ (s.image r).card := Finset.card_le_card hsurj
    _ ≤ s.card := Finset.card_image_le

end Counting

section Shift

variable [AddMonoidWithOne G]

private lemma iterate_shift_one (k : ℕ) (x : G → α) : (shift (1 : G))^[k] x = shift (k : G) x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, ← shift_add, Nat.cast_succ]

/-- Agreeing on `S` for `n` steps of the shift is agreeing on the translates `k + S`, `k < n`. -/
private lemma dynEntourage_shift_agreeOn (S : Set G) (n : ℕ) :
    dynEntourage (shift (1 : G)) (agreeOn S : SetRel (G → α) (G → α)) n =
      agreeOn (⋃ k < n, (fun i ↦ (k : G) + i) '' S) := by
  ext ⟨x, y⟩
  simp only [mem_dynEntourage, iterate_shift_one, agreeOn, mem_ofPred_eq, shift_apply,
    mem_iUnion, mem_image]
  constructor
  · rintro h _ ⟨k, hk, i, hi, rfl⟩
    exact h k hk i hi
  · intro h k hk i hi
    exact h _ ⟨k, hk, i, hi, rfl⟩

variable [Fintype α] [Nonempty α]

/-- If `S` lies in the window `{a + j | j < c}`, the minimal dynamical covers for agreement on `S`
grow at most like `card α ^ (n + c)`. -/
private lemma coverMincard_shift_le {S : Set G} {a : G} {c : ℕ}
    (hS : S ⊆ (fun j : ℕ ↦ (j : G) + a) '' Iio c) (n : ℕ) :
    (coverMincard (shift (1 : G)) univ (agreeOn S : SetRel (G → α) (G → α)) n : ℝ≥0∞) ≤
      (Fintype.card α : ℝ≥0∞) ^ c * (Fintype.card α : ℝ≥0∞) ^ n := by
  classical
  let W : Finset G := (Finset.range (n + c)).image fun j : ℕ ↦ (j : G) + a
  obtain ⟨s, hcard, hs⟩ := exists_finset_agreeOn (α := α) W
  have hcov : IsDynCoverOf (shift (1 : G)) univ (agreeOn S) n (s : Set (G → α)) := by
    intro x _
    obtain ⟨y, hy, hxy⟩ := hs x
    refine ⟨y, hy, ?_⟩
    rw [dynEntourage_shift_agreeOn]
    refine agreeOn_anti ?_ hxy
    rintro _ ⟨_, ⟨k, rfl⟩, _, ⟨hk, rfl⟩, i, hi, rfl⟩
    obtain ⟨j, hj, rfl⟩ := hS hi
    simp only [W, Finset.coe_image, Finset.coe_range, mem_image, mem_Iio]
    exact ⟨k + j, by simp only [mem_Iio] at hj; omega, by push_cast; rw [add_assoc]⟩
  have hone : 1 ≤ Fintype.card α := Fintype.card_pos
  calc (coverMincard (shift (1 : G)) univ (agreeOn S) n : ℝ≥0∞) ≤ (s.card : ℝ≥0∞) :=
        ENat.toENNReal_le.2 hcov.coverMincard_le_card
    _ ≤ ((Fintype.card α ^ (n + c) : ℕ) : ℝ≥0∞) := by
        exact_mod_cast hcard.trans (Nat.pow_le_pow_right hone (Finset.card_image_le.trans
          (by simp)))
    _ = _ := by push_cast; ring

/-- If the cast `ℕ → G` is injective, agreement at the coordinate `0` for `n` steps needs at
least `card α ^ n` points. -/
private lemma pow_le_coverMincard_shift (hG : Function.Injective (Nat.cast : ℕ → G)) (n : ℕ) :
    (Fintype.card α : ℝ≥0∞) ^ n ≤
      (coverMincard (shift (1 : G)) univ (agreeOn {0} : SetRel (G → α) (G → α)) n : ℝ≥0∞) := by
  classical
  let W : Finset G := (Finset.range n).image fun k : ℕ ↦ (k : G)
  have hW : (W : Set G) = ⋃ k < n, (fun i ↦ (k : G) + i) '' {0} := by
    ext g; simp [W, eq_comm]
  have hWcard : W.card = n := by
    rw [Finset.card_image_of_injective _ hG, Finset.card_range]
  have : ((Fintype.card α ^ n : ℕ) : ℕ∞) ≤
      coverMincard (shift (1 : G)) univ (agreeOn {0} : SetRel (G → α) (G → α)) n := by
    refine le_iInf₂ fun s hs ↦ ?_
    rw [← hWcard]
    exact_mod_cast card_le_of_agreeOn W s fun x ↦ by
      obtain ⟨y, hy, hxy⟩ := hs (mem_univ x)
      exact ⟨y, hy, by rw [hW, ← dynEntourage_shift_agreeOn]; exact hxy⟩
  calc (Fintype.card α : ℝ≥0∞) ^ n = (((Fintype.card α ^ n : ℕ) : ℕ∞) : ℝ≥0∞) := by simp
    _ ≤ _ := ENat.toENNReal_le.2 this

/-- The full shift over an index monoid `G` whose finite sets lie in windows of consecutive
coordinates, and into which `ℕ` embeds, has topological entropy `log (card α)`. -/
private lemma coverEntropy_shift_of_window [UniformSpace α] [DiscreteUniformity α]
    (hG : Function.Injective (Nat.cast : ℕ → G))
    (hwin : ∀ S : Set G, S.Finite → ∃ a : G, ∃ c : ℕ, S ⊆ (fun j : ℕ ↦ (j : G) + a) '' Iio c) :
    coverEntropy (shift (1 : G)) (univ : Set (G → α)) = ENNReal.log (Fintype.card α) ∧
      coverEntropyInf (shift (1 : G)) (univ : Set (G → α)) = ENNReal.log (Fintype.card α) := by
  have hupper : ∀ S : Set G, S.Finite → coverEntropyEntourage (shift (1 : G))
      (univ : Set (G → α)) (agreeOn S) ≤ ENNReal.log (Fintype.card α) := by
    intro S hS
    obtain ⟨a, c, hac⟩ := hwin S hS
    calc _ ≤ expGrowthSup fun n ↦ (Fintype.card α : ℝ≥0∞) ^ n :=
          expGrowthSup_le_of_eventually_le (by simp)
            (Eventually.of_forall (coverMincard_shift_le hac))
      _ = _ := expGrowthSup_pow
  have hlower : ENNReal.log (Fintype.card α) ≤ coverEntropyInfEntourage (shift (1 : G))
      (univ : Set (G → α)) (agreeOn {0}) := by
    rw [← expGrowthInf_pow]
    exact expGrowthInf_monotone fun n ↦ pow_le_coverMincard_shift hG n
  have hmem := agreeOn_mem_uniformity (α := α) (finite_singleton (0 : G))
  have hle : coverEntropy (shift (1 : G)) (univ : Set (G → α)) ≤ ENNReal.log (Fintype.card α) :=
    iSup₂_le fun U hU ↦ by
      obtain ⟨S, hS, hSU⟩ := exists_agreeOn_subset hU
      exact (coverEntropyEntourage_antitone _ _ hSU).trans (hupper S hS)
  have hge : ENNReal.log (Fintype.card α) ≤
      coverEntropyInf (shift (1 : G)) (univ : Set (G → α)) :=
    hlower.trans (coverEntropyInfEntourage_le_coverEntropyInf _ _ hmem)
  exact ⟨hle.antisymm (hge.trans (coverEntropyInf_le_coverEntropy _ _)),
    ((coverEntropyInf_le_coverEntropy _ _).trans hle).antisymm hge⟩

end Shift

variable [Fintype α] [Nonempty α] [UniformSpace α] [DiscreteUniformity α]

private lemma window_nat (S : Set ℕ) (hS : S.Finite) :
    ∃ a : ℕ, ∃ c : ℕ, S ⊆ (fun j : ℕ ↦ (j : ℕ) + a) '' Iio c := by
  obtain ⟨c, hc⟩ := hS.bddAbove
  exact ⟨0, c + 1, fun i hi ↦ ⟨i, Nat.lt_succ_of_le (hc hi), by simp⟩⟩

private lemma window_int (S : Set ℤ) (hS : S.Finite) :
    ∃ a : ℤ, ∃ c : ℕ, S ⊆ (fun j : ℕ ↦ (j : ℤ) + a) '' Iio c := by
  obtain ⟨m, hm⟩ := hS.bddAbove
  obtain ⟨l, hl⟩ := hS.bddBelow
  refine ⟨l, (m - l).toNat + 1, fun i hi ↦ ⟨(i - l).toNat, ?_, ?_⟩⟩
  · have := hm hi; have := hl hi
    simp only [mem_Iio]; omega
  · have := hl hi
    simp only; omega

/-- The one-sided full shift on a finite nonempty discrete alphabet `α` has topological entropy
`log (card α)`. -/
theorem coverEntropy_shift_nat :
    coverEntropy (shift (1 : ℕ)) (univ : Set (ℕ → α)) = ENNReal.log (Fintype.card α) :=
  (coverEntropy_shift_of_window Nat.cast_injective window_nat).1

/-- The `liminf` topological entropy of the one-sided full shift is `log (card α)`. -/
theorem coverEntropyInf_shift_nat :
    coverEntropyInf (shift (1 : ℕ)) (univ : Set (ℕ → α)) = ENNReal.log (Fintype.card α) :=
  (coverEntropy_shift_of_window Nat.cast_injective window_nat).2

/-- The two-sided full shift on a finite nonempty discrete alphabet `α` has topological entropy
`log (card α)`. -/
theorem coverEntropy_shift_int :
    coverEntropy (shift (1 : ℤ)) (univ : Set (ℤ → α)) = ENNReal.log (Fintype.card α) :=
  (coverEntropy_shift_of_window Nat.cast_injective window_int).1

/-- The `liminf` topological entropy of the two-sided full shift is `log (card α)`. -/
theorem coverEntropyInf_shift_int :
    coverEntropyInf (shift (1 : ℤ)) (univ : Set (ℤ → α)) = ENNReal.log (Fintype.card α) :=
  (coverEntropy_shift_of_window Nat.cast_injective window_int).2

end TauCeti
