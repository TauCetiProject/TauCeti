/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Staged.Race
public import TauCeti.Computability.SingleOracle.Stage

/-!
# Racing fixed-oracle computations

`TauCeti.Oracle.Single.Code.raceStage` races the normalized stage evaluations of two programs.
The first discovered successful run wins, with a left tie rule. The winning tag, output and use
then persist. It is not the left-preferred choice between the two *current* stage evaluations:
that choice can change sides after a later discovery.

Soundness and completeness connect this race to the existing partial evaluator. For a fixed
oracle supplying exactly the given answers, the race eventually succeeds if and only if one of
the two computations converges. Its winner is a genuine run of the tagged program. No oracle
representation or alternative partial-computability predicate is introduced.

The finite stage operation is primitive recursive in primitive-recursive finite oracle answers,
programs, input and stage. No computable bound on discovery time is asserted.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, III.1
  (bounded oracle computations and effective searches).
-/

public section

namespace TauCeti.Oracle.Single.Code

/-- Race two programs on the same input against fixed answers, retaining the first discovered
successful normalized run, including its use. The left program wins simultaneous discovery. -/
def raceStage (σ : ℕ → Option ℕ) (s : ℕ) (c d : Code) (x : ℕ) : Option (Halt ⊕ Halt) :=
  Staged.race (fun t => evalStage σ t c x) (fun t => evalStage σ t d x) s

/-- The fixed-oracle race is the earliest-discovery race of the normalized evaluations. -/
theorem raceStage_def (σ : ℕ → Option ℕ) (s : ℕ) (c d : Code) (x : ℕ) :
    raceStage σ s c d x =
      Staged.race (fun t => evalStage σ t c x) (fun t => evalStage σ t d x) s := (rfl)

variable {σ : ℕ → Option ℕ} {s t x : ℕ} {c d : Code} {z : Halt ⊕ Halt}

/-- Stage zero has no winner. -/
@[simp]
theorem raceStage_zero (σ : ℕ → Option ℕ) (c d : Code) (x : ℕ) :
    raceStage σ 0 c d x = none := by
  simp [raceStage_def]

/-- For fixed answers, no discovery so far is equivalent to both computations failing at the
current stage. This uses persistence of normalized evaluations. -/
@[simp]
theorem raceStage_eq_none_iff :
    raceStage σ s c d x = none ↔ evalStage σ s c x = none ∧ evalStage σ s d x = none := by
  rw [raceStage_def, Staged.race_eq_none_iff]
  constructor
  · exact fun h => h s le_rfl
  · exact fun h t hts => ⟨evalStage_eq_none_of_le hts h.1, evalStage_eq_none_of_le hts h.2⟩

/-- The left program wins exactly when it succeeds at a stage with no earlier success on
either side. A simultaneous right success does not prevent a left win. -/
@[simp]
theorem raceStage_eq_some_inl_iff {a : Halt} :
    raceStage σ s c d x = some (Sum.inl a) ↔ ∃ t ≤ s,
      (∀ u < t, evalStage σ u c x = none ∧ evalStage σ u d x = none) ∧
        evalStage σ t c x = some a := by
  rw [raceStage_def, Staged.race_eq_some_inl_iff]

/-- The right program wins exactly when it first succeeds while the left program is still
absent. Persistence makes earlier failures on the left redundant. -/
@[simp]
theorem raceStage_eq_some_inr_iff {b : Halt} :
    raceStage σ s c d x = some (Sum.inr b) ↔ ∃ t ≤ s,
      evalStage σ t c x = none ∧ (∀ u < t, evalStage σ u d x = none) ∧
        evalStage σ t d x = some b := by
  rw [raceStage_def, Staged.race_eq_some_inr_iff]
  constructor
  · rintro ⟨t, hts, hbefore, hc, hd⟩
    exact ⟨t, hts, hc, fun u hu => (hbefore u hu).2, hd⟩
  · rintro ⟨t, hts, hc, hbefore, hd⟩
    exact ⟨t, hts, fun u hu => ⟨evalStage_eq_none_of_le hu.le hc, hbefore u hu⟩, hc, hd⟩

/-- Once the race has a winner, increasing the stage preserves its side, output and use. -/
theorem raceStage_mono (hst : s ≤ t) (h : raceStage σ s c d x = some z) :
    raceStage σ t c d x = some z := by
  rw [raceStage_def] at h ⊢
  exact Staged.race_mono hst h

/-- The retained winner is still a successful run at the current stage, with exactly its
original output and use. -/
theorem evalStage_eq_some_of_raceStage_eq_some (h : raceStage σ s c d x = some z) :
    z.elim (fun a => evalStage σ s c x = some a) (fun b => evalStage σ s d x = some b) := by
  cases z with
  | inl a =>
    obtain ⟨t, hts, -, ht⟩ := raceStage_eq_some_inl_iff.1 h
    exact evalStage_mono hts ht
  | inr b =>
    obtain ⟨t, hts, -, -, ht⟩ := raceStage_eq_some_inr_iff.1 h
    exact evalStage_mono hts ht

/-- A winner is a genuine partial computation of the indicated program. The supplied answers
need only be sound below the winner's recorded use for the same fixed oracle. -/
theorem raceStage_sound {O : ℕ →. ℕ}
    (hσ : ∀ q < z.elim Halt.use Halt.use, ∀ y, σ q = some y → y ∈ O q)
    (h : raceStage σ s c d x = some z) :
    z.elim (fun a => a.output ∈ eval O c x) (fun b => b.output ∈ eval O d x) := by
  have hz := evalStage_eq_some_of_raceStage_eq_some h
  cases z <;> exact evalStage_sound hz hσ

/-- The race eventually discovers a winner exactly when at least one of the partial
computations converges. Completeness requires all defined oracle answers to be supplied. -/
theorem exists_raceStage_eq_some_iff {O : ℕ →. ℕ}
    (hσ : ∀ q y, σ q = some y ↔ y ∈ O q) :
    (∃ s z, raceStage σ s c d x = some z) ↔ (eval O c x).Dom ∨ (eval O d x).Dom := by
  simp only [raceStage_def, Staged.exists_race_eq_some_iff, Part.dom_iff_mem,
    mem_eval_iff_exists_evalStage hσ]
  apply or_congr
  all_goals
    constructor
    · rintro ⟨s, a, ha⟩
      exact ⟨a.output, s, a, ha, rfl⟩
    · rintro ⟨y, s, a, ha, -⟩
      exact ⟨s, a, ha⟩

/-- Normalized racing is primitive recursive uniformly in finite oracle data, the two
programs, the input and the stage. -/
theorem primrec_raceStage {α : Type*} [Primcodable α] {σ : α → ℕ → Option ℕ}
    {c d : α → Code} {x s : α → ℕ} (hσ : Primrec₂ σ)
    (hc : Primrec c) (hd : Primrec d) (hx : Primrec x) (hs : Primrec s) :
    Primrec fun a => raceStage (σ a) (s a) (c a) (d a) (x a) := by
  have hl : Primrec₂ fun a t => evalStage (σ a) t (c a) (x a) :=
    ((primrec_evalStage hσ).comp
      (Primrec.fst.pair (Primrec.snd.pair
        ((hc.comp Primrec.fst).pair (hx.comp Primrec.fst))))).to₂
  have hr : Primrec₂ fun a t => evalStage (σ a) t (d a) (x a) :=
    ((primrec_evalStage hσ).comp
      (Primrec.fst.pair (Primrec.snd.pair
        ((hd.comp Primrec.fst).pair (hx.comp Primrec.fst))))).to₂
  exact ((Staged.primrec_race hl hr).comp Primrec.id hs).of_eq fun a =>
    (raceStage_def (σ a) (s a) (c a) (d a) (x a)).symm

end TauCeti.Oracle.Single.Code
