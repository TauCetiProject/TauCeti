/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Staged.Race.Family
public import TauCeti.Computability.SingleOracle.Stage.Relative

/-!
# Racing a finite family of fixed-oracle programs

`raceFamilyStage` races normalized stage computations on a common input against fixed oracle
answers. It retains the full successful run of the first program to halt in stage order, taking
the least family index in a tie. The eventual discovery criterion relates the race to partial
evaluation of the programs. With a set oracle, the bounded race is uniformly computable from
the set and the tuple of programs.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, III.1
  (bounded oracle computations and effective searches).
-/

public section

namespace TauCeti.Oracle.Single.Code

variable {k : ℕ}

/-- Race a tuple of oracle programs on the same input, using normalized stage evaluation against
fixed answers. The result retains the tuple index, output and use of the first discovery. -/
def raceFamilyStage (σ : ℕ → Option ℕ) (cs : Fin k → Code) (x s : ℕ) :
    Option (Fin k × Halt) :=
  Staged.raceFamily (fun i t => evalStage σ t (cs i) x) s

/-- The oracle-program race specializes the finite-family race to normalized evaluations. -/
theorem raceFamilyStage_def (σ : ℕ → Option ℕ) (cs : Fin k → Code) (x s : ℕ) :
    raceFamilyStage σ cs x s = Staged.raceFamily (fun i t => evalStage σ t (cs i) x) s := (rfl)

variable {σ : ℕ → Option ℕ} {cs : Fin k → Code} {x s t : ℕ} {i : Fin k} {d : Halt}

/-- A race against fixed answers has no winner precisely when all current runs fail. -/
@[simp]
theorem raceFamilyStage_eq_none_iff :
    raceFamilyStage σ cs x s = none ↔ ∀ j, evalStage σ s (cs j) x = none := by
  rw [raceFamilyStage_def]
  exact Staged.raceFamily_eq_none_iff_of_persistent (fun _ _ _ _ hst h => evalStage_mono hst h)

/-- The race wins at the earliest successful stage, choosing the least successful tuple index
at that stage. -/
@[simp]
theorem raceFamilyStage_eq_some_iff :
    raceFamilyStage σ cs x s = some (i, d) ↔ ∃ t ≤ s, evalStage σ t (cs i) x = some d ∧
      (∀ u < t, ∀ j, evalStage σ u (cs j) x = none) ∧
      (∀ j < i, evalStage σ t (cs j) x = none) := by
  rw [raceFamilyStage_def, Staged.raceFamily_eq_some_iff]

/-- Increasing the stage after a discovery preserves the winner, output and use. -/
theorem raceFamilyStage_mono {w : Fin k × Halt} (hst : s ≤ t)
    (h : raceFamilyStage σ cs x s = some w) : raceFamilyStage σ cs x t = some w := by
  rw [raceFamilyStage_def] at h ⊢
  exact Staged.raceFamily_mono hst h

/-- The retained winner is also a successful run at the current stage. -/
theorem evalStage_eq_some_of_raceFamilyStage_eq_some
    (h : raceFamilyStage σ cs x s = some (i, d)) : evalStage σ s (cs i) x = some d := by
  obtain ⟨t, ht, hd, _, _⟩ := raceFamilyStage_eq_some_iff.1 h
  exact evalStage_mono ht hd

/-- The winner computes its reported output against any oracle that supplies the answers
used in that run. -/
theorem raceFamilyStage_sound {O : ℕ →. ℕ}
    (hσ : ∀ z < d.use, ∀ y, σ z = some y → y ∈ O z)
    (h : raceFamilyStage σ cs x s = some (i, d)) : d.output ∈ eval O (cs i) x :=
  evalStage_sound (evalStage_eq_some_of_raceFamilyStage_eq_some h) hσ

/-- With all the answers of a fixed partial oracle, the race eventually succeeds exactly when
some program in the family halts on the input. -/
theorem exists_raceFamilyStage_eq_some_iff {O : ℕ →. ℕ}
    (hσ : ∀ z y, σ z = some y ↔ y ∈ O z) :
    (∃ s w, raceFamilyStage σ cs x s = some w) ↔ ∃ i, (eval O (cs i) x).Dom := by
  simp only [raceFamilyStage_def, Staged.exists_raceFamily_eq_some_iff, Part.dom_iff_mem,
    mem_eval_iff_exists_evalStage hσ]
  constructor
  · rintro ⟨i, s, d, hd⟩
    exact ⟨i, d.output, s, d, hd, rfl⟩
  · rintro ⟨i, _, s, d, hd, _⟩
    exact ⟨i, s, d, hd⟩

/-- The bounded race is oracle-computable uniformly in its stage, input, programs and any
parameters of the supplied answers. -/
theorem computableIn₂_raceFamilyStage {γ : Type*} [Primcodable γ] {G : Set (ℕ →. ℕ)}
    {σ : γ → ℕ → Option ℕ} {cs : γ → Fin k → Code} {x : γ → ℕ}
    (hσ : ComputableIn₂ G σ) (hcs : ComputableIn₂ G cs) (hx : ComputableIn G x) :
    ComputableIn₂ G fun a s => raceFamilyStage (σ a) (cs a) (x a) s := by
  simp only [raceFamilyStage_def]
  have hparam : ComputableIn G (fun p : (γ × ℕ) × Fin k => p.1.1) :=
    ComputableIn.fst.comp ComputableIn.fst
  have hargs : ComputableIn G (fun p : (γ × ℕ) × Fin k =>
      (p.1.1, p.1.2, cs p.1.1 p.2, x p.1.1)) :=
    hparam.pair ((ComputableIn.snd.comp ComputableIn.fst).pair
      ((hcs.comp (hparam.pair ComputableIn.snd)).pair (hx.comp hparam)))
  exact Staged.computableIn₂_raceFamily ((computableIn_evalStage hσ).comp hargs)

/-- For any fixed set oracle, the race is computable from that set uniformly in the finite
tuple of programs, the input and the stage. The tuple is supplied as a vector of codes. -/
theorem computableIn_raceFamilyStage_setAnswers (Z : Set ℕ) :
    ComputableIn {Z.oracle} fun p : List.Vector Code k × ℕ × ℕ =>
      raceFamilyStage (setAnswers Z) p.1.get p.2.1 p.2.2 := by
  have hZ : ComputableIn {Z.oracle} (setAnswers Z) :=
    (Primrec.option_some.computableIn.comp Z.computableIn_indicator).of_eq fun z =>
      congrArg Part.some (setAnswers_apply Z z).symm
  have hf : ComputableIn₂ {Z.oracle} fun (p : List.Vector Code k × ℕ) s =>
      raceFamilyStage (setAnswers Z) p.1.get p.2 s :=
    computableIn₂_raceFamilyStage (hZ.comp ComputableIn.snd)
      (Primrec.vector_get.computableIn.comp
        ((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd))
      ComputableIn.snd
  exact hf.comp ((ComputableIn.fst.pair (ComputableIn.fst.comp ComputableIn.snd)).pair
    (ComputableIn.snd.comp ComputableIn.snd))

end TauCeti.Oracle.Single.Code
