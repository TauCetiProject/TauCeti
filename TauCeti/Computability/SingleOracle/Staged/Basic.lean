/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Relative
public import TauCeti.Computability.SingleOracle.Staged.Search
public import TauCeti.Computability.Staged.Partial

/-!
# Staged presentations of fixed-oracle computations

For fixed answers, each code gives a staged partial function of its input. A successful
observation records the output and use in a `Halt`. If the answers are exactly those of
the oracle, projecting the recorded output gives the partial evaluation of the code.

For a total oracle, normalized stage evaluation is computable in that oracle. This gives an
effective staged presentation for every partial function recursive in a fixed total oracle.
Conversely, searching a uniformly oracle-computable stage table recovers a partial function
recursive in the same oracle.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter III.1.
-/

public section

namespace TauCeti.Oracle.Single.Code

/-- Staged observations of a code against fixed answers, retaining both the output and use. -/
def stagedEval (c : Code) (σ : ℕ → Option ℕ) : StagedPartial ℕ Halt where
  stage x s := evalStage σ s c x
  persistent hst h := evalStage_mono hst h

/-- The presentation uses the normalized stage bound. -/
@[simp]
theorem stage_stagedEval (c : Code) (σ : ℕ → Option ℕ) (x s : ℕ) :
    (c.stagedEval σ).stage x s = evalStage σ s c x := (rfl)

/-- Projecting the output from staged evaluations gives the partial evaluation of the program
when the fixed answers give exactly the oracle's values. -/
theorem eval_map_stagedEval (c : Code) {σ : ℕ → Option ℕ} {O : ℕ →. ℕ}
    (hσ : ∀ z y, σ z = some y ↔ y ∈ O z) (x : ℕ) :
    ((c.stagedEval σ).map Halt.output).eval x = eval O c x := by
  ext y
  simp only [StagedPartial.mem_eval_iff, StagedPartial.stage_map, stage_stagedEval,
    Option.map_eq_some_iff, mem_eval_iff_exists_evalStage hσ]

/-- A fixed code gives an effective stage table when its optional oracle answers are effective
in the same oracle family. -/
theorem computableIn₂_stage_stagedEval (c : Code) {G : Set (ℕ →. ℕ)}
    {σ : ℕ → Option ℕ} (hσ : ComputableIn G σ) : ComputableIn₂ G (c.stagedEval σ).stage := by
  have hf : ComputableIn₂ G (fun (_ : Unit) z => σ z) := hσ.comp ComputableIn.snd
  simpa only [ComputableIn₂, stage_stagedEval] using (computableIn_evalStage hf).comp
    ((ComputableIn.const ()).pair
      (ComputableIn.snd.pair ((ComputableIn.const c).pair ComputableIn.fst)) :
        ComputableIn G fun p : ℕ × ℕ => ((), p.2, c, p.1))

/-- Compiling a program for the stages of a persistent presentation computes its partial
function relative to the same oracle. -/
theorem eval_searchStages_eq_of_stagedPartial {c : Code} {P : StagedPartial ℕ ℕ}
    {O : ℕ →. ℕ}
    (hP : ∀ x s, eval O c (Nat.pair x s) = Part.some (Encodable.encode (P.stage x s))) :
    eval O c.searchStages = P.eval := by
  funext x
  rw [eval_searchStages (hP x), P.eval_def]

end TauCeti.Oracle.Single.Code

namespace TauCeti

open Encodable Oracle.Single.Code

/-- A partial function between primcodable types is recursive in a total oracle exactly when it has
a persistent stage table uniformly computable in that oracle. Its presentation can be taken
to decode the outputs of normalized bounded simulations on encoded inputs. -/
theorem recursiveIn_iff_exists_stagedPartial {α β : Type*} [Primcodable α] [Primcodable β]
    (O : ℕ → ℕ) (f : α →. β) :
    RecursiveIn {(O : ℕ →. ℕ)} f ↔ ∃ P : StagedPartial α β,
      ComputableIn₂ {(O : ℕ →. ℕ)} P.stage ∧ P.eval = f := by
  constructor
  · intro hf
    unfold RecursiveIn at hf
    obtain ⟨c, hc⟩ := Oracle.Single.Code.exists_code.1 hf
    let σ : ℕ → Option ℕ := fun z => some (O z)
    let P : StagedPartial α β :=
      { stage := fun x s => (evalStage σ s c (encode x)).bind fun d => decode d.output
        persistent := by
          intro x s t y hst hy
          obtain ⟨d, hd, hv⟩ := Option.bind_eq_some_iff.1 hy
          exact Option.bind_eq_some_iff.2 ⟨d, evalStage_mono hst hd, hv⟩ }
    refine ⟨P, ?_, ?_⟩
    · have hO : ComputableIn {(O : ℕ →. ℕ)} O := RecursiveIn.oracle _ (Set.mem_singleton _)
      have hσ : ComputableIn {(O : ℕ →. ℕ)} σ := Primrec.option_some.computableIn.comp hO
      have hargs : ComputableIn {(O : ℕ →. ℕ)} fun p : α × ℕ => (encode p.1, p.2) :=
        (Primrec.encode.computableIn.comp ComputableIn.fst).pair ComputableIn.snd
      simpa only [ComputableIn₂, P, stage_stagedEval] using
        (Primrec.option_bind₁ (Primrec.decode.comp Halt.primrec_output)).computableIn.comp
          ((c.computableIn₂_stage_stagedEval hσ).comp hargs)
    · funext x
      have hcode : eval (O : ℕ →. ℕ) c (encode x) = (f x).map encode := by
        rw [hc]
        simp [encodek]
      have hstage (n : ℕ) : n ∈ eval (O : ℕ →. ℕ) c (encode x) ↔
          ∃ s d, evalStage σ s c (encode x) = some d ∧ d.output = n :=
        mem_eval_iff_exists_evalStage (by simp [σ, eq_comm])
      ext y
      simp only [P.mem_eval_iff, P, Option.bind_eq_some_iff]
      constructor
      · rintro ⟨s, d, hd, hy⟩
        have hmem := (hstage d.output).2 ⟨s, d, hd, rfl⟩
        rw [hcode, Part.mem_map_iff] at hmem
        obtain ⟨b, hb, hbd⟩ := hmem
        have hby : b = y := by simpa [← hbd, encodek] using hy
        exact hby ▸ hb
      · intro hy
        have hmem : encode y ∈ eval (O : ℕ →. ℕ) c (encode x) := by
          rw [hcode]
          exact (Part.mem_map_iff _).2 ⟨y, hy, rfl⟩
        obtain ⟨s, d, hd, hdy⟩ := (hstage _).1 hmem
        exact ⟨s, d, hd, by simp [hdy, encodek]⟩
  · rintro ⟨P, hP, rfl⟩
    exact P.recursiveIn_eval hP

end TauCeti
