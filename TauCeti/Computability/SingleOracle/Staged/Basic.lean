/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Stage
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

/-- Normalized stage evaluation is uniformly computable in a family of total oracle answers
computable in `G`. To simulate stage `s` it suffices to read the first `s` answers. -/
theorem computableIn_evalStage {α : Type*} [Primcodable α] {G : Set (ℕ →. ℕ)}
    {O : α → ℕ → ℕ} (hO : ComputableIn₂ G O) :
    ComputableIn G fun p : α × ℕ × Code × ℕ =>
      evalStage (fun z => some (O p.1 z)) p.2.1 p.2.2.1 p.2.2.2 := by
  have hp : ComputableIn G fun p : α × ℕ × Code × ℕ => (List.range p.2.1).map (O p.1) :=
    hO.list_range_map.comp (ComputableIn.fst.pair (ComputableIn.fst.comp ComputableIn.snd))
  refine RecursiveIn.of_eq (primrec_evalStage_list.computableIn.comp (hp.pair ComputableIn.snd))
    fun p => ?_
  simp only [Part.some_inj]
  ext d
  simp only [evalStage_eq_some_iff, evaln_range_map]

/-- For a fixed code and total oracle, the presentation's stage table is computable in that
oracle, including the recorded uses. -/
theorem computableIn₂_stage_stagedEval (c : Code) (O : ℕ → ℕ) :
    ComputableIn₂ {(O : ℕ →. ℕ)} (c.stagedEval fun z => some (O z)).stage := by
  have hO : ComputableIn {(O : ℕ →. ℕ)} O := RecursiveIn.oracle _ (Set.mem_singleton _)
  have hf : ComputableIn₂ {(O : ℕ →. ℕ)} (fun (_ : Unit) z => O z) :=
    hO.comp ComputableIn.snd
  simpa only [ComputableIn₂, stage_stagedEval] using (computableIn_evalStage hf).comp
    ((ComputableIn.const ()).pair
      (ComputableIn.snd.pair ((ComputableIn.const c).pair ComputableIn.fst)) :
        ComputableIn {(O : ℕ →. ℕ)} fun p : ℕ × ℕ => ((), p.2, c, p.1))

/-- Compiling a program for the stages of a persistent presentation computes its partial
function relative to the same oracle. -/
theorem eval_searchStages_eq_of_stagedPartial {c : Code} {P : StagedPartial ℕ ℕ}
    {O : ℕ →. ℕ}
    (hP : ∀ x s, eval O c (Nat.pair x s) = Part.some (Encodable.encode (P.stage x s))) :
    eval O c.searchStages = P.eval := by
  funext x
  ext y
  rw [eval_searchStages (hP x), P.mem_eval_iff]
  exact Nat.rfindOpt_mono fun hst hs => P.persistent hst hs

end TauCeti.Oracle.Single.Code

namespace TauCeti

/-- A partial function on the naturals is recursive in a total oracle exactly when it has
a persistent stage table uniformly computable in that oracle. Its presentation can be taken
to be the output projection of a normalized bounded simulation. -/
theorem recursiveIn_iff_exists_stagedPartial (O : ℕ → ℕ) (f : ℕ →. ℕ) :
    RecursiveIn {(O : ℕ →. ℕ)} f ↔ ∃ P : StagedPartial ℕ ℕ,
      ComputableIn₂ {(O : ℕ →. ℕ)} P.stage ∧ P.eval = f := by
  constructor
  · intro hf
    obtain ⟨c, hc⟩ := Oracle.Single.Code.exists_code.1 (RecursiveIn.iff_nat.1 hf)
    refine ⟨(c.stagedEval (fun z => some (O z))).map Oracle.Single.Code.Halt.output, ?_, ?_⟩
    · simpa only [ComputableIn₂, StagedPartial.stage_map] using
        (Primrec.option_map₁ Oracle.Single.Code.Halt.primrec_output).computableIn.comp
          (c.computableIn₂_stage_stagedEval O)
    · funext x
      rw [c.eval_map_stagedEval (O := (O : ℕ →. ℕ)) (by simp [eq_comm]), hc]
  · rintro ⟨P, hP, rfl⟩
    exact P.recursiveIn_eval hP

end TauCeti
