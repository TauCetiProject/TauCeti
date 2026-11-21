/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Stage
public import TauCeti.Computability.RecursiveIn

/-!
# Oracle-relative computability of normalized stage evaluation

A normalized stage simulation uses only the finite prefix of optional oracle answers up to
the stage. If those answers are uniformly computable in an oracle family, so is the simulation.
-/

public section

namespace TauCeti.Oracle.Single.Code

/-- Normalized stage evaluation of optional answers uniformly computable in `G` is uniformly
computable in `G`. To simulate stage `s` it suffices to read the first `s` answers. -/
theorem computableIn_evalStage {α : Type*} [Primcodable α] {G : Set (ℕ →. ℕ)}
    {σ : α → ℕ → Option ℕ} (hσ : ComputableIn₂ G σ) :
    ComputableIn G fun p : α × ℕ × Code × ℕ =>
      evalStage (σ p.1) p.2.1 p.2.2.1 p.2.2.2 := by
  have hp : ComputableIn G fun p : α × ℕ × Code × ℕ => (List.range p.2.1).map (σ p.1) :=
    hσ.list_range_map.comp (ComputableIn.fst.pair (ComputableIn.fst.comp ComputableIn.snd))
  have hlookup : Primrec₂ fun (l : List (Option ℕ)) z => l[z]?.bind id :=
    (Primrec.option_bind₁ Primrec.id).comp Primrec.list_getElem?
  have hsim := (primrec_evalStage hlookup).computableIn.comp (hp.pair ComputableIn.snd)
  refine RecursiveIn.of_eq hsim fun p => congrArg Part.some ?_
  apply Option.ext
  intro d
  simp only [evalStage_eq_some_iff, evaln_range_map_option]

end TauCeti.Oracle.Single.Code
