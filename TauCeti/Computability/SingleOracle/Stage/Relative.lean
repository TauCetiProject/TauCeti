/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Stage
public import TauCeti.Computability.RecursiveIn
import TauCeti.Computability.SingleOracle.Relative

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
  simpa only [evalStage_def] using primrec_normalizeStage.computableIn.comp
    (((ComputableIn.fst.comp ComputableIn.snd).pair
      (ComputableIn.fst.comp (ComputableIn.snd.comp ComputableIn.snd))).pair
      (computableIn_evaln_option hσ))

end TauCeti.Oracle.Single.Code
