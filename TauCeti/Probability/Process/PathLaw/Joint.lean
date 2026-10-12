/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.PathLaw.FiniteMarginals
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Joint laws of random elements and paths

For a process `X : ℕ → Ω → α` carried along by a random element `Y : Ω → β`,
`jointPathLaw μ X Y` is the law of the pair `(Y ω, fun i => X i ω)` on `β × (ℕ → α)`.

## Main declarations

* `jointPathLaw` — the definition, with `jointPathLaw_def` its unfolding;
* `map_fst_jointPathLaw`, `map_snd_jointPathLaw` — the two marginals, `μ.map Y` and
  `pathLaw μ X`;
* `map_prefixProjPair_jointPathLaw` — the pushforward along the paired prefix projection.

These constructions require no symmetry or conditional-independence hypothesis. They support
joint distribution arguments in which a random parameter is retained alongside a process path.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure Ω} {X : ℕ → Ω → α} {Y : Ω → β}

/-- The joint law of a random element together with a process path. -/
def jointPathLaw (μ : Measure Ω) (X : ℕ → Ω → α) (Y : Ω → β) :
    Measure (β × (ℕ → α)) :=
  μ.map fun ω => (Y ω, fun i => X i ω)

/-- The definitional expansion of `jointPathLaw`: the pushforward of `μ` along
`ω ↦ (Y ω, fun i => X i ω)`. -/
@[simp]
theorem jointPathLaw_def (μ : Measure Ω) (X : ℕ → Ω → α) (Y : Ω → β) :
    jointPathLaw μ X Y = μ.map fun ω => (Y ω, fun i => X i ω) := (rfl)

/-- The first marginal of the joint path law is the law of the random element. -/
-- `@[grind =>]` rather than `@[simp]`: `jointPathLaw_def` is the registered simp normal form, so
-- simp rewrites this left-hand side away before the lemma could fire and `simpNF` rejects the
-- annotation; `grind` is not subject to that normalisation.
@[grind =>]
theorem map_fst_jointPathLaw (hY : AEMeasurable Y μ) (hX : ∀ i, AEMeasurable (X i) μ) :
    (jointPathLaw μ X Y).map Prod.fst = μ.map Y := by
  rw [jointPathLaw_def]
  exact Measure.fst_map_prodMk₀ hY (AEMeasurable.of_eval hX)

/-- The second marginal of the joint path law is the law of the path. -/
@[grind =>]
theorem map_snd_jointPathLaw (hY : AEMeasurable Y μ) (hX : ∀ i, AEMeasurable (X i) μ) :
    (jointPathLaw μ X Y).map Prod.snd = pathLaw μ X := by
  rw [jointPathLaw_def, pathLaw_def]
  exact Measure.snd_map_prodMk₀ hY (AEMeasurable.of_eval hX)

/-- The prefix pushforward of the joint path law is the joint law of the random element and the
first `n` process coordinates. -/
theorem map_prefixProjPair_jointPathLaw (hX : ∀ i, AEMeasurable (X i) μ) (hY : AEMeasurable Y μ)
    (n : ℕ) :
    (jointPathLaw μ X Y).map (prefixProjPair β α n)
      = μ.map fun ω => (Y ω, fun i : Fin n => X i ω) := by
  have hpath : AEMeasurable (fun ω => (Y ω, fun i => X i ω) : Ω → β × (ℕ → α)) μ :=
    hY.prodMk (AEMeasurable.of_eval hX)
  rw [jointPathLaw_def,
    AEMeasurable.map_map_of_aemeasurable
      (measurable_prefixProjPair β α n).aemeasurable hpath]
  simp only [Function.comp_def, prefixProjPair_apply]

end Probability

end TauCeti

end

end
