/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Array
public import TauCeti.Probability.Process.PathLaw.Joint

/-!
# Array laws as laws of row and column processes

An array process `X : ℕ × ℕ → Ω → α` can be read either as a process of row paths or as a
process of column paths. Currying identifies the row-path law with the array law, while currying
followed by transposition does the same for columns. The corresponding identities also retain an
auxiliary random element in a joint path law.

These transport results require only coordinatewise almost-everywhere measurability. In particular,
they apply independently of any exchangeability or conditional-independence hypothesis.

## Main results

* `TauCeti.Probability.map_uncurry_pathLaw_arrayRow` and
  `TauCeti.Probability.map_uncurrySwap_pathLaw_arrayCol` identify the array law with the path law
  of its row and column processes;
* `TauCeti.Probability.map_uncurry_jointPathLaw_arrayRow` and
  `TauCeti.Probability.map_uncurrySwap_jointPathLaw_arrayCol` give the corresponding identities
  while retaining an auxiliary random element.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure Ω} {X : ℕ × ℕ → Ω → α} {Y : Ω → β}

/-- **An array law is the uncurried path law of its row process.** A statement about the law of
the row process therefore transports to one about the law of the array. -/
theorem map_uncurry_pathLaw_arrayRow (hX : ∀ p, AEMeasurable (X p) μ) :
    (pathLaw μ (arrayRow X)).map Function.uncurry = μ.map fun ω p ↦ X p ω := by
  rw [pathLaw_def, AEMeasurable.map_map_of_aemeasurable measurable_uncurry.aemeasurable
    (AEMeasurable.of_eval fun i ↦ aemeasurable_arrayRow hX i)]
  refine congrArg (Measure.map · _) ?_
  funext ω ⟨i, j⟩
  simp

/-- **An array law is the transposed uncurried path law of its column process.** A statement about
the law of the column process therefore transports to one about the law of the array. -/
theorem map_uncurrySwap_pathLaw_arrayCol (hX : ∀ p, AEMeasurable (X p) μ) :
    (pathLaw μ (arrayCol X)).map
        (fun x : ℕ → ℕ → α ↦ fun p : ℕ × ℕ ↦ x p.2 p.1) =
      μ.map fun ω p ↦ X p ω := by
  rw [pathLaw_def, AEMeasurable.map_map_of_aemeasurable
    (by fun_prop : Measurable fun x : ℕ → ℕ → α ↦ fun p : ℕ × ℕ ↦ x p.2 p.1).aemeasurable
    (AEMeasurable.of_eval fun j ↦ aemeasurable_arrayCol hX j)]
  refine congrArg (Measure.map · _) ?_
  funext ω ⟨i, j⟩
  simp

/-- Reassembling an array from its row process turns the joint law of a random element and the row
process into the joint law of that random element and the array. -/
theorem map_uncurry_jointPathLaw_arrayRow (hX : ∀ p, AEMeasurable (X p) μ)
    (hY : AEMeasurable Y μ) :
    (jointPathLaw μ (arrayRow X) Y).map (Prod.map id Function.uncurry)
      = μ.map fun ω ↦ (Y ω, fun p : ℕ × ℕ ↦ X p ω) := by
  rw [jointPathLaw_def, AEMeasurable.map_map_of_aemeasurable
    (measurable_id.prodMap measurable_uncurry).aemeasurable
    (hY.prodMk (AEMeasurable.of_eval (aemeasurable_arrayRow hX)))]
  refine congrArg (Measure.map · _) (funext fun ω ↦ Prod.ext rfl (funext fun p ↦ ?_))
  simp [Function.uncurry]

/-- Reassembling an array from its column process turns the joint law of a random element and the
column process into the joint law of that random element and the array. -/
theorem map_uncurrySwap_jointPathLaw_arrayCol (hX : ∀ p, AEMeasurable (X p) μ)
    (hY : AEMeasurable Y μ) :
    (jointPathLaw μ (arrayCol X) Y).map
        (Prod.map id fun x : ℕ → ℕ → α ↦ fun p : ℕ × ℕ ↦ x p.2 p.1)
      = μ.map fun ω ↦ (Y ω, fun p : ℕ × ℕ ↦ X p ω) := by
  rw [jointPathLaw_def, AEMeasurable.map_map_of_aemeasurable
    (measurable_id.prodMap
      (by fun_prop : Measurable fun x : ℕ → ℕ → α ↦ fun p : ℕ × ℕ ↦ x p.2 p.1)).aemeasurable
    (hY.prodMk (AEMeasurable.of_eval (aemeasurable_arrayCol hX)))]
  refine congrArg (Measure.map · _) (funext fun ω ↦ Prod.ext rfl (funext fun p ↦ ?_))
  simp

end Probability

end TauCeti

end

end
