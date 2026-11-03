/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.SetTheory.Descriptive.ClosedEquivalence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Classifying closed equivalence relations

The kernel of a continuous map from a Polish space to any Hausdorff space has a measurable
classification by Cantor space. In particular, this applies to equality of absolute values on
`ℝ`. The target of the original continuous map need not itself be Polish or measurable.
-/

/-- Continuous kernels have countably separated measurable quotients. -/
example {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [TopologicalSpace Y] [T2Space Y] {f : X → Y}
    (hf : Continuous f) : MeasurableSpace.CountablySeparated (Quotient (Setoid.ker f)) :=
  (Setoid.ker f).countablySeparated_quotient_of_isClosed
    (isClosed_eq (hf.comp continuous_fst) (hf.comp continuous_snd))

/-- Equality of absolute values on the reals admits a measurable classification by Cantor
space. -/
example : ∃ f : ℝ → (ℕ → Bool), Measurable f ∧ ∀ x y, f x = f y ↔ |x| = |y| := by
  obtain ⟨f, hf, hE⟩ := Setoid.isSmooth_iff.mp <|
    (Setoid.ker (abs : ℝ → ℝ)).isSmooth_of_isClosed
      (isClosed_eq (continuous_abs.comp continuous_fst) (continuous_abs.comp continuous_snd))
  exact ⟨f, hf, fun x y => (hE x y).symm⟩
