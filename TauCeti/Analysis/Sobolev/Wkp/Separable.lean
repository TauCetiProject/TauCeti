/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.MeyersSerrin
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Separability of higher-order Sobolev spaces

For finite `p`, the iterated weak-derivative graph topology on `W^{k,p}(Ω)` is second
countable, hence separable, on every open set `Ω`. No boundedness or boundary regularity
is needed. Combining this with smooth-interior density gives a countable dense family
whose members have smooth representatives on `Ω`.

The topology is the full Sobolev topology, not the topology inherited from the value map
into `Lᵖ`. The finite-exponent hypothesis is essential: no separability assertion is made
for `W^{k,∞}`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set
open scoped ContDiff

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- At every order and finite exponent, the full weak Sobolev topology is second countable. -/
instance Wkp.instSecondCountableTopology [Fact (p ≠ ⊤)] (k : ℕ) :
    SecondCountableTopology (Wkp mu Omega p k) := by
  cases k with
  | zero => exact inferInstance
  | succ k =>
    induction k with
    | zero =>
      -- Order one is definitionally `W1p`, whose topology is the subspace topology of
      -- its value-gradient `Lᵖ` jet.
      exact (inferInstance : SecondCountableTopology (W1p mu Omega p))
    | succ k ih =>
      have := ih
      -- The successor stage is the weak-derivative graph in the product of the previous
      -- stage and the finite-dimensional-derivative-valued `Lᵖ` space.
      exact (inferInstance : SecondCountableTopology
        (WeakDerivStep mu Omega p
          (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL))

/-- Every finite-exponent Sobolev space has a countable dense subset consisting of classes
with smooth representatives on the domain. -/
theorem Wkp.exists_countable_dense_contDiffOn_representatives (hp : p ≠ ⊤) (k : ℕ) :
    ∃ s : Set (Wkp mu Omega p k), s.Countable ∧ Dense s ∧
      ∀ u ∈ s, ∃ f : E → ℝ, ContDiffOn ℝ ∞ f Omega ∧
        (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f := by
  let : Fact (p ≠ ⊤) := ⟨hp⟩
  obtain ⟨s, hs, hcount, hdense⟩ := Dense.exists_countable_dense_subset
    (Wkp.dense_contDiffOn_representatives (mu := mu) (Omega := Omega) hp k)
  exact ⟨s, hcount, hdense, hs⟩

end TauCeti
