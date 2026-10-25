/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.ArrayLaw
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Relational.Dissociated
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Infinite.Sampling
import TauCeti.Dynamics.Ergodic.Action.Map

/-!
# Ergodic exchangeable graph laws as ergodic relational laws

The finitely supported permutations of `ℕ` act on configurations over `ℕ` by relabelling, and an
exchangeable law on configurations over `ℕ` is invariant under this action. An exchangeable law on
infinite graphs is dissociated exactly when the action is ergodic on its relational law, the law of
its encoding as configurations of the language of graphs.

A configuration of the language of graphs is the same as its array of truth values on the
adjacency atoms (`TauCeti.RelationalConfiguration.adjArrayEquiv`), and relabelling a configuration
relabels both axes of its array. Ergodicity therefore transfers along this equivariant measurable
equivalence to the array law, where dissociation is ergodicity of the diagonal finitary action
(`isDissociated_iff_ergodicSMul`).

Read through the generic correspondence between consistent finite marginals and invariant laws on
`ℕ`, this says that an exchangeable relational law of the language of graphs concentrated on simple
graphs is dissociated exactly when the finitary action is ergodic on its extension to `ℕ`. In
particular the relational law of the joint sampling law of any graphon, on any probability carrier,
is ergodic.

## Main results

* `TauCeti.RelationalConfiguration.adjArrayEquiv_finitaryPerm_smul` — the array of a
  relabelled configuration is the relabelled array;
* `TauCeti.DenseGraphLimits.isDissociated_iff_ergodicSMul_toRelationalLaw` — an exchangeable law
  on infinite graphs is dissociated exactly when the finitary action is ergodic on its relational
  law;
* `TauCeti.DenseGraphLimits.isDissociated_iff_ergodicSMul_exchangeableRelationalLawEquivInfinite`
  — an exchangeable relational law of the language of graphs concentrated on simple graphs is
  dissociated exactly when the finitary action is ergodic on its extension to `ℕ`;
* `TauCeti.DenseGraphLimits.ergodicSMul_map_toRelationalConfiguration_infiniteSampleLaw` — the
  relational law of the joint sampling law of a graphon is ergodic.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Section 5.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

open MeasureTheory TauCeti.RelationalConfiguration TauCeti.Probability

open _root_.FirstOrder (Language)

namespace TauCeti

namespace RelationalConfiguration

/-- Relabelling a configuration of the language of graphs relabels both axes of its array: the
measurable equivalence `adjArrayEquiv` is equivariant for the finitary actions. -/
@[simp]
theorem adjArrayEquiv_finitaryPerm_smul (g : FinitaryPerm)
    (c : RelationalConfiguration Language.graph ℕ) :
    adjArrayEquiv (g • c) = g • adjArrayEquiv c := by
  funext p
  simp

end RelationalConfiguration

namespace DenseGraphLimits

/-- **Dissociation is ergodicity of the relational law**: an exchangeable law on infinite graphs
is dissociated exactly when the finitely supported permutations of `ℕ` act ergodically on its
encoding as a law on configurations of the language of graphs. -/
theorem isDissociated_iff_ergodicSMul_toRelationalLaw (L : InfiniteExchangeableGraphLaw) :
    (exchangeableGraphLawEquivInfinite.symm L).IsDissociated ↔
      ErgodicSMul FinitaryPerm (RelationalConfiguration Language.graph ℕ)
        L.toRelationalLaw.law := by
  -- The array of the encoding of a graph is its adjacency array, so the array law is the image of
  -- the relational law under the equivariant measurable equivalence `adjArrayEquiv`.
  have hcomp : adjArrayEquiv ∘ SimpleGraph.toRelationalConfiguration =
      (SimpleGraph.adjArray : SimpleGraph ℕ → ℕ × ℕ → Bool) :=
    funext SimpleGraph.adjArrayEquiv_toRelationalConfiguration
  have harray : arrayLaw L.law = L.toRelationalLaw.law.map adjArrayEquiv := by
    rw [InfiniteExchangeableGraphLaw.toRelationalLaw_law,
      Measure.map_map adjArrayEquiv.measurable SimpleGraph.measurable_toRelationalConfiguration,
      hcomp, arrayLaw_def]
  rw [isDissociated_iff_ergodicSMul, harray,
    adjArrayEquiv.measurableEmbedding.ergodicSMul_map_iff adjArrayEquiv_finitaryPerm_smul]

/-- **Dissociated relational laws of graphs are the ergodic ones.** An exchangeable relational law
of the language of graphs whose marginals are concentrated on simple graphs is dissociated exactly
when the finitely supported permutations of `ℕ` act ergodically on its extension to a law on
configurations over `ℕ`. -/
theorem isDissociated_iff_ergodicSMul_exchangeableRelationalLawEquivInfinite
    {ν : ExchangeableRelationalLaw Language.graph} (hν : ∀ n, ∀ᵐ c ∂ν.law n, IsSimpleGraph c) :
    ν.IsDissociated ↔ ErgodicSMul FinitaryPerm (RelationalConfiguration Language.graph ℕ)
      (exchangeableRelationalLawEquivInfinite Language.graph ν).law := by
  -- Write `ν` as the relational law of a graph law and transport along the graph extension.
  obtain ⟨L, hL⟩ := ExchangeableGraphLaw.relationalLawEquiv.surjective ⟨ν, hν⟩
  obtain rfl : L.toRelationalLaw = ν := by
    rw [← ExchangeableGraphLaw.coe_relationalLawEquiv, hL]
  rw [ExchangeableGraphLaw.isDissociated_toRelationalLaw_iff,
    ExchangeableGraphLaw.exchangeableRelationalLawEquivInfinite_toRelationalLaw,
    ← isDissociated_iff_ergodicSMul_toRelationalLaw, Equiv.symm_apply_apply]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Graphon samples are ergodic**: the finitely supported permutations of `ℕ` act ergodically on
the joint sampling law of a graphon, on any probability carrier, encoded as a law on configurations
of the language of graphs. -/
theorem ergodicSMul_map_toRelationalConfiguration_infiniteSampleLaw (W : Graphon Ω μ) :
    ErgodicSMul FinitaryPerm (RelationalConfiguration Language.graph ℕ)
      ((infiniteSampleLaw W).map SimpleGraph.toRelationalConfiguration) := by
  rw [infiniteSampleLaw_eq_extension, ← InfiniteExchangeableGraphLaw.toRelationalLaw_law,
    ← isDissociated_iff_ergodicSMul_toRelationalLaw, Equiv.symm_apply_apply]
  exact isDissociated_sampleExchangeableLaw W

end DenseGraphLimits

end TauCeti
