/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Data.ZMod.Defs
public import Mathlib.NumberTheory.Padics.ProperSpace
public import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.HeckeUnit
public import TauCeti.Topology.Algebra.Nonarchimedean.Basic

/-!
# Examples: identity elements for convolution

* On the discrete group `Multiplicative (ZMod 3)` with counting volume (`μ({1}) = 1`), the point
  mass at its identity `1` (the element `0` of `ZMod 3`) is a two-sided identity for convolution
  on `C_c^∞(Multiplicative (ZMod 3), ℤ)`.
* On `ℤ_p`, which is not discrete, no element of `C_c^∞(ℤ_p, ℚ)` is a left identity for
  convolution, for any `ℚ`-valued Haar measure.
-/

public section

open TopologicalSpace LocallyConstant

namespace TauCeti.HaarMeasureWithValues

/-- With counting volume on `Multiplicative (ZMod 3)`, the point mass at its identity `1` (the
element `0` of `ZMod 3`) is an identity for convolution. -/
example (μ : HaarMeasureWithValues ℤ (Multiplicative (ZMod 3)))
    (h1 : μ ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩ = 1)
    (f : compactlySupported ℤ (Multiplicative (ZMod 3)) ℤ) :
    μ.convolution ⟨compactOpenIndicator ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩ 1,
        compactOpenIndicator_mem_compactlySupported _ 1⟩ f = f ∧
      μ.convolution f ⟨compactOpenIndicator ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩ 1,
        compactOpenIndicator_mem_compactlySupported _ 1⟩ = f := by
  rw [convolution_compactOpenIndicator_singleton_one_left,
    convolution_compactOpenIndicator_singleton_one_right, h1, one_mul, one_smul]
  exact ⟨rfl, rfl⟩

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- Convolution on `C_c^∞(ℤ_p, ℚ)` has no left identity, whatever the `ℚ`-valued Haar measure:
`ℤ_p` is compact and infinite, so not discrete. -/
example (μ : HaarMeasureWithValues ℚ (Multiplicative ℤ_[p])) :
    ¬∃ e : compactlySupported ℚ (Multiplicative ℤ_[p]) ℚ, ∀ f, μ.convolution e f = f := by
  rintro ⟨e, he⟩
  have : WeaklyLocallyCompactSpace (Multiplicative ℤ_[p]) :=
    inferInstanceAs (WeaklyLocallyCompactSpace ℤ_[p])
  have := μ.discreteTopology_of_forall_convolution_eq_left he
  have : CompactSpace (Multiplicative ℤ_[p]) := inferInstanceAs (CompactSpace ℤ_[p])
  have : Finite (Multiplicative ℤ_[p]) := finite_of_compact_of_discrete
  have : Infinite (Multiplicative ℤ_[p]) :=
    Infinite.of_injective (fun n : ℕ ↦ Multiplicative.ofAdd (n : ℤ_[p]))
      fun _ _ h ↦ Nat.cast_injective (Multiplicative.ofAdd.injective h)
  exact not_finite (Multiplicative ℤ_[p])

end Padic

end TauCeti.HaarMeasureWithValues
