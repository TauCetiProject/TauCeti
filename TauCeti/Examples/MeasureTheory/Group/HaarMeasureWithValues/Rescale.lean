/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.ZMod.Defs
import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Rescale

/-!
# Examples: rescaling a Haar measure with values in a ring

* Rescaling by `0` gives the zero measure, hence zero multiplication.
* With counting volume on `C₂ = {1, s}` doubled, `(f ⋆ g)(1) = 2 (f(1) g(1) + f(s) g(s))`.
* Rescaling by `-1 ∈ ℤˣ` identifies the Hecke algebras of `-μ` and `μ`, through `f ↦ -f`.
-/

open TopologicalSpace LocallyConstant

namespace TauCeti.HaarMeasureWithValues

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

/-- Rescaling by `0` gives zero convolution. -/
example (μ : HaarMeasureWithValues ℚ G) (f g : compactlySupported ℚ G ℚ) :
    ((0 : ℚ) • μ).convolution f g = 0 := by
  rw [convolution_smul_measure, zero_smul]

/-- With doubled counting volume on `C₂ = {1, s}`, `(f ⋆ g)(1) = 2 (f(1) g(1) + f(s) g(s))`. -/
example (μ : HaarMeasureWithValues ℤ (Multiplicative (ZMod 2)))
    (h1 : μ ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩ = 1)
    (f g : compactlySupported ℤ (Multiplicative (ZMod 2)) ℤ) :
    (((2 : ℤ) • μ).convolution f g : LocallyConstant (Multiplicative (ZMod 2)) ℤ) 1 =
      2 * ((f : LocallyConstant (Multiplicative (ZMod 2)) ℤ) 1 *
          (g : LocallyConstant (Multiplicative (ZMod 2)) ℤ) 1 +
        (f : LocallyConstant (Multiplicative (ZMod 2)) ℤ) (Multiplicative.ofAdd 1) *
          (g : LocallyConstant (Multiplicative (ZMod 2)) ℤ) (Multiplicative.ofAdd 1)) := by
  have hsum (φ : Multiplicative (ZMod 2) → ℤ) : ∑ y, φ y = φ 1 + φ (Multiplicative.ofAdd 1) :=
    Fintype.sum_eq_add 1 (Multiplicative.ofAdd 1) (by decide) fun x hx ↦ by
      fin_cases x
      exacts [(hx.1 rfl).elim, (hx.2 rfl).elim]
  have hs : (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ = Multiplicative.ofAdd 1 := by decide
  simp only [convolution_smul_measure, Submodule.coe_smul, LocallyConstant.coe_smul, Pi.smul_apply,
    smul_eq_mul, convolution_apply_of_discrete, h1, one_mul, hsum, inv_one, mul_one, hs]

/-- Rescaling by the unit `-1` identifies `H(G, -μ)` with `H(G, μ)` through `f ↦ -f`. -/
example (μ : HaarMeasureWithValues ℤ G) (f : HeckeAlgebra (((-1 : ℤˣ) : ℤ) • μ)) :
    (HeckeAlgebra.rescaleRingEquiv μ (-1) f).toCompactlySupported = -f.toCompactlySupported := by
  rw [HeckeAlgebra.toCompactlySupported_rescaleRingEquiv]
  exact neg_one_smul ℤ _

end TauCeti.HaarMeasureWithValues
