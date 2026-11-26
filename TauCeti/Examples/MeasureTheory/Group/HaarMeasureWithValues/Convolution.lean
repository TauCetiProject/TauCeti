/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.ZMod.Defs
import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Convolution

/-!
# Examples of convolution against a Haar measure with values in a ring

This file tests `TauCeti.HaarMeasureWithValues.convolution` and `TauCeti.HeckeAlgebra`:

* zero volume gives zero multiplication;
* for `C₂ = {1, s}` with counting volume, `(f ⋆ g)(1) = f(1) g(1) + f(s) g(s)`;
* the Hecke algebra over a commutative ring is an associative non-unital ring whose
  multiplication is convolution.
-/

open TopologicalSpace LocallyConstant

namespace TauCeti.HaarMeasureWithValues

variable {A G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

/-! ### 1. Zero volume -/

example [CommRing A] (f g : compactlySupported A G A) :
    (0 : HaarMeasureWithValues A G).convolution f g = 0 := by
  simp

/-! ### 2. The group of order two -/

/-- With counting volume on `C₂ = {1, s}`, `(f ⋆ g)(1) = f(1) g(1) + f(s) g(s)`. -/
example (μ : HaarMeasureWithValues ℤ (Multiplicative (ZMod 2)))
    (h1 : μ ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩ = 1)
    (f g : compactlySupported ℤ (Multiplicative (ZMod 2)) ℤ) :
    (μ.convolution f g : LocallyConstant (Multiplicative (ZMod 2)) ℤ) 1 =
      (f : LocallyConstant (Multiplicative (ZMod 2)) ℤ) 1 *
          (g : LocallyConstant (Multiplicative (ZMod 2)) ℤ) 1 +
        (f : LocallyConstant (Multiplicative (ZMod 2)) ℤ) (Multiplicative.ofAdd 1) *
          (g : LocallyConstant (Multiplicative (ZMod 2)) ℤ) (Multiplicative.ofAdd 1) := by
  rw [convolution_apply_of_discrete, h1, one_smul,
    Fintype.sum_eq_add 1 (Multiplicative.ofAdd 1) (by decide) fun x hx ↦ by
      fin_cases x
      exacts [(hx.1 rfl).elim, (hx.2 rfl).elim]]
  have hs : (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ * 1 = Multiplicative.ofAdd 1 := by decide
  rw [inv_one, mul_one, hs]

/-! ### 3. The Hecke algebra -/

example [CommRing A] (μ : HaarMeasureWithValues A G) (f₁ f₂ f₃ : HeckeAlgebra μ) :
    f₁ * (f₂ - f₃) = f₁ * f₂ - f₁ * f₃ ∧ f₁ * f₂ * f₃ = f₁ * (f₂ * f₃) :=
  ⟨mul_sub f₁ f₂ f₃, mul_assoc f₁ f₂ f₃⟩

example [CommRing A] (μ : HaarMeasureWithValues A G) (f₁ f₂ : HeckeAlgebra μ) :
    HeckeAlgebra.linearEquiv μ (f₁ * f₂) =
      μ.convolution (HeckeAlgebra.linearEquiv μ f₁) (HeckeAlgebra.linearEquiv μ f₂) := by
  simp

end TauCeti.HaarMeasureWithValues
