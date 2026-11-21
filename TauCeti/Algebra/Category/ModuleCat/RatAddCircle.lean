/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# The short exact sequence `0 → ℤ → ℚ → ℚ/ℤ → 0`

The inclusion of the integers into the rationals followed by reduction modulo `1`, with `ℚ/ℤ`
realized as the rational circle `AddCircle (1 : ℚ)`, is a short exact sequence of `ℤ`-modules.

## Main definitions

* `ModuleCat.ratAddCircleShortComplex`: the short complex `ℤ → ℚ → ℚ/ℤ` of `ℤ`-modules.

## Main results

* `ModuleCat.ratAddCircleShortComplex_shortExact`: `0 → ℤ → ℚ → ℚ/ℤ → 0` is short exact.
-/

public noncomputable section

open CategoryTheory

namespace ModuleCat

/-- The short complex `ℤ → ℚ → ℚ/ℤ` of `ℤ`-modules, with `ℚ/ℤ` the rational circle
`AddCircle (1 : ℚ)`: the inclusion of the integers followed by reduction modulo `1`. -/
abbrev ratAddCircleShortComplex : ShortComplex (ModuleCat.{0} ℤ) where
  X₁ := .of ℤ ℤ
  X₂ := .of ℤ ℚ
  X₃ := .of ℤ (AddCircle (1 : ℚ))
  f := ofHom (Int.castAddHom ℚ).toIntLinearMap
  g := ofHom (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).toIntLinearMap
  zero := by ext; simp

/-- The sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` of `ℤ`-modules is short exact. -/
theorem ratAddCircleShortComplex_shortExact : ratAddCircleShortComplex.ShortExact :=
  -- exactness at `ℚ`: `x : ℚ` vanishes modulo `1` iff it lies in `zmultiples 1`, the image of
  -- `Int.cast`
  shortComplex_shortExact _ (fun _ ↦ by simp [AddSubgroup.mem_zmultiples_iff])
    (by simpa using Int.cast_injective) (by simpa using QuotientAddGroup.mk_surjective)

end ModuleCat
