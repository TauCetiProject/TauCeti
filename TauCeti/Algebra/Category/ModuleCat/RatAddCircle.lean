/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

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
abbrev ratAddCircleShortComplex : ShortComplex (ModuleCat.{0} ℤ) :=
  .moduleCatMk (Int.castAddHom ℚ).toIntLinearMap
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).toIntLinearMap (by ext; simp)

/-- The sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` of `ℤ`-modules is short exact. -/
theorem ratAddCircleShortComplex_shortExact : ratAddCircleShortComplex.ShortExact :=
  -- exactness at `ℚ` says that `x : ℚ` vanishes modulo `1` iff it lies in `zmultiples 1`, the
  -- image of `Int.cast`. The three facts are applied pointwise because the maps of
  -- `ShortComplex.moduleCatMk` are `ModuleCat.ofHom`s, which unify with the plain functions only
  -- after applying them to an element.
  shortComplex_shortExact _
    (fun (x : ℚ) ↦ by
      change (x : AddCircle (1 : ℚ)) = 0 ↔ ∃ n : ℤ, (n : ℚ) = x
      simp [AddSubgroup.mem_zmultiples_iff])
    (fun _ _ h ↦ Int.cast_injective (α := ℚ) h)
    (fun x ↦ QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℚ)) x)

end ModuleCat
