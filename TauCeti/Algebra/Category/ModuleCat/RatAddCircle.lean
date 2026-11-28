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
* `ModuleCat.isIso_zsmul_id_rat`: multiplication by a nonzero integer is an automorphism of `ℚ`.
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

/-- Multiplication by a nonzero integer is an automorphism of the `ℤ`-module `ℚ`. -/
theorem isIso_zsmul_id_rat {m : ℤ} (hm : m ≠ 0) : IsIso (m • 𝟙 (ModuleCat.of ℤ ℚ)) := by
  have hm' : (m : ℚ) ≠ 0 := Int.cast_ne_zero.2 hm
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨(m : ℚ)⁻¹ * y, ?_⟩⟩
  · simp only [hom_smul, hom_id, zsmul_eq_mul] at hxy
    exact mul_left_cancel₀ hm' hxy
  · simp only [hom_smul, hom_id, zsmul_eq_mul]
    exact mul_inv_cancel_left₀ hm' y

end ModuleCat
