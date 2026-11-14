/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Additive.Convolution
public import TauCeti.Analysis.InnerProductSpace.Gram.PosSemidef
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Positive-definite finite-set convolutions

The convolution of a finite subset of a group with its inverse is positive definite.
It counts the overlap of the set with its left translates, and is the coefficient of its
indicator in the counting-measure regular representation. Normalizing these functions gives
finitely supported approximations to the constant function one from Følner sets.

The argument is the finite-set version of the regular-representation coefficient construction;
see Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*, Appendix G.5.
-/

public section

open MeasureTheory
open scoped Pointwise ComplexOrder

namespace Finset

variable {G 𝕜 : Type*} [Group G] [DecidableEq G] [RCLike 𝕜]

/-- The convolution of a finite set with its inverse is positive definite, over either `ℝ`
or `ℂ`. -/
theorem posSemidef_convolution_inv (F : Finset G) :
    (Matrix.of fun g h : G ↦ (F.convolution F⁻¹ (g⁻¹ * h) : 𝕜)).PosSemidef := by
  let : MeasurableSpace G := ⊤
  let v (g : G) : Lp 𝕜 2 (Measure.count : Measure G) :=
    indicatorConstLp 2 (g • F).measurableSet (by simp) (1 : 𝕜)
  convert TauCeti.posSemidef_gram 𝕜 v using 1
  ext g h
  rw [Matrix.of_apply, Matrix.gram_apply,
    L2.inner_indicatorConstLp_one_indicatorConstLp_one _ _ (by simp) (by simp)]
  simp [measureReal_def, ← Finset.coe_inter, card_smul_inter_smul,
    -Finset.coe_smul_finset]

end Finset
