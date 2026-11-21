/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.CompletedCoordinateAction
public import TauCeti.Algebra.Lie.Current.Sugawara

/-!
# Scaling of normally ordered and Segal--Sugawara modes

The formal homothety `t ↦ u t`, for a unit `u`, acts on the current generator of integer
mode `m` by `u ^ m`. Each summand of the normally ordered quadratic mode of degree `n`
therefore scales by `u ^ n`. Continuity of the coordinate action passes this identity to
the convergent normally ordered mode, and hence to the Segal--Sugawara mode `Sₙ`.

These formulas hold over every field, at every central value and for all integer modes.
-/

public section

noncomputable section

open scoped LaurentSeries

namespace TauCeti.CurrentAlgebra

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
variable (Φ : LinearMap.BilinForm K L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : K)

/-- Every summand of a normally ordered mode scales with its total mode, at any cut. -/
@[simp]
theorem coordinateEnvelopingAut_homothety_normalOrderedSummand
    (u : Kˣ) (p n m : ℤ) (x y : L) :
    coordinateEnvelopingAut Φ hΦ hΦs a (FormalCoordinate.homothety u).substAlgEquiv
        (normalOrderedSummand Φ hΦ hΦs a p n m x y) =
      (u : K) ^ n • normalOrderedSummand Φ hΦ hΦs a p n m x y := by
  have hu : (u : K) ^ m * (u : K) ^ (n - m) = (u : K) ^ n := by
    rw [← zpow_add₀ u.ne_zero, add_sub_cancel]
  have hu' : (u : K) ^ (n - m) * (u : K) ^ m = (u : K) ^ n := by
    rw [mul_comm, hu]
  simp only [normalOrderedSummand_apply]
  split_ifs <;>
    simp only [map_mul, coordinateEnvelopingAut_homothety_envelopingι,
      smul_mul_smul, hu, hu']

/-- A formal homothety scales the convergent normally ordered mode of degree `n` by `u ^ n`. -/
@[simp]
theorem coordinateCompletedEnvelopingAut_homothety_normalOrderedMode
    (u : Kˣ) (n : ℤ) (x y : L) :
    coordinateCompletedEnvelopingAut Φ hΦ hΦs a (FormalCoordinate.homothety u).substAlgEquiv
        (normalOrderedMode Φ hΦ hΦs a n x y) =
      (u : K) ^ n • normalOrderedMode Φ hΦ hΦs a n x y := by
  refine ((hasSum_normalOrderedMode n x y).map
    (coordinateCompletedEnvelopingAut Φ hΦ hΦs a (FormalCoordinate.homothety u).substAlgEquiv)
    (continuous_coordinateCompletedEnvelopingAut _)).unique ?_
  have hs := (hasSum_normalOrderedMode (Φ := Φ) (hΦ := hΦ) (hΦs := hΦs) (a := a) n x y).mul_left
    (algebraMap K (CompletedEnveloping Φ hΦ hΦs a) ((u : K) ^ n))
  convert hs using 1
  · ext m
    dsimp only [Function.comp_def]
    rw [coe_toCompletedEnveloping, coordinateCompletedEnvelopingAut_toLimQuotients,
      ← coe_toCompletedEnveloping, coordinateEnvelopingAut_homothety_normalOrderedSummand,
      map_smul, Algebra.smul_def]
  · rw [Algebra.smul_def]

variable [FiniteDimensional K L] [LieAlgebra.IsKilling K L]

/-- Under the coordinate substitution `t ↦ u t`, the Segal--Sugawara mode `Sₙ` maps to
`u ^ n • Sₙ`. This holds at every central value, without a critical-level assumption. -/
@[simp]
theorem coordinateCompletedEnvelopingAut_homothety_sugawaraMode (u : Kˣ) (n : ℤ) :
    coordinateCompletedEnvelopingAut Φ hΦ hΦs a (FormalCoordinate.homothety u).substAlgEquiv
        (sugawaraMode Φ hΦ hΦs a n) =
      (u : K) ^ n • sugawaraMode Φ hΦ hΦs a n := by
  rw [sugawaraMode_eq_sum (Module.finBasis K L), map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ ↦
    coordinateCompletedEnvelopingAut_homothety_normalOrderedMode Φ hΦ hΦs a u n _ _

end TauCeti.CurrentAlgebra
