/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Harmonic
public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Haar
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Regularity, triviality, and radial scaling for `Grossencharacter.archWeight`

This module complements `TauCeti.NumberTheory.LFunctions.Grossencharacter.Harmonic` with the
properties of the archimedean parameter weight `χ.archWeight y = ∏_w y_w ^ (P_w / 2)`
(`P_w = χ.harmonicExponent w`) needed for Hecke's twisted theta series and Mellin kernel:

* `archWeight_of_harmonicDegree_eq_zero`: when `χ.harmonicDegree = 0`, `χ.archWeight` is
  identically `1`;
* `continuous_archWeight`: continuity on `realSpace K`;
* `archWeight_surfaceScale`: radial scaling under `surfaceScale x t` (Neukirch VII (8.3)).

## References

* E. Hecke, *Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen
  (Zweite Mitteilung)*, Math. Z. **6** (1920), 11–51.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §8.
-/

public section

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Real

namespace TauCeti.LFunctions.Grossencharacter

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- When `harmonicDegree` vanishes, `archWeight` is identically `1`. -/
theorem archWeight_of_harmonicDegree_eq_zero {χ : Grossencharacter K 𝔪}
    (h : χ.harmonicDegree = 0) (y : realSpace K) : χ.archWeight y = 1 := by
  have hw : ∀ w, χ.harmonicExponent w = 0 := by
    classical simpa [harmonicDegree_def] using h
  simp [archWeight_def, hw]

@[fun_prop]
theorem continuous_archWeight (χ : Grossencharacter K 𝔪) : Continuous χ.archWeight := by
  rw [funext χ.archWeight_def]
  exact continuous_finsetProd _ fun w _ ↦ (continuous_apply w).rpow_const fun _ ↦
    Or.inr (by positivity)

/-- **Radial scaling of `archWeight`** (Neukirch VII (8.3)): for `0 ≤ t`, scaling by
`surfaceScale x t` multiplies `archWeight x` by `t ^ (Tr(p) / (2 [K : ℚ]))`. -/
theorem archWeight_surfaceScale (χ : Grossencharacter K 𝔪) (x : realSpace K) {t : ℝ}
    (ht : 0 ≤ t) :
    χ.archWeight (surfaceScale x t) =
      χ.archWeight x * t ^ ((χ.harmonicDegree : ℝ) / (2 * Module.finrank ℚ K)) := by
  have hsplit : χ.archWeight (surfaceScale x t) =
      χ.archWeight x *
        ∏ w : InfinitePlace K, t ^ ((χ.harmonicExponent w : ℝ) / (2 * Module.finrank ℚ K)) := by
    rw [archWeight_def, archWeight_def, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [surfaceScale_apply, mul_comm (x w), Real.mul_rpow_of_nonneg_left (Real.rpow_nonneg ht _),
      mul_comm, ← Real.rpow_mul ht]
    congr 2
    ring
  rw [hsplit]
  congr 1
  rw [← Real.rpow_sum_of_nonneg ht fun _ _ ↦ by positivity, ← Finset.sum_div, ← Nat.cast_sum,
    ← harmonicDegree_def]

end TauCeti.LFunctions.Grossencharacter
