/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Harmonic

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
  rw [archWeight_eq_infinityType]
  exact χ.toHeckeCharacter.infinityType.archWeight_of_harmonicDegree_eq_zero
    (χ.harmonicDegree_eq_infinityType ▸ h) y

/-- `archWeight` is continuous on `realSpace K`. -/
@[fun_prop]
theorem continuous_archWeight (χ : Grossencharacter K 𝔪) : Continuous χ.archWeight := by
  simpa only [funext χ.archWeight_eq_infinityType] using
    χ.toHeckeCharacter.infinityType.continuous_archWeight

/-- **Radial scaling of `archWeight`** (Neukirch VII (8.3)): for `0 ≤ t`, scaling by
`surfaceScale x t` multiplies `archWeight x` by `t ^ (Tr(p) / (2 [K : ℚ]))`. -/
theorem archWeight_surfaceScale (χ : Grossencharacter K 𝔪) (x : realSpace K) {t : ℝ}
    (ht : 0 ≤ t) :
    χ.archWeight (surfaceScale x t) =
      χ.archWeight x * t ^ ((χ.harmonicDegree : ℝ) / (2 * Module.finrank ℚ K)) := by
  simp only [archWeight_eq_infinityType, harmonicDegree_eq_infinityType]
  exact χ.toHeckeCharacter.infinityType.archWeight_surfaceScale x ht

end TauCeti.LFunctions.Grossencharacter
