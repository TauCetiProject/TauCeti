/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Global symmetry between projective and injective dimensions

In an abelian category `C`, an object `X` has projective dimension `< n` when `Extⁱ(X, Y)`
vanishes for all `i ≥ n` and all `Y`, while `Y` has injective dimension `< n` when `Extⁱ(X, Y)`
vanishes for all `i ≥ n` and all `X`. Quantifying universally over both arguments makes the two
uniform dimension bounds identical: every object of `C` has projective dimension `< n` (or `≤ n`)
if and only if every object of `C` has injective dimension `< n` (or `≤ n`), and the suprema of
projective and injective dimensions over `C` coincide.

## Main results

* `CategoryTheory.forall_hasProjectiveDimensionLT_iff` and
  `CategoryTheory.forall_hasProjectiveDimensionLE_iff`: uniform projective and injective dimension
  bounds on an abelian category are equivalent.
* `CategoryTheory.iSup_projectiveDimension_eq_iSup_injectiveDimension`: the global projective and
  injective dimensions of an abelian category coincide.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 4.1.
-/

public section

open CategoryTheory

namespace CategoryTheory

variable (C : Type*) [Category* C] [Abelian C]

/-- Every object of an abelian category has projective dimension `< n` if and only if every object
has injective dimension `< n`: both conditions assert the vanishing of `Extⁱ(X, Y)` for all
`i ≥ n` and all `X, Y : C`. -/
theorem forall_hasProjectiveDimensionLT_iff (n : ℕ) :
    (∀ X : C, HasProjectiveDimensionLT X n) ↔ ∀ Y : C, HasInjectiveDimensionLT Y n := by
  let := HasExt.standard C
  simp only [hasProjectiveDimensionLT_iff, hasInjectiveDimensionLT_iff]
  exact ⟨fun h Y i hi X e ↦ h X i hi e, fun h X i hi Y e ↦ h Y i hi e⟩

/-- Every object of an abelian category has projective dimension `≤ n` if and only if every object
has injective dimension `≤ n`. -/
theorem forall_hasProjectiveDimensionLE_iff (n : ℕ) :
    (∀ X : C, HasProjectiveDimensionLE X n) ↔ ∀ Y : C, HasInjectiveDimensionLE Y n :=
  forall_hasProjectiveDimensionLT_iff C (n + 1)

/-- The supremum of projective dimensions over all objects of an abelian category equals the
supremum of injective dimensions. -/
theorem iSup_projectiveDimension_eq_iSup_injectiveDimension :
    (⨆ X : C, projectiveDimension X) = ⨆ Y : C, injectiveDimension Y := by
  apply eq_of_forall_ge_iff
  intro d
  induction d using WithBot.recBotCoe with
  | bot =>
    simp only [le_bot_iff, iSup_eq_bot, projectiveDimension_eq_bot_iff,
      injectiveDimension_eq_bot_iff]
  | coe d =>
    induction d with
    | top => simp
    | coe n =>
      simp only [WithBot.coe_natCast, iSup_le_iff, projectiveDimension_le_iff,
        injectiveDimension_le_iff]
      exact forall_hasProjectiveDimensionLE_iff C n

end CategoryTheory
