/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Global symmetry of projective and injective dimension bounds

In an abelian category `C`, both `HasProjectiveDimensionLT X n` and `HasInjectiveDimensionLT Y n`
express the vanishing of `Abelian.Ext X Y i` for all `n ≤ i`. Quantifying universally over all
objects of `C` therefore identifies uniform bounds on projective and injective dimension.

## Main results

* `CategoryTheory.hasInjectiveDimensionLE_of_forall_hasProjectiveDimensionLE` and
  `CategoryTheory.hasProjectiveDimensionLE_of_forall_hasInjectiveDimensionLE`: a uniform
  projective (resp. injective) dimension bound on all objects implies the same injective
  (resp. projective) dimension bound.
* `CategoryTheory.forall_hasProjectiveDimensionLT_iff_forall_hasInjectiveDimensionLT` and
  `CategoryTheory.forall_hasProjectiveDimensionLE_iff_forall_hasInjectiveDimensionLE`: uniform
  projective and injective dimension bounds on all objects of `C` are equivalent.
-/

public section

namespace CategoryTheory

variable {C : Type*} [Category* C] [Abelian C]

/-- If every object of an abelian category has projective dimension `< n`, then every object has
injective dimension `< n`. -/
theorem hasInjectiveDimensionLT_of_forall_hasProjectiveDimensionLT {n : ℕ}
    (hn : ∀ X : C, HasProjectiveDimensionLT X n) (Y : C) : HasInjectiveDimensionLT Y n := by
  let := HasExt.standard C
  exact .mk fun i hi X e ↦ have := hn X; e.eq_zero_of_hasProjectiveDimensionLT n hi

/-- If every object of an abelian category has injective dimension `< n`, then every object has
projective dimension `< n`. -/
theorem hasProjectiveDimensionLT_of_forall_hasInjectiveDimensionLT {n : ℕ}
    (hn : ∀ Y : C, HasInjectiveDimensionLT Y n) (X : C) : HasProjectiveDimensionLT X n := by
  let := HasExt.standard C
  exact .mk fun i hi Y e ↦ have := hn Y; e.eq_zero_of_hasInjectiveDimensionLT n hi

/-- Every object of an abelian category has projective dimension `< n` iff every object has
injective dimension `< n`. -/
theorem forall_hasProjectiveDimensionLT_iff_forall_hasInjectiveDimensionLT (n : ℕ) :
    (∀ X : C, HasProjectiveDimensionLT X n) ↔ ∀ Y : C, HasInjectiveDimensionLT Y n :=
  ⟨hasInjectiveDimensionLT_of_forall_hasProjectiveDimensionLT,
    hasProjectiveDimensionLT_of_forall_hasInjectiveDimensionLT⟩

/-- If every object of an abelian category has projective dimension `≤ n`, then every object has
injective dimension `≤ n`. -/
theorem hasInjectiveDimensionLE_of_forall_hasProjectiveDimensionLE {n : ℕ}
    (hn : ∀ X : C, HasProjectiveDimensionLE X n) (Y : C) : HasInjectiveDimensionLE Y n :=
  hasInjectiveDimensionLT_of_forall_hasProjectiveDimensionLT hn Y

/-- If every object of an abelian category has injective dimension `≤ n`, then every object has
projective dimension `≤ n`. -/
theorem hasProjectiveDimensionLE_of_forall_hasInjectiveDimensionLE {n : ℕ}
    (hn : ∀ Y : C, HasInjectiveDimensionLE Y n) (X : C) : HasProjectiveDimensionLE X n :=
  hasProjectiveDimensionLT_of_forall_hasInjectiveDimensionLT hn X

/-- Every object of an abelian category has projective dimension `≤ n` iff every object has
injective dimension `≤ n`. -/
theorem forall_hasProjectiveDimensionLE_iff_forall_hasInjectiveDimensionLE (n : ℕ) :
    (∀ X : C, HasProjectiveDimensionLE X n) ↔ ∀ Y : C, HasInjectiveDimensionLE Y n :=
  forall_hasProjectiveDimensionLT_iff_forall_hasInjectiveDimensionLT (n + 1)

end CategoryTheory
