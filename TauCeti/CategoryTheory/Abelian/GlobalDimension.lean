/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Abelian.Injective.Dimension

import TauCeti.Algebra.Homology.Ext.Equivalence

/-!
# Global dimension of an abelian category

The global dimension is the supremum of the projective dimensions of the objects. It is also
the supremum of their injective dimensions, since both use the same vanishing bounds on all
pairs of objects. The value is `⊥` exactly when every object is zero. Equivalences and
opposition preserve the global dimension.

## References

* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161, §9, p. 42.
-/

public section

open CategoryTheory Limits Opposite

namespace CategoryTheory.Abelian

variable (C : Type*) [Category* C] [Abelian C]

/-- The global dimension of an abelian category is the supremum of the projective dimensions
of its objects. -/
noncomputable def globalDimension : WithBot ℕ∞ :=
  ⨆ X : C, projectiveDimension X

/-- The supremum formula for global dimension. -/
theorem globalDimension_def : globalDimension C = ⨆ X : C, projectiveDimension X := (rfl)

/-- The global dimension is at most `d` iff every object has projective dimension at most `d`. -/
theorem globalDimension_le_iff (d : WithBot ℕ∞) :
    globalDimension C ≤ d ↔ ∀ X : C, projectiveDimension X ≤ d :=
  iSup_le_iff

variable {C} in
/-- The projective dimension of each object is bounded by the global dimension. -/
theorem projectiveDimension_le_globalDimension (X : C) :
    projectiveDimension X ≤ globalDimension C :=
  le_iSup (fun X : C ↦ projectiveDimension X) X

/-- The global dimension is at most `n` iff all objects have projective dimension at most `n`. -/
theorem globalDimension_le_iff_hasProjectiveDimensionLE (n : ℕ) :
    globalDimension C ≤ n ↔ ∀ X : C, HasProjectiveDimensionLE X n := by
  simp only [globalDimension_le_iff, projectiveDimension_le_iff]

/-- The global dimension is at most `n` iff all objects have injective dimension at most `n`. -/
theorem globalDimension_le_iff_hasInjectiveDimensionLE (n : ℕ) :
    globalDimension C ≤ n ↔ ∀ X : C, HasInjectiveDimensionLE X n :=
  (globalDimension_le_iff_hasProjectiveDimensionLE C n).trans
    (TauCeti.forall_hasProjectiveDimensionLE_iff_forall_hasInjectiveDimensionLE n)

/-- The global dimension is `⊥` exactly when every object is zero. -/
theorem globalDimension_eq_bot_iff :
    globalDimension C = ⊥ ↔ ∀ X : C, IsZero X := by
  simp only [globalDimension, iSup_eq_bot, projectiveDimension_eq_bot_iff]

/-- Global dimension may equivalently be computed as the supremum of injective dimensions. -/
theorem globalDimension_eq_iSup_injectiveDimension :
    globalDimension C = ⨆ X : C, injectiveDimension X := by
  suffices h : ∀ d : WithBot ℕ∞,
      globalDimension C ≤ d ↔ (⨆ X : C, injectiveDimension X) ≤ d from
    (h _).mpr le_rfl |>.antisymm ((h _).mp le_rfl)
  intro d
  induction d using WithBot.recBotCoe with
  | bot =>
    simp only [le_bot_iff, globalDimension_eq_bot_iff, iSup_eq_bot, injectiveDimension_eq_bot_iff]
  | coe d =>
    induction d with
    | top => simp
    | coe n =>
      exact (globalDimension_le_iff_hasInjectiveDimensionLE C n).trans
        (iSup_le_iff.trans (forall_congr' fun X ↦ injectiveDimension_le_iff X n)).symm

/-- An abelian category and its opposite have the same global dimension. -/
@[simp]
theorem globalDimension_op : globalDimension Cᵒᵖ = globalDimension C := by
  rw [globalDimension_eq_iSup_injectiveDimension C, globalDimension_def]
  calc
    (⨆ X : Cᵒᵖ, projectiveDimension X) = ⨆ X : C, projectiveDimension (op X) :=
      (op_surjective.iSup_comp _).symm
    _ = ⨆ X : C, injectiveDimension X := iSup_congr projectiveDimension_op

end CategoryTheory.Abelian

namespace CategoryTheory.Equivalence

/-- An equivalence of abelian categories preserves global dimension. -/
theorem globalDimension_eq {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (e : C ≌ D) : Abelian.globalDimension C = Abelian.globalDimension D := by
  refine le_antisymm ((Abelian.globalDimension_le_iff C _).2 fun X ↦ ?_)
    ((Abelian.globalDimension_le_iff D _).2 fun Y ↦ ?_)
  · simpa only [e.projectiveDimension_functor_obj] using
      Abelian.projectiveDimension_le_globalDimension (e.functor.obj X)
  · have h := e.symm.projectiveDimension_functor_obj Y
    exact h ▸ Abelian.projectiveDimension_le_globalDimension (e.inverse.obj Y)

end CategoryTheory.Equivalence
