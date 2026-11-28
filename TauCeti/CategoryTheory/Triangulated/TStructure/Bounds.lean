/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Bounds on the first vertex of a distinguished triangle

In a t-structure, a lower or upper bound passes to the first vertex if the second
vertex satisfies that bound and the third vertex satisfies the bound shifted by one.
-/

public section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.Triangulated.TStructure

variable {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] (t : TStructure D)

/-- The first vertex has lower bound `n` if the second has bound `n`
and the third has bound `n - 1`. -/
lemma isGE₁ (T : Triangle D) (hT : T ∈ distTriang D) (n : ℤ)
    (h₂ : t.IsGE T.obj₂ n) (h₃ : t.IsGE T.obj₃ (n - 1)) : t.IsGE T.obj₁ n :=
  t.isGE₂ T.invRotate (inv_rot_of_distTriang T hT) n
    (t.isGE_shift T.obj₃ (n - 1) (-1) n (by omega)) h₂

/-- The first vertex has upper bound `n` if the second has bound `n`
and the third has bound `n - 1`. -/
lemma isLE₁ (T : Triangle D) (hT : T ∈ distTriang D) (n : ℤ)
    (h₂ : t.IsLE T.obj₂ n) (h₃ : t.IsLE T.obj₃ (n - 1)) : t.IsLE T.obj₁ n :=
  t.isLE₂ T.invRotate (inv_rot_of_distTriang T hT) n
    (t.isLE_shift T.obj₃ (n - 1) (-1) n (by omega)) h₂

end CategoryTheory.Triangulated.TStructure
