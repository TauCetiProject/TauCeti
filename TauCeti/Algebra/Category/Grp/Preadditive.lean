/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive

/-!
# Multiples of the identity of an abelian group

A natural number `e` kills an abelian group `M` exactly when the endomorphism `e • 𝟙 M` vanishes
(`AddCommGrpCat.nsmul_id_eq_zero_iff`). This is the analogue for `AddCommGrpCat` of
`ModuleCat.nsmul_id_eq_zero_iff`.
-/

public section

open CategoryTheory

namespace AddCommGrpCat

/-- A natural number `e` kills an abelian group `M`, in the sense that `e • 𝟙 M = 0`, exactly
when `e • x = 0` for every element `x` of `M`. -/
theorem nsmul_id_eq_zero_iff {M : AddCommGrpCat} {e : ℕ} : e • 𝟙 M = 0 ↔ ∀ x : M, e • x = 0 :=
  ⟨fun h x ↦ by simpa using ConcreteCategory.congr_hom h x, fun h ↦ by ext x; simpa using h x⟩

end AddCommGrpCat
