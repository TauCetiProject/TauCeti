/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.FoelnerFilter

/-!
# Følner families under `Multiplicative` and `Additive`

Mathlib's `IsFoelner` and `IsAddFoelner` define Følner families for multiplicative and additive
group actions on a measure space. Because the action of `Multiplicative A` on `X` is the additive
action of `A` on `X` (and dually for `Additive G`), being a Følner family is preserved across the
`Multiplicative` and `Additive` type tags.

## Main results

* `TauCeti.isFoelner_multiplicative_iff`: a family of sets is Følner for `Multiplicative A` acting
  on `X` if and only if it is additively Følner for `A` acting on `X`.
* `TauCeti.isAddFoelner_additive_iff`: a family of sets is additively Følner for `Additive G`
  acting on `X` if and only if it is Følner for `G` acting on `X`.
-/

public section

open Filter MeasureTheory

namespace TauCeti

variable {A G X ι : Type*} [MeasurableSpace X] {μ : Measure X} {l : Filter ι} {F : ι → Set X}

/-- A family of sets is Følner for `Multiplicative A` acting on `X` if and only if it is additively
Følner for `A` acting on `X`. -/
@[simp]
theorem isFoelner_multiplicative_iff [AddGroup A] [AddAction A X] :
    IsFoelner (Multiplicative A) μ l F ↔ IsAddFoelner A μ l F := by
  simp only [isFoelner_iff, isAddFoelner_iff, Multiplicative.forall, ← Set.image_smul, ofAdd_smul,
    Set.image_vadd]

/-- A family of sets is additively Følner for `Additive G` acting on `X` if and only if it is
Følner for `G` acting on `X`. -/
@[simp]
theorem isAddFoelner_additive_iff [Group G] [MulAction G X] :
    IsAddFoelner (Additive G) μ l F ↔ IsFoelner G μ l F := by
  simp only [isAddFoelner_iff, isFoelner_iff, Additive.forall, ← Set.image_vadd, ofMul_vadd,
    Set.image_smul]

end TauCeti
