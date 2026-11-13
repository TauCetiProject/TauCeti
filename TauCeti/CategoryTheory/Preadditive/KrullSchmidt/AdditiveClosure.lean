/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.AdditiveGenerator

/-!
# Additive closures in a Krull-Schmidt category

In a Krull-Schmidt category, an object `X` lies in the additive closure `add M` exactly when every
indecomposable direct summand of `X` is a direct summand of `M`
(`TauCeti.additiveClosure_iff_forall_indecomposable`). One direction is
`TauCeti.additiveClosure_iff_nonempty_retract` for objects with local endomorphism rings; for the
other, `X` is a finite biproduct of indecomposable objects, each a direct summand of `X`.

## Main results

* `TauCeti.additiveClosure_iff_forall_indecomposable`: in a Krull-Schmidt category, `X ∈ add M`
  exactly when every indecomposable direct summand of `X` is a direct summand of `M`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- **Additive closures through indecomposable summands**: in a Krull-Schmidt category, `X` lies in
`add M` exactly when every indecomposable direct summand of `X` is a direct summand of `M`. -/
theorem additiveClosure_iff_forall_indecomposable [IsKrullSchmidt C] {M X : C} :
    additiveClosure M X ↔
      ∀ Y : C, Indecomposable Y → Nonempty (Retract Y X) → Nonempty (Retract Y M) := by
  refine ⟨fun hX Y hY ⟨r⟩ ↦ ?_, fun h ↦ ?_⟩
  · have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end Y).1 hY
    exact additiveClosure_iff_nonempty_retract.1 ((additiveClosure M).prop_of_retract r hX)
  · obtain ⟨n, P, hP, ⟨e⟩⟩ := IsKrullSchmidt.exists_iso_biproduct X
    refine (additiveClosure M).prop_of_retract e.retract
      ((additiveClosure M).prop_of_isLimit (biproduct.isLimit P) fun ⟨i⟩ ↦ ?_)
    have := hP i
    obtain ⟨r⟩ := h (P i) indecomposable_of_isLocalRing_end
      ⟨{ i := biproduct.ι P i ≫ e.inv, r := e.hom ≫ biproduct.π P i }⟩
    exact (additiveClosure M).prop_of_retract r (additiveClosure_self M)

end TauCeti
