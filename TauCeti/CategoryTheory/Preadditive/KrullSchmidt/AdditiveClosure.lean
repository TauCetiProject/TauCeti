/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.AdditiveClosure.Basic
public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Basic
import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Uniqueness

/-!
# Additive closures in a Krull-Schmidt category

An object with a local endomorphism ring lies in the additive closure `add G` exactly when it is a
direct summand of `G` (`TauCeti.additiveClosure_iff_nonempty_retract`), since the identity is a
finite sum of composites through the copies of `G` and one of them is invertible; and it lies in
`add (⨁ P)`, for a finite biproduct `⨁ P` of objects with local endomorphism rings, exactly when it
is isomorphic to some `P j` (`TauCeti.additiveClosure_biproduct_iff_exists_iso`).

Hence, in a Krull-Schmidt category, an object `X` lies in `add M` exactly when every
indecomposable direct summand of `X` is a direct summand of `M`
(`TauCeti.additiveClosure_iff_forall_indecomposable`): `X` is a finite biproduct of indecomposable
objects, each a direct summand of `X`.

## Main results

* `TauCeti.additiveClosure_iff_nonempty_retract`: an object with a local endomorphism ring lies in
  `add G` exactly when it is a direct summand of `G`.
* `TauCeti.additiveClosure_biproduct_iff_exists_iso`: for a finite family `P` of objects with
  local endomorphism rings, the objects of `add (⨁ P)` with local endomorphism rings are the `P j`,
  up to isomorphism.
* `TauCeti.additiveClosure_iff_forall_indecomposable`: in a Krull-Schmidt category, `X ∈ add M`
  exactly when every indecomposable direct summand of `X` is a direct summand of `M`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- An object with a local endomorphism ring lies in the additive closure of `G` exactly when it
is a direct summand of `G`. -/
theorem additiveClosure_iff_nonempty_retract {G X : C} [IsLocalRing (End X)] :
    additiveClosure G X ↔ Nonempty (Retract X G) := by
  refine ⟨fun hX ↦ ?_, fun ⟨h⟩ ↦ (additiveClosure G).prop_of_retract h (additiveClosure_self G)⟩
  obtain ⟨n, ⟨h⟩⟩ := additiveClosure_iff.1 hX
  exact (exists_nonempty_retract_of_retract_biproduct _ h).choose_spec

/-- **The objects of `add (⨁ P)` with local endomorphism rings**: for a finite family `P` of objects
with local endomorphism rings and `X` with a local endomorphism ring, `X` lies in the additive
closure of the finite biproduct `⨁ P` exactly when it is isomorphic to some `P j`. -/
theorem additiveClosure_biproduct_iff_exists_iso {κ : Type w} [Finite κ] (P : κ → C)
    (hP : ∀ j, IsLocalRing (End (P j))) {X : C} [IsLocalRing (End X)] :
    additiveClosure (⨁ P) X ↔ ∃ j, Nonempty (X ≅ P j) := by
  rw [additiveClosure_iff_nonempty_retract]
  refine ⟨fun ⟨h⟩ ↦ ?_, fun ⟨j, ⟨e⟩⟩ ↦
    ⟨(Retract.ofIso e).trans ⟨biproduct.ι P j, biproduct.π P j, by simp⟩⟩⟩
  obtain ⟨j, hj⟩ := exists_isIso_comp_π_of_retract P hP h
  exact ⟨j, ⟨asIso (h.i ≫ biproduct.π P j)⟩⟩

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
