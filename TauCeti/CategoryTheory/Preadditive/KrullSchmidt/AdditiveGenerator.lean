/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.AdditiveGenerator
public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Basic
import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Uniqueness

/-!
# Additive generators of Krull-Schmidt categories

An object with a local endomorphism ring lies in the additive closure `add G` exactly when it is a
direct summand of `G` (`TauCeti.additiveClosure_iff_nonempty_retract`), since the identity is a
finite sum of composites through the copies of `G` and one of them is invertible; and it lies in
`add (⨁ P)`, for a finite biproduct `⨁ P` of objects with local endomorphism rings, exactly when it
is isomorphic to some `P j`
(`TauCeti.additiveClosure_biproduct_iff_exists_iso`). Hence, in a Krull-Schmidt category, `G` is
an additive generator exactly when every indecomposable object is a direct summand of `G`. A
biproduct of objects representing every indecomposable object is then an additive generator, and a
Krull-Schmidt category has an additive generator exactly when it has finitely many indecomposable
objects up to isomorphism.

Outside Krull-Schmidt categories neither condition implies the other. In a nonzero category with
no indecomposable objects, `0` has every indecomposable object as a direct summand but is not an
additive generator. Among the finitely generated projective modules over `ℤ[√-5]`, the ring is an
additive generator, but a non-principal ideal is indecomposable and not a direct summand of it.

## Main results

* `TauCeti.additiveClosure_iff_nonempty_retract`: an object with a local endomorphism ring lies in
  `add G` exactly when it is a direct summand of `G`.
* `TauCeti.additiveClosure_biproduct_iff_exists_iso`: for a finite family `P` of objects with
  local endomorphism rings, the objects of `add (⨁ P)` with local endomorphism rings are the `P j`,
  up to isomorphism.
* `TauCeti.isAdditiveGenerator_iff_forall_indecomposable`: in a Krull-Schmidt category, `G` is an
  additive generator exactly when every indecomposable object is a direct summand of `G`.
* `TauCeti.isAdditiveGenerator_biproduct`: in a Krull-Schmidt category, a biproduct of objects
  representing every indecomposable object is an additive generator.
* `TauCeti.exists_isAdditiveGenerator_iff`: a Krull-Schmidt category has an additive generator
  exactly when finitely many objects represent every indecomposable object up to isomorphism.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995).
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

/-- In a Krull-Schmidt category, every indecomposable object is a retract of an additive
generator. -/
theorem IsAdditiveGenerator.nonempty_retract [IsKrullSchmidt C] {G : C}
    (hG : IsAdditiveGenerator G) {X : C} (hX : Indecomposable X) : Nonempty (Retract X G) :=
  have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end X).1 hX
  additiveClosure_iff_nonempty_retract.1 (hG.additiveClosure X)

/-- **Additive generators of a Krull-Schmidt category**: `G` is an additive generator exactly when
every indecomposable object is a direct summand of `G`. -/
theorem isAdditiveGenerator_iff_forall_indecomposable [IsKrullSchmidt C] {G : C} :
    IsAdditiveGenerator G ↔ ∀ X : C, Indecomposable X → Nonempty (Retract X G) := by
  refine ⟨fun hG X hX ↦ hG.nonempty_retract hX, fun hG ↦ isAdditiveGenerator_def.2 fun X ↦ ?_⟩
  obtain ⟨m, P, hP, ⟨φ⟩⟩ := IsKrullSchmidt.exists_iso_biproduct X
  refine (additiveClosure G).prop_of_iso φ.symm
    ((additiveClosure G).prop_of_isLimit (biproduct.isLimit _) fun ⟨i⟩ ↦ ?_)
  obtain ⟨h⟩ := hG (P i) indecomposable_of_isLocalRing_end
  exact (additiveClosure G).prop_of_retract h (additiveClosure_self G)

/-- **Representatives of the indecomposable objects give an additive generator**: in a
Krull-Schmidt category, if every indecomposable object is isomorphic to one of the objects `P i`,
their biproduct is an additive generator. -/
theorem isAdditiveGenerator_biproduct [IsKrullSchmidt C] {ι : Type w} (P : ι → C)
    [HasBiproduct P] (hP : ∀ X : C, Indecomposable X → ∃ i, Nonempty (X ≅ P i)) :
    IsAdditiveGenerator (⨁ P) :=
  isAdditiveGenerator_iff_forall_indecomposable.2 fun X hX ↦ by
    obtain ⟨i, ⟨e⟩⟩ := hP X hX
    exact ⟨(Retract.ofIso e).trans ⟨biproduct.ι P i, biproduct.π P i, by simp⟩⟩

/-- **A Krull-Schmidt category has an additive generator exactly when it has finitely many
indecomposable objects up to isomorphism.** -/
theorem exists_isAdditiveGenerator_iff [IsKrullSchmidt C] :
    (∃ G : C, IsAdditiveGenerator G) ↔
      ∃ (n : ℕ) (P : Fin n → C), ∀ X : C, Indecomposable X → ∃ i, Nonempty (X ≅ P i) := by
  refine ⟨fun ⟨G, hG⟩ ↦ ?_, fun ⟨n, P, hP⟩ ↦ ⟨⨁ P, isAdditiveGenerator_biproduct P hP⟩⟩
  obtain ⟨n, P, hP, ⟨φ⟩⟩ := IsKrullSchmidt.exists_iso_biproduct G
  refine ⟨n, P, fun X hX ↦ ?_⟩
  have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end X).1 hX
  exact (additiveClosure_biproduct_iff_exists_iso P hP).1 ((hG.of_iso φ).additiveClosure X)

end TauCeti
