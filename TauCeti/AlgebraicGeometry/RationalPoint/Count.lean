/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
import TauCeti.CategoryTheory.Limits.Shapes.Pullback.OverClass

/-!
# The number of points of a scheme with values in a field

For a ring `k` and a field `L` over `k`, `a.numberOfRationalPoints L` is the number of `L`-valued
points of a `k`-scheme `a : X ⟶ Spec k`, that is, of morphisms `Spec L ⟶ X` over `Spec k`, with
the convention of `Nat.card` that an infinite set of points has count `0`. It is multiplicative in
fibre products over `k` (`AlgebraicGeometry.Scheme.Hom.numberOfRationalPoints_pullback`), by the
universal property of the fibre product `CategoryTheory.IsPullback.homIsOverEquiv`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.numberOfRationalPoints`: the number of `L`-valued points of a
  `k`-scheme.

## Main results

* `AlgebraicGeometry.Scheme.Hom.numberOfRationalPoints_pullback`: point counts are multiplicative
  in fibre products.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [CommRing k] (L : Type u) [Field L] [Algebra k L]

/-- The number of `L`-valued points of a scheme `a : X ⟶ Spec k` over `Spec k`. With the
convention of `Nat.card`, it is `0` when there are infinitely many such points. -/
noncomputable def numberOfRationalPoints {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) : ℕ :=
  Nat.card {x : Spec (.of L) ⟶ X // x ≫ a = Spec.map (CommRingCat.ofHom (algebraMap k L))}

variable {L}

/-- Unfolding lemma for `numberOfRationalPoints`. -/
theorem numberOfRationalPoints_def {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) :
    a.numberOfRationalPoints L =
      Nat.card {x : Spec (.of L) ⟶ X // x ≫ a = Spec.map (CommRingCat.ofHom (algebraMap k L))} :=
  (rfl)

/-- **Point counts are multiplicative in fibre products.** The number of `L`-valued points of
`X ×_k Y` is the product of the numbers of `L`-valued points of `X` and of `Y`; with the
convention of `Nat.card`, both sides are `0` as soon as one factor has infinitely many points and
the other has at least one. -/
theorem numberOfRationalPoints_pullback {X Y : Scheme.{u}} (a : X ⟶ Spec (.of k))
    (b : Y ⟶ Spec (.of k)) :
    (pullback.fst a b ≫ a).numberOfRationalPoints L =
      a.numberOfRationalPoints L * b.numberOfRationalPoints L := by
  -- View `X`, `Y`, `X ×_k Y` and `Spec L` as objects over `Spec k`, to use the universal
  -- property of the fibre product in the `OverClass` vocabulary.
  let _ : OverClass X (Spec (.of k)) := ⟨a⟩
  let _ : OverClass Y (Spec (.of k)) := ⟨b⟩
  let _ : OverClass (pullback a b) (Spec (.of k)) := ⟨pullback.fst a b ≫ a⟩
  let _ : OverClass (Spec (.of L)) (Spec (.of k)) :=
    ⟨Spec.map (CommRingCat.ofHom (algebraMap k L))⟩
  have : HomIsOver (pullback.fst a b) (Spec (.of k)) := ⟨rfl⟩
  rw [numberOfRationalPoints_def, numberOfRationalPoints_def, numberOfRationalPoints_def,
    ← Nat.card_prod]
  exact Nat.card_congr <| (Equiv.subtypeEquivRight fun _ ↦ ⟨fun h ↦ ⟨h⟩, fun h ↦ h.1⟩).trans <|
    (IsPullback.homIsOverEquiv _ (IsPullback.of_hasPullback a b)).trans <|
    Equiv.prodCongr (Equiv.subtypeEquivRight fun _ ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩)
      (Equiv.subtypeEquivRight fun _ ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩)

end AlgebraicGeometry.Scheme.Hom
