/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import TauCeti.AlgebraicGeometry.RationalPoint.FixedField
public import TauCeti.FieldTheory.Finite.SepClosedSubfield

/-!
# The points of affine space

For a commutative ring `k` and a field `L` over `k`, the `L`-valued points of the affine space
`𝔸(n; Spec k)` over `Spec k` are the `n`-tuples of elements of `L`
(`AlgebraicGeometry.AffineSpace.homOverEquiv`). So for a finite index type `n` the affine
`n`-space has `|L| ^ |n|` points with values in `L`
(`AlgebraicGeometry.AffineSpace.numberOfRationalPoints_eq`), with the convention of `Nat.card`
that an infinite field `L` gives `0` unless `n` is empty.

Over a finite field `k` with `q` elements, let `L` be an algebraic closure of `k`, or more
generally a separably closed algebraic extension. Points with values in the degree-`r` extension
of `k` are the `L`-valued points fixed by the `r`-th power of the arithmetic Frobenius
(`AlgEquiv.numberOfRationalPoints_fixedField_eq_natCard`), and that extension has `q ^ r`
elements. Hence the `r`-th power of Frobenius has `(q ^ r) ^ |n|` fixed points on the
`L`-valued points of affine `n`-space
(`AlgebraicGeometry.AffineSpace.natCard_fixedPoints_frobeniusAlgEquivOfAlgebraic_pow`). For the
affine line this is the count `q ^ r`, the basic instance of counting points over finite fields
by fixed points of Frobenius.

## Main results

* `AlgebraicGeometry.AffineSpace.numberOfRationalPoints_eq`: for finite `n`, `𝔸(n; Spec k)` has
  `|L| ^ |n|` points with values in a field `L` over `k`.
* `AlgebraicGeometry.AffineSpace.natCard_fixedPoints_frobeniusAlgEquivOfAlgebraic_pow`: the
  `r`-th power of Frobenius has `(q ^ r) ^ |n|` fixed points on affine `n`-space.

## References

* P. Deligne, *Cohomologie étale (SGA 4½)*, Rapport, §1, for rational points over finite fields
  as fixed points of Frobenius.
-/

public section

open CategoryTheory IntermediateField

universe u

namespace AlgebraicGeometry.AffineSpace

/-- **The points of affine space.** For a field `L` over a commutative ring `k` and a finite index
type `n`, the affine space `𝔸(n; Spec k)` has `|L| ^ |n|` points with values in `L` over
`Spec k`. -/
@[simp]
theorem numberOfRationalPoints_eq {k : Type u} [CommRing k] (L : Type u) [Field L] [Algebra k L]
    (n : Type u) [Finite n] :
    (𝔸(n; Spec (.of k)) ↘ Spec (.of k)).numberOfRationalPoints L = Nat.card L ^ Nat.card n := by
  let _ : (Spec (.of L)).Over (Spec (.of k)) := ⟨Spec.map (CommRingCat.ofHom (algebraMap k L))⟩
  rw [Scheme.Hom.numberOfRationalPoints_def, ← Nat.card_fun]
  -- a point over `Spec k` is a morphism over `Spec k`, that is an `n`-tuple of global sections
  exact Nat.card_congr <| (Equiv.subtypeEquivRight fun _ ↦ (Scheme.Hom.isOver_iff _).symm).trans <|
    (homOverEquiv (Spec (.of k))).trans <|
      Equiv.arrowCongr (.refl n) (Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv.toEquiv

/-- **Frobenius fixed points on affine space.** Let `k` be a finite field with `q` elements and
`L` a separably closed algebraic extension of `k`, for instance an algebraic closure. For
`r ≠ 0`, the `r`-th power of the arithmetic Frobenius `x ↦ x ^ q` of `L` fixes exactly
`(q ^ r) ^ |n|` of the `L`-valued points of the affine space `𝔸(n; Spec k)`. -/
@[simp]
theorem natCard_fixedPoints_frobeniusAlgEquivOfAlgebraic_pow (k L : Type u) [Field k] [Fintype k]
    [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] [IsSepClosed L] (n : Type u) [Finite n]
    {r : ℕ} (hr : r ≠ 0) :
    Nat.card {x : Spec (.of L) ⟶ 𝔸(n; Spec (.of k)) //
        x ≫ (𝔸(n; Spec (.of k)) ↘ Spec (.of k)) =
          Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧
        Spec.map (CommRingCat.ofHom
          ((FiniteField.frobeniusAlgEquivOfAlgebraic k L ^ r : L ≃ₐ[k] L) : L →+* L)) ≫ x = x} =
      (Fintype.card k ^ r) ^ Nat.card n := by
  rw [← AlgEquiv.numberOfRationalPoints_fixedField_eq_natCard, numberOfRationalPoints_eq,
    TauCeti.natCard_fixedField_zpowers_frobeniusAlgEquivOfAlgebraic_pow k L hr]

end AlgebraicGeometry.AffineSpace
