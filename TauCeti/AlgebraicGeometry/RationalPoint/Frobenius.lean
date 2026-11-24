/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.SplittingField.Construction
public import TauCeti.AlgebraicGeometry.RationalPoint.FixedField
public import TauCeti.FieldTheory.Finite.SepClosedSubfield
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Point counts over the finite extensions of a finite field

Let `k` be a finite field with `q` elements and `a : X ⟶ Spec k` a `k`-scheme. The zeta function
of `X` is formed from the numbers of points of `X` with values in the extensions of `k` of degree
`r`, for `r = 1, 2, …`. This file fixes these numbers as functions of `r` alone.

The extension of degree `r` of `k` is unique only up to a non-unique isomorphism, so
`AlgebraicGeometry.Scheme.Hom.pointCount a r` uses one model of it in the universe of `k`: the
splitting field of `X ^ (q ^ r) - X` over `k`. It is the number of points of `X` with values in
that field (`AlgebraicGeometry.Scheme.Hom.numberOfRationalPoints`). The definition is stated for
every field `k`, with `q = Nat.card k`, but it has the meaning above only for finite `k`. For
infinite `k` the convention of `Nat.card` gives `q = 0`, so for `r ≠ 0` the polynomial is `1 - X`,
its splitting field is `k`, and the definition gives the number of `k`-valued points at every `r`;
it has no degree-`r` meaning there. The theorems about extensions assume `k` finite.

The model does not matter: for every finite extension `E / k` of degree `d`, `E` has `q ^ d`
elements, hence is a splitting field of `X ^ (q ^ d) - X` over `k`, hence is `k`-isomorphic to
the model, and the point count does not change under such isomorphisms. So the count at `d` is
the number of `E`-valued points
(`AlgebraicGeometry.Scheme.Hom.pointCount_eq_numberOfRationalPoints`).

Applied to the fixed field of the `r`-th power of the arithmetic Frobenius `x ↦ x ^ q` of an
algebraic closure `L` of `k`, which has degree `r` over `k` for `r ≠ 0`, this gives the
description of the count by Frobenius fixed points: the count at `r ≠ 0` is the number of
`L`-valued points of `X` fixed by the `r`-th power of the arithmetic Frobenius
(`Scheme.Hom.pointCount_eq_natCard_fixedPoints_frobeniusAlgEquivOfAlgebraic_pow`),
or equivalently by the `r`-th power of the geometric Frobenius, its inverse. No finiteness
hypothesis is put on `X`: with the convention of `Nat.card`, both sides are `0` when there are
infinitely many points. At `r = 0` the polynomial `X ^ (q ^ 0) - X` is zero, its splitting field
is `k`, and the count is the number of `k`-valued points
(`AlgebraicGeometry.Scheme.Hom.pointCount_zero`); the fixed-point formula fails there, since the
fixed field of the identity is the infinite field `L`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.pointCount a r`: the number of points of `a : X ⟶ Spec k` with
  values in the splitting field of `X ^ (q ^ r) - X` over `k`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.pointCount_eq_numberOfRationalPoints`: over a finite field, the
  count at the degree of a finite extension `E` is the number of `E`-valued points.
* `Scheme.Hom.pointCount_eq_natCard_fixedPoints_frobeniusAlgEquivOfAlgebraic_pow` and
  `Scheme.Hom.pointCount_eq_natCard_fixedPoints_inv_frobeniusAlgEquivOfAlgebraic_pow`: for
  `r ≠ 0` the count at `r` is the number of points with values in a separably closed algebraic
  extension that are fixed by the `r`-th power of the arithmetic, or geometric, Frobenius.
* `AlgebraicGeometry.Scheme.Hom.pointCount_pullback`: the counts are multiplicative in fibre
  products over `k`.

## References

* The Stacks Project, proof of Theorem 64.16.1 (Tag 03UG), step 2, for the points over a finite
  field as fixed points of Frobenius.
* P. Deligne, *Cohomologie étale (SGA 4½)*, Rapport, §1, for the zeta function of a scheme over a
  finite field and its point counts.
-/

public section

open CategoryTheory Limits Polynomial IntermediateField

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- For a finite field `k`, the number of points of a `k`-scheme `a : X ⟶ Spec k` over the
extension of degree `r` of `k`, modelled by the splitting field of `X ^ (q ^ r) - X` over `k`,
where `q = Nat.card k`. This does not depend on the model of the extension
(`AlgebraicGeometry.Scheme.Hom.pointCount_eq_numberOfRationalPoints`). The definition is stated
for every field, but for infinite `k` the convention of `Nat.card` gives `q = 0`, so for `r ≠ 0`
the polynomial is `1 - X` and the value is the number of `k`-valued points at every `r`, with no
degree-`r` meaning. -/
noncomputable def pointCount (a : X ⟶ Spec (.of k)) (r : ℕ) : ℕ :=
  a.numberOfRationalPoints (SplittingField (Polynomial.X ^ Nat.card k ^ r - Polynomial.X : k[X]))

/-- Unfolding lemma for `pointCount`. -/
theorem pointCount_def (a : X ⟶ Spec (.of k)) (r : ℕ) :
    a.pointCount r = a.numberOfRationalPoints
      (SplittingField (Polynomial.X ^ Nat.card k ^ r - Polynomial.X : k[X])) :=
  (rfl)

/-- At `r = 0` the polynomial `X ^ (q ^ 0) - X` is zero, whose splitting field is `k`, so the
count is the number of `k`-valued points. This holds for every field `k`. -/
@[simp]
theorem pointCount_zero (a : X ⟶ Spec (.of k)) :
    a.pointCount 0 = a.numberOfRationalPoints k := by
  have : IsSplittingField k k (Polynomial.X ^ Nat.card k ^ 0 - Polynomial.X : k[X]) := by
    simpa using isSplittingField_C (0 : k)
  rw [pointCount_def, numberOfRationalPoints_congr
    (IsSplittingField.algEquiv k (Polynomial.X ^ Nat.card k ^ 0 - Polynomial.X : k[X])) a]

/-- **The point count does not depend on the model of the extension.** For a finite field `k` and
a finite extension `E / k`, the count at the degree of `E` is the number of `E`-valued points:
`E` is a splitting field of `X ^ (q ^ d) - X` over `k`, where `d` is its degree. -/
theorem pointCount_eq_numberOfRationalPoints [Finite k] (E : Type u) [Field E] [Algebra k E]
    [Module.Finite k E] (a : X ⟶ Spec (.of k)) :
    a.pointCount (Module.finrank k E) = a.numberOfRationalPoints E := by
  have : Finite E := Module.finite_of_finite k
  have : Fintype E := .ofFinite E
  have : IsSplittingField k E
      (Polynomial.X ^ Nat.card k ^ Module.finrank k E - Polynomial.X : k[X]) := by
    rw [← Module.natCard_eq_pow_finrank, ← Fintype.card_eq_nat_card]
    exact FiniteField.isSplittingField_sub E k
  rw [pointCount_def, numberOfRationalPoints_congr (IsSplittingField.algEquiv E
    (Polynomial.X ^ Nat.card k ^ Module.finrank k E - Polynomial.X : k[X])) a]

/-- Over a finite field `k`, the count at `r = 1` is the number of `k`-valued points. -/
@[simp]
theorem pointCount_one [Finite k] (a : X ⟶ Spec (.of k)) :
    a.pointCount 1 = a.numberOfRationalPoints k := by
  simpa using a.pointCount_eq_numberOfRationalPoints k

/-- **Point counts are fixed points of Frobenius.** Let `k` be a finite field with `q` elements
and `L` a separably closed algebraic extension of `k`, for instance an algebraic closure. For
`r ≠ 0`, the count at `r` is the number of `L`-valued points of `X` fixed by the `r`-th power of
the arithmetic Frobenius `x ↦ x ^ q` of `L`, acting on a point `x` by `Spec.map σ ≫ x`. No
finiteness hypothesis is put on `X`. -/
theorem pointCount_eq_natCard_fixedPoints_frobeniusAlgEquivOfAlgebraic_pow [Fintype k]
    (L : Type u) [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] [IsSepClosed L]
    (a : X ⟶ Spec (.of k)) {r : ℕ} (hr : r ≠ 0) :
    a.pointCount r =
      Nat.card {x : Spec (.of L) ⟶ X // x ≫ a = Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧
        Spec.map (CommRingCat.ofHom
          ((FiniteField.frobeniusAlgEquivOfAlgebraic k L ^ r : L ≃ₐ[k] L) : L →+* L)) ≫ x = x} := by
  have h := TauCeti.finrank_fixedField_zpowers_frobeniusAlgEquivOfAlgebraic_pow k L hr
  have : Module.Finite k
      (fixedField (Subgroup.zpowers (FiniteField.frobeniusAlgEquivOfAlgebraic k L ^ r))) :=
    Module.finite_of_finrank_pos (by omega)
  rw [← AlgEquiv.numberOfRationalPoints_fixedField_eq_natCard,
    ← a.pointCount_eq_numberOfRationalPoints (fixedField _), h]

/-- The geometric form of
`AlgebraicGeometry.Scheme.Hom.pointCount_eq_natCard_fixedPoints_frobeniusAlgEquivOfAlgebraic_pow`:
for `r ≠ 0`, the count at `r` is also the number of `L`-valued points fixed by the `r`-th power of
the geometric Frobenius, the inverse of the arithmetic Frobenius. -/
theorem pointCount_eq_natCard_fixedPoints_inv_frobeniusAlgEquivOfAlgebraic_pow [Fintype k]
    (L : Type u) [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] [IsSepClosed L]
    (a : X ⟶ Spec (.of k)) {r : ℕ} (hr : r ≠ 0) :
    a.pointCount r =
      Nat.card {x : Spec (.of L) ⟶ X // x ≫ a = Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧
        Spec.map (CommRingCat.ofHom
          (((FiniteField.frobeniusAlgEquivOfAlgebraic k L ^ r)⁻¹ : L ≃ₐ[k] L) : L →+* L)) ≫ x =
          x} := by
  simp_rw [AlgEquiv.SpecMap_inv_comp_eq_self_iff]
  exact a.pointCount_eq_natCard_fixedPoints_frobeniusAlgEquivOfAlgebraic_pow L hr

/-- The spectrum of `k` has exactly one point over each extension of `k`. -/
@[simp]
theorem pointCount_id (r : ℕ) : pointCount (𝟙 (Spec (.of k))) r = 1 :=
  numberOfRationalPoints_id

/-- **Point counts are multiplicative in fibre products.** The count of `X ×_k Y` at `r` is the
product of the counts of `X` and of `Y` at `r`. -/
theorem pointCount_pullback {Y : Scheme.{u}} (a : X ⟶ Spec (.of k)) (b : Y ⟶ Spec (.of k))
    (r : ℕ) : (pullback.fst a b ≫ a).pointCount r = a.pointCount r * b.pointCount r :=
  numberOfRationalPoints_pullback a b

end AlgebraicGeometry.Scheme.Hom
