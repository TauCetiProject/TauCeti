/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import TauCeti.RingTheory.MvPolynomial.Expand
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# The power map of affine space

For a commutative ring `R`, a set of variables `σ` and `n > 0`, the power map `x_i ↦ x_i ^ n` of
the affine space `Spec R[x_i]` is `Spec` of `MvPolynomial.expand n`. It is dominant, since
`expand n` is injective, and flat. For finitely many variables it is finite, and its rank is
`n ^ |σ|` at every point, `R[x_i]` being free of rank `n ^ |σ|` over `R[x_i ^ n]`
(`TauCeti.MvPolynomial.finrank_expand`).

## Main results

* `AlgebraicGeometry.isDominant_SpecMap_expand`, `AlgebraicGeometry.flat_SpecMap_expand` and
  `AlgebraicGeometry.isFinite_SpecMap_expand`: the power map is dominant and flat, and finite for
  finitely many variables.
* `AlgebraicGeometry.finrank_SpecMap_expand`: its rank is `n ^ |σ|` at every point.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

variable (σ R : Type*) [CommRing R] (n : ℕ) [NeZero n]

/-- The power map `x_i ↦ x_i ^ n` of affine space is dominant, `MvPolynomial.expand n` being
injective. -/
instance isDominant_SpecMap_expand :
    IsDominant (Spec.map (CommRingCat.ofHom
      (MvPolynomial.expand n : MvPolynomial σ R →ₐ[R] _).toRingHom)) :=
  ⟨RingHom.denseRange_comap_of_injective _
    (MvPolynomial.expand_injective (Nat.pos_of_neZero n))⟩

/-- The power map `x_i ↦ x_i ^ n` of affine space is flat. -/
instance flat_SpecMap_expand :
    Flat (Spec.map (CommRingCat.ofHom
      (MvPolynomial.expand n : MvPolynomial σ R →ₐ[R] _).toRingHom)) :=
  Flat.SpecMap_iff.2 (TauCeti.MvPolynomial.flat_expand (Nat.pos_of_neZero n))

variable [Finite σ]

/-- The power map `x_i ↦ x_i ^ n` of affine space in finitely many variables is finite. -/
instance isFinite_SpecMap_expand :
    IsFinite (Spec.map (CommRingCat.ofHom
      (MvPolynomial.expand n : MvPolynomial σ R →ₐ[R] _).toRingHom)) :=
  (IsFinite.SpecMap_iff _).2 (TauCeti.MvPolynomial.finite_expand (Nat.pos_of_neZero n))

/-- The power map `x_i ↦ x_i ^ n` of affine space in finitely many variables has rank `n ^ |σ|`
at every point. -/
theorem finrank_SpecMap_expand :
    (Spec.map (CommRingCat.ofHom
      (MvPolynomial.expand n : MvPolynomial σ R →ₐ[R] _).toRingHom)).finrank =
      fun _ ↦ n ^ Nat.card σ := by
  have hn := Nat.pos_of_neZero n
  exact (Scheme.Hom.finrank_SpecMap_eq_finrank (TauCeti.MvPolynomial.finite_expand hn)
    (TauCeti.MvPolynomial.flat_expand hn)).trans (TauCeti.MvPolynomial.finrank_expand hn)

end AlgebraicGeometry
