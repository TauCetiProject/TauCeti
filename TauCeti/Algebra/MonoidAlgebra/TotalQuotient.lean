/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Localization
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.Jacobson.Semiprimary

/-!
# Total quotient rings of finite monoid algebras

For a finite commutative monoid `M` and a coefficient ring `R` with fraction field `K`,
`K[M]` is the total quotient ring of `R[M]`. In particular, rationalizing the coefficients
computes the total quotient ring of an integral finite abelian group ring. The group ring
need not be a domain: all its nonzerodivisors become units after rationalization.

For a finite abelian group whose order is nonzero in the coefficient fraction field, the
total quotient ring is a finite product of finite-dimensional field extensions of that field.
The components are the quotients by the maximal ideals of the coefficient-field group algebra.
The decomposition respects coefficient scalars. In characteristic zero, all component fields
have characteristic zero.

The algebra structure on coefficient extension is Mathlib's scoped `AlgebraMonoidAlgebra`
structure. No field structure on the group ring is assumed.

## References

* V. Turaev, *Introduction to Combinatorial Torsions*, Chapter I, for total quotient
  coefficients of abelian group rings.
-/

public section

namespace TauCeti

open scoped AlgebraMonoidAlgebra

-- Mathlib declares the multiplicative and additive finiteness instances separately.
attribute [to_additive existing] _root_.MonoidAlgebra.moduleFinite

/-- A monoid algebra over an Artinian coefficient ring is Artinian when the monoid is finite. -/
@[to_additive (dont_translate := R) AddMonoidAlgebra.isArtinianRing_of_finite
/-- An additive monoid algebra over an Artinian coefficient ring is Artinian when the
additive monoid is finite. -/]
instance MonoidAlgebra.isArtinianRing_of_finite (R M : Type*) [Ring R]
    [IsArtinianRing R] [Monoid M] [Finite M] : IsArtinianRing (MonoidAlgebra R M) :=
  isArtinian_of_tower R inferInstance

/-- For a finite commutative monoid, extension to a fraction field of the coefficients is
already the total quotient ring of the monoid algebra. -/
@[to_additive (dont_translate := R K) AddMonoidAlgebra.isFractionRing_of_finite
/-- For a finite commutative additive monoid, extension to a fraction field of the coefficients
is already the total quotient ring of the additive monoid algebra. -/]
theorem MonoidAlgebra.isFractionRing_of_finite (R K M : Type*) [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] [CommMonoid M] [Finite M] :
    IsFractionRing (MonoidAlgebra R M) (MonoidAlgebra K M) := by
  let U := Algebra.algebraMapSubmonoid (MonoidAlgebra R M) (nonZeroDivisors R)
  have : IsLocalization U (MonoidAlgebra K M) :=
    MonoidAlgebra.isLocalization_coefficients R (nonZeroDivisors R)
  have hinj : Function.Injective
      (algebraMap (MonoidAlgebra R M) (MonoidAlgebra K M)) :=
    _root_.MonoidAlgebra.map_injective (algebraMap R K).toAddMonoidHom
      (IsFractionRing.injective R K)
  have hU : U ≤ nonZeroDivisors (MonoidAlgebra R M) := by
    intro x hx
    exact isRegular_iff_mem_nonZeroDivisors.mp
      ((IsLocalization.injective_iff_isRegular U).mp hinj ⟨x, hx⟩)
  refine IsLocalization.of_le U (nonZeroDivisors (MonoidAlgebra R M)) hU ?_
  intro x hx
  exact IsArtinianRing.isUnit_of_mem_nonZeroDivisors
    (a := algebraMap (MonoidAlgebra R M) (MonoidAlgebra K M) x)
    (IsLocalization.nonZeroDivisors_le_comap U (MonoidAlgebra K M) hx)

/-- The canonical identification of a total quotient ring of a finite additive monoid algebra
with its coefficient fraction-field extension. It preserves the original monoid-algebra
scalars. -/
noncomputable def AddMonoidAlgebra.totalQuotientAlgEquiv
    (R K H Q : Type*) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommMonoid H] [Finite H] [CommRing Q] [Algebra (AddMonoidAlgebra R H) Q]
    [IsFractionRing (AddMonoidAlgebra R H) Q] :
    Q ≃ₐ[AddMonoidAlgebra R H] AddMonoidAlgebra K H := by
  have := AddMonoidAlgebra.isFractionRing_of_finite R K H
  exact IsLocalization.algEquiv (nonZeroDivisors (AddMonoidAlgebra R H)) Q _

/-- The canonical total-quotient identification sends a fraction to the same fraction
in the coefficient extension. -/
@[simp]
theorem addMonoidAlgebra_totalQuotientAlgEquiv_mk'
    (R K H Q : Type*) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommMonoid H] [Finite H] [CommRing Q] [Algebra (AddMonoidAlgebra R H) Q]
    [IsFractionRing (AddMonoidAlgebra R H) Q]
    (x : AddMonoidAlgebra R H) (s : nonZeroDivisors (AddMonoidAlgebra R H)) :
    letI := AddMonoidAlgebra.isFractionRing_of_finite R K H
    AddMonoidAlgebra.totalQuotientAlgEquiv R K H Q (IsLocalization.mk' Q x s) =
      IsLocalization.mk' (AddMonoidAlgebra K H) x s := by
  have := AddMonoidAlgebra.isFractionRing_of_finite R K H
  exact IsLocalization.algEquiv_mk' _ _

/-- Maximal-ideal field components of an additive monoid algebra over a characteristic-zero
field have characteristic zero. -/
instance AddMonoidAlgebra.charZeroQuotientMaximalSpectrum
    (K H : Type*) [Field K] [CharZero K] [AddCommMonoid H]
    (I : MaximalSpectrum (AddMonoidAlgebra K H)) :
    CharZero (AddMonoidAlgebra K H ⧸ I.asIdeal) :=
  charZero_of_injective_algebraMap (algebraMap K _).injective

/-- A finite abelian group algebra whose group order is nonzero in the coefficient field is
the product of its maximal-ideal field components, as an algebra over the coefficient field.
The index set is finite, and each component is finite-dimensional over that field. -/
noncomputable def AddMonoidAlgebra.algEquivPiField
    (K H : Type*) [Field K] [AddCommGroup H] [Finite H] [NeZero (Nat.card H : K)] :
    AddMonoidAlgebra K H ≃ₐ[K]
      ∀ I : MaximalSpectrum (AddMonoidAlgebra K H), AddMonoidAlgebra K H ⧸ I.asIdeal :=
  (IsArtinianRing.equivPi (AddMonoidAlgebra K H)).restrictScalars K

/-- Evaluation of the field decomposition is the quotient map at the chosen maximal ideal. -/
@[simp]
theorem addMonoidAlgebra_algEquivPiField_apply
    (K H : Type*) [Field K] [AddCommGroup H] [Finite H] [NeZero (Nat.card H : K)]
    (x : AddMonoidAlgebra K H) (I : MaximalSpectrum (AddMonoidAlgebra K H)) :
    AddMonoidAlgebra.algEquivPiField K H x I = Ideal.Quotient.mk I.asIdeal x :=
  IsArtinianRing.equivPi_apply _ x I

end TauCeti
