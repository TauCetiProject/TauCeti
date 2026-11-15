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
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.Jacobson.Semiprimary
public import Mathlib.RingTheory.FiniteType
public import TauCeti.Algebra.MonoidAlgebra.Basic
public import TauCeti.Algebra.MonoidAlgebra.Reduced
public import TauCeti.Algebra.Regular.NatCast
public import TauCeti.RingTheory.Localization.Reduced
public import TauCeti.RingTheory.Localization.FractionRing

/-!
# Total quotient rings of monoid algebras

For a finite commutative monoid `M` and a coefficient ring `R` with Artinian total quotient
ring `K`, `K[M]` is the total quotient ring of `R[M]`. In particular, rationalizing the coefficients
computes the total quotient ring of an integral finite abelian group ring. The group ring
need not be a domain: all its nonzerodivisors become units after rationalization.

For a finite abelian group whose order is nonzero in the coefficient fraction field, the
total quotient ring is a finite product of finite-dimensional field extensions of that field.
The components are the quotients by the maximal ideals of the coefficient-field group algebra.
The decomposition respects coefficient scalars. In characteristic zero, all component fields
have characteristic zero; the general `charZero_of_injective_algebraMap` theorem can be
used to equip them with this instance.

For a finitely generated, possibly infinite, commutative group `G` and a formally real Noetherian
coefficient ring `R`, such as `ℤ` or `ℚ`, the group ring `R[G]` is reduced and Noetherian, so its
total quotient ring is Artinian. It is therefore again a finite product of fields, namely its
residue fields at its maximal ideals, and these have characteristic zero
(`MonoidAlgebra.exists_ringEquiv_pi_field_of_isFractionRing`). Torsion in `G` is allowed, and no
splitting of `G` into free and torsion parts is chosen.

The algebra structure on coefficient extension is Mathlib's scoped `AlgebraMonoidAlgebra`
structure. No field structure on the group ring is assumed.

## References

* V. Turaev, *Introduction to Combinatorial Torsions*, Chapter I, for total quotient
  coefficients of abelian group rings.
* D. S. Passman, *The Algebraic Structure of Group Rings*, Wiley, 1977, for reducedness of
  commutative group rings in characteristic zero.
-/

public section

open scoped AlgebraMonoidAlgebra

-- Mathlib declares the multiplicative and additive finiteness instances separately.
attribute [to_additive existing] _root_.MonoidAlgebra.moduleFinite

/-- A monoid algebra over an Artinian coefficient ring is Artinian when the monoid is finite. -/
@[to_additive (dont_translate := R)
/-- An additive monoid algebra over an Artinian coefficient ring is Artinian when the
additive monoid is finite. -/]
instance MonoidAlgebra.isArtinianRing_of_finite (R M : Type*) [Ring R]
    [IsArtinianRing R] [Monoid M] [Finite M] : IsArtinianRing (MonoidAlgebra R M) :=
  isArtinian_of_tower R inferInstance

/-- For a finite commutative monoid, extension to an Artinian total quotient ring of the
coefficients is already the total quotient ring of the monoid algebra. -/
@[to_additive (dont_translate := R K)
/-- For a finite commutative additive monoid, extension to an Artinian total quotient ring of
the coefficients is already the total quotient ring of the additive monoid algebra. -/]
theorem MonoidAlgebra.isFractionRing_of_finite (R K M : Type*) [CommRing R] [CommRing K]
    [IsArtinianRing K] [Algebra R K] [IsFractionRing R K] [CommMonoid M] [Finite M] :
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

scoped[AlgebraMonoidAlgebra] attribute [instance]
  MonoidAlgebra.isFractionRing_of_finite AddMonoidAlgebra.isFractionRing_of_finite

/-- A finite abelian group algebra whose group order is nonzero in the coefficient field is
the product of its maximal-ideal field components, as an algebra over the coefficient field.
The index set is finite, and each component is finite-dimensional over that field. -/
noncomputable def MonoidAlgebra.algEquivPiField
    (K G : Type*) [Field K] [CommGroup G] [Finite G] [NeZero (Nat.card G : K)] :
    MonoidAlgebra K G ≃ₐ[K]
      ∀ I : MaximalSpectrum (MonoidAlgebra K G), MonoidAlgebra K G ⧸ I.asIdeal :=
  (IsArtinianRing.equivPi (MonoidAlgebra K G)).restrictScalars K

-- Maschke's multiplicative module and additive ring instances are not a to_additive pair.
/-- A finite additive abelian group algebra whose group order is nonzero in the coefficient
field is the product of its maximal-ideal field components as a coefficient-field algebra.
The index set is finite, and each component is finite-dimensional over that field. -/
noncomputable def AddMonoidAlgebra.algEquivPiField
    (K H : Type*) [Field K] [AddCommGroup H] [Finite H] [NeZero (Nat.card H : K)] :
    AddMonoidAlgebra K H ≃ₐ[K]
      ∀ I : MaximalSpectrum (AddMonoidAlgebra K H), AddMonoidAlgebra K H ⧸ I.asIdeal :=
  (IsArtinianRing.equivPi (AddMonoidAlgebra K H)).restrictScalars K

/-- Evaluation of the field decomposition is the quotient map at the chosen maximal ideal. -/
@[simp]
theorem MonoidAlgebra.algEquivPiField_apply
    (K G : Type*) [Field K] [CommGroup G] [Finite G] [NeZero (Nat.card G : K)]
    (x : MonoidAlgebra K G) (I : MaximalSpectrum (MonoidAlgebra K G)) :
    MonoidAlgebra.algEquivPiField K G x I = Ideal.Quotient.mk I.asIdeal x :=
  IsArtinianRing.equivPi_apply _ x I

/-- Evaluation of the field decomposition is the quotient map at the chosen maximal ideal. -/
@[simp]
theorem AddMonoidAlgebra.algEquivPiField_apply
    (K H : Type*) [Field K] [AddCommGroup H] [Finite H] [NeZero (Nat.card H : K)]
    (x : AddMonoidAlgebra K H) (I : MaximalSpectrum (AddMonoidAlgebra K H)) :
    AddMonoidAlgebra.algEquivPiField K H x I = Ideal.Quotient.mk I.asIdeal x :=
  IsArtinianRing.equivPi_apply _ x I

section CharZero

variable (R M K : Type*) [CommRing R] [IsAddTorsionFree R] [CommMonoid M]
  [CommRing K] [Algebra (MonoidAlgebra R M) K] [IsFractionRing (MonoidAlgebra R M) K]

include R M in
/-- Every quotient of the total quotient ring of a monoid ring over a ring without additive torsion
by a proper ideal has characteristic zero. -/
@[to_additive (dont_translate := R K)
/-- Every quotient of the total quotient ring of an additive monoid ring over a ring without
additive torsion by a proper ideal has characteristic zero. -/]
theorem MonoidAlgebra.charZero_quotient_of_isFractionRing {I : Ideal K} (hI : I ≠ ⊤) :
    CharZero (K ⧸ I) :=
  IsFractionRing.charZero_quotient (MonoidAlgebra R M) K
    (fun _ ↦ TauCeti.natCast_mem_nonZeroDivisors) hI

end CharZero

section FG

open scoped nonZeroDivisors

universe u v w

variable (R : Type u) (G : Type v) (K : Type w) [CommRing R] [IsFormallyReal R] [CommGroup G]
  [CommRing K] [Algebra (MonoidAlgebra R G) K] [IsFractionRing (MonoidAlgebra R G) K]

/-- The total quotient ring of the group ring of a finitely generated commutative group over a
formally real Noetherian ring is Artinian. -/
@[to_additive (dont_translate := R K)
/-- The total quotient ring of the group ring of a finitely generated commutative additive group
over a formally real Noetherian ring is Artinian. -/]
theorem MonoidAlgebra.isArtinianRing_of_isFractionRing [IsNoetherianRing R] [Group.FG G] :
    IsArtinianRing K :=
  have : Monoid.FG G := Group.fg_iff_monoid_fg.mp ‹_›
  have : IsNoetherianRing (MonoidAlgebra R G) :=
    Algebra.FiniteType.isNoetherianRing R (MonoidAlgebra R G)
  IsFractionRing.isArtinianRing_of_isReduced (MonoidAlgebra R G) K

/-- The total quotient ring of the group ring of a finitely generated commutative group over a
formally real Noetherian ring is a finite product of fields of characteristic zero. -/
theorem MonoidAlgebra.exists_ringEquiv_pi_field_of_isFractionRing [IsNoetherianRing R]
    [Group.FG G] :
    ∃ (ι : Type w) (_ : Finite ι) (F : ι → Type w) (_ : ∀ i, Field (F i)),
      (∀ i, CharZero (F i)) ∧ Nonempty (K ≃+* ∀ i, F i) := by
  have := MonoidAlgebra.isArtinianRing_of_isFractionRing R G K
  have := IsLocalization.isReduced (MonoidAlgebra R G)⁰ K
  exact ⟨MaximalSpectrum K, inferInstance, fun I ↦ K ⧸ I.asIdeal,
    fun I ↦ have := I.isMaximal; Ideal.Quotient.field I.asIdeal,
    fun I ↦ MonoidAlgebra.charZero_quotient_of_isFractionRing R G K I.isMaximal.ne_top,
    ⟨(IsArtinianRing.equivPi K).toRingEquiv⟩⟩

end FG

section AddFG

open scoped nonZeroDivisors

universe u v w

variable (R : Type u) (H : Type v) (K : Type w) [CommRing R] [IsFormallyReal R] [AddCommGroup H]
  [CommRing K] [Algebra (AddMonoidAlgebra R H) K] [IsFractionRing (AddMonoidAlgebra R H) K]

/-- The total quotient ring of the group ring of a finitely generated commutative additive group
over a formally real Noetherian ring, such as `ℤ[H]` for a finitely generated abelian group `H`,
is a finite product of fields of characteristic zero. -/
theorem AddMonoidAlgebra.exists_ringEquiv_pi_field_of_isFractionRing [IsNoetherianRing R]
    [AddGroup.FG H] :
    ∃ (ι : Type w) (_ : Finite ι) (F : ι → Type w) (_ : ∀ i, Field (F i)),
      (∀ i, CharZero (F i)) ∧ Nonempty (K ≃+* ∀ i, F i) := by
  have := AddMonoidAlgebra.isArtinianRing_of_isFractionRing R H K
  have := IsLocalization.isReduced (AddMonoidAlgebra R H)⁰ K
  exact ⟨MaximalSpectrum K, inferInstance, fun I ↦ K ⧸ I.asIdeal,
    fun I ↦ have := I.isMaximal; Ideal.Quotient.field I.asIdeal,
    fun I ↦ AddMonoidAlgebra.charZero_quotient_of_isFractionRing R H K I.isMaximal.ne_top,
    ⟨(IsArtinianRing.equivPi K).toRingEquiv⟩⟩

end AddFG
