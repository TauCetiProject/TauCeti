/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Localization
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Artinian.Module
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
  have : Module.Finite K (MonoidAlgebra K M) :=
    Module.Finite.of_basis (_root_.MonoidAlgebra.basis M K)
  have : IsArtinianRing (MonoidAlgebra K M) := isArtinian_of_tower K inferInstance
  refine IsLocalization.of_le U (nonZeroDivisors (MonoidAlgebra R M)) hU ?_
  intro x hx
  exact IsArtinianRing.isUnit_of_mem_nonZeroDivisors
    (a := algebraMap (MonoidAlgebra R M) (MonoidAlgebra K M) x)
    (IsLocalization.nonZeroDivisors_le_comap U (MonoidAlgebra K M) hx)

universe u v w q

/-- If the order of a finite abelian group is nonzero in the coefficient fraction field,
every total quotient ring of its group algebra admits a compatible coefficient-field algebra
structure and is a finite product of finite-dimensional field extensions. Compatibility means
that the coefficient-field action extends the original coefficient map from `R`. -/
theorem AddMonoidAlgebra.exists_totalQuotient_algEquiv_pi_field
    (R : Type u) (K : Type v) (H : Type w) (Q : Type q)
    [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup H] [Finite H] [NeZero (Nat.card H : K)]
    [CommRing Q] [Algebra (AddMonoidAlgebra R H) Q]
    [IsFractionRing (AddMonoidAlgebra R H) Q] :
    ∃ (_ : Algebra K Q)
      (_ : ∀ r : R, algebraMap K Q (algebraMap R K r) =
        algebraMap (AddMonoidAlgebra R H) Q (algebraMap R (AddMonoidAlgebra R H) r))
      (ι : Type (max v w)) (_ : Finite ι) (F : ι → Type (max v w))
      (_ : ∀ i, Field (F i)) (_ : ∀ i, Algebra K (F i))
      (_ : ∀ i, Module.Finite K (F i)), Nonempty (Q ≃ₐ[K] ∀ i, F i) := by
  let A := AddMonoidAlgebra K H
  have : Module.Finite K A := Module.Finite.of_basis (_root_.AddMonoidAlgebra.basis H K)
  have : IsArtinianRing A := isArtinian_of_tower K inferInstance
  have : IsFractionRing (AddMonoidAlgebra R H) A :=
    AddMonoidAlgebra.isFractionRing_of_finite R K H
  let e := IsLocalization.algEquiv (nonZeroDivisors (AddMonoidAlgebra R H)) Q A
  let : Algebra K Q := (e.symm.toRingHom.comp (algebraMap K A)).toAlgebra
  let F (I : MaximalSpectrum A) := A ⧸ I.asIdeal
  let (I : MaximalSpectrum A) : Field (F I) := Ideal.Quotient.field I.asIdeal
  let eK : Q ≃ₐ[K] A :=
    { e.toRingEquiv with commutes' := fun k ↦ e.apply_symm_apply (algebraMap K A k) }
  refine ⟨inferInstance, ?_, MaximalSpectrum A, inferInstance, F,
    inferInstance, inferInstance, inferInstance, ?_⟩
  · intro r
    exact (congrArg e.symm
      ((IsScalarTower.algebraMap_apply R K A r).symm.trans
        (IsScalarTower.algebraMap_apply R (AddMonoidAlgebra R H) A r))).trans
      (e.symm.commutes _)
  · exact ⟨eK.trans ((IsArtinianRing.equivPi A).restrictScalars K)⟩

/-- In characteristic zero, every total quotient ring of a finite abelian group algebra is
a finite product of characteristic-zero fields, finite-dimensional over the coefficient
fraction field. The returned algebra structure extends the original coefficient map. -/
theorem AddMonoidAlgebra.exists_totalQuotient_algEquiv_pi_field_charZero
    (R : Type u) (K : Type v) (H : Type w) (Q : Type q)
    [CommRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup H] [Finite H] [CommRing Q] [Algebra (AddMonoidAlgebra R H) Q]
    [IsFractionRing (AddMonoidAlgebra R H) Q] :
    ∃ (_ : Algebra K Q)
      (_ : ∀ r : R, algebraMap K Q (algebraMap R K r) =
        algebraMap (AddMonoidAlgebra R H) Q (algebraMap R (AddMonoidAlgebra R H) r))
      (ι : Type (max v w)) (_ : Finite ι) (F : ι → Type (max v w))
      (_ : ∀ i, Field (F i)) (_ : ∀ i, Algebra K (F i))
      (_ : ∀ i, Module.Finite K (F i)) (_ : ∀ i, CharZero (F i)),
      Nonempty (Q ≃ₐ[K] ∀ i, F i) := by
  have : NeZero (Nat.card H : K) := ⟨by simp [Nat.card_pos.ne']⟩
  obtain ⟨a, ha, ι, hι, F, hF, hA, hfin, e⟩ :=
    AddMonoidAlgebra.exists_totalQuotient_algEquiv_pi_field R K H Q
  let := a
  let := hF
  let := hA
  refine ⟨a, ha, ι, hι, F, hF, hA, hfin, ?_, e⟩
  intro i
  exact charZero_of_injective_algebraMap (algebraMap K (F i)).injective

end TauCeti
