/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

-- Public because `IsDedekindDomain` appears in the STATEMENTS of `finite_of_fraction_model` and
-- `finite_of_separable_model`, which are public; a plain import cannot carry a public statement.
public import Mathlib.RingTheory.DedekindDomain.Basic
-- Proof-only: the integral-closure-over-a-Dedekind-domain machinery is used in the proofs; the
-- public statements mention only `IsDedekindDomain`, which comes from `DedekindDomain.Basic`.
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
-- Proof-only, and NOT redundant with `DedekindDomain.Overring` below, which imports it plainly
-- and so re-exports nothing. This supplies the `IsFractionRing` instance on a subalgebra of the
-- fraction field, which `finite_of_fraction_model` needs; removing it fails to synthesize.
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import TauCeti.RingTheory.Adjoin.Tower
import TauCeti.RingTheory.DedekindDomain.Overring
import TauCeti.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# A finite normalization from a separating polynomial model

Let `A` be a polynomial algebra `F[X]` over a field, `K` its fraction field and `L` a finite
separable extension of `K`. If every element of `A` is integral over a base ring `R` inside `L`,
then any integral closure `C` of `R` in `L` is a **finite** `R`-module.

This is the finiteness a relative ideal norm needs: norms of ideals are defined by a determinant,
so the extension has to be finite as a module, not merely algebraic. The polynomial-model form is
the one an affine curve supplies, its coordinate ring being finite over a polynomial ring in one
of the coordinates.

## Main results

* `IsIntegralClosure.finite_of_fraction_model`: the finite-type Dedekind model, over the fraction
  field itself.
* `IsIntegralClosure.finite_of_separable_model`: a finite separable extension of that fraction
  field.
* `IsIntegralClosure.finite_of_polynomial_model`: the specialization to a polynomial model, which
  is a Dedekind domain of finite type.

Companion results live in `NormalizationFinite.lean`, which proves Krull–Akizuki: the integral
closure is *Noetherian* with no separability hypothesis, but need not be a finite module. Neither
statement subsumes the other.

## Provenance

Adapted from D. K. Angdinata's `NormalizationFinite.lean`, Apache-2.0, supplied by the author on
2026-09-07, declarations `Subalgebra.isIntegrallyClosed_overring`,
`TauCeti.isIntegral_trans_common`, `Finset.algebraMap_mem_adjoin_image`,
`IsIntegralClosure.finite_of_fraction_model`, `IsIntegralClosure.finite_of_separable_model` and
`IsIntegralClosure.finite_of_polynomial_model`.
-/

noncomputable section

public section

open Polynomial

open scoped nonZeroDivisors

namespace IsIntegralClosure

section

variable {F R A K : Type*} [CommRing F] [CommRing R] [CommRing A] [Field K]
  [Algebra F R] [Algebra F A] [Algebra F K] [Algebra R K] [Algebra A K]
  [IsScalarTower F R K] [IsScalarTower F A K]

variable {C : Type*} [IsDedekindDomain A] [IsFractionRing A K]
  [CommRing C] [Algebra R C] [Algebra C K] [IsScalarTower R C K]
  [IsIntegralClosure C R K] [Algebra.FiniteType F A]

include F in
/-- A finite-type fraction-field model integral over the base yields a finite normalization. -/
theorem finite_of_fraction_model
    (hint : ∀ x : A, IsIntegral R (algebraMap A K x)) : Module.Finite R C := by
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType F A).out
  let B : Subalgebra R K := Algebra.adjoin R (algebraMap A K '' (s : Set A))
  let finite : Module.Finite R B :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (s.finite_toSet.image _) fun _ hx ↦ by
      obtain ⟨x, -, rfl⟩ := hx
      exact hint x
  let D : Subalgebra A K :=
    { carrier := B
      mul_mem' := B.mul_mem
      add_mem' := B.add_mem
      algebraMap_mem' := Set.algebraMap_mem_adjoin_image _ hs }
  let integrallyClosedB : IsIntegrallyClosed B := Subalgebra.isIntegrallyClosed_overring D
  let fractionRingB : IsFractionRing B K := inferInstanceAs (IsFractionRing D K)
  let isIntegralClosure : IsIntegralClosure B R K := IsIntegralClosure.of_isIntegrallyClosed B R K
  exact Module.Finite.equiv (IsIntegralClosure.equiv R B K C).toLinearEquiv

end

section

variable {F R A K L C : Type*} [CommRing F] [CommRing R] [CommRing A]
  [Field K] [Field L] [CommRing C]
  [Algebra F R] [Algebra F A] [Algebra F L] [Algebra R L]
  [Algebra A K] [Algebra A L] [Algebra K L]
  [IsScalarTower F R L] [IsScalarTower F A L] [IsScalarTower A K L]
  [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [IsDedekindDomain A] [Algebra.FiniteType F A]
  [Algebra R C] [Algebra C L] [IsScalarTower R C L] [IsIntegralClosure C R L]

include F K in
/-- A finite separable field model integral over the base yields a finite normalization. -/
theorem finite_of_separable_model
    (hint : ∀ x : A, IsIntegral R (algebraMap A L x)) : Module.Finite R C := by
  let D := integralClosure A L
  let finite : Module.Finite A D := IsIntegralClosure.finite A K L D
  let dedekind : IsDedekindDomain D := IsIntegralClosure.isDedekindDomain A K L D
  let fractionRing : IsFractionRing D L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L D
  let finiteType : Algebra.FiniteType F D :=
    (inferInstance : Algebra.FiniteType F A).trans inferInstance
  exact finite_of_fraction_model (F := F) (A := D) (K := L)
    fun x ↦ TauCeti.isIntegral_trans_common hint x.property

end

section

variable {F R A K L C : Type*} [Field F] [CommRing R] [CommRing A]
  [Field K] [Field L] [CommRing C]
  [Algebra F R] [Algebra F A] [Algebra F L] [Algebra R L]
  [Algebra A K] [Algebra A L] [Algebra K L]
  [IsScalarTower F R L] [IsScalarTower F A L] [IsScalarTower A K L]
  [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Algebra R C] [Algebra C L] [IsScalarTower R C L] [IsIntegralClosure C R L]

include K in
/-- A separating polynomial model integral over the base yields a finite normalization. -/
theorem finite_of_polynomial_model (e : F[X] ≃ₐ[F] A)
    (hint : ∀ x : A, IsIntegral R (algebraMap A L x)) : Module.Finite R C := by
  let nontrivial : Nontrivial A := e.symm.toRingHom.domain_nontrivial
  let noZeroDivisors : NoZeroDivisors A := Function.Injective.noZeroDivisors e.symm
    e.symm.injective e.symm.map_zero e.symm.map_mul
  let domain : IsDomain A := NoZeroDivisors.to_isDomain A
  let principal : IsPrincipalIdealRing A :=
    IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  let dedekind : IsDedekindDomain A := inferInstance
  let finiteType : Algebra.FiniteType F A :=
    Algebra.FiniteType.of_surjective e.toAlgHom e.surjective
  exact finite_of_separable_model (F := F) (R := R) (A := A) (K := K) (L := L) (C := C) hint

end

end IsIntegralClosure
