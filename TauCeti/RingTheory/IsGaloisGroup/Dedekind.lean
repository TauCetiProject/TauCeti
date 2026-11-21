/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import TauCeti.RingTheory.DedekindDomain.IntegralClosure
public import TauCeti.RingTheory.IsGaloisGroup.IntegralClosure

/-!
# Integral closures in a Galois extension over a Dedekind base

Let `A` be a Dedekind domain with fraction field `K`, let `M / K` be a finite Galois extension,
and let `B` be the integral closure of `A` in `M`. For a subgroup `H` of `Gal(M/K)`, let `C` be the
integral closure of `A` in the fixed field `M ^ H`. This file bundles the structure that a
Dedekind base provides for these rings: `B` is a domain, finite and flat over `A`, with Galois
group `Gal(M/K)`, and `C` is a Dedekind domain, finite and flat over `A`. Together with
`TauCeti.IsIntegralClosure.isGaloisGroup_fixedField_and_faithfulSMul`, these are the instances
needed to specialize statements about invariant rings to integral closures.

The statement for `C` only requires that `M ^ H` be finite and separable over `K`; the ambient
extension `M / K` need not be finite or Galois.

## Main results

* `TauCeti.IsIntegralClosure.isDomain_and_finite_and_flat_and_isGaloisGroup`: `B` is a domain,
  finite and flat over `A`, with Galois group `Gal(M/K)`.
* `TauCeti.IsIntegralClosure.isDedekindDomain_and_finite_and_flat_fixedField`: `C` is a Dedekind
  domain, finite and flat over `A`.
-/

public section

open IntermediateField

namespace TauCeti.IsIntegralClosure

variable {A K M : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field M] [Algebra K M]

section Top

variable [FiniteDimensional K M] [IsGalois K M] {B : Type*} [Algebra A M]
  [IsScalarTower A K M] [CommRing B] [Algebra A B] [Algebra B M] [IsScalarTower A B M]
  [IsIntegralClosure B A M]
  [MulSemiringAction Gal(M/K) B] [SMulDistribClass Gal(M/K) B M]

include K M in
/-- Over a Dedekind base, `B` is a finite flat `A`-algebra and a domain, with Galois group
`Gal(M/K)`. -/
theorem isDomain_and_finite_and_flat_and_isGaloisGroup :
    IsDomain B ∧ Module.Finite A B ∧ Module.Flat A B ∧ IsGaloisGroup Gal(M/K) A B := by
  have : IsDomain B := (_root_.IsIntegralClosure.algebraMap_injective B A M).isDomain _
  have : FaithfulSMul A M := .trans A K M
  exact ⟨inferInstance, _root_.IsIntegralClosure.finite A K M B, IsIntegralClosure.flat A M B,
    IsGaloisGroup.of_isIntegralClosure Gal(M/K) A B K M⟩

end Top

section FixedField

variable (H : Subgroup Gal(M/K)) [Module.Finite K (fixedField H)]
  [Algebra.IsSeparable K (fixedField H)] [Algebra A (fixedField H)]
  [IsScalarTower A K (fixedField H)]
  (C : Type*) [CommRing C] [Algebra A C] [Algebra C (fixedField H)]
  [IsScalarTower A C (fixedField H)] [IsIntegralClosure C A (fixedField H)]

include K M H in
/-- Over a Dedekind base, the integral closure in a finite separable fixed field is a Dedekind
domain and a finite flat `A`-algebra. The ambient extension need not be finite or Galois. -/
theorem isDedekindDomain_and_finite_and_flat_fixedField :
    IsDedekindDomain C ∧ Module.Finite A C ∧ Module.Flat A C := by
  have : FaithfulSMul A (fixedField H) := .trans A K (fixedField H)
  exact ⟨IsIntegralClosure.isDedekindDomain A K (fixedField H) C,
    _root_.IsIntegralClosure.finite A K (fixedField H) C,
    IsIntegralClosure.flat A (fixedField H) C⟩

end FixedField

end TauCeti.IsIntegralClosure
