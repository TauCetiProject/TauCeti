/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.Invariant.Galois

/-!
# Galois groups of integral closures in fixed fields

Let `A` be a domain with fraction field `K`, let `M / K` be finite Galois, and let `B` be the
integral closure of `A` in `M`. For a subgroup `H` of `Gal(M/K)`, let `C` be the integral closure
of `A` in the fixed field `M ^ H`. Then `H`, acting on `B` by restriction of the action of
`Gal(M/K)`, is a Galois group for the ring extension `B / C`.

No Dedekind, Noetherian, or separability hypothesis on `A` is needed: the integral closure `C`
is integrally closed because its fraction field is `M ^ H`.

## Main results

* `TauCeti.IsIntegralClosure.smulCommClass`: the restricted action of `Gal(L/K)` on an integral
  closure commutes with the base ring.
* `TauCeti.IsIntegralClosure.isGaloisGroup_fixedField`: `H` is a Galois group for `B / C`.
-/

public section

open IntermediateField

namespace TauCeti

/-- The action of `Gal(L/K)` on an integral closure `B` of `A` in `L` commutes with the action of
`A`, since it is the restriction of the action by `K`-algebra automorphisms of `L`. -/
theorem IsIntegralClosure.smulCommClass (A K L B : Type*)
    [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L] :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    SMulCommClass (L ≃ₐ[K] L) A B :=
  letI := IsIntegralClosure.MulSemiringAction A K L B
  ⟨fun σ a b ↦ map_smul (galRestrict A K L B σ) a b⟩

/-- Let `B` and `C` be the integral closures of `A` in a finite Galois extension `M` of its
fraction field `K` and in the fixed field `M ^ H` of a subgroup `H` of `Gal(M/K)`. Then `H` is a
Galois group for `B / C`, acting by restriction of the action of `Gal(M/K)` on `B`. -/
theorem IsIntegralClosure.isGaloisGroup_fixedField (A K M B C : Type*)
    [CommRing A] [CommRing B] [CommRing C] [Field K] [Field M]
    [Algebra A K] [Algebra K M] [Algebra A M] [IsScalarTower A K M]
    [Algebra A B] [Algebra B M] [IsScalarTower A B M]
    [IsFractionRing A K] [IsIntegralClosure B A M] [IsGalois K M] [FiniteDimensional K M]
    (H : Subgroup (M ≃ₐ[K] M))
    [Algebra A C] [Algebra C ↥(fixedField H)] [Algebra C M]
    [IsScalarTower A C ↥(fixedField H)] [IsScalarTower C ↥(fixedField H) M]
    [IsScalarTower A C M] [IsIntegralClosure C A ↥(fixedField H)]
    [Algebra C B] [IsScalarTower C B M] :
    letI := IsIntegralClosure.MulSemiringAction A K M B
    IsGaloisGroup H C B := by
  let _ := IsIntegralClosure.MulSemiringAction A K M B
  have : IsDomain A := (IsFractionRing.injective A K).isDomain
  have : IsDomain C := (IsIntegralClosure.algebraMap_injective C A ↥(fixedField H)).isDomain
    (algebraMap C ↥(fixedField H))
  have : IsFractionRing C ↥(fixedField H) :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K ↥(fixedField H) C
  have : Algebra.IsIntegral A C := IsIntegralClosure.isIntegral_algebra A ↥(fixedField H)
  -- An integral closure in its own fraction field is integrally closed.
  have : IsIntegrallyClosed C := (isIntegrallyClosed_iff ↥(fixedField H)).mpr fun {x} hx ↦
    ⟨IsIntegralClosure.mk' C x (isIntegral_trans (R := A) _ hx),
      IsIntegralClosure.algebraMap_mk' _ _ _⟩
  have : IsIntegralClosure B C M := IsIntegralClosure.tower_top (R := A) (A := C) (B := M) (C := B)
  have : Algebra.IsIntegral C B := IsIntegralClosure.isIntegral_algebra C M
  have : IsDomain B := (IsIntegralClosure.algebraMap_injective B A M).isDomain (algebraMap B M)
  have : IsFractionRing B M := IsIntegralClosure.isFractionRing_of_finite_extension A K M B
  let _ := IsIntegralClosure.MulSemiringAction C ↥(fixedField H) M B
  have : IsGaloisGroup (M ≃ₐ[↥(fixedField H)] M) C B :=
    IsGaloisGroup.of_isFractionRing (M ≃ₐ[↥(fixedField H)] M) C B ↥(fixedField H) M
  exact IsGaloisGroup.of_mulEquiv (subgroupEquivAlgEquiv H) fun h x ↦ by
    apply IsFractionRing.injective B M
    -- Expose the two integral-closure actions so their restrictions can be compared in `M`.
    change algebraMap B M (galRestrict C ↥(fixedField H) M B (subgroupEquivAlgEquiv H h) x) =
      algebraMap B M (galRestrict A K M B h.1 x)
    rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply]
    rfl

end TauCeti
