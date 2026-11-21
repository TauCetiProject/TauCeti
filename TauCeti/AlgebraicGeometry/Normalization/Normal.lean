/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import TauCeti.AlgebraicGeometry.Scheme.Normal
import TauCeti.RingTheory.IntegralClosure.ReducedArtinian
import TauCeti.RingTheory.Localization.Reduced
import TauCeti.RingTheory.SerreCondition.Normal

/-!
# Normality of relative normalization in a normal scheme

For an affine morphism `f : X ⟶ Y` with `X` normal and locally Noetherian, the relative
normalization of `Y` in `X` is normal. Neither finiteness of the normalization nor integrality
of `X` or `Y` is required. In particular the source may be disconnected.

On an affine open of `Y`, write `A → B` for the map on sections. The ring `B` is normal and
Noetherian, so it is integrally closed in its total quotient ring, a reduced Artinian ring.
The integral closure of `A` in `B` is therefore also integrally closed in that reduced Artinian
ring, which makes its localizations at primes integrally closed domains.

This ensures that normalizing a model in its smooth generic fibre produces a normal total
space, as required when iterating normalized blowups.

## References

* The Stacks Project, Definition 29.54.3 (035H), relative normalization.
* The Stacks Project, Lemma 10.37.16 (030C), normal rings and total quotient rings.
* The Stacks Project, Lemma 10.157.4 (031S), Serre's criterion for normality.
-/

public section

open CategoryTheory TauCeti TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- The relative normalization in a locally Noetherian normal scheme along an affine morphism
is normal. No finiteness hypothesis on the normalization or irreducibility hypothesis is needed.
-/
instance isNormalScheme_normalization {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    [IsLocallyNoetherian X] [IsNormalScheme X] : IsNormalScheme f.normalization := by
  refine isNormalScheme_iff_forall_exists_affineOpens.mpr fun x ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.fromNormalization x))
      isOpen_univ
  refine ⟨⟨_, hU.preimage f.fromNormalization⟩, hxU, ?_⟩
  let := (f.app U).hom.toAlgebra
  let B := Γ(X, f ⁻¹ᵁ U)
  have : IsNoetherianRing B := IsLocallyNoetherian.component_noetherian
    ⟨_, hU.preimage f⟩
  have hB := (isNormalScheme_Spec_iff_forall_localization B).mp
    (isNormalScheme_iff_forall_affineOpens.mp ‹IsNormalScheme X› ⟨_, hU.preimage f⟩)
  obtain ⟨hR, hS⟩ :=
    forall_isDomain_and_isIntegrallyClosed_iff_satisfiesSerreR_one_and_satisfiesSerreS_two.mp hB
  have : IsIntegrallyClosed B :=
    isIntegrallyClosed_of_satisfiesSerreR_one_of_satisfiesSerreS_two hR hS
  let E := FractionRing B
  let A := Γ(Y, U)
  let C := integralClosure A B
  have : IsIntegralClosure C A E :=
    IsIntegralClosure.of_isIntegralClosure_of_isIntegrallyClosedIn A C B E
  have : IsIntegrallyClosedIn C E := IsIntegrallyClosedIn.of_isIntegralClosure (R := A)
  have : IsArtinianRing E := IsFractionRing.isArtinianRing_of_isReduced B E
  have : _root_.IsReduced E := IsLocalization.isReduced (nonZeroDivisors B) E
  have hC : IsNormalScheme (Spec (.of C)) :=
    (isNormalScheme_Spec_iff_forall_localization _).mpr fun p _ ↦
      ⟨IsIntegrallyClosedIn.isDomain_localization_atPrime E p,
        IsIntegrallyClosedIn.isIntegrallyClosed_localization_atPrime E p⟩
  exact IsNormalScheme.of_isOpenImmersion
    (Spec.map (f.normalizationObjIso hU).inv)

end AlgebraicGeometry.Scheme.Hom
