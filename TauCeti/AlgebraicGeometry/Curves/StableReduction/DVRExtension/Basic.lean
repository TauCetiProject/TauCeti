/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Finite separable extensions of a discrete valuation ring, with a chosen place

Let `R` be a discrete valuation ring with fraction field `K`. A `TauCeti.FiniteDVRExtension R K`
records a finite separable extension `K'` of `K` together with a *chosen* place of `K'` above the
closed point of `R`: the integral closure `C` of `R` in `K'`, a maximal ideal `𝔪'` of `C` lying
over the maximal ideal of `R`, and a ring `R'` presented as the localization of `C` at `𝔪'`.

The choice is genuine data. The integral closure `C` is in general semilocal rather than local, so
`C` is not itself a discrete valuation ring, and the valuation of `R` extends to `K'` in as many
ways as `C` has maximal ideals; the package fixes one such extension. Accordingly `R'` is not
required to be `Localization.AtPrime 𝔪'` on the nose: it is any ring carrying
`IsLocalization.AtPrime`, so that a package can be assembled from whichever model of the local ring
is already at hand.

The package carries only what is not forced: the two type-valued carriers, the algebra maps that
relate them, the chosen ideal, and the `Ideal.LiesOver` witness pinning it above the closed point
of `R`. That `R'` is a discrete valuation ring with fraction field `K'` dominating `R` is proved
here rather than assumed. Domination in particular makes `algebraMap R R'` an `IsLocalHom`, which
is what lets Mathlib's residue-field machinery view the residue field of `R'` as an extension of
that of `R`.

## Main definitions

* `TauCeti.FiniteDVRExtension`: the package described above.
* `TauCeti.FiniteDVRExtension.integralClosure`: the integral closure of `R` in the extension field,
  the ring the chosen place is an ideal of.
* `TauCeti.FiniteDVRExtension.of`: the package attached to a maximal ideal of that integral closure
  lying over the maximal ideal of `R`, with `Localization.AtPrime` as its local ring.

## Main results

* `TauCeti.FiniteDVRExtension.isDiscreteValuationRing_localRing`: the chosen local ring is a
  discrete valuation ring.
* `TauCeti.FiniteDVRExtension.isFractionRing_localRing`: its fraction field is the extension field.
* `TauCeti.FiniteDVRExtension.under_prime`: the chosen place lies over the closed point of `R`.
* `TauCeti.FiniteDVRExtension.isLocalHom_algebraMap` and
  `TauCeti.FiniteDVRExtension.under_maximalIdeal_localRing`: the chosen local ring dominates `R`.
* `TauCeti.FiniteDVRExtension.exists_algEquiv_extensionField`: every finite separable extension of
  `K` is, as a `K`-algebra, the extension field of such a package, for some place above the closed
  point of `R`; to fix a specified place, use `TauCeti.FiniteDVRExtension.of`.

## References

The mathematics is standard; Q. Liu, *Algebraic Geometry and Arithmetic Curves*, covers reduction
of curves over a discrete valuation ring.
-/

public section

universe u

namespace TauCeti

open IsLocalRing

-- Source: the chosen-place convention (choose a maximal ideal of the integral closure above the
-- closed point and localize there, never treating the integral closure itself as a discrete
-- valuation ring) is the standing convention "DVR extensions are local data" of the Tau Ceti
-- `StableReduction` roadmap's `README.md`,
-- https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/StableReduction/README.md
-- and this structure adapts the `FiniteDVRExtension` signature (same carriers, algebra maps,
-- scalar towers and chosen prime) of that roadmap's `Suggested.lean`,
-- https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/StableReduction/Suggested.lean

/-- A finite separable extension of the fraction field `K` of a discrete valuation ring `R`,
together with a chosen place of that extension above the closed point of `R`.

The place is recorded as a maximal ideal `prime` of the integral closure of `R` in the extension
field, lying over the maximal ideal of `R`, together with a ring `localRing` presented as the
localization there. See `TauCeti.FiniteDVRExtension.of` for the construction from such an ideal and
`TauCeti.FiniteDVRExtension.exists_algEquiv_extensionField` for the fact that one always
exists. -/
structure FiniteDVRExtension (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] where
  /-- The extension field `K'` of `K`. -/
  extensionField : Type u
  [extensionFieldInst : Field extensionField]
  [extensionAlgebra : Algebra K extensionField]
  [extensionFinite : FiniteDimensional K extensionField]
  [extensionSeparable : Algebra.IsSeparable K extensionField]
  [extensionBaseAlgebra : Algebra R extensionField]
  [extensionTower : IsScalarTower R K extensionField]
  /-- The chosen place of `K'`, as a maximal ideal of the integral closure of `R` in `K'`. -/
  prime : Ideal (integralClosure R extensionField)
  [prime_isMaximal : prime.IsMaximal]
  [prime_liesOver : prime.LiesOver (maximalIdeal R)]
  /-- The local ring `R'` of the chosen place. -/
  localRing : Type u
  [localRingInst : CommRing localRing]
  [localRingClosureAlgebra : Algebra (integralClosure R extensionField) localRing]
  [localRingIsLocalization : IsLocalization.AtPrime localRing prime]
  [localRingAlgebra : Algebra R localRing]
  [localRingTower : IsScalarTower R (integralClosure R extensionField) localRing]
  [fractionAlgebra : Algebra localRing extensionField]
  [fractionTower : IsScalarTower (integralClosure R extensionField) localRing extensionField]

namespace FiniteDVRExtension

attribute [instance] extensionFieldInst extensionAlgebra extensionFinite extensionSeparable
  extensionBaseAlgebra extensionTower prime_isMaximal prime_liesOver localRingInst
  localRingClosureAlgebra localRingIsLocalization localRingAlgebra localRingTower
  fractionAlgebra fractionTower

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] (E : FiniteDVRExtension R K)

/-- The integral closure of `R` in the extension field: the ring the chosen place is an ideal
of. -/
abbrev integralClosure : Type u := _root_.integralClosure R E.extensionField

instance isFractionRing_integralClosure : IsFractionRing E.integralClosure E.extensionField :=
  IsIntegralClosure.isFractionRing_of_finite_extension R K E.extensionField _

instance isDedekindDomain_integralClosure : IsDedekindDomain E.integralClosure :=
  _root_.integralClosure.isDedekindDomain R K E.extensionField

/-- The integral closure `C` of `R` in `K'` is a Noetherian `R`-module: it is a finite `R`-module,
because `K'` is a finite separable extension of the fraction field of the Noetherian integrally
closed domain `R`. -/
instance isNoetherian_integralClosure : IsNoetherian R E.integralClosure :=
  IsIntegralClosure.isNoetherian R K E.extensionField _

instance faithfulSMul_extensionField : FaithfulSMul R E.extensionField :=
  have : FaithfulSMul K E.extensionField :=
    (faithfulSMul_iff_algebraMap_injective K E.extensionField).2
      (algebraMap K E.extensionField).injective
  FaithfulSMul.trans R K E.extensionField

instance faithfulSMul_integralClosure : FaithfulSMul R E.integralClosure :=
  FaithfulSMul.tower_bot R E.integralClosure E.extensionField

/-- The chosen place lies above the closed point of `R`, spelled as a contraction of ideals. -/
@[simp]
theorem under_prime : E.prime.under R = maximalIdeal R :=
  (Ideal.over_def E.prime _).symm

/-- The chosen place is a nonzero prime: it lies over the maximal ideal of `R`, which is nonzero
because a discrete valuation ring is not a field. -/
theorem prime_ne_bot : E.prime ≠ ⊥ :=
  Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field R) E.prime

instance isDomain_localRing : IsDomain E.localRing :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _ E.prime.primeCompl_le_nonZeroDivisors

/-- The extension field is the fraction field of the chosen localized ring. -/
instance isFractionRing_localRing : IsFractionRing E.localRing E.extensionField :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization E.prime.primeCompl _ _

/-- The local ring of the chosen place is a discrete valuation ring: it is the localization of the
Dedekind domain `C` at the nonzero prime `𝔪'`. -/
instance isDiscreteValuationRing_localRing : IsDiscreteValuationRing E.localRing :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain E.integralClosure
    E.prime_ne_bot _

instance isScalarTower_localRing : IsScalarTower R E.localRing E.extensionField :=
  .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply R E.integralClosure E.localRing,
      ← IsScalarTower.algebraMap_apply E.integralClosure E.localRing E.extensionField,
      ← IsScalarTower.algebraMap_apply R E.integralClosure E.extensionField]

instance faithfulSMul_localRing : FaithfulSMul R E.localRing :=
  have := IsLocalization.AtPrime.faithfulSMul E.localRing E.integralClosure E.prime
  FaithfulSMul.trans R E.integralClosure E.localRing

/-- The maximal ideal of the local ring of the chosen place contracts to the chosen place. -/
@[simp]
theorem under_maximalIdeal_integralClosure :
    (maximalIdeal E.localRing).under E.integralClosure = E.prime :=
  IsLocalization.AtPrime.under_maximalIdeal _ _

/-- The local ring of the chosen place dominates `R`. -/
instance isLocalHom_algebraMap : IsLocalHom (algebraMap R E.localRing) := by
  refine ((local_hom_TFAE (algebraMap R E.localRing)).out 4 1).1 fun x hx ↦ ?_
  rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply R E.integralClosure E.localRing]
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ E.prime _).2
    ((Ideal.mem_of_liesOver E.prime (maximalIdeal R) x).1 hx)

/-- Domination spelled as a contraction of ideals: the closed point of `Spec R'` lies over the
closed point of `Spec R`. -/
@[simp]
theorem under_maximalIdeal_localRing : (maximalIdeal E.localRing).under R = maximalIdeal R :=
  IsLocalRing.maximalIdeal_comap _

section Construction

variable (R K)
variable (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Algebra R L] [IsScalarTower R K L]

/-- The finite extension of the discrete valuation ring `R` cut out by a maximal ideal `P` of the
integral closure `C` of `R` in a finite separable extension `L` of `K`, provided `P` lies above the
maximal ideal of `R`. Its local ring is `Localization.AtPrime P`.

The map from that local ring to `L` is Mathlib's canonical comparison
`IsLocalization.localizationAlgebraOfSubmonoidLe` between the localizations of `C` at the two
submonoids `P.primeCompl ≤ nonZeroDivisors C`, the second localization being `L` itself because
`L` is the fraction field of `C`. -/
noncomputable def of (P : Ideal (_root_.integralClosure R L)) [P.IsPrime]
    [P.LiesOver (maximalIdeal R)] : FiniteDVRExtension R K :=
  haveI : IsFractionRing (_root_.integralClosure R L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension R K L _
  letI : P.IsMaximal := .of_liesOver_isMaximal P (maximalIdeal R)
  { extensionField := L
    prime := P
    localRing := Localization.AtPrime P
    fractionAlgebra := IsLocalization.localizationAlgebraOfSubmonoidLe _ _ P.primeCompl
      (nonZeroDivisors _) P.primeCompl_le_nonZeroDivisors
    fractionTower := IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ _ }

@[simp]
theorem of_extensionField (P : Ideal (_root_.integralClosure R L)) [P.IsPrime]
    [P.LiesOver (maximalIdeal R)] : (of R K L P).extensionField = L := by
  rw [of]

@[simp]
theorem of_prime (P : Ideal (_root_.integralClosure R L)) [P.IsPrime]
    [P.LiesOver (maximalIdeal R)] : HEq (of R K L P).prime P := by
  rw [of]

@[simp]
theorem of_localRing (P : Ideal (_root_.integralClosure R L)) [P.IsPrime]
    [P.LiesOver (maximalIdeal R)] : (of R K L P).localRing = Localization.AtPrime P := by
  rw [of]

@[simp]
theorem of_extensionFieldInst (P : Ideal (_root_.integralClosure R L)) [P.IsPrime]
    [P.LiesOver (maximalIdeal R)] :
    HEq (of R K L P).extensionFieldInst (inferInstance : Field L) := by
  rw [of]

@[simp]
theorem of_localRingInst (P : Ideal (_root_.integralClosure R L)) [P.IsPrime]
    [P.LiesOver (maximalIdeal R)] :
    HEq (of R K L P).localRingInst (inferInstance : CommRing (Localization.AtPrime P)) := by
  rw [of]

@[simp]
theorem of_extensionAlgebra (P : Ideal (_root_.integralClosure R L)) [P.IsPrime]
    [P.LiesOver (maximalIdeal R)] :
    HEq (of R K L P).extensionAlgebra (inferInstance : Algebra K L) := by
  rw [of]

@[simp]
theorem of_extensionBaseAlgebra (P : Ideal (_root_.integralClosure R L)) [P.IsPrime]
    [P.LiesOver (maximalIdeal R)] :
    HEq (of R K L P).extensionBaseAlgebra (inferInstance : Algebra R L) := by
  rw [of]

@[simp]
theorem of_localRingClosureAlgebra (P : Ideal (_root_.integralClosure R L)) [P.IsPrime]
    [P.LiesOver (maximalIdeal R)] :
    HEq (of R K L P).localRingClosureAlgebra
      (inferInstance : Algebra (_root_.integralClosure R L) (Localization.AtPrime P)) := by
  rw [of]

@[simp]
theorem of_localRingAlgebra (P : Ideal (_root_.integralClosure R L)) [P.IsPrime]
    [P.LiesOver (maximalIdeal R)] :
    HEq (of R K L P).localRingAlgebra (inferInstance : Algebra R (Localization.AtPrime P)) := by
  rw [of]

@[simp]
theorem of_fractionAlgebra (P : Ideal (_root_.integralClosure R L)) [P.IsPrime]
    [P.LiesOver (maximalIdeal R)] :
    haveI : IsFractionRing (_root_.integralClosure R L) L :=
      IsIntegralClosure.isFractionRing_of_finite_extension R K L _
    HEq (of R K L P).fractionAlgebra
      (IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.AtPrime P) L P.primeCompl
        (nonZeroDivisors _) P.primeCompl_le_nonZeroDivisors) := by
  rw [of]

/-- The algebra-level refinement of `TauCeti.FiniteDVRExtension.of_extensionField`: the extension
field of the package cut out by `P` is `L` itself as a `K`-algebra, not merely as a type. -/
theorem nonempty_algEquiv_of_extensionField (P : Ideal (_root_.integralClosure R L)) [P.IsPrime]
    [P.LiesOver (maximalIdeal R)] : Nonempty ((of R K L P).extensionField ≃ₐ[K] L) := by
  rw [of]
  exact ⟨AlgEquiv.refl⟩

/-- Every finite separable extension `L` of `K` underlies a `FiniteDVRExtension R K`: the integral
closure of `R` in `L` is integral over `R`, so going up produces a maximal ideal above the maximal
ideal of `R`, and any such ideal cuts out a package whose extension field is `L` as a
`K`-algebra. -/
theorem exists_algEquiv_extensionField :
    ∃ E : FiniteDVRExtension R K, Nonempty (E.extensionField ≃ₐ[K] L) := by
  have : FaithfulSMul K L :=
    (faithfulSMul_iff_algebraMap_injective K L).2 (algebraMap K L).injective
  have : FaithfulSMul R L := FaithfulSMul.trans R K L
  have : FaithfulSMul R (_root_.integralClosure R L) :=
    FaithfulSMul.tower_bot R (_root_.integralClosure R L) L
  obtain ⟨P, _, _⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := R) (S := _root_.integralClosure R L)
      (maximalIdeal R)
  exact ⟨of R K L P, nonempty_algEquiv_of_extensionField R K L P⟩

end Construction

/-- The trivial extension exists: `K` itself is a finite separable extension of `K`, and `R` is
already local, so `FiniteDVRExtension R K` is never empty. -/
instance : Nonempty (FiniteDVRExtension R K) :=
  ⟨(exists_algEquiv_extensionField R K K).choose⟩

end FiniteDVRExtension

end TauCeti
