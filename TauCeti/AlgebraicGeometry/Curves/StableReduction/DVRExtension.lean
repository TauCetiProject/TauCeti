/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
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
* `TauCeti.FiniteDVRExtension.finite_primesOver`: only finitely many places lie over it, so the
  choice is a choice among finitely many.
* `TauCeti.FiniteDVRExtension.isLocalHom_algebraMap` and
  `TauCeti.FiniteDVRExtension.under_maximalIdeal_localRing`: the chosen local ring dominates `R`.
* `TauCeti.FiniteDVRExtension.exists_extensionField_eq`: every finite separable extension of `K`
  underlies such a package, one for each place above the closed point of `R`.
-/

public section

universe u

namespace TauCeti

open IsLocalRing

/-- A finite separable extension of the fraction field `K` of a discrete valuation ring `R`,
together with a chosen place of that extension above the closed point of `R`.

The place is recorded as a maximal ideal `prime` of the integral closure of `R` in the extension
field, lying over the maximal ideal of `R`, together with a ring `localRing` presented as the
localization there. See `TauCeti.FiniteDVRExtension.of` for the construction from such an ideal and
`TauCeti.FiniteDVRExtension.exists_extensionField_eq` for the fact that one always exists. -/
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

instance isIntegral_integralClosure : Algebra.IsIntegral R E.integralClosure :=
  IsIntegralClosure.isIntegral_algebra R E.extensionField

/-- The integral closure is a finite `R`-module, so it is semilocal: the places of `K'` above the
closed point of `R` are the finitely many maximal ideals of `C`, and there is more than one as soon
as the place of `R` does not extend uniquely. -/
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
theorem under_prime : E.prime.under R = maximalIdeal R :=
  (Ideal.over_def E.prime _).symm

/-- The chosen place is one of finitely many: the places of `K'` above the closed point of `R` are
the maximal ideals of the Dedekind domain `C` lying over it, and there are finitely many. -/
theorem finite_primesOver : ((maximalIdeal R).primesOver E.integralClosure).Finite :=
  IsDedekindDomain.primesOver_finite _ _

/-- The chosen place is a nonzero prime: it lies over the maximal ideal of `R`, which is nonzero
because a discrete valuation ring is not a field. -/
theorem prime_ne_bot : E.prime ≠ ⊥ :=
  Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field R) E.prime

instance isDomain_localRing : IsDomain E.localRing :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _ E.prime.primeCompl_le_nonZeroDivisors

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

instance faithfulSMul_localRing : FaithfulSMul R E.localRing := by
  rw [faithfulSMul_iff_algebraMap_injective,
    IsScalarTower.algebraMap_eq R E.integralClosure E.localRing]
  exact (IsLocalization.injective E.localRing E.prime.primeCompl_le_nonZeroDivisors).comp
    (FaithfulSMul.algebraMap_injective R E.integralClosure)

/-- The maximal ideal of the local ring of the chosen place contracts to the chosen place. -/
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
theorem under_maximalIdeal_localRing : (maximalIdeal E.localRing).under R = maximalIdeal R :=
  IsLocalRing.maximalIdeal_comap _

section Construction

variable (R K)
variable (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Algebra R L] [IsScalarTower R K L]

/-- The algebra structure on `Localization.AtPrime P`, for `P` a prime of the integral closure `C`
of `R` in `L`, given by mapping a fraction of integral elements to the corresponding element of
`L`. This is legitimate because a prime of a domain misses `0`, so the denominators become units.

This is a reducible non-instance in the sense of the note [reducible non-instances]: which algebra
structure a localization should carry towards a further ring is context-dependent. It is the value
taken by the `fractionAlgebra` field of `TauCeti.FiniteDVRExtension.of`. -/
noncomputable abbrev localizationAlgebra (P : Ideal (_root_.integralClosure R L)) [P.IsPrime] :
    Algebra (Localization.AtPrime P) L :=
  RingHom.toAlgebra <| IsLocalization.lift
    (M := P.primeCompl) (g := algebraMap (_root_.integralClosure R L) L) fun y ↦
      isUnit_iff_ne_zero.2 fun h ↦ y.2 <| by
        rw [show (y : _root_.integralClosure R L) = 0 from
          FaithfulSMul.algebraMap_injective (_root_.integralClosure R L) L (by simpa using h)]
        exact P.zero_mem

attribute [local instance] localizationAlgebra

instance isScalarTower_localizationAlgebra (P : Ideal (_root_.integralClosure R L)) [P.IsPrime] :
    IsScalarTower (_root_.integralClosure R L) (Localization.AtPrime P) L :=
  .of_algebraMap_eq fun x ↦ (IsLocalization.lift_eq _ x).symm

/-- The finite extension of the discrete valuation ring `R` cut out by a maximal ideal `P` of the
integral closure of `R` in a finite separable extension `L` of `K`, provided `P` lies above the
maximal ideal of `R`. Its local ring is `Localization.AtPrime P`. -/
@[expose]
noncomputable def of (P : Ideal (_root_.integralClosure R L)) [P.IsMaximal]
    [P.LiesOver (maximalIdeal R)] : FiniteDVRExtension R K where
  extensionField := L
  prime := P
  localRing := Localization.AtPrime P
  fractionAlgebra := localizationAlgebra R L P

@[simp]
theorem of_extensionField (P : Ideal (_root_.integralClosure R L)) [P.IsMaximal]
    [P.LiesOver (maximalIdeal R)] : (of R K L P).extensionField = L := rfl

@[simp]
theorem of_prime (P : Ideal (_root_.integralClosure R L)) [P.IsMaximal]
    [P.LiesOver (maximalIdeal R)] : (of R K L P).prime = P := rfl

@[simp]
theorem of_localRing (P : Ideal (_root_.integralClosure R L)) [P.IsMaximal]
    [P.LiesOver (maximalIdeal R)] : (of R K L P).localRing = Localization.AtPrime P := rfl

/-- Every finite separable extension `L` of `K` underlies a `FiniteDVRExtension R K`: the integral
closure of `R` in `L` is integral over `R`, so going up produces a maximal ideal above the maximal
ideal of `R`, and any such ideal cuts out a package with extension field `L`. -/
theorem exists_extensionField_eq : ∃ E : FiniteDVRExtension R K, E.extensionField = L := by
  have : FaithfulSMul K L :=
    (faithfulSMul_iff_algebraMap_injective K L).2 (algebraMap K L).injective
  have : FaithfulSMul R L := FaithfulSMul.trans R K L
  have : FaithfulSMul R (_root_.integralClosure R L) :=
    FaithfulSMul.tower_bot R (_root_.integralClosure R L) L
  obtain ⟨P, _, _⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := R) (S := _root_.integralClosure R L)
      (maximalIdeal R)
  exact ⟨of R K L P, rfl⟩

end Construction

/-- The trivial extension exists: `K` itself is a finite separable extension of `K`, and `R` is
already local, so `FiniteDVRExtension R K` is never empty. -/
instance : Nonempty (FiniteDVRExtension R K) :=
  ⟨(exists_extensionField_eq R K K).choose⟩

end FiniteDVRExtension

end TauCeti
