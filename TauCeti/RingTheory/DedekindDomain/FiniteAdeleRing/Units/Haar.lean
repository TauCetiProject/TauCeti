/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Constructions.Polish.Units
public import TauCeti.MeasureTheory.Measure.Haar.RestrictedProduct.Basic
public import TauCeti.NumberTheory.LocalField.Topology
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.BorelSpace
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Topology
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Units

/-!
# The normalized Haar measure on the finite ideles

Let `R` be a Dedekind domain with fraction field `K`, countably many places and finite residue
fields, for instance the ring of integers of a number field. The everywhere-integral finite ideles
`Ôˣ = ∏_v 𝒪_vˣ` (`IsDedekindDomain.FiniteAdeleRing.integralUnits`) are a compact open subgroup of
the finite idele group `𝔸ᶠˣ`, so there is exactly one Haar measure `d^×x_f` on `𝔸ᶠˣ` with
`d^×x_f(Ôˣ) = 1`, namely Mathlib's `MeasureTheory.Measure.haarMeasure` at `Ôˣ`. This file shows that
it is the restricted product of the local Haar measures `d^×x_v` on `K_vˣ` normalized by
`d^×x_v(𝒪_vˣ) = 1`, carried to `𝔸ᶠˣ` by the isomorphism of topological groups
`IsDedekindDomain.FiniteAdeleRing.unitsContinuousMulEquiv` between the finite ideles and the
restricted product of the `K_vˣ` with respect to the `𝒪_vˣ`. This is the finite part of the
normalized Haar measure on the ideles; it is the multiplicative counterpart of
`IsDedekindDomain.FiniteAdeleRing.addHaarMeasure_eq_restrictedAddHaar` for the finite adeles.

## Main definitions

* `IsDedekindDomain.FiniteAdeleRing.integralUnitsPositiveCompacts`: the everywhere-integral finite
  ideles `Ôˣ` as a compact set with nonempty interior, at which `haarMeasure` is normalized.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.isOpen_units_adicCompletionIntegers`: the local integral units
  `𝒪_vˣ` are open in `K_vˣ`.
* `IsDedekindDomain.FiniteAdeleRing.preimage_unitsContinuousMulEquiv_box`: under
  `unitsContinuousMulEquiv`, `Ôˣ` is the coordinate box with factors `𝒪_vˣ`.
* `IsDedekindDomain.FiniteAdeleRing.haarMeasure_integralUnits_eq_map_restrictedHaar`: the Haar
  measure on the finite ideles giving `Ôˣ` mass one is the restricted product of local Haar
  measures giving each `𝒪_vˣ` mass one.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. 1,
  2nd ed., Cambridge University Press (2023), Lemma 3.63 and the measure construction following
  it, pp. 188–189.
-/

public section
noncomputable section

open MeasureTheory Measure RestrictedProduct TauCeti
open scoped RestrictedProduct

namespace IsDedekindDomain.FiniteAdeleRing

open HeightOneSpectrum

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The local integral units `𝒪_vˣ` are open in the unit group `K_vˣ` of the completion. -/
theorem isOpen_units_adicCompletionIntegers (v : HeightOneSpectrum R) :
    IsOpen ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ) :=
  Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)

/-- The local integral units are open at every place, in the form in which the restricted
products of Haar measures (`TauCeti.restrictedHaar`) take this hypothesis. -/
instance instFactIsOpenUnitsAdicCompletionIntegers :
    Fact (∀ v : HeightOneSpectrum R, IsOpen
      ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ)) :=
  ⟨isOpen_units_adicCompletionIntegers R K⟩

/-- Under the isomorphism `unitsContinuousMulEquiv` of the finite ideles with the restricted
product of the `K_vˣ`, the everywhere-integral finite ideles are the preimage of the coordinate
box with factors the local integral units `𝒪_vˣ`. -/
theorem preimage_unitsContinuousMulEquiv_box :
    unitsContinuousMulEquiv R K ⁻¹' box (fun v : HeightOneSpectrum R ↦
        ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ)) =
      integralUnits R K := by
  ext x
  simp only [Set.mem_preimage, mem_box, SetLike.mem_coe, Submonoid.mem_units_iff,
    mem_integralUnits_iff_forall_mem_adicCompletionIntegers]
  refine forall_congr' fun v ↦ ?_
  rw [← RestrictedProduct.inv_apply, ← map_inv, coe_unitsContinuousMulEquiv_apply,
    coe_unitsContinuousMulEquiv_apply]
  -- The two sides read the coordinates of `x` and `x⁻¹` through the coercions of
  -- `FiniteAdeleRing R K` and of the underlying restricted product, which agree by definition.
  rfl

section PositiveCompacts

variable [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]

/-- The everywhere-integral finite ideles `Ôˣ = ∏_v 𝒪_vˣ`, as a compact set with nonempty interior:
they form a compact open subgroup of the finite ideles. Mathlib's
`MeasureTheory.Measure.haarMeasure` at this set is the Haar measure on the finite ideles giving
`Ôˣ` mass one. -/
def integralUnitsPositiveCompacts : TopologicalSpace.PositiveCompacts 𝔸ᶠ[R, K]ˣ where
  carrier := integralUnits R K
  isCompact' := isCompact_integralUnits R K
  interior_nonempty' := ⟨1, by
    rw [(isOpen_integralUnits R K).interior_eq]
    exact one_mem _⟩

/-- The compact set `integralUnitsPositiveCompacts R K` is the set of everywhere-integral finite
ideles. -/
@[simp]
theorem coe_integralUnitsPositiveCompacts :
    (integralUnitsPositiveCompacts R K : Set 𝔸ᶠ[R, K]ˣ) = integralUnits R K :=
  (rfl)

end PositiveCompacts

variable [Countable (HeightOneSpectrum R)] [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]
  [∀ v : HeightOneSpectrum R, MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum R, BorelSpace (v.adicCompletion K)]

/-- **The normalized Haar measure on the finite ideles is a restricted product.** The Haar measure
on the finite ideles giving the everywhere-integral finite ideles `Ôˣ` mass one is the restricted
product of local Haar measures `μ v` on `K_vˣ` with `μ v 𝒪_vˣ = 1`, carried to the finite ideles
by `unitsContinuousMulEquiv`. -/
theorem haarMeasure_integralUnits_eq_map_restrictedHaar
    (μ : ∀ v : HeightOneSpectrum R, Measure (v.adicCompletion K)ˣ) [∀ v, (μ v).IsHaarMeasure]
    (hμ : ∀ v, μ v (Submonoid.ofClass (v.adicCompletionIntegers K)).units = 1) :
    haarMeasure (integralUnitsPositiveCompacts R K) =
      (restrictedHaar (fun v : HeightOneSpectrum R ↦
        (Submonoid.ofClass (v.adicCompletionIntegers K)).units) μ (.of_forall hμ)).map
          (unitsContinuousMulEquiv R K).symm := by
  refine (haarMeasure_eq_iff (integralUnitsPositiveCompacts R K) _).2 ?_
  rw [coe_integralUnitsPositiveCompacts,
    map_apply (map_continuous (unitsContinuousMulEquiv R K).symm).measurable
      (isOpen_integralUnits R K).measurableSet, ← preimage_unitsContinuousMulEquiv_box,
    ← Set.preimage_comp]
  simp [hμ]

end IsDedekindDomain.FiniteAdeleRing
