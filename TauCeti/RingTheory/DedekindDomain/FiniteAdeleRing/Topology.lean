/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Units
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Maps.OpenQuotient
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# The discrete ideal quotients of the finite ideles

The fractional-ideal map on finite ideles is locally constant for the units topology:
its kernel is the open subgroup of everywhere-integral units. When the local integer
rings are compact, this kernel is also compact (in particular, for number fields).
In that case the fractional ideals form a discrete quotient of the finite ideles by
a compact open subgroup. The ideal class group is the further discrete quotient by
principal finite ideles.

This file supplies the topological part of the arithmetic dictionary established by
`IsDedekindDomain.FiniteAdeleRing.toFractionalIdeal` and `toClassGroup`. Local constancy
is stated without assigning a topology to either ideal carrier. The open-quotient
statements apply to any discrete topology on those carriers. For finite `S`, the file also
shows that the `S`-integral finite ideles `∏_{v ∈ S} K_vˣ × ∏_{v ∉ S} 𝒪_vˣ` carry the product
topology of the local unit groups.

For the arithmetic maps in `IsDedekindDomain.FiniteAdeleRing`, use:

* `TauCeti.isOpen_integralUnits` and `TauCeti.isCompact_integralUnits` for `integralUnits`;
* `TauCeti.isOpen_sIntegralUnits`, `TauCeti.isClosed_sIntegralUnits` and
  `IsDedekindDomain.FiniteAdeleRing.isEmbedding_coe_sIntegralUnits` for `sIntegralUnits`;
* `TauCeti.isLocallyConstant_toFractionalIdeal` and
  `TauCeti.isOpenQuotientMap_toFractionalIdeal` for `toFractionalIdeal`;
* `TauCeti.isLocallyConstant_toClassGroup` and `TauCeti.isOpenQuotientMap_toClassGroup`
  for `toClassGroup`.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §16.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open scoped nonZeroDivisors RestrictedProduct

namespace TauCeti

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The everywhere-integral finite ideles form an open subgroup in the units topology. -/
theorem isOpen_integralUnits : IsOpen (integralUnits R K : Set (FiniteAdeleRing R K)ˣ) := by
  rw [integralUnits_eq_units_integralAdeles]
  exact Submonoid.isOpen_units (isOpen_integralAdeles R K)

/-- If the local integer rings are compact, the everywhere-integral finite ideles form a
compact subgroup in the units topology. -/
theorem isCompact_integralUnits
    [∀ v : HeightOneSpectrum R, CompactSpace (v.adicCompletionIntegers K)] :
    IsCompact (integralUnits R K : Set (FiniteAdeleRing R K)ˣ) := by
  rw [integralUnits_eq_units_integralAdeles]
  exact Submonoid.units_isCompact (isCompact_integralAdeles (R := R) (K := K))

/-- The `S`-integral finite ideles form an open subgroup of the finite idele group. -/
theorem isOpen_sIntegralUnits (S : Set (HeightOneSpectrum R)) :
    IsOpen (sIntegralUnits R K S : Set (FiniteAdeleRing R K)ˣ) :=
  Subgroup.isOpen_mono (sIntegralUnits_mono R K (Set.empty_subset S))
    (sIntegralUnits_empty R K ▸ isOpen_integralUnits R K)

/-- The `S`-integral finite ideles form a closed subgroup of the finite idele group. -/
theorem isClosed_sIntegralUnits (S : Set (HeightOneSpectrum R)) :
    IsClosed (sIntegralUnits R K S : Set (FiniteAdeleRing R K)ˣ) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_sIntegralUnits R K S)

/-- The fractional ideal attached to a finite idele is locally constant, simultaneously
in all its prime multiplicities. -/
theorem isLocallyConstant_toFractionalIdeal :
    IsLocallyConstant (toFractionalIdeal (R := R) (K := K)) := by
  let : TopologicalSpace (FractionalIdeal R⁰ K)ˣ := ⊥
  let : DiscreteTopology (FractionalIdeal R⁰ K)ˣ := ⟨rfl⟩
  apply (IsLocallyConstant.iff_continuous _).mpr
  apply MonoidHom.continuous_of_isOpen_ker
  rw [ker_toFractionalIdeal]
  exact isOpen_integralUnits R K

/-- The ideal class attached to a finite idele is locally constant. -/
theorem isLocallyConstant_toClassGroup :
    IsLocallyConstant (toClassGroup R K) := by
  simpa only [Function.comp_def, ← toClassGroup_apply] using
    (isLocallyConstant_toFractionalIdeal R K).comp (ClassGroup.mk K)

/-- With the discrete topology on invertible fractional ideals, their canonical map from
finite ideles is an open quotient map, with kernel the everywhere-integral units. -/
theorem isOpenQuotientMap_toFractionalIdeal
    [TopologicalSpace (FractionalIdeal R⁰ K)ˣ] [DiscreteTopology (FractionalIdeal R⁰ K)ˣ] :
    IsOpenQuotientMap (toFractionalIdeal (R := R) (K := K)) :=
  ⟨toFractionalIdeal_surjective, (isLocallyConstant_toFractionalIdeal R K).continuous,
    fun _ _ ↦ isOpen_discrete _⟩

/-- With the discrete topology on the ideal class group, its canonical map from finite
ideles is an open quotient map. Its kernel is generated by the everywhere-integral units
and principal finite ideles. -/
theorem isOpenQuotientMap_toClassGroup
    [TopologicalSpace (ClassGroup R)] [DiscreteTopology (ClassGroup R)] :
    IsOpenQuotientMap (toClassGroup R K) :=
  ⟨toClassGroup_surjective, (isLocallyConstant_toClassGroup R K).continuous,
    fun _ _ ↦ isOpen_discrete _⟩

end TauCeti

namespace IsDedekindDomain.FiniteAdeleRing

open HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **For finite `S`, the `S`-integral finite ideles carry the product topology** of
`∏_{v ∈ S} K_vˣ × ∏_{v ∉ S} 𝒪_vˣ`: reading off the local units embeds them topologically into the
full product `∏_v K_vˣ` of the local unit groups. Finiteness of `S` cannot be dropped in general:
for `S = Set.univ` this would say that the units topology of the finite ideles is the product
topology. -/
theorem isEmbedding_coe_sIntegralUnits {S : Set (HeightOneSpectrum R)} (hS : S.Finite) :
    Topology.IsEmbedding fun x : sIntegralUnits R K S ↦ ⇑(unitsContinuousMulEquiv R K x) := by
  refine TauCeti.isEmbedding_restrictedProduct_coe_comp
    (Filter.le_principal_iff.mpr hS.compl_mem_cofinite)
    ((unitsContinuousMulEquiv R K).toHomeomorph.isEmbedding.comp
      Topology.IsEmbedding.subtypeVal) fun x v hv ↦ ?_
  -- outside `S` the component of an `S`-integral finite idele has valuation one, so it is a unit
  -- of the local integers
  refine adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr ?_
  rw [coe_unitsContinuousMulEquiv_apply]
  exact mem_sIntegralUnits_iff.mp x.2 v hv

end IsDedekindDomain.FiniteAdeleRing
