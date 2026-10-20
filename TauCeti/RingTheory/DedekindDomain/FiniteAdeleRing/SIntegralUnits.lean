/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Units


/-!
# The topology of the `S`-integral finite ideles

Let `R` be a Dedekind domain with fraction field `K`, and let `S` be a set of height one primes of
`R`. The finite ideles that are units of the local integers at every place outside `S` form the
subgroup `IsDedekindDomain.FiniteAdeleRing.sIntegralUnits R K S`

`∏_{v ∈ S} K_vˣ × ∏_{v ∉ S} 𝒪_vˣ`

of the finite ideles `𝔸ᶠ[R, K]ˣ`, the **`S`-integral finite ideles**, defined in
`TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup`, where their algebraic structure
(the restricted-product condition, their principal elements and their ideal classes) is developed.
This file shows that for finite `S` their subspace topology is the product topology of the local
unit groups.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.isEmbedding_coe_sIntegralUnits`: the topology of the
  `S`-integral finite ideles for finite `S`.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §16.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct

namespace IsDedekindDomain.FiniteAdeleRing

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
  -- outside `S` the component of an `S`-integral finite idele has valuation one, so it and its
  -- inverse are local integers
  have h : Valued.v (((x : 𝔸ᶠ[R, K]ˣ) : 𝔸ᶠ[R, K]) v) = 1 := mem_sIntegralUnits_iff.mp x.2 v hv
  simp only [SetLike.mem_coe, Submonoid.mem_units_iff, Units.val_inv_eq_inv_val,
    coe_unitsContinuousMulEquiv_apply]
  simp [Submonoid.ofClass, mem_adicCompletionIntegers, h]

end IsDedekindDomain.FiniteAdeleRing
