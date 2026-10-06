/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Krull dimension and heights under quotients

For an ideal `I` of a commutative ring `R`, the quotient map `R → R ⧸ I` identifies
`Spec (R ⧸ I)` homeomorphically with the closed subset `V(I)` of `Spec R`. So the topological Krull
dimension of `V(I)` is the Krull dimension of `R ⧸ I`.
Quotienting by the nilradical preserves the entire prime spectrum, hence its Krull dimension and
the height of each prime ideal.

## Main results

* `Ideal.topologicalKrullDim_zeroLocus`: the closed subset `V(I)` of `Spec R` has the Krull
  dimension of `R ⧸ I`.
* `TauCeti.ringKrullDim_quotient_nilradical`: reduction preserves Krull dimension.
* `Ideal.height_map_quotientMk_nilradical`: reduction preserves the height of a prime ideal.
-/

public section

namespace Ideal

open PrimeSpectrum

variable {R : Type*} [CommRing R]

/-- The closed subset `V(I)` of `Spec R` has the Krull dimension of `R ⧸ I`. -/
@[simp]
theorem topologicalKrullDim_zeroLocus (I : Ideal R) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set R)) = ringKrullDim (R ⧸ I) := by
  have hi := isClosedEmbedding_comap_of_surjective _ _ (Quotient.mk_surjective (I := I))
  have hrange :
      Set.range (PrimeSpectrum.comap (Quotient.mk I)) = PrimeSpectrum.zeroLocus (I : Set R) := by
    rw [range_comap_of_surjective _ _ Quotient.mk_surjective, mk_ker]
  rw [← topologicalKrullDim_eq_ringKrullDim]
  exact ((hi.isEmbedding.toHomeomorph).trans (Homeomorph.setCongr hrange)).symm.isHomeomorph
    |>.topologicalKrullDim_eq

end Ideal

namespace TauCeti

variable (R : Type*) [CommRing R]

/-- Passing to the quotient by the nilradical preserves Krull dimension. -/
@[simp]
theorem ringKrullDim_quotient_nilradical :
    ringKrullDim (R ⧸ nilradical R) = ringKrullDim R := by
  rw [ringKrullDim_quotient, PrimeSpectrum.zeroLocus_nilradical, ringKrullDim]
  exact Order.krullDim_eq_of_orderIso OrderIso.Set.univ

end TauCeti

namespace Ideal

variable {R : Type*} [CommRing R]

/-- Passing to the quotient by the nilradical preserves the height of a prime ideal. -/
@[simp]
theorem height_map_quotientMk_nilradical (p : Ideal R) [p.IsPrime] :
    (p.map (Ideal.Quotient.mk (nilradical R))).height = p.height := by
  let I : Ideal R := nilradical R
  let e : PrimeSpectrum (R ⧸ I) ≃o PrimeSpectrum R :=
    (I.primeSpectrumQuotientOrderIsoZeroLocus).trans
      ((Set.orderIsoOfEq _ _ PrimeSpectrum.zeroLocus_nilradical).trans OrderIso.Set.univ)
  have hIp : I ≤ p := nilradical_le_prime p
  let q : Ideal (R ⧸ I) := p.map (Ideal.Quotient.mk I)
  have : q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa [Ideal.mk_ker] using hIp)
  have he : e ⟨q, inferInstance⟩ = (⟨p, inferInstance⟩ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    -- The composite `e` is definitionally contraction by `Quotient.mk I` on underlying ideals.
    -- Mathlib provides no apply lemma for this composite of the quotient-spectrum equivalence,
    -- `Set.orderIsoOfEq`, and `OrderIso.Set.univ`.
    change (p.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = p
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_of_le_left hIp
  calc
    q.height = Order.height (⟨q, inferInstance⟩ : PrimeSpectrum (R ⧸ I)) :=
      PrimeSpectrum.height_eq_orderHeight (⟨q, inferInstance⟩ : PrimeSpectrum (R ⧸ I))
    _ = Order.height (⟨p, inferInstance⟩ : PrimeSpectrum R) := by
      rw [← he, Order.height_orderIso]
    _ = p.height :=
      (PrimeSpectrum.height_eq_orderHeight (⟨p, inferInstance⟩ : PrimeSpectrum R)).symm

end Ideal
