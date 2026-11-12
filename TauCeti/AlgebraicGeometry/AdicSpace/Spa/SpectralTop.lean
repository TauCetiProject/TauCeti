/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap
public import TauCeti.RingTheory.Huber.TateGauge.Spectral.Topology
import TauCeti.RingTheory.Huber.TateGauge.Spectral.Valuation

/-!
# The adic spectrum of the spectral topology

Let `A` be a Tate ring and `A_sp = SpectralTop A` the ring `A` with its spectral topology, which
is coarser than the topology of `A`. A valuation is continuous for the topology of `A` exactly
when it is continuous for the spectral topology
(`TauCeti.Huber.SpectralTop.valuation_isContinuous_iff`). This file draws the consequences for
valuation spectra: `Cont(A_sp) = Cont(A)`, and for every subring `A⁺` of `A`, the adic spectra
`Spa(A_sp, A⁺)` and `Spa(A, A⁺)` agree, and so do their rational subsets `R(T/s)`.

Points of `Spv A_sp` are compared with points of `Spv A` by pullback along the ring isomorphism
`toSpectralTop A : A ≃+* A_sp`; this is a bijection, and its inverse is pullback along the
(in general discontinuous) inverse isomorphism, which is still continuous on valuation spectra.

## Main results

* `TauCeti.Huber.SpectralTop.isContinuous_iff`, `TauCeti.Huber.SpectralTop.comap_preimage_cont`:
  `Cont(A_sp) = Cont(A)`.
* `Subring.comap_toSpectralTop_preimage_spa`: `Spa(A_sp, A⁺) = Spa(A, A⁺)`.
* `Subring.isHomeomorph_spaComap_toSpectralTop`: the pullback map `Spa(A_sp, A⁺) → Spa(A, A⁺)` is
  a homeomorphism.
* `Subring.comap_toSpectralTop_preimage_rationalSubset`: the rational subsets `R(T/s)` of the two
  adic spectra agree.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Definition 2.8.13.
* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Theorem 7.10.
-/

public section

open Topology TauCeti.ValuationSpectrum

namespace TauCeti.Huber.SpectralTop

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]

/-- **`Cont(A_sp) = Cont(A)`, pointwise.** A point of `Spv (SpectralTop A)` is continuous exactly
when its pullback to `Spv A` is. -/
theorem isContinuous_iff (v : Spv (SpectralTop A)) :
    v.IsContinuous ↔ (comap (toSpectralTop A : A →+* SpectralTop A) v).IsContinuous := by
  conv_rhs => rw [← ofValuation_valuation v, comap_ofValuation, isContinuous_ofValuation_iff]
  exact (isContinuous_def v).trans valuation_isContinuous_iff

/-- **`Cont(A_sp) = Cont(A)`.** Pulling back along `toSpectralTop A`, the continuous points of
`Spv A` are exactly the continuous points of `Spv (SpectralTop A)`. -/
theorem comap_preimage_cont :
    comap (toSpectralTop A : A →+* SpectralTop A) ⁻¹' cont A = cont (SpectralTop A) :=
  Set.ext fun v ↦ by rw [Set.mem_preimage, mem_cont_iff, mem_cont_iff, isContinuous_iff]

omit [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A] in
/-- Pulling back along `toSpectralTop A` undoes pulling back along its inverse. -/
private theorem comap_comap_symm (v : Spv A) :
    comap (toSpectralTop A : A →+* SpectralTop A)
      (comap ((toSpectralTop A).symm : SpectralTop A →+* A) v) = v := by
  rw [← Function.comp_apply (f := comap _), ← comap_comp]
  simp

omit [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A] in
/-- Pulling back along the inverse of `toSpectralTop A` undoes pulling back along it. -/
private theorem comap_symm_comap (v : Spv (SpectralTop A)) :
    comap ((toSpectralTop A).symm : SpectralTop A →+* A)
      (comap (toSpectralTop A : A →+* SpectralTop A) v) = v := by
  rw [← Function.comp_apply (f := comap _), ← comap_comp]
  simp

end TauCeti.Huber.SpectralTop

namespace Subring

open TauCeti TauCeti.Huber TauCeti.Huber.SpectralTop

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]

/-- **`Spa(A_sp, A⁺) = Spa(A, A⁺)`.** For every subring `A⁺` of `A`, pulling back along
`toSpectralTop A` identifies the adic spectrum of `A` with that of `SpectralTop A` for the image
of `A⁺`. -/
theorem comap_toSpectralTop_preimage_spa (Aplus : Subring A) :
    ValuationSpectrum.comap (toSpectralTop A : A →+* SpectralTop A) ⁻¹' spa Aplus =
      spa (Aplus.map (toSpectralTop A : A →+* SpectralTop A)) := by
  ext v
  rw [Set.mem_preimage]
  by_cases hv : v.IsContinuous
  · exact (mem_spa_map_iff continuous_toSpectralTop Aplus hv).symm
  · rw [mem_spa_iff, mem_spa_iff, ← isContinuous_iff]
    simp [hv, -isContinuous_def]

/-- **The adic spectra of `A` and `A_sp` are homeomorphic.** For every subring `A⁺` of `A`, the
pullback `Spa(A_sp, A⁺) → Spa(A, A⁺)` along the continuous identity `A → A_sp` is a
homeomorphism. Its inverse is pullback along the inverse ring isomorphism, which need not be
continuous for the topologies on the rings. -/
theorem isHomeomorph_spaComap_toSpectralTop (Aplus : Subring A) :
    IsHomeomorph (spaComap (toSpectralTop A : A →+* SpectralTop A)
      (continuous_toSpectralTop : Continuous (toSpectralTop A : A →+* SpectralTop A)) Aplus
      (Aplus.map (toSpectralTop A : A →+* SpectralTop A))
      fun _ ha ↦ Subring.mem_map.mpr ⟨_, ha, rfl⟩) := by
  have hcont : Continuous (toSpectralTop A : A →+* SpectralTop A) := continuous_toSpectralTop
  let e : SpectralTop A →+* A := (toSpectralTop A).symm
  have he (v : Spv A) (hv : v ∈ spa Aplus) :
      ValuationSpectrum.comap e v ∈ spa (Aplus.map (toSpectralTop A : A →+* SpectralTop A)) := by
    rw [← comap_toSpectralTop_preimage_spa, Set.mem_preimage, comap_comap_symm]
    exact hv
  refine Homeomorph.isHomeomorph
    { toFun := spaComap _ hcont Aplus _ fun _ ha ↦ Subring.mem_map.mpr ⟨_, ha, rfl⟩
      invFun v := ⟨ValuationSpectrum.comap e v.1, he v.1 v.2⟩
      left_inv v := Subtype.ext ?_
      right_inv v := Subtype.ext ?_
      continuous_toFun := continuous_spaComap ..
      continuous_invFun := continuous_induced_rng.mpr
        ((continuous_comap e).comp continuous_subtype_val) }
  · simp only [spaComap_val]
    exact comap_symm_comap v.1
  · rw [spaComap_val]
    exact comap_comap_symm v.1

open scoped Classical in
/-- **The rational subsets of `Spa(A_sp, A⁺)` and `Spa(A, A⁺)` agree.** Pulling back along
`toSpectralTop A`, the rational subset `R(T/s)` of `Spa(A, A⁺)` is the rational subset of
`Spa(A_sp, A⁺)` presented by the same numerators and denominator. -/
theorem comap_toSpectralTop_preimage_rationalSubset (Aplus : Subring A) (T : Finset A) (s : A) :
    ValuationSpectrum.comap (toSpectralTop A : A →+* SpectralTop A) ⁻¹'
        rationalSubset Aplus T s =
      rationalSubset (Aplus.map (toSpectralTop A : A →+* SpectralTop A))
        (T.image (toSpectralTop A)) (toSpectralTop A s) := by
  have hcont : Continuous (toSpectralTop A : A →+* SpectralTop A) := continuous_toSpectralTop
  have h := comap_preimage_rationalSubset_inter_spa _ hcont (Aplus := Aplus)
    (fun _ ha ↦ Subring.mem_map.mpr ⟨_, ha, rfl⟩) T s
  rw [← comap_toSpectralTop_preimage_spa, ← Set.preimage_inter,
    Set.inter_eq_left.mpr (rationalSubset_subset_spa Aplus T s)] at h
  simpa only [RingEquiv.coe_toRingHom] using h

end Subring
