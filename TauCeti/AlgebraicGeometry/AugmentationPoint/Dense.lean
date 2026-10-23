/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.AugmentationPoint.Basic
public import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Density of rational points over an algebraically closed field

The kernels of points of a finite-type algebra over an algebraically closed field are dense
in its prime spectrum, even when the algebra is nonreduced. This allows arguments on open
subsets of the spectrum to be tested on rational points.
-/

public section

namespace TauCeti

variable {k A : Type*} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- Rational points are dense in the spectrum of a finite-type algebra over an
algebraically closed field. -/
theorem denseRange_kernelPoint : DenseRange (AlgHom.kernelPoint (k := k) (H := A)) := by
  -- The augmentation API returns a scheme point; use its prime-spectrum carrier for the basis.
  change DenseRange (fun p : A →ₐ[k] k ↦ (AlgHom.kernelPoint p : PrimeSpectrum A))
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨x, hx⟩
  obtain ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, hxa, haU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx hU
  have ha : ¬ IsNilpotent a := by
    intro hn
    apply hxa
    exact x.isPrime.mem_of_pow_mem _ (hn.choose_spec ▸ x.asIdeal.zero_mem)
  obtain ⟨p, hp⟩ := exists_algHom_apply_ne_zero_of_not_isNilpotent (k := k) (A := A) (K := k) ha
  refine ⟨AlgHom.kernelPoint p, haU ?_, ⟨p, rfl⟩⟩
  apply (PrimeSpectrum.mem_basicOpen a (AlgHom.kernelPoint p)).mpr
  rwa [AlgHom.kernelPoint_asIdeal]

end TauCeti
