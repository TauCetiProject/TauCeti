/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import TauCeti.Algebra.Star.Projection.Dilation

/-!
# Positive contractions as compressions of projections

Let `q` be a star projection in a unital C⋆-algebra, and let `u` satisfy `star u * u = q` and
`q * u = 0`, so that `u` carries `q` to an orthogonal copy of itself. Then every positive
contraction `a` has the same compression to `q` as some star projection `p`:
`q * p * q = q * a * q`. With `c = q * a * q`, the projection is the projection dilation
`TauCeti.projectionDilation q u c (CFC.sqrt (c - c * c))`, the block operator
`[[c, √(c - c²)], [√(c - c²), q - c]]` relative to `q` and `u * star u`.

On `B(H)` with `q` the projection onto a finite-dimensional subspace this produces, for every
positive contraction, projections with prescribed matrix coefficients on that subspace. This
identifies the positive contractions with the weak operator closure of the projections on an
infinite-dimensional Hilbert space.

## Main statements

* `IsStarProjection.exists_isStarProjection_mul_mul_eq`: a positive contraction has the same
  compression to `q` as some star projection.
-/

public section

open TauCeti

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Let `q` be a star projection and `u` satisfy `star u * u = q` and `q * u = 0`. Then every
positive contraction `a` has the same compression to `q` as a star projection `p`:
`q * p * q = q * a * q`. -/
theorem IsStarProjection.exists_isStarProjection_mul_mul_eq {q u a : A} (hq : IsStarProjection q)
    (hu : star u * u = q) (hqu : q * u = 0) (ha : a ∈ Set.Icc 0 1) :
    ∃ p : A, IsStarProjection p ∧ q * p * q = q * a * q := by
  have hqq : q * q = q := hq.isIdempotentElem.eq
  have hqs : star q = q := hq.isSelfAdjoint.star_eq
  have hc : q * a * q ∈ Set.Icc 0 1 := by
    refine ⟨by simpa [hqs] using star_left_conjugate_nonneg ha.1 q, ?_⟩
    calc q * a * q = star q * a * q := by rw [hqs]
      _ ≤ star q * 1 * q := star_left_conjugate_le_conjugate ha.2 q
      _ = q := by rw [hqs, mul_one, hqq]
      _ ≤ 1 := hq.le_one
  have hcq : q * a * q * q = q * a * q := by rw [mul_assoc, hqq]
  have hqc : q * (q * a * q) = q * a * q := by rw [← mul_assoc, ← mul_assoc, hqq]
  generalize q * a * q = c at hc hcq hqc ⊢
  have hcc : 0 ≤ c - c * c := sub_nonneg.mpr (CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one
    hc.1 ((CStarAlgebra.norm_le_one_iff_of_nonneg c hc.1).mpr hc.2))
  have hd : IsSelfAdjoint (CFC.sqrt (c - c * c)) := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hdd : CFC.sqrt (c - c * c) * CFC.sqrt (c - c * c) = c - c * c :=
    CFC.sqrt_mul_sqrt_self _ hcc
  have hcd : Commute c (CFC.sqrt (c - c * c)) := by
    rw [CFC.sqrt_eq_cfc]
    have h : Commute (c - c * c) c := (Commute.refl c).sub_left ((Commute.refl c).mul_left
      (Commute.refl c))
    exact (h.cfc_nnreal NNReal.sqrt).symm
  generalize CFC.sqrt (c - c * c) = d at hd hdd hcd
  -- `d` vanishes off `q`: the element `x = d * (1 - q)` has `star x * x = 0`.
  have hdq : d * q = d := by
    have hc1q : c * (1 - q) = 0 := by rw [mul_sub, mul_one, hcq, sub_self]
    have hcc1q : (c - c * c) * (1 - q) = 0 := by
      rw [sub_mul, mul_assoc, hc1q, mul_zero, sub_zero]
    have hx : star (d * (1 - q)) * (d * (1 - q)) = 0 := by
      calc star (d * (1 - q)) * (d * (1 - q)) = (1 - q) * ((d * d) * (1 - q)) := by
            rw [star_mul, star_sub, star_one, hqs, hd.star_eq]; noncomm_ring
        _ = 0 := by rw [hdd, hcc1q, mul_zero]
    have := star_mul_self_eq_zero.mp hx
    rwa [mul_sub, mul_one, sub_eq_zero, eq_comm] at this
  refine ⟨projectionDilation q u c d,
    isStarProjection_projectionDilation hq hu hqu (IsSelfAdjoint.of_nonneg hc.1) hcq hd hdq hcd
      hdd, ?_⟩
  rw [mul_projectionDilation_mul hq.isSelfAdjoint hqu, hqc, hcq]
