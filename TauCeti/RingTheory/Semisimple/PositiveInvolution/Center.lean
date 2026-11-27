/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.Algebra.Central.Star
public import TauCeti.RingTheory.Semisimple.PositiveInvolution

import TauCeti.NumberTheory.NumberField.ComplexConjugation.PositiveInvolution

/-!
# The centre of a simple algebra with a positive involution

Let `B` be a simple `ℚ`-algebra, central and finite-dimensional over a number field `K`, with a
positive involution `x ↦ x*` (`TauCeti.PositiveInvolution B`). The involution restricts to a field
automorphism `σ` of the centre `K` with `σ² = id` (`TauCeti.Algebra.centerInvolution K B`). It is
positive for the field trace: `Trd_{B/ℚ}(c) = deg_K B · Tr_{K/ℚ}(c)` for `c ∈ K`
(`TauCeti.Algebra.semisimpleReducedTrace_algebraMap`), so `Tr_{K/ℚ}(x σ(x)) > 0` for every
nonzero `x ∈ K` (`TauCeti.PositiveInvolution.trace_mul_centerInvolution_pos`). By the
classification of positive involutions of number fields, `K` is totally real with `σ = id`, or
`K` is a CM field and `σ` is its complex conjugation
(`TauCeti.PositiveInvolution.center_classification`); in either case the fixed field `K₀` of `σ`
is totally real (`TauCeti.PositiveInvolution.fixedCenter_totallyReal`).

## Main results

* `TauCeti.PositiveInvolution.trace_mul_centerInvolution_pos`: `Tr_{K/ℚ}(x σ(x)) > 0` for
  `x ≠ 0`.
* `TauCeti.PositiveInvolution.trace_mul_centerInvolution_nonneg`: `Tr_{K/ℚ}(x σ(x)) ≥ 0`.
* `TauCeti.PositiveInvolution.center_classification`: `K` is totally real and `σ = id`, or `K` is
  CM and `σ` is complex conjugation.
* `TauCeti.PositiveInvolution.fixedCenter_totallyReal`: the fixed field of `σ` is totally real.

## References

* J. S. Milne, *Introduction to Shimura varieties*, Proposition 8.10 and Definition 8.11.
* R. Kottwitz, *Points on some Shimura varieties over finite fields*, §5.
-/

public section

open NumberField

namespace TauCeti.PositiveInvolution

variable {B : Type*} [Ring B] [Algebra ℚ B] (P : PositiveInvolution B)
  (K : Type*) [Field K] [Algebra K B] [Algebra.IsCentral K B] [IsSimpleRing B] [NumberField K]
  [IsScalarTower ℚ K B] [FiniteDimensional K B]

/-- **The induced involution is positive for the field trace**: `Tr_{K/ℚ}(x σ(x)) > 0` for every
nonzero `x ∈ K`. On the centre, `Trd_{B/ℚ}(c) = deg_K B • Tr_{K/ℚ}(c)`. -/
theorem trace_mul_centerInvolution_pos {x : K} (hx : x ≠ 0) :
    letI := P.toStarRing
    0 < Algebra.trace ℚ K (x * Algebra.centerInvolution K B x) := by
  let := P.toStarRing
  have h := P.semisimpleReducedTrace_mul_star_pos (algebraMap K B x)
    ((map_ne_zero_iff _ (algebraMap K B).injective).mpr hx)
  rwa [← Algebra.algebraMap_centerInvolution, ← map_mul,
    Algebra.semisimpleReducedTrace_algebraMap K, nsmul_pos_iff (Algebra.deg_ne_zero K B)] at h

/-- `Tr_{K/ℚ}(x σ(x)) ≥ 0` for every `x ∈ K`. -/
theorem trace_mul_centerInvolution_nonneg (x : K) :
    letI := P.toStarRing
    0 ≤ Algebra.trace ℚ K (x * Algebra.centerInvolution K B x) := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · exact (P.trace_mul_centerInvolution_pos K hx).le

/-- **The centre of a simple algebra with a positive involution is totally real or CM**: either
`K` is totally real and the involution is the identity on `K`, or `K` is a CM field and the
involution is its complex conjugation. -/
theorem center_classification :
    letI := P.toStarRing
    (IsTotallyReal K ∧ Algebra.centerInvolution K B = RingHom.id K) ∨
      ∃ _ : IsCMField K, ∀ x, Algebra.centerInvolution K B x = IsCMField.complexConj K x :=
  NumberField.isTotallyReal_and_eq_id_or_isCMField_and_eq_complexConj_of_trace_mul_nonneg
    (P.trace_mul_centerInvolution_nonneg K)

/-- **The fixed centre is totally real**: the subfield of `K` fixed by the involution is totally
real. -/
theorem fixedCenter_totallyReal :
    letI := P.toStarRing
    IsTotallyReal ((Algebra.centerInvolution K B).eqLocusField (RingHom.id K)) :=
  NumberField.isTotallyReal_eqLocusField_of_trace_mul_nonneg
    (P.trace_mul_centerInvolution_nonneg K)

end TauCeti.PositiveInvolution
