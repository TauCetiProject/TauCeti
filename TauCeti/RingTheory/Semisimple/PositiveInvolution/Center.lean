/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.RingTheory.Semisimple.PositiveInvolution

import Mathlib.Algebra.Star.Center
import TauCeti.NumberTheory.NumberField.ComplexConjugation.PositiveInvolution

/-!
# The centre of a simple algebra with a positive involution

Let `B` be a simple `ℚ`-algebra, central and finite-dimensional over a number field `K`, with a
positive involution `x ↦ x*` (`TauCeti.PositiveInvolution B`). The involution preserves the centre
`K` of `B`, and since `K` is commutative it restricts to a field automorphism `σ` of `K` with
`σ² = id` (`TauCeti.PositiveInvolution.centerInvolution`). It is positive for the field trace:
`Trd_{B/ℚ}(c) = Tr_{K/ℚ}(Trd_{B/K}(c)) = deg_K B · Tr_{K/ℚ}(c)` for `c ∈ K`, so
`Tr_{K/ℚ}(x σ(x)) > 0` for every nonzero `x ∈ K`
(`TauCeti.PositiveInvolution.trace_mul_centerInvolution_pos`). By the classification of positive
involutions of number fields, `K` is totally real with `σ = id`, or `K` is a CM field and `σ` is
its complex conjugation (`TauCeti.PositiveInvolution.center_classification`); in either case the
fixed field `K₀` of `σ` is totally real (`TauCeti.PositiveInvolution.fixedCenter_totallyReal`).

## Main definitions

* `TauCeti.PositiveInvolution.centerInvolution`: the involution induced on the centre `K`.

## Main results

* `TauCeti.PositiveInvolution.algebraMap_centerInvolution`: `σ` is the restriction of `x ↦ x*`.
* `TauCeti.PositiveInvolution.centerInvolution_centerInvolution`: `σ² = id`.
* `TauCeti.PositiveInvolution.trace_mul_centerInvolution_pos`: `Tr_{K/ℚ}(x σ(x)) > 0` for
  `x ≠ 0`.
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
  (K : Type*) [Field K] [Algebra K B] [Algebra.IsCentral K B]

/-- The involution maps the image of `K` into itself. -/
theorem exists_algebraMap_eq_star (x : K) :
    letI := P.toStarRing
    ∃ y : K, algebraMap K B y = star (algebraMap K B x) := by
  let := P.toStarRing
  have hc : star (algebraMap K B x) ∈ Subalgebra.center K B :=
    Set.star_mem_center ((Subalgebra.center K B).algebraMap_mem x)
  obtain ⟨y, hy⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hc)
  exact ⟨y, hy⟩

variable [IsSimpleRing B]

/-- The **involution induced on the centre** `K` of `B`: `σ(x)` is the element of `K` with image
`(algebraMap K B x)*`. It is a ring endomorphism since `K` is commutative. -/
noncomputable def centerInvolution : K →+* K :=
  letI := P.toStarRing
  have hinj : Function.Injective (algebraMap K B) := (algebraMap K B).injective
  have hspec (x : K) : algebraMap K B (P.exists_algebraMap_eq_star K x).choose =
      star (algebraMap K B x) := (P.exists_algebraMap_eq_star K x).choose_spec
  { toFun x := (P.exists_algebraMap_eq_star K x).choose
    map_one' := hinj (by simp)
    map_mul' x y := hinj (by
      rw [hspec, map_mul, map_mul, star_mul, hspec, hspec, ← hspec x, ← hspec y, ← map_mul,
        ← map_mul, mul_comm])
    map_zero' := hinj (by simp)
    map_add' x y := hinj (by rw [hspec, map_add, map_add, star_add, hspec, hspec]) }

/-- The induced involution is the restriction of `x ↦ x*` to `K`. -/
@[simp]
theorem algebraMap_centerInvolution (x : K) :
    letI := P.toStarRing
    algebraMap K B (P.centerInvolution K x) = star (algebraMap K B x) :=
  (P.exists_algebraMap_eq_star K x).choose_spec

/-- The induced involution of `K` is an involution: `σ(σ(x)) = x`. -/
@[simp]
theorem centerInvolution_centerInvolution (x : K) :
    P.centerInvolution K (P.centerInvolution K x) = x := by
  let := P.toStarRing
  refine (algebraMap K B).injective ?_
  rw [algebraMap_centerInvolution, algebraMap_centerInvolution, star_star]

variable [NumberField K] [IsScalarTower ℚ K B] [FiniteDimensional K B]

/-- **The induced involution is positive for the field trace**: `Tr_{K/ℚ}(x σ(x)) > 0` for every
nonzero `x ∈ K`. On the centre, `Trd_{B/ℚ}(c) = deg_K B · Tr_{K/ℚ}(c)`. -/
theorem trace_mul_centerInvolution_pos {x : K} (hx : x ≠ 0) :
    0 < Algebra.trace ℚ K (x * P.centerInvolution K x) := by
  let := P.toStarRing
  have h := P.semisimpleReducedTrace_mul_star_pos (algebraMap K B x)
    ((map_ne_zero_iff _ (algebraMap K B).injective).mpr hx)
  rw [← algebraMap_centerInvolution, ← map_mul,
    Algebra.semisimpleReducedTrace_eq_trace_reducedTrace K, Algebra.reducedTrace_algebraMap,
    ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul] at h
  exact pos_of_mul_pos_right h (Nat.cast_nonneg _)

/-- **The centre of a simple algebra with a positive involution is totally real or CM**: either
`K` is totally real and the involution is the identity on `K`, or `K` is a CM field and the
involution is its complex conjugation. -/
theorem center_classification :
    (IsTotallyReal K ∧ P.centerInvolution K = RingHom.id K) ∨
      ∃ _ : IsCMField K, ∀ x, P.centerInvolution K x = IsCMField.complexConj K x :=
  NumberField.isTotallyReal_and_eq_id_or_isCMField_and_eq_complexConj_of_trace_mul_nonneg
    fun x ↦ by
      obtain rfl | hx := eq_or_ne x 0
      · simp
      · exact (P.trace_mul_centerInvolution_pos K hx).le

/-- **The fixed centre is totally real**: the subfield of `K` fixed by the involution is totally
real. -/
theorem fixedCenter_totallyReal :
    IsTotallyReal ((P.centerInvolution K).eqLocusField (RingHom.id K)) :=
  NumberField.isTotallyReal_eqLocusField_of_trace_mul_nonneg fun x ↦ by
    obtain rfl | hx := eq_or_ne x 0
    · simp
    · exact (P.trace_mul_centerInvolution_pos K hx).le

end TauCeti.PositiveInvolution
