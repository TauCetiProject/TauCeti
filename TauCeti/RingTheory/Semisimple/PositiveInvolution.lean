/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Basic
public import TauCeti.RingTheory.CentralIdempotent
public import TauCeti.RingTheory.Semisimple.Star.Isotypic
public import TauCeti.RingTheory.Semisimple.Trace.Reduced

import Mathlib.Algebra.Star.Center
import TauCeti.RingTheory.Semisimple.Star.Basic

/-!
# Positive involutions

Let `B` be a finite-dimensional semisimple `ℚ`-algebra. An *involution* of `B` is an additive map
`x ↦ x*` with `(x y)* = y* x*` and `x** = x`; it is automatically `ℚ`-linear. It is *positive* if
`Trd_{B/ℚ}(x x*) > 0` for every nonzero `x ∈ B`, where `Trd_{B/ℚ}` is the reduced trace
`TauCeti.Algebra.semisimpleReducedTrace ℚ B`: the sum over the simple factors `B_i` of `B`, with
centres `F_i`, of `Tr_{F_i/ℚ}` composed with the reduced trace of `B_i` over `F_i`. The Rosati
involution of a polarized abelian variety is positive, and a semisimple `ℚ`-algebra with a positive
involution is the starting point of PEL data.

The definition makes sense for any `ℚ`-algebra; it is the classical notion when `B` is
finite-dimensional and semisimple.

## Main definitions

* `TauCeti.PositiveInvolution B`: a `StarRing` structure on the `ℚ`-algebra `B` with
  `Trd_{B/ℚ}(x x*) > 0` for `x ≠ 0`.
* `TauCeti.PositiveInvolution.ofStarRing`: a `StarRing` structure satisfying the positivity
  inequality is a positive involution; this is the constructor, and
  `TauCeti.PositiveInvolution.toStarRing` recovers the `StarRing` structure.

## Main results

* `TauCeti.PositiveInvolution.semisimpleReducedTrace_mul_star_pos`: the defining inequality
  `Trd(x x*) > 0`.
* `TauCeti.PositiveInvolution.semisimpleReducedTrace_star_mul_pos`: also `Trd(x* x) > 0` for
  `x ≠ 0`.
* `TauCeti.PositiveInvolution.semisimpleReducedTrace_mul_star_eq_zero`,
  `TauCeti.PositiveInvolution.semisimpleReducedTrace_star_mul_eq_zero`: `Trd(x x*)` and `Trd(x* x)`
  vanish only at `x = 0`.
* `TauCeti.PositiveInvolution.isProperStar`: a positive involution is proper.
* `TauCeti.PositiveInvolution.center_stable`: a positive involution preserves the centre.
* `TauCeti.PositiveInvolution.centralIdempotent_fixed`: it fixes every central idempotent.
* `TauCeti.forall_pos_semisimpleReducedTrace_mul_star_iff_forall_pos_trace`: on a
  finite-dimensional algebra over an ordered field `F`, an involution has `Trd_{B/F}(x x*) > 0` for
  all `x ≠ 0` exactly when it has `Tr_{B/F}(L_{x x*}) > 0` for all `x ≠ 0`; the regular trace is a
  positive multiple of `Trd` on each simple factor.
* `TauCeti.PositiveInvolution.iff_trace_pos`: the case `F = ℚ`, so an involution of a
  finite-dimensional `ℚ`-algebra is positive for the reduced trace `Trd_{B/ℚ}` exactly when it is
  positive for the regular trace `Tr_{B/ℚ}(L_x)`.
* `TauCeti.PositiveInvolution.trace_mulLeft_mul_star_pos`: `Tr_{B/ℚ}(L_{x x*}) > 0` for `x ≠ 0`;
  `TauCeti.PositiveInvolution.ofTracePos` is the converse constructor, and
  `TauCeti.PositiveInvolution.toStarRing_ofTracePos` says its involution is the given `StarRing`
  structure.

## Implementation notes

A positive involution bundles its `StarRing` structure, so Mathlib's `star` API applies to it
under `letI := P.toStarRing`. For instance `star_rat_smul` says that the involution is
`ℚ`-linear, and `starAddEquiv` and `starLinearEquiv ℚ` are the involution as an equivalence.

## References

* J. S. Milne, *Introduction to Shimura varieties*, Proposition 8.10 and Definition 8.11.
* K.-W. Lan, *Arithmetic compactifications of PEL-type Shimura varieties*, §1.2.1.
* R. Kottwitz, *Points on some Shimura varieties over finite fields*, §5.
-/

public section

namespace TauCeti

section TracePos

variable {F R : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [Ring R] [Algebra F R]
  [FiniteDimensional F R] [StarRing R]

/-- **Positivity for the reduced trace is positivity for the regular trace.** On a
finite-dimensional algebra over an ordered field `F`, an involution has `Trd_{R/F}(x x*) > 0` for
every `x ≠ 0` exactly when it has `Tr_{R/F}(L_{x x*}) > 0` for every `x ≠ 0`: either condition
makes the involution proper, hence `R` semisimple and `x x*` split along the simple factors, and on
a simple factor the two traces have the same sign. -/
theorem forall_pos_semisimpleReducedTrace_mul_star_iff_forall_pos_trace :
    (∀ x : R, x ≠ 0 → 0 < Algebra.semisimpleReducedTrace F R (x * star x)) ↔
      ∀ x : R, x ≠ 0 → 0 < LinearMap.trace F R (LinearMap.mulLeft F (x * star x)) := by
  -- The regular trace `a ↦ Tr_{R/F}(L_a)`, as an additive map.
  let τ := ((LinearMap.trace F R).comp (Algebra.lmul F R).toLinearMap).toAddMonoidHom
  have hτ (a : R) : τ a = LinearMap.trace F R (LinearMap.mulLeft F a) := by
    simp only [τ, LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, Algebra.coe_lmul_eq_mul]
    -- `LinearMap.mul F R a` is left multiplication by `a`.
    exact congrArg _ (LinearMap.ext fun b ↦ (LinearMap.mul_apply' a b).trans
      (LinearMap.mulLeft_apply F a b).symm)
  let Trd := (Algebra.semisimpleReducedTrace F R).toAddMonoidHom
  -- A finite-dimensional algebra with a proper involution is semisimple.
  have hss (_ : IsProperStar R) : IsSemisimpleRing R :=
    have := IsArtinianRing.of_finite F R
    isSemisimpleRing_of_isProperStar R
  have hsign [IsSemisimpleRing R] (c : Ideal R) (hc : c ∈ isotypicComponents R R) (y : R)
      (hy : y ∈ c) : 0 < τ (y * star y) ↔ 0 < Trd (y * star y) := by
    have := isTwoSided_of_mem_isotypicComponents hc
    exact Algebra.trace_mulLeft_pos_iff_semisimpleReducedTrace_pos hc
      (Ideal.mul_mem_right (star y) c hy)
  simp only [← hτ]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := hss (isProperStar_of_forall_pos_mul_star Trd h)
    exact forall_pos_mul_star_of_isotypicComponents Trd τ h fun c hc y hy ↦ (hsign c hc y hy).mpr
  · have := hss (isProperStar_of_forall_pos_mul_star τ h)
    exact forall_pos_mul_star_of_isotypicComponents τ Trd h fun c hc y hy ↦ (hsign c hc y hy).mp

end TracePos

variable (B : Type*) [Ring B] [Algebra ℚ B]

/-- A **positive involution** of a `ℚ`-algebra `B`: a `StarRing` structure `x ↦ x*` on `B` (so
`(x y)* = y* x*` and `x** = x`) such that the reduced trace `Trd_{B/ℚ}(x x*)` is positive for every
nonzero `x`. For `B` finite-dimensional and semisimple this is the positivity of the involution in
the sense of PEL data. -/
structure PositiveInvolution where
  /-- **A `StarRing` structure satisfying the positivity inequality is a positive involution.** -/
  ofStarRing ::
  /-- The involution `x ↦ x*`, as a `StarRing` structure on `B`. -/
  [toStarRing : StarRing B]
  /-- **Positivity**: `Trd_{B/ℚ}(x x*) > 0` for every nonzero `x`. -/
  semisimpleReducedTrace_mul_star_pos (x : B) (hx : x ≠ 0) :
    0 < Algebra.semisimpleReducedTrace ℚ B (x * star x)

namespace PositiveInvolution

variable {B}

/-- Two positive involutions with the same underlying map are equal. -/
@[ext]
theorem ext {P Q : PositiveInvolution B}
    (h : ∀ x, P.toStarRing.star x = Q.toStarRing.star x) : P = Q := by
  obtain @⟨@⟨@⟨@⟨⟨p⟩, _⟩, _⟩, _⟩, _⟩ := P
  obtain @⟨@⟨@⟨@⟨⟨q⟩, _⟩, _⟩, _⟩, _⟩ := Q
  obtain rfl : p = q := funext h
  rfl

variable (P : PositiveInvolution B)

/-- **Positivity of `x* x`.** For a positive involution, also `Trd_{B/ℚ}(x* x) > 0` for every
nonzero `x`. -/
theorem semisimpleReducedTrace_star_mul_pos {x : B} (hx : x ≠ 0) :
    letI := P.toStarRing
    0 < Algebra.semisimpleReducedTrace ℚ B (star x * x) := by
  let := P.toStarRing
  simpa using P.semisimpleReducedTrace_mul_star_pos (star x) (star_ne_zero.2 hx)

/-- `Trd_{B/ℚ}(x x*) ≥ 0` for every `x`. -/
theorem semisimpleReducedTrace_mul_star_nonneg (x : B) :
    letI := P.toStarRing
    0 ≤ Algebra.semisimpleReducedTrace ℚ B (x * star x) := by
  let := P.toStarRing
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · exact (P.semisimpleReducedTrace_mul_star_pos x hx).le

/-- `Trd_{B/ℚ}(x x*) = 0` only for `x = 0`. -/
@[simp]
theorem semisimpleReducedTrace_mul_star_eq_zero {x : B} :
    letI := P.toStarRing
    Algebra.semisimpleReducedTrace ℚ B (x * star x) = 0 ↔ x = 0 := by
  let := P.toStarRing
  exact ⟨fun h ↦ by_contra fun hx ↦ (P.semisimpleReducedTrace_mul_star_pos x hx).ne' h,
    fun h ↦ by simp [h]⟩

/-- `Trd_{B/ℚ}(x* x) ≥ 0` for every `x`. -/
theorem semisimpleReducedTrace_star_mul_nonneg (x : B) :
    letI := P.toStarRing
    0 ≤ Algebra.semisimpleReducedTrace ℚ B (star x * x) := by
  let := P.toStarRing
  simpa using P.semisimpleReducedTrace_mul_star_nonneg (star x)

/-- `Trd_{B/ℚ}(x* x) = 0` only for `x = 0`. -/
@[simp]
theorem semisimpleReducedTrace_star_mul_eq_zero {x : B} :
    letI := P.toStarRing
    Algebra.semisimpleReducedTrace ℚ B (star x * x) = 0 ↔ x = 0 := by
  let := P.toStarRing
  simpa using P.semisimpleReducedTrace_mul_star_eq_zero (x := star x)

/-- **A positive involution is proper**: `x* x = 0` only for `x = 0`. -/
theorem isProperStar :
    letI := P.toStarRing
    IsProperStar B := by
  let := P.toStarRing
  exact isProperStar_of_forall_pos_mul_star (Algebra.semisimpleReducedTrace ℚ B).toAddMonoidHom
    P.semisimpleReducedTrace_mul_star_pos

/-- **A positive involution preserves the centre.** -/
theorem center_stable {z : B} (hz : z ∈ Subalgebra.center ℚ B) :
    letI := P.toStarRing
    star z ∈ Subalgebra.center ℚ B := by
  let := P.toStarRing
  exact Set.star_mem_center hz

/-- **A positive involution fixes every central idempotent.** -/
theorem centralIdempotent_fixed {e : B} (he : e ∈ centralIdempotents B) :
    letI := P.toStarRing
    star e = e := by
  let := P.toStarRing
  have := P.isProperStar
  exact star_eq_self_of_mem_centralIdempotents he

section Trace

variable [FiniteDimensional ℚ B]

/-- **Positivity for the reduced trace is positivity for the regular trace.** On a
finite-dimensional `ℚ`-algebra, an involution has `Trd_{B/ℚ}(x x*) > 0` for every `x ≠ 0` exactly
when it has `Tr_{B/ℚ}(L_{x x*}) > 0` for every `x ≠ 0`: either condition makes the involution
proper, hence `B` semisimple, so `x x*` splits along the simple factors, and on a simple factor `c`
the regular trace is `d_c > 0` times the reduced trace. This is the case `F = ℚ` of
`TauCeti.forall_pos_semisimpleReducedTrace_mul_star_iff_forall_pos_trace`. -/
theorem iff_trace_pos [StarRing B] :
    (∀ x : B, x ≠ 0 → 0 < Algebra.semisimpleReducedTrace ℚ B (x * star x)) ↔
      ∀ x : B, x ≠ 0 → 0 < LinearMap.trace ℚ B (LinearMap.mulLeft ℚ (x * star x)) :=
  forall_pos_semisimpleReducedTrace_mul_star_iff_forall_pos_trace

/-- **Positivity for the regular trace**: a positive involution has `Tr_{B/ℚ}(L_{x x*}) > 0` for
every nonzero `x`. -/
theorem trace_mulLeft_mul_star_pos {x : B} (hx : x ≠ 0) :
    letI := P.toStarRing
    0 < LinearMap.trace ℚ B (LinearMap.mulLeft ℚ (x * star x)) := by
  let := P.toStarRing
  exact iff_trace_pos.mp P.semisimpleReducedTrace_mul_star_pos x hx

/-- A `StarRing` structure on a finite-dimensional `ℚ`-algebra with `Tr_{B/ℚ}(L_{x x*}) > 0` for
every nonzero `x` is a positive involution. -/
def ofTracePos [StarRing B]
    (h : ∀ x : B, x ≠ 0 → 0 < LinearMap.trace ℚ B (LinearMap.mulLeft ℚ (x * star x))) :
    PositiveInvolution B :=
  ofStarRing (iff_trace_pos.mpr h)

/-- The involution of `ofTracePos` is the given `StarRing` structure. -/
@[simp]
theorem toStarRing_ofTracePos [inst : StarRing B]
    (h : ∀ x : B, x ≠ 0 → 0 < LinearMap.trace ℚ B (LinearMap.mulLeft ℚ (x * star x))) :
    (ofTracePos h).toStarRing = inst := by
  unfold ofTracePos
  rfl

end Trace

end PositiveInvolution

end TauCeti
