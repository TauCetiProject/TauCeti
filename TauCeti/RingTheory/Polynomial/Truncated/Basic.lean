/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# The truncated polynomial algebra `R[X]/(Xⁿ)`

Mathlib builds `AdjoinRoot f` for any polynomial and, for a monic `f`, its power basis
`AdjoinRoot.powerBasis'`. It does not record what the quotient by a power of `X` looks like. This
file does: the class of `X` is nilpotent, and over a local ring `R` the algebra `R[X]/(Xⁿ)` is
again **local** when `n ≠ 0`.

Locality is the useful form of the statement, because it is what pins the idempotents: through
`IsIdempotentElem.eq_zero_or_eq_one_of_isLocalRing` a truncated polynomial algebra has no
idempotent besides `0` and `1`. That is exactly the input to the indecomposability of a nilpotent
Jordan block, whose endomorphism algebra is `k[X]/(Xⁿ)`.

The other half of that indecomposability argument -- that an endomorphism of the Jordan block *is*
multiplication by an element of `k[X]/(Xⁿ)` -- needs nothing about `Xⁿ` beyond monicity, so it
is stated for an arbitrary monic relator and lives with the rest of the general `AdjoinRoot`
material, as `AdjoinRoot.eq_mulRight_of_root_mul` in `TauCeti.RingTheory.AdjoinRoot.Basic`.

## Main results

* `TauCeti.isNilpotent_root_X_pow`: the class of `X` is nilpotent in `R[X]/(Xⁿ)`.
* `TauCeti.isLocalRing_adjoinRoot_X_sub_C_pow`: over a local ring `R`, the thickening
  `R[X]/((X-c)ⁿ)` is local for `n ≠ 0`.
* `TauCeti.isLocalRing_adjoinRoot_X_pow`: in particular `R[X]/(Xⁿ)` is local for `n ≠ 0`.

The dimension of `R[X]/(Xⁿ)` over `R` is not recorded here: `AdjoinRoot f` is by definition
`R[X] ⧸ (f)`, so Mathlib's `finrank_quotient_span_eq_natDegree` over a field, and
`finrank_quotient_span_eq_natDegree'` for a monic relator over a ring, already give it.

## Implementation notes

The evaluation `R[X]/((X-c)ⁿ) → R` at `c` is `AdjoinRoot.lift` of the identity of `R` at the root
`c`, and `AdjoinRoot.lift_mk` computes it on a class; for `c = 0` it reads off the constant term.
It is a step in the proof of locality rather than API, so the two lemmas phrased against that
unnamed map -- that its kernel consists of nilpotents, and that an element it sends to a unit is a
unit -- are `private`.

Locality is proved for `R[X]/((X-c)ⁿ)` and then specialised to `c = 0`. The second private lemma
says that the evaluation is a local homomorphism, so `RingHom.domain_isLocalRing` transfers locality
from `R`. It holds because an element is its value at `c` plus an element of the kernel, and adding
a nilpotent to a unit leaves a unit (`IsNilpotent.isUnit_add_left_of_commute`).

Everything is stated over a commutative ring; locality of course asks in addition that `R` be
local, which for the base field of the intended application is automatic.

Locality genuinely needs the hypothesis `n ≠ 0`: `R[X]/(X⁰)` is the zero ring, which is not local.
-/

public section

open Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- **The class of `X` is nilpotent in `R[X]/(Xⁿ)`**: its `n`-th power vanishes. -/
theorem isNilpotent_root_X_pow (n : ℕ) :
    IsNilpotent (AdjoinRoot.root ((X : R[X]) ^ n)) :=
  ⟨n, by rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]⟩

/-- An element of `R[X]/((X-c)ⁿ)` whose value at `c` vanishes is nilpotent. -/
private theorem isNilpotent_of_lift_eq_zero {c : R} {n : ℕ} [NeZero n]
    {x : AdjoinRoot ((X - C c) ^ n)}
    (hx : AdjoinRoot.lift (RingHom.id R) c (by simp [NeZero.ne n]) x = 0) :
    IsNilpotent x := by
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    have hp : p.IsRoot c := by simpa using hx
    obtain ⟨q, rfl⟩ := dvd_iff_isRoot.mpr hp
    rw [map_mul]
    exact (Commute.all _ _).isNilpotent_mul_right ⟨n, by rw [← map_pow, AdjoinRoot.mk_self]⟩

/-- An element of `R[X]/((X-c)ⁿ)` whose value at `c` is a unit is a unit. -/
private theorem isUnit_of_isUnit_lift {c : R} {n : ℕ} [NeZero n]
    {x : AdjoinRoot ((X - C c) ^ n)}
    (hx : IsUnit (AdjoinRoot.lift (RingHom.id R) c (by simp [NeZero.ne n]) x)) :
    IsUnit x := by
  set a := AdjoinRoot.lift (RingHom.id R) c (by simp [NeZero.ne n]) x with ha
  have hker : AdjoinRoot.lift (RingHom.id R) c (by simp [NeZero.ne n])
      (x - algebraMap R _ a) = 0 := by
    simp [ha]
  have := (isNilpotent_of_lift_eq_zero hker).isUnit_add_left_of_commute
    (hx.map (algebraMap R (AdjoinRoot ((X - C c) ^ n)))) (Commute.all _ _)
  rwa [add_sub_cancel] at this

/-- A thickening `R[X]/((X-c)ⁿ)` of a rational polynomial point over a local ring is local when
`n ≠ 0`. -/
theorem isLocalRing_adjoinRoot_X_sub_C_pow [IsLocalRing R] (c : R) (n : ℕ) [NeZero n] :
    IsLocalRing (AdjoinRoot ((X - C c) ^ n)) :=
  let φ : AdjoinRoot ((X - C c) ^ n) →+* R :=
    AdjoinRoot.lift (RingHom.id R) c (by simp [NeZero.ne n])
  have : IsLocalHom φ := ⟨fun _ ↦ isUnit_of_isUnit_lift⟩
  φ.domain_isLocalRing

/-- The truncated polynomial algebra `R[X]/(Xⁿ)` over a local ring is local when `n ≠ 0`. -/
instance isLocalRing_adjoinRoot_X_pow [IsLocalRing R] (n : ℕ) [NeZero n] :
    IsLocalRing (AdjoinRoot ((X : R[X]) ^ n)) :=
  (by simp : X - C (0 : R) = X) ▸ isLocalRing_adjoinRoot_X_sub_C_pow (0 : R) n

end TauCeti
