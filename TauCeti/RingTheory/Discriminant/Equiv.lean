/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Discriminant

/-!
# Discriminants under base ring equivalences

Let `e : R ≃+* S` be a ring isomorphism compatible with `R`- and `S`-algebra structures on a
commutative ring `M` (`(algebraMap S M).comp e = algebraMap R M`). By Mathlib's
`Algebra.trace_eq_of_ringEquiv`, `e` intertwines the traces `Algebra.trace R M` and
`Algebra.trace S M`. Consequently, `e` carries the trace matrix and discriminant of any family in
`M` over `R` to the trace matrix and discriminant of the same family over `S`.

## Main results

* `TauCeti.Algebra.traceMatrix_eq_of_ringEquiv`:
  `(Algebra.traceMatrix R v).map e = Algebra.traceMatrix S v`.
* `TauCeti.Algebra.discr_eq_of_ringEquiv`:
  `e (Algebra.discr R v) = Algebra.discr S v`.
-/

public section

namespace TauCeti

variable {R S M ι : Type*} [CommRing R] [CommRing S] [CommRing M]
  [Algebra R M] [Algebra S M]

/-- Transporting the base ring of an algebra along a compatible ring isomorphism maps the trace
matrix entrywise. -/
theorem Algebra.traceMatrix_eq_of_ringEquiv (e : R ≃+* S)
    (he : (algebraMap S M).comp e = algebraMap R M) (v : ι → M) :
    (Algebra.traceMatrix R v).map e = Algebra.traceMatrix S v := by
  ext i j
  simp [Algebra.traceMatrix_apply, Algebra.trace_eq_of_ringEquiv e he]

/-- Transporting the base ring of an algebra along a compatible ring isomorphism maps the
discriminant of a finite family along the isomorphism. -/
theorem Algebra.discr_eq_of_ringEquiv [Fintype ι] [DecidableEq ι] (e : R ≃+* S)
    (he : (algebraMap S M).comp e = algebraMap R M) (v : ι → M) :
    e (Algebra.discr R v) = Algebra.discr S v := by
  rw [Algebra.discr_def, Algebra.discr_def, ← RingEquiv.coe_toRingHom, RingHom.map_det,
    RingHom.mapMatrix_apply, RingEquiv.coe_toRingHom, Algebra.traceMatrix_eq_of_ringEquiv e he]

end TauCeti
