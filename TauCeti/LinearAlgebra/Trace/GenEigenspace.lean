/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Trace

import Mathlib.RingTheory.Finiteness.Nilpotent

/-!
# Trace of an endomorphism shifted by a scalar, and on a generalized eigenspace

If `f : Module.End R M` is an endomorphism of a finite free module `M` over a reduced commutative
ring `R` such that `f - c • 1` is nilpotent, then `LinearMap.trace R M f = c * Module.finrank R M`.
Over a domain of characteristic zero, this trace is nonzero whenever `c ≠ 0` and `M` is nontrivial.
Specializing to a `b`-invariant finite free submodule `p ≤ b.maxGenEigenspace c` gives the trace
formula and nonvanishing criterion for `b.restrict h_stable`.

## Main results

* `LinearMap.trace_eq_mul_finrank_of_isNilpotent_sub`: if `IsNilpotent (f - c • 1)`, then
  `LinearMap.trace R M f = c * Module.finrank R M`.
* `LinearMap.trace_ne_zero_of_isNilpotent_sub`: over a domain of characteristic zero, if
  `IsNilpotent (f - c • 1)`, `c ≠ 0`, and `Nontrivial M`, then `LinearMap.trace R M f ≠ 0`.
* `LinearMap.trace_restrict_eq_mul_finrank_of_le_maxGenEigenspace`: specialization to a
  `b`-invariant submodule `p ≤ b.maxGenEigenspace c`.
* `LinearMap.trace_restrict_ne_zero_of_le_maxGenEigenspace`: nonvanishing of the restricted trace
  on a nonzero `b`-invariant submodule `p ≤ b.maxGenEigenspace c`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/General/LinearAlgebra/Eigenvalues.lean` (`New.trace_restrict_ne_zero`).
-/

@[expose] public section

open Module

namespace LinearMap

/-- If `f : Module.End R M` on a finite free module over a reduced commutative ring satisfies
`IsNilpotent (f - c • 1)`, then `LinearMap.trace R M f = c * Module.finrank R M`. -/
theorem trace_eq_mul_finrank_of_isNilpotent_sub {R M : Type*} [CommRing R] [IsReduced R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] {f : End R M} {c : R}
    (h : IsNilpotent (f - c • 1)) :
    trace R M f = c * finrank R M := by
  have h_nil : IsNilpotent (f - algebraMap R (End R M) c) := by
    rwa [Module.algebraMap_end_eq_smul_id]
  simpa [mul_comm, trace_one, ← Module.End.mul_eq_comp] using
    trace_comp_eq_mul_of_commute_of_isNilpotent c (Commute.one_left f) h_nil

/-- Over a commutative domain of characteristic zero, if `f : Module.End R M` on a nontrivial
finite free module satisfies `IsNilpotent (f - c • 1)` with `c ≠ 0`, then
`LinearMap.trace R M f ≠ 0`. -/
theorem trace_ne_zero_of_isNilpotent_sub {R M : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] [Nontrivial M]
    {f : End R M} {c : R} (hc : c ≠ 0) (h : IsNilpotent (f - c • 1)) :
    trace R M f ≠ 0 := by
  rw [trace_eq_mul_finrank_of_isNilpotent_sub h]
  exact mul_ne_zero hc (Nat.cast_ne_zero.mpr finrank_pos.ne')

/-- For a `b`-invariant finite free submodule `p ≤ b.maxGenEigenspace c` over a reduced commutative
ring `R`, the trace of `b.restrict h_stable` equals `c * Module.finrank R p`. -/
theorem trace_restrict_eq_mul_finrank_of_le_maxGenEigenspace {R V : Type*} [CommRing R]
    [IsReduced R] [AddCommGroup V] [Module R V] {p : Submodule R V} [Module.Free R p]
    [Module.Finite R p] {b : End R V} {c : R} (hp_le : p ≤ b.maxGenEigenspace c)
    (h_stable : ∀ x ∈ p, b x ∈ p) :
    trace R p (b.restrict h_stable) = c * finrank R p :=
  trace_eq_mul_finrank_of_isNilpotent_sub <|
    End.isNilpotent_iff_of_finite.mpr fun v ↦
      End.mem_genEigenspace_top.mp
        ((End.genEigenspace_restrict b p ⊤ c h_stable).ge (hp_le v.property))

/-- Over a commutative domain of characteristic zero, if `p ≠ ⊥` is a `b`-invariant finite free
submodule contained in `b.maxGenEigenspace c` with `c ≠ 0`, then the trace of `b.restrict h_stable`
is nonzero. -/
theorem trace_restrict_ne_zero_of_le_maxGenEigenspace {R V : Type*} [CommRing R] [IsDomain R]
    [CharZero R] [AddCommGroup V] [Module R V] {p : Submodule R V} [Module.Free R p]
    [Module.Finite R p] {b : End R V} {c : R} (hc : c ≠ 0) (hp_ne : p ≠ ⊥)
    (hp_le : p ≤ b.maxGenEigenspace c) (h_stable : ∀ x ∈ p, b x ∈ p) :
    trace R p (b.restrict h_stable) ≠ 0 :=
  have : Nontrivial p := Submodule.nontrivial_iff_ne_bot.mpr hp_ne
  trace_ne_zero_of_isNilpotent_sub hc <|
    End.isNilpotent_iff_of_finite.mpr fun v ↦
      End.mem_genEigenspace_top.mp
        ((End.genEigenspace_restrict b p ⊤ c h_stable).ge (hp_le v.property))

end LinearMap
