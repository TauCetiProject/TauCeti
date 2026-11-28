/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Trace

import Mathlib.RingTheory.Finiteness.Nilpotent
import TauCeti.LinearAlgebra.Trace.Basic

/-!
# Trace of an endomorphism restricted to a generalized eigenspace

Specializing `LinearMap.trace_eq_mul_finrank_of_isNilpotent_sub` and
`LinearMap.trace_ne_zero_of_isNilpotent_sub` to a `b`-invariant finite free submodule
`p ≤ b.maxGenEigenspace c` gives the trace formula and nonvanishing criterion for
`b.restrict h_stable`.

## Main results

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
