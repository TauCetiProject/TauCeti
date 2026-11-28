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
# Trace of an endomorphism restricted to a generalized eigenspace

Let `b : Module.End R M` be an endomorphism of a module over a reduced commutative ring `R`, and
let `p : Submodule R M` be a finite free `b`-invariant submodule contained in
`b.maxGenEigenspace c`. Then `b.restrict h_stable - c • 1` is nilpotent on `p`, so its trace
vanishes and the trace of `b` on `p` equals `c * Module.finrank R p`. Over a domain of
characteristic zero, this trace is nonzero whenever `c ≠ 0` and `p ≠ ⊥`.

## Main results

* `LinearMap.trace_restrict_eq_mul_finrank_of_le_maxGenEigenspace`: the trace of `b` restricted to
  a finite free invariant submodule `p ≤ b.maxGenEigenspace c` is `c * Module.finrank R p`.
* `LinearMap.trace_restrict_ne_zero_of_le_maxGenEigenspace`: over a domain of characteristic zero,
  the trace is nonzero when `c ≠ 0` and `p ≠ ⊥`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/General/LinearAlgebra/Eigenvalues.lean` (`New.trace_restrict_ne_zero`).
-/

@[expose] public section

open LinearMap Module

/-- If `p` is a finite free `b`-invariant submodule contained in the generalized eigenspace
`b.maxGenEigenspace c` over a reduced commutative ring `R`, then the trace of `b` restricted to `p`
equals `c * Module.finrank R p`. -/
theorem LinearMap.trace_restrict_eq_mul_finrank_of_le_maxGenEigenspace {R M : Type*} [CommRing R]
    [IsReduced R] [AddCommGroup M] [Module R M] {p : Submodule R M} [Module.Free R p]
    [Module.Finite R p] {b : Module.End R M} {c : R} (hp : p ≤ b.maxGenEigenspace c)
    (h_stable : ∀ x ∈ p, b x ∈ p) :
    LinearMap.trace R p (b.restrict h_stable) = c * Module.finrank R p := by
  have h_nil : IsNilpotent (b.restrict h_stable - c • 1) :=
    Module.End.isNilpotent_iff_of_finite.mpr fun v ↦
      Module.End.mem_genEigenspace_top.mp
        ((Module.End.genEigenspace_restrict b p ⊤ c h_stable).ge (hp v.property))
  have h_tr : LinearMap.trace R p (b.restrict h_stable - c • 1) = 0 :=
    (LinearMap.isNilpotent_trace_of_isNilpotent h_nil).eq_zero
  simpa [map_sub, map_smul, LinearMap.trace_one, smul_eq_mul, sub_eq_zero] using h_tr

/-- Over a commutative domain `R` of characteristic zero, if `p ≠ ⊥` is a finite free `b`-invariant
submodule contained in `b.maxGenEigenspace c` with `c ≠ 0`, then the trace of `b` restricted to `p`
is nonzero. -/
theorem LinearMap.trace_restrict_ne_zero_of_le_maxGenEigenspace {R M : Type*} [CommRing R]
    [IsDomain R] [CharZero R] [AddCommGroup M] [Module R M] {p : Submodule R M} [Module.Free R p]
    [Module.Finite R p] {b : Module.End R M} {c : R} (hc : c ≠ 0) (hp_ne : p ≠ ⊥)
    (hp : p ≤ b.maxGenEigenspace c) (h_stable : ∀ x ∈ p, b x ∈ p) :
    LinearMap.trace R p (b.restrict h_stable) ≠ 0 := by
  rw [trace_restrict_eq_mul_finrank_of_le_maxGenEigenspace hp h_stable]
  have hpos : 0 < Module.finrank R p :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hp_ne)
  exact mul_ne_zero hc (Nat.cast_ne_zero.mpr hpos.ne')
