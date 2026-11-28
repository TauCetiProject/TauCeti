/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Ideal
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Defs

import Mathlib.Algebra.Order.Group.Ideal
import Mathlib.Data.Finsupp.PWO
import TauCeti.Algebra.Group.Ideal

/-!
# Uniform cut-off degree for cardinality bounds on monomial ideals

Specializing `TauCeti.eventually_forall_ncard_sdiff_le` to `α = J →₀ ℕ` (with `Finite J`) and
`S i = Finsupp.degree ⁻¹' {f i}` for any degree sequence `f : ℕ → ℕ` yields the uniform cut-off
index for monomial ideals in finitely many variables.

## Main results

* `TauCeti.eventually_forall_ncard_degree_sdiff_le`: uniform cut-off index for monomial ideals
  `AddSemigroupIdeal (J →₀ ℕ)` in finitely many variables `J` and arbitrary degree sequence
  `f : ℕ → ℕ`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Shimura/ThetaModuli/FlatClosure.lean` (`eventually_isCutDegree`).
-/

public section

open Filter Set

namespace TauCeti

/-- For finitely many variables `J`, any degree sequence `f : ℕ → ℕ`, and any count bounds
`σ : ℕ → ℕ`, every sufficiently large `d : ℕ` is a uniform cut-off for monomial ideals
`M : AddSemigroupIdeal (J →₀ ℕ)`: omitting at most `σ i` monomials of degree `f i` for all
`i ≤ d` forces the same bound for all `i : ℕ`. -/
theorem eventually_forall_ncard_degree_sdiff_le {J : Type*} [Finite J] (f σ : ℕ → ℕ) :
    ∀ᶠ d : ℕ in atTop, ∀ M : AddSemigroupIdeal (J →₀ ℕ),
      (∀ i ≤ d, (Finsupp.degree ⁻¹' {f i} \ M.carrier).ncard ≤ σ i) →
        ∀ i : ℕ, (Finsupp.degree ⁻¹' {f i} \ M.carrier).ncard ≤ σ i :=
  eventually_forall_ncard_sdiff_le
    (fun i ↦ Finsupp.degree ⁻¹' {f i}) (fun i ↦ Finsupp.finite_of_degree_eq (f i)) σ

end TauCeti
