/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Valuation.ColengthDvd

/-!
# Colength for iterating the level-prime operator

At the level prime, integrality in the rescaled source lattice requires one divisibility
condition per coordinate. If one application of the operator sends this lattice back into the
larger lattice of integral coordinates, iterating the operator costs at most the same colength
at each step. A bound on the sum of the coordinate degrees then controls the colength of the
preimage under the first half of the chain.

The application is the level-prime calculation of `New.Data.colengthDvd_comap_upOperator_pow`
and `New.Data.exists_colengthDvd_upIntegralForms_pow` in lsernau/grh-lean (`72fead1`,
`grh/src/New/UpperBound/Divisibility/ColengthAtLevel.lean`).
-/

public section

open Finset

namespace TauCeti.OneSidedBound

/-- If the sum of the coordinate degrees is at most `B`, the preimage of the rescaled source
lattice under `U ^ (m / 2)` has colength dividing `p ^ e` for `e ≤ m * B`. The coordinates are
defined on the larger lattice `M`; divisibility by `p ^ d j` in each listed coordinate suffices
for membership in `L`. At the level prime, the mean-degree estimate supplies `B = f * b * D`. -/
theorem exists_colengthDvd_comap_half_pow {O V ι : Type*} [CommRing O] [PreValuationRing O]
    [AddCommMonoid V] [Module O V] {M L : Submodule O V} (U : Module.End O V) (p : O)
    (s : Finset ι) (coord : ι → M →ₗ[O] O) (d : ι → ℕ) {m B : ℕ}
    (hcoord : (⨅ j ∈ s, Submodule.comap (coord j) (Ideal.span {p ^ d j})).map M.subtype ≤ L)
    (hU : L.map U ≤ M) (hm : 0 < m) (hsum : ∑ j ∈ s, d j ≤ B) :
    ∃ e ≤ m * B, M.ColengthDvd (L.comap (U ^ (m / 2) : Module.End O V)) (p ^ e) := by
  have h := (Submodule.colengthDvd_map_biInf_comap_span_pow M s coord p d).mono le_rfl hcoord
  refine ⟨(∑ j ∈ s, d j) * (m / 2 + 1), ?_, ?_⟩
  · rw [Nat.mul_comm m B]
    exact Nat.mul_le_mul hsum (by omega)
  · rw [pow_mul]
    exact h.comap_pow hU (m / 2)

end TauCeti.OneSidedBound
