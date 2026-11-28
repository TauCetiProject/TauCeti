/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
import TauCeti.Analysis.Asymptotics.NatFloor

/-!
# Real cutoffs for the signed prime remainder

The theorem `eventually_primeRemainder_le_rpow_iff_natCast` gives the real-cutoff estimate
from integer estimates with arbitrarily small exponent losses, using the local variation bound
`abs_primeRemainder_sub_le` and floor interpolation. Taking `ε = β - 1/2` for `β > 1/2`
supplies the eventual upper bound `y ^ (β - 1)` required by the Dirichlet L-function
zero-exclusion criterion `LFunction_ne_zero_of_primeRemainder_le`.

The transfer is the step in `New.eventually_primeRemainder_le_rpow` in
`grh/src/New/Reduction/OneSidedBound.lean` of lsernau/grh-lean, revision `72fead1`
(<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Filter
open scoped Nat

namespace TauCeti.OneSidedBound

/-- The signed prime remainder has eventual upper bounds `y ^ (-1/2 + ε)` at real cutoffs
for every positive `ε` if and only if it has the corresponding bounds up to an
`ε`-dependent constant at natural cutoffs. Here `d` is prime and `q` is a nonzero modulus. -/
theorem eventually_primeRemainder_le_rpow_iff_natCast {d q : ℕ} [Fact d.Prime] [NeZero q] :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ y : ℝ in atTop, primeRemainder d q y ≤ y ^ (-(1 / 2) + ε)) ↔
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
        primeRemainder d q n ≤ C * (n : ℝ) ^ (-(1 / 2) + ε)) := by
  have hfloor : ∀ᶠ y : ℝ in atTop, primeRemainder d q y - primeRemainder d q ⌊y⌋₊ ≤
      2 * |(13 : ℝ)| / y := by
    apply eventually_sub_nat_floor_le_div
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn y hny _
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    exact (le_abs_self _).trans (abs_primeRemainder_sub_le d q hnpos hny)
  exact eventually_le_rpow_add_iff_natCast (by norm_num) hfloor

end TauCeti.OneSidedBound
