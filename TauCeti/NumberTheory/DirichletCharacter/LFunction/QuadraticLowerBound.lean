/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.FiniteFamily.BoundedConductor
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.LocalFactor

/-!
# A uniform lower bound near one for quadratic Dirichlet L-functions

When the prime divisors of the level range over a fixed finite set, quadratic Dirichlet
characters have bounded conductor. Nonvanishing at `1` in the resulting finite family,
together with a lower bound for the deleted Euler factors, gives a common positive lower bound
on a neighbourhood of `1`. For principal characters the bound is for the L-function with its
pole removed and divided by `s`.

This is the finite-family input to the near-one logarithmic-derivative estimate in
lsernau/grh-lean (revision `72fead1`, `New.eventually_norm_logDeriv_entireL_le_near_one`).
Unlike descent to a fixed level in a modulus tower, the conductor and Euler-factor argument
also allows the prime support to vary within the given set.
-/

public section

open Finset Filter DirichletCharacter
open scoped Topology

namespace TauCeti.DirichletCharacter

/-- For a fixed finite set of primes `S`, the regularized L-functions of all complex characters
whose square is principal and whose level is supported in `S` are uniformly bounded away from
zero on a common neighbourhood of `1`. In the principal case the regularized function is the
pole-removed `LFunctionTrivChar₁` divided by `s`; otherwise it is the ordinary L-function. -/
theorem exists_pos_eventually_le_norm_regularizedLFunction_of_sq_eq_one (S : Finset ℕ) :
    ∃ c > (0 : ℝ), ∀ᶠ s : ℂ in 𝓝 1, ∀ (N : ℕ) [NeZero N], N.primeFactors ⊆ S →
      ∀ χ : DirichletCharacter ℂ N, χ ^ 2 = 1 → c ≤ ‖χ.regularizedLFunction s‖ := by
  obtain ⟨c, hc, hnear⟩ := exists_pos_eventually_le_norm_regularizedLFunction_of_conductor_le
    (∏ p ∈ S.filter Nat.Prime, p ^ 3) S.card
  refine ⟨c, hc, ?_⟩
  filter_upwards [hnear] with s hs N inst hS χ hχ
  exact hs N (card_le_card hS) χ (χ.conductor_le_prod_cube_of_sq_eq_one hχ hS)

end TauCeti.DirichletCharacter
