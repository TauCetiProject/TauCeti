/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Ordered products over primes with finitely many factors deleted

For `f : ℕ → M`, the ordered products `∏ p ∈ Nat.primesLE B, f p` over the primes `p ≤ B` are the
finite cutoffs of a product over all primes, such as an Euler product, whose infinite product need
not converge unconditionally. Deleting the factors at a finite set `S` of primes changes these
cutoffs, once `B` is past `S`, by the fixed factor `∏ p ∈ S, f p`. When no deleted factor vanishes,
convergence of the cutoffs therefore transports in both directions with this explicit correction.

## Main results

* `Nat.eventually_subset_primesLE`: a finite set of primes eventually lies in `Nat.primesLE B`.
* `Nat.prod_primesLE_filter_notMem_mul_prod`: the exact finite correction.
* `Nat.tendsto_prod_primesLE_filter_notMem_iff`: the corresponding equivalence of limits.
-/

public section

open Filter Finset
open scoped Topology

namespace Nat

variable {S : Finset ℕ}

/-- Every element of a finite set of primes eventually lies below the cutoff. -/
theorem eventually_subset_primesLE (hS : ∀ p ∈ S, p.Prime) : ∀ᶠ B in atTop, S ⊆ primesLE B := by
  filter_upwards [eventually_ge_atTop (S.sup id)] with B hB p hp
  exact mem_primesLE.mpr ⟨(le_sup (f := id) hp).trans hB, hS p hp⟩

/-- Once the primes `p ≤ B` contain a finite set `S`, the product over the primes `p ≤ B` outside
`S`, times the product over `S`, is the product over all primes `p ≤ B`. -/
theorem prod_primesLE_filter_notMem_mul_prod {M : Type*} [CommMonoid M] (f : ℕ → M) {B : ℕ}
    (hSB : S ⊆ primesLE B) :
    (∏ p ∈ primesLE B with p ∉ S, f p) * ∏ p ∈ S, f p = ∏ p ∈ primesLE B, f p := by
  rw [← sdiff_eq_filter, prod_sdiff hSB]

/-- **Deleting finitely many factors from ordered prime products.** Let `S` be a finite set of
primes at which no factor `f p` vanishes. The products of `f` over all primes `p ≤ B` converge to
`L * ∏ p ∈ S, f p` if and only if the products over the primes `p ≤ B` outside `S` converge to
`L`. -/
theorem tendsto_prod_primesLE_filter_notMem_iff {G₀ : Type*} [CommGroupWithZero G₀]
    [TopologicalSpace G₀] [SeparatelyContinuousMul G₀] {f : ℕ → G₀} (hS : ∀ p ∈ S, p.Prime)
    (hf : ∀ p ∈ S, f p ≠ 0) {L : G₀} :
    Tendsto (fun B : ℕ ↦ ∏ p ∈ primesLE B, f p) atTop (𝓝 (L * ∏ p ∈ S, f p)) ↔
      Tendsto (fun B : ℕ ↦ ∏ p ∈ primesLE B with p ∉ S, f p) atTop (𝓝 L) := by
  have heq : (fun B : ℕ ↦ ∏ p ∈ primesLE B, f p) =ᶠ[atTop]
      fun B ↦ (∏ p ∈ primesLE B with p ∉ S, f p) * ∏ p ∈ S, f p := by
    filter_upwards [eventually_subset_primesLE hS] with B hB
    exact (prod_primesLE_filter_notMem_mul_prod f hB).symm
  rw [tendsto_congr' heq]
  exact ((Homeomorph.mulRight₀ _ (prod_ne_zero_iff.mpr hf)).isInducing.tendsto_nhds_iff).symm

end Nat
