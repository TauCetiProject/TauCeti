/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Cohomology
public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology

/-!
# The singular cohomology of real projective space over a field

Over a field `k`, singular cohomology is the dual of singular homology
(`TopCat.singularCohomologyDualEquiv`), so the dimensions of the cohomology groups of `RPᴺ` are
those of its homology groups, computed from its CW structure in
`TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology`. The answer depends on the
characteristic of `k`:

* if `2 = 0` in `k`, then `Hᵈ(RPᴺ; k)` is one-dimensional for every `d ≤ N` and zero above;
* if `2 ≠ 0` in `k`, for instance `k = ℚ`, then `Hᵈ(RPᴺ; k)` is one-dimensional in degree `0` and,
  for odd `N`, in degree `N`, and vanishes in every other degree. So over such a field `RPᴺ` has
  the cohomology of a point for even `N`, and that of the sphere `Sᴺ` for odd `N`.

These are the inputs to the cup length of `RPᴺ`, and so to the cup-length lower bound for its
Lusternik–Schnirelmann category.

## Main declarations

* `TauCeti.RealProjectiveSpace.finrank_singularCohomology_of_two_eq_zero`: the dimensions of the
  cohomology of `RPᴺ` in characteristic two.
* `TauCeti.RealProjectiveSpace.finrank_singularCohomology_of_two_ne_zero`: the dimensions of the
  cohomology of `RPᴺ` away from characteristic two.
* `TauCeti.RealProjectiveSpace.subsingleton_singularCohomology_of_two_ne_zero`: away from
  characteristic two, the cohomology of `RPᴺ` vanishes in every positive degree other than an odd
  `N`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Example 2.42, and Section 3.1, Theorem 3.2.
-/

public section

noncomputable section

open Module

namespace TauCeti.RealProjectiveSpace

variable {N : ℕ} {k : Type} [Field k]

/-- **Cohomology of real projective space in characteristic two.** If `2 = 0` in the field `k`, then
`Hᵈ(RPᴺ; k)` is one-dimensional for `d ≤ N` and zero for `d > N`. -/
theorem finrank_singularCohomology_of_two_eq_zero (h2 : (2 : k) = 0) (d : ℕ) :
    finrank k ((TopCat.of (RealProjectiveSpace N)).singularCohomology (ModuleCat.of k k) k
      (ModuleCat.of k k) d) = if d ≤ N then 1 else 0 := by
  rw [TopCat.finrank_singularCohomology, finrank_singularHomology_of_two_eq_zero h2]

/-- **Cohomology of real projective space away from characteristic two.** If `2 ≠ 0` in the field
`k`, for instance `k = ℚ`, then `H⁰(RPᴺ; k)` is one-dimensional, so is `Hᴺ(RPᴺ; k)` for odd `N`, and
every other `Hᵈ(RPᴺ; k)` vanishes. -/
theorem finrank_singularCohomology_of_two_ne_zero (h2 : (2 : k) ≠ 0) (d : ℕ) :
    finrank k ((TopCat.of (RealProjectiveSpace N)).singularCohomology (ModuleCat.of k k) k
      (ModuleCat.of k k) d) = if d = 0 ∨ d = N ∧ Odd N then 1 else 0 := by
  rw [TopCat.finrank_singularCohomology, finrank_singularHomology_of_two_ne_zero h2]

/-- If `2 ≠ 0` in the field `k`, then `Hᵈ(RPᴺ; k)` vanishes in every positive degree `d`, except in
degree `N` when `N` is odd. -/
theorem subsingleton_singularCohomology_of_two_ne_zero (h2 : (2 : k) ≠ 0) {d : ℕ} (hd : d ≠ 0)
    (hdN : d = N → Even N) :
    Subsingleton ((TopCat.of (RealProjectiveSpace N)).singularCohomology (ModuleCat.of k k) k
      (ModuleCat.of k k) d) := by
  have := finite_singularCohomology_of_finiteCWType (RealProjectiveSpace N) k d
  rw [← finrank_zero_iff (R := k), finrank_singularCohomology_of_two_ne_zero h2, ite_eq_right_iff]
  rintro (rfl | ⟨rfl, hN⟩)
  exacts [absurd rfl hd, absurd hN (Nat.not_odd_iff_even.2 (hdN rfl))]

end TauCeti.RealProjectiveSpace
