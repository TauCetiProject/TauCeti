/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.NumberTheory.LSeries.WienerIkehara.Variants
import TauCeti.Analysis.Convex.Cone.PositiveDual

/-!
# The Wiener--Ikehara theorem for coefficients in an ordered vector space

Let `E` be a finite-dimensional real normed space with a partial order compatible with its module
structure and a closed positive cone; for instance `ι → ℝ` with the coordinatewise order for a
finite type `ι`, or any finite-dimensional ordered real normed algebra with closed positive cone.
For coefficients `a n ∈ E` that are eventually nonnegative, this file deduces the asymptotic
`x⁻¹ ∑_{1 ≤ n ≤ x} a n → κ` in `E` from the scalar theorem
`TauCeti.LSeries.wienerIkehara_of_eventually_nonneg`.

Mathlib's `LSeries` has complex coefficients, so the analytic input is stated one monotone
continuous linear functional `φ` at a time: the real coefficients `φ (a n)` are eventually
nonnegative, and their Dirichlet series, less `φ κ / (s - 1)`, is required to extend continuously
to `Re s ≥ 1`. The scalar theorem then gives the asymptotic for every `φ (a n)`. Monotone
continuous functionals separate the points of `E` because its positive cone is closed
(`TauCeti.eq_of_forall_monotone_dual_eq`, a consequence of Farkas' lemma), so evaluation at them is
an injective linear map from the finite-dimensional space `E`, hence a closed embedding, and the
scalar limits assemble to the limit in `E` (`TauCeti.tendsto_iff_forall_monotone_dual`).

Finite dimensionality is what turns convergence against each functional into convergence in `E`.
Closedness of the positive cone is what makes the monotone functionals separate points: for the
lexicographic order on `ℝ²`, whose positive cone is not closed, the monotone continuous linear
functionals are the nonnegative multiples of the first coordinate, so the hypotheses say nothing
about the second coordinates of the `a n`.

## Main results

* `TauCeti.LSeries.wienerIkehara_of_forall_monotone_dual`: the Wiener--Ikehara theorem for
  eventually nonnegative coefficients in a finite-dimensional ordered real normed space with
  closed positive cone.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
-/

public section

open Filter Topology

namespace TauCeti.LSeries

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [PartialOrder E] [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [OrderClosedTopology E]

/-- **The Wiener--Ikehara theorem for coefficients in an ordered vector space.** Let `E` be a
finite-dimensional ordered real normed space with closed positive cone, and let `a n ∈ E` satisfy
`0 ≤ a n` for all large `n`. Suppose that for every monotone continuous linear functional `φ` on
`E`, the Dirichlet series of the real coefficients `φ (a n)` has sum `F s` on `Re s > 1` and there
is a function `G` continuous on `Re s ≥ 1` with `G s = F s - φ κ / (s - 1)` on `Re s > 1`. Then
`x⁻¹ ∑_{1 ≤ n ≤ x} a n → κ` in `E` as `x → ∞`. -/
theorem wienerIkehara_of_forall_monotone_dual {a : ℕ → E} {κ : E}
    (ha : ∀ᶠ n in atTop, 0 ≤ a n)
    (hφ : ∀ φ : StrongDual ℝ E, Monotone φ → ∃ F G : ℂ → ℂ,
      (∀ s : ℂ, 1 < s.re → LSeriesHasSum (fun n ↦ (φ (a n) : ℂ)) s (F s)) ∧
      ContinuousOn G {s : ℂ | 1 ≤ s.re} ∧ ∀ s : ℂ, 1 < s.re → G s = F s - φ κ / (s - 1)) :
    Tendsto (fun x : ℝ ↦ x⁻¹ • ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) atTop (𝓝 κ) := by
  -- Convergence in `E` is detected by the monotone functionals, and in each of them this is the
  -- scalar theorem for the coefficients `φ (a n)`.
  refine tendsto_iff_forall_monotone_dual.2 fun φ hφm ↦ ?_
  obtain ⟨F, G, hF, hG, hGF⟩ := hφ φ hφm
  have hφa : ∀ᶠ n in atTop, 0 ≤ φ (a n) :=
    ha.mono fun n hn ↦ (monotone_iff_map_nonneg φ).1 hφm _ hn
  have key (x : ℝ) : φ (x⁻¹ • ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) =
      x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, φ (a n) := by
    rw [map_smul, map_sum, smul_eq_mul]
  simpa only [key] using wienerIkehara_of_eventually_nonneg hφa hF hG hGF

end TauCeti.LSeries
