/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Algebra.Order.ToIntervalMod

/-!
# The Hungerbühler–Wasem crossing angle and regularity condition (B)

For a curve `γ : ℝ → ℂ` on `[a, b]` and an integrand `f : ℂ → ℂ`, this file defines the **crossing
angle** of `γ` at an interior time and the Hungerbühler–Wasem regularity **condition (B)** at the
on-curve singularities of `f`. Condition (B) is one of the two regularity hypotheses (with
condition (A′), the transversal-approach/flatness condition) under which the Cauchy principal
value `PV ∮_γ f` exists in the generalized residue theorem (HW Thm 3.3). It governs poles of
order `> 1`, coupling the Laurent principal part of `f` at each on-curve singularity with the
entry/exit tangents of `γ` there, through a sector-cancellation identity.

## Main definitions

* `crossingAngle γ t₀` — the model-sector opening angle in `[0, 2π)`, from the exit tangent `L₊` to
  the reversed entry tangent `−L₋` (`mod 2π`), where `L₋`, `L₊` are the one-sided limits of
  `deriv γ` from the left and right at `t₀`. Junk when a one-sided tangent fails to exist; a smooth
  crossing gives `π`. Meaningful at the corners/crossings of a piecewise-`C¹` curve.
* `ConditionB γ a b f` — HW condition (B): at every interior on-curve singularity of `f`, the
  crossing angle is a rational multiple of `π`, and the Laurent principal part of `f` there
  resonates with that angle for each surviving higher-order coefficient (sector cancellation).

On-curve singularities are detected **intrinsically** as the interior times `t₀ ∈ (a, b)` with
`¬ AnalyticAt ℂ f (γ t₀)`, so the predicate is `S`-free and depends only on `(γ, f)`, matching the
roadmap signature and the way the generalized residue theorem consumes it. Being a `structure`,
`ConditionB` supplies its two clauses as the projections `ConditionB.angle_rational` and
`ConditionB.laurent_compatible`, and is built with the anonymous constructor `⟨·, ·⟩`.

## Provenance

Migrated and adapted from the AINTLIB `LeanModularForms` project (`angleAtCrossing` and
`SatisfiesConditionB`), specialised to the raw-function (`γ : ℝ → ℂ` on `[a, b]`) design of the
contour-integration roadmap, with the singular set detected intrinsically rather than prescribed.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

/-- **Crossing angle** of `γ : ℝ → ℂ` at an interior time `t₀`, valued in `[0, 2π)`: the opening
angle of the model sector, from the exit tangent `L₊` to the reversed entry tangent `−L₋`, taken
`mod 2π`. Here `L₋ = lim_{t → t₀⁻} γ'(t)`, `L₊ = lim_{t → t₀⁺} γ'(t)` are the one-sided limits of
`deriv γ`. The normalization keeps it nonnegative: a **smooth** crossing (`L₊ = L₋`) gives `π`, as
in HW §3. As a `limUnder`-based value it is junk when a one-sided tangent fails to exist; it is
meaningful at the corners/crossings of a piecewise-`C¹` curve. -/
def crossingAngle (γ : ℝ → ℂ) (t₀ : ℝ) : ℝ :=
  toIcoMod Real.two_pi_pos 0
    (Complex.arg (-limUnder (𝓝[<] t₀) (deriv γ)) - Complex.arg (limUnder (𝓝[>] t₀) (deriv γ)))

/-- **Hungerbühler–Wasem condition (B)** for `f` along `γ` on `[a, b]`, imposed at each interior
time `t₀ ∈ (a, b)` where `f` fails to be analytic at `γ t₀` — the on-curve singularities of `f`.
One of the two regularity conditions (with (A′)) that make the Cauchy principal value `PV ∮_γ f`
exist in the generalized residue theorem, governing poles of order `> 1` via sector cancellation.
The singular set is detected intrinsically through `¬ AnalyticAt`, so the predicate is `S`-free. -/
structure ConditionB (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) : Prop where
  /-- At each interior on-curve singularity of `f`, the crossing angle of `γ` is a rational multiple
  `p·π/q` of `π` (`q ≠ 0`, `p`, `q` coprime) — the sector opens at a commensurable angle. -/
  angle_rational : ∀ t₀ ∈ Set.Ioo a b, ¬ AnalyticAt ℂ f (γ t₀) →
    ∃ p q : ℕ, q ≠ 0 ∧ Nat.Coprime p q ∧ crossingAngle γ t₀ = (p : ℝ) * Real.pi / (q : ℝ)
  /-- At each interior on-curve singularity of `f`, `f` has a finite Laurent principal part
  `∑_{k < N} coeff k · (z − γ t₀)^{-(k+1)}` plus an analytic remainder `g` near `γ t₀`, whose
  surviving higher-order coefficients (`coeff k ≠ 0`, `k ≥ 1`) resonate with the crossing angle
  under the sector-cancellation identity `k · crossingAngle γ t₀ ∈ 2π · ℤ`. -/
  laurent_compatible : ∀ t₀ ∈ Set.Ioo a b, ¬ AnalyticAt ℂ f (γ t₀) →
    ∃ (N : ℕ) (coeff : Fin N → ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g (γ t₀) ∧
      (∀ᶠ z in 𝓝[≠] (γ t₀), f z = g z + ∑ k : Fin N, coeff k / (z - γ t₀) ^ (k.val + 1)) ∧
        ∀ k : Fin N, coeff k ≠ 0 → 1 ≤ k.val →
          ∃ m : ℤ, (k.val : ℝ) * crossingAngle γ t₀ = (m : ℝ) * (2 * Real.pi)

end TauCeti.Contour
