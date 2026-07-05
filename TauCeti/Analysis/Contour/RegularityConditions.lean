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
angle of the model sector, from the reversed entry tangent `−L₋` to the exit tangent `L₊`, taken
`mod 2π`. Here `L₋ = lim_{t → t₀⁻} γ'(t)`, `L₊ = lim_{t → t₀⁺} γ'(t)` are the one-sided limits of
`deriv γ`. The normalization keeps it nonnegative: a **smooth** crossing (`L₊ = L₋`) gives `π`, as
in HW §3. As a `limUnder`-based value it is junk when a one-sided tangent fails to exist; it is
meaningful at the corners/crossings of a piecewise-`C¹` curve. -/
def crossingAngle (γ : ℝ → ℂ) (t₀ : ℝ) : ℝ :=
  toIcoMod Real.two_pi_pos 0
    (Complex.arg (limUnder (𝓝[>] t₀) (deriv γ)) - Complex.arg (-limUnder (𝓝[<] t₀) (deriv γ)))

/-- **Basepoint crossing angle** of a closed curve `γ` on `[a, b]`, valued in `[0, 2π)`: the opening
angle at the join `γ a = γ b`, from the reversed incoming tangent `−L₋` to the outgoing tangent
`L₊`, where `L₋ = lim_{t → b⁻} γ'(t)` and `L₊ = lim_{t → a⁺} γ'(t)`. This is `crossingAngle`'s
analogue at the basepoint, where the two tangents come from opposite ends of `[a, b]`; a smooth join
(`L₊ = L₋`) gives `π`. -/
def basepointAngle (γ : ℝ → ℂ) (a b : ℝ) : ℝ :=
  toIcoMod Real.two_pi_pos 0
    (Complex.arg (limUnder (𝓝[>] a) (deriv γ)) - Complex.arg (-limUnder (𝓝[<] b) (deriv γ)))

/-- **Sector compatibility** of `f` at an on-curve singularity `z₀` whose sector opens at angle `θ`
(the Hungerbühler–Wasem condition at one crossing): `θ` is a rational multiple `p·π/q` of `π`
(`q ≠ 0`, `p`, `q` coprime), and `f`'s finite Laurent principal part plus analytic remainder near
`z₀` has its surviving higher-order coefficients (`coeff k ≠ 0`, `k ≥ 1`) resonate with `θ` under
the sector-cancellation identity `k · θ ∈ 2π · ℤ`. -/
def SectorCompatible (f : ℂ → ℂ) (z₀ : ℂ) (θ : ℝ) : Prop :=
  (∃ p q : ℕ, q ≠ 0 ∧ Nat.Coprime p q ∧ θ = (p : ℝ) * Real.pi / (q : ℝ)) ∧
    ∃ (N : ℕ) (coeff : Fin N → ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g z₀ ∧
      (∀ᶠ z in 𝓝[≠] z₀, f z = g z + ∑ k : Fin N, coeff k / (z - z₀) ^ (k.val + 1)) ∧
        ∀ k : Fin N, coeff k ≠ 0 → 1 ≤ k.val → ∃ m : ℤ, (k.val : ℝ) * θ = (m : ℝ) * (2 * Real.pi)

/-- **Hungerbühler–Wasem condition (B)** for `f` along `γ` on `[a, b]`: at each on-curve singularity
of `f` (where `f` is not analytic at `γ t₀`) the sector is compatible (`SectorCompatible`), so
poles of order `> 1` cancel and `PV ∮_γ f` exists in the generalized residue theorem. Imposed at
each *interior* crossing `t₀ ∈ (a, b)` and at the *basepoint* `γ a` (via `basepointAngle`), so a
join singularity `γ a = γ b` is not left free. Singularities are found intrinsically via
`¬ AnalyticAt`, so the predicate is `S`-free. -/
structure ConditionB (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) : Prop where
  /-- At each interior on-curve singularity of `f`, the crossing sector at `γ t₀` is compatible. -/
  interior : ∀ t₀ ∈ Set.Ioo a b, ¬ AnalyticAt ℂ f (γ t₀) →
    SectorCompatible f (γ t₀) (crossingAngle γ t₀)
  /-- If the basepoint `γ a` (`= γ b` for a closed curve) is an on-curve singularity of `f`, its
  join sector is compatible — the endpoint case the `interior` clause cannot reach. -/
  basepoint : ¬ AnalyticAt ℂ f (γ a) → SectorCompatible f (γ a) (basepointAngle γ a b)

end TauCeti.Contour
