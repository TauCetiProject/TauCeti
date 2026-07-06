/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Algebra.Order.ToIntervalMod

/-!
# The Hungerbühler–Wasem crossing angle and regularity conditions (A′) and (B)

For a curve `γ : ℝ → ℂ` on `[a, b]` and an integrand `f : ℂ → ℂ`, this file defines the **crossing
angle** and the **flatness** of `γ` at a time, and the roadmap's two Hungerbühler–Wasem regularity
conditions at its on-curve singularities: the geometric transversal-approach condition **(A′)** and
the analytic sector-cancellation condition **(B)**, the two regularity hypotheses of the generalized
residue theorem (HW Thm 3.3), which evaluates the Cauchy principal value `PV ∮_γ f`. Condition (A′)
asks that `γ` approach each prescribed on-curve singularity transversally (flat of order `1`) — its
order-`1` form, exact for simple poles (the reach of this development, whose valence-formula
target uses `f′/f`); the full higher-order (A′), matching flatness to pole order, needs order data
absent from the f-free roadmap signature and is left as a roadmap-signature question. Condition (B)
governs poles of order `> 1`, coupling the Laurent principal part of `f` at each such pole with the
entry/exit tangents of `γ` there, via a sector-cancellation identity; simple poles need no sector
condition.

## Main definitions

* `crossingAngle γ t₀` — the model-sector opening angle in `[0, 2π)`, from the reversed entry
  tangent `−L₋` to the exit tangent `L₊` (`mod 2π`), where `L₋`, `L₊` are the one-sided limits of
  `deriv γ` from the left and right at `t₀`. Junk when a one-sided tangent fails to exist; a smooth
  crossing gives `π` (`crossingAngle_eq_pi`). Meaningful at the corners/crossings of a
  piecewise-`C¹` curve.
* `basepointAngle γ a b` — the analogous opening angle at the join `γ a = γ b` of a closed curve,
  from the reversed incoming tangent at `b` to the outgoing tangent at `a`.
* `FlatOfOrder γ t₀ n` — `γ` is **flat of order `n`** at `t₀` (parametrized-tangent form): from each
  side, `γ` deviates from a one-sided tangent line by `o(‖γ t − γ t₀‖ⁿ)`. Order `1` is a transversal
  crossing (HW's flatness for immersions); see its docstring for the `n ≥ 2` caveat vs HW Def. 3.2.
* `FlatOfOrderBasepoint γ a b n` — the analogue at the join `γ a = γ b` of a closed curve, matching
  the outgoing tangent at `a` (from the right) with the incoming tangent at `b` (from the left).
* `ConditionAprime γ a b S` — the roadmap's condition (A′) target in transversal (order-`1`) form: a
  structure asking `γ` be flat of order `1` at every crossing of every singularity `s ∈ S`,
  at each interior crossing (`ConditionAprime.interior`) and at the basepoint
  (`ConditionAprime.basepoint`). Purely geometric (f-free), exact for simple poles; its docstring
  explains why the full higher-order HW (A′) is a roadmap-signature question.
* `SectorCompatible f z₀ θ` — the one-crossing Hungerbühler–Wasem sector condition, a structure with
  fields `angle_rational` (`θ` is a rational multiple of `π`) and `laurent_compatible` (the Laurent
  principal part of `f` at `z₀` resonates with `θ`).
* `ConditionB γ a b f` — HW condition (B), a structure imposing `SectorCompatible` at every
  higher-order (order `> 1`) on-curve pole of `f`: at each interior crossing (`ConditionB.interior`)
  and at the basepoint (`ConditionB.basepoint`).

Higher-order on-curve poles (for condition (B)) are detected **intrinsically** as the times `t₀`
where `meromorphicOrderAt f (γ t₀) < -1` (a pole of order `> 1`), so `ConditionB` is `S`-free and
depends only on `(γ, f)`. Condition (A′), the geometric condition, is imposed on the prescribed
singular set `S`. Both match the roadmap signatures and the way the generalized residue theorem
consumes them.

## Provenance

Migrated and adapted from the AINTLIB `LeanModularForms` project (`angleAtCrossing`, `FlatOfOrder`,
and `SatisfiesConditionB`), specialised to the raw-function (`γ : ℝ → ℂ` on `[a, b]`) design of the
contour-integration roadmap. Condition (A′) is imposed on the prescribed singular set `S`; condition
(B) detects the higher-order poles of `f` intrinsically via `meromorphicOrderAt`.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

/-- **Crossing angle** of `γ : ℝ → ℂ` at a time `t₀`, valued in `[0, 2π)`: the opening angle of the
model sector, from the reversed entry tangent `−L₋` to the exit tangent `L₊`, taken `mod 2π`. Here
`L₋ = lim_{t → t₀⁻} γ'(t)`, `L₊ = lim_{t → t₀⁺} γ'(t)` are the one-sided limits of `deriv γ`. The
normalization keeps it nonnegative: a **smooth** crossing (`L₊ = L₋`) gives `π`, as in HW §3. As a
`limUnder`-based value it is junk when a one-sided tangent fails to exist; it is meaningful at the
corners/crossings of a piecewise-`C¹` curve. -/
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

/-- For a nonzero `L : ℂ`, the normalized angle from `−L` to `L` is `π`: `L.arg - (-L).arg`
is `±π`, and both representatives land on `π` in `[0, 2π)`. This is the engine behind the
smooth-crossing values of `crossingAngle` and `basepointAngle`. -/
private theorem toIcoMod_arg_sub_arg_neg {L : ℂ} (hL : L ≠ 0) :
    toIcoMod Real.two_pi_pos 0 (Complex.arg L - Complex.arg (-L)) = Real.pi := by
  have hmem : Real.pi ∈ Set.Ico (0 : ℝ) (0 + 2 * Real.pi) :=
    Set.mem_Ico.mpr ⟨Real.pi_nonneg, by rw [zero_add]; linarith [Real.pi_pos]⟩
  -- `arg L - arg (-L)` is `π` or `-π`, according to the sign of the tangent `L ≠ 0`.
  have key : Complex.arg L - Complex.arg (-L) = Real.pi ∨
      Complex.arg L - Complex.arg (-L) = -Real.pi := by
    rcases lt_trichotomy L.im 0 with him | him | him
    · exact Or.inr (by rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg him]; ring)
    · have hre : L.re ≠ 0 := fun h => hL (by simp [Complex.ext_iff, h, him])
      rcases lt_or_gt_of_ne hre with hre' | hre'
      · exact Or.inl (by rw [Complex.arg_neg_eq_arg_sub_pi_iff.mpr (Or.inr ⟨him, hre'⟩)]; ring)
      · exact Or.inr (by rw [Complex.arg_neg_eq_arg_add_pi_iff.mpr (Or.inr ⟨him, hre'⟩)]; ring)
    · exact Or.inl (by rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos him]; ring)
  rcases key with h | h <;> rw [h]
  · exact (toIcoMod_eq_self Real.two_pi_pos).mpr hmem
  · -- `toIcoMod` is `2π`-periodic, so the representative of `-π` in `[0, 2π)` is `-π + 2π = π`.
    have hshift : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [← toIcoMod_add_right Real.two_pi_pos 0 (-Real.pi), hshift]
    exact (toIcoMod_eq_self Real.two_pi_pos).mpr hmem

/-- `crossingAngle γ t₀` lies in `[0, 2π)`, the range of the model-sector normalization. Its two
projections `crossingAngle_nonneg`/`crossingAngle_lt_two_pi` are the `@[simp]` normal forms. -/
theorem crossingAngle_mem_Ico (γ : ℝ → ℂ) (t₀ : ℝ) :
    crossingAngle γ t₀ ∈ Set.Ico 0 (2 * Real.pi) := by
  have h := toIcoMod_mem_Ico Real.two_pi_pos 0
    (Complex.arg (limUnder (𝓝[>] t₀) (deriv γ)) - Complex.arg (-limUnder (𝓝[<] t₀) (deriv γ)))
  rw [zero_add] at h
  rw [crossingAngle]
  exact h

@[simp] theorem crossingAngle_nonneg (γ : ℝ → ℂ) (t₀ : ℝ) : 0 ≤ crossingAngle γ t₀ :=
  (Set.mem_Ico.mp (crossingAngle_mem_Ico γ t₀)).1

@[simp] theorem crossingAngle_lt_two_pi (γ : ℝ → ℂ) (t₀ : ℝ) :
    crossingAngle γ t₀ < 2 * Real.pi :=
  (Set.mem_Ico.mp (crossingAngle_mem_Ico γ t₀)).2

/-- **Smooth-crossing value.** If the one-sided tangents of `γ` at `t₀` agree and are nonzero, the
crossing angle is `π`: there is no genuine corner. -/
theorem crossingAngle_eq_pi {γ : ℝ → ℂ} {t₀ : ℝ}
    (h : limUnder (𝓝[<] t₀) (deriv γ) = limUnder (𝓝[>] t₀) (deriv γ))
    (hL : limUnder (𝓝[>] t₀) (deriv γ) ≠ 0) :
    crossingAngle γ t₀ = Real.pi := by
  rw [crossingAngle, h]
  exact toIcoMod_arg_sub_arg_neg hL

/-- `basepointAngle γ a b` lies in `[0, 2π)`, the range of the model-sector normalization. Its two
projections `basepointAngle_nonneg`/`basepointAngle_lt_two_pi` are the `@[simp]` normal forms. -/
theorem basepointAngle_mem_Ico (γ : ℝ → ℂ) (a b : ℝ) :
    basepointAngle γ a b ∈ Set.Ico 0 (2 * Real.pi) := by
  have h := toIcoMod_mem_Ico Real.two_pi_pos 0
    (Complex.arg (limUnder (𝓝[>] a) (deriv γ)) - Complex.arg (-limUnder (𝓝[<] b) (deriv γ)))
  rw [zero_add] at h
  rw [basepointAngle]
  exact h

@[simp] theorem basepointAngle_nonneg (γ : ℝ → ℂ) (a b : ℝ) : 0 ≤ basepointAngle γ a b :=
  (Set.mem_Ico.mp (basepointAngle_mem_Ico γ a b)).1

@[simp] theorem basepointAngle_lt_two_pi (γ : ℝ → ℂ) (a b : ℝ) :
    basepointAngle γ a b < 2 * Real.pi :=
  (Set.mem_Ico.mp (basepointAngle_mem_Ico γ a b)).2

/-- **Smooth-join value.** If the incoming tangent at `b` and the outgoing tangent at `a` agree and
are nonzero, the basepoint angle is `π`: the closed curve joins smoothly. -/
theorem basepointAngle_eq_pi {γ : ℝ → ℂ} {a b : ℝ}
    (h : limUnder (𝓝[<] b) (deriv γ) = limUnder (𝓝[>] a) (deriv γ))
    (hL : limUnder (𝓝[>] a) (deriv γ) ≠ 0) :
    basepointAngle γ a b = Real.pi := by
  rw [basepointAngle, h]
  exact toIcoMod_arg_sub_arg_neg hL

/-- **Flatness of order `n`** of `γ : ℝ → ℂ` at a time `t₀`, in *parametrized-tangent* form: from
each side there is a one-sided velocity (`t_plus` right, `t_minus` left) with
`‖γ t − (γ t₀ + (t − t₀) • t_plus)‖ = o(‖γ t − γ t₀‖ⁿ)` as `t → t₀⁺`, symmetrically as `t → t₀⁻`
(migrated from AINTLIB). At order `1` for an immersion (nonzero one-sided velocity — any genuine
contour crossing) this is HW's flatness: `γ` has a one-sided tangent. For `n ≥ 2` it is *stricter*
than HW Def. 3.2, measuring deviation from the tangent *line* (orthogonal projection) rather than
the parametrized tangent *point*; the two coincide when the along-tangent speed is linear. Only the
order-`1` case is used below (by `ConditionAprime`). -/
def FlatOfOrder (γ : ℝ → ℂ) (t₀ : ℝ) (n : ℕ) : Prop :=
  ∃ t_plus t_minus : ℂ,
    (fun t => ‖γ t - (γ t₀ + (t - t₀) • t_plus)‖) =o[𝓝[>] t₀] (fun t => ‖γ t - γ t₀‖ ^ n) ∧
    (fun t => ‖γ t - (γ t₀ + (t - t₀) • t_minus)‖) =o[𝓝[<] t₀] (fun t => ‖γ t - γ t₀‖ ^ n)

/-- **Flatness of order `n` at the basepoint** of a closed curve `γ` on `[a, b]`, at the join
`γ a = γ b`: the outgoing branch at `a` (from the right) and the incoming branch at `b` (from the
left) each agree with a one-sided tangent line, up to `o(‖γ t − γ a‖ⁿ)` and `o(‖γ t − γ b‖ⁿ)`
respectively. This is `FlatOfOrder`'s analogue at the basepoint, where the two branches come from
opposite ends of `[a, b]`. -/
def FlatOfOrderBasepoint (γ : ℝ → ℂ) (a b : ℝ) (n : ℕ) : Prop :=
  ∃ t_plus t_minus : ℂ,
    (fun t => ‖γ t - (γ a + (t - a) • t_plus)‖) =o[𝓝[>] a] (fun t => ‖γ t - γ a‖ ^ n) ∧
    (fun t => ‖γ t - (γ b + (t - b) • t_minus)‖) =o[𝓝[<] b] (fun t => ‖γ t - γ b‖ ^ n)

/-- The roadmap's **condition (A′)** target, in transversal (order-`1`) form: `γ` approaches each
prescribed singularity `s ∈ S` **transversally** — flat of order `1` at every time it meets `s` — so
it meets `s` as finitely many model sectors, at each *interior* crossing `t₀ ∈ (a, b)` and at the
*basepoint* `γ a` (`= γ b` for a closed curve), leaving no join singularity free. It is the purely
geometric half of the roadmap's A′/B split (A′ on the set `S`; the analytic data in condition (B)),
and does not refer to `f`.

This order-`1` form is **exact for simple poles**, this development's reach (the valence formula
applies the residue theorem to `f′/f`, whose poles are all simple). It is **not** the full
higher-order HW condition (A′): faithful HW (A) demands flatness of order equal to the *pole
order*, which needs the pole orders of `f`. The roadmap signature `ConditionAprime (γ)(a b)(S)` is
f-free and `S` carries no order data, so that matching cannot be expressed here; supplying it is
a roadmap-signature decision, not settled in this file. -/
structure ConditionAprime (γ : ℝ → ℂ) (a b : ℝ) (S : Finset ℂ) : Prop where
  /-- At each interior time where `γ` meets a prescribed singularity, `γ` crosses transversally,
  i.e. is flat of order `1`. -/
  interior : ∀ t₀ ∈ Set.Ioo a b, γ t₀ ∈ S → FlatOfOrder γ t₀ 1
  /-- If the basepoint `γ a` (`= γ b` for a closed curve) is a prescribed singularity, `γ` meets it
  transversally across the join — the endpoint case the `interior` clause cannot reach. -/
  basepoint : γ a ∈ S → FlatOfOrderBasepoint γ a b 1

/-- Characterization of `ConditionAprime` by its two clauses, for rewriting the hypothesis into the
`interior ∧ basepoint` conjunction (and back via the anonymous constructor). -/
theorem conditionAprime_iff {γ : ℝ → ℂ} {a b : ℝ} {S : Finset ℂ} :
    ConditionAprime γ a b S ↔
      (∀ t₀ ∈ Set.Ioo a b, γ t₀ ∈ S → FlatOfOrder γ t₀ 1) ∧
        (γ a ∈ S → FlatOfOrderBasepoint γ a b 1) :=
  ⟨fun h => ⟨h.interior, h.basepoint⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **Sector compatibility** of `f` at an on-curve singularity `z₀` whose sector opens at angle `θ`
(the Hungerbühler–Wasem condition at one crossing): the angle is a rational multiple of `π` and the
finite Laurent principal part of `f` at `z₀` resonates with `θ` under the sector-cancellation
identity `k · θ ∈ 2π · ℤ`. -/
structure SectorCompatible (f : ℂ → ℂ) (z₀ : ℂ) (θ : ℝ) : Prop where
  /-- The opening angle `θ` is a rational multiple `p·π/q` of `π` (`q ≠ 0`, `p`, `q` coprime). -/
  angle_rational : ∃ p q : ℕ, q ≠ 0 ∧ Nat.Coprime p q ∧ θ = (p : ℝ) * Real.pi / (q : ℝ)
  /-- Near `z₀`, `f` is an analytic remainder plus a finite Laurent principal part whose surviving
  higher-order coefficients (`coeff k ≠ 0`, `k ≥ 1`) resonate with `θ` as `k · θ ∈ 2π · ℤ`. -/
  laurent_compatible : ∃ (N : ℕ) (coeff : Fin N → ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g z₀ ∧
    (∀ᶠ z in 𝓝[≠] z₀, f z = g z + ∑ k : Fin N, coeff k / (z - z₀) ^ (k.val + 1)) ∧
      ∀ k : Fin N, coeff k ≠ 0 → 1 ≤ k.val → ∃ m : ℤ, (k.val : ℝ) * θ = (m : ℝ) * (2 * Real.pi)

/-- Characterization of `SectorCompatible` by its two fields, for rewriting the hypothesis into the
`angle_rational ∧ laurent_compatible` conjunction (and back via the anonymous constructor). -/
theorem sectorCompatible_iff {f : ℂ → ℂ} {z₀ : ℂ} {θ : ℝ} :
    SectorCompatible f z₀ θ ↔
      (∃ p q : ℕ,
        q ≠ 0 ∧ Nat.Coprime p q ∧ θ = (p : ℝ) * Real.pi / (q : ℝ)) ∧
      ∃ (N : ℕ) (coeff : Fin N → ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g z₀ ∧
        (∀ᶠ z in 𝓝[≠] z₀, f z = g z + ∑ k : Fin N, coeff k / (z - z₀) ^ (k.val + 1)) ∧
        ∀ k : Fin N, coeff k ≠ 0 → 1 ≤ k.val →
          ∃ m : ℤ, (k.val : ℝ) * θ = (m : ℝ) * (2 * Real.pi) :=
  ⟨fun h => ⟨h.angle_rational, h.laurent_compatible⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **Hungerbühler–Wasem condition (B)** for `f` along `γ` on `[a, b]`: at each higher-order
on-curve pole of `f` the crossing sector is `SectorCompatible`. Together with condition (A′)
it is a hypothesis of the generalized residue theorem (HW Thm 3.3), where it forces the
order-`> 1` principal parts to cancel, so that the `PV ∮_γ f` the theorem evaluates is
well-defined. Imposed at each *interior* crossing `t₀ ∈ (a, b)` and at the *basepoint* `γ a`
(via `basepointAngle`), so a join singularity `γ a = γ b` is not left free. Higher-order poles
are found intrinsically via `meromorphicOrderAt f (γ t₀) < -1`; simple poles need no sector
condition, so the predicate is `S`-free. -/
structure ConditionB (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) : Prop where
  /-- At each interior higher-order (order `> 1`) on-curve pole of `f`, the crossing sector at
  `γ t₀` is compatible. -/
  interior : ∀ t₀ ∈ Set.Ioo a b, meromorphicOrderAt f (γ t₀) < (-1 : ℤ) →
    SectorCompatible f (γ t₀) (crossingAngle γ t₀)
  /-- If the basepoint `γ a` (`= γ b` for a closed curve) is a higher-order on-curve pole of `f`,
  its join sector is compatible — the endpoint case the `interior` clause cannot reach. -/
  basepoint : meromorphicOrderAt f (γ a) < (-1 : ℤ) →
    SectorCompatible f (γ a) (basepointAngle γ a b)

/-- Characterization of `ConditionB` by its two clauses, for rewriting the hypothesis into the
`interior ∧ basepoint` conjunction (and back via the anonymous constructor). -/
theorem conditionB_iff {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} :
    ConditionB γ a b f ↔
      (∀ t₀ ∈ Set.Ioo a b, meromorphicOrderAt f (γ t₀) < (-1 : ℤ) →
          SectorCompatible f (γ t₀) (crossingAngle γ t₀)) ∧
        (meromorphicOrderAt f (γ a) < (-1 : ℤ) →
          SectorCompatible f (γ a) (basepointAngle γ a b)) :=
  ⟨fun h => ⟨h.interior, h.basepoint⟩, fun h => ⟨h.1, h.2⟩⟩

end TauCeti.Contour
