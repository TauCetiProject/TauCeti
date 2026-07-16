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
public import Mathlib.Algebra.Order.ToIntervalMod

/-!
# The Hungerbühler–Wasem crossing angle and regularity conditions (A′) and (B)

For a curve `γ : ℝ → ℂ` on `[a, b]` and an integrand `f : ℂ → ℂ`, this file defines the **crossing
angle** and the **flatness** of `γ` at a time, and the roadmap's two Hungerbühler–Wasem regularity
conditions at its on-curve singularities: the geometric flatness condition **(A′)** and the analytic
sector-cancellation condition **(B)**, the two regularity hypotheses of the generalized residue
theorem (HW Thm 3.3), evaluating the Cauchy principal value `PV ∮_γ f`. Condition (A′) asks that
at each prescribed singularity `s ∈ S` the curve `γ` be **flat of order equal to the order of `f`'s
pole there** — with a one-sided tangent line at a simple pole, hugged ever tighter at a higher-order
pole — and that it meet each `s` only finitely often. Condition (B) governs poles of order
`> 1`, coupling the Laurent principal part of `f` at each such pole with the entry/exit tangents of
`γ` there, via a sector-cancellation identity; simple poles need no sector condition.

## Main definitions

* `crossingAngle γ t₀` — the model-sector opening angle in `[0, 2π)`, from the reversed entry
  tangent `−L₋` to the exit tangent `L₊` (`mod 2π`), where `L₋`, `L₊` are the one-sided limits of
  `deriv γ` from the left and right at `t₀`. Junk when a one-sided tangent fails to exist; a smooth
  crossing gives `π` (`crossingAngle_eq_pi`). Meaningful at the corners/crossings of a
  piecewise-`C¹` curve.
* `basepointAngle γ a b` — the analogous opening angle at the join `γ a = γ b` of a closed curve,
  from the reversed incoming tangent at `b` to the outgoing tangent at `a`.
* `FlatOfOrder γ t₀ n` — `γ` is **flat of order `n`** at `t₀` (HW Def. 3.2): from each side the
  perpendicular distance from `γ t` to a one-sided tangent line at `γ t₀` is `o(‖γ t − γ t₀‖ⁿ)`.
  Order `1` gives a one-sided tangent line; larger `n` hugs the line more tightly.
* `FlatOfOrderBasepoint γ a b n` — the analogue at the join `γ a = γ b` of a closed curve, for the
  outgoing branch at `a` (from the right) and the incoming branch at `b` (from the left).
* `ConditionAprime γ a b f S` — HW condition (A′), a structure requiring `γ` to meet each `s ∈ S`
  finitely often (`finite_crossings`) and be flat of order `n` wherever `f` has a pole of order `n`
  there (`interior`, `basepoint`). Pole orders come from `f` via `meromorphicOrderAt`; `S` selects
  the singularities.
* `SectorCompatible f z₀ θ` — the one-crossing Hungerbühler–Wasem sector condition, a structure with
  fields `angle_rational` (`θ` is a rational multiple of `π`) and `laurent_compatible` (the Laurent
  principal part of `f` at `z₀` resonates with `θ`).
* `ConditionB γ a b f` — HW condition (B), a structure imposing `SectorCompatible` at every
  higher-order (order `> 1`) on-curve pole of `f`: at each interior crossing (`ConditionB.interior`)
  and at the basepoint (`ConditionB.basepoint`).

Both conditions read the on-curve pole orders of `f` from `meromorphicOrderAt`. Condition (B) needs
no explicit singular set — it fires **intrinsically** at the times `t₀` where
`meromorphicOrderAt f (γ t₀) < -1` (a pole of order `> 1`), so it is `S`-free. Condition (A′) is
imposed at the prescribed set `S` (selecting the singularities), with the required flatness order
taken from `f`. Both match the roadmap signatures and the way the residue theorem consumes them.

## Provenance

Migrated and adapted from the AINTLIB `LeanModularForms` project (`angleAtCrossing`, `FlatOfOrder`,
and `SatisfiesConditionB`), specialised to the raw-function (`γ : ℝ → ℂ` on `[a, b]`) design of the
contour-integration roadmap. `FlatOfOrder` here uses HW Def. 3.2's tangent-*line* (orthogonal
projection) distance, so it is speed-independent at every order. Condition (A′) matches the flatness
order to `f`'s pole order at each `s ∈ S`; condition (B) detects the higher-order poles of
`f` intrinsically via `meromorphicOrderAt`.

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

/-- **Flatness of order `n`** of `γ : ℝ → ℂ` at `t₀` (HW Def. 3.2): from each side, `γ` hugs a
one-sided **tangent line** through `γ t₀`, its perpendicular distance to that line vanishing faster
than `‖γ t − γ t₀‖ⁿ`. There are nonzero one-sided directions `v_plus` (right) and `v_minus` (left)
for which the component of `γ t − γ t₀` orthogonal to `v` — of length
`|((γ t − γ t₀) · conj v).im| / ‖v‖`, the distance from `γ t` to the line `γ t₀ + ℝ • v` — is
`o(‖γ t − γ t₀‖ⁿ)` as `t → t₀⁺`, symmetrically as `t → t₀⁻`. Order `1` is first-order tangency to a
line; larger `n` forces it to hug the line ever more tightly. Distance is measured to the tangent
*line*, not to a moving point on it, so flatness ignores the along-tangent speed, as in HW. -/
def FlatOfOrder (γ : ℝ → ℂ) (t₀ : ℝ) (n : ℕ) : Prop :=
  ∃ v_plus v_minus : ℂ, v_plus ≠ 0 ∧ v_minus ≠ 0 ∧
    (fun t => |((γ t - γ t₀) * star v_plus).im| / ‖v_plus‖)
        =o[𝓝[>] t₀] (fun t => ‖γ t - γ t₀‖ ^ n) ∧
    (fun t => |((γ t - γ t₀) * star v_minus).im| / ‖v_minus‖)
        =o[𝓝[<] t₀] (fun t => ‖γ t - γ t₀‖ ^ n)

/-- **Flatness of order `n` at the basepoint** of a closed curve `γ` on `[a, b]`, at the join
`γ a = γ b`: the outgoing branch at `a` (from the right) and the incoming branch at `b` (from the
left) each hug their one-sided tangent line in the perpendicular sense of `FlatOfOrder`, to order
`n`. The two branches come from opposite ends of `[a, b]`. -/
def FlatOfOrderBasepoint (γ : ℝ → ℂ) (a b : ℝ) (n : ℕ) : Prop :=
  ∃ v_plus v_minus : ℂ, v_plus ≠ 0 ∧ v_minus ≠ 0 ∧
    (fun t => |((γ t - γ a) * star v_plus).im| / ‖v_plus‖) =o[𝓝[>] a] (fun t => ‖γ t - γ a‖ ^ n) ∧
    (fun t => |((γ t - γ b) * star v_minus).im| / ‖v_minus‖) =o[𝓝[<] b] (fun t => ‖γ t - γ b‖ ^ n)

/-- `FlatOfOrder` unfolded: the one-sided little-o clauses that build the flatness hypothesis, so
downstream code can construct or destruct it without unfolding the definition. -/
theorem flatOfOrder_iff {γ : ℝ → ℂ} {t₀ : ℝ} {n : ℕ} :
    FlatOfOrder γ t₀ n ↔
      ∃ v_plus v_minus : ℂ, v_plus ≠ 0 ∧ v_minus ≠ 0 ∧
        (fun t => |((γ t - γ t₀) * star v_plus).im| / ‖v_plus‖)
            =o[𝓝[>] t₀] (fun t => ‖γ t - γ t₀‖ ^ n) ∧
        (fun t => |((γ t - γ t₀) * star v_minus).im| / ‖v_minus‖)
            =o[𝓝[<] t₀] (fun t => ‖γ t - γ t₀‖ ^ n) :=
  Iff.rfl

/-- `FlatOfOrderBasepoint` unfolded: the two one-sided little-o clauses (outgoing at `a`, incoming
at `b`) that build the basepoint flatness hypothesis, exposed without unfolding the definition. -/
theorem flatOfOrderBasepoint_iff {γ : ℝ → ℂ} {a b : ℝ} {n : ℕ} :
    FlatOfOrderBasepoint γ a b n ↔
      ∃ v_plus v_minus : ℂ, v_plus ≠ 0 ∧ v_minus ≠ 0 ∧
        (fun t => |((γ t - γ a) * star v_plus).im| / ‖v_plus‖)
            =o[𝓝[>] a] (fun t => ‖γ t - γ a‖ ^ n) ∧
        (fun t => |((γ t - γ b) * star v_minus).im| / ‖v_minus‖)
            =o[𝓝[<] b] (fun t => ‖γ t - γ b‖ ^ n) :=
  Iff.rfl

/-- **Hungerbühler–Wasem condition (A′)** for `γ` along `[a, b]`, at the prescribed singular set `S`
of the integrand `f`: `γ` meets each singularity only **finitely often** and is **flat** to the
order of `f`'s pole there. Wherever `γ` meets a point of `S` at which `f` has a pole of order `n`,
the curve is flat of order `n` — tangent to a line at a simple pole, flatter at a higher pole — and
each such `s` is met only finitely often. Together with
condition (B) it is a regularity hypothesis of the generalized residue theorem (HW Thm 3.3). It is
imposed at each *interior* crossing `t₀` strictly between the endpoints and at the *basepoint*
`γ (min a b)` (`= γ (max a b)` for a closed curve), so a join singularity is not left free. The
clauses are stated over `min`/`max`, so the condition is invariant under swapping the endpoints
(`conditionAprime_comm`), like the curve predicates it accompanies. Pole orders are read from
`f` via `meromorphicOrderAt`; `S` selects the singularities to constrain. -/
structure ConditionAprime (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) (S : Finset ℂ) : Prop where
  /-- Each prescribed singularity `s ∈ S` is met only **finitely often** on `[[a, b]]`: the
  crossing set `[[a, b]] ∩ γ ⁻¹' {s}` is finite. -/
  finite_crossings : ∀ s ∈ S, (Set.uIcc a b ∩ γ ⁻¹' {s}).Finite
  /-- At each interior crossing of a prescribed singularity where `f` has a pole of order `n`, the
  curve `γ` is flat of order `n`. -/
  interior : ∀ t₀ ∈ Set.Ioo (min a b) (max a b), γ t₀ ∈ S → ∀ n : ℕ, 1 ≤ n →
    meromorphicOrderAt f (γ t₀) = (-(n : ℤ) : WithTop ℤ) → FlatOfOrder γ t₀ n
  /-- If the basepoint `γ (min a b)` (`= γ (max a b)` for a closed curve) is a prescribed
  singularity where `f` has a pole of order `n`, then `γ` is flat of order `n` across the
  join. -/
  basepoint : γ (min a b) ∈ S → ∀ n : ℕ, 1 ≤ n →
    meromorphicOrderAt f (γ (min a b)) = (-(n : ℤ) : WithTop ℤ) →
      FlatOfOrderBasepoint γ (min a b) (max a b) n

/-- Characterization of `ConditionAprime` by its three clauses, for rewriting the hypothesis into
the `finite_crossings ∧ interior ∧ basepoint` conjunction (and back via the anonymous constructor).
-/
theorem conditionAprime_iff {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {S : Finset ℂ} :
    ConditionAprime γ a b f S ↔
      (∀ s ∈ S, (Set.uIcc a b ∩ γ ⁻¹' {s}).Finite) ∧
      (∀ t₀ ∈ Set.Ioo (min a b) (max a b), γ t₀ ∈ S → ∀ n : ℕ, 1 ≤ n →
          meromorphicOrderAt f (γ t₀) = (-(n : ℤ) : WithTop ℤ) → FlatOfOrder γ t₀ n) ∧
        (γ (min a b) ∈ S → ∀ n : ℕ, 1 ≤ n →
          meromorphicOrderAt f (γ (min a b)) = (-(n : ℤ) : WithTop ℤ) →
          FlatOfOrderBasepoint γ (min a b) (max a b) n) :=
  ⟨fun h => ⟨h.finite_crossings, h.interior, h.basepoint⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- Condition (A′) is invariant under swapping the endpoints: all its clauses are stated over
`min`/`max`. -/
theorem conditionAprime_comm {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {S : Finset ℂ} :
    ConditionAprime γ a b f S ↔ ConditionAprime γ b a f S := by
  rw [conditionAprime_iff, conditionAprime_iff, Set.uIcc_comm, min_comm a b, max_comm a b]

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
well-defined. Imposed at each *interior* crossing `t₀` strictly between the endpoints and at
the *basepoint* `γ (min a b)` (via `basepointAngle`), so a join singularity is not left free;
stated over `min`/`max`, the condition is invariant under swapping the endpoints
(`conditionB_comm`). Higher-order poles are found intrinsically via
`meromorphicOrderAt f (γ t₀) < -1`; simple poles need no sector
condition, so the predicate is `S`-free. -/
structure ConditionB (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) : Prop where
  /-- At each interior higher-order (order `> 1`) on-curve pole of `f`, the crossing sector at
  `γ t₀` is compatible. -/
  interior : ∀ t₀ ∈ Set.Ioo (min a b) (max a b), meromorphicOrderAt f (γ t₀) < (-1 : ℤ) →
    SectorCompatible f (γ t₀) (crossingAngle γ t₀)
  /-- If the basepoint `γ (min a b)` (`= γ (max a b)` for a closed curve) is a higher-order
  on-curve pole of `f`, its join sector is compatible — the endpoint case the `interior` clause
  cannot reach. -/
  basepoint : meromorphicOrderAt f (γ (min a b)) < (-1 : ℤ) →
    SectorCompatible f (γ (min a b)) (basepointAngle γ (min a b) (max a b))

/-- Characterization of `ConditionB` by its two clauses, for rewriting the hypothesis into the
`interior ∧ basepoint` conjunction (and back via the anonymous constructor). -/
theorem conditionB_iff {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} :
    ConditionB γ a b f ↔
      (∀ t₀ ∈ Set.Ioo (min a b) (max a b), meromorphicOrderAt f (γ t₀) < (-1 : ℤ) →
          SectorCompatible f (γ t₀) (crossingAngle γ t₀)) ∧
        (meromorphicOrderAt f (γ (min a b)) < (-1 : ℤ) →
          SectorCompatible f (γ (min a b)) (basepointAngle γ (min a b) (max a b))) :=
  ⟨fun h => ⟨h.interior, h.basepoint⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Condition (B) is invariant under swapping the endpoints: both its clauses are stated over
`min`/`max`. -/
theorem conditionB_comm {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} :
    ConditionB γ a b f ↔ ConditionB γ b a f := by
  rw [conditionB_iff, conditionB_iff, min_comm a b, max_comm a b]

end TauCeti.Contour
