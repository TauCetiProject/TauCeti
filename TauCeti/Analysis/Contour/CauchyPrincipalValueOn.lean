/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.CauchyPrincipalValue

/-!
# The Cauchy principal value of a contour integral on a set (Hungerbühler–Wasem)

For a curve `γ : ℝ → ℂ` on `[a, b]` and an integrand `f : ℂ → ℂ`, this file defines the **Cauchy
principal value** of the contour integral `∮_γ f` *excising a symmetric `ε`-ball about each point of
a finite singular set simultaneously*: `HasCauchyPV γ a b f v` says there is a finite set `S ⊆ ℂ`
for which the truncated integrand along `γ` over `[a, b]`, zeroed within `ε` of any point of `S`, is
eventually `IntervalIntegrable` and its integral tends to `v` as `ε → 0⁺`.

This is the set-level (`…On`) companion of `HasCauchyPVAt` (`CauchyPrincipalValue.lean`), which
excises a single prescribed point `z₀`; the naming mirrors Mathlib's `MeromorphicAt` (at a point)
versus `MeromorphicOn` (on a set). The singular set `S` is bound **existentially**, so the predicate
is intrinsic to `(γ, f)` and stays faithful to the roadmap's `S`-free signature: it holds when
*some* finite excision set satisfies the two clauses. Any prescribed set (for instance the pole set
`S` in the generalized residue theorem, whose value is `2πi · ∑_{s ∈ S} n_γ(s) · res f s`) witnesses
the existential directly. Morally one covers the on-curve singularities of `f`, enlarging past them
being inert as `ε → 0⁺`; but that inertness is a downstream result and is not established here.

As with `HasCauchyPVAt`, the predicate carries a truncated-**integrability** clause alongside the
`Tendsto` clause. Without it the `Tendsto` clause alone would be met vacuously by integrands whose
truncations are non-integrable, since a Bochner interval integral of a non-integrable function is
`0` by convention. This keeps the principal value honest and separate from ordinary integrability
of `f` (which fails at an on-curve singularity), never silently identifying the two.

## Main definitions

* `HasCauchyPV γ a b f v` — some finite excision set makes the truncated integrals converge to `v`
  (the primary predicate).
* `CauchyPVExists γ a b f` — the principal value exists (`∃ v, HasCauchyPV γ a b f v`).

## Main results

* `hasCauchyPV_iff`, `cauchyPVExists_iff` — restate the predicates as their defining existentials,
  so consumers can characterize them without unfolding the definitions.
* `HasCauchyPV.intro` builds the predicate from a witnessing set `S` and its two clauses, while
  `CauchyPVExists.intro` builds existence from a `HasCauchyPV` witness.
* `HasCauchyPVAt.hasCauchyPV`, `CauchyPVExistsAt.cauchyPVExists` — the single-point principal value
  at `z₀` is the set-level principal value with `S = {z₀}`: the excision `‖γ t − z₀‖ > ε` is exactly
  the `S = {z₀}` case of the set excision.
* `HasCauchyPV.of_integrable` — if the ordinary contour integrand is interval-integrable, the empty
  excision witnesses that the principal value is the ordinary integral (as when no on-curve
  singularity of `f` obstructs integrability).
* `HasCauchyPV.zero`, `HasCauchyPV.const_mul`, `HasCauchyPV.congr_along_curve` (and their
  `CauchyPVExists` forms) — the excision-set-preserving operations: the zero integrand, scaling by a
  constant, and replacing `f` by a function agreeing with it along `γ`. These need no change of the
  witnessing set; the multi-point `add`/`sum`/uniqueness API, which requires reconciling *different*
  excision sets (an enlargement-inertness argument), is deferred to a follow-up.

## Provenance

Migrated and adapted from the AINTLIB `LeanModularForms` project (the multi-point principal value
`CauchyPrincipalValueExistsOn`), specialised to the raw-function (`γ : ℝ → ℂ` on `[a, b]`) design of
the contour-integration roadmap, with the singular set bound existentially and the
truncated-integrability clause added.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

/-- The **Cauchy principal value on a set** of the contour integral `∮_γ f` exists with value `v`:
there is a finite set `S ⊆ ℂ` such that the truncated integrand along `γ` over `[a, b]`, zeroed
within a symmetric `ε`-ball of any point of `S`, is eventually `IntervalIntegrable` and its integral
tends to `v` as `ε → 0⁺`. The set is existential so the predicate stays `S`-free, intrinsic to
`(γ, f)`; the integrability clause prevents the `Tendsto` clause from being met vacuously through
the convention that a Bochner integral of a non-integrable function is `0`. Set-level companion of
`HasCauchyPVAt` (raw `γ : ℝ → ℂ`, `[a, b]`). -/
def HasCauchyPV (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) (v : ℂ) : Prop :=
  ∃ S : Finset ℂ,
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
        (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
        MeasureTheory.volume a b) ∧
      Tendsto (fun ε ↦ ∫ t in a..b, if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
        (𝓝[>] 0) (𝓝 v)

/-- Restatement of `HasCauchyPV` as the existence of a finite excision set making the excised
integrand eventually integrable and its integrals convergent, so consumers can characterize the
predicate without unfolding its definition. -/
theorem hasCauchyPV_iff {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {v : ℂ} :
    HasCauchyPV γ a b f v ↔
      ∃ S : Finset ℂ,
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
            (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
            MeasureTheory.volume a b) ∧
          Tendsto (fun ε ↦ ∫ t in a..b, if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
            (𝓝[>] 0) (𝓝 v) :=
  Iff.rfl

/-- Constructor for `HasCauchyPV` from a witnessing finite set `S` and its two clauses — eventual
integrability of the `S`-excised integrand and convergence of the excised integrals — without
unfolding the definition. -/
theorem HasCauchyPV.intro {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {v : ℂ} (S : Finset ℂ)
    (h_int : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
        (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
        MeasureTheory.volume a b)
    (h_tendsto : Tendsto
        (fun ε ↦ ∫ t in a..b, if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
        (𝓝[>] 0) (𝓝 v)) :
    HasCauchyPV γ a b f v :=
  ⟨S, h_int, h_tendsto⟩

/-- The Cauchy principal value on a set exists: shorthand for `∃ v, HasCauchyPV γ a b f v`. -/
def CauchyPVExists (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ v : ℂ, HasCauchyPV γ a b f v

/-- Characterization of `CauchyPVExists` as the existence of a principal value — the
eliminator/constructor interface, so downstream users need not unfold the definition. -/
theorem cauchyPVExists_iff {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} :
    CauchyPVExists γ a b f ↔ ∃ v, HasCauchyPV γ a b f v :=
  Iff.rfl

/-- Constructor for `CauchyPVExists` from a `HasCauchyPV` witness. -/
theorem CauchyPVExists.intro {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {v : ℂ}
    (h : HasCauchyPV γ a b f v) : CauchyPVExists γ a b f :=
  ⟨v, h⟩

/-- **From a point to a set.** The single-point principal value at `z₀` is the set-level principal
value with `S = {z₀}`: the single-point excision `‖γ t − z₀‖ > ε` (keep) is exactly the negation of
the set excision `∃ s ∈ {z₀}, ‖γ t − s‖ ≤ ε` (zero). -/
theorem HasCauchyPVAt.hasCauchyPV {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) : HasCauchyPV γ a b f L := by
  have hbody : ∀ (ε : ℝ) (t : ℝ),
      (if ∃ s ∈ ({z₀} : Finset ℂ), ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
        = if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0 := by
    intro ε t
    simp only [Finset.mem_singleton, exists_eq_left]
    by_cases h' : ‖γ t - z₀‖ ≤ ε
    · rw [if_pos h', if_neg (not_lt.mpr h')]
    · rw [if_neg h', if_pos (not_le.mp h')]
  refine ⟨{z₀}, ?_, ?_⟩
  · filter_upwards [h.eventually_intervalIntegrable] with ε hε
    exact (intervalIntegrable_congr fun t _ => hbody ε t).mpr hε
  · refine h.tendsto.congr fun ε => ?_
    exact (intervalIntegral.integral_congr fun t _ => hbody ε t).symm

/-- Existence form of `HasCauchyPVAt.hasCauchyPV`: if the single-point principal value at `z₀`
exists, so does the set-level principal value. -/
theorem CauchyPVExistsAt.cauchyPVExists {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ a b f z₀) : CauchyPVExists γ a b f :=
  let ⟨_, hL⟩ := cauchyPVExistsAt_iff.mp h
  ⟨_, hL.hasCauchyPV⟩

/-- **Integrable integrand.** If the ordinary contour integrand `t ↦ f (γ t) · γ'(t)` is
`IntervalIntegrable` on `[a, b]`, then the empty excision (`S = ∅`) is inert, so the principal value
exists and equals the ordinary contour integral `∫_a^b f (γ t) · γ'(t) dt`. This applies in
particular when no singularity of `f` lies on `γ`, which is what secures the integrability. -/
theorem HasCauchyPV.of_integrable {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    (hf_int : IntervalIntegrable (fun t => f (γ t) * deriv γ t) MeasureTheory.volume a b) :
    HasCauchyPV γ a b f (∫ t in a..b, f (γ t) * deriv γ t) := by
  refine ⟨∅, ?_, ?_⟩
  · filter_upwards with ε
    simpa using hf_int
  · refine tendsto_const_nhds.congr fun ε => ?_
    exact intervalIntegral.integral_congr fun t _ => by simp

/-- **Zero integrand.** The principal value of the zero integrand is `0`, witnessed by the empty
excision: the truncated integrand is identically `0`, hence integrable with vanishing integral. -/
theorem HasCauchyPV.zero {γ : ℝ → ℂ} {a b : ℝ} : HasCauchyPV γ a b (fun _ => 0) 0 := by
  refine ⟨∅, ?_, ?_⟩
  · filter_upwards with ε
    simp
  · simp

/-- **Scaling by a constant.** Scaling the integrand by `c : ℂ` scales the principal value by `c`,
reusing the same excision set: the truncation and the integral both commute with multiplication by
the constant `c`. -/
theorem HasCauchyPV.const_mul {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {v : ℂ}
    (h : HasCauchyPV γ a b f v) (c : ℂ) : HasCauchyPV γ a b (fun z => c * f z) (c * v) := by
  obtain ⟨S, hint, htend⟩ := h
  have hbody : ∀ (ε : ℝ) (t : ℝ),
      (if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else (fun z => c * f z) (γ t) * deriv γ t)
        = c * (if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t) := by
    intro ε t
    by_cases hc : ∃ s ∈ S, ‖γ t - s‖ ≤ ε
    · simp [hc]
    · simp [hc, mul_assoc]
  refine ⟨S, ?_, ?_⟩
  · filter_upwards [hint] with ε hε
    exact (intervalIntegrable_congr fun t _ => hbody ε t).mpr (hε.const_mul c)
  · refine (htend.const_mul c).congr fun ε => ?_
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => (hbody ε t).symm

/-- **Congruence along the curve.** If `f` and `g` agree along `γ` on the open interval `Set.uIoo a
b`, they share the same principal value there, with the same excision set (the endpoints are
invisible to the interval integral; the excised integrand reads `f` only through `f (γ t)`). -/
theorem HasCauchyPV.congr_along_curve {γ : ℝ → ℂ} {a b : ℝ} {f g : ℂ → ℂ} {v : ℂ}
    (h : HasCauchyPV γ a b f v) (hfg : ∀ t ∈ Set.uIoo a b, f (γ t) = g (γ t)) :
    HasCauchyPV γ a b g v := by
  obtain ⟨S, hint, htend⟩ := h
  have hbody : ∀ ε : ℝ, ∀ t ∈ Set.uIoo a b,
      (if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
        = if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else g (γ t) * deriv γ t := by
    intro ε t ht
    by_cases hc : ∃ s ∈ S, ‖γ t - s‖ ≤ ε
    · simp [hc]
    · simp [hc, hfg t ht]
  refine ⟨S, ?_, ?_⟩
  · filter_upwards [hint] with ε hε
    exact (intervalIntegrable_congr_uIoo fun t ht => hbody ε t ht).mp hε
  · refine htend.congr fun ε => ?_
    exact intervalIntegral.integral_congr_uIoo fun t ht => hbody ε t ht

/-- Existence form of `HasCauchyPV.zero`: the principal value of the zero integrand exists. -/
theorem CauchyPVExists.zero {γ : ℝ → ℂ} {a b : ℝ} : CauchyPVExists γ a b (fun _ => 0) :=
  .intro HasCauchyPV.zero

/-- Existence form of `HasCauchyPV.const_mul`: if the principal value of `f` exists, so does that of
`fun z => c * f z`. -/
theorem CauchyPVExists.const_mul {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    (h : CauchyPVExists γ a b f) (c : ℂ) : CauchyPVExists γ a b (fun z => c * f z) :=
  let ⟨_, hv⟩ := cauchyPVExists_iff.mp h
  ⟨_, hv.const_mul c⟩

/-- Existence form of `HasCauchyPV.congr_along_curve`: agreement along `γ` on `Set.uIoo a b`
transports existence of the principal value from `f` to `g`. -/
theorem CauchyPVExists.congr_along_curve {γ : ℝ → ℂ} {a b : ℝ} {f g : ℂ → ℂ}
    (h : CauchyPVExists γ a b f) (hfg : ∀ t ∈ Set.uIoo a b, f (γ t) = g (γ t)) :
    CauchyPVExists γ a b g :=
  let ⟨_, hv⟩ := cauchyPVExists_iff.mp h
  ⟨_, hv.congr_along_curve hfg⟩

end TauCeti.Contour
