/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact

/-!
# The Cauchy principal value of a contour integral at a point (Hungerbühler–Wasem)

For a curve `γ : ℝ → ℂ` on `[a, b]`, an integrand `f : ℂ → ℂ`, and a point `z₀ ∈ ℂ`, this file
defines the **Cauchy principal value** of the contour integral `∮_γ f` *excising a symmetric
`ε`-ball about `z₀`*: the limit as `ε → 0⁺` of the truncated integral
`∫_a^b 𝟙[‖γ t − z₀‖ > ε] · f (γ t) · γ'(t) dt`. This is the value one must use in place of the
ordinary contour integral exactly when a singularity of `f` sits *on* the curve at `z₀`, where the
integrand is not integrable; away from `z₀` the truncation is eventually inert and the principal
value collapses to the ordinary integral (`HasCauchyPVAt.of_avoidance`).

The predicate carries **two** conditions: that the truncated integrand is (eventually) genuinely
`IntervalIntegrable`, and that the truncated integrals converge. The integrability clause is
essential: without it the `Tendsto` clause alone is met vacuously by functions whose truncations are
non-integrable, since a Bochner interval integral of a non-integrable function is `0` by convention.
This keeps the principal value honest and separate from ordinary integrability of `f` (which fails
at the on-curve singularity), never silently identifying the two.

This is the single-point companion of the roadmap's `HasCauchyPV` predicate: `HasCauchyPVAt`
symmetrically excises one prescribed point `z₀`, the case that defines the generalized winding
number `n_{z₀}(γ) = (2πi)⁻¹ · PV ∮_γ dz/(z − z₀)` and that feeds the on-curve residue theory
(Hungerbühler–Wasem, arXiv:1808.00997). The naming mirrors Mathlib's `MeromorphicAt` (at a point)
versus `MeromorphicOn` (on a set).

## Main definitions

* `HasCauchyPVAt γ a b f z₀ L` — the truncations are eventually integrable and their integrals tend
  to `L` (the primary predicate).
* `cauchyPVAt γ a b f z₀` — the value of that limit (`limUnder`-based; junk when it does not exist).
* `CauchyPVExistsAt γ a b f z₀` — the principal value exists (`∃ L, HasCauchyPVAt γ a b f z₀ L`).

## Main results

* `hasCauchyPVAt_iff` — restates the predicate as its two defining clauses, so consumers can
  characterize `HasCauchyPVAt` without unfolding its hidden body; the value `cauchyPVAt` is read off
  a witness through `HasCauchyPVAt.cauchyPVAt_eq`.
* `HasCauchyPVAt.intro` — build the predicate from its two clauses; `HasCauchyPVAt.tendsto`,
  `HasCauchyPVAt.eventually_intervalIntegrable` — the clauses as named accessors;
  `HasCauchyPVAt.cauchyPVAt_eq`, `HasCauchyPVAt.unique` — the value and its uniqueness;
  `cauchyPVExistsAt_iff`, `CauchyPVExistsAt.intro`, `CauchyPVExistsAt.hasCauchyPVAt_cauchyPVAt` —
  package/unpack existence and recover the predicate at `cauchyPVAt`.
* `HasCauchyPVAt.congr_along_curve` — the integrand only matters along `γ` on `[a, b]`;
  `HasCauchyPVAt.zero`, `HasCauchyPVAt.const_mul`, `HasCauchyPVAt.add`, `HasCauchyPVAt.sum` (and the
  `CauchyPVExistsAt` forms) — the principal value is `ℂ`-linear in the integrand, including over
  finite sums.
* `HasCauchyPVAt.of_avoidance` — if `γ` avoids `z₀` on `[a, b]` and the integrand is integrable
  there, the principal value is the ordinary integral (`cauchyPVExistsAt_of_avoidance` is the
  existence form).
* `HasCauchyPVAt.symm`, `CauchyPVExistsAt.symm`, `cauchyPVAt_symm` — reversing the interval
  orientation negates the single-point principal value.
* `HasCauchyPVAt.concat` — the principal values on `[a, b]` and `[b, c]` add
  (`CauchyPVExistsAt.concat` is the existence form).

## Provenance

Migrated and adapted from the AINTLIB `LeanModularForms` project, file
`ForMathlib/ClassicalCPV.lean`, specialised to the raw-function (`γ : ℝ → ℂ` on `[a, b]`) design of
the contour-integration roadmap, and strengthened with the truncated-integrability clause.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

/-- The **Cauchy principal value at `z₀`** of the contour integral `∮_γ f` exists with value `L`:
the truncated integrand along `γ` over `[a, b]`, excluding the symmetric `ε`-ball about `z₀`, is
eventually `IntervalIntegrable`, and its integral tends to `L` as `ε → 0⁺`. The integrability clause
prevents the `Tendsto` clause from being met vacuously through the convention that a Bochner
integral of a non-integrable function is `0`. Primary API predicate (raw `γ : ℝ → ℂ`, `[a, b]`). -/
def HasCauchyPVAt (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) (L : ℂ) : Prop :=
  (∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) MeasureTheory.volume a b) ∧
    Tendsto (fun ε ↦ ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
      (𝓝[>] 0) (𝓝 L)

/-- Restatement of `HasCauchyPVAt` as the conjunction of its two defining clauses — eventual
integrability of the excised integrand and convergence of the excised integrals — so consumers can
characterize the predicate without unfolding its definition. -/
theorem hasCauchyPVAt_iff {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ} :
    HasCauchyPVAt γ a b f z₀ L ↔
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
          (fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) MeasureTheory.volume a b) ∧
        Tendsto (fun ε ↦ ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
          (𝓝[>] 0) (𝓝 L) :=
  Iff.rfl

/-- The **Cauchy principal value at `z₀`** of `∮_γ f`, excluding the symmetric `ε`-ball about `z₀`.
`limUnder`-based; returns junk when the limit does not exist, so use `HasCauchyPVAt` for the
predicate and `HasCauchyPVAt.cauchyPVAt_eq` to read the value off it. -/
def cauchyPVAt (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε ↦
    ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0

/-- The Cauchy principal value at `z₀` exists: shorthand for `∃ L, HasCauchyPVAt γ a b f z₀ L`. -/
def CauchyPVExistsAt (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∃ L : ℂ, HasCauchyPVAt γ a b f z₀ L

/-- Characterization of `CauchyPVExistsAt` as the existence of a principal value — the
eliminator/constructor interface, so downstream users need not unfold the definition. -/
theorem cauchyPVExistsAt_iff {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} :
    CauchyPVExistsAt γ a b f z₀ ↔ ∃ L, HasCauchyPVAt γ a b f z₀ L :=
  Iff.rfl

/-- Constructor for `CauchyPVExistsAt` from a `HasCauchyPVAt` witness. -/
theorem CauchyPVExistsAt.intro {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) : CauchyPVExistsAt γ a b f z₀ :=
  ⟨L, h⟩

/-- Constructor for `HasCauchyPVAt` from its two clauses — eventual integrability of the excised
integrand and convergence of the excised integrals — without unfolding the definition. -/
theorem HasCauchyPVAt.intro {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (hint : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) MeasureTheory.volume a b)
    (htendsto : Tendsto
      (fun ε ↦ ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) (𝓝[>] 0) (𝓝 L)) :
    HasCauchyPVAt γ a b f z₀ L :=
  ⟨hint, htendsto⟩

/-- The convergence clause of `HasCauchyPVAt`: the excised integrals tend to the value. -/
theorem HasCauchyPVAt.tendsto {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) :
    Tendsto (fun ε ↦ ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
      (𝓝[>] 0) (𝓝 L) :=
  h.2

/-- The integrability clause of `HasCauchyPVAt`: the excised integrand is eventually integrable. -/
theorem HasCauchyPVAt.eventually_intervalIntegrable {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    {L : ℂ} (h : HasCauchyPVAt γ a b f z₀ L) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) MeasureTheory.volume a b :=
  h.1

/-- If `HasCauchyPVAt γ a b f z₀ L`, then `cauchyPVAt γ a b f z₀ = L`: the value function reads off
the limit whenever it exists. -/
theorem HasCauchyPVAt.cauchyPVAt_eq {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) : cauchyPVAt γ a b f z₀ = L :=
  h.2.limUnder_eq

/-- The value of the Cauchy principal value at `z₀` is unique. -/
theorem HasCauchyPVAt.unique {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L₁ L₂ : ℂ}
    (h₁ : HasCauchyPVAt γ a b f z₀ L₁) (h₂ : HasCauchyPVAt γ a b f z₀ L₂) : L₁ = L₂ :=
  tendsto_nhds_unique h₁.2 h₂.2

/-- If the principal value exists, it holds at the canonical value `cauchyPVAt`. This recovers a
`HasCauchyPVAt` statement from mere existence, as the winding-number value definition needs. -/
theorem CauchyPVExistsAt.hasCauchyPVAt_cauchyPVAt {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ a b f z₀) :
    HasCauchyPVAt γ a b f z₀ (cauchyPVAt γ a b f z₀) := by
  obtain ⟨_, hL⟩ := h
  rwa [hL.cauchyPVAt_eq]

/-- The principal value depends on the integrand only through its values along `γ` on the open
interval between `a` and `b`: if `f = g` on the image of `γ` restricted to `Set.uIoo a b`, their
principal values agree (endpoint values are invisible to the interval integral). -/
theorem HasCauchyPVAt.congr_along_curve {γ : ℝ → ℂ} {a b : ℝ} {f g : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) (h_eq : ∀ t ∈ Set.uIoo a b, f (γ t) = g (γ t)) :
    HasCauchyPVAt γ a b g z₀ L := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1] with ε hε
    refine (intervalIntegrable_congr_uIoo fun t ht => ?_).mp hε
    simp only [h_eq t ht]
  · refine Filter.Tendsto.congr (fun ε => intervalIntegral.integral_congr_uIoo fun t ht => ?_) h.2
    simp only [h_eq t ht]

/-- Scalar multiplication: if the principal value of `f` is `L`, that of `c • f` is `c • L`. -/
theorem HasCauchyPVAt.const_mul {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) (c : ℂ) :
    HasCauchyPVAt γ a b (fun z => c * f z) z₀ (c * L) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1] with ε hε
    exact (intervalIntegrable_congr (g := fun t => c * if ‖γ t - z₀‖ > ε
      then f (γ t) * deriv γ t else 0) fun t _ => by
        simp only []; split_ifs <;> ring).mpr (hε.const_mul c)
  · refine Filter.Tendsto.congr (fun ε => ?_) (h.2.const_mul c)
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by simp only []; split_ifs <;> ring

/-- Additivity: the principal values of `f` and `g` add to that of `f + g`. Together with
`HasCauchyPVAt.const_mul` this is the `ℂ`-linearity of the principal value in the integrand. -/
theorem HasCauchyPVAt.add {γ : ℝ → ℂ} {a b : ℝ} {f g : ℂ → ℂ} {z₀ : ℂ} {L₁ L₂ : ℂ}
    (hf : HasCauchyPVAt γ a b f z₀ L₁) (hg : HasCauchyPVAt γ a b g z₀ L₂) :
    HasCauchyPVAt γ a b (fun z => f z + g z) z₀ (L₁ + L₂) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.1, hg.1] with ε hfi hgi
    refine (intervalIntegrable_congr (g := fun t =>
      (if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
        + if ‖γ t - z₀‖ > ε then g (γ t) * deriv γ t else 0) fun t _ => ?_).mpr (hfi.add hgi)
    simp only [gt_iff_lt]
    split_ifs <;> simp [add_mul]
  · refine Filter.Tendsto.congr' ?_ (hf.2.add hg.2)
    filter_upwards [hf.1, hg.1] with ε hfi hgi
    rw [← intervalIntegral.integral_add hfi hgi]
    exact intervalIntegral.integral_congr fun t _ => by split_ifs <;> ring

/-- The principal value of the zero integrand is `0` — the additive identity for
`HasCauchyPVAt.add`. -/
theorem HasCauchyPVAt.zero {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} :
    HasCauchyPVAt γ a b (fun _ => 0) z₀ 0 := by
  refine ⟨?_, ?_⟩
  · filter_upwards with ε
    simp only [zero_mul, ite_self]
    exact intervalIntegrable_const
  · simp only [zero_mul, ite_self, intervalIntegral.integral_zero]
    exact tendsto_const_nhds

/-- The value form of `HasCauchyPVAt.zero`: the principal value of the zero integrand is `0`. -/
@[simp]
theorem cauchyPVAt_zero {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} :
    cauchyPVAt γ a b (fun _ => 0) z₀ = 0 :=
  HasCauchyPVAt.zero.cauchyPVAt_eq

/-- The Cauchy principal value at a single point over a zero-length interval is `0`. -/
theorem HasCauchyPVAt.refl (γ : ℝ → ℂ) (a : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) :
    HasCauchyPVAt γ a a f z₀ 0 := by
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards with ε
    exact IntervalIntegrable.refl
  · simpa only [intervalIntegral.integral_same] using tendsto_const_nhds (x := (0 : ℂ))

/-- If the two endpoints are equal, the single-point Cauchy principal value is `0`. -/
theorem HasCauchyPVAt.of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (f : ℂ → ℂ) (z₀ : ℂ) :
    HasCauchyPVAt γ a b f z₀ 0 := by
  subst b
  exact HasCauchyPVAt.refl γ a f z₀

/-- Existence form of `HasCauchyPVAt.refl`: a zero-length interval always has a single-point
Cauchy principal value. -/
theorem CauchyPVExistsAt.refl (γ : ℝ → ℂ) (a : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) :
    CauchyPVExistsAt γ a a f z₀ :=
  CauchyPVExistsAt.intro (HasCauchyPVAt.refl γ a f z₀)

/-- Existence form of `HasCauchyPVAt.of_eq`. -/
theorem CauchyPVExistsAt.of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (f : ℂ → ℂ) (z₀ : ℂ) :
    CauchyPVExistsAt γ a b f z₀ :=
  CauchyPVExistsAt.intro (HasCauchyPVAt.of_eq γ hab f z₀)

/-- Value form of `HasCauchyPVAt.refl`: the single-point Cauchy principal value on `[a, a]` is
`0`. -/
@[simp]
theorem cauchyPVAt_same (γ : ℝ → ℂ) (a : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) :
    cauchyPVAt γ a a f z₀ = 0 :=
  (HasCauchyPVAt.refl γ a f z₀).cauchyPVAt_eq

/-- Value form of `HasCauchyPVAt.of_eq`. -/
theorem cauchyPVAt_eq_zero_of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (f : ℂ → ℂ) (z₀ : ℂ) :
    cauchyPVAt γ a b f z₀ = 0 :=
  (HasCauchyPVAt.of_eq γ hab f z₀).cauchyPVAt_eq

/-- **Finite additivity.** The principal value of a finite sum of integrands is the sum of their
principal values. With `HasCauchyPVAt.zero` and `HasCauchyPVAt.add` this extends the `ℂ`-linearity
of the principal value to finite sums, as the generalized residue theorem's residue sum needs. -/
theorem HasCauchyPVAt.sum {ι : Type*} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {f : ι → ℂ → ℂ} {L : ι → ℂ}
    {s : Finset ι} (h : ∀ i ∈ s, HasCauchyPVAt γ a b (f i) z₀ (L i)) :
    HasCauchyPVAt γ a b (fun z => ∑ i ∈ s, f i z) z₀ (∑ i ∈ s, L i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasCauchyPVAt.zero
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self j s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Avoidance.** If `γ` stays away from `z₀` throughout `[a, b]` and the ordinary contour
integrand is integrable there, the symmetric excision is eventually inert, so the principal value
exists and equals the ordinary contour integral. -/
theorem HasCauchyPVAt.of_avoidance {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h_cont : ContinuousOn γ (Set.uIcc a b))
    (h_avoid : ∀ t ∈ Set.uIcc a b, γ t ≠ z₀)
    (hf_int : IntervalIntegrable (fun t => f (γ t) * deriv γ t) MeasureTheory.volume a b) :
    HasCauchyPVAt γ a b f z₀ (∫ t in a..b, f (γ t) * deriv γ t) := by
  obtain ⟨t₀, ht₀, ht₀_min⟩ := isCompact_uIcc.exists_isMinOn
    Set.nonempty_uIcc (h_cont.sub continuousOn_const).norm
  have hpos : 0 < ‖γ t₀ - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (h_avoid t₀ ht₀))
  refine ⟨?_, ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
    refine (intervalIntegrable_congr fun t ht => ?_).mpr hf_int
    exact if_pos (lt_of_lt_of_le hε.2 (ht₀_min (Set.uIoc_subset_uIcc ht)))
  · apply Filter.Tendsto.congr' _ tendsto_const_nhds
    rw [Filter.EventuallyEq, Filter.eventually_iff_exists_mem]
    refine ⟨Set.Ioo 0 ‖γ t₀ - z₀‖, Ioo_mem_nhdsGT hpos, fun ε hε => ?_⟩
    exact intervalIntegral.integral_congr fun t ht =>
      (if_pos (lt_of_lt_of_le hε.2 (ht₀_min ht))).symm

/-- **Concatenation.** The principal values along adjacent subcurves `[a, b]` and `[b, c]` add to
the principal value along `[a, c]`. The integrability of the excised integrand across `[a, c]` and
the additivity of the integral both follow from the two given principal values, so no ordering or
separate integrability hypothesis is needed. -/
theorem HasCauchyPVAt.concat {γ : ℝ → ℂ} {a b c : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L₁ L₂ : ℂ}
    (h_ab : HasCauchyPVAt γ a b f z₀ L₁) (h_bc : HasCauchyPVAt γ b c f z₀ L₂) :
    HasCauchyPVAt γ a c f z₀ (L₁ + L₂) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h_ab.1, h_bc.1] with ε hab_int hbc_int
    exact hab_int.trans hbc_int
  · refine Filter.Tendsto.congr' ?_ (h_ab.2.add h_bc.2)
    filter_upwards [h_ab.1, h_bc.1] with ε hab_int hbc_int
    exact intervalIntegral.integral_add_adjacent_intervals hab_int hbc_int

/-- Existence form of `HasCauchyPVAt.of_avoidance`. -/
theorem cauchyPVExistsAt_of_avoidance {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h_cont : ContinuousOn γ (Set.uIcc a b))
    (h_avoid : ∀ t ∈ Set.uIcc a b, γ t ≠ z₀)
    (hf_int : IntervalIntegrable (fun t => f (γ t) * deriv γ t) MeasureTheory.volume a b) :
    CauchyPVExistsAt γ a b f z₀ :=
  ⟨_, HasCauchyPVAt.of_avoidance h_cont h_avoid hf_int⟩

/-- Existence-level scalar multiplication: scaling preserves existence of the principal value. -/
theorem CauchyPVExistsAt.const_mul {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ a b f z₀) (c : ℂ) :
    CauchyPVExistsAt γ a b (fun z => c * f z) z₀ :=
  let ⟨_, hL⟩ := h
  ⟨_, hL.const_mul c⟩

/-- Existence-level additivity: existence of the principal values of `f` and `g` gives that of
`f + g`. -/
theorem CauchyPVExistsAt.add {γ : ℝ → ℂ} {a b : ℝ} {f g : ℂ → ℂ} {z₀ : ℂ}
    (hf : CauchyPVExistsAt γ a b f z₀) (hg : CauchyPVExistsAt γ a b g z₀) :
    CauchyPVExistsAt γ a b (fun z => f z + g z) z₀ :=
  let ⟨_, hLf⟩ := hf
  let ⟨_, hLg⟩ := hg
  ⟨_, hLf.add hLg⟩

/-- Existence-level: the zero integrand has a principal value. -/
theorem CauchyPVExistsAt.zero {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} :
    CauchyPVExistsAt γ a b (fun _ => 0) z₀ :=
  ⟨0, HasCauchyPVAt.zero⟩

/-- Existence-level finite additivity: if each summand has a principal value, so does the finite
sum of integrands. -/
theorem CauchyPVExistsAt.sum {ι : Type*} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {f : ι → ℂ → ℂ}
    {s : Finset ι} (h : ∀ i ∈ s, CauchyPVExistsAt γ a b (f i) z₀) :
    CauchyPVExistsAt γ a b (fun z => ∑ i ∈ s, f i z) z₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simpa using HasCauchyPVAt.zero⟩
  | @insert j s hj ih =>
    obtain ⟨Lj, hLj⟩ := h j (Finset.mem_insert_self j s)
    obtain ⟨Ls, hLs⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact ⟨Lj + Ls, by simpa only [Finset.sum_insert hj] using hLj.add hLs⟩

/-- Reversing the interval orientation negates a single-point Cauchy principal value. -/
theorem HasCauchyPVAt.symm {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) :
    HasCauchyPVAt γ b a f z₀ (-L) := by
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards [h.eventually_intervalIntegrable] with ε hε
    exact hε.symm
  · refine Filter.Tendsto.congr (fun ε => ?_) h.tendsto.neg
    exact (intervalIntegral.integral_symm (f :=
      fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) a b).symm

/-- Existence of a single-point Cauchy principal value is invariant under reversing the interval
orientation. -/
theorem CauchyPVExistsAt.symm {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ a b f z₀) :
    CauchyPVExistsAt γ b a f z₀ :=
  let ⟨_, hL⟩ := cauchyPVExistsAt_iff.mp h
  cauchyPVExistsAt_iff.mpr ⟨_, hL.symm⟩

/-- Value form of `HasCauchyPVAt.symm`: if the single-point principal value exists on `[a, b]`,
then the value on `[b, a]` is its negative. -/
theorem cauchyPVAt_symm {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ a b f z₀) :
    cauchyPVAt γ b a f z₀ = -cauchyPVAt γ a b f z₀ :=
  h.hasCauchyPVAt_cauchyPVAt.symm.cauchyPVAt_eq

/-- Existence form of `HasCauchyPVAt.concat`. -/
theorem CauchyPVExistsAt.concat {γ : ℝ → ℂ} {a b c : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h_ab : CauchyPVExistsAt γ a b f z₀) (h_bc : CauchyPVExistsAt γ b c f z₀) :
    CauchyPVExistsAt γ a c f z₀ :=
  let ⟨_, hL₁⟩ := h_ab
  let ⟨_, hL₂⟩ := h_bc
  ⟨_, hL₁.concat hL₂⟩

end TauCeti.Contour

end
