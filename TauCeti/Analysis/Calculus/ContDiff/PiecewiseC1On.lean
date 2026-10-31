/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.ContDiff.ClosedInterval
import TauCeti.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import TauCeti.Order.Interval.Finite

/-!
# Piecewise `C¹` curves on an interval

A curve `γ : ℝ → E` in a real normed space is **piecewise `C¹`** on the closed interval
`[[a, b]]` between two parameters (in either order) if it is continuous there, and `C¹` on each
piece between finitely many breakpoints. This file introduces that regularity as a predicate
`TauCeti.IsPiecewiseC1On γ a b` on the raw function `γ`, with no bundled path type, together with
its API. Contour integrals, generalized winding numbers, and the Hungerbühler--Wasem regularity
conditions are stated for such curves, with `E = ℂ`.

The predicate is used to *discharge* the integrand-level hypotheses — continuity, pointwise
differentiability, and integrability of the derivative — that the raw contour-integral lemmas take
directly. Those lemmas do not consume the predicate themselves: the fundamental theorem of calculus
along a contour in `Contour.ArcFTC`, for instance, is stated on the integrand, so it applies to any
curve for which these hypotheses can be established.

## Main definitions

* `TauCeti.IsPiecewiseC1On γ a b` — `γ` is continuous on `[[a, b]]` and `C¹` on every closed
  subinterval whose interior avoids a fixed finite breakpoint set in `(min a b, max a b)`.

## Main results

* `TauCeti.isPiecewiseC1On_iff` — unfold the predicate to its defining clauses.
* `TauCeti.IsPiecewiseC1On.continuousOn` — the underlying continuity on `[[a, b]]`.
* `TauCeti.IsPiecewiseC1On.of_contDiffOn` — a `C¹` curve is piecewise `C¹`, with no breakpoints.
* `TauCeti.IsPiecewiseC1On.of_breakpoints`, `TauCeti.IsPiecewiseC1On.exists_breakpoints` —
  introduce the predicate from, and eliminate it to, a finite breakpoint witness.
* `TauCeti.IsPiecewiseC1On.mono` — restrict the regularity to a subinterval `[[c, d]] ⊆ [[a, b]]`.
* `TauCeti.isPiecewiseC1On_comm`, `TauCeti.IsPiecewiseC1On.symm` — endpoint-swap invariance.
* `TauCeti.IsPiecewiseC1On.add`, `TauCeti.IsPiecewiseC1On.sub`,
  `TauCeti.IsPiecewiseC1On.const_smul` — the predicate is stable under the module operations
  on curves, the two breakpoint sets being merged by union.
* `TauCeti.IsPiecewiseC1On.exists_finset_differentiableAt`,
  `TauCeti.IsPiecewiseC1On.exists_countable_differentiableAt` — differentiability off a finite
  (hence countable) set, in the exact shapes the raw contour-integral lemmas consume.
* `TauCeti.IsPiecewiseC1On.eventually_differentiableAt` — eventual differentiability near an
  interior parameter.
* `TauCeti.IsPiecewiseC1On.intervalIntegrable_deriv` — the derivative is interval-integrable on
  `a..b`, glued across the breakpoints from the `C¹` pieces.
* `TauCeti.IsPiecewiseC1On.isBounded_image_deriv` — the derivative has bounded image on
  `[[a, b]]`, glued the same way.

## Provenance

Adapted from the regularity fields of the `PiecewiseC1PathOn` structure in the AINTLIB
`LeanModularForms` development, re-expressed as a predicate on a raw function `γ` rather than as
a bundled path type. The gluing of the integrability of the derivative across the breakpoints
(`IsPiecewiseC1On.intervalIntegrable_deriv`) follows
`ClosedPwC1Curve.deriv_extend_intervalIntegrable` in the same development's
`PaperPwC1Immersion.lean`, restated for the raw curve; the piece-level step is
`ContDiffOn.intervalIntegrable_deriv`.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : ℝ → E} {a b : ℝ}

/-- **Piecewise `C¹` on the interval between `a` and `b`.** The curve `γ : ℝ → E` is continuous on
the closed interval `[[a, b]]` (unordered, hence orientation-robust), and there is a finite set of
breakpoints `p ⊆ (min a b, max a b)` such that `γ` is `C¹` on every closed subinterval of `[[a, b]]`
whose interior avoids `p`. Equivalently `γ` is continuously differentiable on each piece between
consecutive breakpoints, with corners allowed only at the breakpoints; an unbounded-derivative cusp
such as `t ↦ √|t|` is excluded, being not `C¹` up to the breakpoint. This is a `Prop` on the raw
function `γ` itself, with no bundled path type. -/
def IsPiecewiseC1On (γ : ℝ → E) (a b : ℝ) : Prop :=
  ContinuousOn γ (uIcc a b) ∧
    ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
      ∀ c d : ℝ, Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
        ContDiffOn ℝ 1 γ (Icc c d)

/-- `IsPiecewiseC1On` unfolded to its defining clauses: continuity on `[[a, b]]`, and a finite
breakpoint set off which every breakpoint-free closed subinterval carries a `C¹` restriction. -/
theorem isPiecewiseC1On_iff :
    IsPiecewiseC1On γ a b ↔
      ContinuousOn γ (uIcc a b) ∧
        ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
          ∀ c d : ℝ, Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
            ContDiffOn ℝ 1 γ (Icc c d) :=
  Iff.rfl

/-- A piecewise-`C¹` curve is continuous on the parameter interval `[[a, b]]`. -/
theorem IsPiecewiseC1On.continuousOn (h : IsPiecewiseC1On γ a b) :
    ContinuousOn γ (uIcc a b) :=
  h.1

/-- A `C¹` curve on `[[a, b]]` is piecewise `C¹`, with no breakpoints. -/
theorem IsPiecewiseC1On.of_contDiffOn (h : ContDiffOn ℝ 1 γ (uIcc a b)) :
    IsPiecewiseC1On γ a b :=
  ⟨h.continuousOn, ∅, by simp, fun c d hcd _ => h.mono hcd⟩

/-- Build a piecewise-`C¹` curve from continuity on `[[a, b]]` together with a finite breakpoint set
off which every breakpoint-free closed subinterval carries a `C¹` restriction. -/
theorem IsPiecewiseC1On.of_breakpoints (hcont : ContinuousOn γ (uIcc a b)) (p : Finset ℝ)
    (hp : ↑p ⊆ Ioo (min a b) (max a b))
    (hC1 : ∀ c d : ℝ, Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
      ContDiffOn ℝ 1 γ (Icc c d)) :
    IsPiecewiseC1On γ a b :=
  ⟨hcont, p, hp, hC1⟩

/-- Extract the finite breakpoint set of a piecewise-`C¹` curve, together with the `C¹` restriction
it induces on every breakpoint-free closed subinterval of `[[a, b]]`. -/
theorem IsPiecewiseC1On.exists_breakpoints (h : IsPiecewiseC1On γ a b) :
    ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
      ∀ c d : ℝ, Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
        ContDiffOn ℝ 1 γ (Icc c d) :=
  h.2

/-- Piecewise-`C¹` regularity restricts to any subinterval: if `γ` is piecewise `C¹` on `[[a, b]]`
and `[[c, d]] ⊆ [[a, b]]`, then `γ` is piecewise `C¹` on `[[c, d]]`, with the breakpoint set cut
down to the smaller interior. -/
theorem IsPiecewiseC1On.mono (h : IsPiecewiseC1On γ a b) {c d : ℝ}
    (hsub : uIcc c d ⊆ uIcc a b) : IsPiecewiseC1On γ c d := by
  obtain ⟨p, _, hC1⟩ := h.exists_breakpoints
  refine ⟨h.continuousOn.mono hsub, p.filter (· ∈ Ioo (min c d) (max c d)),
    fun x hx => (Finset.mem_filter.mp hx).2, fun u v huv hdis => hC1 u v (huv.trans hsub) ?_⟩
  refine Set.disjoint_left.mpr fun x hxp hxuv => Set.disjoint_left.mp hdis ?_ hxuv
  rw [← Icc_min_max] at huv
  obtain ⟨hlu, hvu⟩ := (Icc_subset_Icc_iff (hxuv.1.trans hxuv.2).le).1 huv
  exact Finset.mem_filter.mpr ⟨hxp, hlu.trans_lt hxuv.1, hxuv.2.trans_le hvu⟩

/-- Piecewise-`C¹` regularity is symmetric in the endpoints, since `[[a, b]] = [[b, a]]`. -/
theorem isPiecewiseC1On_comm : IsPiecewiseC1On γ a b ↔ IsPiecewiseC1On γ b a := by
  simp only [isPiecewiseC1On_iff, Set.uIcc_comm a b, min_comm a b, max_comm a b]

/-- Piecewise-`C¹` regularity is invariant under swapping the endpoints of the interval. -/
theorem IsPiecewiseC1On.symm (h : IsPiecewiseC1On γ a b) : IsPiecewiseC1On γ b a :=
  isPiecewiseC1On_comm.mp h

/-- **A sum of piecewise-`C¹` curves is piecewise `C¹`**, with the union of the two breakpoint sets
as breakpoints. -/
theorem IsPiecewiseC1On.add {γ₁ γ₂ : ℝ → E} (h₁ : IsPiecewiseC1On γ₁ a b)
    (h₂ : IsPiecewiseC1On γ₂ a b) : IsPiecewiseC1On (fun t => γ₁ t + γ₂ t) a b := by
  obtain ⟨p₁, hp₁, hC₁⟩ := h₁.exists_breakpoints
  obtain ⟨p₂, hp₂, hC₂⟩ := h₂.exists_breakpoints
  refine ⟨h₁.continuousOn.add h₂.continuousOn, p₁ ∪ p₂, by simpa using union_subset hp₁ hp₂,
    fun c d hcd hdisj => ?_⟩
  rw [Finset.coe_union, disjoint_union_left] at hdisj
  exact (hC₁ c d hcd hdisj.1).add (hC₂ c d hcd hdisj.2)

/-- **A difference of piecewise-`C¹` curves is piecewise `C¹`.** -/
theorem IsPiecewiseC1On.sub {γ₁ γ₂ : ℝ → E} (h₁ : IsPiecewiseC1On γ₁ a b)
    (h₂ : IsPiecewiseC1On γ₂ a b) : IsPiecewiseC1On (fun t => γ₁ t - γ₂ t) a b := by
  obtain ⟨p₁, hp₁, hC₁⟩ := h₁.exists_breakpoints
  obtain ⟨p₂, hp₂, hC₂⟩ := h₂.exists_breakpoints
  refine ⟨h₁.continuousOn.sub h₂.continuousOn, p₁ ∪ p₂, by simpa using union_subset hp₁ hp₂,
    fun c d hcd hdisj => ?_⟩
  rw [Finset.coe_union, disjoint_union_left] at hdisj
  exact (hC₁ c d hcd hdisj.1).sub (hC₂ c d hcd hdisj.2)

/-- **A constant multiple of a piecewise-`C¹` curve is piecewise `C¹`**, with the same
breakpoints. The scalars may be any ring acting continuously and compatibly with the real
structure, e.g. `ℂ` acting on a complex curve. -/
theorem IsPiecewiseC1On.const_smul {R : Type*} [Semiring R] [Module R E] [SMulCommClass ℝ R E]
    [ContinuousConstSMul R E] (c : R) (h : IsPiecewiseC1On γ a b) :
    IsPiecewiseC1On (fun t => c • γ t) a b := by
  obtain ⟨p, hp, hC1⟩ := h.exists_breakpoints
  exact ⟨h.continuousOn.const_smul c, p, hp,
    fun u v huv hdisj => (hC1 u v huv hdisj).const_smul c⟩

/-- Around any interior parameter outside a closed set `s` there is a closed subinterval of
`[[a, b]]` whose interior contains `t` and is disjoint from `s`. -/
theorem exists_Icc_subset_uIcc_disjoint {s : Set ℝ} (hs : IsClosed s) {t : ℝ}
    (ht : t ∈ Ioo (min a b) (max a b)) (hts : t ∉ s) :
    ∃ c d : ℝ, t ∈ Ioo c d ∧ Icc c d ⊆ uIcc a b ∧ Disjoint s (Ioo c d) := by
  have hmem : Ioo (min a b) (max a b) \ s ∈ 𝓝 t := (isOpen_Ioo.sdiff hs).mem_nhds ⟨ht, hts⟩
  obtain ⟨c, d, -, hnhds, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds hmem
  refine ⟨c, d, interior_Icc (a := c) (b := d) ▸ mem_interior_iff_mem_nhds.mpr hnhds,
    fun x hx => Icc_min_max.subset (Ioo_subset_Icc_self (hsub hx).1),
    disjoint_right.mpr fun x hx => (hsub (Ioo_subset_Icc_self hx)).2⟩

/-- **Differentiability off a finite set.** A piecewise-`C¹` curve is differentiable at every
interior parameter outside a finite set — the breakpoints. -/
theorem IsPiecewiseC1On.exists_finset_differentiableAt (h : IsPiecewiseC1On γ a b) :
    ∃ p : Finset ℝ,
      ∀ t ∈ Ioo (min a b) (max a b) \ (↑p : Set ℝ), DifferentiableAt ℝ γ t := by
  obtain ⟨p, -, hC1⟩ := h.exists_breakpoints
  refine ⟨p, fun t ht => ?_⟩
  obtain ⟨c, d, htcd, hsub, hdisj⟩ :=
    exists_Icc_subset_uIcc_disjoint p.finite_toSet.isClosed ht.1 ht.2
  exact ((hC1 c d hsub hdisj).differentiableOn one_ne_zero).differentiableAt
    (Icc_mem_nhds htcd.1 htcd.2)

/-- **Differentiability off a countable set.** A piecewise-`C¹` curve is differentiable at every
interior parameter outside a countable set — the breakpoints. This is the exact regularity shape
consumed by the raw contour-integral development (Dixon's argument and the winding-number
machinery). -/
theorem IsPiecewiseC1On.exists_countable_differentiableAt (h : IsPiecewiseC1On γ a b) :
    ∃ P : Set ℝ, P.Countable ∧
      ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t :=
  let ⟨p, hp⟩ := h.exists_finset_differentiableAt
  ⟨↑p, p.countable_toSet, hp⟩

/-- **Eventual differentiability near an interior parameter**, on any within-filter avoiding
the parameter itself. -/
theorem IsPiecewiseC1On.eventually_differentiableAt (h : IsPiecewiseC1On γ a b) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (min a b) (max a b)) {u : Set ℝ} (hu : t₀ ∉ u) :
    ∀ᶠ t in 𝓝[u] t₀, DifferentiableAt ℝ γ t := by
  obtain ⟨p, hp⟩ := h.exists_finset_differentiableAt
  have hcl : IsClosed ((↑p \ {t₀} : Set ℝ)) := (p.finite_toSet.subset sdiff_subset).isClosed
  filter_upwards [nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds (by simp)),
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ht₀), self_mem_nhdsWithin] with t htc htIoo htu
  exact hp t ⟨htIoo, fun htp => htc ⟨htp, fun h_eq => hu (h_eq ▸ htu)⟩⟩

/-- **Interval-integrability of the derivative.** The derivative of a piecewise-`C¹` curve is
interval-integrable on `a..b`. This discharges the `hderiv_int` hypothesis of the raw
contour-integral lemmas. -/
theorem IsPiecewiseC1On.intervalIntegrable_deriv (h : IsPiecewiseC1On γ a b) :
    IntervalIntegrable (fun t ↦ deriv γ t) volume a b := by
  obtain ⟨p, -, hC1⟩ := h.exists_breakpoints
  -- Glue the integrability of each `C¹` piece across the breakpoints.
  refine (Icc_induction_of_disjoint_Ioo (p := p)
    (Q := fun c d => IntervalIntegrable (fun t ↦ deriv γ t) volume c d)
    (fun c d hcd hsub hdisj =>
      ((hC1 c d hsub hdisj).mono (uIcc_of_le hcd).le).intervalIntegrable_deriv le_rfl)
    (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂) min_le_max Icc_min_max.subset).mono_set ?_
  rw [uIcc_of_le min_le_max, Icc_min_max]

/-- **Boundedness of the derivative of a piecewise-`C¹` curve on its whole parameter interval.**
The image of `[[a, b]]` under `deriv γ` is bounded, in either orientation of the endpoints; at
the breakpoints `deriv γ` takes whatever value it has, which affects only finitely many points. -/
theorem IsPiecewiseC1On.isBounded_image_deriv (h : IsPiecewiseC1On γ a b) :
    Bornology.IsBounded (deriv γ '' uIcc a b) := by
  obtain ⟨p, -, hC1⟩ := h.exists_breakpoints
  -- Glue the boundedness on each `C¹` piece across the breakpoints.
  rw [← Icc_min_max]
  refine Icc_induction_of_disjoint_Ioo (p := p)
    (Q := fun c d => Bornology.IsBounded (deriv γ '' Icc c d))
    (fun c d _ hsub hdisj => (hC1 c d hsub hdisj).isBounded_image_deriv le_rfl)
    (fun c m d hcm hmd h₁ h₂ => ?_) min_le_max Icc_min_max.subset
  rw [← Icc_union_Icc_eq_Icc hcm hmd, image_union]
  exact h₁.union h₂

end TauCeti
