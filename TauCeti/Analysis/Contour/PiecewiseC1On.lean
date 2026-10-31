/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Piecewise `C¹` curves on an interval

Contour integrals, generalized winding numbers, and the Hungerbühler--Wasem regularity conditions
are stated for a **piecewise `C¹`** curve `γ` on the closed interval `[[a, b]]` between two
parameters (in either order): continuous there, and `C¹` on each piece between finitely many
breakpoints. This file introduces that regularity as a predicate `Contour.IsPiecewiseC1On γ a b`
on the raw function `γ : ℝ → E`, valued in any real normed space (contours take `E = ℂ`), with no
bundled path type, together with its API.

The predicate is used to *discharge* the integrand-level hypotheses — continuity, pointwise
differentiability, and integrability of the derivative — that the raw contour-integral lemmas take
directly. Those lemmas do not consume the predicate themselves: the fundamental theorem of calculus
along a contour in `Contour.ArcFTC`, for instance, is stated on the integrand, so it applies to any
curve for which these hypotheses can be established.

## Main definitions

* `Contour.IsPiecewiseC1On γ a b` — `γ` is continuous on `[[a, b]]` and `C¹` on every closed
  subinterval whose interior avoids a fixed finite breakpoint set in `(min a b, max a b)`.

## Main results

* `Contour.isPiecewiseC1On_iff` — unfold the predicate to its defining clauses.
* `Contour.IsPiecewiseC1On.continuousOn` — the underlying continuity on `[[a, b]]`.
* `Contour.IsPiecewiseC1On.of_contDiffOn` — a `C¹` curve is piecewise `C¹`, with no breakpoints.
* `Contour.IsPiecewiseC1On.of_breakpoints`, `Contour.IsPiecewiseC1On.exists_breakpoints` —
  introduce the predicate from, and eliminate it to, a finite breakpoint witness.
* `Contour.IsPiecewiseC1On.mono` — restrict the regularity to a subinterval `[[c, d]] ⊆ [[a, b]]`.
* `Contour.isPiecewiseC1On_comm`, `Contour.IsPiecewiseC1On.symm` — endpoint-swap invariance.
* `Contour.IsPiecewiseC1On.add`, `Contour.IsPiecewiseC1On.sub`,
  `Contour.IsPiecewiseC1On.const_smul` — the predicate is stable under the module operations
  on curves, the two breakpoint sets being merged by union.
* `Contour.IsPiecewiseC1On.exists_finset_differentiableAt`,
  `Contour.IsPiecewiseC1On.exists_countable_differentiableAt` — differentiability off a finite
  (hence countable) set, in the exact shapes the raw contour-integral lemmas consume.
* `Contour.IsPiecewiseC1On.eventually_differentiableAt` — eventual differentiability near an
  interior parameter.
* `Contour.IsPiecewiseC1On.intervalIntegrable_deriv` — the derivative is interval-integrable on
  `a..b`, glued across the breakpoints from the `C¹` pieces.
* `Contour.IsPiecewiseC1On.isBounded_image_deriv` — the derivative has bounded image on
  `[[a, b]]`, glued the same way.

## Provenance

Adapted from the regularity fields of the `PiecewiseC1PathOn` structure in the AINTLIB
`LeanModularForms` development, re-expressed as a predicate on a raw function `γ` rather than as
a bundled path type. The piece-level integrability of the derivative and its gluing across the
breakpoints (`IsPiecewiseC1On.intervalIntegrable_deriv`) follow
`ClosedPwC1Curve.deriv_intervalIntegrable_piece` and
`ClosedPwC1Curve.deriv_extend_intervalIntegrable` in the same development's
`PaperPwC1Immersion.lean`, restated for the raw curve.
-/

public section

noncomputable section

namespace TauCeti.Contour

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

/-- The derivative of a curve that is `C¹` on `[c, d]` is interval-integrable on `c..d`: the
within-interval derivative is continuous on the compact piece, and agrees with `deriv` on the
interior, hence almost everywhere. -/
private theorem intervalIntegrable_deriv_of_contDiffOn {c d : ℝ} (hcd : c ≤ d)
    (hC1 : ContDiffOn ℝ 1 γ (Icc c d)) :
    IntervalIntegrable (fun t ↦ deriv γ t) volume c d := by
  rcases eq_or_lt_of_le hcd with rfl | hlt
  · exact IntervalIntegrable.refl
  have hdw : ContinuousOn (derivWithin γ (Icc c d)) (Icc c d) :=
    hC1.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) le_rfl
  have hint : IntervalIntegrable (derivWithin γ (Icc c d)) volume c d :=
    (hdw.mono (uIcc_of_le hcd).le).intervalIntegrable
  rw [intervalIntegrable_iff] at hint ⊢
  refine hint.congr ?_
  rw [uIoc_of_le hcd, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)

/-- **Generic breakpoint-gluing induction.** An invariant `Q` that holds on every closed,
breakpoint-free subinterval of `[[a, b]]` (`hbase`) and is closed under concatenation at a shared
endpoint (`hglue`) holds on every closed subinterval, by induction on the number of breakpoints
strictly inside it, splitting off the largest one. Shared scaffolding for gluing a piecewise-`C¹`
invariant across breakpoints — e.g. `IntervalIntegrable (deriv γ) volume` via `.trans`, or
`Bornology.IsBounded (deriv γ '' ·)` via `.union` on `Icc c m ∪ Icc m d = Icc c d`. -/
private theorem piecewise_gluing_induction {p : Finset ℝ} {Q : ℝ → ℝ → Prop}
    (hbase : ∀ c d : ℝ, c ≤ d → Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) → Q c d)
    (hglue : ∀ c m d : ℝ, c ≤ m → m ≤ d → Q c m → Q m d → Q c d) :
    ∀ c d : ℝ, c ≤ d → Icc c d ⊆ uIcc a b → Q c d := by
  have hdisj : ∀ {c d : ℝ}, p.filter (· ∈ Ioo c d) = ∅ → Disjoint (↑p : Set ℝ) (Ioo c d) :=
    fun he => disjoint_left.mpr fun _ hxp hx => Finset.filter_eq_empty_iff.mp he hxp hx
  -- Strong induction on the number of breakpoints strictly inside `[c, d]`, via an explicit
  -- upper bound `n` discharged with `le_rfl` at the end -- internal scaffolding, not part of the
  -- public signature above.
  suffices h : ∀ n, ∀ c d : ℝ, (p.filter (· ∈ Ioo c d)).card ≤ n → c ≤ d → Icc c d ⊆ uIcc a b →
      Q c d from fun c d => h _ c d le_rfl
  intro n
  induction n with
  | zero =>
    intro c d hcard hcd hsub
    exact hbase c d hcd hsub (hdisj (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)))
  | succ n ih =>
    intro c d hcard hcd hsub
    rcases (p.filter (· ∈ Ioo c d)).eq_empty_or_nonempty with he | hne
    · exact hbase c d hcd hsub (hdisj he)
    set m := (p.filter (· ∈ Ioo c d)).max' hne
    obtain ⟨hmp, hm⟩ := Finset.mem_filter.mp ((p.filter (· ∈ Ioo c d)).max'_mem hne)
    have hssub : p.filter (· ∈ Ioo c m) ⊂ p.filter (· ∈ Ioo c d) :=
      (Finset.ssubset_iff_of_subset (Finset.monotone_filter_right _ fun x _ hx =>
          ⟨hx.1, hx.2.trans hm.2⟩)).mpr
        ⟨m, Finset.mem_filter.mpr ⟨hmp, hm⟩, fun hmem =>
          (Finset.mem_filter.mp hmem).2.2.false⟩
    have h₁ : Q c m :=
      ih c m (Nat.le_of_lt_succ ((Finset.card_lt_card hssub).trans_le hcard)) hm.1.le
        ((Icc_subset_Icc le_rfl hm.2.le).trans hsub)
    have h₂ : Q m d :=
      hbase m d hm.2.le ((Icc_subset_Icc hm.1.le le_rfl).trans hsub) <|
        disjoint_left.mpr fun x hxp hx => ((p.filter (· ∈ Ioo c d)).le_max' x
          (Finset.mem_filter.mpr ⟨hxp, hm.1.trans hx.1, hx.2⟩)).not_gt hx.1
    exact hglue c m d hm.1.le hm.2.le h₁ h₂

/-- **Interval-integrability of the derivative.** The derivative of a piecewise-`C¹` curve is
interval-integrable on `a..b`. This discharges the `hderiv_int` hypothesis of the raw
contour-integral lemmas. -/
theorem IsPiecewiseC1On.intervalIntegrable_deriv (h : IsPiecewiseC1On γ a b) :
    IntervalIntegrable (fun t ↦ deriv γ t) volume a b := by
  obtain ⟨p, -, hC1⟩ := h.exists_breakpoints
  -- Glue the integrability of each `C¹` piece across the breakpoints.
  refine (piecewise_gluing_induction (p := p)
    (Q := fun c d => IntervalIntegrable (fun t ↦ deriv γ t) volume c d)
    (fun c d hcd hsub hdisj => intervalIntegrable_deriv_of_contDiffOn hcd (hC1 c d hsub hdisj))
    (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂) _ _ min_le_max Icc_min_max.subset).mono_set ?_
  rw [uIcc_of_le min_le_max, Icc_min_max]

/-- The derivative of a curve that is `C¹` on `[c, d]` has bounded image on `[c, d]`: the
within-interval derivative is continuous on the compact piece, hence bounded there by
compactness, and agrees with `deriv` on the interior; the two endpoints contribute at most two
further (arbitrary, automatically bounded) values. -/
private theorem isBounded_image_deriv_of_contDiffOn {c d : ℝ} (hcd : c ≤ d)
    (hC1 : ContDiffOn ℝ 1 γ (Icc c d)) :
    Bornology.IsBounded (deriv γ '' Icc c d) := by
  rcases hcd.eq_or_lt with rfl | hlt
  · simp
  have hdw : ContinuousOn (derivWithin γ (Icc c d)) (Icc c d) :=
    hC1.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) le_rfl
  have hdw_bdd : Bornology.IsBounded (derivWithin γ (Icc c d) '' Icc c d) :=
    (isCompact_Icc.image_of_continuousOn hdw).isBounded
  refine (hdw_bdd.union (Set.toFinite {deriv γ c, deriv γ d}).isBounded).subset ?_
  rintro y ⟨t, ht, rfl⟩
  rcases eq_or_ne t c with rfl | htc
  · simp
  rcases eq_or_ne t d with rfl | htd
  · simp
  exact Or.inl ⟨t, ht, derivWithin_of_mem_nhds (Icc_mem_nhds (ht.1.lt_of_ne' htc)
    (ht.2.lt_of_ne htd))⟩

/-- **Boundedness of the derivative of a piecewise-`C¹` curve on its whole parameter interval.**
The image of `[[a, b]]` under `deriv γ` is bounded, in either orientation of the endpoints; at
the breakpoints `deriv γ` takes whatever value it has, which affects only finitely many points. -/
theorem IsPiecewiseC1On.isBounded_image_deriv (h : IsPiecewiseC1On γ a b) :
    Bornology.IsBounded (deriv γ '' uIcc a b) := by
  obtain ⟨p, -, hC1⟩ := h.exists_breakpoints
  -- Glue the boundedness on each `C¹` piece across the breakpoints.
  rw [← Icc_min_max]
  refine piecewise_gluing_induction (p := p)
    (Q := fun c d => Bornology.IsBounded (deriv γ '' Icc c d))
    (fun c d hcd hsub hdisj => isBounded_image_deriv_of_contDiffOn hcd (hC1 c d hsub hdisj))
    (fun c m d hcm hmd h₁ h₂ => ?_) _ _ min_le_max Icc_min_max.subset
  rw [← Icc_union_Icc_eq_Icc hcm hmd, image_union]
  exact h₁.union h₂

end TauCeti.Contour
