/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Order.IntermediateValue

/-!
# The Warsaw circle and lifting of maps from compact locally path-connected spaces

The **Warsaw circle** `TauCeti.WarsawCircle` is the planar continuum formed by closing up the
closed topologist's sine curve on `(0, 1]` with a polygonal arc joining `(1, sin 1)` back to the
lower endpoint `(0, -1)` of the vertical limit segment `{0} × [-1, 1]`. Explicitly, its underlying
set `TauCeti.warsawCircleSet` in `ℝ × ℝ` is the union of:

* the vertical limit segment `TauCeti.warsawCircleLimitSegment = {0} × [-1, 1]`;
* the oscillatory graph `TauCeti.warsawCircleSineGraph = {(x, sin x⁻¹) | x ∈ (0, 1]}`; and
* the three-segment closing arc `TauCeti.warsawCircleClosingArc` running from `(0, -1)` through
  `(0, -2)` and `(1, -2)` to `(1, sin 1)`.

Although `WarsawCircle` is a compact metric continuum, the half-line `[0, ∞)` parameterizes it by
a continuous bijection `TauCeti.WarsawCircle.ofHalfLine : C(Ici (0 : ℝ), WarsawCircle)` that
traverses `{0} × [-2, 1]` on `[0, 3]`, the bottom and right edges of the closing arc on `[3, 5]`,
and the oscillatory sine graph `((t - 4)⁻¹, sin (t - 4))` on `[5, ∞)`. In particular `WarsawCircle`
is path-connected, unlike the closed topologist's sine curve itself.

The key geometric property of `ofHalfLine`, from which the vanishing of all homotopy groups of
`WarsawCircle` follows in `TauCeti.AlgebraicTopology.WarsawCircle.Homotopy`, is a **lifting
theorem** (`TauCeti.WarsawCircle.existsUnique_lift_ofHalfLine`): every continuous map
`f : C(K, WarsawCircle)` from a compact, locally path-connected space `K` lifts uniquely to a
continuous map `g : C(K, Ici (0 : ℝ))` with `ofHalfLine.comp g = f`. Indeed, inside the open
window `x < 1, y > -3/2` of `WarsawCircle`, no path can join a point on the vertical axis `x = 0`
to a point with `x > 0` (`TauCeti.WarsawCircle.not_joinedIn_oscillationOpen`). If the parameter
values of `f` were unbounded on `[5, ∞)`, a cluster point `k₀` of a sequence with `t_n → ∞` would
map into the limit segment while a path-connected neighborhood of `k₀` inside the preimage of that
open window would contain some `k_n` mapping to `x > 0`, a contradiction. Thus `f` lands in the
image of a compact prefix `[0, M]`, on which `ofHalfLine` restricts to a closed embedding. As an
immediate consequence, `WarsawCircle` itself is not locally path-connected
(`TauCeti.WarsawCircle.not_locallyPathConnectedSpace`).

The oscillation argument in `not_joinedIn_oscillationOpen` adapts the classical intermediate-value
proof that the topologist's sine curve is not path-connected (see also
`Counterexamples/TopologistsSineCurve.lean` in the Mathlib repository, by Daniele Bolla and David
Loeffler).

## Main definitions

* `TauCeti.warsawCircleLimitSegment`, `TauCeti.warsawCircleSineGraph`,
  `TauCeti.warsawCircleSineCurve`, `TauCeti.warsawCircleClosingArc`, `TauCeti.warsawCircleSet`:
  the planar subsets building the Warsaw circle.
* `TauCeti.WarsawCircle`: the Warsaw circle as a subspace of `ℝ × ℝ`, with marked points
  `TauCeti.WarsawCircle.basepoint`, `TauCeti.WarsawCircle.origin`, and
  `TauCeti.WarsawCircle.rightEndpoint`.
* `TauCeti.WarsawCircle.ofHalfLine`: the continuous bijection `C(Ici (0 : ℝ), WarsawCircle)`.

## Main results

* `TauCeti.closure_warsawCircleSineGraph`: the closure of the sine graph on `(0, 1]` is its union
  with the vertical limit segment `{0} × [-1, 1]`.
* `TauCeti.isCompact_warsawCircleSet` and `CompactSpace TauCeti.WarsawCircle`: compactness of the
  Warsaw circle.
* `TauCeti.WarsawCircle.ofHalfLine_bijective` and `PathConnectedSpace TauCeti.WarsawCircle`:
  `ofHalfLine` is a continuous bijection, so the Warsaw circle is path-connected.
* `TauCeti.WarsawCircle.existsUnique_lift_ofHalfLine`: **every continuous map from a compact
  locally path-connected space to `WarsawCircle` lifts uniquely to `[0, ∞)`.**
* `TauCeti.WarsawCircle.not_locallyPathConnectedSpace`: the Warsaw circle is not locally
  path-connected.

## References

* R. Schwamberger and R. M. Vogt, *Dold spaces in homotopy theory*, Algebr. Geom. Topol. **9**
  (2009), 1585--1622.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.3 and Section 4.1.
* D. Bolla and D. Loeffler, `Counterexamples.TopologistsSineCurve` in the Mathlib repository, for
  the oscillation argument on `sin x⁻¹`.
-/

public section

noncomputable section

open Filter Function Set Topology

namespace TauCeti

/-! ### Planar pieces of the Warsaw circle -/

/-- The vertical limit segment `{0} × [-1, 1]` of the Warsaw circle. -/
def warsawCircleLimitSegment : Set (ℝ × ℝ) :=
  {0} ×ˢ Icc (-1) 1

/-- The oscillatory sine graph `{(x, sin x⁻¹) | x ∈ (0, 1]}` of the Warsaw circle. -/
def warsawCircleSineGraph : Set (ℝ × ℝ) :=
  (fun x : ℝ ↦ (x, Real.sin x⁻¹)) '' Ioc 0 1

/-- The closed topologist's sine curve on `[0, 1]`: the union of the vertical limit segment and
the oscillatory sine graph. -/
def warsawCircleSineCurve : Set (ℝ × ℝ) :=
  warsawCircleLimitSegment ∪ warsawCircleSineGraph

/-- The polygonal closing arc joining `(0, -1)` to `(1, sin 1)` through `(0, -2)` and `(1, -2)`. -/
def warsawCircleClosingArc : Set (ℝ × ℝ) :=
  ({0} ×ˢ Icc (-2) (-1)) ∪ (Icc 0 1 ×ˢ {-2}) ∪ ({1} ×ˢ Icc (-2) (Real.sin 1))

/-- The underlying subset of `ℝ × ℝ` of the Warsaw circle. -/
def warsawCircleSet : Set (ℝ × ℝ) :=
  warsawCircleSineCurve ∪ warsawCircleClosingArc

/-- Membership characterization for `warsawCircleLimitSegment`. -/
@[simp]
theorem mem_warsawCircleLimitSegment_iff {p : ℝ × ℝ} :
    p ∈ warsawCircleLimitSegment ↔ p.1 = 0 ∧ p.2 ∈ Icc (-1) 1 := by
  simp [warsawCircleLimitSegment]

/-- Membership characterization for `warsawCircleSineGraph`. -/
@[simp]
theorem mem_warsawCircleSineGraph_iff {p : ℝ × ℝ} :
    p ∈ warsawCircleSineGraph ↔ p.1 ∈ Ioc 0 1 ∧ p.2 = Real.sin p.1⁻¹ := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨hx, hy⟩
    exact ⟨p.1, hx, Prod.ext rfl hy.symm⟩

/-- Membership characterization for `warsawCircleSineCurve`. -/
theorem mem_warsawCircleSineCurve_iff {p : ℝ × ℝ} :
    p ∈ warsawCircleSineCurve ↔ p ∈ warsawCircleLimitSegment ∨ p ∈ warsawCircleSineGraph :=
  Iff.rfl

/-- Membership characterization for `warsawCircleClosingArc`. -/
@[simp]
theorem mem_warsawCircleClosingArc_iff {p : ℝ × ℝ} :
    p ∈ warsawCircleClosingArc ↔
      (p.1 = 0 ∧ p.2 ∈ Icc (-2) (-1)) ∨
      (p.1 ∈ Icc 0 1 ∧ p.2 = -2) ∨
      (p.1 = 1 ∧ p.2 ∈ Icc (-2) (Real.sin 1)) := by
  simp [warsawCircleClosingArc, or_assoc]

/-- Membership characterization for `warsawCircleSet`. -/
theorem mem_warsawCircleSet_iff {p : ℝ × ℝ} :
    p ∈ warsawCircleSet ↔ p ∈ warsawCircleSineCurve ∨ p ∈ warsawCircleClosingArc :=
  Iff.rfl

/-- `warsawCircleSineCurve` as the union of the vertical limit segment and the sine graph. -/
theorem warsawCircleSineCurve_eq_union :
    warsawCircleSineCurve = warsawCircleLimitSegment ∪ warsawCircleSineGraph :=
  (rfl)

/-- `warsawCircleSet` as the union of `warsawCircleSineCurve` and `warsawCircleClosingArc`. -/
theorem warsawCircleSet_eq_union :
    warsawCircleSet = warsawCircleSineCurve ∪ warsawCircleClosingArc :=
  (rfl)

/-- For every `y ∈ [-1, 1]` and `a > 0`, `warsawCircleSineGraph` attains height `y` at some
`x ∈ (0, a]`. -/
theorem exists_mem_Ioc_warsawCircleSineGraph {y : ℝ} (hy : y ∈ Icc (-1) 1) {a : ℝ} (ha : 0 < a) :
    ∃ x ∈ Ioc 0 a, (x, y) ∈ warsawCircleSineGraph := by
  have hb : 0 < min a 1 := lt_min ha zero_lt_one
  obtain ⟨n, hn⟩ := exists_nat_gt (((min a 1)⁻¹ - Real.arcsin y) / (2 * Real.pi))
  have hpi : 0 < 2 * Real.pi := by positivity
  have ht_gt : (min a 1)⁻¹ < Real.arcsin y + n * (2 * Real.pi) := by
    have := (div_lt_iff₀ hpi).mp hn
    linarith
  have ht_pos : 0 < Real.arcsin y + n * (2 * Real.pi) :=
    lt_trans (inv_pos.mpr hb) ht_gt
  have hx_lt : (Real.arcsin y + n * (2 * Real.pi))⁻¹ < min a 1 :=
    (inv_lt_comm₀ hb ht_pos).mp ht_gt
  refine ⟨(Real.arcsin y + n * (2 * Real.pi))⁻¹,
    ⟨inv_pos.mpr ht_pos, hx_lt.le.trans (min_le_left a 1)⟩,
    mem_warsawCircleSineGraph_iff.mpr ⟨⟨inv_pos.mpr ht_pos, hx_lt.le.trans (min_le_right a 1)⟩, ?_⟩⟩
  dsimp
  rw [inv_inv, Real.sin_add_nat_mul_two_pi, Real.sin_arcsin hy.1 hy.2]

/-- **The closure of the oscillatory sine graph on `(0, 1]` is `warsawCircleSineCurve`.** -/
theorem closure_warsawCircleSineGraph :
    closure warsawCircleSineGraph = warsawCircleSineCurve := by
  refine Subset.antisymm ?_ ?_
  · intro p hp
    rw [mem_closure_iff_seq_limit] at hp
    obtain ⟨u, hu, hlim⟩ := hp
    have hx_mem : p.1 ∈ Icc 0 1 := by
      refine isClosed_Icc.mem_of_tendsto (continuous_fst.tendsto p |>.comp hlim)
        (Eventually.of_forall fun n ↦ ?_)
      have h := (mem_warsawCircleSineGraph_iff.mp (hu n)).1
      exact ⟨h.1.le, h.2⟩
    rcases hx_mem.1.eq_or_lt with hx0 | hx_pos
    · left
      refine mem_warsawCircleLimitSegment_iff.mpr ⟨hx0.symm, ?_⟩
      refine isClosed_Icc.mem_of_tendsto (continuous_snd.tendsto p |>.comp hlim)
        (Eventually.of_forall fun n ↦ ?_)
      dsimp
      rw [(mem_warsawCircleSineGraph_iff.mp (hu n)).2]
      exact Real.sin_mem_Icc _
    · right
      refine mem_warsawCircleSineGraph_iff.mpr ⟨⟨hx_pos, hx_mem.2⟩, ?_⟩
      have hcont : ContinuousAt (fun x : ℝ ↦ Real.sin x⁻¹) p.1 :=
        Real.continuous_sin.continuousAt.comp (continuousAt_inv₀ hx_pos.ne')
      refine tendsto_nhds_unique (continuous_snd.tendsto p |>.comp hlim) ?_
      refine (hcont.tendsto.comp (continuous_fst.tendsto p |>.comp hlim)).congr fun n ↦ ?_
      exact ((mem_warsawCircleSineGraph_iff.mp (hu n)).2).symm
  · rintro ⟨x, y⟩ (hp | hp)
    · have hp' := mem_warsawCircleLimitSegment_iff.mp hp
      dsimp at hp'
      obtain ⟨rfl, hy⟩ := hp'
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨x, ⟨hx0, hxa⟩, hx_mem⟩ := exists_mem_Ioc_warsawCircleSineGraph hy (half_pos hε)
      refine ⟨(x, y), hx_mem, ?_⟩
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, dist_comm, Real.dist_eq, sub_zero,
        abs_of_pos hx0]
      linarith
    · exact subset_closure hp

/-- The vertical limit segment is closed in `ℝ × ℝ`. -/
theorem isClosed_warsawCircleLimitSegment : IsClosed warsawCircleLimitSegment :=
  isClosed_singleton.prod isClosed_Icc

/-- The closed topologist's sine curve on `[0, 1]` is closed in `ℝ × ℝ`. -/
theorem isClosed_warsawCircleSineCurve : IsClosed warsawCircleSineCurve :=
  closure_warsawCircleSineGraph ▸ isClosed_closure

/-- The polygonal closing arc is closed in `ℝ × ℝ`. -/
theorem isClosed_warsawCircleClosingArc : IsClosed warsawCircleClosingArc :=
  ((isClosed_singleton.prod isClosed_Icc).union (isClosed_Icc.prod isClosed_singleton)).union
    (isClosed_singleton.prod isClosed_Icc)

/-- The underlying set of the Warsaw circle is closed in `ℝ × ℝ`. -/
theorem isClosed_warsawCircleSet : IsClosed warsawCircleSet :=
  isClosed_warsawCircleSineCurve.union isClosed_warsawCircleClosingArc

/-- `Real.sin 1 + 2` is strictly positive, since `-1 ≤ sin 1`. -/
private theorem sin_one_add_two_pos : 0 < Real.sin 1 + 2 := by
  linarith [Real.neg_one_le_sin 1]

/-- The closed sine curve and the closing arc meet solely at `(0, -1)` and `(1, sin 1)`. -/
theorem warsawCircleSineCurve_inter_warsawCircleClosingArc :
    warsawCircleSineCurve ∩ warsawCircleClosingArc = {(0, -1), (1, Real.sin 1)} := by
  ext ⟨x, y⟩
  simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hs, hc⟩
    have hy_ge : -1 ≤ y := by
      rcases hs with hlim | hgr
      · exact (mem_warsawCircleLimitSegment_iff.mp hlim).2.1
      · have hgr' := (mem_warsawCircleSineGraph_iff.mp hgr).2
        dsimp at hgr'
        rw [hgr']
        exact Real.neg_one_le_sin _
    rcases mem_warsawCircleClosingArc_iff.mp hc with ⟨rfl, _, hy2⟩ | ⟨_, rfl⟩ | ⟨rfl, _⟩
    · exact Or.inl ⟨rfl, le_antisymm hy2 hy_ge⟩
    · linarith
    · rcases hs with hlim | hgr
      · exact absurd (mem_warsawCircleLimitSegment_iff.mp hlim).1 one_ne_zero
      · have hy_eq := (mem_warsawCircleSineGraph_iff.mp hgr).2
        dsimp at hy_eq
        rw [inv_one] at hy_eq
        exact Or.inr ⟨rfl, hy_eq⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Or.inl ⟨rfl, le_rfl, by norm_num⟩,
        mem_warsawCircleClosingArc_iff.mpr (Or.inl ⟨rfl, by norm_num, le_rfl⟩)⟩
    · refine ⟨Or.inr (mem_warsawCircleSineGraph_iff.mpr ⟨⟨zero_lt_one, le_rfl⟩, by simp⟩), ?_⟩
      refine mem_warsawCircleClosingArc_iff.mpr (Or.inr (Or.inr ⟨rfl, ?_, le_rfl⟩))
      linarith [sin_one_add_two_pos]

/-- The Warsaw circle lies inside the rectangle `[0, 1] × [-2, 1]`. -/
theorem warsawCircleSet_subset_box : warsawCircleSet ⊆ Icc 0 1 ×ˢ Icc (-2) 1 := by
  rintro ⟨x, y⟩ (hs | hc)
  · rcases hs with hlim | hgr
    · have hlim' := mem_warsawCircleLimitSegment_iff.mp hlim
      dsimp at hlim'
      obtain ⟨rfl, hy1, hy2⟩ := hlim'
      exact ⟨⟨le_rfl, zero_le_one⟩, ⟨by linarith, hy2⟩⟩
    · have hgr' := mem_warsawCircleSineGraph_iff.mp hgr
      dsimp at hgr'
      obtain ⟨⟨hx0, hx1⟩, rfl⟩ := hgr'
      exact ⟨⟨hx0.le, hx1⟩, ⟨by linarith [Real.neg_one_le_sin x⁻¹], Real.sin_le_one x⁻¹⟩⟩
  · have hc' := mem_warsawCircleClosingArc_iff.mp hc
    dsimp at hc'
    rcases hc' with ⟨rfl, hy1, hy2⟩ | ⟨hx, rfl⟩ | ⟨rfl, hy1, hy2⟩
    · exact ⟨⟨le_rfl, zero_le_one⟩, ⟨hy1, by linarith⟩⟩
    · exact ⟨hx, ⟨le_rfl, by norm_num⟩⟩
    · exact ⟨⟨zero_le_one, le_rfl⟩, ⟨hy1, hy2.trans (Real.sin_le_one 1)⟩⟩

/-- **The underlying set of the Warsaw circle is compact.** -/
theorem isCompact_warsawCircleSet : IsCompact warsawCircleSet :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_warsawCircleSet
    warsawCircleSet_subset_box

/-! ### The space `WarsawCircle` and its half-line parameterization -/

/-- **The Warsaw circle**: the compact planar continuum obtained by joining `(1, sin 1)` on the
closed topologist's sine curve to `(0, -1)` along a polygonal arc. It is path-connected and simply
connected (`TauCeti.WarsawCircle.instSimplyConnectedSpace`) with trivial homotopy groups in all
dimensions (`TauCeti.WarsawCircle.instSubsingletonHomotopyGroup`), yet it is not contractible
(`TauCeti.WarsawCircle.not_contractibleSpace`). -/
abbrev WarsawCircle : Type := warsawCircleSet

namespace WarsawCircle

/-- **The Warsaw circle is compact.** -/
instance instCompactSpace : CompactSpace WarsawCircle :=
  isCompact_iff_compactSpace.mp isCompact_warsawCircleSet

/-- The base point `(0, -1)` of the Warsaw circle, where the closing arc meets the vertical limit
segment. -/
def basepoint : WarsawCircle :=
  ⟨(0, -1), Or.inl (Or.inl ⟨rfl, le_rfl, by norm_num⟩)⟩

/-- Coercion of `WarsawCircle.basepoint` to `ℝ × ℝ`. -/
@[simp]
theorem coe_basepoint : (basepoint : ℝ × ℝ) = (0, -1) :=
  (rfl)

/-- The midpoint `(0, 0)` of the vertical limit segment of the Warsaw circle. -/
def origin : WarsawCircle :=
  ⟨(0, 0), Or.inl (Or.inl ⟨rfl, by norm_num, by norm_num⟩)⟩

/-- Coercion of `WarsawCircle.origin` to `ℝ × ℝ`. -/
@[simp]
theorem coe_origin : (origin : ℝ × ℝ) = (0, 0) :=
  (rfl)

/-- The junction `(1, sin 1)` where the closing arc meets the oscillatory sine graph. -/
def rightEndpoint : WarsawCircle :=
  ⟨(1, Real.sin 1), Or.inl (Or.inr (mem_warsawCircleSineGraph_iff.mpr
    ⟨⟨zero_lt_one, le_rfl⟩, by simp⟩))⟩

/-- Coercion of `WarsawCircle.rightEndpoint` to `ℝ × ℝ`. -/
@[simp]
theorem coe_rightEndpoint : (rightEndpoint : ℝ × ℝ) = (1, Real.sin 1) :=
  (rfl)

/-- The raw piecewise curve `ℝ → ℝ × ℝ` tracing `{0} × [-2, 1]` on `[0, 3]`, the bottom and right
segments of the closing arc on `[3, 5]`, and `((t - 4)⁻¹, sin (t - 4))` on `[5, ∞)`. -/
private def rawOfHalfLine (t : ℝ) : ℝ × ℝ :=
  if t ≤ 3 then (0, 1 - t)
  else if t ≤ 4 then (t - 3, -2)
  else if t ≤ 5 then (1, -2 + (t - 4) * (Real.sin 1 + 2))
  else ((t - 4)⁻¹, Real.sin (t - 4))

/-- Continuity of `rawOfHalfLine` on `ℝ`. -/
private theorem continuous_rawOfHalfLine : Continuous rawOfHalfLine := by
  have h5 : Continuous fun t : ℝ ↦
      if t ≤ 5 then (1, -2 + (t - 4) * (Real.sin 1 + 2)) else ((t - 4)⁻¹, Real.sin (t - 4)) := by
    refine continuous_if_le continuous_id continuous_const (by fun_prop) ?_
      (by intro t ht; subst ht; norm_num)
    refine ContinuousOn.prodMk ?_ (by fun_prop)
    exact (continuousOn_id.sub continuousOn_const).inv₀ fun t ht ↦ by
      have ht5 : 5 ≤ t := ht
      dsimp; linarith
  have h4 : Continuous fun t : ℝ ↦
      if t ≤ 4 then (t - 3, -2)
      else if t ≤ 5 then (1, -2 + (t - 4) * (Real.sin 1 + 2))
      else ((t - 4)⁻¹, Real.sin (t - 4)) :=
    continuous_if_le continuous_id continuous_const (by fun_prop) h5.continuousOn
      (by intro t ht; subst ht; norm_num)
  exact continuous_if_le continuous_id continuous_const (by fun_prop) h4.continuousOn
    (by intro t ht; subst ht; norm_num)

/-- Every point `rawOfHalfLine t` for `t ≥ 0` lies on the Warsaw circle. -/
private theorem rawOfHalfLine_mem {t : ℝ} (ht : 0 ≤ t) : rawOfHalfLine t ∈ warsawCircleSet := by
  unfold rawOfHalfLine
  split_ifs with h3 h4 h5
  · rcases le_or_gt t 2 with h2 | h2
    · exact Or.inl (Or.inl ⟨rfl, by linarith, by linarith⟩)
    · exact Or.inr (mem_warsawCircleClosingArc_iff.mpr (Or.inl ⟨rfl, by linarith, by linarith⟩))
  · exact Or.inr (mem_warsawCircleClosingArc_iff.mpr
      (Or.inr (Or.inl ⟨⟨by linarith, by linarith⟩, rfl⟩)))
  · have hpos := sin_one_add_two_pos.le
    exact Or.inr (mem_warsawCircleClosingArc_iff.mpr
      (Or.inr (Or.inr ⟨rfl, by nlinarith, by nlinarith⟩)))
  · refine Or.inl (Or.inr (mem_warsawCircleSineGraph_iff.mpr ⟨⟨?_, ?_⟩, ?_⟩))
    · exact inv_pos.mpr (by linarith)
    · exact inv_le_one_of_one_le₀ (by linarith)
    · dsimp; rw [inv_inv]

/-- **The continuous parameterization `C(Ici (0 : ℝ), WarsawCircle)` of the Warsaw circle by the
closed half-line `[0, ∞)`.** -/
def ofHalfLine : C(Ici (0 : ℝ), WarsawCircle) where
  toFun t := ⟨rawOfHalfLine t.val, rawOfHalfLine_mem t.property⟩
  continuous_toFun := (continuous_rawOfHalfLine.comp continuous_subtypeVal).subtype_mk _

/-- Formula for `ofHalfLine t` when `t ≤ 3`. -/
theorem coe_ofHalfLine_of_le_three {t : Ici (0 : ℝ)} (ht : (t : ℝ) ≤ 3) :
    (ofHalfLine t : ℝ × ℝ) = (0, 1 - t.val) := by
  simp [ofHalfLine, rawOfHalfLine, ht]

/-- Formula for `ofHalfLine t` when `3 ≤ t ≤ 4`. -/
theorem coe_ofHalfLine_of_mem_Icc_three_four {t : Ici (0 : ℝ)} (ht : (t : ℝ) ∈ Icc 3 4) :
    (ofHalfLine t : ℝ × ℝ) = (t.val - 3, -2) := by
  rcases ht.1.eq_or_lt with h3 | h3
  · rw [coe_ofHalfLine_of_le_three h3.symm.le, ← h3]; norm_num
  · simp [ofHalfLine, rawOfHalfLine, not_le.mpr h3, ht.2]

/-- Formula for `ofHalfLine t` when `4 ≤ t ≤ 5`. -/
theorem coe_ofHalfLine_of_mem_Icc_four_five {t : Ici (0 : ℝ)} (ht : (t : ℝ) ∈ Icc 4 5) :
    (ofHalfLine t : ℝ × ℝ) = (1, -2 + (t.val - 4) * (Real.sin 1 + 2)) := by
  rcases ht.1.eq_or_lt with h4 | h4
  · rw [coe_ofHalfLine_of_mem_Icc_three_four ⟨by linarith, h4.symm.le⟩, ← h4]; norm_num
  · simp [ofHalfLine, rawOfHalfLine, not_le.mpr (by linarith : (3 : ℝ) < t.val),
      not_le.mpr h4, ht.2]

/-- Formula for `ofHalfLine t` when `5 ≤ t`. -/
theorem coe_ofHalfLine_of_five_le {t : Ici (0 : ℝ)} (ht : 5 ≤ (t : ℝ)) :
    (ofHalfLine t : ℝ × ℝ) = ((t.val - 4)⁻¹, Real.sin (t.val - 4)) := by
  rcases ht.eq_or_lt with h5 | h5
  · rw [coe_ofHalfLine_of_mem_Icc_four_five ⟨by linarith, h5.symm.le⟩, ← h5]; norm_num
  · simp [ofHalfLine, rawOfHalfLine, not_le.mpr (by linarith : (3 : ℝ) < t.val),
      not_le.mpr (by linarith : (4 : ℝ) < t.val), not_le.mpr h5]

/-- At `t = 1`, `ofHalfLine` hits `WarsawCircle.origin = (0, 0)`. -/
@[simp]
theorem ofHalfLine_one : ofHalfLine ⟨1, zero_le_one⟩ = origin :=
  Subtype.ext <| by
    rw [coe_ofHalfLine_of_le_three (t := ⟨1, zero_le_one⟩) (by dsimp; norm_num)]
    norm_num

/-- At `t = 2`, `ofHalfLine` hits `WarsawCircle.basepoint = (0, -1)`. -/
@[simp]
theorem ofHalfLine_two : ofHalfLine ⟨2, by norm_num⟩ = basepoint :=
  Subtype.ext <| by
    rw [coe_ofHalfLine_of_le_three (t := ⟨2, by norm_num⟩) (by dsimp; norm_num)]
    norm_num

/-- At `t = 5`, `ofHalfLine` hits `WarsawCircle.rightEndpoint = (1, sin 1)`. -/
@[simp]
theorem ofHalfLine_five : ofHalfLine ⟨5, by norm_num⟩ = rightEndpoint :=
  Subtype.ext <| by
    rw [coe_ofHalfLine_of_five_le (t := ⟨5, by norm_num⟩) (by dsimp; exact le_rfl)]
    norm_num

/-- Parameters `t ∈ [0, 2]` trace the vertical limit segment `{0} × [-1, 1]`. -/
theorem coe_ofHalfLine_mem_warsawCircleLimitSegment_of_le_two {t : Ici (0 : ℝ)}
    (ht : (t : ℝ) ≤ 2) : (ofHalfLine t : ℝ × ℝ) ∈ warsawCircleLimitSegment := by
  have ht0 : 0 ≤ t.val := mem_Ici.mp t.property
  rw [coe_ofHalfLine_of_le_three (by linarith), mem_warsawCircleLimitSegment_iff]
  exact ⟨rfl, by dsimp; linarith, by dsimp; linarith⟩

/-- Parameters `t ∈ [2, 5]` trace the closing arc `warsawCircleClosingArc`. -/
theorem coe_ofHalfLine_mem_warsawCircleClosingArc_of_mem_Icc {t : Ici (0 : ℝ)}
    (ht : (t : ℝ) ∈ Icc 2 5) : (ofHalfLine t : ℝ × ℝ) ∈ warsawCircleClosingArc := by
  rcases le_or_gt t.val 3 with h3 | h3
  · rw [coe_ofHalfLine_of_le_three h3, mem_warsawCircleClosingArc_iff]
    exact Or.inl ⟨rfl, by dsimp; linarith [ht.1], by dsimp; linarith [ht.1]⟩
  · rcases le_or_gt t.val 4 with h4 | h4
    · rw [coe_ofHalfLine_of_mem_Icc_three_four ⟨h3.le, h4⟩, mem_warsawCircleClosingArc_iff]
      exact Or.inr (Or.inl ⟨⟨by dsimp; linarith, by dsimp; linarith⟩, rfl⟩)
    · rw [coe_ofHalfLine_of_mem_Icc_four_five ⟨h4.le, ht.2⟩, mem_warsawCircleClosingArc_iff]
      have hpos := sin_one_add_two_pos.le
      exact Or.inr (Or.inr ⟨rfl, by dsimp; nlinarith [ht.2], by dsimp; nlinarith [ht.2]⟩)

/-- Parameters `t ≥ 5` trace the oscillatory sine graph `warsawCircleSineGraph`. -/
theorem coe_ofHalfLine_mem_warsawCircleSineGraph_of_five_le {t : Ici (0 : ℝ)}
    (ht : 5 ≤ (t : ℝ)) : (ofHalfLine t : ℝ × ℝ) ∈ warsawCircleSineGraph := by
  rw [coe_ofHalfLine_of_five_le ht, mem_warsawCircleSineGraph_iff]
  exact ⟨⟨inv_pos.mpr (by linarith), inv_le_one_of_one_le₀ (by linarith)⟩,
    by dsimp; rw [inv_inv]⟩

/-- Region classification of `ofHalfLine t` separating `[0, 3]`, `(3, 4]`, `(4, 5)`, and
`[5, ∞)` by pairwise disjoint coordinate properties. -/
private theorem ofHalfLine_region (t : Ici (0 : ℝ)) :
    ((t : ℝ) ≤ 3 ∧ (ofHalfLine t : ℝ × ℝ) = (0, 1 - t.val)) ∨
    ((t : ℝ) ∈ Ioc 3 4 ∧ (ofHalfLine t : ℝ × ℝ) = (t.val - 3, -2)) ∨
    ((t : ℝ) ∈ Ioo 4 5 ∧ (ofHalfLine t : ℝ × ℝ) = (1, -2 + (t.val - 4) * (Real.sin 1 + 2)) ∧
      (ofHalfLine t : ℝ × ℝ).2 ∈ Ioo (-2) (Real.sin 1)) ∨
    (5 ≤ (t : ℝ) ∧ (ofHalfLine t : ℝ × ℝ) = ((t.val - 4)⁻¹, Real.sin (t.val - 4))) := by
  rcases le_or_gt t.val 3 with h3 | h3
  · exact Or.inl ⟨h3, coe_ofHalfLine_of_le_three h3⟩
  rcases le_or_gt t.val 4 with h4 | h4
  · exact Or.inr (Or.inl ⟨⟨h3, h4⟩, coe_ofHalfLine_of_mem_Icc_three_four ⟨h3.le, h4⟩⟩)
  rcases lt_or_ge t.val 5 with h5 | h5
  · refine Or.inr (Or.inr (Or.inl ⟨⟨h4, h5⟩,
      coe_ofHalfLine_of_mem_Icc_four_five ⟨h4.le, h5.le⟩, ?_⟩))
    rw [coe_ofHalfLine_of_mem_Icc_four_five ⟨h4.le, h5.le⟩]
    have hpos := sin_one_add_two_pos
    exact ⟨by dsimp; nlinarith, by dsimp; nlinarith⟩
  · exact Or.inr (Or.inr (Or.inr ⟨h5, coe_ofHalfLine_of_five_le h5⟩))

/-- `ofHalfLine t` lands in the vertical limit segment `{0} × [-1, 1]` if and only if `t ≤ 2`. -/
theorem coe_ofHalfLine_mem_warsawCircleLimitSegment_iff {t : Ici (0 : ℝ)} :
    (ofHalfLine t : ℝ × ℝ) ∈ warsawCircleLimitSegment ↔ (t : ℝ) ≤ 2 := by
  refine ⟨fun h ↦ ?_, coe_ofHalfLine_mem_warsawCircleLimitSegment_of_le_two⟩
  obtain ⟨hx0, hy⟩ := mem_warsawCircleLimitSegment_iff.mp h
  rcases ofHalfLine_region t with ⟨_, eq_t⟩ | ⟨ht, eq_t⟩ | ⟨_, eq_t, -⟩ | ⟨ht, eq_t⟩
  · rw [eq_t] at hy; dsimp at hy; linarith [hy.1]
  · rw [eq_t] at hx0; dsimp at hx0; linarith [ht.1]
  · rw [eq_t] at hx0; norm_num at hx0
  · rw [eq_t] at hx0; exact absurd hx0 (inv_pos.mpr (by linarith)).ne'

/-- **`WarsawCircle.ofHalfLine` is injective.** -/
theorem ofHalfLine_injective : Injective ofHalfLine := by
  intro s t hst
  have hval : (ofHalfLine s : ℝ × ℝ) = (ofHalfLine t : ℝ × ℝ) := congrArg Subtype.val hst
  ext
  have hpos := sin_one_add_two_pos
  have h54 : (5 : ℝ) - 4 = 1 := by norm_num
  rcases ofHalfLine_region s with ⟨_, eq_s⟩ | ⟨hs, eq_s⟩ | ⟨_, eq_s, hys⟩ | ⟨hs, eq_s⟩ <;>
    rcases ofHalfLine_region t with ⟨_, eq_t⟩ | ⟨ht, eq_t⟩ | ⟨_, eq_t, hyt⟩ | ⟨ht, eq_t⟩
  · have := congrArg Prod.snd (eq_s.symm.trans (hval.trans eq_t)); linarith
  · have := congrArg Prod.fst (eq_s.symm.trans (hval.trans eq_t)); linarith [ht.1]
  · have := congrArg Prod.fst (eq_s.symm.trans (hval.trans eq_t)); norm_num at this
  · have := congrArg Prod.fst (eq_s.symm.trans (hval.trans eq_t))
    exact absurd this.symm (inv_pos.mpr (by linarith)).ne'
  · have := congrArg Prod.fst (eq_s.symm.trans (hval.trans eq_t)); linarith [hs.1]
  · have := congrArg Prod.fst (eq_s.symm.trans (hval.trans eq_t)); linarith
  · rw [hval] at eq_s; rw [eq_s] at hyt; norm_num at hyt
  · have := congrArg Prod.snd (eq_s.symm.trans (hval.trans eq_t))
    linarith [Real.neg_one_le_sin (t.val - 4)]
  · have := congrArg Prod.fst (eq_s.symm.trans (hval.trans eq_t)); norm_num at this
  · rw [← hval] at eq_t; rw [eq_t] at hys; norm_num at hys
  · have := congrArg Prod.snd (eq_s.symm.trans (hval.trans eq_t)); nlinarith
  · have hfst := congrArg Prod.fst (eq_s.symm.trans (hval.trans eq_t))
    have ht5 : t.val = 5 := by
      have : (t.val - 4)⁻¹ = 1 := hfst.symm
      have : t.val - 4 = 1 := inv_eq_one.mp this
      linarith
    have hsnd := congrArg Prod.snd (hval.trans eq_t)
    rw [ht5, h54] at hsnd
    linarith [hys.2]
  · have := congrArg Prod.fst (eq_s.symm.trans (hval.trans eq_t))
    exact absurd this (inv_pos.mpr (by linarith)).ne'
  · have := congrArg Prod.snd (eq_s.symm.trans (hval.trans eq_t))
    linarith [Real.neg_one_le_sin (s.val - 4)]
  · have hfst := congrArg Prod.fst (eq_s.symm.trans (hval.trans eq_t))
    have hs5 : s.val = 5 := by
      have : s.val - 4 = 1 := inv_eq_one.mp hfst
      linarith
    have hsnd := congrArg Prod.snd (hval.symm.trans eq_s)
    rw [hs5, h54] at hsnd
    linarith [hyt.2]
  · have hfst := congrArg Prod.fst (eq_s.symm.trans (hval.trans eq_t))
    have := inv_injective hfst
    linarith

/-- **`WarsawCircle.ofHalfLine` is surjective.** -/
theorem ofHalfLine_surjective : Surjective ofHalfLine := by
  rintro ⟨⟨x, y⟩, hp⟩
  rcases hp with (hlim | hgr) | hc
  · have hlim' := mem_warsawCircleLimitSegment_iff.mp hlim
    dsimp at hlim'
    obtain ⟨rfl, hy1, hy2⟩ := hlim'
    refine ⟨⟨1 - y, mem_Ici.mpr (by linarith)⟩, Subtype.ext ?_⟩
    rw [coe_ofHalfLine_of_le_three (by dsimp; linarith)]; ring_nf
  · obtain ⟨⟨hx0, hx1⟩, hy⟩ := mem_warsawCircleSineGraph_iff.mp hgr
    dsimp at hx0 hx1 hy
    subst hy
    have h1 : 1 ≤ x⁻¹ := (one_le_inv₀ hx0).mpr hx1
    refine ⟨⟨4 + x⁻¹, mem_Ici.mpr (by positivity)⟩, Subtype.ext ?_⟩
    rw [coe_ofHalfLine_of_five_le (by dsimp; linarith)]
    simp
  · have hc' := mem_warsawCircleClosingArc_iff.mp hc
    dsimp at hc'
    rcases hc' with ⟨rfl, hy1, hy2⟩ | ⟨⟨hx0, hx1⟩, rfl⟩ | ⟨rfl, hy1, hy2⟩
    · refine ⟨⟨1 - y, mem_Ici.mpr (by linarith)⟩, Subtype.ext ?_⟩
      rw [coe_ofHalfLine_of_le_three (by dsimp; linarith)]; ring_nf
    · refine ⟨⟨x + 3, mem_Ici.mpr (by linarith)⟩, Subtype.ext ?_⟩
      rw [coe_ofHalfLine_of_mem_Icc_three_four ⟨by dsimp; linarith, by dsimp; linarith⟩]
      simp
    · have hpos := sin_one_add_two_pos
      have hdiv0 : 0 ≤ (y + 2) / (Real.sin 1 + 2) := div_nonneg (by linarith) hpos.le
      have hdiv1 : (y + 2) / (Real.sin 1 + 2) ≤ 1 := (div_le_one hpos).mpr (by linarith)
      refine ⟨⟨4 + (y + 2) / (Real.sin 1 + 2), mem_Ici.mpr (by linarith)⟩, Subtype.ext ?_⟩
      rw [coe_ofHalfLine_of_mem_Icc_four_five ⟨by dsimp; linarith, by dsimp; linarith⟩]
      ext
      · rfl
      · dsimp
        rw [add_sub_cancel_left, div_mul_cancel₀ _ hpos.ne']
        ring

/-- **`WarsawCircle.ofHalfLine` is a continuous bijection `[0, ∞) → WarsawCircle`.** -/
theorem ofHalfLine_bijective : Bijective ofHalfLine :=
  ⟨ofHalfLine_injective, ofHalfLine_surjective⟩

/-- **The Warsaw circle is path-connected**, being the continuous image of `[0, ∞)`. -/
instance instPathConnectedSpace : PathConnectedSpace WarsawCircle :=
  have : PathConnectedSpace (Ici (0 : ℝ)) := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Ici (0 : ℝ)).isPathConnected ⟨0, le_rfl⟩)
  ofHalfLine_surjective.pathConnectedSpace ofHalfLine.continuous

/-- Postcomposition with `ofHalfLine` is injective on continuous maps out of any space `K`. -/
theorem ofHalfLine_comp_injective {K : Type*} [TopologicalSpace K] :
    Injective (fun g : C(K, Ici (0 : ℝ)) ↦ ofHalfLine.comp g) := by
  intro g₁ g₂ h
  exact ContinuousMap.ext fun k ↦ ofHalfLine_injective (DFunLike.congr_fun h k)

/-- On every compact prefix `[0, M]`, `ofHalfLine` restricts to a closed embedding. -/
theorem isClosedEmbedding_ofHalfLine_Icc (M : ℝ) :
    IsClosedEmbedding (fun t : Icc (0 : ℝ) M ↦ ofHalfLine ⟨t.val, t.property.1⟩) := by
  have hcont : Continuous (fun t : Icc (0 : ℝ) M ↦ ofHalfLine ⟨t.val, t.property.1⟩) :=
    ofHalfLine.continuous.comp (continuous_subtypeVal.subtype_mk _)
  refine hcont.isClosedEmbedding fun s t hst ↦ ?_
  exact Subtype.ext (congrArg (Subtype.val : Ici (0 : ℝ) → ℝ) (ofHalfLine_injective hst))

/-! ### Lifting maps from compact locally path-connected spaces -/

/-- The open window `x < 1, y > -3/2` of `WarsawCircle`, containing the vertical limit segment and
all points of `ofHalfLine t` for `t > 5`, while excluding the bottom and right edges of the closing
arc. -/
def oscillationOpen : Set WarsawCircle :=
  {p : WarsawCircle | (p : ℝ × ℝ).1 < 1 ∧ -3 / 2 < (p : ℝ × ℝ).2}

/-- Membership characterization for `WarsawCircle.oscillationOpen`. -/
@[simp]
theorem mem_oscillationOpen_iff {p : WarsawCircle} :
    p ∈ oscillationOpen ↔ (p : ℝ × ℝ).1 < 1 ∧ -3 / 2 < (p : ℝ × ℝ).2 :=
  Iff.rfl

/-- `WarsawCircle.oscillationOpen` is open in `WarsawCircle`. -/
theorem isOpen_oscillationOpen : IsOpen oscillationOpen :=
  (isOpen_lt (continuous_fst.comp continuous_subtypeVal) continuous_const).inter
    (isOpen_lt continuous_const (continuous_snd.comp continuous_subtypeVal))

/-- Every point of `WarsawCircle` whose underlying point lies in `warsawCircleSineCurve` with
`x < 1` belongs to `oscillationOpen`. -/
theorem mem_oscillationOpen_of_mem_warsawCircleSineCurve {p : WarsawCircle}
    (hp : (p : ℝ × ℝ) ∈ warsawCircleSineCurve) (hx : (p : ℝ × ℝ).1 < 1) :
    p ∈ oscillationOpen := by
  refine ⟨hx, ?_⟩
  rcases hp with hlim | hgr
  · linarith [(mem_warsawCircleLimitSegment_iff.mp hlim).2.1]
  · rw [(mem_warsawCircleSineGraph_iff.mp hgr).2]
    linarith [Real.neg_one_le_sin (p : ℝ × ℝ).1⁻¹]

/-- Every point in `oscillationOpen` either lies on the vertical axis `x = 0` or satisfies
`0 < x` and `y = sin x⁻¹`. -/
theorem fst_eq_zero_or_pos_and_snd_eq_sin_inv {p : WarsawCircle} (hp : p ∈ oscillationOpen) :
    (p : ℝ × ℝ).1 = 0 ∨ (0 < (p : ℝ × ℝ).1 ∧ (p : ℝ × ℝ).2 = Real.sin (p : ℝ × ℝ).1⁻¹) := by
  obtain ⟨t, rfl⟩ := ofHalfLine_surjective p
  rcases le_or_gt t.val 3 with h3 | h3
  · rw [coe_ofHalfLine_of_le_three h3]
    exact Or.inl rfl
  rcases le_or_gt t.val 4 with h4 | h4
  · have hy := hp.2
    rw [coe_ofHalfLine_of_mem_Icc_three_four ⟨h3.le, h4⟩] at hy
    norm_num at hy
  rcases le_or_gt t.val 5 with h5 | h5
  · have hx := hp.1
    rw [coe_ofHalfLine_of_mem_Icc_four_five ⟨h4.le, h5⟩] at hx
    norm_num at hx
  · rw [coe_ofHalfLine_of_five_le h5.le]
    exact Or.inr ⟨inv_pos.mpr (by linarith), by rw [inv_inv]⟩

/-- Along a path in `oscillationOpen` that vanishes on the `x`-axis at `s₀` and has positive
`x`-coordinate at `s₁ > s₀`, every `y ∈ [-1, 1]` is attained as a `y`-coordinate at some parameter
in `[s₀, s₁]`. -/
private theorem exists_mem_Icc_snd_eq_of_path_in_oscillationOpen {p q : WarsawCircle}
    (γ : Path p q) (hγ : ∀ s, γ s ∈ oscillationOpen) {s₀ s₁ : unitInterval} (hs₀_s₁ : s₀ < s₁)
    (hs₀_zero : (γ s₀ : ℝ × ℝ).1 = 0) (hx₁_pos : 0 < (γ s₁ : ℝ × ℝ).1)
    {y : ℝ} (hy : y ∈ Icc (-1) 1) :
    ∃ t ∈ Icc s₀ s₁, (γ t : ℝ × ℝ).2 = y := by
  have hcont_x : Continuous fun s : unitInterval ↦ (γ s : ℝ × ℝ).1 :=
    continuous_fst.comp (continuous_subtypeVal.comp γ.continuous)
  have hivt : Icc 0 (γ s₁ : ℝ × ℝ).1 ⊆ (fun s ↦ (γ s : ℝ × ℝ).1) '' Icc s₀ s₁ := by
    simpa [hs₀_zero] using intermediate_value_Icc hs₀_s₁.le hcont_x.continuousOn
  obtain ⟨x, ⟨hx0, hx1⟩, hx_mem⟩ := exists_mem_Ioc_warsawCircleSineGraph hy hx₁_pos
  have hsin : y = Real.sin x⁻¹ := (mem_warsawCircleSineGraph_iff.mp hx_mem).2
  obtain ⟨t, ht_mem, htx⟩ := hivt ⟨hx0.le, hx1⟩
  dsimp at htx
  rcases fst_eq_zero_or_pos_and_snd_eq_sin_inv (hγ t) with h0 | ⟨-, hty⟩
  · linarith
  · exact ⟨t, ht_mem, by rw [hty, htx, ← hsin]⟩

/-- **No path in `oscillationOpen` joins a point with `x = 0` to a point with `x > 0`.** -/
theorem not_joinedIn_oscillationOpen {p q : WarsawCircle} (hp0 : (p : ℝ × ℝ).1 = 0)
    (hq0 : 0 < (q : ℝ × ℝ).1) : ¬ JoinedIn oscillationOpen p q := by
  rintro ⟨γ, hγ⟩
  have hcont_x : Continuous fun s : unitInterval ↦ (γ s : ℝ × ℝ).1 :=
    continuous_fst.comp (continuous_subtypeVal.comp γ.continuous)
  have hcont_y : Continuous fun s : unitInterval ↦ (γ s : ℝ × ℝ).2 :=
    continuous_snd.comp (continuous_subtypeVal.comp γ.continuous)
  let s₀ : unitInterval := sSup {s : unitInterval | (γ s : ℝ × ℝ).1 = 0}
  have hs₀_zero : (γ s₀ : ℝ × ℝ).1 = 0 :=
    (isClosed_eq hcont_x continuous_const).sSup_mem ⟨0, by simp [hp0]⟩
  have hs₀_lt : s₀ < 1 := lt_of_le_of_ne (unitInterval.le_one s₀) fun h1 ↦
    hq0.ne' (by rw [← hs₀_zero, h1, γ.target])
  obtain ⟨δ, hδ, hdist⟩ := Metric.continuousAt_iff.mp (hcont_y.continuousAt (x := s₀)) 1 one_pos
  let s₁ : unitInterval := ⟨min ((s₀ : ℝ) + δ / 2) 1,
    ⟨le_min (add_nonneg s₀.property.1 (by positivity)) zero_le_one, min_le_right _ _⟩⟩
  have hs₀_s₁ : s₀ < s₁ :=
    lt_min (lt_add_of_pos_right (s₀ : ℝ) (half_pos hδ)) (Subtype.coe_lt_coe.mpr hs₀_lt)
  have hx₁_pos : 0 < (γ s₁ : ℝ × ℝ).1 := by
    rcases fst_eq_zero_or_pos_and_snd_eq_sin_inv (hγ s₁) with h0 | ⟨hpos, -⟩
    · exact absurd (le_csSup (OrderTop.bddAbove _) h0) hs₀_s₁.not_ge
    · exact hpos
  have hit (y : ℝ) (hy : y ∈ Icc (-1) 1) : |y - (γ s₀ : ℝ × ℝ).2| < 1 := by
    obtain ⟨t, ht_mem, hy_eq⟩ :=
      exists_mem_Icc_snd_eq_of_path_in_oscillationOpen γ hγ hs₀_s₁ hs₀_zero hx₁_pos hy
    have ht_dist : dist t s₀ < δ := by
      rw [Subtype.dist_eq, Real.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr (Subtype.coe_le_coe.mpr ht_mem.1))]
      have hle1 : (t : ℝ) ≤ (s₁ : ℝ) := Subtype.coe_le_coe.mpr ht_mem.2
      have hle2 : (s₁ : ℝ) ≤ (s₀ : ℝ) + δ / 2 := min_le_left _ _
      linarith
    simpa [Real.dist_eq, hy_eq] using hdist ht_dist
  linarith [(abs_lt.mp (hit 1 ⟨by norm_num, le_rfl⟩)).2,
    (abs_lt.mp (hit (-1) ⟨le_rfl, by norm_num⟩)).1]

/-- If `k : ℕ → K` maps into `warsawCircleSineCurve` with `x`-coordinates tending to `0`, any
cluster point `k₀` of `k` maps into `oscillationOpen` with `x`-coordinate `0`. -/
private theorem clusterPt_fst_eq_zero_and_mem_oscillationOpen {K : Type*} [TopologicalSpace K]
    (f : C(K, WarsawCircle)) {k : ℕ → K}
    (hfk_sine : ∀ n, (f (k n) : ℝ × ℝ) ∈ warsawCircleSineCurve)
    (hlim_x : Tendsto (fun n ↦ (f (k n) : ℝ × ℝ).1) atTop (𝓝 0))
    {k₀ : K} (hk₀ : ClusterPt k₀ (Filter.map k atTop)) :
    (f k₀ : ℝ × ℝ).1 = 0 ∧ f k₀ ∈ oscillationOpen := by
  let φ : K → ℝ × ℝ := fun x ↦ (f x : ℝ × ℝ)
  have hφ : Continuous φ := continuous_subtypeVal.comp f.continuous
  have hφ_cl : MapClusterPt (φ k₀) atTop (φ ∘ k) :=
    MapClusterPt.continuousAt_comp hφ.continuousAt hk₀
  have hk₀_x : (f k₀ : ℝ × ℝ).1 = 0 :=
    eq_of_nhds_neBot
      ((hφ_cl.continuousAt_comp continuous_fst.continuousAt).clusterPt.mono hlim_x).neBot
  have hk₀_sine : (f k₀ : ℝ × ℝ) ∈ warsawCircleSineCurve :=
    isClosed_warsawCircleSineCurve.mem_of_mapClusterPt hφ_cl (Eventually.of_forall hfk_sine)
  exact ⟨hk₀_x, mem_oscillationOpen_of_mem_warsawCircleSineCurve hk₀_sine (by simp [hk₀_x])⟩

/-- For any continuous map from a compact locally path-connected space `K` to `WarsawCircle`, the
preimage parameters under `ofHalfLine` are bounded above. -/
private theorem exists_upper_bound_of_compactSpace {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [LocallyPathConnectedSpace K] (f : C(K, WarsawCircle)) :
    ∃ M : ℝ,
      ∀ k : K, ((Equiv.ofBijective ofHalfLine ofHalfLine_bijective).symm (f k) : ℝ) ≤ M := by
  let τ := (Equiv.ofBijective ofHalfLine ofHalfLine_bijective).symm
  have hτ (k : K) : ofHalfLine (τ (f k)) = f k :=
    (Equiv.ofBijective ofHalfLine ofHalfLine_bijective).apply_symm_apply (f k)
  by_contra! hunb
  choose k hk using fun n : ℕ ↦ hunb (n + 5)
  have hfk_eq (n : ℕ) : (f (k n) : ℝ × ℝ) =
      (((τ (f (k n)) : ℝ) - 4)⁻¹, Real.sin ((τ (f (k n)) : ℝ) - 4)) := by
    conv_lhs => rw [← hτ (k n)]
    exact coe_ofHalfLine_of_five_le (by dsimp [τ]; linarith [hk n])
  have hfk_pos (n : ℕ) : 0 < (f (k n) : ℝ × ℝ).1 := by
    rw [hfk_eq n]; exact inv_pos.mpr (by dsimp [τ]; linarith [hk n])
  have hfk_sine (n : ℕ) : (f (k n) : ℝ × ℝ) ∈ warsawCircleSineCurve := by
    rw [← hτ (k n)]
    exact Or.inr (coe_ofHalfLine_mem_warsawCircleSineGraph_of_five_le
      (by dsimp [τ]; linarith [hk n]))
  have hlim_x : Tendsto (fun n ↦ (f (k n) : ℝ × ℝ).1) atTop (𝓝 0) := by
    refine squeeze_zero (fun n ↦ (hfk_pos n).le) (fun n : ℕ ↦ ?_)
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))
    rw [hfk_eq n]
    have hn_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    exact inv_anti₀ hn_pos (by dsimp [τ]; push_cast; linarith [hk n])
  obtain ⟨k₀, hk₀⟩ := exists_clusterPt_of_compactSpace (Filter.map k atTop)
  obtain ⟨hk₀_x, hk₀_osc⟩ :=
    clusterPt_fst_eq_zero_and_mem_oscillationOpen f hfk_sine hlim_x hk₀
  obtain ⟨U, ⟨hU_nhds, hU_conn⟩, hU_sub⟩ :=
    (path_connected_basis k₀).mem_iff.mp ((isOpen_oscillationOpen.preimage f.continuous).mem_nhds
      hk₀_osc)
  have hfreq := clusterPt_iff_frequently.mp hk₀ U hU_nhds
  rw [frequently_map] at hfreq
  obtain ⟨n, hnU⟩ := hfreq.exists
  obtain ⟨γ, hγ⟩ := hU_conn.joinedIn k₀ (mem_of_mem_nhds hU_nhds) (k n) hnU
  exact not_joinedIn_oscillationOpen hk₀_x (hfk_pos n)
    ⟨γ.map f.continuous, fun s ↦ hU_sub (hγ s)⟩

/-- **Lifting theorem for the Warsaw circle.** Every continuous map from a compact, locally
path-connected space `K` to `WarsawCircle` lifts uniquely along `ofHalfLine` to a continuous map
`C(K, Ici (0 : ℝ))`. -/
theorem existsUnique_lift_ofHalfLine {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [LocallyPathConnectedSpace K] (f : C(K, WarsawCircle)) :
    ∃! g : C(K, Ici (0 : ℝ)), ofHalfLine.comp g = f := by
  refine existsUnique_of_exists_of_unique ?_ fun _ _ h₁ h₂ ↦
    ofHalfLine_comp_injective (h₁.trans h₂.symm)
  obtain ⟨M, hM⟩ := exists_upper_bound_of_compactSpace f
  let τ := (Equiv.ofBijective ofHalfLine ofHalfLine_bijective).symm
  let g₀ : K → Icc (0 : ℝ) M := fun k ↦ ⟨(τ (f k)).val, (τ (f k)).property, hM k⟩
  have hcomp : (fun t : Icc (0 : ℝ) M ↦ ofHalfLine ⟨t.val, t.property.1⟩) ∘ g₀ = f :=
    funext fun k ↦ (Equiv.ofBijective ofHalfLine ofHalfLine_bijective).apply_symm_apply (f k)
  have hg₀ : Continuous g₀ :=
    (isClosedEmbedding_ofHalfLine_Icc M).isEmbedding.continuous_iff.mpr (hcomp ▸ f.continuous)
  exact ⟨⟨fun k ↦ ⟨(g₀ k).val, (g₀ k).property.1⟩, (continuous_subtypeVal.comp hg₀).subtype_mk _⟩,
    ContinuousMap.ext fun k ↦ congrFun hcomp k⟩

/-- **The continuous lift of a map from a compact locally path-connected space to `[0, ∞)`.** -/
def liftOfHalfLine {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [LocallyPathConnectedSpace K] (f : C(K, WarsawCircle)) : C(K, Ici (0 : ℝ)) :=
  (existsUnique_lift_ofHalfLine f).choose

/-- `WarsawCircle.liftOfHalfLine f` lifts `f` along `ofHalfLine`. -/
@[simp]
theorem ofHalfLine_comp_liftOfHalfLine {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [LocallyPathConnectedSpace K] (f : C(K, WarsawCircle)) :
    ofHalfLine.comp (liftOfHalfLine f) = f :=
  (existsUnique_lift_ofHalfLine f).choose_spec.1

/-- Pointwise evaluation of `ofHalfLine` on `liftOfHalfLine f`. -/
@[simp]
theorem ofHalfLine_liftOfHalfLine_apply {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [LocallyPathConnectedSpace K] (f : C(K, WarsawCircle)) (k : K) :
    ofHalfLine (liftOfHalfLine f k) = f k :=
  DFunLike.congr_fun (ofHalfLine_comp_liftOfHalfLine f) k

/-- Uniqueness of `liftOfHalfLine`: any continuous lift of `f` along `ofHalfLine` equals
`liftOfHalfLine f`. -/
theorem eq_liftOfHalfLine {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [LocallyPathConnectedSpace K] {f : C(K, WarsawCircle)} {g : C(K, Ici (0 : ℝ))}
    (hg : ofHalfLine.comp g = f) : g = liftOfHalfLine f :=
  (existsUnique_lift_ofHalfLine f).choose_spec.2 g hg

/-- Lifting `ofHalfLine.comp g` recovers `g`. -/
@[simp]
theorem liftOfHalfLine_ofHalfLine_comp {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [LocallyPathConnectedSpace K] (g : C(K, Ici (0 : ℝ))) :
    liftOfHalfLine (ofHalfLine.comp g) = g :=
  (eq_liftOfHalfLine rfl).symm

/-- **The Warsaw circle is not locally path-connected.** Otherwise the identity map of the compact
Warsaw circle would lift to a continuous surjection onto `[0, ∞)`, making `[0, ∞)` compact. -/
theorem not_locallyPathConnectedSpace : ¬ LocallyPathConnectedSpace WarsawCircle := by
  intro hloc
  let g := liftOfHalfLine (ContinuousMap.id WarsawCircle)
  have hsurj : Surjective g := by
    intro t
    refine ⟨ofHalfLine t, ofHalfLine_injective ?_⟩
    simp [g]
  have hcomp : IsCompact (univ : Set (Ici (0 : ℝ))) := by
    rw [← hsurj.range_eq]
    exact isCompact_range g.continuous
  exact not_bddAbove_Ici (0 : ℝ)
    (Subtype.coe_image_univ (Ici (0 : ℝ)) ▸ hcomp.image continuous_subtypeVal).bddAbove

end WarsawCircle

end TauCeti
