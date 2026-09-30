/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow

/-!
# Fréchet radii and barycenters

The `p`-Fréchet radius of a point `x` with respect to a measure `μ` is the `Lᵖ(μ)` seminorm
of its distance from a random point:

`R_p(x) = ‖d(x, ·)‖_{Lᵖ(μ)}`.

This file defines the radius and its power functional at the measurable pseudometric level. A
Fréchet barycenter is required to have finite radius and to minimize it globally; the finiteness
clause prevents an identically infinite functional from making every point a barycenter. For a
finite positive exponent, minimizing the radius is equivalent to minimizing its `p`-th power.

On a proper metric space, a probability law whose radius is finite somewhere has a nonempty
compact set of Fréchet barycenters. The proof uses the reverse triangle inequality for radii:
the sublevel through one finite-radius point is closed and bounded, hence compact, and contains
every global minimizer.

At exponent `∞`, `TauCeti.chebyshevRadius` exposes the same functional as an essential supremum
and `TauCeti.IsChebyshevCenter` gives its finite minimizers.

## References

* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43
  (2011), 904--924.
* T. Le Gouic and J.-M. Loubes, *Existence and consistency of Wasserstein barycenters*,
  Probab. Theory Relat. Fields 168 (2017), 901--917.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

universe u

variable {X : Type u} [PseudoEMetricSpace X] [MeasurableSpace X]

/-- The `p`-Fréchet radius of `x` with respect to `μ`: the `Lᵖ(μ)` seminorm of
`y ↦ edist x y`. It is extended-valued, so it is defined without a moment assumption. -/
def frechetRadius (p : ℝ≥0∞) (μ : Measure X) (x : X) : ℝ≥0∞ :=
  eLpNorm (fun y ↦ edist x y) p μ

/-- The power functional associated to the `p`-Fréchet radius. For finite positive `p`, it is
the `p`-th power of `TauCeti.frechetRadius`; see `TauCeti.frechetRadius_rpow_eq_frechetPower`. -/
def frechetPower (p : ℝ≥0∞) (μ : Measure X) (x : X) : ℝ≥0∞ :=
  ∫⁻ y, edist x y ^ p.toReal ∂μ

/-- For a finite positive exponent, the `p`-th power of the Fréchet radius is the Fréchet
power functional. -/
theorem frechetRadius_rpow_eq_frechetPower {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp_top : p ≠ ⊤)
    {x : X} {μ : Measure X} (hx : AEMeasurable (fun y ↦ edist x y) μ) :
    frechetRadius p μ x ^ p.toReal = frechetPower p μ x := by
  exact eLpNorm_rpow_eq_lintegral hp₀ hp_top hx

/-- A raw minimizer of the extended-valued Fréchet radius. If the radius is identically infinite,
every point satisfies this predicate; use `TauCeti.IsFrechetBarycenter` when finiteness matters. -/
def IsFrechetMinimizer (p : ℝ≥0∞) (μ : Measure X) (x : X) : Prop :=
  ∀ y, frechetRadius p μ x ≤ frechetRadius p μ y

/-- The defining characterization of a raw minimizer of the Fréchet radius. -/
theorem isFrechetMinimizer_iff {p : ℝ≥0∞} {μ : Measure X} {x : X} :
    IsFrechetMinimizer p μ x ↔ ∀ y, frechetRadius p μ x ≤ frechetRadius p μ y :=
  Iff.rfl

/-- A Fréchet barycenter is a finite raw minimizer of the Fréchet radius. The finiteness clause
prevents an identically infinite radius from making every point a barycenter. -/
def IsFrechetBarycenter (p : ℝ≥0∞) (μ : Measure X) (x : X) : Prop :=
  frechetRadius p μ x ≠ ⊤ ∧ IsFrechetMinimizer p μ x

/-- The defining characterization of a Fréchet barycenter. -/
theorem isFrechetBarycenter_iff {p : ℝ≥0∞} {μ : Measure X} {x : X} :
    IsFrechetBarycenter p μ x ↔
      frechetRadius p μ x ≠ ⊤ ∧ IsFrechetMinimizer p μ x :=
  Iff.rfl

/-- The set of finite Fréchet barycenters of a measure. -/
def frechetBarycenters (p : ℝ≥0∞) (μ : Measure X) : Set X :=
  {x | IsFrechetBarycenter p μ x}

/-- Membership in the set of Fréchet barycenters. -/
@[simp]
theorem mem_frechetBarycenters {p : ℝ≥0∞} {μ : Measure X} {x : X} :
    x ∈ frechetBarycenters p μ ↔ IsFrechetBarycenter p μ x :=
  Iff.rfl

/-- At a finite positive exponent, a finite-radius point is a Fréchet barycenter exactly when it
minimizes the power functional. -/
theorem isFrechetBarycenter_iff_forall_frechetPower_le {p : ℝ≥0∞} (hp₀ : p ≠ 0)
    (hp_top : p ≠ ⊤) {μ : Measure X} {x : X}
    (hxm : AEMeasurable (fun y ↦ edist x y) μ)
    (hm : ∀ z, AEMeasurable (fun y ↦ edist z y) μ) :
    IsFrechetBarycenter p μ x ↔
      frechetRadius p μ x ≠ ⊤ ∧ ∀ z, frechetPower p μ x ≤ frechetPower p μ z := by
  rw [isFrechetBarycenter_iff]
  rw [isFrechetMinimizer_iff]
  refine and_congr_right fun _ ↦ forall_congr' fun z ↦ ?_
  rw [← ENNReal.rpow_le_rpow_iff (ENNReal.toReal_pos hp₀ hp_top),
    frechetRadius_rpow_eq_frechetPower hp₀ hp_top hxm,
    frechetRadius_rpow_eq_frechetPower hp₀ hp_top (hm z)]

/-! ### The essential-supremum endpoint -/

/-- The finite Chebyshev radius of `x` relative to `μ`, before minimizing in `x`: the essential
supremum of the distance from `x`. -/
def chebyshevRadius (μ : Measure X) (x : X) : ℝ≥0∞ :=
  eLpNormEssSup (fun y ↦ edist x y) μ

/-- At exponent `∞`, the Fréchet radius is the essential-supremum Chebyshev radius. -/
theorem frechetRadius_top {x : X} {μ : Measure X}
    (hx : AEStronglyMeasurable (fun y ↦ edist x y) μ) :
    frechetRadius ⊤ μ x = chebyshevRadius μ x := by
  rw [frechetRadius, chebyshevRadius, eLpNorm_exponent_top hx]

/-- A finite Chebyshev center minimizes the essential-supremum radius. -/
def IsChebyshevCenter (μ : Measure X) (x : X) : Prop :=
  chebyshevRadius μ x ≠ ⊤ ∧ ∀ y, chebyshevRadius μ x ≤ chebyshevRadius μ y

/-- The defining characterization of a finite Chebyshev center. -/
theorem isChebyshevCenter_iff {μ : Measure X} {x : X} :
    IsChebyshevCenter μ x ↔
      chebyshevRadius μ x ≠ ⊤ ∧ ∀ y, chebyshevRadius μ x ≤ chebyshevRadius μ y :=
  Iff.rfl

/-- The Fréchet and Chebyshev center predicates agree at exponent `∞`. -/
theorem isFrechetBarycenter_top_iff_isChebyshevCenter {μ : Measure X} {x : X}
    (hm : ∀ z, AEStronglyMeasurable (fun y ↦ edist z y) μ) :
    IsFrechetBarycenter ⊤ μ x ↔ IsChebyshevCenter μ x := by
  simp only [isFrechetBarycenter_iff, isFrechetMinimizer_iff, isChebyshevCenter_iff,
    frechetRadius_top (hm _)]

/-! ### Metric estimates and existence on proper spaces -/

section Proper

variable {Y : Type u} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {p : ℝ≥0∞} (hp : 1 ≤ p)
  (μ : Measure Y) [IsProbabilityMeasure μ]

include hp

/-- Moving the center changes the Fréchet radius by at most the distance moved, in one
direction. -/
theorem frechetRadius_le_add [SecondCountableTopology Y] (x₀ x₁ : Y) :
    frechetRadius p μ x₁ ≤ edist x₁ x₀ + frechetRadius p μ x₀ := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hconst : eLpNorm (fun _ : Y ↦ edist x₁ x₀) p μ = edist x₁ x₀ := by
    rw [eLpNorm_const _ hp₀ (IsProbabilityMeasure.ne_zero μ)]
    simp
  have hmeas : AEStronglyMeasurable (fun y ↦ edist x₁ y) μ :=
    (measurable_edist.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  rw [frechetRadius, frechetRadius, ← hconst]
  calc
    eLpNorm (fun y ↦ edist x₁ y) p μ ≤
        eLpNorm ((fun _ : Y ↦ edist x₁ x₀) + fun y ↦ edist x₀ y) p μ :=
      eLpNorm_mono_enorm hmeas fun y ↦ by simpa using edist_triangle x₁ x₀ y
    _ ≤ eLpNorm (fun _ : Y ↦ edist x₁ x₀) p μ +
        eLpNorm (fun y ↦ edist x₀ y) p μ :=
      eLpNorm_add_le hp

omit [BorelSpace Y] in
/-- The distance between two centers is bounded by the sum of their Fréchet radii. -/
theorem edist_le_frechetRadius_add (x₀ x₁ : Y) :
    edist x₀ x₁ ≤ frechetRadius p μ x₀ + frechetRadius p μ x₁ := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hconst : eLpNorm (fun _ : Y ↦ edist x₀ x₁) p μ = edist x₀ x₁ := by
    rw [eLpNorm_const _ hp₀ (IsProbabilityMeasure.ne_zero μ)]
    simp
  have hmeas : AEStronglyMeasurable (fun _ : Y ↦ edist x₀ x₁) μ :=
    aestronglyMeasurable_const
  rw [← hconst, frechetRadius, frechetRadius]
  calc
    eLpNorm (fun _ : Y ↦ edist x₀ x₁) p μ ≤
        eLpNorm ((fun y ↦ edist x₀ y) + fun y ↦ edist y x₁) p μ :=
      eLpNorm_mono_enorm hmeas fun y ↦ by simpa using edist_triangle x₀ y x₁
    _ ≤ eLpNorm (fun y ↦ edist x₀ y) p μ +
        eLpNorm (fun y ↦ edist y x₁) p μ :=
      eLpNorm_add_le hp
    _ = eLpNorm (fun y ↦ edist x₀ y) p μ +
        eLpNorm (fun y ↦ edist x₁ y) p μ := by
      rw [show (fun y : Y ↦ edist y x₁) = fun y ↦ edist x₁ y by
        funext y
        exact edist_comm y x₁]

/-- If the Fréchet radius is finite at one point, it is finite everywhere. -/
theorem frechetRadius_ne_top_of_ne_top [SecondCountableTopology Y]
    {x₀ : Y} (h₀ : frechetRadius p μ x₀ ≠ ⊤)
    (x : Y) : frechetRadius p μ x ≠ ⊤ :=
  ne_top_of_le_ne_top ((ENNReal.add_ne_top).2 ⟨edist_ne_top _ _, h₀⟩)
    (frechetRadius_le_add hp μ x₀ x)

/-- When it is finite somewhere, the real-valued Fréchet radius is `1`-Lipschitz. -/
theorem lipschitzWith_one_toReal_frechetRadius [SecondCountableTopology Y] {x₀ : Y}
    (h₀ : frechetRadius p μ x₀ ≠ ⊤) :
    LipschitzWith 1 (fun x ↦ (frechetRadius p μ x).toReal) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have hx := frechetRadius_ne_top_of_ne_top hp μ h₀ x
  have hy := frechetRadius_ne_top_of_ne_top hp μ h₀ y
  have hxy := (ENNReal.toReal_le_toReal hx
    ((ENNReal.add_ne_top).2 ⟨edist_ne_top _ _, hy⟩)).2 (frechetRadius_le_add hp μ y x)
  have hyx := (ENNReal.toReal_le_toReal hy
    ((ENNReal.add_ne_top).2 ⟨edist_ne_top _ _, hx⟩)).2 (frechetRadius_le_add hp μ x y)
  rw [ENNReal.toReal_add (edist_ne_top _ _) hy, ← dist_edist] at hxy
  rw [ENNReal.toReal_add (edist_ne_top _ _) hx, ← dist_edist] at hyx
  rw [dist_comm y x] at hyx
  rw [Real.dist_eq]
  simp only [NNReal.coe_one, one_mul]
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- On a proper metric space, every sublevel of a Fréchet radius that is finite somewhere is
compact. -/
theorem isCompact_frechetRadius_sublevel [ProperSpace Y] {x₀ : Y}
    (h₀ : frechetRadius p μ x₀ ≠ ⊤) (r : ℝ) :
    IsCompact {x | (frechetRadius p μ x).toReal ≤ r} := by
  let R : Y → ℝ := fun x ↦ (frechetRadius p μ x).toReal
  have hR : LipschitzWith 1 R := lipschitzWith_one_toReal_frechetRadius hp μ h₀
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le hR.continuous continuous_const
  · refine Metric.isBounded_iff_subset_closedBall x₀ |>.2 ⟨r + R x₀, ?_⟩
    intro x hx
    have hdist := (ENNReal.toReal_le_toReal (edist_ne_top _ _)
      ((ENNReal.add_ne_top).2 ⟨frechetRadius_ne_top_of_ne_top hp μ h₀ x, h₀⟩)).2
        (edist_le_frechetRadius_add hp μ x x₀)
    rw [ENNReal.toReal_add (frechetRadius_ne_top_of_ne_top hp μ h₀ x) h₀,
      ← dist_edist] at hdist
    change R x ≤ r at hx
    change dist x x₀ ≤ r + R x₀
    change dist x x₀ ≤ (frechetRadius p μ x).toReal +
      (frechetRadius p μ x₀).toReal at hdist
    linarith

/-- On a proper metric space, a probability law with finite `p`-Fréchet radius somewhere has a
Fréchet barycenter. -/
theorem exists_isFrechetBarycenter [ProperSpace Y] {x₀ : Y}
    (h₀ : frechetRadius p μ x₀ ≠ ⊤) : ∃ x, IsFrechetBarycenter p μ x := by
  let R : Y → ℝ := fun x ↦ (frechetRadius p μ x).toReal
  let K : Set Y := {x | R x ≤ R x₀}
  have hR : LipschitzWith 1 R := lipschitzWith_one_toReal_frechetRadius hp μ h₀
  have hKcompact : IsCompact K := by
    change IsCompact {x | (frechetRadius p μ x).toReal ≤
      (frechetRadius p μ x₀).toReal}
    exact isCompact_frechetRadius_sublevel hp μ h₀ _
  have hx₀K : x₀ ∈ K := by
    change R x₀ ≤ R x₀
    exact le_rfl
  have hKnonempty : K.Nonempty := ⟨x₀, hx₀K⟩
  obtain ⟨x, hxK, hxmin⟩ := hKcompact.exists_isMinOn hKnonempty hR.continuous.continuousOn
  refine ⟨x, frechetRadius_ne_top_of_ne_top hp μ h₀ x, fun y ↦ ?_⟩
  apply (ENNReal.toReal_le_toReal
    (frechetRadius_ne_top_of_ne_top hp μ h₀ x)
    (frechetRadius_ne_top_of_ne_top hp μ h₀ y)).1
  by_cases hy : y ∈ K
  · exact hxmin hy
  · change ¬R y ≤ R x₀ at hy
    exact (hxmin hx₀K).trans (le_of_lt (not_le.1 hy))

/-- On a proper metric space, the set of `p`-Fréchet barycenters of a probability law with
finite radius somewhere is compact. -/
theorem isCompact_frechetBarycenters [ProperSpace Y] {x₀ : Y}
    (h₀ : frechetRadius p μ x₀ ≠ ⊤) : IsCompact (frechetBarycenters p μ) := by
  obtain ⟨b, hb⟩ := exists_isFrechetBarycenter hp μ h₀
  let R : Y → ℝ := fun x ↦ (frechetRadius p μ x).toReal
  have hR : LipschitzWith 1 R := lipschitzWith_one_toReal_frechetRadius hp μ h₀
  have hfinite (x : Y) : frechetRadius p μ x ≠ ⊤ :=
    frechetRadius_ne_top_of_ne_top hp μ h₀ x
  have hB : frechetBarycenters p μ = {x | R x = R b} := by
    ext x
    constructor
    · intro hx
      change IsFrechetBarycenter p μ x at hx
      exact congrArg ENNReal.toReal (le_antisymm (hx.2 b) (hb.2 x))
    · intro hx
      change R x = R b at hx
      change IsFrechetBarycenter p μ x
      refine ⟨hfinite x, fun y ↦ ?_⟩
      apply (ENNReal.toReal_le_toReal (hfinite x) (hfinite y)).1
      change R x ≤ R y
      rw [hx]
      exact (ENNReal.toReal_le_toReal (hfinite b) (hfinite y)).2 (hb.2 y)
  apply Metric.isCompact_of_isClosed_isBounded
  · rw [hB]
    exact isClosed_eq hR.continuous continuous_const
  · rw [hB]
    refine Metric.isBounded_iff_subset_closedBall b |>.2 ⟨2 * R b, ?_⟩
    intro x hx
    have hdist := (ENNReal.toReal_le_toReal (edist_ne_top _ _)
      ((ENNReal.add_ne_top).2 ⟨hfinite x, hfinite b⟩)).2
        (edist_le_frechetRadius_add hp μ x b)
    rw [ENNReal.toReal_add (hfinite x) (hfinite b), ← dist_edist] at hdist
    change R x = R b at hx
    change dist x b ≤ 2 * R b
    change dist x b ≤ (frechetRadius p μ x).toReal +
      (frechetRadius p μ b).toReal at hdist
    change (frechetRadius p μ x).toReal = (frechetRadius p μ b).toReal at hx
    linarith

end Proper

end TauCeti

end
