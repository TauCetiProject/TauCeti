/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Analysis.Calculus.ContDiff.IntervalExtension
import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Smooth curves joining points of a manifold

A connected `C^n` manifold is `C^n`-path connected: any two of its points are joined by a `C^n`
curve `γ : ℝ → M` which is constant on `(-∞, 0]` and on `[1, ∞)`
(`TauCeti.exists_contMDiff_curve`). This holds over every model with corners, so manifolds with
boundary or corners are included. Points close to `x` are joined to `x` by such curves staying in
any prescribed neighbourhood of `x` (`TauCeti.eventually_exists_contMDiff_curve`): in the chart
at `x`, follow the segment to the chart point of `y`, reparametrized by `Real.smoothTransition`.
Mathlib's `range I` is convex, so the segment stays in the model range.

Curves which are constant near their endpoints can be concatenated smoothly
(`TauCeti.curveConcat`, `ContMDiff.curveConcat`). The concatenation runs through `γ₁` on
`[0, 1/3]` and through `γ₂` on `[2/3, 1]`, and rests at the junction point in between, so that it
is locally a reparametrization of one of the two curves.

In a boundaryless `C^k` manifold (`k : ℕ`), a `C^k` curve on a closed real interval `[a, b]`
extends across both endpoints to a curve that is two-sided `C^k` at every point of `[a, b]`
(`ContMDiffOn.exists_contMDiffAt_Icc`).

These curves are the test curves of line integrals: a closed `1`-form whose integral along every
smooth loop vanishes is exact, with primitive the integral along smooth curves from a base point.

## Main declarations

* `TauCeti.curveConcat`: the concatenation of two curves `ℝ → X`.
* `ContMDiff.curveConcat`: the concatenation of two `C^n` curves constant near the
  junction point is `C^n`.
* `TauCeti.eventually_exists_contMDiff_curve`: nearby points are joined by short `C^n` curves.
* `TauCeti.exists_contMDiff_curve`: a preconnected `C^n` manifold is `C^n`-path connected.
* `ContMDiffOn.exists_contMDiffAt_Icc`: two-sided `C^k` extension of a closed-interval curve
  across its endpoints in a boundaryless manifold.
-/

public section

noncomputable section

open Set Filter Metric
open scoped Manifold Topology

namespace TauCeti

/-! ### Concatenation of curves -/

section Concat

variable {X : Type*}

/-- The concatenation of two curves `γ₁ γ₂ : ℝ → X`: it is `γ₁ (3 * t)` for `t ≤ 1/2` and
`γ₂ (3 * t - 2)` for `t > 1/2`. On `[0, 1]` it runs through `γ₁` on `[0, 1]` and then through `γ₂`
on `[0, 1]`. When `γ₁` is constant on `[1, ∞)` and `γ₂` on `(-∞, 0]` with the same value, it rests
at that point on `[1/3, 2/3]`, so near every parameter it agrees with a reparametrization of `γ₁`
or of `γ₂` (`TauCeti.eqOn_curveConcat_left`, `TauCeti.eqOn_curveConcat_right`). -/
def curveConcat (γ₁ γ₂ : ℝ → X) (t : ℝ) : X :=
  if t ≤ 1 / 2 then γ₁ (3 * t) else γ₂ (3 * t - 2)

variable {γ₁ γ₂ : ℝ → X} {t : ℝ}

@[simp]
theorem curveConcat_of_le (ht : t ≤ 2⁻¹) : curveConcat γ₁ γ₂ t = γ₁ (3 * t) := by
  simp only [curveConcat, one_div, ht, ↓reduceIte]

@[simp]
theorem curveConcat_of_lt (ht : 2⁻¹ < t) : curveConcat γ₁ γ₂ t = γ₂ (3 * t - 2) := by
  simp only [curveConcat, one_div, ht.not_ge, ↓reduceIte]

variable {y : X}

/-- If `γ₁` rests at `y` from time `1` on and `γ₂` rests at `y` up to time `0`, then the
concatenation agrees with `γ₁` at triple speed before time `2/3`. -/
theorem eqOn_curveConcat_left (h₁ : ∀ t, 1 ≤ t → γ₁ t = y) (h₂ : ∀ t ≤ 0, γ₂ t = y) :
    EqOn (curveConcat γ₁ γ₂) (fun t ↦ γ₁ (3 * t)) (Iio (2 / 3)) := by
  intro t ht
  rcases le_or_gt t 2⁻¹ with h | h
  · exact curveConcat_of_le h
  · rw [curveConcat_of_lt h]
    exact (h₂ _ (by linarith [mem_Iio.mp ht])).trans (h₁ _ (by linarith)).symm

/-- If `γ₁` rests at `y` from time `1` on and `γ₂` rests at `y` up to time `0`, then the
concatenation agrees with `γ₂` at triple speed, shifted, after time `1/3`. -/
theorem eqOn_curveConcat_right (h₁ : ∀ t, 1 ≤ t → γ₁ t = y) (h₂ : ∀ t ≤ 0, γ₂ t = y) :
    EqOn (curveConcat γ₁ γ₂) (fun t ↦ γ₂ (3 * t - 2)) (Ioi (1 / 3)) := by
  intro t ht
  rcases le_or_gt t 2⁻¹ with h | h
  · rw [curveConcat_of_le h]
    exact (h₁ _ (by linarith [mem_Ioi.mp ht])).trans (h₂ _ (by linarith)).symm
  · exact curveConcat_of_lt h

/-- If `γ₁` rests at `y` from time `1` on and `γ₂` rests at `y` up to time `0`, then the
concatenation rests at `y` between times `1/3` and `2/3`. -/
theorem curveConcat_eq_of_mem_Icc (h₁ : ∀ t, 1 ≤ t → γ₁ t = y) (h₂ : ∀ t ≤ 0, γ₂ t = y)
    (ht : t ∈ Icc (1 / 3) (2 / 3)) : curveConcat γ₁ γ₂ t = y := by
  rcases le_or_gt t 2⁻¹ with h | h
  · rw [curveConcat_of_le h, h₁ _ (by linarith [ht.1])]
  · rw [curveConcat_of_lt h, h₂ _ (by linarith [ht.2])]

end Concat

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The concatenation of two `C^n` curves, the first resting at `y` from time `1` on and the
second resting at `y` up to time `0`, is `C^n`. -/
theorem _root_.ContMDiff.curveConcat {n : WithTop ℕ∞} {γ₁ γ₂ : ℝ → M} {y : M}
    (hγ₁ : ContMDiff 𝓘(ℝ, ℝ) I n γ₁) (hγ₂ : ContMDiff 𝓘(ℝ, ℝ) I n γ₂)
    (h₁ : ∀ t, 1 ≤ t → γ₁ t = y) (h₂ : ∀ t ≤ 0, γ₂ t = y) :
    ContMDiff 𝓘(ℝ, ℝ) I n (TauCeti.curveConcat γ₁ γ₂) := by
  have hs₁ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n fun s : ℝ ↦ 3 * s :=
    (by fun_prop : ContDiff ℝ n fun s : ℝ ↦ 3 * s).contMDiff
  have hs₂ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n fun s : ℝ ↦ 3 * s - 2 :=
    (by fun_prop : ContDiff ℝ n fun s : ℝ ↦ 3 * s - 2).contMDiff
  have heq : TauCeti.curveConcat γ₁ γ₂ =
      (Iic (1 / 2)).piecewise (fun t ↦ γ₁ (3 * t)) fun t ↦ γ₂ (3 * t - 2) := by
    ext t
    simp only [TauCeti.curveConcat, Set.piecewise, mem_Iic]
  rw [heq]
  refine (hγ₁.comp hs₁).piecewise_Iic (hγ₂.comp hs₂) ?_
  filter_upwards [Ioo_mem_nhds (by norm_num : (1 / 3 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 2 / 3)] with t ht
  exact (h₁ _ (by linarith [ht.1])).trans (h₂ _ (by linarith [ht.2])).symm

/-! ### Smooth path connectivity -/

variable {n : ℕ∞}

/-- Points close to `x` are joined to `x` by `C^n` curves staying in a prescribed neighbourhood
`U` of `x`, which are constant on `(-∞, 0]` and on `[1, ∞)`. -/
theorem eventually_exists_contMDiff_curve [IsManifold I n M] {x : M} {U : Set M} (hU : U ∈ 𝓝 x) :
    ∀ᶠ y in 𝓝 x, ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I n γ ∧ (∀ t ≤ 0, γ t = x) ∧
      (∀ t, 1 ≤ t → γ t = y) ∧ ∀ t, γ t ∈ U := by
  obtain ⟨ε, hε, hsub⟩ := exists_ball_inter_range_subset_extChartAt (I := I) hU
  obtain ⟨hconv, -, hx⟩ := convex_uniqueDiffOn_ball_inter_range_extChartAt (I := I) x hε
  filter_upwards [extChartAt_source_mem_nhds (I := I) x,
    (continuousAt_extChartAt (I := I) x).preimage_mem_nhds (ball_mem_nhds _ hε)]
    with y hys hyb
  -- In the chart at `x`, follow the segment from the chart point of `x` to that of `y`.
  set c : ℝ → E := fun t ↦ extChartAt I x x +
    Real.smoothTransition t • (extChartAt I x y - extChartAt I x x) with hc_def
  have hmem (t : ℝ) : c t ∈ ball (extChartAt I x x) ε ∩ range I :=
    hconv.add_smul_sub_mem hx
      ⟨hyb, extChartAt_target_subset_range x ((extChartAt I x).map_source hys)⟩
      ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) n c :=
    (contDiff_const.add (Real.smoothTransition.contDiff.smul contDiff_const)).contMDiff
  refine ⟨(extChartAt I x).symm ∘ c,
    (contMDiffOn_extChartAt_symm x).comp_contMDiff hc fun t ↦ (hsub (hmem t)).1,
    fun t ht ↦ ?_, fun t ht ↦ ?_, fun t ↦ (hsub (hmem t)).2⟩
  · simp [hc_def, Real.smoothTransition.zero_of_nonpos ht]
  · have hys' : y ∈ (chartAt H x).source := by rwa [← extChartAt_source (I := I)]
    simp [hc_def, Real.smoothTransition.one_of_one_le ht, (chartAt H x).left_inv hys']

/-- **Smooth path connectivity.** In a preconnected `C^n` manifold, any two points are joined by a
`C^n` curve `γ : ℝ → M` which is constant on `(-∞, 0]` and on `[1, ∞)`. -/
theorem exists_contMDiff_curve [IsManifold I n M] [PreconnectedSpace M] (x y : M) :
    ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I n γ ∧ (∀ t ≤ 0, γ t = x) ∧ ∀ t, 1 ≤ t → γ t = y := by
  refine PreconnectedSpace.induction₂'
    (fun x y ↦ ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I n γ ∧ (∀ t ≤ 0, γ t = x) ∧
      ∀ t, 1 ≤ t → γ t = y) (fun x ↦ ?_) ⟨fun x y z ⟨γ₁, hγ₁, h₁, h₁'⟩ ⟨γ₂, hγ₂, h₂, h₂'⟩ ↦ ?_⟩ x y
  · filter_upwards [eventually_exists_contMDiff_curve (I := I) (n := n) (x := x) univ_mem]
      with y hy
    obtain ⟨γ, hγ, h₀, h₁, -⟩ := hy
    have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n fun s : ℝ ↦ 1 - s :=
      (by fun_prop : ContDiff ℝ n fun s : ℝ ↦ 1 - s).contMDiff
    exact ⟨⟨γ, hγ, h₀, h₁⟩, γ ∘ fun s ↦ 1 - s, hγ.comp hs,
      fun t ht ↦ h₁ _ (by linarith), fun t ht ↦ h₀ _ (by linarith)⟩
  · refine ⟨curveConcat γ₁ γ₂, ContMDiff.curveConcat hγ₁ hγ₂ h₁' h₂, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
    · rw [curveConcat_of_le (by linarith), h₁ _ (by linarith)]
    · rw [curveConcat_of_lt (by linarith), h₂' _ (by linarith)]

/-! ### Extending a closed-interval curve across its endpoints -/

/-- Extend a `C^k` curve on `[a, b]` (`a < b`) in a boundaryless manifold across the left endpoint
`a`, keeping `C^k` regularity on `[a, b]` and achieving two-sided `ContMDiffAt` at `a`. -/
private theorem exists_contMDiffAt_left_Icc [I.Boundaryless] {k : ℕ} [IsManifold I k M]
    {γ : ℝ → M} {a b : ℝ} (hab : a < b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I k γ (Icc a b)) :
    ∃ δ : ℝ → M, ContMDiffAt 𝓘(ℝ, ℝ) I k δ a ∧ ContMDiffOn 𝓘(ℝ, ℝ) I k δ (Icc a b) ∧
      EqOn δ γ (Icc a b) := by
  let e := extChartAt I (γ a)
  have hpre : γ ⁻¹' e.source ∈ 𝓝[Icc a b] a :=
    hγ.continuousOn.continuousWithinAt ⟨le_rfl, hab.le⟩ (extChartAt_source_mem_nhds (I := I) (γ a))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  set c := min b (a + r / 2)
  have hac : a < c := lt_min hab (by linarith)
  have hcb : c ≤ b := min_le_left _ _
  have hsub : MapsTo γ (Icc a c) e.source := fun t ht ↦ hball ⟨by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 ht.1)]
    linarith [ht.2, min_le_right b (a + r / 2)], ht.1, ht.2.trans hcb⟩
  have hchart : ContDiffOn ℝ k (e ∘ γ) (Icc a c) :=
    contMDiffOn_iff_contDiffOn.1 <|
      (contMDiffOn_extChartAt (I := I) (x := γ a)).comp (hγ.mono (Icc_subset_Icc_right hcb))
        (fun t ht ↦ by simpa only [e, extChartAt_source, mem_preimage] using hsub ht)
  obtain ⟨g, hg, hgeq⟩ := TauCeti.exists_contDiff_extension_Icc (e ∘ γ) hchart
  have hga : g a = e (γ a) := hgeq ⟨le_rfl, hac.le⟩
  have hgtgt : g ⁻¹' e.target ∈ 𝓝 a := hg.continuous.continuousAt.preimage_mem_nhds <|
    hga ▸ (isOpen_extChartAt_target (I := I) (γ a)).mem_nhds (mem_extChartAt_target (I := I) (γ a))
  obtain ⟨ε, hε, -⟩ := Metric.mem_nhds_iff.1 hgtgt
  let δ : ℝ → M := fun t ↦ if t ≤ a then e.symm (g t) else γ t
  have hEqOn : EqOn δ γ (Icc a b) := fun t ht ↦ by
    by_cases hta : t ≤ a
    · simp only [δ, le_antisymm hta ht.1, le_refl, ↓reduceIte, hga,
        e.left_inv (mem_extChartAt_source (I := I) _)]
    · simp only [δ, hta, ↓reduceIte]
  have hnear : δ =ᶠ[𝓝 a] e.symm ∘ g := by
    refine eventuallyEq_of_mem
      (Ioo_mem_nhds (sub_lt_self a hε) (lt_min hac (lt_add_of_pos_right a hε))) fun t ht ↦ ?_
    by_cases hta : t ≤ a
    · simp only [δ, hta, ↓reduceIte, Function.comp_apply]
    · have htc : t ∈ Icc a c := ⟨le_of_not_ge hta, ht.2.le.trans (min_le_left _ _)⟩
      simp only [δ, hta, ↓reduceIte, Function.comp_apply, hgeq htc, e.left_inv (hsub htc)]
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I k e.symm (g a) :=
    (contMDiffOn_extChartAt_symm (I := I) (x := γ a)).contMDiffAt
      ((isOpen_extChartAt_target (I := I) (γ a)).mem_nhds
        (hga ▸ mem_extChartAt_target (I := I) (γ a)))
  exact ⟨δ, (hsymm.comp a hg.contMDiff.contMDiffAt).congr_of_eventuallyEq hnear, hγ.congr hEqOn,
    hEqOn⟩

/-- A `C^k` curve (`k : ℕ`) on a closed interval `[a, b]` in a boundaryless `C^k` manifold agrees on
`[a, b]` with a curve that is two-sided `C^k` at every point of `[a, b]`. -/
theorem _root_.ContMDiffOn.exists_contMDiffAt_Icc [I.Boundaryless] {k : ℕ} [IsManifold I k M]
    {γ : ℝ → M} {a b : ℝ} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I k γ (Icc a b)) :
    ∃ δ : ℝ → M, (∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ) I k δ t) ∧ EqOn δ γ (Icc a b) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · obtain ⟨δ₁, hδ₁a, hδ₁, hEq₁⟩ := exists_contMDiffAt_left_Icc hab hγ
    have hrev : ContMDiffOn 𝓘(ℝ, ℝ) I k (fun t ↦ δ₁ (-t)) (Icc (-b) (-a)) :=
      hδ₁.comp contDiff_neg.contMDiff.contMDiffOn fun t ht ↦
        ⟨by linarith [ht.2], by linarith [ht.1]⟩
    obtain ⟨δ₂, hδ₂b, -, hEq₂⟩ := exists_contMDiffAt_left_Icc (neg_lt_neg hab) hrev
    let m := (a + b) / 2
    let δ : ℝ → M := fun t ↦ if t < m then δ₁ t else δ₂ (-t)
    have hEq : EqOn δ γ (Icc a b) := fun t ht ↦ by
      by_cases htm : t < m
      · simpa only [δ, htm, ↓reduceIte] using hEq₁ ht
      · have h2 := hEq₂ (x := -t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
        simp only [neg_neg] at h2; simpa only [δ, htm, ↓reduceIte] using h2.trans (hEq₁ ht)
    refine ⟨δ, fun t ht ↦ ?_, hEq⟩
    rcases eq_or_lt_of_le ht.1 with rfl | hat
    · have ham : a < m := by dsimp only [m]; linarith
      exact hδ₁a.congr_of_eventuallyEq <| eventuallyEq_of_mem (Iio_mem_nhds ham)
        fun s hs ↦ by simp only [δ, mem_Iio.1 hs, ↓reduceIte]
    · rcases eq_or_lt_of_le ht.2 with rfl | htb
      · have hmt : m < t := by dsimp only [m]; linarith
        exact (hδ₂b.comp t contDiff_neg.contMDiff.contMDiffAt).congr_of_eventuallyEq <|
          eventuallyEq_of_mem (Ioi_mem_nhds hmt) fun s hs ↦ by
            simp only [δ, not_lt.2 (mem_Ioi.1 hs).le, ↓reduceIte, Function.comp_apply]
      · exact (hγ.contMDiffAt (Icc_mem_nhds hat htb)).congr_of_eventuallyEq
          (eventuallyEq_of_mem (Icc_mem_nhds hat htb) hEq)
  · exact ⟨fun _ ↦ γ a, fun _ _ ↦ contMDiffAt_const, fun t ht ↦ by rw [le_antisymm ht.2 ht.1]⟩
  · exact ⟨γ, fun _ ht ↦ absurd (ht.1.trans ht.2) (not_le.2 hba), fun _ _ ↦ rfl⟩

end TauCeti
