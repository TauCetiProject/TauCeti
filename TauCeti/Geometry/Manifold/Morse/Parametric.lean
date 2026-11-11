/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import TauCeti.Analysis.Calculus.Morse.Parametric
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Calculus.Morse.ZeroSectionChart
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# The parametric Morse lemma on a vector bundle

Let `V → B` be a `C^{n+2}` vector bundle with finite-dimensional fibres over a boundaryless
finite-dimensional manifold, and let `g` be a `C^{n+2}` function on an open set of its total space,
with `1 ≤ n ≤ ∞`, whose restriction to each fibre over an open set `U ⊆ B` has a nondegenerate
critical point at `0`. Then near the zero section over `U`, in `C^n` coordinates which preserve
the fibres and fix the zero section, `g` is its value on the zero section plus half its fibrewise
Hessian quadratic form (`TauCeti.exists_bundle_morse_normal_form`). This is the form in which the
Morse lemma applies along a critical submanifold of a Morse–Bott function: there `g` is the
function read on the normal bundle through a tubular neighbourhood.

The coordinates are built from the canonical parametric Morse coordinate
`TauCeti.parametricMorseCoord` of `TauCeti.Analysis.Calculus.Morse.Parametric`. In the chart of the
total space at a point `0_b` of the zero section, it is a partial diffeomorphism on a product
neighbourhood (`TauCeti.exists_parametricMorseCoord_partialDiffeomorph_prod_ball`). These local
coordinates glue to a single map, because any two of them agree wherever both are defined. Near the
zero section this agreement is the naturality of the canonical coordinate under the linear
coordinate changes of the bundle. Away from the zero section, the charts at two different points
`0_b` and `0_{b'}` are related by coordinate changes over which nothing is uniform, so the
coordinates are compared along the segment from `0` to a vector `v` of the fibre instead: in both
charts they are given by continuous families of square roots of the same comparison operators,
equal to the identity at `0`, and one of the two families stays in the region where
`TauCeti.sqrtNearOne` inverts squaring, so the families agree all along the segment
(`TauCeti.eqOn_morseCongruence_bilinearComp`).

The glued map is a local diffeomorphism at every point of its domain, an open neighbourhood of the
zero section over `U`. It is not shown here to be injective on a neighbourhood of the whole zero
section.

## Main declarations

* `TauCeti.exists_bundle_morse_normal_form`: the parametric Morse lemma on a vector bundle.

## References

* R. S. Palais, *The Morse lemma for Banach spaces*, Bull. Amer. Math. Soc. **75** (1969),
  968--971, for the operator square root.
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics **60** (1954), 248--261, for
  the normal form along a nondegenerate critical submanifold.
-/

public section

noncomputable section

open Bundle Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

section Congruence

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E]

/-- The canonical congruence of a family `G` at `z`, comparing its averaged vertical Hessian at
`z` with its vertical Hessian at `(z.1, 0)`; the canonical parametric Morse coordinate of `G` at
`z` is its value on `z.2`. -/
private def congruenceAt (G : P × E → ℝ) (z : P × E) : E →L[ℝ] E :=
  morseCongruence (fderiv ℝ (fderiv ℝ fun w ↦ G (z.1, w)) 0)
    (hessianAverage (fun w ↦ G (z.1, w)) 0 z.2)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem parametricMorseCoord_eq_congruenceAt (G : P × E → ℝ) (z : P × E) :
    parametricMorseCoord G z = congruenceAt G z z.2 := by
  rw [parametricMorseCoord_def, congruenceAt]

/-- The points at which the canonical congruence of `G` is continuous, is a square root of the
comparison operator of the vertical Hessian and the averaged vertical Hessian, and lies where
`TauCeti.sqrtNearOne` inverts squaring, and at which the vertical Hessian is invertible. These
are the points along whose fibre segments the canonical coordinates read in two trivializations
can be compared. -/
private def IsCongruencePoint (G : P × E → ℝ) (z : P × E) : Prop :=
  ContinuousAt (congruenceAt G) z ∧
    congruenceAt G z * congruenceAt G z = (fderiv ℝ (fderiv ℝ fun w ↦ G (z.1, w)) 0).inverse ∘L
      hessianAverage (fun w ↦ G (z.1, w)) 0 z.2 ∧
    congruenceAt G z ∈ interior {r : E →L[ℝ] E | sqrtNearOne (E →L[ℝ] E) (r * r) = r} ∧
    (fderiv ℝ (fderiv ℝ fun w ↦ G (z.1, w)) 0).IsInvertible

/-- Near a point of the zero section with invertible vertical Hessian, every point is a congruence
point. -/
private theorem eventually_isCongruencePoint {G : P × E → ℝ} (hG : ContDiff ℝ 2 G) {a : P}
    (hH : (fderiv ℝ (fderiv ℝ fun w ↦ G (a, w)) 0).IsInvertible) :
    ∀ᶠ z in 𝓝 (a, (0 : E)), IsCongruencePoint G z := by
  -- The pair of the vertical Hessian at `(z.1, 0)` and the averaged vertical Hessian at `z`.
  have hA : Continuous fun z : P × E ↦ hessianAverage (fun w ↦ G (z.1, w)) 0 z.2 :=
    (contDiff_hessianAverage_param (n := 0) (by simpa using hG) 0).continuous
  have hpair : Continuous fun z : P × E ↦ (fderiv ℝ (fderiv ℝ fun w ↦ G (z.1, w)) 0,
      hessianAverage (fun w ↦ G (z.1, w)) 0 z.2) := by
    refine Continuous.prodMk ?_ hA
    simpa only [Function.comp_def, hessianAverage_zero] using
      hA.comp (continuous_fst.prodMk continuous_const : Continuous fun z : P × E ↦ (z.1, (0 : E)))
  have hT : Tendsto (fun z : P × E ↦ (fderiv ℝ (fderiv ℝ fun w ↦ G (z.1, w)) 0,
      hessianAverage (fun w ↦ G (z.1, w)) 0 z.2)) (𝓝 (a, 0))
      (𝓝 (fderiv ℝ (fderiv ℝ fun w ↦ G (a, w)) 0, fderiv ℝ (fderiv ℝ fun w ↦ G (a, w)) 0)) := by
    simpa using hpair.tendsto (a, 0)
  have hW : interior {r : E →L[ℝ] E | sqrtNearOne (E →L[ℝ] E) (r * r) = r} ∈ 𝓝 1 :=
    interior_mem_nhds.2 eventually_sqrtNearOne_mul_self
  filter_upwards [hT.eventually (eventually_contDiffAt_morseCongruence hH (n := 0)),
    hT.eventually (eventually_morseCongruence_mul_self hH),
    ((tendsto_morseCongruence hH).comp hT).eventually hW,
    hT.fst_nhds.eventually hH.eventually_nhds] with z hz hsq hzW hinv
  exact ⟨hz.continuousAt.comp (f := fun z : P × E ↦ (fderiv ℝ (fderiv ℝ fun w ↦ G (z.1, w)) 0,
    hessianAverage (fun w ↦ G (z.1, w)) 0 z.2)) hpair.continuousAt, hsq, hzW, hinv⟩

/-- **Comparison of canonical coordinates in two charts.** Let `G₀` and `G₁` be `C²` families
whose fibres over `x₀` and `x₁` correspond on balls about `0` through a linear isomorphism `T`,
and suppose that all points of these fibre balls are congruence points. Then the canonical
coordinates correspond through `T` at every pair of corresponding points of the two balls. -/
private theorem parametricMorseCoord_eq_of_isCongruencePoint {G₀ G₁ : P × E → ℝ}
    (hG₁ : ContDiff ℝ 2 G₁) {x₀ x₁ : P} {r₀ r₁ : ℝ} (T : E ≃L[ℝ] E)
    (hG : ∀ w ∈ Metric.ball (0 : E) r₀, T w ∈ Metric.ball (0 : E) r₁ → G₀ (x₀, w) = G₁ (x₁, T w))
    (h₀ : ∀ w ∈ Metric.ball (0 : E) r₀, IsCongruencePoint G₀ (x₀, w))
    (h₁ : ∀ w ∈ Metric.ball (0 : E) r₁, IsCongruencePoint G₁ (x₁, w))
    {w₀ : E} (hw₀ : w₀ ∈ Metric.ball (0 : E) r₀) (hw₁ : T w₀ ∈ Metric.ball (0 : E) r₁) :
    parametricMorseCoord G₁ (x₁, T w₀) = T (parametricMorseCoord G₀ (x₀, w₀)) := by
  set k₀ : E → ℝ := fun w ↦ G₀ (x₀, w) with hk₀def
  set k₁ : E → ℝ := fun w ↦ G₁ (x₁, w) with hk₁def
  -- The fibres correspond on the convex open set `D` of points of the first ball sent into the
  -- second ball, which contains the segment from `0` to `w₀`.
  set D : Set E := Metric.ball (0 : E) r₀ ∩ T ⁻¹' Metric.ball (0 : E) r₁ with hD
  have hDo : IsOpen D := Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage T.continuous)
  have hDc : Convex ℝ D :=
    (convex_ball 0 r₀).inter ((convex_ball 0 r₁).linear_preimage (T : E →ₗ[ℝ] E))
  have hD₀ : (0 : E) ∈ D :=
    ⟨Metric.mem_ball_self (Metric.pos_of_mem_ball hw₀), by simp [Metric.pos_of_mem_ball hw₁]⟩
  have hDw : w₀ ∈ D := ⟨hw₀, hw₁⟩
  have hseg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t • w₀ ∈ D :=
    (hDc.starConvex hD₀).smul_mem hDw ht.1 ht.2
  have hloc {y : E} (hy : y ∈ D) : k₀ =ᶠ[𝓝 y] k₁ ∘ T :=
    Filter.eventuallyEq_of_mem (hDo.mem_nhds hy) fun w hw ↦ hG w hw.1 hw.2
  have hk₁ : ContDiff ℝ 2 k₁ := hG₁.comp (contDiff_const.prodMk contDiff_id)
  -- The Hessians and averaged Hessians of the two fibres are pulled back from each other.
  have hHess : fderiv ℝ (fderiv ℝ k₀) 0 = (fderiv ℝ (fderiv ℝ k₁) 0).bilinearComp
      (T : E →L[ℝ] E) (T : E →L[ℝ] E) := by
    rw [(hloc hD₀).fderiv.fderiv_eq]
    ext u u'
    simpa using T.fderiv_fderiv_comp_right_apply_apply k₁ 0 u u'
  have havg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : hessianAverage k₀ 0 (t • w₀) =
      (hessianAverage k₁ 0 (t • T w₀)).bilinearComp (T : E →L[ℝ] E) (T : E →L[ℝ] E) := by
    rw [hessianAverage_congr_of_eventuallyEq (f₂ := k₁ ∘ T) fun s hs ↦ hloc (by
      simpa [smul_smul] using
        hseg ⟨mul_nonneg hs.1 ht.1, (mul_le_of_le_one_left ht.1 hs.2).trans ht.2⟩)]
    ext u u'
    simpa using hessianAverage_comp_continuousLinearEquiv_apply hk₁ T 0 (t • w₀) u u'
  have hmem₁ {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t • T w₀ ∈ Metric.ball (0 : E) r₁ := by
    simpa using (hseg ht).2
  have hmem₀ {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t • w₀ ∈ Metric.ball (0 : E) r₀ := (hseg ht).1
  -- The two congruences along the segments, read as functions of the time `t`.
  have hpath₁ : Continuous fun t : ℝ ↦ (x₁, t • T w₀) := by fun_prop
  have hpath₀ : Continuous fun t : ℝ ↦ (x₀, t • w₀) := by fun_prop
  have hR : ContinuousOn (fun t : ℝ ↦ morseCongruence (fderiv ℝ (fderiv ℝ k₁) 0)
      (hessianAverage k₁ 0 (t • T w₀))) (Icc 0 1) := fun t ht ↦
    ((h₁ _ (hmem₁ ht)).1.comp (f := fun t : ℝ ↦ (x₁, t • T w₀))
      hpath₁.continuousAt).continuousWithinAt
  have hR' : ContinuousOn (fun t : ℝ ↦ morseCongruence ((fderiv ℝ (fderiv ℝ k₁) 0).bilinearComp
      (T : E →L[ℝ] E) (T : E →L[ℝ] E))
      ((hessianAverage k₁ 0 (t • T w₀)).bilinearComp (T : E →L[ℝ] E) (T : E →L[ℝ] E)))
      (Icc 0 1) := by
    refine ContinuousOn.congr (f := fun t : ℝ ↦ congruenceAt G₀ (x₀, t • w₀)) (fun t ht ↦
      ((h₀ _ (hmem₀ ht)).1.comp (f := fun t : ℝ ↦ (x₀, t • w₀))
        hpath₀.continuousAt).continuousWithinAt) fun t ht ↦ ?_
    simp only [congruenceAt, ← hk₀def]
    rw [← hHess, ← havg ht]
  have hEq := eqOn_morseCongruence_bilinearComp isPreconnected_Icc
    (left_mem_Icc.2 zero_le_one) (B₀ := fderiv ℝ (fderiv ℝ k₁) 0)
    (B := fun t : ℝ ↦ hessianAverage k₁ 0 (t • T w₀))
    (h₁ 0 (Metric.mem_ball_self (Metric.pos_of_mem_ball hw₁))).2.2.2
    (by simp) T hR hR' (fun t ht ↦ (h₁ _ (hmem₁ ht)).2.1)
    (fun t ht ↦ by
      have h := (h₀ _ (hmem₀ ht)).2.1
      simp only [congruenceAt, ← hk₀def] at h
      rwa [hHess, havg ht] at h)
    (fun t ht ↦ (h₁ _ (hmem₁ ht)).2.2.1) (right_mem_Icc.2 zero_le_one)
  have havg₁ := havg (right_mem_Icc.2 zero_le_one)
  simp only [one_smul] at hEq havg₁
  rw [← hHess, ← havg₁] at hEq
  rw [parametricMorseCoord_eq_congruenceAt, parametricMorseCoord_eq_congruenceAt]
  simp only [congruenceAt, ← hk₀def, ← hk₁def, hEq]
  simp

end Congruence

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, TopologicalSpace (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]

section Chart

/-- The chart of the total space at a point of the zero section. -/
private theorem extChartAt_zeroSection_apply (b₀ : B) {v : TotalSpace F V}
    (hv : v.proj ∈ (trivializationAt F V b₀).baseSet) :
    extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b₀) v =
      (extChartAt IB b₀ v.proj, (trivializationAt F V b₀ v).2) := by
  rw [FiberBundle.extChartAt]
  simp [(trivializationAt F V b₀).coe_fst' hv]

/-- The inverse of the chart of the total space at a point of the zero section. -/
private theorem extChartAt_zeroSection_symm_apply (b₀ : B) {x : EB}
    (hx : (extChartAt IB b₀).symm x ∈ (trivializationAt F V b₀).baseSet) (w : F) :
    (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b₀)).symm (x, w) =
      ⟨(extChartAt IB b₀).symm x,
        (trivializationAt F V b₀).symm ((extChartAt IB b₀).symm x) w⟩ := by
  rw [FiberBundle.extChartAt]
  exact ((trivializationAt F V b₀).mk_symm hx w).symm

/-- The source of the chart of the total space at a point of the zero section. -/
private theorem mem_extChartAt_zeroSection_source (b₀ : B) (v : TotalSpace F V) :
    v ∈ (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b₀)).source ↔
      v.proj ∈ (extChartAt IB b₀).source ∩ (trivializationAt F V b₀).baseSet := by
  rw [FiberBundle.extChartAt]
  simp only [PartialEquiv.trans_source, mem_inter_iff,
    Trivialization.mem_source, mem_preimage, PartialEquiv.prod_source, PartialEquiv.refl_source,
    mem_prod, mem_univ, and_true, zeroSection_proj]
  exact ⟨fun h ↦ ⟨(trivializationAt F V b₀).coe_fst' h.1 ▸ h.2, h.1⟩,
    fun h ↦ ⟨h.2, ((trivializationAt F V b₀).coe_fst' h.2).symm ▸ h.1⟩⟩

/-- The inverse of the chart of the total space at a point of the zero section, at a point
`(φ b, w)` of the image of the fibre over `b`. -/
private theorem extChartAt_zeroSection_symm_apply_extChartAt (b₀ : B) {b : B}
    (hb : b ∈ (extChartAt IB b₀).source ∩ (trivializationAt F V b₀).baseSet) (w : F) :
    (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b₀)).symm (extChartAt IB b₀ b, w) =
      ⟨b, (trivializationAt F V b₀).symm b w⟩ := by
  have h := (extChartAt IB b₀).left_inv hb.1
  rw [extChartAt_zeroSection_symm_apply b₀ (by rw [h]; exact hb.2) w, h]

/-- The target of the chart of the total space at a point of the zero section. -/
private theorem extChartAt_zeroSection_target (b₀ : B) :
    (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b₀)).target =
      ((extChartAt IB b₀).target ∩
        (extChartAt IB b₀).symm ⁻¹' (trivializationAt F V b₀).baseSet) ×ˢ univ := by
  rw [FiberBundle.extChartAt_target]
  rfl

end Chart

section Fiber

variable [∀ b, Module ℝ (V b)] (g : TotalSpace F V → ℝ)

omit [∀ b, TopologicalSpace (V b)] [FiberBundle F V] in
/-- Read in two trivializations, the restrictions of a function to a fibre differ by the
coordinate change of the trivializations. -/
private theorem fiber_comp_coordChangeL (e e' : Trivialization F (π F V)) [e.IsLinear ℝ]
    [e'.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    (fun w ↦ g ⟨b, e'.symm b w⟩) ∘ e.coordChangeL ℝ e' b = fun w ↦ g ⟨b, e.symm b w⟩ := by
  funext w
  simp [e.coordChangeL_apply e' hb, e'.symm_apply_apply_mk hb.2]

end Fiber

section MorseLemma

variable [∀ b, Module ℝ (V b)] [VectorBundle ℝ F V] [FiniteDimensional ℝ EB] [IB.Boundaryless]
  [FiniteDimensional ℝ F] {n : ℕ∞} [IsManifold IB (n + 2) B] [ContMDiffVectorBundle (n + 2) F V IB]
  {g : TotalSpace F V → ℝ} {N : Set (TotalSpace F V)}

/-- **The parametric Morse lemma in the chart at a point of the zero section.** Read in the chart
of the total space at `0_{b₀}`, a function `g` which is `C^{n+2}` near `0_{b₀}`, with critical and
nondegenerate fibre restrictions near `b₀`, agrees on a product `U₀ ×ˢ ball 0 r` with a globally
`C^{n+2}` family `G`, whose canonical coordinate is a partial diffeomorphism `Θ` on that product,
putting `G` in normal form, and all of whose points are congruence points. -/
private theorem exists_extChartAt_zeroSection_morse_data (hN : IsOpen N)
    (hg : ContMDiffOn (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ) (n + 2) g N) {b₀ : B}
    (hb₀ : zeroSection F V b₀ ∈ N)
    (hcrit : ∀ᶠ b in 𝓝 b₀, fderiv ℝ (fun w ↦ g ⟨b, (trivializationAt F V b).symm b w⟩) 0 = 0)
    (hH : (fderiv ℝ (fderiv ℝ fun w ↦ g ⟨b₀, (trivializationAt F V b₀).symm b₀ w⟩) 0).IsInvertible)
    (hn : n ≠ 0) :
    ∃ (G : EB × F → ℝ) (U₀ : Set EB) (r : ℝ)
      (Θ : PartialDiffeomorph 𝓘(ℝ, EB × F) 𝓘(ℝ, EB × F) (EB × F) (EB × F) n),
      ContDiff ℝ 2 G ∧ IsOpen U₀ ∧ extChartAt IB b₀ b₀ ∈ U₀ ∧ 0 < r ∧
      U₀ ⊆ (extChartAt IB b₀).target ∩
        (extChartAt IB b₀).symm ⁻¹' (trivializationAt F V b₀).baseSet ∧
      Θ.source = U₀ ×ˢ Metric.ball 0 r ∧
      (∀ z ∈ U₀ ×ˢ Metric.ball 0 r, Θ z = (z.1, parametricMorseCoord G z)) ∧
      (∀ z ∈ U₀ ×ˢ Metric.ball 0 r,
        (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b₀)).symm z ∈ N ∧
        G z = g ((extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b₀)).symm z)) ∧
      (∀ z ∈ U₀ ×ˢ Metric.ball 0 r, G z = G (z.1, 0) + (2 : ℝ)⁻¹ *
        fderiv ℝ (fderiv ℝ (fun v ↦ G (z.1, v))) 0 (parametricMorseCoord G z)
          (parametricMorseCoord G z)) ∧
      ∀ z ∈ U₀ ×ˢ Metric.ball 0 r, IsCongruencePoint G z := by
  set χ := extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b₀) with hχ
  set φ := extChartAt IB b₀ with hφ
  set e₀ := trivializationAt F V b₀ with he₀
  have hb₀e₀ : b₀ ∈ e₀.baseSet := FiberBundle.mem_baseSet_trivializationAt' b₀
  -- The coordinate expression of `g` is `C^{n+2}` on an open neighbourhood `O` of `(φ b₀, 0)`.
  set O : Set (EB × F) := χ.target ∩ χ.symm ⁻¹' N with hOdef
  have hO : IsOpen O :=
    (continuousOn_extChartAt_symm _).isOpen_inter_preimage (isOpen_extChartAt_target _) hN
  have hχ₀ : χ (zeroSection F V b₀) = (φ b₀, 0) := by
    rw [hχ, extChartAt_zeroSection_apply b₀ (by simpa using hb₀e₀)]
    simp [hφ, ← he₀, e₀.zeroSection ℝ hb₀e₀]
  have hx₀O : (φ b₀, (0 : F)) ∈ O := by
    rw [← hχ₀]
    exact ⟨mem_extChartAt_target _, by rwa [mem_preimage, extChartAt_to_inv]⟩
  have hf : ContDiffOn ℝ (n + 2) (g ∘ χ.symm) O := by
    have h := (contMDiffOn_iff.1 hg).2 (zeroSection F V b₀) (g (zeroSection F V b₀))
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, PartialEquiv.refl_source,
      preimage_univ, inter_univ, Function.id_comp, ← hχ] at h
    exact h
  obtain ⟨G, hG, -, hGf⟩ := hf.exists_contDiff_eventuallyEq_of_finiteDimensional
    (hO.mem_nhds hx₀O)
  have hG₂ : ContDiff ℝ 2 G := hG.of_le (WithTop.coe_le_coe.2 (le_add_self : (2 : ℕ∞) ≤ n + 2))
  -- Over a point `x` whose image `b` lies in the base set of `e₀`, the fibre of the coordinate
  -- expression is the restriction of `g` to the fibre over `b`, read in `e₀`.
  have hfib {x : EB} (hx : φ.symm x ∈ e₀.baseSet) :
      (fun w ↦ (g ∘ χ.symm) (x, w)) = fun w ↦ g ⟨φ.symm x, e₀.symm (φ.symm x) w⟩ := by
    funext w
    rw [Function.comp_apply, hχ, extChartAt_zeroSection_symm_apply b₀ hx w]
  obtain ⟨U₁, V₁, hU₁, hx₀U₁, hV₁, h0V₁, hUV₁⟩ := mem_nhds_prod_iff'.1 hGf
  have hslice {x : EB} (hx : x ∈ U₁) : (fun w ↦ G (x, w)) =ᶠ[𝓝 0] fun w ↦ (g ∘ χ.symm) (x, w) :=
    Filter.eventuallyEq_of_mem (hV₁.mem_nhds h0V₁) fun w hw ↦ hUV₁ (mk_mem_prod hx hw)
  have hφsymm : Tendsto φ.symm (𝓝 (φ b₀)) (𝓝 b₀) := by
    simpa [hφ, extChartAt_to_inv] using (continuousAt_extChartAt_symm (I := IB) b₀).tendsto
  -- The zero section of `G` is critical near `φ b₀`, and its vertical Hessian at `φ b₀` is that
  -- of `g` on the fibre over `b₀`.
  have hcritG : ∀ᶠ x in 𝓝 (φ b₀), fderiv ℝ (fun w ↦ G (x, w)) 0 = 0 := by
    filter_upwards [hU₁.mem_nhds hx₀U₁, hφsymm.eventually (e₀.open_baseSet.mem_nhds hb₀e₀),
      hφsymm.eventually hcrit] with x hxU₁ hxe₀ hxcrit
    rw [(hslice hxU₁).fderiv_eq, hfib hxe₀, ← fiber_comp_coordChangeL g e₀
      (trivializationAt F V (φ.symm x)) ⟨hxe₀, FiberBundle.mem_baseSet_trivializationAt' _⟩,
      ContinuousLinearEquiv.comp_right_fderiv, map_zero, hxcrit, ContinuousLinearMap.zero_comp]
  have hHG : (fderiv ℝ (fderiv ℝ fun w ↦ G (φ b₀, w)) 0).IsInvertible := by
    rw [(hslice hx₀U₁).fderiv.fderiv_eq, hfib (by rwa [extChartAt_to_inv]), extChartAt_to_inv]
    exact hH
  obtain ⟨U₀', r', Θ', -, hx₀U₀', hr', hΘ'src, -, hΘ'eq, hΘ'nf⟩ :=
    exists_parametricMorseCoord_partialDiffeomorph_prod_ball (W := univ) univ_mem hG.contDiffOn
      hcritG hHG hn
  -- A product neighbourhood on which all of the above hold.
  have hS : {z | G z = (g ∘ χ.symm) z} ∩ O ∩ {z | IsCongruencePoint G z} ∩ Θ'.source ∈
      𝓝 (φ b₀, (0 : F)) := by
    refine inter_mem (inter_mem (inter_mem hGf (hO.mem_nhds hx₀O))
      (eventually_isCongruencePoint hG₂ hHG)) (Θ'.open_source.mem_nhds ?_)
    exact hΘ'src ▸ mk_mem_prod hx₀U₀' (Metric.mem_ball_self hr')
  obtain ⟨U₀, V₀, hU₀, hx₀U₀, hV₀, h0V₀, hUV₀⟩ := mem_nhds_prod_iff'.1 hS
  obtain ⟨r, hr, hrV₀⟩ := Metric.isOpen_iff.1 hV₀ 0 h0V₀
  have hsub : U₀ ×ˢ Metric.ball (0 : F) r ⊆ _ := (prod_mono le_rfl hrV₀).trans hUV₀
  refine ⟨G, U₀, r, Θ'.restrOpen (U₀ ×ˢ Metric.ball 0 r) (hU₀.prod Metric.isOpen_ball), hG₂,
    hU₀, hx₀U₀, hr, fun x hx ↦ ?_, ?_, fun z hz ↦ ?_, fun z hz ↦ ⟨(hsub hz).1.1.2.2,
      (hsub hz).1.1.1⟩, fun z hz ↦ hΘ'nf z (hΘ'src ▸ (hsub hz).2), fun z hz ↦ (hsub hz).1.2⟩
  · have h := (hsub (mk_mem_prod hx (Metric.mem_ball_self hr))).1.1.2.1
    rw [hχ, extChartAt_zeroSection_target] at h
    exact h.1
  · rw [PartialDiffeomorph.restrOpen_source, inter_eq_right]
    exact fun z hz ↦ (hsub hz).2
  · rw [PartialDiffeomorph.coe_restrOpen]
    exact hΘ'eq z (hΘ'src ▸ (hsub hz).2)

/-- **The parametric Morse lemma on a vector bundle.** Let `g` be a `C^{n+2}` function, with
`1 ≤ n ≤ ∞`, on an open set `N` of the total space of a `C^{n+2}` vector bundle `V` with
finite-dimensional fibres over a boundaryless finite-dimensional manifold, and let `U` be an open
set of the base over which the zero section lies in `N`. Suppose that over each `b ∈ U` the
restriction of `g` to the fibre, read in the trivialization at `b`, has a nondegenerate critical
point at `0`. Then there is a `C^n` local diffeomorphism `Ψ` of the total space on an open
neighbourhood `W ⊆ N` of the zero section over `U`, preserving every fibre and fixing the zero
section over `U`, which puts `g` in normal form: for every `v ∈ W` over `b`,
`g v = g 0_b + ½ H_b (Ψ v, Ψ v)`, where `H_b` is the Hessian at `0` of the restriction of `g` to
the fibre over `b`, read in any linear trivialization around `b`. Near each point `0_b` of the
zero section, `Ψ` is read in the chart of the total space at `0_b` as the canonical parametric
Morse coordinate `TauCeti.parametricMorseCoord` of `g` in that chart. -/
theorem exists_bundle_morse_normal_form (hN : IsOpen N)
    (hg : ContMDiffOn (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ) (n + 2) g N) {U : Set B} (hU : IsOpen U)
    (hUN : ∀ b ∈ U, zeroSection F V b ∈ N)
    (hcrit : ∀ b ∈ U, fderiv ℝ (fun w ↦ g ⟨b, (trivializationAt F V b).symm b w⟩) 0 = 0)
    (hH : ∀ b ∈ U,
      (fderiv ℝ (fderiv ℝ fun w ↦ g ⟨b, (trivializationAt F V b).symm b w⟩) 0).IsInvertible)
    (hn : n ≠ 0) :
    ∃ (W : Set (TotalSpace F V)) (Ψ : TotalSpace F V → TotalSpace F V),
      IsOpen W ∧ W ⊆ N ∧ (∀ b ∈ U, zeroSection F V b ∈ W) ∧
      IsLocalDiffeomorphOn (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) n Ψ W ∧
      (∀ v, (Ψ v).proj = v.proj) ∧ (∀ b ∈ U, Ψ (zeroSection F V b) = zeroSection F V b) ∧
      (∀ v ∈ W, ∀ (e : Trivialization F (π F V)) [e.IsLinear ℝ], v.proj ∈ e.baseSet →
        g v = g (zeroSection F V v.proj) + (2 : ℝ)⁻¹ *
          fderiv ℝ (fderiv ℝ fun w ↦ g ⟨v.proj, e.symm v.proj w⟩) 0 (e (Ψ v)).2 (e (Ψ v)).2) ∧
      ∀ b ∈ U, ∀ᶠ v in 𝓝 (zeroSection F V b),
        extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b) (Ψ v) =
          ((extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b) v).1,
            parametricMorseCoord (g ∘ (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b)).symm)
              (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b) v)) := by
  classical
  have : Nonempty (PartialDiffeomorph 𝓘(ℝ, EB × F) 𝓘(ℝ, EB × F) (EB × F) (EB × F) n) :=
    ⟨(Diffeomorph.refl 𝓘(ℝ, EB × F) (EB × F) n).toPartialDiffeomorph⟩
  have hloc := fun b₀ (hb₀ : b₀ ∈ U) ↦ exists_extChartAt_zeroSection_morse_data hN hg
    (hUN b₀ hb₀) (Filter.eventually_of_mem (hU.mem_nhds hb₀) hcrit) (hH b₀ hb₀) hn
  choose! G U₀ r Θ hG hU₀ hx₀ hr hU₀sub hΘsrc hΘeq hGN hnf hgood using hloc
  -- The chart of the total space at `0_b`, as a partial diffeomorphism onto its open target.
  let Ξ : B → PartialDiffeomorph (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, EB × F) (TotalSpace F V) (EB × F) n :=
    fun b₀ ↦
      { toPartialEquiv := extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b₀)
        open_source := isOpen_extChartAt_source _
        open_target := isOpen_extChartAt_target _
        contMDiffOn_toFun := by
          rw [extChartAt_source]
          exact (contMDiffOn_extChartAt (n := (n : WithTop ℕ∞) + 2)).of_le le_self_add
        contMDiffOn_invFun :=
          (contMDiffOn_extChartAt_symm (n := (n : WithTop ℕ∞) + 2) _).of_le le_self_add }
  -- In the chart at `0_b`, the canonical coordinate is the partial diffeomorphism `Θ b`.
  let Φ : B → PartialDiffeomorph (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F))
      (TotalSpace F V) (TotalSpace F V) n :=
    fun b₀ ↦ ((Ξ b₀).trans (Θ b₀)).trans (Ξ b₀).symm
  have hΞ (b₀ : B) : ⇑(Ξ b₀) = extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b₀) := rfl
  have hΞsymm (b₀ : B) :
      ⇑(Ξ b₀).symm = (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b₀)).symm := rfl
  have hΞtarget (b₀ : B) :
      (Ξ b₀).symm.source = (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b₀)).target := rfl
  -- The source of `Φ b₀` is the set of points read in the chart at `0_{b₀}` in `U₀ b₀ ×ˢ ball`.
  have hΦsrc {b₀ : B} (hb₀ : b₀ ∈ U) {v : TotalSpace F V} :
      v ∈ (Φ b₀).source ↔ v ∈ (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b₀)).source ∧
        extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b₀) v ∈
          U₀ b₀ ×ˢ Metric.ball 0 (r b₀) := by
    simp only [Φ, PartialDiffeomorph.trans_source, mem_inter_iff, mem_preimage,
      PartialDiffeomorph.coe_trans, Function.comp_apply, hΘsrc b₀ hb₀, hΞ, hΞtarget]
    refine ⟨fun h ↦ ⟨h.1.1, h.1.2⟩, fun h ↦ ⟨h, ?_⟩⟩
    rw [hΘeq b₀ hb₀ _ h.2, extChartAt_zeroSection_target]
    exact ⟨hU₀sub b₀ hb₀ h.2.1, mem_univ _⟩
  -- On its source, `Φ b₀` is the canonical coordinate read in the trivialization at `b₀`.
  have hΦ {b₀ : B} (hb₀ : b₀ ∈ U) {v : TotalSpace F V} (hv : v ∈ (Φ b₀).source) :
      v.proj ∈ (extChartAt IB b₀).source ∩ (trivializationAt F V b₀).baseSet ∧
      extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b₀) v =
        (extChartAt IB b₀ v.proj, (trivializationAt F V b₀ v).2) ∧
      Φ b₀ v = ⟨v.proj, (trivializationAt F V b₀).symm v.proj (parametricMorseCoord (G b₀)
        (extChartAt IB b₀ v.proj, (trivializationAt F V b₀ v).2))⟩ := by
    have hv' := (hΦsrc hb₀).1 hv
    have hb := (mem_extChartAt_zeroSection_source b₀ v).1 hv'.1
    have hχv := extChartAt_zeroSection_apply (IB := IB) b₀ hb.2
    refine ⟨hb, hχv, ?_⟩
    simp only [Φ, PartialDiffeomorph.coe_trans, Function.comp_apply, hΞ, hΞsymm]
    rw [hΘeq b₀ hb₀ _ hv'.2, hχv, extChartAt_zeroSection_symm_apply_extChartAt b₀ hb]
  -- The canonical coordinates read in the charts at two points of the zero section agree.
  have hagree {b₀ b₁ : B} (hb₀ : b₀ ∈ U) (hb₁ : b₁ ∈ U) {v : TotalSpace F V}
      (hv₀ : v ∈ (Φ b₀).source) (hv₁ : v ∈ (Φ b₁).source) : Φ b₀ v = Φ b₁ v := by
    obtain ⟨hb₀v, hχ₀, hΦ₀⟩ := hΦ hb₀ hv₀
    obtain ⟨hb₁v, hχ₁, hΦ₁⟩ := hΦ hb₁ hv₁
    have hz₀ := ((hΦsrc hb₀).1 hv₀).2
    have hz₁ := ((hΦsrc hb₁).1 hv₁).2
    rw [hχ₀] at hz₀
    rw [hχ₁] at hz₁
    set e₀ := trivializationAt F V b₀
    set e₁ := trivializationAt F V b₁
    set b := v.proj
    have hb : b ∈ e₀.baseSet ∩ e₁.baseSet := ⟨hb₀v.2, hb₁v.2⟩
    set T := e₀.coordChangeL ℝ e₁ b
    have hTw : T (e₀ v).2 = (e₁ v).2 := by
      rw [e₀.coordChangeL_apply e₁ hb, e₀.symm_proj_apply v hb₀v.2]
    have hT (c : F) : e₁.symm b (T c) = e₀.symm b c := by
      rw [e₀.coordChangeL_apply e₁ hb, e₁.symm_apply_apply_mk hb.2]
    -- The two families agree on corresponding points of the fibre balls.
    have hGG (w : F) (hw : w ∈ Metric.ball (0 : F) (r b₀))
        (hTw : T w ∈ Metric.ball (0 : F) (r b₁)) :
        G b₀ (extChartAt IB b₀ b, w) = G b₁ (extChartAt IB b₁ b, T w) := by
      rw [(hGN b₀ hb₀ (extChartAt IB b₀ b, w) ⟨hz₀.1, hw⟩).2,
        (hGN b₁ hb₁ (extChartAt IB b₁ b, T w) ⟨hz₁.1, hTw⟩).2,
        extChartAt_zeroSection_symm_apply_extChartAt b₀ hb₀v,
        extChartAt_zeroSection_symm_apply_extChartAt b₁ hb₁v, hT]
    have hc := parametricMorseCoord_eq_of_isCongruencePoint (hG b₁ hb₁) T hGG
      (fun w hw ↦ hgood b₀ hb₀ (extChartAt IB b₀ b, w) ⟨hz₀.1, hw⟩)
      (fun w hw ↦ hgood b₁ hb₁ (extChartAt IB b₁ b, w) ⟨hz₁.1, hw⟩) hz₀.2
      (hTw ▸ hz₁.2)
    rw [hΦ₀, hΦ₁, ← hTw, hc, hT]
  -- Glue the local coordinates.
  let Ψ : TotalSpace F V → TotalSpace F V := fun v ↦
    if h : ∃ b ∈ U, v ∈ (Φ b).source then Φ h.choose v else v
  have hΨ {b₀ : B} (hb₀ : b₀ ∈ U) {v : TotalSpace F V} (hv : v ∈ (Φ b₀).source) :
      Ψ v = Φ b₀ v := by
    have h : ∃ b ∈ U, v ∈ (Φ b).source := ⟨b₀, hb₀, hv⟩
    simp only [Ψ, h, ↓reduceDIte]
    exact hagree h.choose_spec.1 hb₀ h.choose_spec.2 hv
  have hzero {b₀ : B} (hb₀ : b₀ ∈ U) : zeroSection F V b₀ ∈ (Φ b₀).source := by
    have hb : b₀ ∈ (extChartAt IB b₀).source ∩ (trivializationAt F V b₀).baseSet :=
      ⟨mem_extChartAt_source b₀, FiberBundle.mem_baseSet_trivializationAt' b₀⟩
    refine (hΦsrc hb₀).2 ⟨(mem_extChartAt_zeroSection_source b₀ _).2 hb, ?_⟩
    rw [extChartAt_zeroSection_apply b₀ hb.2]
    simpa [(trivializationAt F V b₀).zeroSection ℝ hb.2, hr b₀ hb₀] using hx₀ b₀ hb₀
  refine ⟨⋃ b ∈ U, (Φ b).source, Ψ, isOpen_biUnion fun b _ ↦ (Φ b).open_source, ?_,
    fun b hb ↦ mem_biUnion hb (hzero hb), ?_, fun v ↦ ?_, fun b hb ↦ ?_, ?_, fun b hb ↦ ?_⟩
  · -- The glued domain lies in `N`.
    simp only [iUnion_subset_iff]
    intro b₀ hb₀ v hv
    have hv' := (hΦsrc hb₀).1 hv
    have h := (hGN b₀ hb₀ _ hv'.2).1
    rwa [(extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b₀)).left_inv hv'.1] at h
  · -- `Ψ` agrees with a partial diffeomorphism near each point of the glued domain.
    rintro ⟨v, hv⟩
    obtain ⟨b₀, hb₀, hv⟩ := mem_iUnion₂.1 hv
    exact isLocalDiffeomorphAt_of_eqOn hv fun y hy ↦ hΨ hb₀ hy
  · -- `Ψ` preserves the fibres.
    by_cases h : ∃ b ∈ U, v ∈ (Φ b).source
    · rw [hΨ h.choose_spec.1 h.choose_spec.2, (hΦ h.choose_spec.1 h.choose_spec.2).2.2]
    · simp only [Ψ, h, ↓reduceDIte]
  · -- `Ψ` fixes the zero section.
    have hb' := (hΦ hb (hzero hb)).1.2
    rw [hΨ hb (hzero hb), (hΦ hb (hzero hb)).2.2]
    simp only [zeroSection_proj] at hb' ⊢
    rw [(trivializationAt F V b).zeroSection ℝ hb', parametricMorseCoord_mk_zero,
      ← (trivializationAt F V b).symmₗ_apply (R := ℝ) hb', map_zero]
    rfl
  · -- The normal form, read first in the trivialization at `b₀` and then in `e`.
    intro v hv e _ hve
    obtain ⟨b₀, hb₀, hv⟩ := mem_iUnion₂.1 hv
    obtain ⟨hb, hχv, hΦv⟩ := hΦ hb₀ hv
    have hz := ((hΦsrc hb₀).1 hv).2
    rw [hχv] at hz
    set e₀ := trivializationAt F V b₀
    set b := v.proj
    have h0 : (0 : F) ∈ Metric.ball 0 (r b₀) := Metric.mem_ball_self (hr b₀ hb₀)
    have hfib : (fun w ↦ G b₀ (extChartAt IB b₀ b, w)) =ᶠ[𝓝 0] fun w ↦ g ⟨b, e₀.symm b w⟩ :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds h0) fun w hw ↦ by
        rw [(hGN b₀ hb₀ (extChartAt IB b₀ b, w) ⟨hz.1, hw⟩).2,
          extChartAt_zeroSection_symm_apply_extChartAt b₀ hb]
    have hb' : b ∈ e₀.baseSet ∩ e.baseSet := ⟨hb.2, hve⟩
    have h := hnf b₀ hb₀ _ hz
    rw [(hGN b₀ hb₀ _ hz).2, (hGN b₀ hb₀ (extChartAt IB b₀ b, 0) ⟨hz.1, h0⟩).2,
      extChartAt_zeroSection_symm_apply_extChartAt b₀ hb,
      extChartAt_zeroSection_symm_apply_extChartAt b₀ hb, e₀.symm_proj_apply v hb.2,
      ← e₀.symmₗ_apply (R := ℝ) hb.2, map_zero, hfib.fderiv.fderiv_eq,
      ← fiber_comp_coordChangeL g e₀ e hb',
      ContinuousLinearEquiv.fderiv_fderiv_comp_right_apply_apply] at h
    rw [hΨ hb₀ hv, hΦv, ← e₀.coordChangeL_apply (R := ℝ) e hb']
    simp only [b, TotalSpace.eta, map_zero] at h
    -- `zeroSection F V b` is `⟨b, 0⟩` by definition.
    exact h
  · -- Near `0_b`, `Ψ` is the canonical coordinate read in the chart at `0_b`.
    have hb' : b ∈ (trivializationAt F V b).baseSet := FiberBundle.mem_baseSet_trivializationAt' b
    have hχ0 : extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b) (zeroSection F V b) =
        (extChartAt IB b b, 0) := by
      rw [extChartAt_zeroSection_apply b (by simpa using hb')]
      simp [(trivializationAt F V b).zeroSection ℝ hb']
    have hGeq : G b =ᶠ[𝓝 (extChartAt IB b b, (0 : F))]
        g ∘ (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b)).symm := by
      rw [← hχ0]
      exact Filter.eventuallyEq_of_mem (((hU₀ b hb).prod Metric.isOpen_ball).mem_nhds
        ((hΦsrc hb).1 (hzero hb)).2) fun z hz ↦ (hGN b hb z hz).2
    have hχ : Tendsto (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F V b))
        (𝓝 (zeroSection F V b)) (𝓝 (extChartAt IB b b, (0 : F))) :=
      hχ0 ▸ (continuousAt_extChartAt (zeroSection F V b)).tendsto
    filter_upwards [(Φ b).open_source.mem_nhds (hzero hb), hχ.eventually hGeq.parametricMorseCoord]
      with v hv hpmc
    obtain ⟨hbv, hχv, hΦv⟩ := hΦ hb hv
    rw [hΨ hb hv, ← hpmc, hΦv, hχv, extChartAt_zeroSection_apply (IB := IB) b]
    · simp [(trivializationAt F V b).apply_mk_symm hbv.2]
    · exact hbv.2

end MorseLemma



end TauCeti
