/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Local.Approximation
public import TauCeti.MeasureTheory.Function.Lp.Translation

/-!
# Shifted mollification up to the boundary

Let `u ∈ W^{k,p}(Ω)` vanish off a compact set `K`, and let `h i → 0` be translation vectors and
`φ i` smooth bumps with radii `r i → 0`. Suppose that for every `x ∈ Ω` the closed ball
`closedBall (x + h i) (r i)` either lies in `Ω` or misses `K`. Then the functions
`x ↦ (φ i ⋆ 1_Ω u) (x + h i)` are smooth with compact support in the whole space, and their
restrictions to `Ω` converge to `u` in the full `W^{k,p}(Ω)` norm for `1 ≤ p < ∞`.

This is the approximation step of the segment condition (Adams–Fournier, *Sobolev Spaces*,
Theorem 3.22). Near a boundary point the translation `h i` points into the domain, so the
mollifier only averages values of `u` taken inside `Ω`, even at points of `Ω` next to its
boundary. Away from the support of `u` both sides vanish. The convergence combines the
`Lᵖ` approximate identity with continuity of translation in `Lᵖ`. With `h i = 0` the same
statement covers a function whose support is compact inside `Ω`.

## Main declarations

* `TauCeti.Wkp.mem_closure_range_restrictL_ofTestFunctionₗ_top_of_shift`: under the ball
  condition above, `u` lies in the closure of the restrictions to `Ω` of test functions on the
  whole space.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 3.22.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.3.3.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped Convolution Distributions ENNReal Gradient Pointwise Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

local instance : (mu.restrict (univ : Set E)).IsAddHaarMeasure := by
  rw [Measure.restrict_univ]
  infer_instance

/-- The convolution of the zero extension of a field with a normalized bump. -/
private def bumpField {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (phi : ContDiffBump (0 : E)) (f : Lp F p (mu.restrict Omega)) : E → F :=
  phi.normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] (Omega : Set E).indicator (f : E → F)

private theorem contDiff_bumpField {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (phi : ContDiffBump (0 : E)) (f : Lp F p (mu.restrict Omega)) :
    ContDiff ℝ (⊤ : ℕ∞) (bumpField phi f) := by
  have hmem := (memLp_indicator_iff_restrict Omega.isOpen.measurableSet.nullMeasurableSet).2
    (Lp.memLp f)
  exact phi.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) phi.contDiff_normed (hmem.locallyIntegrable Fact.out)

omit [Fact (1 ≤ p)] in
/-- A mollified field vanishes at every point whose bump ball misses the set off which the field
vanishes. -/
private theorem bumpField_eq_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (phi : ContDiffBump (0 : E)) {K : Set E} (f : Lp F p (mu.restrict Omega))
    (hf : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → f x = 0) {y : E}
    (hy : y ∉ K + closedBall (0 : E) phi.rOut) :
    bumpField phi f y = 0 := by
  have hae : (Omega : Set E).indicator (f : E → F) =ᵐ[mu]
      K.indicator ((Omega : Set E).indicator (f : E → F)) := by
    filter_upwards [(ae_restrict_iff' Omega.isOpen.measurableSet).1 hf] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK]
    · rw [indicator_of_notMem hxK]
      by_cases hxO : x ∈ (Omega : Set E)
      · rw [indicator_of_mem hxO, hx hxO hxK]
      · exact indicator_of_notMem hxO _
  rw [bumpField, convolution_congr _ (EventuallyEq.refl _ _) hae]
  refine Function.notMem_support.1 fun hmem => hy ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := support_convolution_subset _ hmem
  rw [ContDiffBump.support_normed_eq] at ha
  have hbK : b ∈ K := support_indicator_subset hb
  exact ⟨b, hbK, a, ball_subset_closedBall ha, add_comm b a⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- The set of points where the mollified field may be nonzero is compact. -/
private theorem isCompact_add_closedBall {K : Set E} (hK : IsCompact K) (r : ℝ) :
    IsCompact (K + closedBall (0 : E) r) :=
  hK.add (isCompact_closedBall 0 r)

omit [MeasurableSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A ball around `y` missing `K` means that `y` is not in `K + closedBall 0 r`. -/
private theorem notMem_add_closedBall_of_disjoint {K : Set E} {y : E} {r : ℝ}
    (hy : Disjoint (closedBall y r) K) : y ∉ K + closedBall (0 : E) r := by
  rintro ⟨b, hb, a, ha, rfl⟩
  refine hy.notMem_of_mem_left ?_ hb
  rw [mem_closedBall, dist_eq_norm]
  simpa [norm_neg] using ha

/-- The translated mollification of the value of `u`, as a test function on the whole space. -/
private def shiftTest (phi : ContDiffBump (0 : E)) (h : E) {K : Set E} (hK : IsCompact K)
    (k : ℕ) (u : Wkp mu Omega p k)
    (hu : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → value k u x = 0) : 𝓓((⊤ : Opens E), ℝ) :=
  ⟨fun x => bumpField phi (value k u) (x + h),
    (contDiff_bumpField phi _).comp (contDiff_id.add contDiff_const),
    HasCompactSupport.intro
      ((Homeomorph.addRight h).isCompact_preimage.2 (isCompact_add_closedBall hK phi.rOut))
      fun _ hx => bumpField_eq_zero phi (value k u) hu hx,
    subset_univ _⟩

private theorem shiftTest_apply (phi : ContDiffBump (0 : E)) (h : E) {K : Set E}
    (hK : IsCompact K) (k : ℕ) (u : Wkp mu Omega p k)
    (hu : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → value k u x = 0) (x : E) :
    shiftTest phi h hK k u hu x = bumpField phi (value k u) (x + h) :=
  rfl

private theorem shiftTest_lowerOrder (phi : ContDiffBump (0 : E)) (h : E) {K : Set E}
    (hK : IsCompact K) (k : ℕ) (u : Wkp mu Omega p (k + 1))
    (hu : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → value (k + 1) u x = 0)
    (hu' : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → value k (lowerOrder k u) x = 0) :
    shiftTest phi h hK k (lowerOrder k u) hu' = shiftTest phi h hK (k + 1) u hu := by
  ext x
  simp only [shiftTest_apply, value_succ]

/-- Every iterated weak derivative of a function vanishing off a closed set vanishes off it. -/
private theorem iteratedGradient_ae_eq_zero_of_isClosed {K : Set E} (hK : IsClosed K) (k : ℕ)
    (u : Wkp mu Omega p (k + 1))
    (hu : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → value (k + 1) u x = 0) :
    ∀ᵐ x ∂mu.restrict Omega, x ∉ K → iteratedGradient k u x = 0 :=
  iteratedGradient_ae_eq_zero_of_value_ae_eq_zero_of_isOpen k u hK.isOpen_compl hu

/-- The ball condition: for every point of `Ω`, the translated bump ball either stays inside
`Ω` or misses `K`. -/
private def BallCondition (Omega : Opens E) (K : Set E) (phi : ContDiffBump (0 : E)) (h : E) :
    Prop :=
  ∀ x ∈ Omega, closedBall (x + h) phi.rOut ⊆ Omega ∨ Disjoint (closedBall (x + h) phi.rOut) K

omit [Fact (1 ≤ p)] in
/-- Near a point whose translated bump ball misses `K`, the translated field vanishes. -/
private theorem shifted_bumpField_eventuallyEq_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (phi : ContDiffBump (0 : E)) (h : E) {K : Set E} (hK : IsCompact K)
    (f : Lp F p (mu.restrict Omega)) (hf : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → f x = 0) {x : E}
    (hx : Disjoint (closedBall (x + h) phi.rOut) K) :
    (fun y => bumpField phi f (y + h)) =ᶠ[𝓝 x] fun _ => 0 := by
  have hopen : IsOpen ((fun y => y + h) ⁻¹' (K + closedBall (0 : E) phi.rOut)ᶜ) :=
    ((isCompact_add_closedBall hK phi.rOut).isClosed.isOpen_compl).preimage
      (continuous_id.add continuous_const)
  filter_upwards [hopen.mem_nhds (notMem_add_closedBall_of_disjoint hx)] with y hy
  exact bumpField_eq_zero phi f hf hy

private theorem gradient_shifted_bumpField (phi : ContDiffBump (0 : E)) (h : E) {K : Set E}
    (hK : IsCompact K) (u : Wkp mu Omega p 1)
    (hu : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → value 1 u x = 0) {x : E}
    (hx : closedBall (x + h) phi.rOut ⊆ Omega ∨ Disjoint (closedBall (x + h) phi.rOut) K) :
    gradient (fun y => bumpField phi (value 1 u) (y + h)) x =
      bumpField phi (iteratedGradient 0 u) (x + h) := by
  rcases hx with hx | hx
  · have hcomp : gradient (fun y => bumpField phi (value 1 u) (y + h)) x =
        gradient (bumpField phi (value 1 u)) (x + h) := by
      simp only [gradient, fderiv_comp_add_right]
    rw [hcomp]
    apply (InnerProductSpace.toDual ℝ E).injective
    rw [toDual_gradient]
    have hd := fderiv_indicator_convolution_normed_value u phi (x + h) hx
    rw [convolution_flip, convolution_flip] at hd
    rw [bumpField, hd]
    have hmem := (memLp_indicator_iff_restrict Omega.isOpen.measurableSet.nullMeasurableSet).2
      (Lp.memLp (iteratedGradient 0 u))
    have hi := (phi.hasCompactSupport_normed (μ := mu)).convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ) phi.continuous_normed (hmem.locallyIntegrable Fact.out)
      (x + h)
    -- Passing the Riesz map through the integral identifies the vector convolution's dual.
    symm
    rw [bumpField, convolution_def]
    refine ((InnerProductSpace.toDual ℝ E).toLinearIsometry.toContinuousLinearMap
      |>.integral_comp_comm hi).symm.trans ?_
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : x + h - y ∈ Omega <;> simp [hy, ContinuousLinearMap.lsmul_apply]
  · rw [(shifted_bumpField_eventuallyEq_zero phi h hK (value 1 u) hu hx).gradient_eq,
      gradient_fun_const,
      bumpField_eq_zero phi _ (iteratedGradient_ae_eq_zero_of_isClosed hK.isClosed 0 u hu)
        (notMem_add_closedBall_of_disjoint hx)]

private theorem fderiv_shifted_bumpField (phi : ContDiffBump (0 : E)) (h : E) {K : Set E}
    (hK : IsCompact K) (k : ℕ) (u : Wkp mu Omega p (k + 2))
    (hu : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → value (k + 2) u x = 0) {x : E}
    (hx : closedBall (x + h) phi.rOut ⊆ Omega ∨ Disjoint (closedBall (x + h) phi.rOut) K) :
    fderiv ℝ (fun y => bumpField phi (iteratedGradient k (lowerOrder (k + 1) u)) (y + h)) x =
      bumpField phi (iteratedGradient (k + 1) u) (x + h) := by
  rcases hx with hx | hx
  · rw [fderiv_comp_add_right]
    simpa only [bumpField, convolution_flip] using
      fderiv_indicator_convolution_normed_iteratedGradient k u phi (x + h) hx
  · have hlow : ∀ᵐ x ∂mu.restrict Omega, x ∉ K →
        value (k + 1) (lowerOrder (k + 1) u) x = 0 := by
      simpa only [value_succ] using hu
    rw [(shifted_bumpField_eventuallyEq_zero phi h hK _
        (iteratedGradient_ae_eq_zero_of_isClosed hK.isClosed k _ hlow) hx).fderiv_eq,
      fderiv_const_apply,
      bumpField_eq_zero phi _
        (iteratedGradient_ae_eq_zero_of_isClosed hK.isClosed (k + 1) u hu)
        (notMem_add_closedBall_of_disjoint hx)]

/-- On `Ω`, the classical derivative fields of the shifted test function are the shifted
mollifications of the weak derivative fields. -/
private theorem iteratedGradient_shiftTest (phi : ContDiffBump (0 : E)) (h : E) {K : Set E}
    (hK : IsCompact K) (hball : BallCondition Omega K phi h) :
    ∀ (k : ℕ) (u : Wkp mu Omega p (k + 1))
      (hu : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → value (k + 1) u x = 0) (x : E), x ∈ Omega →
      iteratedGradientTestFunction (shiftTest phi h hK (k + 1) u hu) k x =
        bumpField phi (iteratedGradient k u) (x + h) := by
  intro k
  induction k with
  | zero =>
      intro u hu x hx
      simp only [iteratedGradientTestFunction_zero]
      exact gradient_shifted_bumpField phi h hK u hu (hball x hx)
  | succ k ih =>
      intro u hu x hx
      have hlow : ∀ᵐ x ∂mu.restrict Omega, x ∉ K →
          value (k + 1) (lowerOrder (k + 1) u) x = 0 := by
        simpa only [value_succ] using hu
      rw [iteratedGradientTestFunction_succ,
        ← shiftTest_lowerOrder phi h hK (k + 1) u hu hlow]
      have heq : iteratedGradientTestFunction
          (shiftTest phi h hK (k + 1) (lowerOrder (k + 1) u) hlow) k =ᶠ[𝓝 x]
          fun y => bumpField phi (iteratedGradient k (lowerOrder (k + 1) u)) (y + h) := by
        filter_upwards [Omega.isOpen.mem_nhds hx] with y hy using ih _ hlow y hy
      rw [heq.fderiv_eq]
      exact fderiv_shifted_bumpField phi h hK k u hu (hball x hx)

/-- The `Lᵖ(Ω)` class of a translated mollified zero extension. -/
private def shiftAverage {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) (h : E)
    (f : Lp F p (mu.restrict Omega)) : Lp F p (mu.restrict Omega) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
    simpa only [one_smul] using Measure.restrict_mono_set mu (subset_univ (Omega : Set E)))
      ((mu.restrict (univ : Set E)).translateLp p h
        (normedBumpLp hp phi (mu.restrict univ)
          (extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (subset_univ _) f)))

private theorem shiftAverage_ae {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) (h : E)
    (f : Lp F p (mu.restrict Omega)) :
    shiftAverage hp phi h f =ᵐ[mu.restrict Omega] fun x => bumpField phi f (x + h) := by
  have he := normedBumpLp_extendByZero_ae_eq_convolution hp phi Omega.isOpen.measurableSet f
  have hshift := (Measure.coeFn_translateLp (mu := mu.restrict (univ : Set E)) (p := p) h
    (normedBumpLp hp phi (mu.restrict univ)
      (extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (subset_univ _) f))).trans
    ((measurePreserving_add_right (mu.restrict (univ : Set E)) h).quasiMeasurePreserving.ae_eq_comp
      he)
  have hshift' := hshift.filter_mono
    (ae_mono (Measure.restrict_mono_set mu (subset_univ (Omega : Set E))))
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _).trans (by
    simpa only [Measure.restrict_univ, bumpField, Function.comp_def] using hshift')

/-- Translations by vectors tending to zero of `Lᵖ` classes converging to `g` converge to `g`. -/
private theorem tendsto_translateLp_of_tendsto {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hp : p ≠ ∞) {I : Type*} {l : Filter I} {h : I → E}
    (hh : Tendsto h l (𝓝 0)) {A : I → Lp F p (mu.restrict (univ : Set E))}
    {g : Lp F p (mu.restrict (univ : Set E))} (hA : Tendsto A l (𝓝 g)) :
    Tendsto (fun i => (mu.restrict (univ : Set E)).translateLp p (h i) (A i)) l (𝓝 g) := by
  have htr : Tendsto (fun i => (mu.restrict (univ : Set E)).translateLp p (h i) g) l (𝓝 g) := by
    simpa only [Measure.translateLp_zero, Function.comp_def] using
      ((Measure.continuous_translateLp hp g).tendsto 0).comp hh
  rw [tendsto_iff_dist_tendsto_zero] at hA htr ⊢
  refine squeeze_zero (fun _ => dist_nonneg) (fun i => ?_) (by simpa using hA.add htr)
  calc dist ((mu.restrict (univ : Set E)).translateLp p (h i) (A i)) g
      ≤ dist ((mu.restrict (univ : Set E)).translateLp p (h i) (A i))
          ((mu.restrict (univ : Set E)).translateLp p (h i) g) +
        dist ((mu.restrict (univ : Set E)).translateLp p (h i) g) g := dist_triangle _ _ _
    _ = dist (A i) g + dist ((mu.restrict (univ : Set E)).translateLp p (h i) g) g := by
      rw [LinearIsometryEquiv.dist_map]

private theorem tendsto_shiftAverage {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (hp : p ≠ ∞) {I : Type*} {l : Filter I} {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i => (phi i).rOut) l (𝓝 0)) {h : I → E} (hh : Tendsto h l (𝓝 0))
    (f : Lp F p (mu.restrict Omega)) :
    Tendsto (fun i => shiftAverage hp (phi i) (h i) f) l (𝓝 f) := by
  let r : Lp F p (mu.restrict (univ : Set E)) →L[ℝ] Lp F p (mu.restrict Omega) :=
    Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
      simpa only [one_smul] using Measure.restrict_mono_set mu (subset_univ (Omega : Set E)))
  let e : Lp F p (mu.restrict Omega) →ₗᵢ[ℝ] Lp F p (mu.restrict (univ : Set E)) :=
    extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (subset_univ _)
  have hlimit := (r.continuous.tendsto (e f)).comp
    (tendsto_translateLp_of_tendsto hp hh (tendsto_normedBumpLp hp hphi (e f)))
  have hre : r (e f) = f := by
    apply Lp.ext
    exact (Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _).trans
      (coeFn_extendByZeroLpₗᵢ_restrict ℝ Omega.isOpen.measurableSet (subset_univ _) f)
  rw [hre] at hlimit
  exact hlimit

private theorem value_restrictL_shiftTest (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) (h : E)
    {K : Set E} (hK : IsCompact K) (k : ℕ) (u : Wkp mu Omega p k)
    (hu : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → value k u x = 0) :
    value k (restrictL (le_top : Omega ≤ ⊤) k
      (ofTestFunctionₗ (mu := mu) (p := p) k (shiftTest phi h hK k u hu))) =
        shiftAverage hp phi h (value k u) := by
  apply Lp.ext
  filter_upwards [value_restrictL_ofTestFunctionₗ_ae (mu := mu) (p := p) (le_top : Omega ≤ ⊤) k
      (shiftTest phi h hK k u hu), shiftAverage_ae hp phi h (value k u)] with x hr ha
  rw [hr, ha, shiftTest_apply]

private theorem iteratedGradient_restrictL_shiftTest (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (h : E) {K : Set E} (hK : IsCompact K) (hball : BallCondition Omega K phi h) (k : ℕ)
    (u : Wkp mu Omega p (k + 1))
    (hu : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → value (k + 1) u x = 0) :
    iteratedGradient k (restrictL (le_top : Omega ≤ ⊤) (k + 1)
      (ofTestFunctionₗ (mu := mu) (p := p) (k + 1) (shiftTest phi h hK (k + 1) u hu))) =
        shiftAverage hp phi h (iteratedGradient k u) := by
  apply Lp.ext
  filter_upwards [iteratedGradient_restrictL_ae (le_top : Omega ≤ ⊤) k
      (ofTestFunctionₗ (mu := mu) (p := p) (k + 1) (shiftTest phi h hK (k + 1) u hu)),
    iteratedGradientTestFunctionLp_apply_ae (mu := mu) p k
      (shiftTest phi h hK (k + 1) u hu) |>.filter_mono
        (ae_mono (Measure.restrict_mono_set mu (subset_univ (Omega : Set E)))),
    shiftAverage_ae hp phi h (iteratedGradient k u),
    ae_restrict_mem Omega.isOpen.measurableSet] with x hr ht ha hx
  have ht' : iteratedGradientTestFunctionLp (mu := mu) p k (shiftTest phi h hK (k + 1) u hu) x =
      iteratedGradientTestFunction (shiftTest phi h hK (k + 1) u hu) k x := by
    simpa only [Opens.coe_top] using ht
  rw [hr, iteratedGradient_ofTestFunctionₗ, ht', ha]
  exact iteratedGradient_shiftTest phi h hK hball k u hu x hx

private theorem tendsto_restrictL_shiftTest (hp : p ≠ ∞) {K : Set E} (hK : IsCompact K)
    {I : Type*} {l : Filter I} {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i => (phi i).rOut) l (𝓝 0)) {h : I → E} (hh : Tendsto h l (𝓝 0))
    (hball : ∀ i, BallCondition Omega K (phi i) (h i)) :
    ∀ (k : ℕ) (u : Wkp mu Omega p k)
      (hu : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → value k u x = 0),
      Tendsto (fun i => restrictL (le_top : Omega ≤ ⊤) k
        (ofTestFunctionₗ (mu := mu) (p := p) k (shiftTest (phi i) (h i) hK k u hu)))
        l (𝓝 u) := by
  intro k
  -- Orders zero and one use convergence of the value and gradient in `Lᵖ`; successive
  -- orders use the two components of the closed weak-derivative graph.
  induction k using Nat.twoStepInduction with
  | zero =>
      intro u hu
      have h' := tendsto_shiftAverage hp hphi hh (value 0 u)
      simp only [value_zero] at h'
      convert h' using 1
      funext i
      simpa only [value_zero] using value_restrictL_shiftTest hp (phi i) (h i) hK 0 u hu
  | one =>
      intro u hu
      refine W1p.tendsto_iff_value_gradient.2 ⟨?_, ?_⟩
      · have h' := tendsto_shiftAverage hp hphi hh (value 1 u)
        simp only [value_one] at h'
        convert h' using 1
        funext i
        simpa only [value_one] using value_restrictL_shiftTest hp (phi i) (h i) hK 1 u hu
      · have h' := tendsto_shiftAverage hp hphi hh (iteratedGradient 0 u)
        simp only [iteratedGradient_zero] at h'
        convert h' using 1
        funext i
        simpa only [iteratedGradient_zero] using
          iteratedGradient_restrictL_shiftTest hp (phi i) (h i) hK (hball i) 0 u hu
  | more k _ ih =>
      intro u hu
      have hlow : ∀ᵐ x ∂mu.restrict Omega, x ∉ K →
          value (k + 1) (lowerOrder (k + 1) u) x = 0 := by
        simpa only [value_succ] using hu
      rw [tendsto_iff_lowerOrder_iteratedGradient (k + 1)]
      constructor
      · have h' := ih (lowerOrder (k + 1) u) hlow
        simp_rw [shiftTest_lowerOrder _ _ hK (k + 1) u hu hlow] at h'
        convert h' using 1
        funext i
        rw [lowerOrder_restrictL, lowerOrder_ofTestFunctionₗ]
      · have h' := tendsto_shiftAverage hp hphi hh (iteratedGradient (k + 1) u)
        simpa only [← iteratedGradient_restrictL_shiftTest hp _ _ hK (hball _) (k + 1) u hu]
          using h'

/-- **Shifted mollification up to the boundary.** Let `1 ≤ p < ∞` and let `u ∈ W^{k,p}(Ω)`
vanish almost everywhere off a compact set `K`. Suppose that translations `h i → 0` and bumps
`φ i` with radii tending to zero satisfy, for every `x ∈ Ω`, that `closedBall (x + h i) (r i)`
either lies in `Ω` or misses `K`. Then `u` is a `W^{k,p}(Ω)`-limit of restrictions to `Ω` of test
functions on the whole space.

The approximants are `x ↦ (φ i ⋆ 1_Ω u) (x + h i)`. The ball condition ensures that their
classical derivatives on `Ω` are the translated mollifications of the weak derivatives of `u`. -/
theorem mem_closure_range_restrictL_ofTestFunctionₗ_top_of_shift (hp : p ≠ ∞) {K : Set E}
    (hK : IsCompact K) {I : Type*} {l : Filter I} [l.NeBot] {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i => (phi i).rOut) l (𝓝 0)) {h : I → E} (hh : Tendsto h l (𝓝 0))
    (hball : ∀ i, ∀ x ∈ Omega, closedBall (x + h i) (phi i).rOut ⊆ Omega ∨
      Disjoint (closedBall (x + h i) (phi i).rOut) K)
    (k : ℕ) (u : Wkp mu Omega p k) (hu : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → value k u x = 0) :
    u ∈ closure (range fun psi : 𝓓((⊤ : Opens E), ℝ) =>
      restrictL (le_top : Omega ≤ ⊤) k (ofTestFunctionₗ (mu := mu) (p := p) k psi)) :=
  mem_closure_of_tendsto (tendsto_restrictL_shiftTest hp hK hphi hh hball k u hu)
    (Eventually.of_forall fun _ => ⟨_, rfl⟩)

end TauCeti.Wkp
