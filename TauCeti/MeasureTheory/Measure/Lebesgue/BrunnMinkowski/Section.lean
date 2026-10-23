/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.Analysis.Convex.Prod
public import TauCeti.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Basic
public import TauCeti.MeasureTheory.Measure.Lebesgue.OrthogonalSlices

/-!
# Brunn's concavity principle

Let `s ⊆ P × F` be convex, where `F` is a finite-dimensional real inner product space of
dimension `m`. A weighted sum of two fibers of `s` lies in the fiber over the weighted base
point, so the Brunn–Minkowski inequality in `F` shows that the dimension root of the fiber
volume, `p ↦ volume (Prod.mk p ⁻¹' s) ^ (1 / m)`, is concave on the projection `Prod.fst '' s`.
This is **Brunn's concavity principle**. When the fibers have finite volume, a concave function
on a finite-dimensional base is continuous on the interior of its domain, hence so is the fiber
volume itself.

The main specialization concerns the hyperplane sections `{y ∈ (ℝ ∙ e)ᗮ | y + t • e ∈ s}` of a
convex set `s` in a Euclidean space of dimension `n`, along a unit vector `e`. Their volume,
raised to the power `1 / (n - 1)`, is concave in `t` on the interval `⟪e, s⟫`. For a bounded
Borel convex set, the volume of the part `{x ∈ s | ⟪e, x⟫ ≤ c}` below a hyperplane is the
integral of the section volumes up to height `c`, and the continuity of the sections shows that
it is differentiable, with derivative the section volume, at every interior height. These are
the inputs for the classical analysis of equality cases in the Brunn–Minkowski inequality for
convex bodies, which compares the volume distributions of two bodies along each direction.

No dimension assumption is made. In a zero-dimensional fiber space every nonempty fiber is the
whole space and the dimension root is the constant `1` on the projection, so concavity and
continuity hold trivially.

## Main results

* `Convex.concaveOn_volume_real_preimage_prodMk_rpow`: Brunn's concavity principle for fibers.
* `Convex.continuousOn_volume_real_preimage_prodMk`: continuity of fiber volumes on the interior
  of the projection.
* `Convex.concaveOn_volume_real_hyperplaneSection_rpow`: concavity of hyperplane sections.
* `Convex.continuousOn_volume_real_hyperplaneSection`: continuity of hyperplane sections.
* `Convex.hasDerivAt_volume_real_sep_inner_le`: the volume below a hyperplane has the section
  volume as derivative.
* `TauCeti.volume_hyperplaneSection_rpow_mul_volume_hyperplaneSection_rpow_le`: multiplicative
  Brunn–Minkowski for the hyperplane sections of two sets, at the weighted height.

## References

* R. J. Gardner, *The Brunn–Minkowski inequality*, Bull. Amer. Math. Soc. **39** (2002),
  355–405, Section 4, for Brunn's concavity principle as a consequence of the Brunn–Minkowski
  inequality.
* R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, 2nd ed., Cambridge University
  Press, 2014, Section 7.1.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise RealInnerProductSpace

section Fiber

variable {P F : Type*} [AddCommGroup P] [Module ℝ P]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **Brunn's concavity principle**, extended form: the dimension root of the fiber volume of
a convex set is concave along segments joining points with nonempty fibers. Fibers may have
infinite volume, and no dimension assumption is needed. -/
theorem Convex.mul_volume_preimage_prodMk_rpow_add_mul_volume_preimage_prodMk_rpow_le
    {s : Set (P × F)} (hs : Convex ℝ s) {p q : P} (hp : (Prod.mk p ⁻¹' s).Nonempty)
    (hq : (Prod.mk q ⁻¹' s).Nonempty) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ENNReal.ofReal a * volume (Prod.mk p ⁻¹' s) ^ (Module.finrank ℝ F : ℝ)⁻¹ +
      ENNReal.ofReal b * volume (Prod.mk q ⁻¹' s) ^ (Module.finrank ℝ F : ℝ)⁻¹ ≤
        volume (Prod.mk (a • p + b • q) ⁻¹' s) ^ (Module.finrank ℝ F : ℝ)⁻¹ := by
  have hsub := hs.smul_preimage_prodMk_add_smul_preimage_prodMk_subset p q ha hb hab
  rcases eq_or_ne (Module.finrank ℝ F) 0 with hn | hn
  · -- In dimension zero every dimension root is `1`, so the claim is `a + b ≤ 1`.
    simp [hn, ← ENNReal.ofReal_add ha hb, hab]
  · exact (TauCeti.mul_volume_rpow_add_mul_volume_rpow_le hn hp
      (Convex.nullMeasurableSet volume (hs.preimage_prodMk p)) hq
      (Convex.nullMeasurableSet volume (hs.preimage_prodMk q)) ha hb).trans
      (ENNReal.rpow_le_rpow (measure_mono hsub) (by positivity))

/-- **Brunn's concavity principle**: if every fiber of a convex set has finite volume, the
dimension root of the fiber volume is concave on the projection of the set. -/
theorem Convex.concaveOn_volume_real_preimage_prodMk_rpow {s : Set (P × F)} (hs : Convex ℝ s)
    (hfin : ∀ p, volume (Prod.mk p ⁻¹' s) ≠ ∞) :
    ConcaveOn ℝ (Prod.fst '' s)
      (fun p ↦ volume.real (Prod.mk p ⁻¹' s) ^ (Module.finrank ℝ F : ℝ)⁻¹) := by
  refine ⟨hs.linear_image (LinearMap.fst ℝ P F), ?_⟩
  rintro _ ⟨⟨p, y⟩, hy, rfl⟩ _ ⟨⟨q, z⟩, hz, rfl⟩ a b ha hb hab
  have hr : (0 : ℝ) ≤ (Module.finrank ℝ F : ℝ)⁻¹ := by positivity
  have h := ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg hr (hfin _))
    (hs.mul_volume_preimage_prodMk_rpow_add_mul_volume_preimage_prodMk_rpow_le
      ⟨y, hy⟩ ⟨z, hz⟩ ha hb hab)
  rwa [ENNReal.toReal_add (by finiteness [ENNReal.rpow_ne_top_of_nonneg hr (hfin p)])
      (by finiteness [ENNReal.rpow_ne_top_of_nonneg hr (hfin q)]),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb,
    ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at h

end Fiber

section FiberContinuous

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- If every fiber of a convex set has finite volume, the fiber volume is continuous on the
interior of the projection of the set. This follows from Brunn's concavity principle. -/
theorem Convex.continuousOn_volume_real_preimage_prodMk {s : Set (P × F)} (hs : Convex ℝ s)
    (hfin : ∀ p, volume (Prod.mk p ⁻¹' s) ≠ ∞) :
    ContinuousOn (fun p ↦ volume.real (Prod.mk p ⁻¹' s)) (interior (Prod.fst '' s)) := by
  rcases eq_or_ne (Module.finrank ℝ F) 0 with hn | hn
  · -- In dimension zero every nonempty fiber is the whole space.
    have : Subsingleton F := Module.finrank_zero_iff.1 hn
    refine continuousOn_const (c := volume.real (univ : Set F)).congr fun p hp ↦ ?_
    obtain ⟨⟨p, y⟩, hy, rfl⟩ := interior_subset hp
    rw [(Subsingleton.eq_univ_of_nonempty ⟨y, hy⟩ : Prod.mk p ⁻¹' s = univ)]
  · refine ((hs.concaveOn_volume_real_preimage_prodMk_rpow hfin).continuousOn_interior.pow
      (Module.finrank ℝ F)).congr fun p _ ↦ ?_
    exact (Real.rpow_inv_natCast_pow ENNReal.toReal_nonneg hn).symm

end FiberContinuous

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The hyperplane sections of `s` along `e`, as fibers of a subset of `ℝ × (ℝ ∙ e)ᗮ`. -/
private def hyperplaneFibers (e : E) (s : Set E) : Set (ℝ × (ℝ ∙ e)ᗮ) :=
  {z | (z.2 : E) + z.1 • e ∈ s}

private theorem convex_hyperplaneFibers (e : E) {s : Set E} (hs : Convex ℝ s) :
    Convex ℝ (hyperplaneFibers e s) := by
  convert hs.linear_preimage ((ℝ ∙ e)ᗮ.subtype ∘ₗ LinearMap.snd ℝ ℝ (ℝ ∙ e)ᗮ +
    (LinearMap.fst ℝ ℝ (ℝ ∙ e)ᗮ).smulRight e) using 1
  ext z
  simp [hyperplaneFibers]

/-- Along a unit vector, the heights with a nonempty hyperplane section are the values of the
inner product on the set. -/
private theorem fst_image_hyperplaneFibers (e : E) (he : ‖e‖ = 1) (s : Set E) :
    Prod.fst '' hyperplaneFibers e s = (fun x ↦ ⟪e, x⟫) '' s := by
  ext t
  constructor
  · rintro ⟨⟨t, y⟩, hy, rfl⟩
    exact ⟨_, hy, inner_add_smul e he y t⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(⟪e, x⟫, ((orthogonalLineEquiv e he).symm x).1), ?_, rfl⟩
    simpa [hyperplaneFibers, orthogonalLineEquiv_symm_fst] using hx

/-- A weighted sum of hyperplane sections of two sets lies in the hyperplane section of their
weighted sum, at the weighted height. -/
theorem smul_hyperplaneSection_add_smul_hyperplaneSection_subset (e : E) (K L : Set E)
    (a b s t : ℝ) :
    a • {y : (ℝ ∙ e)ᗮ | (y : E) + s • e ∈ K} + b • {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ L} ⊆
      {y : (ℝ ∙ e)ᗮ | (y : E) + (a * s + b * t) • e ∈ a • K + b • L} := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩
  refine ⟨a • ((y : E) + s • e), smul_mem_smul_set hy, b • ((z : E) + t • e),
    smul_mem_smul_set hz, ?_⟩
  simp only [Submodule.coe_add, Submodule.coe_smul, smul_add, add_smul, smul_smul]
  abel

variable [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

/-- **Brunn's concavity principle** for hyperplane sections, extended form. Along a unit vector
`e` in a space of dimension `n`, the `(n - 1)`-th root of the section volume of a convex set is
concave on the heights at which the section is nonempty. -/
theorem _root_.Convex.mul_volume_hyperplaneSection_rpow_add_mul_volume_hyperplaneSection_rpow_le
    {s : Set E} (hs : Convex ℝ s) {e : E} (he : ‖e‖ = 1) {t u : ℝ}
    (ht : t ∈ (fun x ↦ ⟪e, x⟫) '' s) (hu : u ∈ (fun x ↦ ⟪e, x⟫) '' s)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ENNReal.ofReal a * volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s} ^
        ((Module.finrank ℝ E - 1 : ℕ) : ℝ)⁻¹ +
      ENNReal.ofReal b * volume {y : (ℝ ∙ e)ᗮ | (y : E) + u • e ∈ s} ^
        ((Module.finrank ℝ E - 1 : ℕ) : ℝ)⁻¹ ≤
        volume {y : (ℝ ∙ e)ᗮ | (y : E) + (a * t + b * u) • e ∈ s} ^
          ((Module.finrank ℝ E - 1 : ℕ) : ℝ)⁻¹ := by
  rw [← fst_image_hyperplaneFibers e he] at ht hu
  obtain ⟨⟨t, y⟩, hy, rfl⟩ := ht
  obtain ⟨⟨u, z⟩, hz, rfl⟩ := hu
  rw [← Submodule.finrank_orthogonal_span_singleton_eq_finrank_sub_one
    (norm_ne_zero_iff.1 (he ▸ one_ne_zero))]
  exact Convex.mul_volume_preimage_prodMk_rpow_add_mul_volume_preimage_prodMk_rpow_le
    (convex_hyperplaneFibers e hs) ⟨y, hy⟩ ⟨z, hz⟩ ha hb hab

/-- **Brunn's concavity principle** for hyperplane sections. If the hyperplane sections of a
convex set along a unit vector `e` have finite volume, then in a space of dimension `n` the
`(n - 1)`-th root of their volume is concave on the interval `⟪e, s⟫`. -/
theorem _root_.Convex.concaveOn_volume_real_hyperplaneSection_rpow {s : Set E} (hs : Convex ℝ s)
    {e : E} (he : ‖e‖ = 1) (hfin : ∀ t : ℝ, volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s} ≠ ∞) :
    ConcaveOn ℝ ((fun x ↦ ⟪e, x⟫) '' s) (fun t : ℝ ↦
      volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s} ^
        ((Module.finrank ℝ E - 1 : ℕ) : ℝ)⁻¹) := by
  rw [← fst_image_hyperplaneFibers e he,
    ← Submodule.finrank_orthogonal_span_singleton_eq_finrank_sub_one
      (norm_ne_zero_iff.1 (he ▸ one_ne_zero))]
  exact (convex_hyperplaneFibers e hs).concaveOn_volume_real_preimage_prodMk_rpow hfin

/-- If the hyperplane sections of a convex set along a unit vector have finite volume, their
volume is continuous on the interior of the interval `⟪e, s⟫`. -/
theorem _root_.Convex.continuousOn_volume_real_hyperplaneSection {s : Set E} (hs : Convex ℝ s)
    {e : E} (he : ‖e‖ = 1) (hfin : ∀ t : ℝ, volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s} ≠ ∞) :
    ContinuousOn (fun t : ℝ ↦ volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s})
      (interior ((fun x ↦ ⟪e, x⟫) '' s)) := by
  rw [← fst_image_hyperplaneFibers e he]
  exact (convex_hyperplaneFibers e hs).continuousOn_volume_real_preimage_prodMk hfin

/-- For a bounded Borel convex set, the volume of the part below the hyperplane `⟪e, x⟫ = c` is
differentiable in `c` at every height interior to `⟪e, s⟫`, and its derivative is the volume of
the hyperplane section at height `c`. -/
theorem _root_.Convex.hasDerivAt_volume_real_sep_inner_le {s : Set E} (hs : Convex ℝ s)
    (hsb : Bornology.IsBounded s) (hsm : MeasurableSet s) {e : E} (he : ‖e‖ = 1) {c : ℝ}
    (hc : c ∈ interior ((fun x ↦ ⟪e, x⟫) '' s)) :
    HasDerivAt (fun c ↦ volume.real {x ∈ s | ⟪e, x⟫ ≤ c})
      (volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + c • e ∈ s}) c := by
  set φ : ℝ → ℝ := fun t ↦ volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s}
  have hfin (t : ℝ) := (hsb.volume_hyperplaneSection_lt_top e t).ne
  have hm := measurable_volume_hyperplaneSection e he hsm
  -- `φ` is integrable since its integral is the volume of `s`.
  have hφi : Integrable φ := integrable_toReal_of_lintegral_ne_top hm.aemeasurable (by
    rw [← volume_eq_lintegral_volume_hyperplaneSection e he hsm.nullMeasurableSet]
    exact hsb.measure_lt_top.ne)
  -- Choose a height `a < c` below `s`; near `c` the volume below `c'` is an interval integral.
  obtain ⟨m, hmin⟩ := ((innerSL ℝ e).lipschitzWith.isBounded_image hsb).bddBelow
  set a := min m c - 1
  have ha (x : E) (hx : x ∈ s) : a < ⟪e, x⟫ :=
    (sub_one_lt _).trans_le ((min_le_left _ _).trans (hmin ⟨x, hx, rfl⟩))
  have hvol : ∀ᶠ c' in nhds c, volume.real {x ∈ s | ⟪e, x⟫ ≤ c'} = ∫ t in a..c', φ t := by
    filter_upwards [lt_mem_nhds ((sub_one_lt _).trans_le (min_le_right m c))] with c' hc'
    have hsep : {x ∈ s | ⟪e, x⟫ ≤ c'} = {x ∈ s | ⟪e, x⟫ ∈ Ioc a c'} := by
      ext x
      exact and_congr_right fun hx ↦ ⟨fun h ↦ ⟨ha x hx, h⟩, And.right⟩
    have hlin : ∫⁻ t in Ioc a c', volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s} =
        ENNReal.ofReal (∫ t in Ioc a c', φ t) := by
      rw [ofReal_integral_eq_lintegral_ofReal hφi.integrableOn
        (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg)]
      exact setLIntegral_congr_fun measurableSet_Ioc fun t _ ↦
        (ENNReal.ofReal_toReal (hfin t)).symm
    rw [intervalIntegral.integral_of_le hc'.le, measureReal_def, hsep,
      volume_sep_inner_mem_eq_setLIntegral e he hsm.nullMeasurableSet measurableSet_Ioc, hlin]
    exact ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioc
      fun _ _ ↦ ENNReal.toReal_nonneg)
  -- By Brunn's concavity principle `φ` is continuous at the interior height `c`.
  have hcont : ContinuousAt φ c :=
    (hs.continuousOn_volume_real_hyperplaneSection he hfin).continuousAt
      (isOpen_interior.mem_nhds hc)
  exact (intervalIntegral.integral_hasDerivAt_right hφi.intervalIntegrable
    hm.ennreal_toReal.stronglyMeasurable.stronglyMeasurableAtFilter hcont).congr_of_eventuallyEq
    hvol

/-- **Multiplicative Brunn–Minkowski for hyperplane sections.** The weighted geometric mean of the
volumes of a section of `K` and a section of `L` is at most the volume of the section of
`(1 - θ) • K + θ • L` at the weighted height. -/
theorem volume_hyperplaneSection_rpow_mul_volume_hyperplaneSection_rpow_le (e : E) {K L : Set E}
    (hK : MeasurableSet K) (hL : MeasurableSet L) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (s t : ℝ) :
    volume {y : (ℝ ∙ e)ᗮ | (y : E) + s • e ∈ K} ^ (1 - θ) *
        volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ L} ^ θ ≤
      volume {y : (ℝ ∙ e)ᗮ | (y : E) + ((1 - θ) * s + θ * t) • e ∈ (1 - θ) • K + θ • L} := by
  have hsec {u : ℝ} {S : Set E} (hS : MeasurableSet S) :
      MeasurableSet {y : (ℝ ∙ e)ᗮ | (y : E) + u • e ∈ S} :=
    hS.preimage (continuous_subtype_val.add continuous_const).measurable
  exact (volume_rpow_mul_volume_rpow_le (hsec hK).nullMeasurableSet (hsec hL).nullMeasurableSet
    hθ₀ hθ₁).trans (measure_mono
      (smul_hyperplaneSection_add_smul_hyperplaneSection_subset e K L (1 - θ) θ s t))

end TauCeti
