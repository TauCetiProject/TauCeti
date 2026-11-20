/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Isoperimetric
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Calculus.FDeriv.CircleMap
import TauCeti.Analysis.RCLike.OperatorNorm
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.MeasureTheory.Integral.Disc
import TauCeti.Topology.MetricSpace.Annulus

/-!
# Exponential decay of energy along long annuli

In Gromov compactness, a bubble is attached to the rest of the limit through a *neck*: a long
annulus `a ≤ |z - z₀| ≤ b`, conformally the cylinder `[log a, log b] × S¹` of length
`log (b / a)`, which carries little energy. This file proves that the energy of a solution of
`∂ₜu = J(u) ∂ₛu` decays exponentially towards the middle of such a cylinder, that its
derivative decays there pointwise, and that the middle of the cylinder has small image.

Let a constant symplectic form `ω` with compatible inner product tame `J` along `u` with constant
`c > 0`, and let `‖J(u)‖ ≤ M`. Write `E(r₁, r₂)` for the real-direction energy `∫ ‖∂ₛu‖²` over the
annulus `r₁ ≤ |z - z₀| ≤ r₂`, and `κ = 2c / (1 + M)²`.

* **Boundary control.** `2c E(a, b)` is at most `(1 + M)²` times the sum of the boundary densities
  `r² ∫ ‖∂ₛu(z₀ + r e^{iθ})‖² dθ` of the two circles `r = a` and `r = b`
  (`TauCeti.SymplecticForm.two_mul_mul_integral_norm_fderiv_one_sq_annulus_le`). This combines
  the isoperimetric bound of the annulus by its boundary-loop energies
  (`TauCeti.SymplecticForm.integral_norm_fderiv_one_sq_annulus_le`) with the angular bound
  `TauCeti.integral_norm_deriv_comp_circleMap_sq_le`.
* **Exponential decay.** Shrinking the annulus symmetrically in the cylinder coordinate, the
  function `f(T) = E(a e^T, b e^{-T})` has derivative `-(ρ₁² g(ρ₁) + ρ₂² g(ρ₂))` at the radii
  `ρ₁ = a e^T`, `ρ₂ = b e^{-T}`, where `g` is the circle integral of the energy density. Boundary
  control therefore reads `κ f ≤ -f'`, so `e^{κT} f(T)` is antitone and
  `E(a e^T, b e^{-T}) ≤ e^{-κT} E(a, b)`
  (`TauCeti.SymplecticForm.integral_norm_fderiv_one_sq_annulus_le_exp_mul`). For a general
  subannulus, `E(r₁, r₂) ≤ max (a / r₁) (r₂ / b) ^ κ E(a, b)`
  (`TauCeti.SymplecticForm.integral_norm_fderiv_one_sq_annulus_le_rpow_mul`). Neither statement
  assumes small energy or compact image.
* **Pointwise decay.** If moreover `J` is `C²` near a compact set `K` containing the image, then
  there is a threshold `δ > 0` such that every such solution with `E(a, b) < δ` satisfies
  `π |z - z₀|² ‖∂ₛu(z)‖² ≤ 32 max (2a / |z - z₀|) (3 |z - z₀| / (2b)) ^ κ E(a, b)` for
  `2a ≤ |z - z₀|` and `3 |z - z₀| ≤ 2b`
  (`TauCeti.SymplecticForm.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_annulus`):
  apply the mean-value inequality on the disc of radius `|z - z₀| / 2` about `z`, which lies in
  the annulus `|z - z₀| / 2 ≤ |w - z₀| ≤ 3 |z - z₀| / 2`, and the exponential decay to that
  annulus.
  In the cylinder coordinate this is exponential decay of `|du|` towards the middle of the neck.
* **Small image.** Integrating this bound along an arc and a ray, the image of the middle annulus
  `r₁ ≤ |w - z₀| ≤ r₂`, for `2a ≤ r₁` and `3 r₂ ≤ 2b`, has diameter at most
  `(1 + M) (2π + 1 / γ) √(32 E(a, b) / π) ((2a / r₁) ^ γ + (3 r₂ / (2b)) ^ γ)` with `γ = κ / 2`
  (`TauCeti.SymplecticForm.exists_pos_forall_norm_sub_le_annulus`). So the middle of a neck of small
  energy is mapped into a small ball, which is how the two ends of a neck are shown to converge to
  the same node point.

The energy decay is the isoperimetric argument of McDuff and Salamon for long cylinders of small
energy, and the statements are those of Ivashkovich and Shevchishin's long-cylinder lemma. The
statement that no energy is lost in the necks of a convergent sequence is not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Sections 4.4 and 4.7 (the isoperimetric inequality, and
  long cylinders of small energy in the proof that bubbles connect).
* S. Ivashkovich and V. Shevchishin, *Gromov compactness theorem for J-complex curves with
  boundary*, arXiv:math/9903047, Lemma 3.7 (long cylinders of small energy).
-/

public section

open Complex MeasureTheory Metric Set Filter
open scoped Real RealInnerProductSpace Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {u : ℂ → V} {J : V → V →L[ℝ] V} {z₀ : ℂ} {a b c M : ℝ}

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- For `0 ≤ t ≤ T` with `a e^T ≤ b e^{-T}`, the radii `a e^t ≤ b e^{-t}` lie in `[a, b]`. -/
private theorem radii_mem {T t : ℝ} (ha : 0 < a) (hTab : a * Real.exp T ≤ b * Real.exp (-T))
    (ht : t ∈ Icc 0 T) :
    a ≤ a * Real.exp t ∧ a * Real.exp t ≤ b * Real.exp (-t) ∧ b * Real.exp (-t) ≤ b := by
  have hb : 0 < b := pos_of_mul_pos_left ((mul_pos ha (Real.exp_pos T)).trans_le hTab)
    (Real.exp_pos _).le
  refine ⟨le_mul_of_one_le_right ha.le (Real.one_le_exp ht.1), ?_,
    mul_le_of_le_one_right hb.le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.1))⟩
  calc a * Real.exp t ≤ a * Real.exp T := by gcongr; exact ht.2
    _ ≤ b * Real.exp (-T) := hTab
    _ ≤ b * Real.exp (-t) := by gcongr; exact ht.2

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The Grönwall step of the exponential decay. Let `P` be continuous on `[a, b]` with derivative
`G` on `(a, b)`, `0 < a`, and write `f(t) = P (b e^{-t}) - P (a e^t)`, whose derivative is
`-(b e^{-t} G(b e^{-t}) + a e^t G(a e^t))`. If `κ f ≤ -f'` on `(0, T)`, then
`e^{κ T} f(T) ≤ f(0)`. -/
private theorem exp_mul_sub_le_sub {P G : ℝ → ℝ} {κ T : ℝ} (ha : 0 < a) (hT : 0 ≤ T)
    (hTab : a * Real.exp T ≤ b * Real.exp (-T)) (hPc : ContinuousOn P (Icc a b))
    (hPd : ∀ x ∈ Ioo a b, HasDerivAt P (G x) x)
    (hle : ∀ t ∈ Ioo 0 T, κ * (P (b * Real.exp (-t)) - P (a * Real.exp t)) ≤
      b * Real.exp (-t) * G (b * Real.exp (-t)) + a * Real.exp t * G (a * Real.exp t)) :
    Real.exp (κ * T) * (P (b * Real.exp (-T)) - P (a * Real.exp T)) ≤ P b - P a := by
  set α : ℝ → ℝ := fun t ↦ a * Real.exp t with hα_def
  set β : ℝ → ℝ := fun t ↦ b * Real.exp (-t) with hβ_def
  have hαβ (t : ℝ) (ht : t ∈ Icc 0 T) := radii_mem ha hTab ht
  have hαβ' (t : ℝ) (ht : t ∈ Ioo 0 T) : a < α t ∧ β t < b := by
    have hb : 0 < b := ha.trans_le ((hαβ T ⟨hT, le_rfl⟩).1.trans
      ((hαβ T ⟨hT, le_rfl⟩).2.1.trans (hαβ T ⟨hT, le_rfl⟩).2.2))
    exact ⟨lt_mul_of_one_lt_right ha (Real.one_lt_exp_iff.mpr ht.1),
      mul_lt_of_lt_one_right hb (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht.1))⟩
  -- `h(t) = e^{κ t} f(t)` is continuous on `[0, T]` and has nonpositive derivative inside.
  set h : ℝ → ℝ := fun t ↦ Real.exp (κ * t) * (P (β t) - P (α t)) with hh_def
  have hcont : ContinuousOn h (Icc 0 T) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      ((hPc.comp (continuous_const.mul (Real.continuous_exp.comp continuous_neg)).continuousOn
          fun t ht ↦ ⟨(hαβ t ht).1.trans (hαβ t ht).2.1, (hαβ t ht).2.2⟩).sub
        (hPc.comp (continuous_const.mul Real.continuous_exp).continuousOn
          fun t ht ↦ ⟨(hαβ t ht).1, (hαβ t ht).2.1.trans (hαβ t ht).2.2⟩))
  have hderiv (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt h
      (Real.exp (κ * t) * (κ * (P (β t) - P (α t)) - (β t * G (β t) + α t * G (α t)))) t := by
    have hle := hαβ t (Ioo_subset_Icc_self ht)
    have hβd : HasDerivAt β (-β t) t := by
      simpa only [hβ_def, Function.comp_def, mul_neg, mul_one] using
        ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).const_mul b
    have hPβ := (hPd (β t) ⟨(hαβ' t ht).1.trans_le hle.2.1, (hαβ' t ht).2⟩).comp t hβd
    have hPα := (hPd (α t) ⟨(hαβ' t ht).1, hle.2.1.trans_lt (hαβ' t ht).2⟩).comp t
      ((Real.hasDerivAt_exp t).const_mul a)
    convert ((Real.hasDerivAt_exp (κ * t)).comp t ((hasDerivAt_id t).const_mul κ)).mul
      (hPβ.sub hPα) using 1
    · ext s
      simp [hh_def]
    · simp only [Pi.sub_apply, Function.comp_apply, mul_one]
      ring
  have hanti : AntitoneOn h (Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hcont
      (fun t ht ↦ (hderiv t (by rwa [interior_Icc] at ht)).hasDerivWithinAt) fun t ht ↦ ?_
    rw [interior_Icc] at ht
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [hle t ht])
  simpa [hh_def, hα_def, hβ_def] using hanti ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The integration step of the exponential decay. Let `G` be continuous on `[a, b]`, `0 < a`,
and write `f(t) = ∫_{a e^t}^{b e^{-t}} G`, whose derivative is
`-(b e^{-t} G(b e^{-t}) + a e^t G(a e^t))`. If `κ f ≤ -f'` on `(0, T)`, then
`e^{κ T} f(T) ≤ f(0)`. -/
private theorem exp_mul_integral_le_integral {G : ℝ → ℝ} {κ T : ℝ} (ha : 0 < a) (hT : 0 ≤ T)
    (hTab : a * Real.exp T ≤ b * Real.exp (-T)) (hG : ContinuousOn G (Icc a b))
    (hle : ∀ t ∈ Ioo 0 T, κ * ∫ r in a * Real.exp t..b * Real.exp (-t), G r ≤
      b * Real.exp (-t) * G (b * Real.exp (-t)) + a * Real.exp t * G (a * Real.exp t)) :
    Real.exp (κ * T) * ∫ r in a * Real.exp T..b * Real.exp (-T), G r ≤ ∫ r in a..b, G r := by
  have hT' := radii_mem ha hTab ⟨hT, le_rfl⟩
  have hab : a ≤ b := hT'.1.trans (hT'.2.1.trans hT'.2.2)
  -- The primitive `P` of `G` from `a`, so that `f(t) = P (b e^{-t}) - P (a e^t)`.
  have hPc : ContinuousOn (fun x ↦ ∫ r in a..x, G r) (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := a) (b := b)
      (f := G) (by rw [uIcc_of_le hab]; exact hG.integrableOn_Icc)
    rwa [uIcc_of_le hab] at h
  have hPd (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt (fun x ↦ ∫ r in a..x, G r) (G x) x :=
    intervalIntegral.integral_hasDerivAt_right
      ((hG.mono (Icc_subset_Icc le_rfl hx.2.le)).intervalIntegrable_of_Icc hx.1.le)
      (_root_.AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
        (hG.aestronglyMeasurable measurableSet_Icc) (Icc_mem_nhds hx.1 hx.2))
      (hG.continuousAt (Icc_mem_nhds hx.1 hx.2))
  have hf (t : ℝ) (ht : t ∈ Icc 0 T) : ∫ r in a * Real.exp t..b * Real.exp (-t), G r =
      (∫ r in a..b * Real.exp (-t), G r) - ∫ r in a..a * Real.exp t, G r := by
    obtain ⟨h₁, h₁₂, h₂⟩ := radii_mem ha hTab ht
    exact (intervalIntegral.integral_interval_sub_left
      ((hG.mono (Icc_subset_Icc le_rfl h₂)).intervalIntegrable_of_Icc (h₁.trans h₁₂))
      ((hG.mono (Icc_subset_Icc le_rfl (h₁₂.trans h₂))).intervalIntegrable_of_Icc h₁)).symm
  have key := exp_mul_sub_le_sub ha hT hTab hPc hPd fun t ht ↦ by
    rw [← hf t (Ioo_subset_Icc_self ht)]
    exact hle t ht
  rwa [← hf T ⟨hT, le_rfl⟩, intervalIntegral.integral_same, sub_zero] at key

omit [FiniteDimensional ℝ V] in
/-- The energy density `‖∂ₛu‖²` of a `C¹` map on the annulus `a ≤ |z - z₀| ≤ b` is continuous
there. -/
private theorem continuousOn_norm_fderiv_one_sq_annulus
    (hu : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 1 u z) :
    ContinuousOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} :=
  fun z hz ↦ ((((hu z hz).continuousAt_fderiv one_ne_zero).clm_apply
    continuousAt_const).norm.pow 2).continuousWithinAt

omit [FiniteDimensional ℝ V] in
/-- The energy density `‖∂ₛu‖²` of a `C¹` map on the annulus `a ≤ |z - z₀| ≤ b` is integrable
on every subannulus. -/
private theorem integrableOn_norm_fderiv_one_sq_annulus
    (hu : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 1 u z) {r₁ r₂ : ℝ}
    (h₁ : a ≤ r₁) (h₂ : r₂ ≤ b) :
    IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) {z : ℂ | r₁ ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ r₂} :=
  ((continuousOn_norm_fderiv_one_sq_annulus hu).mono
    (setOf_le_norm_sub_le_subset h₁ h₂)).integrableOn_compact
    (isCompact_setOf_le_norm_sub_le z₀ r₁ r₂)

/-- **Exponential decay of energy along a long annulus.** For a uniformly tamed solution of
`∂ₜu = J(u) ∂ₛu` on the annulus `a ≤ |z - z₀| ≤ b` with `‖J(u)‖ ≤ M`, the energy of the
subannulus `a e^T ≤ |z - z₀| ≤ b e^{-T}`, obtained by removing collars of length `T` from both
ends of the cylinder `[log a, log b] × S¹`, is at most `e^{-κT}` times the energy of the whole
annulus, where `κ = 2c / (1 + M)²`. -/
theorem integral_norm_fderiv_one_sq_annulus_le_exp_mul
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (ha : 0 < a)
    (hu : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 2 u z)
    (hCR : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
      fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (htame : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hJ : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ‖J (u z)‖ ≤ M)
    {T : ℝ} (hT : 0 ≤ T) (hTab : a * Real.exp T ≤ b * Real.exp (-T)) :
    (∫ z in {z : ℂ | a * Real.exp T ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b * Real.exp (-T)},
        ‖fderiv ℝ u z 1‖ ^ 2) ≤
      Real.exp (-(2 * c / (1 + M) ^ 2 * T)) *
        ∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ‖fderiv ℝ u z 1‖ ^ 2 := by
  have hT' := radii_mem ha hTab ⟨hT, le_rfl⟩
  have hab : a ≤ b := hT'.1.trans (hT'.2.1.trans hT'.2.2)
  have hM : 0 ≤ M := (norm_nonneg _).trans
    (hJ _ (circleMap_mem_setOf_le_norm_sub_le ha.le ⟨le_rfl, hab⟩ 0))
  -- The energy of a subannulus is the radial integral of the boundary densities `G r`.
  have he := continuousOn_norm_fderiv_one_sq_annulus fun z hz ↦ (hu z hz).of_le one_le_two
  set G : ℝ → ℝ := fun r ↦ r * ∫ θ in -π..π, ‖fderiv ℝ u (circleMap z₀ r θ) 1‖ ^ 2
  have hpolar (r₁ r₂ : ℝ) (h₁ : a ≤ r₁) (h₁₂ : r₁ ≤ r₂) (h₂ : r₂ ≤ b) :
      (∫ z in {z : ℂ | r₁ ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ r₂}, ‖fderiv ℝ u z 1‖ ^ 2) =
        ∫ r in r₁..r₂, G r := by
    simpa only [smul_eq_mul] using integral_annulus_eq_integral_circleMap
      (ha.le.trans h₁) h₁₂
      (integrableOn_norm_fderiv_one_sq_annulus (fun z hz ↦ (hu z hz).of_le one_le_two) h₁ h₂)
  -- Boundary control on every subannulus `a e^t ≤ |z - z₀| ≤ b e^{-t}` is `κ f ≤ -f'`.
  have hkey := exp_mul_integral_le_integral (κ := 2 * c / (1 + M) ^ 2) ha hT hTab
    (by simpa only [smul_eq_mul] using he.smul_integral_comp_circleMap ha.le) fun t ht ↦ by
      obtain ⟨h₁, h₁₂, h₂⟩ := radii_mem ha hTab (Ioo_subset_Icc_self ht)
      have hbd := ω.two_mul_mul_integral_norm_fderiv_one_sq_annulus_le hg hc
        (ha.le.trans h₁) h₁₂ (fun z hz ↦ hu z (setOf_le_norm_sub_le_subset h₁ h₂ hz))
        (fun z hz ↦ hCR z (setOf_le_norm_sub_le_subset h₁ h₂ hz))
        (fun z hz ↦ htame z (setOf_le_norm_sub_le_subset h₁ h₂ hz))
        (fun z hz ↦ hJ z (setOf_le_norm_sub_le_subset h₁ h₂ hz))
      rw [hpolar _ _ h₁ h₁₂ h₂] at hbd
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      linarith
  rw [← hpolar _ _ hT'.1 hT'.2.1 hT'.2.2, ← hpolar _ _ le_rfl hab le_rfl] at hkey
  rwa [Real.exp_neg (2 * c / (1 + M) ^ 2 * T), inv_mul_eq_div, le_div_iff₀' (Real.exp_pos _)]

/-- **Energy decay towards the middle of an annulus.** For a uniformly tamed solution of
`∂ₜu = J(u) ∂ₛu` on the annulus `a ≤ |z - z₀| ≤ b` with `‖J(u)‖ ≤ M`, and `a ≤ r₁ ≤ r₂ ≤ b`, the
energy of the subannulus `r₁ ≤ |z - z₀| ≤ r₂` is at most `max (a / r₁) (r₂ / b) ^ κ` times the
energy of the whole annulus, where `κ = 2c / (1 + M)²`. -/
theorem integral_norm_fderiv_one_sq_annulus_le_rpow_mul
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (ha : 0 < a)
    (hu : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 2 u z)
    (hCR : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
      fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (htame : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hJ : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ‖J (u z)‖ ≤ M)
    {r₁ r₂ : ℝ} (h₁ : a ≤ r₁) (h₁₂ : r₁ ≤ r₂) (h₂ : r₂ ≤ b) :
    (∫ z in {z : ℂ | r₁ ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ r₂}, ‖fderiv ℝ u z 1‖ ^ 2) ≤
      max (a / r₁) (r₂ / b) ^ (2 * c / (1 + M) ^ 2) *
        ∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ‖fderiv ℝ u z 1‖ ^ 2 := by
  have hr₁ : 0 < r₁ := ha.trans_le h₁
  have hr₂ : 0 < r₂ := hr₁.trans_le h₁₂
  have hb : 0 < b := hr₂.trans_le h₂
  -- The collar length `T`: the largest one whose middle annulus contains `[r₁, r₂]`, so that
  -- `e^{-T} = max (a / r₁) (r₂ / b)`.
  set m := max (a / r₁) (r₂ / b)
  have hm : 0 < m := lt_max_of_lt_left (div_pos ha hr₁)
  set T := -Real.log m with hT_def
  have hexp : Real.exp (-T) = m := by rw [hT_def, neg_neg, Real.exp_log hm]
  have hT : 0 ≤ T :=
    neg_nonneg.2 (Real.log_nonpos hm.le (max_le ((div_le_one hr₁).2 h₁) ((div_le_one hb).2 h₂)))
  have h₁T : a * Real.exp T ≤ r₁ := by
    rw [hT_def, Real.exp_neg, Real.exp_log hm, mul_inv_le_iff₀ hm, ← div_le_iff₀' hr₁]
    exact le_max_left _ _
  have h₂T : r₂ ≤ b * Real.exp (-T) := by
    rw [hexp, ← div_le_iff₀' hb]
    exact le_max_right _ _
  have hdecay := integral_norm_fderiv_one_sq_annulus_le_exp_mul hg hc ha hu hCR htame hJ hT
    (h₁T.trans (h₁₂.trans h₂T))
  have hsub : {z : ℂ | r₁ ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ r₂} ⊆
      {z : ℂ | a * Real.exp T ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b * Real.exp (-T)} :=
    setOf_le_norm_sub_le_subset h₁T h₂T
  have hab : b * Real.exp (-T) ≤ b := mul_le_of_le_one_right hb.le
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hT))
  have hmono := setIntegral_mono_set
    (integrableOn_norm_fderiv_one_sq_annulus (fun z hz ↦ (hu z hz).of_le one_le_two)
      (le_mul_of_one_le_right ha.le (Real.one_le_exp hT)) hab)
    (ae_of_all _ fun z ↦ sq_nonneg _) hsub.eventuallySubset
  rw [← hexp, ← Real.exp_mul, show -T * (2 * c / (1 + M) ^ 2) = -(2 * c / (1 + M) ^ 2 * T) by ring]
  exact hmono.trans hdecay

/-- **Pointwise decay of the derivative in the middle of a neck.** Let `J` be `C²` on an open set
`W` containing a compact set `K`, with `J(x)² = -1` on `K`. There is `δ > 0`, depending only on
`J` and `K`, with the following property. Let `u` be a `C³` solution of `∂ₜu = J(u) ∂ₛu` on the
annulus `a ≤ |z - z₀| ≤ b` with image in `K`, uniformly tamed by `ω` with constant `c`, with
`‖J(u)‖ ≤ M`, and with energy `E` less than `δ`. Then every `z` with `2a ≤ |z - z₀|` and
`3 |z - z₀| ≤ 2b` satisfies
`π |z - z₀|² ‖∂ₛu(z)‖² ≤ 32 max (2a / |z - z₀|) (3 |z - z₀| / (2b)) ^ κ E`, where
`κ = 2c / (1 + M)²`. -/
theorem exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_annulus
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) {W K : Set V} (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W)
    (hK : IsCompact K) (hKW : K ⊆ W) (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) :
    ∃ δ > 0, ∀ ⦃u : ℂ → V⦄ ⦃z₀ : ℂ⦄ ⦃a b c M : ℝ⦄, 0 < a → 0 < c →
      (∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 3 u z) →
      (∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
        fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1)) →
      (∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ∀ v : V,
        c * ‖v‖ ^ 2 ≤ ω v (J (u z) v)) →
      (∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ‖J (u z)‖ ≤ M) →
      (∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, u z ∈ K) →
      (∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ‖fderiv ℝ u z 1‖ ^ 2) < δ →
      ∀ z, 2 * a ≤ ‖z - z₀‖ → 3 * ‖z - z₀‖ ≤ 2 * b →
        π * ‖z - z₀‖ ^ 2 * ‖fderiv ℝ u z 1‖ ^ 2 ≤
          32 * (max (2 * a / ‖z - z₀‖) (3 * ‖z - z₀‖ / (2 * b)) ^ (2 * c / (1 + M) ^ 2) *
            ∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ‖fderiv ℝ u z 1‖ ^ 2) := by
  obtain ⟨δ, hδ, hmv⟩ :=
    exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball
      hW hJ hK hKW hJsq
  refine ⟨δ, hδ, fun u z₀ a b c M ha hc hu hCR htame hJM huK hE z hz₁ hz₂ ↦ ?_⟩
  set ρ := ‖z - z₀‖
  have hρ : 0 < ρ := by linarith
  -- The disc of radius `ρ / 2` about `z` lies in the annulus `ρ / 2 ≤ |w - z₀| ≤ 3ρ / 2`.
  have hball : closedBall z (ρ / 2) ⊆ {w : ℂ | ρ / 2 ≤ ‖w - z₀‖ ∧ ‖w - z₀‖ ≤ 3 * ρ / 2} := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have h1 := norm_sub_le_norm_sub_add_norm_sub z w z₀
    have h2 := norm_sub_le_norm_sub_add_norm_sub w z z₀
    rw [norm_sub_rev z w] at h1
    exact ⟨by linarith, by linarith⟩
  have hsub : {w : ℂ | ρ / 2 ≤ ‖w - z₀‖ ∧ ‖w - z₀‖ ≤ 3 * ρ / 2} ⊆
      {w : ℂ | a ≤ ‖w - z₀‖ ∧ ‖w - z₀‖ ≤ b} :=
    setOf_le_norm_sub_le_subset (by linarith) (by linarith)
  have hu1 (w : ℂ) (hw : w ∈ {w : ℂ | a ≤ ‖w - z₀‖ ∧ ‖w - z₀‖ ≤ b}) : ContDiffAt ℝ 1 u w :=
    (hu w hw).of_le (by norm_num)
  have hEball := setIntegral_mono_set
    (integrableOn_norm_fderiv_one_sq_annulus hu1 (a := a) (b := b) (r₁ := ρ / 2)
      (r₂ := 3 * ρ / 2) (by linarith) (by linarith))
    (ae_of_all _ fun w ↦ sq_nonneg _)
    (ball_subset_closedBall.trans hball).eventuallySubset
  have hEann := setIntegral_mono_set
    (integrableOn_norm_fderiv_one_sq_annulus hu1 (a := a) (b := b) le_rfl le_rfl)
    (ae_of_all _ fun w ↦ sq_nonneg _) hsub.eventuallySubset
  have hdecay := integral_norm_fderiv_one_sq_annulus_le_rpow_mul hg hc ha
    (fun w hw ↦ (hu w hw).of_le (by norm_num)) hCR htame hJM (r₁ := ρ / 2) (r₂ := 3 * ρ / 2)
    (by linarith) (by linarith) (by linarith)
  have hmean := hmv (u := u) (z₀ := z) (r := ρ / 2) (by positivity)
    (fun w hw ↦ (hu w (hsub (hball (ball_subset_closedBall hw)))).contDiffWithinAt)
    (fun w hw ↦ ((((hu w (hsub (hball hw))).continuousAt_fderiv (by norm_num)).clm_apply
      continuousAt_const)).continuousWithinAt)
    (fun w hw ↦ hCR w (hsub (hball (ball_subset_closedBall hw))))
    (fun w hw ↦ huK w (hsub (hball (ball_subset_closedBall hw))))
    ((hEball.trans hEann).trans_lt hE)
  have h2a : a / (ρ / 2) = 2 * a / ρ := by field_simp
  have h3b : 3 * ρ / 2 / b = 3 * ρ / (2 * b) := div_div _ _ _
  rw [h2a, h3b] at hdecay
  calc π * ρ ^ 2 * ‖fderiv ℝ u z 1‖ ^ 2 = 4 * (π * (ρ / 2) ^ 2 * ‖fderiv ℝ u z 1‖ ^ 2) := by ring
    _ ≤ 4 * (8 * ∫ w in ball z (ρ / 2), ‖fderiv ℝ u w 1‖ ^ 2) := by gcongr
    _ ≤ 32 * ∫ w in {w : ℂ | ρ / 2 ≤ ‖w - z₀‖ ∧ ‖w - z₀‖ ≤ 3 * ρ / 2},
          ‖fderiv ℝ u w 1‖ ^ 2 := by linarith
    _ ≤ _ := by gcongr

omit [FiniteDimensional ℝ V] in
/-- A path whose speed at `ρ` is at most `K ((x / ρ) ^ γ + (ρ y) ^ γ) / ρ`, the profile of the
derivative in the middle of a neck, moves by at most `K ((x / s) ^ γ + (t y) ^ γ) / γ` between the
radii `s ≤ t`. -/
private theorem norm_sub_le_of_norm_deriv_le {φ φ' : ℝ → V} {K x y γ s t : ℝ}
    (hK : 0 ≤ K) (hx : 0 ≤ x) (hy : 0 ≤ y) (hγ : 0 < γ) (hs : 0 < s) (hst : s ≤ t)
    (hφ : ∀ ρ ∈ Icc s t, HasDerivAt φ (φ' ρ) ρ)
    (hbound : ∀ ρ ∈ Icc s t, ‖φ' ρ‖ ≤ K * ((x / ρ) ^ γ + (ρ * y) ^ γ) / ρ) :
    ‖φ t - φ s‖ ≤ K * ((x / s) ^ γ + (t * y) ^ γ) / γ := by
  -- The bounding function `B` vanishes at `s` and has the speed bound as derivative.
  set B : ℝ → ℝ := fun ρ ↦ K * (x ^ γ * (s ^ (-γ) - ρ ^ (-γ)) + y ^ γ * (ρ ^ γ - s ^ γ)) / γ
  have hB (ρ : ℝ) (hρ : 0 < ρ) : HasDerivAt B (K * ((x / ρ) ^ γ + (ρ * y) ^ γ) / ρ) ρ := by
    have h1 := (Real.hasDerivAt_rpow_const (x := ρ) (p := -γ) (Or.inl hρ.ne')).const_sub
      (s ^ (-γ))
    have h2 := (Real.hasDerivAt_rpow_const (x := ρ) (p := γ) (Or.inl hρ.ne')).sub_const (s ^ γ)
    convert (((h1.const_mul (x ^ γ)).add (h2.const_mul (y ^ γ))).const_mul K).div_const γ
      using 1
    rw [Real.div_rpow hx hρ.le, Real.mul_rpow hρ.le hy, Real.rpow_sub_one hρ.ne',
      Real.rpow_sub_one hρ.ne', Real.rpow_neg hρ.le]
    field_simp
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary' (f := fun ρ ↦ φ ρ - φ s)
    (a := s) (b := t) (B := B)
    (fun ρ hρ ↦ ((hφ ρ hρ).continuousAt.sub continuousAt_const).continuousWithinAt)
    (fun ρ hρ ↦ ((hφ ρ (Ico_subset_Icc_self hρ)).sub_const (φ s)).hasDerivWithinAt)
    (by simp [B])
    (fun ρ hρ ↦ (hB ρ (hs.trans_le hρ.1)).continuousAt.continuousWithinAt)
    (fun ρ hρ ↦ (hB ρ (hs.trans_le hρ.1)).hasDerivWithinAt)
    (fun ρ hρ ↦ hbound ρ (Ico_subset_Icc_self hρ)) ⟨hst, le_rfl⟩
  refine key.trans ?_
  have ht : 0 < t := hs.trans_le hst
  have h1 : 0 ≤ x ^ γ * t ^ (-γ) := by positivity
  have h2 : 0 ≤ y ^ γ * s ^ γ := by positivity
  rw [Real.div_rpow hx hs.le, Real.mul_rpow ht.le hy, div_eq_mul_inv (x ^ γ),
    ← Real.rpow_neg hs.le]
  have hle : x ^ γ * (s ^ (-γ) - t ^ (-γ)) + y ^ γ * (t ^ γ - s ^ γ) ≤
      x ^ γ * s ^ (-γ) + t ^ γ * y ^ γ := by nlinarith
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle hK) hγ.le

omit [FiniteDimensional ℝ V] in
/-- The squared pointwise bound of
`TauCeti.SymplecticForm.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_annulus` in linear
form, for the whole derivative: with `γ = c / (1 + M)²`, `E ≥ 0` and `ρ = |z - z₀| > 0`,
`‖du(z)‖ ≤ (1 + M) √(32 E / π) ((2a / ρ) ^ γ + (ρ (3 / (2b))) ^ γ) / ρ`. -/
private theorem norm_fderiv_le_of_pi_mul_sq_mul_norm_fderiv_one_sq_le {z : ℂ} {E : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hE : 0 ≤ E) (hρ : 0 < ‖z - z₀‖)
    (hCR : fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1)) (hJ : ‖J (u z)‖ ≤ M)
    (h : π * ‖z - z₀‖ ^ 2 * ‖fderiv ℝ u z 1‖ ^ 2 ≤
      32 * (max (2 * a / ‖z - z₀‖) (3 * ‖z - z₀‖ / (2 * b)) ^ (2 * c / (1 + M) ^ 2) * E)) :
    ‖fderiv ℝ u z‖ ≤ (1 + M) * √(32 * E / π) *
      ((2 * a / ‖z - z₀‖) ^ (c / (1 + M) ^ 2) +
        (‖z - z₀‖ * (3 / (2 * b))) ^ (c / (1 + M) ^ 2)) / ‖z - z₀‖ := by
  set ρ := ‖z - z₀‖
  set γ := c / (1 + M) ^ 2 with hγ_def
  set m := max (2 * a / ρ) (3 * ρ / (2 * b))
  have hm : 0 ≤ m := le_max_of_le_left (by positivity)
  have hκ : 2 * c / (1 + M) ^ 2 = γ * 2 := by rw [hγ_def]; ring
  rw [hκ, Real.rpow_mul hm, Real.rpow_two] at h
  -- `ρ ‖∂ₛu(z)‖ ≤ √(32 E / π) m ^ γ`, by comparing squares.
  have h1 : ρ * ‖fderiv ℝ u z 1‖ ≤ √(32 * E / π) * m ^ γ := by
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero, mul_pow, mul_pow,
      Real.sq_sqrt (by positivity), div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
    linarith
  -- `m ^ γ` is at most the sum of the powers of its two candidates.
  have h2 : m ^ γ ≤ (2 * a / ρ) ^ γ + (ρ * (3 / (2 * b))) ^ γ := by
    have e : ρ * (3 / (2 * b)) = 3 * ρ / (2 * b) := by ring
    have p1 : 0 ≤ (2 * a / ρ) ^ γ := by positivity
    have p2 : 0 ≤ (3 * ρ / (2 * b)) ^ γ := by positivity
    rw [e]
    rcases max_choice (2 * a / ρ) (3 * ρ / (2 * b)) with hmax | hmax <;> simp only [m, hmax] <;>
      linarith
  have h3 : ‖fderiv ℝ u z 1‖ ≤
      √(32 * E / π) * ((2 * a / ρ) ^ γ + (ρ * (3 / (2 * b))) ^ γ) / ρ := by
    rw [le_div_iff₀ hρ, mul_comm]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
  calc ‖fderiv ℝ u z‖ ≤ (1 + M) * (√(32 * E / π) * ((2 * a / ρ) ^ γ +
        (ρ * (3 / (2 * b))) ^ γ) / ρ) := (fderiv ℝ u z).norm_le_of_apply_I_eq hCR hJ h3
    _ = _ := by ring

omit [FiniteDimensional ℝ V] in
/-- If `‖du‖ ≤ Kc ((2a / ρ) ^ γ + (ρ (3 / (2b))) ^ γ) / ρ` on the middle `2a ≤ ρ`, `3ρ ≤ 2b` of an
annulus, `ρ = |z - z₀|`, then `u` moves by at most `Kc ((2a / s) ^ γ + (t (3 / (2b))) ^ γ) / γ`
along a ray from radius `s` to radius `t` in the middle. -/
private theorem norm_sub_le_of_forall_norm_fderiv_le_ray {Kc γ s t θ : ℝ} (hKc : 0 ≤ Kc)
    (hγ : 0 < γ) (ha : 0 < a) (hb : 0 ≤ b) (hs : 2 * a ≤ s) (hst : s ≤ t) (ht : 3 * t ≤ 2 * b)
    (hdiff : ∀ z, 2 * a ≤ ‖z - z₀‖ → 3 * ‖z - z₀‖ ≤ 2 * b → DifferentiableAt ℝ u z)
    (hd : ∀ z, 2 * a ≤ ‖z - z₀‖ → 3 * ‖z - z₀‖ ≤ 2 * b → ‖fderiv ℝ u z‖ ≤
      Kc * ((2 * a / ‖z - z₀‖) ^ γ + (‖z - z₀‖ * (3 / (2 * b))) ^ γ) / ‖z - z₀‖) :
    ‖u (circleMap z₀ t θ) - u (circleMap z₀ s θ)‖ ≤
      Kc * ((2 * a / s) ^ γ + (t * (3 / (2 * b))) ^ γ) / γ := by
  have hs0 : 0 < s := by linarith
  have hin {ρ : ℝ} (hρ : ρ ∈ Icc s t) :
      2 * a ≤ ‖circleMap z₀ ρ θ - z₀‖ ∧ 3 * ‖circleMap z₀ ρ θ - z₀‖ ≤ 2 * b := by
    rw [norm_circleMap_sub_center _ (hs0.le.trans hρ.1)]
    constructor <;> linarith [hρ.1, hρ.2]
  refine norm_sub_le_of_norm_deriv_le (φ := fun ρ ↦ u (circleMap z₀ ρ θ))
    (φ' := fun ρ ↦ fderiv ℝ u (circleMap z₀ ρ θ) (exp (θ * I))) hKc (by linarith)
    (by positivity) hγ hs0 hst (fun ρ hρ ↦ ?_) (fun ρ hρ ↦ ?_)
  · exact (hdiff _ (hin hρ).1 (hin hρ).2).hasFDerivAt.comp_hasDerivAt ρ
      (hasDerivAt_circleMap_radius z₀ ρ θ)
  · calc _ ≤ ‖fderiv ℝ u (circleMap z₀ ρ θ)‖ * ‖exp (θ * I)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := by
        rw [norm_exp_ofReal_mul_I, mul_one]
        refine (hd _ (hin hρ).1 (hin hρ).2).trans_eq ?_
        rw [norm_circleMap_sub_center _ (hs0.le.trans hρ.1)]

omit [FiniteDimensional ℝ V] in
/-- If `‖du‖ ≤ Kc ((2a / ρ) ^ γ + (ρ (3 / (2b))) ^ γ) / ρ` on the middle `2a ≤ ρ`, `3ρ ≤ 2b` of an
annulus, `ρ = |z - z₀|`, then for `2a ≤ r₁ ≤ r₂` and `3 r₂ ≤ 2b` any two points of the annulus
`r₁ ≤ |w - z₀| ≤ r₂` have images at distance at most
`Kc (2π + 1 / γ) ((2a / r₁) ^ γ + (r₂ (3 / (2b))) ^ γ)`: join them by an arc and a ray. -/
private theorem norm_sub_le_of_forall_norm_fderiv_le {Kc γ r₁ r₂ : ℝ} (hKc : 0 ≤ Kc)
    (hγ : 0 < γ) (ha : 0 < a) (hb : 0 ≤ b) (h₁ : 2 * a ≤ r₁) (h₂ : 3 * r₂ ≤ 2 * b)
    (hdiff : ∀ z, 2 * a ≤ ‖z - z₀‖ → 3 * ‖z - z₀‖ ≤ 2 * b → DifferentiableAt ℝ u z)
    (hd : ∀ z, 2 * a ≤ ‖z - z₀‖ → 3 * ‖z - z₀‖ ≤ 2 * b → ‖fderiv ℝ u z‖ ≤
      Kc * ((2 * a / ‖z - z₀‖) ^ γ + (‖z - z₀‖ * (3 / (2 * b))) ^ γ) / ‖z - z₀‖)
    {w₁ w₂ : ℂ} (hw₁ : w₁ ∈ {w : ℂ | r₁ ≤ ‖w - z₀‖ ∧ ‖w - z₀‖ ≤ r₂})
    (hw₂ : w₂ ∈ {w : ℂ | r₁ ≤ ‖w - z₀‖ ∧ ‖w - z₀‖ ≤ r₂}) :
    ‖u w₁ - u w₂‖ ≤ Kc * (2 * π + 1 / γ) * ((2 * a / r₁) ^ γ + (r₂ * (3 / (2 * b))) ^ γ) := by
  wlog hle : ‖w₁ - z₀‖ ≤ ‖w₂ - z₀‖ generalizing w₁ w₂
  · rw [norm_sub_rev]
    exact this hw₂ hw₁ (le_of_not_ge hle)
  have hr₁ : 0 < r₁ := by linarith
  have hρ₁ : 0 < ‖w₁ - z₀‖ := hr₁.trans_le hw₁.1
  have hQ {ρ ρ' : ℝ} (hρ : r₁ ≤ ρ) (hρ' : ρ' ≤ r₂) (hρ'0 : 0 ≤ ρ') :
      (2 * a / ρ) ^ γ + (ρ' * (3 / (2 * b))) ^ γ ≤
        (2 * a / r₁) ^ γ + (r₂ * (3 / (2 * b))) ^ γ := by
    gcongr
    exact div_nonneg (by positivity) (by linarith)
  have hQs : 0 ≤ (2 * a / r₁) ^ γ + (r₂ * (3 / (2 * b))) ^ γ :=
    add_nonneg (Real.rpow_nonneg (div_nonneg (by linarith) hr₁.le) _)
      (Real.rpow_nonneg (mul_nonneg (by linarith [hw₁.1, hw₁.2]) (by positivity)) _)
  -- Along the arc of radius `|w₁ - z₀|` from the angle of `w₁` to the angle of `w₂`.
  have harc := norm_sub_le_of_norm_fderiv_le_circle (z₀ := z₀) (u := u) hρ₁.le
    (θ₁ := arg (w₁ - z₀)) (θ₂ := arg (w₂ - z₀))
    (L := Kc * ((2 * a / r₁) ^ γ + (r₂ * (3 / (2 * b))) ^ γ) / ‖w₁ - z₀‖)
    (fun θ _ ↦ hdiff _ (by rw [norm_circleMap_sub_center _ hρ₁.le]; linarith [hw₁.1])
      (by rw [norm_circleMap_sub_center _ hρ₁.le]; linarith [hle, hw₂.2]))
    fun θ _ ↦ by
      refine (hd _ ?_ ?_).trans ?_ <;> rw [norm_circleMap_sub_center _ hρ₁.le]
      · linarith [hw₁.1]
      · linarith [hle, hw₂.2]
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hQ hw₁.1 (hle.trans hw₂.2) hρ₁.le) hKc) hρ₁.le
  -- Along the ray at the angle of `w₂`, from radius `|w₁ - z₀|` to radius `|w₂ - z₀|`.
  have hrad := (norm_sub_le_of_forall_norm_fderiv_le_ray (θ := arg (w₂ - z₀)) hKc hγ ha hb
    (h₁.trans hw₁.1) hle (by linarith [hw₂.2]) hdiff hd).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hQ hw₁.1 hw₂.2 (norm_nonneg _)) hKc)
      hγ.le)
  have hθ : |arg (w₂ - z₀) - arg (w₁ - z₀)| ≤ 2 * π := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [neg_pi_lt_arg (w₁ - z₀), arg_le_pi (w₁ - z₀),
      neg_pi_lt_arg (w₂ - z₀), arg_le_pi (w₂ - z₀)]
  rw [div_mul_cancel₀ _ hρ₁.ne', circleMap_norm_sub_arg_sub z₀ w₁] at harc
  rw [circleMap_norm_sub_arg_sub z₀ w₂] at hrad
  calc ‖u w₁ - u w₂‖ ≤ ‖u w₁ - u (circleMap z₀ ‖w₁ - z₀‖ (arg (w₂ - z₀)))‖ +
        ‖u (circleMap z₀ ‖w₁ - z₀‖ (arg (w₂ - z₀))) - u w₂‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
      rw [norm_sub_rev (u w₁), norm_sub_rev _ (u w₂)]
      refine (add_le_add (harc.trans (mul_le_mul_of_nonneg_left hθ
        (mul_nonneg hKc hQs))) hrad).trans_eq ?_
      ring

/-- **The middle of a neck has small image.** Let `J` be `C²` on an open set `W` containing a
compact set `K`, with `J(x)² = -1` on `K`. There is `δ > 0`, depending only on `J` and `K`, with
the following property. Let `u` be a `C³` solution of `∂ₜu = J(u) ∂ₛu` on the annulus
`a ≤ |z - z₀| ≤ b` with image in `K`, uniformly tamed by `ω` with constant `c`, with
`‖J(u)‖ ≤ M`, and with energy `E` less than `δ`. If `2a ≤ r₁ ≤ r₂` and `3 r₂ ≤ 2b`, then any two
points `w₁`, `w₂` of the annulus `r₁ ≤ |w - z₀| ≤ r₂` satisfy
`‖u w₁ - u w₂‖ ≤ (1 + M) (2π + 1 / γ) √(32 E / π) ((2a / r₁) ^ γ + (3 r₂ / (2b)) ^ γ)`,
where `γ = c / (1 + M)²`. So the image of the middle of a neck has diameter bounded by the square
root of its energy, and it shrinks as the collars `[a, r₁]` and `[r₂, b]` grow. -/
theorem exists_pos_forall_norm_sub_le_annulus
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) {W K : Set V} (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W)
    (hK : IsCompact K) (hKW : K ⊆ W) (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) :
    ∃ δ > 0, ∀ ⦃u : ℂ → V⦄ ⦃z₀ : ℂ⦄ ⦃a b c M : ℝ⦄, 0 < a → 0 < c →
      (∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 3 u z) →
      (∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
        fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1)) →
      (∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ∀ v : V,
        c * ‖v‖ ^ 2 ≤ ω v (J (u z) v)) →
      (∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ‖J (u z)‖ ≤ M) →
      (∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, u z ∈ K) →
      (∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ‖fderiv ℝ u z 1‖ ^ 2) < δ →
      ∀ ⦃r₁ r₂ : ℝ⦄, 2 * a ≤ r₁ → 3 * r₂ ≤ 2 * b →
      ∀ w₁ ∈ {w : ℂ | r₁ ≤ ‖w - z₀‖ ∧ ‖w - z₀‖ ≤ r₂},
      ∀ w₂ ∈ {w : ℂ | r₁ ≤ ‖w - z₀‖ ∧ ‖w - z₀‖ ≤ r₂},
        ‖u w₁ - u w₂‖ ≤ (1 + M) * (2 * π + (1 + M) ^ 2 / c) *
          √(32 * (∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ‖fderiv ℝ u z 1‖ ^ 2) / π) *
          ((2 * a / r₁) ^ (c / (1 + M) ^ 2) + (3 * r₂ / (2 * b)) ^ (c / (1 + M) ^ 2)) := by
  obtain ⟨δ, hδ, hpt⟩ :=
    exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_annulus hg hW hJ hK hKW hJsq
  refine ⟨δ, hδ, fun u z₀ a b c M ha hc hu hCR htame hJM huK hE r₁ r₂ h₁ h₂ w₁ hw₁ w₂ hw₂ ↦ ?_⟩
  have hb : 0 ≤ b := by linarith [hw₁.1, hw₁.2]
  have hM : 0 ≤ M := (norm_nonneg _).trans
    (hJM _ (circleMap_mem_setOf_le_norm_sub_le ha.le ⟨le_rfl, by linarith [hw₁.1, hw₁.2]⟩ 0))
  have hmem {z : ℂ} (hz₁ : 2 * a ≤ ‖z - z₀‖) (hz₂ : 3 * ‖z - z₀‖ ≤ 2 * b) :
      z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} := ⟨by linarith, by linarith⟩
  have h := norm_sub_le_of_forall_norm_fderiv_le (γ := c / (1 + M) ^ 2)
    (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) (by positivity) ha hb h₁ h₂
    (fun z hz₁ hz₂ ↦ (hu z (hmem hz₁ hz₂)).differentiableAt (by norm_num))
    (fun z hz₁ hz₂ ↦ norm_fderiv_le_of_pi_mul_sq_mul_norm_fderiv_one_sq_le ha.le hb
      (integral_nonneg fun _ ↦ sq_nonneg _) (by linarith) (hCR _ (hmem hz₁ hz₂))
      (hJM _ (hmem hz₁ hz₂)) (hpt ha hc hu hCR htame hJM huK hE _ hz₁ hz₂)) hw₁ hw₂
  rw [one_div_div, show r₂ * (3 / (2 * b)) = 3 * r₂ / (2 * b) by ring] at h
  refine h.trans_eq ?_
  ring

end TauCeti.SymplecticForm

end
