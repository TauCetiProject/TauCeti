/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Energy
public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import TauCeti.Analysis.Calculus.IntervalIntegral.Inverse
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Integral.IntervalIntegral.CauchySchwarz

/-!
# Arc-length reparametrization of regular Riemannian curves

Every regular `C¹` curve on a compact interval admits a unit-speed forward reparametrization,
whether it is `C¹` on an open parameter set containing the interval or only within the interval
itself. The new parameter is the accumulated Riemannian speed

`s(t) = ∫ r in a..t, ‖γ'(r)‖`.

Extending the speed by constants outside `[a, b]` makes `s` a `C¹` increasing bijection of `ℝ`
with positive derivative. Its inverse `ψ` is `C¹`, with derivative the reciprocal speed, and
the chain rule then gives `‖(γ ∘ ψ)'‖ = 1`. Besides unit speed, the theorems record the inverse
identities, endpoint values, monotonicity, and invariance of `Manifold.pathELength`, making the
results usable without unfolding their construction.

The first part of the file computes lengths from speeds: the length of a `C¹` curve is the integral
of its speed, a curve of constant speed `C` on `(a, b)` has length `C * (b - a)`, and the length
`L` and energy `E` over `[a, b]` satisfy the Cauchy–Schwarz bound `L ^ 2 ≤ 2 * (b - a) * E`, so
that energy less than `(b - a) / 2` forces length less than `b - a`.

## Main results

* `TauCeti.Manifold.pathELength_eq_setLIntegral_enorm_curveVelocity_Icc` and its `Ioo` variant:
  the Riemannian length of any curve is the integral of its speed.
* `ContMDiffOn.continuousOn_norm_curveVelocityWithin`: the speed of a `C¹` curve is continuous on
  a parameter set with unique derivatives, and `ContMDiffOn.continuousOn_norm_curveVelocity` is
  its open-set case.
* `ContMDiffOn.setLIntegral_enorm_curveVelocity_lt_top`: a `C¹` curve on an open parameter set
  has finite length on every compact subset of it.
* `ContMDiffOn.pathELength_eq_ofReal_integral_norm_curveVelocityWithin`: the Riemannian length of a
  `C¹` curve over a compact interval is the integral of its speed.
* `ContMDiff.integral_eq_intervalIntegral_norm_curveVelocity_smul`: integrals against the image of
  the speed-weighted Lebesgue measure on `(a, b]` under a `C¹` curve `γ` are integrals over
  `[a, b]` of the composite with `γ`, weighted by the speed.
* `TauCeti.Manifold.pathELength_eq_of_norm_curveVelocity_eq`: a curve of constant speed `C` on
  `(a, b)` has length `C * (b - a)`.
* `TauCeti.Manifold.pathELength_le_ofReal_sqrt_energy_of_intervalIntegrable`: the length `L` and
  the energy `E` of a curve with square-integrable speed over `[a, b]` satisfy
  `L ^ 2 ≤ 2 * (b - a) * E`; `ContMDiffOn.pathELength_le_ofReal_sqrt_energy` is the `C¹` case.
* `TauCeti.Manifold.pathELength_lt_of_energy_lt_of_intervalIntegrable` and
  `ContMDiffOn.pathELength_lt_of_energy_lt`: energy less than `(b - a) / 2` forces length less
  than `b - a`.
* `TauCeti.Manifold.exists_unit_speed_reparametrization`: a regular curve, `C¹` on an open set
  containing `[a, b]`, has a `C¹`, unit-speed reparametrization on the interval from zero to its
  length.
* `TauCeti.Manifold.exists_unit_speed_reparametrization_Icc`: the same for a curve which is only
  `C¹` within `[a, b]`, with velocities read within the parameter intervals.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Proposition 2.49(a).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §12, for the
  comparison of length and energy.
* The proof is adapted from `LeeLib/Ch02/ArcLengthReparametrization.lean` in the Apache-2.0
  [`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture)
  repository, revision `24f32e4d600878bfaac6bc2f2f9324175571c321`. This version works at the
  `C¹` regularity of the theorem and uses Mathlib's Riemannian bundle and path-length APIs.
-/

public section

open Bundle Filter MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-! ### Length as the integral of speed -/

omit [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
/-- The Riemannian length of a curve from `a` to `b` is the integral of its speed over `Icc a b`.
No regularity of the curve is assumed. -/
theorem pathELength_eq_setLIntegral_enorm_curveVelocity_Icc {γ : ℝ → M} {a b : ℝ} :
    Manifold.pathELength I γ a b = ∫⁻ t in Icc a b, ‖curveVelocity I γ t‖ₑ := by
  simp only [Manifold.pathELength_eq_lintegral_mfderiv_Icc, curveVelocity_apply]
  -- Mathlib evaluates `mfderiv% γ t` at `1 : TangentSpace 𝓘(ℝ) t`, while `curveVelocity_apply`
  -- evaluates it at `1 : ℝ`; the two agree because that tangent space is `ℝ` by definition.
  rfl

omit [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
/-- The Riemannian length of a curve from `a` to `b` is the integral of its speed over `Ioo a b`.
No regularity of the curve is assumed, and its velocities at `a` and `b` play no role. -/
theorem pathELength_eq_setLIntegral_enorm_curveVelocity_Ioo {γ : ℝ → M} {a b : ℝ} :
    Manifold.pathELength I γ a b = ∫⁻ t in Ioo a b, ‖curveVelocity I γ t‖ₑ := by
  rw [pathELength_eq_setLIntegral_enorm_curveVelocity_Icc, restrict_Ioo_eq_restrict_Icc]

/-- The Riemannian speed of a `C¹` curve, read within a parameter set with unique derivatives, is
continuous on that set. -/
theorem _root_.ContMDiffOn.continuousOn_norm_curveVelocityWithin {γ : ℝ → M} {s : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) (hs : UniqueMDiffOn 𝓘(ℝ, ℝ) s) :
    ContinuousOn (fun t ↦ ‖curveVelocityWithin I γ s t‖) s := by
  have hlift : ContinuousOn
      (fun t ↦ (TotalSpace.mk' E (γ t) (curveVelocityWithin I γ s t) : TangentBundle I M)) s :=
    (ContMDiffOn.continuousOn_curveVelocityLiftWithin hγ hs).congr fun t _ ↦
      (curveVelocityLiftWithin_apply (I := I) γ s t).symm
  exact (TauCeti.continuous_norm_bundle E (fun x : M ↦ TangentSpace I x)).comp_continuousOn hlift

/-- The Riemannian speed of a `C¹` curve on an open parameter set is continuous there. -/
theorem _root_.ContMDiffOn.continuousOn_norm_curveVelocity {γ : ℝ → M} {O : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ O) (hO : IsOpen O) :
    ContinuousOn (fun t ↦ ‖curveVelocity I γ t‖) O :=
  (hγ.continuousOn_norm_curveVelocityWithin hO.uniqueMDiffOn).congr fun t ht ↦ by
    simp only [curveVelocityWithin_of_mem_nhds (hO.mem_nhds ht)]

/-- A `C¹` curve on an open parameter set has finite length on every compact subset of it: the
integral of its speed over such a set is finite. -/
theorem _root_.ContMDiffOn.setLIntegral_enorm_curveVelocity_lt_top {γ : ℝ → M} {O : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ O) (hO : IsOpen O) {K : Set ℝ} (hK : IsCompact K)
    (hKO : K ⊆ O) : ∫⁻ t in K, ‖curveVelocity I γ t‖ₑ < (∞ : ℝ≥0∞) := by
  simpa only [ofReal_norm] using
    (((hγ.continuousOn_norm_curveVelocity hO).mono hKO).integrableOn_compact
      (μ := volume) hK).lintegral_lt_top

/-- The Riemannian length of a `C¹` curve over a compact interval inside its parameter set is the
integral of its speed. -/
theorem _root_.ContMDiffOn.pathELength_eq_ofReal_integral_norm_curveVelocityWithin
    {γ : ℝ → M} {s : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) {a b : ℝ} (hsub : Icc a b ⊆ s) :
    Manifold.pathELength I γ a b =
      ENNReal.ofReal (∫ t in a..b, ‖curveVelocityWithin I γ s t‖) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · have hcont : ContinuousOn (fun t ↦ ‖curveVelocityWithin I γ (Icc a b) t‖) (Icc a b) :=
      (hγ.mono hsub).continuousOn_norm_curveVelocityWithin (uniqueDiffOn_Icc hab).uniqueMDiffOn
    have hint : IntegrableOn (fun t ↦ ‖curveVelocityWithin I γ (Icc a b) t‖) (Ioo a b) :=
      (hcont.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
    have hcongr : ∀ t ∈ Ioo a b, curveVelocityWithin I γ s t = curveVelocity I γ t := fun t ht ↦
      curveVelocityWithin_of_mem_nhds
        (mem_nhds_iff.2 ⟨Ioo a b, Ioo_subset_Icc_self.trans hsub, isOpen_Ioo, ht⟩)
    have hcongr' : ∀ t ∈ Ioo a b, curveVelocityWithin I γ (Icc a b) t = curveVelocity I γ t :=
      fun t ht ↦ curveVelocityWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
    have hI : ∫ t in Ioo a b, ‖curveVelocityWithin I γ s t‖ =
        ∫ t in Ioo a b, ‖curveVelocityWithin I γ (Icc a b) t‖ :=
      setIntegral_congr_fun measurableSet_Ioo fun t ht ↦ by simp only [hcongr t ht, hcongr' t ht]
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo, hI,
      ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ ↦ norm_nonneg _),
      Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
    rw [ofReal_norm, hcongr' t ht, curveVelocity_apply]
    -- both sides are the Riemannian norm at `γ t`; they differ only in how the fibre is presented
    rfl
  · simp
  · rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc, Icc_eq_empty (not_le.2 hab),
      Measure.restrict_empty, lintegral_zero_measure, intervalIntegral.integral_symm,
      ENNReal.ofReal_of_nonpos]
    exact neg_nonpos.2 (intervalIntegral.integral_nonneg hab.le fun _ _ ↦ norm_nonneg _)

/-- The squared Riemannian speed of a `C¹` curve is interval integrable between any two
parameters of a parameter set with unique derivatives containing the interval between them. -/
theorem _root_.ContMDiffOn.intervalIntegrable_norm_curveVelocity_sq {γ : ℝ → M} {s : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) (hs : UniqueMDiffOn 𝓘(ℝ, ℝ) s) {a b : ℝ}
    (hsub : uIcc a b ⊆ s) :
    IntervalIntegrable (fun t ↦ ‖curveVelocity I γ t‖ ^ 2) volume a b := by
  refine (((hγ.continuousOn_norm_curveVelocityWithin hs).mono hsub).pow 2).intervalIntegrable
    |>.congr_uIoo fun t ht ↦ ?_
  have hmem : s ∈ 𝓝 t :=
    mem_interior_iff_mem_nhds.mp (interior_mono hsub (by rwa [uIcc, interior_Icc]))
  rw [Pi.pow_apply, curveVelocityWithin_of_mem_nhds hmem]

/-- If a `C¹` curve `γ` carries the Lebesgue measure on `(a, b]`, weighted by its speed, to a
measure `ν`, then integrals against `ν` are integrals over `[a, b]` weighted by the speed. -/
theorem _root_.ContMDiff.integral_eq_intervalIntegral_norm_curveVelocity_smul
    [MeasurableSpace M] [BorelSpace M] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 1 γ) {a b : ℝ} (hab : a ≤ b) {ν : Measure M}
    (hν : Measure.map γ ((volume.restrict (Ioc a b)).withDensity
      fun t ↦ ‖curveVelocity I γ t‖ₑ) = ν) {f : M → G} (hf : AEStronglyMeasurable f ν) :
    ∫ y, f y ∂ν = ∫ t in a..b, ‖curveVelocity I γ t‖ • f (γ t) := by
  have hc : Continuous fun t ↦ ‖curveVelocity I γ t‖ := by
    simpa only [curveVelocityWithin_univ, continuousOn_univ] using
      hγ.contMDiffOn.continuousOn_norm_curveVelocityWithin uniqueMDiffOn_univ
  have hρ : AEMeasurable (fun t ↦ ‖curveVelocity I γ t‖ₑ) (volume.restrict (Ioc a b)) := by
    simpa only [ofReal_norm] using hc.measurable.ennreal_ofReal.aemeasurable
  subst hν
  rw [integral_map hγ.continuous.aemeasurable hf,
    integral_withDensity_eq_integral_toReal_smul₀ hρ (ae_of_all _ fun _ ↦ eNorm_lt_top),
    intervalIntegral.integral_of_le hab]
  simp only [toReal_eNorm]

omit [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
/-- A curve whose Riemannian speed is `C` on the open interval `(a, b)` has length `C * (b - a)`
from `a` to `b`. No regularity of the curve is assumed, and its velocities at `a` and `b` play no
role. -/
theorem pathELength_eq_of_norm_curveVelocity_eq {γ : ℝ → M} {a b C : ℝ}
    (h : ∀ t ∈ Ioo a b, ‖curveVelocity I γ t‖ = C) :
    Manifold.pathELength I γ a b = ENNReal.ofReal C * ENNReal.ofReal (b - a) := by
  have key : ∀ t ∈ Ioo a b, ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ = ENNReal.ofReal C := fun t ht ↦ by
    rw [← h t ht, ofReal_norm, curveVelocity_apply]
    rfl
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo, setLIntegral_congr_fun measurableSet_Ioo key,
    setLIntegral_const, Real.volume_Ioo]

omit [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
/-- A curve with unit Riemannian speed on the open interval `(a, b)` has length `b - a` from `a`
to `b`. -/
theorem pathELength_eq_of_norm_curveVelocity_eq_one {γ : ℝ → M} {a b : ℝ}
    (h : ∀ t ∈ Ioo a b, ‖curveVelocity I γ t‖ = 1) :
    Manifold.pathELength I γ a b = ENNReal.ofReal (b - a) := by
  simpa only [ENNReal.ofReal_one, one_mul] using pathELength_eq_of_norm_curveVelocity_eq h

/-! ### Length and energy -/

omit [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
/-- **Length is controlled by energy.** If the squared Riemannian speed of a curve is integrable
on `[a, b]`, its length `L` and its energy `E` over `[a, b]` satisfy `L ^ 2 ≤ 2 * (b - a) * E`.
This is the Cauchy–Schwarz inequality for the speed `‖γ'‖` on `[a, b]`. No regularity of the
curve is assumed, so this applies to curves with finitely many corners. -/
theorem pathELength_le_ofReal_sqrt_energy_of_intervalIntegrable {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b) (hγ : IntervalIntegrable (fun t ↦ ‖curveVelocity I γ t‖ ^ 2) volume a b) :
    Manifold.pathELength I γ a b ≤ ENNReal.ofReal √(2 * (b - a) * energy I γ a b) := by
  set v : ℝ → ℝ := fun t ↦ ‖curveVelocity I γ t‖
  -- the speed is the square root of the integrable squared speed, hence itself in `L²`
  have hvm : AEStronglyMeasurable v (volume.restrict (Ioc a b)) := by
    simpa only [Function.comp_def, v, Real.sqrt_sq (norm_nonneg _)] using
      Real.continuous_sqrt.comp_aestronglyMeasurable hγ.1.aestronglyMeasurable
  have hv : IntegrableOn v (Ioc a b) :=
    ((memLp_two_iff_integrable_sq hvm).2 hγ.1).integrable one_le_two
  have hlen : Manifold.pathELength I γ a b = ENNReal.ofReal (∫ t in a..b, v t) := by
    rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
      ofReal_integral_eq_lintegral_ofReal (hv.mono_set Ioo_subset_Ioc_self)
        (Eventually.of_forall fun _ ↦ norm_nonneg _),
      Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t _ ↦ ?_
    rw [ofReal_norm, curveVelocity_apply]
    rfl
  rw [hlen]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ∫ t in a..b, v t
      ≤ √(b - a) * √(∫ t in a..b, v t ^ 2) :=
        TauCeti.integral_le_sqrt_mul_sqrt_integral_sq hab hγ
    _ = √(2 * (b - a) * energy I γ a b) := by
        rw [← Real.sqrt_mul (sub_nonneg.2 hab), energy_def]
        congr 1
        ring

omit [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
/-- If the squared Riemannian speed of a curve is integrable on `[a, b]`, where `a < b`, and its
energy over `[a, b]` is less than `(b - a) / 2`, the energy of a unit-speed curve, then its length
over `[a, b]` is less than `b - a`. -/
theorem pathELength_lt_of_energy_lt_of_intervalIntegrable {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : IntervalIntegrable (fun t ↦ ‖curveVelocity I γ t‖ ^ 2) volume a b)
    (hE : energy I γ a b < (b - a) / 2) :
    Manifold.pathELength I γ a b < ENNReal.ofReal (b - a) := by
  have hL : 0 < b - a := sub_pos.mpr hab
  have hE₀ := energy_nonneg (I := I) γ hab.le
  have hsq : 2 * (b - a) * energy I γ a b < (b - a) ^ 2 := by
    have hm := mul_lt_mul_of_pos_left hE (by positivity : 0 < 2 * (b - a))
    nlinarith
  have hroot := Real.sqrt_lt_sqrt (by positivity : 0 ≤ 2 * (b - a) * energy I γ a b) hsq
  rw [Real.sqrt_sq hL.le] at hroot
  exact (pathELength_le_ofReal_sqrt_energy_of_intervalIntegrable hab.le hγ).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff hL).mpr hroot)

/-- **Length is controlled by energy.** The Riemannian length `L` of a `C¹` curve over a compact
interval `[a, b]` inside its parameter set and its energy `E` satisfy `L ^ 2 ≤ 2 * (b - a) * E`.
This is the Cauchy–Schwarz inequality for the speed `‖γ'‖` on `[a, b]`. -/
theorem _root_.ContMDiffOn.pathELength_le_ofReal_sqrt_energy {γ : ℝ → M} {s : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) {a b : ℝ} (hsub : Icc a b ⊆ s) :
    Manifold.pathELength I γ a b ≤ ENNReal.ofReal √(2 * (b - a) * energy I γ a b) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact pathELength_le_ofReal_sqrt_energy_of_intervalIntegrable hab.le
      ((hγ.mono hsub).intervalIntegrable_norm_curveVelocity_sq (uniqueDiffOn_Icc hab).uniqueMDiffOn
        (by rw [uIcc_of_le hab.le]))
  · exact pathELength_le_ofReal_sqrt_energy_of_intervalIntegrable le_rfl
      (IntervalIntegrable.refl)
  · rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc, Icc_eq_empty (not_le.2 hab),
      Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le

/-- If the energy of a `C¹` curve over a compact interval `[a, b]` inside its parameter set, where
`a < b`, is less than `(b - a) / 2`, then its length over `[a, b]` is less than `b - a`. -/
theorem _root_.ContMDiffOn.pathELength_lt_of_energy_lt {γ : ℝ → M} {s : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) (hs : UniqueMDiffOn 𝓘(ℝ, ℝ) s)
    {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ s) (hE : energy I γ a b < (b - a) / 2) :
    Manifold.pathELength I γ a b < ENNReal.ofReal (b - a) :=
  pathELength_lt_of_energy_lt_of_intervalIntegrable hab
    (hγ.intervalIntegrable_norm_curveVelocity_sq hs (by rwa [uIcc_of_le hab.le])) hE

/-! ### Unit-speed reparametrization -/

/-- **Arc-length reparametrization of a regular curve on a closed interval.** Let `γ` be `C¹`
within `[a, b]`, where `a < b`, with nonzero velocity within `[a, b]` at every point of `[a, b]`.
There is a globally `C¹` function `ψ`, increasing from `[0, ∫_a^b ‖γ'(t)‖ dt]` onto `[a, b]`,
which inverts accumulated length. The curve `γ ∘ ψ` has the same endpoints and path length as
`γ`, and its velocity within its parameter interval has norm one throughout that interval. The
accumulated-speed endpoint is identified with the real value of `Manifold.pathELength`.

Unlike `exists_unit_speed_reparametrization`, nothing is assumed about `γ` outside `[a, b]`, and
all velocities are read within the parameter interval. The interval is nondegenerate because a
velocity within a singleton carries no information. -/
theorem exists_unit_speed_reparametrization_Icc {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hreg : ∀ t ∈ Icc a b, curveVelocityWithin I γ (Icc a b) t ≠ 0) :
    ∃ ψ : ℝ → ℝ,
      (∀ t ∈ Icc a b, ψ (∫ r in a..t, ‖curveVelocityWithin I γ (Icc a b) r‖) = t) ∧
      (∀ s ∈ Icc (0 : ℝ) (∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖),
        (∫ r in a..ψ s, ‖curveVelocityWithin I γ (Icc a b) r‖) = s) ∧
      (∀ s ∈ Icc (0 : ℝ) (∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖),
        ψ s ∈ Icc a b) ∧
      StrictMonoOn ψ (Icc 0 (∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖)) ∧
      ContDiff ℝ 1 ψ ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 (γ ∘ ψ)
        (Icc 0 (∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖)) ∧
      (γ ∘ ψ) 0 = γ a ∧
      (γ ∘ ψ) (∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖) = γ b ∧
      (∀ s ∈ Icc (0 : ℝ) (∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖),
        ‖curveVelocityWithin I (γ ∘ ψ)
          (Icc 0 (∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖)) s‖ = 1) ∧
      Manifold.pathELength I (γ ∘ ψ) 0 (∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖) =
        Manifold.pathELength I γ a b ∧
      (∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖) =
        (Manifold.pathELength I γ a b).toReal := by
  have hU : UniqueMDiffOn 𝓘(ℝ, ℝ) (Icc a b) :=
    uniqueMDiffOn_iff_uniqueDiffOn.2 (uniqueDiffOn_Icc hab)
  obtain ⟨ψ, hψmono, hψC1, hleft, hright⟩ :=
    exists_contDiff_inverse_intervalIntegral hab.le
      (hγ.continuousOn_norm_curveVelocityWithin hU) fun t ht ↦ norm_pos_iff.2 (hreg t ht)
  set L := ∫ r in a..b, ‖curveVelocityWithin I γ (Icc a b) r‖
  have hψa : ψ 0 = a := by simpa using hleft a (left_mem_Icc.2 hab.le)
  have hψb : ψ L = b := hleft b (right_mem_Icc.2 hab.le)
  have hL : 0 < L := hψmono.lt_iff_lt.1 (by rw [hψa, hψb]; exact hab)
  have hmaps : MapsTo ψ (Icc 0 L) (Icc a b) := fun s hs ↦ (hright s hs).1
  have hlength : Manifold.pathELength I (γ ∘ ψ) 0 L = Manifold.pathELength I γ a b := by
    have h := Manifold.pathELength_comp_of_monotoneOn (I := I) hL.le (hψmono.monotone.monotoneOn _)
      (hψC1.differentiable one_ne_zero).differentiableOn
      (by rw [hψa, hψb]; exact hγ.mdifferentiableOn one_ne_zero)
    simpa only [hψa, hψb] using h
  have hlength_toReal : L = (Manifold.pathELength I γ a b).toReal := by
    rw [hγ.pathELength_eq_ofReal_integral_norm_curveVelocityWithin subset_rfl,
      ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hab.le fun _ _ ↦ norm_nonneg _)]
  refine ⟨ψ, hleft, fun s hs ↦ (hright s hs).2.1, hmaps, hψmono.strictMonoOn _,
    hψC1, hγ.comp (contMDiffOn_iff_contDiffOn.2 hψC1.contDiffOn) hmaps,
    by rw [Function.comp_apply, hψa], by rw [Function.comp_apply, hψb], fun s hs ↦ ?_,
    hlength, hlength_toReal⟩
  obtain ⟨hψs, -, hψd⟩ := hright s hs
  have hpos : 0 < ‖curveVelocityWithin I γ (Icc a b) (ψ s)‖ := norm_pos_iff.2 (hreg _ hψs)
  rw [curveVelocityWithin_comp hψd.hasDerivWithinAt hmaps
      (hγ.mdifferentiableOn one_ne_zero _ hψs) (uniqueDiffOn_Icc hL s hs),
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]
  exact inv_mul_cancel₀ hpos.ne'

omit [IsManifold I 1 M] in
/-- The degenerate case `a = b` of `exists_unit_speed_reparametrization`: on a singleton the
within-interval velocity is not unique, so the reparametrization is the affine inverse
`s ↦ a + ‖γ' a‖⁻¹ * s`. -/
private lemma exists_unit_speed_reparametrization_self {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ J) {a : ℝ} (hsub : Icc a a ⊆ J)
    (hreg : ∀ t ∈ Icc a a, curveVelocity I γ t ≠ 0) :
    ∃ ψ : ℝ → ℝ,
      (∀ t ∈ Icc a a, ψ (∫ r in a..t, ‖curveVelocity I γ r‖) = t) ∧
      (∀ s ∈ Icc (0 : ℝ) (∫ r in a..a, ‖curveVelocity I γ r‖),
        (∫ r in a..ψ s, ‖curveVelocity I γ r‖) = s) ∧
      (∀ s ∈ Icc (0 : ℝ) (∫ r in a..a, ‖curveVelocity I γ r‖), ψ s ∈ Icc a a) ∧
      StrictMonoOn ψ (Icc 0 (∫ r in a..a, ‖curveVelocity I γ r‖)) ∧
      ContDiffOn ℝ 1 ψ (Icc 0 (∫ r in a..a, ‖curveVelocity I γ r‖)) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 (γ ∘ ψ) (Icc 0 (∫ r in a..a, ‖curveVelocity I γ r‖)) ∧
      (γ ∘ ψ) 0 = γ a ∧
      (γ ∘ ψ) (∫ r in a..a, ‖curveVelocity I γ r‖) = γ a ∧
      (∀ s ∈ Icc (0 : ℝ) (∫ r in a..a, ‖curveVelocity I γ r‖),
        ‖curveVelocity I (γ ∘ ψ) s‖ = 1) ∧
      Manifold.pathELength I (γ ∘ ψ) 0 (∫ r in a..a, ‖curveVelocity I γ r‖) =
        Manifold.pathELength I γ a a ∧
      (∫ r in a..a, ‖curveVelocity I γ r‖) = (Manifold.pathELength I γ a a).toReal := by
  let c := ‖curveVelocity I γ a‖⁻¹
  let ψ : ℝ → ℝ := fun s ↦ a + c * s
  have hpos : 0 < ‖curveVelocity I γ a‖ := norm_pos_iff.2 (hreg a (by simp))
  have hc : 0 < c := inv_pos.2 hpos
  have hC1 : ContDiff ℝ 1 ψ := contDiff_const.add (contDiff_const.mul contDiff_id)
  have ha : ψ 0 = a := by simp [ψ]
  have hd : HasDerivAt ψ c 0 := by
    simpa [ψ] using ((hasDerivAt_id 0).const_mul c).const_add a
  have hγa := hγ.contMDiffAt (hJ.mem_nhds (hsub (by simp : a ∈ Icc a a)))
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (γ ∘ ψ) (Icc 0 0) := by
    refine hγ.comp (contMDiffOn_iff_contDiffOn.2 hC1.contDiffOn) ?_
    intro s hs
    have hs0 : s = 0 := by simpa using hs
    simpa [hs0, ha] using hsub (by simp : a ∈ Icc a a)
  have hpos0 : 0 < ‖curveVelocity I γ (ψ 0)‖ := by
    rw [ha]
    exact hpos
  have hc0 : c = ‖curveVelocity I γ (ψ 0)‖⁻¹ := by rw [ha]
  have hunit : ‖curveVelocity I (γ ∘ ψ) 0‖ = 1 := by
    rw [curveVelocity_comp hd (by simpa only [ha] using hγa.mdifferentiableAt one_ne_zero),
      norm_smul, Real.norm_eq_abs, abs_of_pos hc, hc0]
    exact inv_mul_cancel₀ hpos0.ne'
  refine ⟨ψ, ?_⟩
  simp only [intervalIntegral.integral_same, Icc_self, mem_singleton_iff,
    forall_eq, Function.comp_apply, ha, Manifold.pathELength_self, ENNReal.toReal_zero,
    and_true, true_and]
  exact ⟨by simp [StrictMonoOn], hC1.contDiffOn,
    by simpa only [Icc_self] using hcomp, hunit⟩

/-- **Arc-length reparametrization of a regular curve.** Let `γ` be `C¹` on an open set `J`
containing `[a, b]`, with nonzero velocity along `[a, b]`. There is an increasing `C¹` function
`ψ` from
`[0, ∫_a^b ‖γ'(t)‖ dt]` to `[a, b]` which inverts accumulated length. The curve `γ ∘ ψ`
has the same endpoints and path length as `γ`, and its velocity has norm one throughout its
parameter interval. The accumulated-speed endpoint is identified with the real value of
`Manifold.pathELength`.

The case `a = b` is included: the new parameter interval is then the singleton `{0}`. For a curve
which is only `C¹` within `[a, b]`, see `exists_unit_speed_reparametrization_Icc`. -/
theorem exists_unit_speed_reparametrization {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ J) {a b : ℝ} (hab : a ≤ b)
    (hsub : Icc a b ⊆ J) (hreg : ∀ t ∈ Icc a b, curveVelocity I γ t ≠ 0) :
    ∃ ψ : ℝ → ℝ,
      (∀ t ∈ Icc a b, ψ (∫ r in a..t, ‖curveVelocity I γ r‖) = t) ∧
      (∀ s ∈ Icc (0 : ℝ) (∫ r in a..b, ‖curveVelocity I γ r‖),
        (∫ r in a..ψ s, ‖curveVelocity I γ r‖) = s) ∧
      (∀ s ∈ Icc (0 : ℝ) (∫ r in a..b, ‖curveVelocity I γ r‖), ψ s ∈ Icc a b) ∧
      StrictMonoOn ψ (Icc 0 (∫ r in a..b, ‖curveVelocity I γ r‖)) ∧
      ContDiffOn ℝ 1 ψ (Icc 0 (∫ r in a..b, ‖curveVelocity I γ r‖)) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 (γ ∘ ψ) (Icc 0 (∫ r in a..b, ‖curveVelocity I γ r‖)) ∧
      (γ ∘ ψ) 0 = γ a ∧
      (γ ∘ ψ) (∫ r in a..b, ‖curveVelocity I γ r‖) = γ b ∧
      (∀ s ∈ Icc (0 : ℝ) (∫ r in a..b, ‖curveVelocity I γ r‖),
        ‖curveVelocity I (γ ∘ ψ) s‖ = 1) ∧
      Manifold.pathELength I (γ ∘ ψ) 0 (∫ r in a..b, ‖curveVelocity I γ r‖) =
        Manifold.pathELength I γ a b ∧
      (∫ r in a..b, ‖curveVelocity I γ r‖) = (Manifold.pathELength I γ a b).toReal := by
  rcases lt_or_eq_of_le hab with hab | rfl
  · -- Restriction preserves velocities, so apply the closed-interval theorem to `γ`.
    have hγd : ∀ t ∈ Icc a b, MDifferentiableAt 𝓘(ℝ, ℝ) I γ t := fun t ht ↦
      (hγ.contMDiffAt (hJ.mem_nhds (hsub ht))).mdifferentiableAt one_ne_zero
    have hv : ∀ t ∈ Icc a b, curveVelocityWithin I γ (Icc a b) t =
        curveVelocity I γ t := fun t ht ↦ by
      rw [curveVelocityWithin_apply, curveVelocity_apply,
        mfderivWithin_eq_mfderiv (uniqueDiffOn_Icc hab t ht).uniqueMDiffWithinAt (hγd t ht)]
    have hint : ∀ t ∈ Icc a b,
        (∫ r in a..t, ‖curveVelocityWithin I γ (Icc a b) r‖) =
          ∫ r in a..t, ‖curveVelocity I γ r‖ := fun t ht ↦
      intervalIntegral.integral_congr fun r hr ↦
        congrArg norm (hv r (uIcc_subset_Icc (left_mem_Icc.2 hab.le) ht hr))
    obtain ⟨ψ, hleft, hright, hmaps, hmono, hC1, hcomp, ha, hb, hunit, hlength, hreal⟩ :=
      exists_unit_speed_reparametrization_Icc hab (hγ.mono hsub) fun t ht ↦ by
        rw [hv t ht]
        exact hreg t ht
    rw [hint b (right_mem_Icc.2 hab.le)] at hright hmaps hmono hcomp hb hunit hlength hreal
    have hleft' : ∀ t ∈ Icc a b, ψ (∫ r in a..t, ‖curveVelocity I γ r‖) = t :=
      fun t ht ↦ by simpa only [hint t ht] using hleft t ht
    have hψa : ψ 0 = a := by simpa using hleft' a (left_mem_Icc.2 hab.le)
    have hψb : ψ (∫ r in a..b, ‖curveVelocity I γ r‖) = b :=
      hleft' b (right_mem_Icc.2 hab.le)
    have hL : 0 < ∫ r in a..b, ‖curveVelocity I γ r‖ := by
      refine lt_of_le_of_ne (intervalIntegral.integral_nonneg hab.le fun _ _ ↦ norm_nonneg _) ?_
      intro hzero
      rw [← hzero] at hψb
      exact hab.ne (hψa.symm.trans hψb)
    refine ⟨ψ, hleft', fun s hs ↦ ?_, hmaps, hmono, hC1.contDiffOn, hcomp, ha, hb,
      fun s hs ↦ ?_, hlength, hreal⟩
    · simpa only [hint (ψ s) (hmaps s hs)] using hright s hs
    · -- Global regularity of `ψ` recovers the ambient velocity, including at the endpoints.
      have hd : MDifferentiableAt 𝓘(ℝ, ℝ) I (γ ∘ ψ) s :=
        (hγd _ (hmaps s hs)).comp s
          ((contMDiffAt_iff_contDiffAt.2 hC1.contDiffAt).mdifferentiableAt one_ne_zero)
      have hvcomp : curveVelocityWithin I (γ ∘ ψ)
          (Icc 0 (∫ r in a..b, ‖curveVelocity I γ r‖)) s =
            curveVelocity I (γ ∘ ψ) s := by
        rw [curveVelocityWithin_apply, curveVelocity_apply,
          mfderivWithin_eq_mfderiv (uniqueDiffOn_Icc hL s hs).uniqueMDiffWithinAt hd]
      simpa only [hvcomp] using hunit s hs
  · exact exists_unit_speed_reparametrization_self hJ hγ hsub hreg

end TauCeti.Manifold

end
