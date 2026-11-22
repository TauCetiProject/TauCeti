/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Quotient
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.WithMetric

/-!
# Conformal invariance of the Yamabe quotient

Let `g` be a smooth Riemannian metric on a manifold `M` without boundary of dimension `n ≠ 2`, and
let `ĝ = u ^ (4 / (n - 2)) g` for a positive function `u`. The Yamabe quotient
`Q_g(v) = (∫ (aₙ |grad v|² + Scal_g v²) dV_g) / (∫ |v| ^ pₙ dV_g) ^ (2 / pₙ)`
(`TauCeti.Yamabe.yamabeQuotient`) is conformally invariant:

`Q_ĝ(v) = Q_g(u v)`

for every compactly supported `C²` function `v`
(`Bundle.ContMDiffRiemannianMetric.yamabeQuotient_rescale`). The numerator is the conformally
invariant energy `TauCeti.Yamabe.integral_energy_rescale`, and the denominator is invariant by
`TauCeti.WithMetric.integral_abs_rpow_rescale_rpow`.

Two consequences on a closed manifold are recorded here.

* The quotient of the constant function `1` is the volume-normalized total scalar curvature
  `(∫ Scal_g dV_g) / Vol(g) ^ (2 / pₙ)` (`TauCeti.Yamabe.yamabeQuotient_one`, proved with the
  definition of the quotient). Applied to `ĝ`,
  conformal invariance gives `Q_g(u) = (∫ Scal_ĝ dV_ĝ) / Vol(ĝ) ^ (2 / pₙ)`. This is the
  integrated-by-parts form of
  `TauCeti.Yamabe.integral_scalarCurvature_rescale_div_riemannianTotalVolume_rpow`.
* Multiplication by `u` is a bijection of the positive smooth functions, so two conformal metrics
  have the same set of Yamabe quotients of positive smooth functions. Hence the infimum of `Q`
  over positive smooth functions depends only on the conformal class.

These are identities for differentiable functions. The extension of `v ↦ u v` to the Sobolev
space `H¹` and the invariance of the quotient on that weak domain are not treated here.

Each metric is installed as the `RiemannianBundle` instance of the tangent bundle of `M` when its
quotient is evaluated, as for `TauCeti.Yamabe.yamabeQuotient`. In the proofs the integrals are
compared on the metric-indexed copies `TauCeti.WithMetric g` and `TauCeti.WithMetric ĝ`, so no
two metric instances are ever installed on one carrier at once.

## Main results

In the namespace `Bundle.ContMDiffRiemannianMetric`, for dot notation on the metric `g`:

* `yamabeQuotient_eq_of_riemannianBundle_eq`: transports `yamabeQuotient` along an equality of
  installed fibre metrics.
* `yamabeQuotient_rescale_const`: `Q_{c g}(u) = Q_g(u)` for a positive constant `c`, in every
  dimension and without regularity or boundary assumptions.
* `yamabeQuotient_rescale`: `Q_ĝ(v) = Q_g(u v)`.
* `yamabeQuotient_eq_rescale_inv_mul`: for a positive smooth `u`, `Q_g(w) = Q_ĝ(w / u)`.
* `yamabeQuotient_eq_integral_scalarCurvature_rescale_div_riemannianTotalVolume_rpow`:
  `Q_g(u) = (∫ Scal_ĝ dV_ĝ) / Vol(ĝ) ^ (2 / pₙ)`.

In the namespace `TauCeti.Yamabe`:

* `image_yamabeQuotient_eq_of_mem_conformalClass`: conformal metrics have the same Yamabe
  quotients of positive smooth functions.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §2 (the
  conformal invariance of the Yamabe functional and its interpretation as normalized total scalar
  curvature).
-/

public section

open Bundle MeasureTheory Module TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti TauCeti.Yamabe

section Rescale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]

omit [I.Boundaryless] in
/-- The Yamabe quotient of `g`, written with integrals over the metric-indexed copy
`WithMetric g`. -/
private theorem yamabeQuotient_eq_withMetric
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (u : M → ℝ) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
     letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
       instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric;
     yamabeQuotient I u) =
      (∫ x, ((letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          conformalCoefficient (finrank ℝ E) * ‖mgradient I u x.ofWithMetric‖ ^ 2) +
          g.scalarCurvature x.ofWithMetric * u x.ofWithMetric ^ 2)
          ∂riemannianVolume I (WithMetric g)) /
        (∫ x, |u x.ofWithMetric| ^ criticalExponent (finrank ℝ E)
          ∂riemannianVolume I (WithMetric g)) ^ (2 / criticalExponent (finrank ℝ E)) := by
  rw [WithMetric.integral_comp_ofWithMetric g fun y ↦
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        conformalCoefficient (finrank ℝ E) * ‖mgradient I u y‖ ^ 2) +
        g.scalarCurvature y * u y ^ 2,
    WithMetric.integral_comp_ofWithMetric g fun y ↦ |u y| ^ criticalExponent (finrank ℝ E)]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  simp only [g.scalarCurvature_def]
  exact yamabeQuotient_def I u

omit [I.Boundaryless] in
/-- If the installed fibre metric is `g`, its Yamabe quotient is `yamabeQuotient I u`. This
transports the Yamabe quotient along an equality of fibre metrics, such as
`toRiemannianMetric_ofLE`, which cannot be rewritten inside the instance-dependent arguments. -/
theorem yamabeQuotient_eq_of_riemannianBundle_eq
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    [inst : RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (hg : RiemannianBundle.g = g.toRiemannianMetric) (u : M → ℝ) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
     letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
       instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric;
     yamabeQuotient I u) = yamabeQuotient I u := by
  obtain ⟨_⟩ := inst
  subst hg
  rfl

omit [I.Boundaryless] in
/-- **Homothety invariance of the Yamabe quotient.** Multiplying a smooth metric `g` by a positive
constant `c` leaves the Yamabe quotient `Q_{c g}(u) = Q_g(u)` unchanged in every dimension, without
regularity or boundary assumptions. -/
theorem yamabeQuotient_rescale_const
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {c : ℝ} (hc : 0 < c)
    (u : M → ℝ) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
       ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
     letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
       instIsContinuousRiemannianBundle
         (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toContinuousRiemannianMetric;
     yamabeQuotient I u) =
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
       letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
         instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric;
       yamabeQuotient I u) := by
  rw [yamabeQuotient_eq_withMetric, yamabeQuotient_eq_withMetric]
  rcases eq_or_ne (finrank ℝ E) 0 with hd | hd
  · have : Subsingleton E := (finrank_eq_zero_iff_of_free ℝ E).mp hd
    have hzero (h : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (y : M) :
        ((letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨h.toRiemannianMetric⟩;
          conformalCoefficient (finrank ℝ E) * ‖mgradient I u y‖ ^ 2) +
          h.scalarCurvature y * u y ^ 2) = 0 := by
      have : Subsingleton (TangentSpace I y) := inferInstanceAs (Subsingleton E)
      have hm : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨h.toRiemannianMetric⟩;
          ‖mgradient I u y‖ ^ 2) = 0 := by
        let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨h.toRiemannianMetric⟩
        rw [Subsingleton.elim (mgradient I u y) 0]
        exact sq_eq_zero_iff.2 norm_zero
      simp [hm, h.scalarCurvature_eq_zero_of_subsingleton y]
    simp only [hzero, integral_zero, zero_div]
  · have hd' : (finrank ℝ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
    rw [WithMetric.integral_riemannianVolume_rescale fun y ↦
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
           ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
         conformalCoefficient (finrank ℝ E) * ‖mgradient I u y‖ ^ 2) +
          (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).scalarCurvature y * u y ^ 2,
      WithMetric.integral_riemannianVolume_rescale fun y ↦
        |u y| ^ criticalExponent (finrank ℝ E)]
    have hnum (x : WithMetric g) :
        c ^ ((finrank ℝ E : ℝ) / 2) •
          ((letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
              ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
            conformalCoefficient (finrank ℝ E) * ‖mgradient I u x.ofWithMetric‖ ^ 2) +
            (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).scalarCurvature x.ofWithMetric *
              u x.ofWithMetric ^ 2) =
          (c ^ ((finrank ℝ E : ℝ) / 2) * c⁻¹) *
            ((letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩;
              conformalCoefficient (finrank ℝ E) * ‖mgradient I u x.ofWithMetric‖ ^ 2) +
              g.scalarCurvature x.ofWithMetric * u x.ofWithMetric ^ 2) := by
      rw [smul_eq_mul, norm_sq_mgradient_rescale_const g hc u, g.scalarCurvature_rescale_const hc]
      ring
    have hpow : (c ^ ((finrank ℝ E : ℝ) / 2)) ^ (2 / criticalExponent (finrank ℝ E)) =
        c ^ ((finrank ℝ E : ℝ) / 2) * c⁻¹ := by
      have hexp : (finrank ℝ E : ℝ) / 2 * (((finrank ℝ E : ℝ) - 2) / finrank ℝ E) =
          (finrank ℝ E : ℝ) / 2 - 1 := by field_simp
      rw [← Real.rpow_mul hc.le, two_div_criticalExponent, hexp, Real.rpow_sub hc, Real.rpow_one,
        div_eq_mul_inv]
    simp only [hnum, smul_eq_mul, integral_const_mul]
    rw [Real.mul_rpow (by positivity) (integral_nonneg fun _ ↦ by positivity), hpow,
      mul_div_mul_left _ _ (by positivity)]

/-- **Conformal invariance of the Yamabe quotient.** In dimension `n ≠ 2`, let `u` be a positive
function such that `ĝ = u ^ (4 / (n - 2)) g` is a smooth metric on a manifold without boundary.
Then `Q_ĝ(v) = Q_g(u v)` for every compactly supported `C²` function `v`. -/
theorem yamabeQuotient_rescale
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u : M → ℝ} (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))} {v : M → ℝ}
    (hv : ContMDiff I 𝓘(ℝ) 2 v) (hvc : HasCompactSupport v) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
       ⟨(g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos).toRiemannianMetric⟩;
     letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
       instIsContinuousRiemannianBundle (g.rescale _ hf hf_pos).toContinuousRiemannianMetric;
     yamabeQuotient I v) =
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
       letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
         instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric;
       yamabeQuotient I (u * v)) := by
  rw [yamabeQuotient_eq_withMetric, yamabeQuotient_eq_withMetric,
    integral_energy_rescale g hn hu_pos hv hvc, criticalExponent_def,
    WithMetric.integral_abs_rpow_rescale_rpow (fun x ↦ (hu_pos x).le)]
  simp only [Pi.mul_apply]

/-- **The Yamabe quotient after dividing by a positive function.** In dimension `n ≠ 2`, let `u`
be a positive smooth function on a manifold without boundary. Writing `w = u (w / u)`, the Yamabe
quotient of `g` at a compactly supported `C²` function `w` is the Yamabe quotient of
`ĝ = u ^ (4 / (n - 2)) g` at `w / u`. -/
theorem yamabeQuotient_eq_rescale_inv_mul
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hu_pos : ∀ x, 0 < u x) {w : M → ℝ}
    (hw : ContMDiff I 𝓘(ℝ) 2 w) (hwc : HasCompactSupport w) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
     letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
       instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric;
     yamabeQuotient I w) =
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
         ⟨(g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2)))
           (hu.rpow_const_of_ne (fun x ↦ (hu_pos x).ne') _)
           (fun x ↦ Real.rpow_pos_of_pos (hu_pos x) _)).toRiemannianMetric⟩;
       letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
         instIsContinuousRiemannianBundle (g.rescale _
           (hu.rpow_const_of_ne (fun x ↦ (hu_pos x).ne') _)
           (fun x ↦ Real.rpow_pos_of_pos (hu_pos x) _)).toContinuousRiemannianMetric;
       yamabeQuotient I fun x ↦ (u x)⁻¹ * w x) := by
  have huv : (u * fun x ↦ (u x)⁻¹ * w x) = w :=
    funext fun x ↦ mul_inv_cancel_left₀ (hu_pos x).ne' (w x)
  rw [g.yamabeQuotient_rescale hn hu_pos (v := fun x ↦ (u x)⁻¹ * w x)
    (((hu.of_le (by simp)).inv₀ fun x ↦ (hu_pos x).ne').mul hw) hwc.mul_left, huv]

end Rescale

section Compact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]

/-- **The Yamabe quotient is a normalized total scalar curvature.** On a closed manifold of
dimension `n ≠ 2`, let `u` be a positive function such that `ĝ = u ^ (4 / (n - 2)) g` is a smooth
metric. Then `Q_g(u) = (∫ Scal_ĝ dV_ĝ) / Vol(ĝ) ^ (2 / pₙ)`. -/
theorem yamabeQuotient_eq_integral_scalarCurvature_rescale_div_riemannianTotalVolume_rpow
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u : M → ℝ} (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))} :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
     letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
       instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric;
     yamabeQuotient I u) =
      (∫ x, (g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos).scalarCurvature
          x.ofWithMetric ∂riemannianVolume I (WithMetric (g.rescale _ hf hf_pos))) /
        riemannianTotalVolume I (WithMetric (g.rescale _ hf hf_pos)) ^
          (2 / criticalExponent (finrank ℝ E)) := by
  have h := g.yamabeQuotient_rescale hn hu_pos (hf := hf) (hf_pos := hf_pos)
    (v := fun _ ↦ 1) contMDiff_const (HasCompactSupport.of_compactSpace _)
  have hu1 : (u * fun _ ↦ (1 : ℝ)) = u := funext fun x ↦ mul_one (u x)
  have h0 (y : M) :
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf
          hf_pos).toRiemannianMetric⟩;
        ‖mgradient I (fun _ : M ↦ (1 : ℝ)) y‖) = 0 := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos).toRiemannianMetric⟩
    rw [mgradient_const]
    -- `simp` cannot use `norm_zero` here: the norm comes from the installed metric, and its zero
    -- agrees with that of the tangent space only up to unfolding instances.
    exact norm_zero
  rw [yamabeQuotient_eq_withMetric] at h
  simp only [h0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, one_pow,
    mul_one, zero_add, abs_one, Real.one_rpow, integral_const, smul_eq_mul,
    ← riemannianTotalVolume_def] at h
  -- Rewriting with `hu1` would fail: the goal mentions the installed metric, whose continuity
  -- instance matches it only up to unfolding, so its motive is not type correct reducibly.
  exact (congrArg _ hu1).symm.trans h.symm

end Compact

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti.Yamabe

section Compact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]

/-- **The Yamabe quotients of positive smooth functions are a conformal invariant.** On a closed
manifold of dimension `n ≠ 2`, two conformal smooth metrics `g` and `g'` have the same set of
Yamabe quotients `Q(w)` of positive smooth functions `w`, so the infimum of these quotients
depends only on the conformal class. -/
theorem image_yamabeQuotient_eq_of_mem_conformalClass (hn : finrank ℝ E ≠ 2)
    {g g' : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg' : g' ∈ g.conformalClass) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩;
     letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
       instIsContinuousRiemannianBundle g'.toContinuousRiemannianMetric;
     yamabeQuotient I '' {w : M → ℝ | ContMDiff I 𝓘(ℝ) ∞ w ∧ ∀ x, 0 < w x}) =
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
       letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
         instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric;
       yamabeQuotient I '' {w : M → ℝ | ContMDiff I 𝓘(ℝ) ∞ w ∧ ∀ x, 0 < w x}) := by
  have hn' : (finrank ℝ E : ℝ) - 2 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hn)
  obtain ⟨u, hu, hu_pos, rfl⟩ :=
    (ContMDiffRiemannianMetric.mem_conformalClass_iff_exists_rpow
      (div_ne_zero four_ne_zero hn')).mp hg'
  ext q
  constructor
  · rintro ⟨w, ⟨hw, hw_pos⟩, rfl⟩
    exact ⟨u * w, ⟨hu.mul hw, fun x ↦ mul_pos (hu_pos x) (hw_pos x)⟩,
      (g.yamabeQuotient_rescale hn hu_pos (hw.of_le (by simp))
        (HasCompactSupport.of_compactSpace _)).symm⟩
  · rintro ⟨w, ⟨hw, hw_pos⟩, rfl⟩
    have hwu : ContMDiff I 𝓘(ℝ) ∞ (w / u) := hw.div₀ hu fun x ↦ (hu_pos x).ne'
    have h : u * (w / u) = w := funext fun x ↦ mul_div_cancel₀ (w x) (hu_pos x).ne'
    exact ⟨w / u, ⟨hwu, fun x ↦ div_pos (hw_pos x) (hu_pos x)⟩,
      (g.yamabeQuotient_rescale hn hu_pos (hwu.of_le (by simp))
        (HasCompactSupport.of_compactSpace _)).trans (congrArg _ h)⟩

end Compact

end TauCeti.Yamabe
