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

* `yamabeQuotient_rescale`: `Q_ĝ(v) = Q_g(u v)`.
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
