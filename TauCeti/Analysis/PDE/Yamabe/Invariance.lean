/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.SobolevQuotient
public import TauCeti.Analysis.PDE.Yamabe.Quotient
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Volume
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace

/-!
# Geometric and conformal invariance of the Yamabe quotient, and its model values

This file establishes the geometric and conformal transformation properties of the Yamabe quotient
`TauCeti.Yamabe.yamabeQuotient`, connects it to the volume-normalized total scalar curvature and
constant-scalar-curvature metrics on a conformal class, and evaluates it on flat inner product
spaces, Aubin–Talenti bubbles, and round spheres.

1. **Isometry, pullback, and constant-scale invariance.** Because a smooth Riemannian isometry
   `Φ : (M, g) → (N, h)` preserves gradient norms
   (`TauCeti.RiemannianIsometry.norm_mgradient_comp`),
   scalar curvature (`TauCeti.IsLocalRiemannianIsometry.scalarCurvature_map`), and Riemannian volume
   (`TauCeti.RiemannianIsometry.measurePreserving_riemannianVolume`), it preserves the Yamabe
   quotient unconditionally: `Q_g(u ∘ Φ) = Q_h(u)` for every function `u : N → ℝ`. Consequently,
   pulling a smooth metric back along a diffeomorphism preserves `Q`, and multiplying a metric by
   any positive constant `c > 0` leaves `Q_{c g} = Q_g` unchanged in every dimension.

2. **Conformal invariance and the geometric Yamabe functional.** On a manifold without boundary of
   dimension `n ≠ 2`, for a positive conformal factor `ĝ = u ^ (4 / (n - 2)) g` and any compactly
   supported `C²` function `v` (every `C²` function when `M` is compact),
   `Q_ĝ(v) = Q_g(u v)`. Taking `v = 1` on a closed manifold identifies `Q_g(u)` with the
   volume-normalized total scalar curvature `(∫ Scal_ĝ dV_ĝ) / Vol(ĝ) ^ (2 / pₙ)` of `ĝ`, and in
   dimension `n > 2` shows that `u` is a critical point of `Q_g` along smooth variations if and only
   if `ĝ` has constant scalar curvature.

3. **Canonical model values and stereographic bridge.** On a finite-dimensional real inner product
   space `F` carrying its standard flat metric, `Q(u)` reduces to the Euclidean Sobolev quotient
   `(aₙ ∫ ‖du‖²) / (∫ |u| ^ pₙ) ^ (2 / pₙ)`, and every Yamabe bubble `U_{t,b}` (`n > 2`, `t > 0`)
   attains the sphere Yamabe constant `Y(Sⁿ) = n (n - 1) |Sⁿ| ^ (2 / n)`. On the unit round sphere
   `Sⁿ` and on the round sphere `Sⁿ(r)` of any radius `r > 0`, every nonzero constant function
   likewise has Yamabe quotient `Y(Sⁿ)` (`n ≠ 2`), while in stereographic coordinates
   `stereographic' n v` the Riemannian volume Jacobian on `Sⁿ` is `U_{2,0} ^ pₙ`, identifying
   critical `L ^ pₙ` integrals on `Sⁿ` with Euclidean `L ^ pₙ` integrals weighted by `U_{2,0}`.

## Main results

* `TauCeti.RiemannianIsometry.yamabeQuotient_comp`,
  `TauCeti.WithMetric.yamabeQuotient_comp_ofWithMetric`, and
  `TauCeti.Yamabe.yamabeQuotient_pullback`: isometry and diffeomorphism-pullback invariance of the
  Yamabe quotient.
* `TauCeti.Yamabe.yamabeQuotient_rescale_const`: invariance under constant positive metric
  rescaling `c g`.
* `TauCeti.Yamabe.yamabeQuotient_rescale` and
  `TauCeti.Yamabe.yamabeQuotient_rescale_of_compactSpace`: conformal invariance
  `Q_ĝ(v) = Q_g(u v)`.
* `TauCeti.Yamabe.integral_scalarCurvature_rescale_div_riemannianTotalVolume_rpow_eq_yamabeQuotient`
  — `(∫ Scal_ĝ dV_ĝ) / Vol(ĝ) ^ (2 / pₙ) = Q_g(u)` on a closed manifold (`n ≠ 2`).
* `TauCeti.Yamabe.forall_hasDerivAt_yamabeQuotient_add_smul_iff_exists_scalarCurvature_rescale_eq`:
  positive smooth critical points of `Q_g` on a closed manifold (`n > 2`) are the conformal factors
  of constant-scalar-curvature metrics.
* `TauCeti.Yamabe.yamabeQuotient_model_space` and `TauCeti.Yamabe.yamabeQuotient_bubble`:
  Euclidean Sobolev form of `Q` and `Q(U_{t,b}) = Y(Sⁿ)`.
* `TauCeti.Yamabe.yamabeQuotient_sphere_one`, `TauCeti.Yamabe.yamabeQuotient_sphere_const`, and
  `TauCeti.Yamabe.yamabeQuotient_sphereRoundMetricOfRadius_const`: `Q(c) = Y(Sⁿ)` on unit and
  radius-`r` round spheres.
* `TauCeti.Yamabe.normDet_fderiv_coe_comp_stereographic'_symm_eq_bubble_rpow_criticalExponent`,
  `TauCeti.Yamabe.integral_riemannianVolume_sphere_eq_integral_bubble_rpow_criticalExponent`, and
  `TauCeti.Yamabe.integral_abs_rpow_criticalExponent_sphere_eq_stereographic'`: stereographic
  Jacobian `U_{2,0} ^ pₙ` and critical `L ^ pₙ` pullback from `Sⁿ` to `ℝⁿ`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  §§2–3.
-/

public section

open Bundle MeasureTheory Metric Module TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

section Isometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ∞ M]

/-- **Isometry invariance of the Yamabe quotient.** A smooth Riemannian isometry `Φ : M → N`
preserves the Yamabe quotient of every function `u : N → ℝ`. -/
theorem TauCeti.RiemannianIsometry.yamabeQuotient_comp
    [MeasurableSpace M] [BorelSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N] [SigmaCompactSpace N]
    [IsManifold J ∞ N] [MeasurableSpace N] [BorelSpace N]
    [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
    [IsContMDiffRiemannianBundle J ∞ E (fun y : N ↦ TangentSpace J y)]
    [IsContinuousRiemannianBundle E (fun y : N ↦ TangentSpace J y)]
    (Φ : RiemannianIsometry I J M N) (u : N → ℝ) :
    Yamabe.yamabeQuotient I (u ∘ Φ) = Yamabe.yamabeQuotient J u := by
  have hmp : MeasurePreserving Φ (riemannianVolume I M) (riemannianVolume J N) :=
    Φ.measurePreserving_riemannianVolume
  have hemb : MeasurableEmbedding Φ := Φ.toDiffeomorph.toHomeomorph.measurableEmbedding
  rw [Yamabe.yamabeQuotient_def, Yamabe.yamabeQuotient_def]
  congr 1
  · have hnum (x : M) :
        Yamabe.conformalCoefficient (finrank ℝ E) * ‖mgradient I (u ∘ Φ) x‖ ^ 2 +
          (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (u ∘ Φ) x ^ 2 =
        Yamabe.conformalCoefficient (finrank ℝ E) * ‖mgradient J u (Φ x)‖ ^ 2 +
          (CovariantDerivative.leviCivitaConnection J N).scalarCurvature (Φ x) * u (Φ x) ^ 2 := by
      simp only [Function.comp_apply, Φ.norm_mgradient_comp u x,
        Φ.isLocalRiemannianIsometry.scalarCurvature_map x]
    simp_rw [hnum]
    exact hmp.integral_comp hemb fun y ↦
      Yamabe.conformalCoefficient (finrank ℝ E) * ‖mgradient J u y‖ ^ 2 +
        (CovariantDerivative.leviCivitaConnection J N).scalarCurvature y * u y ^ 2
  · congr 1
    exact hmp.integral_comp hemb fun y ↦ |u y| ^ Yamabe.criticalExponent (finrank ℝ E)

/-- Evaluating the Yamabe quotient on the metric-indexed copy `WithMetric g` agrees with evaluating
it on `M` with `g` installed as its `RiemannianBundle` instance. -/
theorem TauCeti.WithMetric.yamabeQuotient_comp_ofWithMetric
    [MeasurableSpace M] [BorelSpace M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (u : M → ℝ) :
    Yamabe.yamabeQuotient I (u ∘ (ofWithMetric : WithMetric g → M)) =
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
        Bundle.instIsContMDiffRiemannianBundle g
      letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        Bundle.instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
      Yamabe.yamabeQuotient I u) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    Bundle.instIsContMDiffRiemannianBundle g
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Bundle.instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  rw [← coe_riemannianIsometry g]
  exact (riemannianIsometry g).yamabeQuotient_comp u

/-- When `g` agrees with the installed `RiemannianBundle` instance on `M`, the Yamabe quotient on
`WithMetric g` equals the Yamabe quotient on `M`. -/
theorem TauCeti.WithMetric.yamabeQuotient_comp_ofWithMetric_of_riemannianBundle_eq
    [MeasurableSpace M] [BorelSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : RiemannianBundle.g = g.toRiemannianMetric) (u : M → ℝ) :
    Yamabe.yamabeQuotient I (u ∘ (ofWithMetric : WithMetric g → M)) =
      Yamabe.yamabeQuotient I u := by
  rw [← coe_riemannianIsometryOfRiemannianBundleEq hg]
  exact (riemannianIsometryOfRiemannianBundleEq hg).yamabeQuotient_comp u

end Isometry

namespace TauCeti.Yamabe

section Invariance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ∞ M]

/-- **Pullback invariance of the Yamabe quotient.** Pulling a smooth metric `g` on `N` back along a
smooth diffeomorphism `Φ : M → N` preserves the Yamabe quotient: `Q_{Φ^* g}(u ∘ Φ) = Q_g(u)`. -/
theorem yamabeQuotient_pullback
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N] [SigmaCompactSpace N]
    [IsManifold J ∞ N]
    (g : ContMDiffRiemannianMetric J ∞ E (fun y : N ↦ TangentSpace J y))
    (Φ : M ≃ₘ^∞⟮I, J⟯ N) (u : N → ℝ) :
    yamabeQuotient I
        ((u ∘ Φ) ∘ (WithMetric.ofWithMetric :
          WithMetric (g.pullback Φ Φ.contMDiff
            fun _ ↦ (Φ.isInvertible_mfderiv (WithTop.coe_ne_zero.2 top_ne_zero)).injective) → M)) =
      yamabeQuotient J (u ∘ (WithMetric.ofWithMetric : WithMetric g → N)) := by
  have hf : ContMDiff I J (∞ + 1) Φ := Φ.contMDiff
  have hinj : ∀ x, Function.Injective (mfderiv I J Φ x) :=
    fun _ ↦ (Φ.isInvertible_mfderiv (WithTop.coe_ne_zero.2 top_ne_zero)).injective
  let _ : MeasurableSpace M := borel M
  have _ : BorelSpace M := ⟨rfl⟩
  let _ : MeasurableSpace N := borel N
  have _ : BorelSpace N := ⟨rfl⟩
  rw [WithMetric.yamabeQuotient_comp_ofWithMetric, WithMetric.yamabeQuotient_comp_ofWithMetric]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.pullback Φ hf hinj).toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    Bundle.instIsContMDiffRiemannianBundle (g.pullback Φ hf hinj)
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Bundle.instIsContinuousRiemannianBundle (g.pullback Φ hf hinj).toContinuousRiemannianMetric
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle J ∞ E (fun y : N ↦ TangentSpace J y) :=
    Bundle.instIsContMDiffRiemannianBundle g
  let _ : IsContinuousRiemannianBundle E (fun y : N ↦ TangentSpace J y) :=
    Bundle.instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have h := (g.pullbackRiemannianIsometry Φ hf hinj).yamabeQuotient_comp u
  rwa [g.coe_pullbackRiemannianIsometry] at h

/-- Rewriting `yamabeQuotient` on `WithMetric g` with the gradient norm and scalar curvature
evaluated on `M` against `g`. -/
private theorem yamabeQuotient_comp_ofWithMetric_eq_div
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (w : M → ℝ) :
    yamabeQuotient I (w ∘ (WithMetric.ofWithMetric : WithMetric g → M)) =
      (∫ x, ((letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
          conformalCoefficient (finrank ℝ E) * ‖mgradient I w x.ofWithMetric‖ ^ 2) +
          g.scalarCurvature x.ofWithMetric * w x.ofWithMetric ^ 2)
          ∂riemannianVolume I (WithMetric g)) /
        (∫ x, |w x.ofWithMetric| ^ criticalExponent (finrank ℝ E)
          ∂riemannianVolume I (WithMetric g)) ^ (2 / criticalExponent (finrank ℝ E)) := by
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
    Bundle.instIsContMDiffRiemannianBundle g
  let Φ := WithMetric.riemannianIsometry g
  have hΦ (x : WithMetric g) : Φ x = x.ofWithMetric :=
    congr_fun (WithMetric.coe_riemannianIsometry g) x
  rw [yamabeQuotient_def]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  dsimp only
  have hgrad : ‖mgradient I (w ∘ WithMetric.ofWithMetric) x‖ = ‖mgradient I w x.ofWithMetric‖ := by
    rw [← WithMetric.coe_riemannianIsometry g,
      (WithMetric.riemannianIsometry g).norm_mgradient_comp w x,
      WithMetric.coe_riemannianIsometry]
  have hscal : (CovariantDerivative.leviCivitaConnection I (WithMetric g)).scalarCurvature x =
      g.scalarCurvature x.ofWithMetric := by
    rw [← Φ.isLocalRiemannianIsometry.scalarCurvature_map x, hΦ, g.scalarCurvature_def]
  rw [hgrad, hscal, Function.comp_apply]

/-- **Scale invariance under constant metric rescaling.** Multiplying a smooth Riemannian metric `g`
by a positive constant `c > 0` leaves the Yamabe quotient of every function `u : M → ℝ` unchanged,
in every dimension. -/
theorem yamabeQuotient_rescale_const
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (u : M → ℝ) :
    yamabeQuotient I
        (u ∘ (WithMetric.ofWithMetric :
          WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) → M)) =
      yamabeQuotient I (u ∘ (WithMetric.ofWithMetric : WithMetric g → M)) := by
  set ĝ := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  rcases eq_or_ne (finrank ℝ E) 0 with h0 | h0
  · have hzero : ∀ (g' : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)),
        yamabeQuotient I (u ∘ (WithMetric.ofWithMetric : WithMetric g' → M)) = 0 := by
      intro g'
      rw [yamabeQuotient_def]
      have hnum : ∀ x : WithMetric g',
          conformalCoefficient (finrank ℝ E) *
              ‖mgradient I (u ∘ WithMetric.ofWithMetric) x‖ ^ 2 +
            (CovariantDerivative.leviCivitaConnection I (WithMetric g')).scalarCurvature x *
              (u ∘ WithMetric.ofWithMetric) x ^ 2 = 0 := by
        intro x
        have hdim : finrank ℝ (TangentSpace I x) = 0 := h0
        have : Subsingleton (TangentSpace I x) := Module.finrank_zero_iff.mp hdim
        have hgrad : mgradient I (u ∘ WithMetric.ofWithMetric) x = 0 := Subsingleton.elim _ _
        have hscal :
            (CovariantDerivative.leviCivitaConnection I (WithMetric g')).scalarCurvature x = 0 := by
          rw [CovariantDerivative.scalarCurvature_eq_sum _ x (stdOrthonormalBasis ℝ _)]
          simp [hdim]
        simp [hgrad, hscal]
      simp_rw [hnum]
      rw [integral_zero, zero_div]
    rw [hzero ĝ, hzero g]
  · set N : ℝ := (finrank ℝ E : ℝ)
    set p : ℝ := criticalExponent (finrank ℝ E)
    have hN0 : N ≠ 0 := Nat.cast_ne_zero.2 h0
    have hgrad_sq (y : M) :
        (letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨ĝ.toRiemannianMetric⟩;
          ‖mgradient I u y‖ ^ 2) =
          c⁻¹ * (letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩;
            ‖mgradient I u y‖ ^ 2) := by
      have h1 : ‖mgradient I (u ∘ WithMetric.ofWithMetric) (WithMetric.toWithMetric ĝ y)‖ ^ 2 =
          (letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨ĝ.toRiemannianMetric⟩;
            ‖mgradient I u y‖ ^ 2) := by
        let _ : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨ĝ.toRiemannianMetric⟩
        rw [← WithMetric.coe_riemannianIsometry ĝ,
          (WithMetric.riemannianIsometry ĝ).norm_mgradient_comp u (WithMetric.toWithMetric ĝ y),
          WithMetric.coe_riemannianIsometry, WithMetric.ofWithMetric_toWithMetric]
      have h2 : ‖mgradient I (u ∘ WithMetric.ofWithMetric) (WithMetric.toWithMetric g y)‖ ^ 2 =
          (letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩;
            ‖mgradient I u y‖ ^ 2) := by
        let _ : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩
        rw [← WithMetric.coe_riemannianIsometry g,
          (WithMetric.riemannianIsometry g).norm_mgradient_comp u (WithMetric.toWithMetric g y),
          WithMetric.coe_riemannianIsometry, WithMetric.ofWithMetric_toWithMetric]
      rw [← h1, ← h2, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        WithMetric.inner_mgradient_rescale]
    let φ : M → ℝ := fun y ↦ c⁻¹ *
      ((letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩;
          conformalCoefficient (finrank ℝ E) * ‖mgradient I u y‖ ^ 2) +
        g.scalarCurvature y * u y ^ 2)
    have hnum_eq :
        ∫ x : WithMetric ĝ,
            ((letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨ĝ.toRiemannianMetric⟩;
                conformalCoefficient (finrank ℝ E) * ‖mgradient I u x.ofWithMetric‖ ^ 2) +
              ĝ.scalarCurvature x.ofWithMetric * u x.ofWithMetric ^ 2)
            ∂riemannianVolume I (WithMetric ĝ) =
          (c ^ (N / 2) * c⁻¹) *
            ∫ x : WithMetric g,
              ((letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
                  conformalCoefficient (finrank ℝ E) * ‖mgradient I u x.ofWithMetric‖ ^ 2) +
                g.scalarCurvature x.ofWithMetric * u x.ofWithMetric ^ 2)
              ∂riemannianVolume I (WithMetric g) := by
      have hcongr (x : WithMetric ĝ) :
          (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨ĝ.toRiemannianMetric⟩;
              conformalCoefficient (finrank ℝ E) * ‖mgradient I u x.ofWithMetric‖ ^ 2) +
            ĝ.scalarCurvature x.ofWithMetric * u x.ofWithMetric ^ 2 = φ x.ofWithMetric := by
        dsimp only [φ]
        rw [hgrad_sq x.ofWithMetric, g.scalarCurvature_rescale_const hc x.ofWithMetric]
        ring
      simp_rw [hcongr]
      rw [WithMetric.integral_riemannianVolume_rescale φ]
      simp only [φ, smul_eq_mul, ← mul_assoc]
      exact integral_const_mul _ _
    have hden_eq :
        ∫ x : WithMetric ĝ, |u x.ofWithMetric| ^ p ∂riemannianVolume I (WithMetric ĝ) =
          c ^ (N / 2) *
            ∫ x : WithMetric g, |u x.ofWithMetric| ^ p ∂riemannianVolume I (WithMetric g) := by
      simpa only [smul_eq_mul, integral_const_mul] using
        WithMetric.integral_riemannianVolume_rescale (g := g) (f := fun _ ↦ c)
          (hf := contMDiff_const) (hf_pos := fun _ ↦ hc) fun y ↦ |u y| ^ p
    have hp : 2 / p = (N - 2) / N := two_div_criticalExponent _
    have hmul : N / 2 * ((N - 2) / N) = N / 2 - 1 := by field_simp
    have hexp : (c ^ (N / 2)) ^ (2 / p) = c ^ (N / 2) * c⁻¹ := by
      rw [← Real.rpow_mul hc.le, hp, hmul, Real.rpow_sub hc, Real.rpow_one, div_eq_mul_inv]
    rw [yamabeQuotient_comp_ofWithMetric_eq_div, yamabeQuotient_comp_ofWithMetric_eq_div,
      hnum_eq, hden_eq,
      Real.mul_rpow (Real.rpow_nonneg hc.le _)
        (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _),
      hexp, mul_div_mul_left _ _ (mul_ne_zero (Real.rpow_pos_of_pos hc _).ne' (inv_ne_zero hc.ne'))]

/-- **Conformal invariance of the Yamabe quotient.** On a manifold without boundary of dimension
`n ≠ 2`, let `u` be a positive function such that `ĝ = u ^ (4 / (n - 2)) g` is a smooth metric.
Then for every compactly supported `C²` function `v`, `Q_ĝ(v) = Q_g(u v)`. -/
theorem yamabeQuotient_rescale [I.Boundaryless]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u : M → ℝ} (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))} {v : M → ℝ}
    (hv : ContMDiff I 𝓘(ℝ) 2 v) (hvc : HasCompactSupport v) :
    yamabeQuotient I
        (v ∘ (WithMetric.ofWithMetric : WithMetric (g.rescale _ hf hf_pos) → M)) =
      yamabeQuotient I ((u * v) ∘ (WithMetric.ofWithMetric : WithMetric g → M)) := by
  rw [yamabeQuotient_comp_ofWithMetric_eq_div, yamabeQuotient_comp_ofWithMetric_eq_div,
    integral_energy_rescale g hn hu_pos hv hvc]
  congr 2
  simpa only [criticalExponent_def, Pi.mul_apply] using
    WithMetric.integral_abs_rpow_rescale_rpow (g := g) (hf := hf) (hf_pos := hf_pos)
      (fun x ↦ (hu_pos x).le) v

/-- **Conformal invariance of the Yamabe quotient on a closed manifold.** On a compact manifold
without boundary of dimension `n ≠ 2`, for `ĝ = u ^ (4 / (n - 2)) g` with `u > 0` and every `C²`
function `v`, `Q_ĝ(v) = Q_g(u v)`. -/
theorem yamabeQuotient_rescale_of_compactSpace [CompactSpace M] [I.Boundaryless]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u : M → ℝ} (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))} {v : M → ℝ}
    (hv : ContMDiff I 𝓘(ℝ) 2 v) :
    yamabeQuotient I
        (v ∘ (WithMetric.ofWithMetric : WithMetric (g.rescale _ hf hf_pos) → M)) =
      yamabeQuotient I ((u * v) ∘ (WithMetric.ofWithMetric : WithMetric g → M)) :=
  yamabeQuotient_rescale g hn hu_pos hv (.of_compactSpace v)

end Invariance

section ConstantAndTotalScalarCurvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  [IsManifold I ∞ M]

/-- **Volume-normalized total scalar curvature equals the Yamabe quotient.** On a closed manifold of
dimension `n ≠ 2`, for a positive function `u` whose conformal metric `ĝ = u ^ (4 / (n - 2)) g` is
smooth, `(∫ Scal_ĝ dV_ĝ) / Vol(ĝ) ^ (2 / pₙ) = Q_g(u)`. -/
theorem integral_scalarCurvature_rescale_div_riemannianTotalVolume_rpow_eq_yamabeQuotient
    [I.Boundaryless]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u : M → ℝ} (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))} :
    (∫ x, (g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos).scalarCurvature
          x.ofWithMetric ∂riemannianVolume I (WithMetric (g.rescale _ hf hf_pos))) /
        riemannianTotalVolume I (WithMetric (g.rescale _ hf hf_pos)) ^
          (2 / criticalExponent (finrank ℝ E)) =
      yamabeQuotient I (u ∘ (WithMetric.ofWithMetric : WithMetric g → M)) := by
  have h := yamabeQuotient_rescale_of_compactSpace (hf := hf) (hf_pos := hf_pos) g hn hu_pos
    (v := 1) contMDiff_const
  have h1 : ((1 : M → ℝ) ∘ (WithMetric.ofWithMetric :
      WithMetric (g.rescale _ hf hf_pos) → M)) = fun _ ↦ (1 : ℝ) := by
    ext
    simp
  rw [mul_one, h1] at h
  rw [← h, yamabeQuotient_one]
  congr 2
  ext x
  let ĝ := g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
    Bundle.instIsContMDiffRiemannianBundle ĝ
  have hΦ : (WithMetric.riemannianIsometry ĝ) x = x.ofWithMetric :=
    congr_fun (WithMetric.coe_riemannianIsometry ĝ) x
  rw [← (WithMetric.riemannianIsometry ĝ).isLocalRiemannianIsometry.scalarCurvature_map x, hΦ]
  exact ĝ.scalarCurvature_def x.ofWithMetric

/-- **Geometric Euler–Lagrange characterization of the Yamabe quotient.** On a closed manifold of
dimension `n > 2`, a positive function `u` for which `ĝ = u ^ (4 / (n - 2)) g` is a smooth metric is
a critical point of the Yamabe quotient in every smooth direction if and only if `ĝ` has constant
scalar curvature. -/
theorem forall_hasDerivAt_yamabeQuotient_add_smul_iff_exists_scalarCurvature_rescale_eq
    [I.Boundaryless]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 2 < finrank ℝ E) {u : M → ℝ} (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))} :
    (∀ v : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ v →
        HasDerivAt (fun t : ℝ ↦ yamabeQuotient I
          ((u + t • v) ∘ (WithMetric.ofWithMetric : WithMetric g → M))) 0 0) ↔
      ∃ c : ℝ, ∀ x,
        (g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos).scalarCurvature x =
          c := by
  rcases isEmpty_or_nonempty M with hM | hM
  · have : IsEmpty (WithMetric g) := (WithMetric.equiv g).isEmpty
    have hzero (w : WithMetric g → ℝ) : yamabeQuotient I w = 0 := by
      rw [yamabeQuotient_def, integral_of_isEmpty, zero_div]
    simp only [hzero]
    exact ⟨fun _ ↦ ⟨0, isEmptyElim⟩, fun _ _ _ ↦ hasDerivAt_const 0 0⟩
  · let _ : MeasurableSpace M := borel M
    have _ : BorelSpace M := ⟨rfl⟩
    simp_rw [WithMetric.yamabeQuotient_comp_ofWithMetric]
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
      Bundle.instIsContMDiffRiemannianBundle g
    let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      Bundle.instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    have hn' : (finrank ℝ E : ℝ) - 2 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hn.ne')
    have hu : ContMDiff I 𝓘(ℝ) 2 u :=
      (hf.of_rpow_const (div_ne_zero four_ne_zero hn') hu_pos).of_le (by simp)
    have hu0 : u ≠ 0 := by
      obtain ⟨x₀⟩ := hM
      intro h0
      exact (hu_pos x₀).ne' (congrFun h0 x₀)
    rw [forall_hasDerivAt_yamabeQuotient_add_smul_iff_exists_conformalLaplacian_eq_of_nonneg hn hu
      hu0 fun x ↦ (hu_pos x).le]
    simp_rw [scalarCurvature_rescale_eq_iff_conformalLaplacian_eq (hf := hf) (hf_pos := hf_pos) g
      hn.ne' hu_pos]

end ConstantAndTotalScalarCurvature

section ModelValues

section Euclidean

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **Yamabe quotient on a flat inner product space.** Carrying its standard flat Riemannian metric,
a finite-dimensional real inner product space `F` has vanishing scalar curvature and Riemannian
volume equal to Lebesgue `volume`, so `Q(u)` reduces to the Euclidean Sobolev quotient
`(aₙ ∫ ‖du‖²) / (∫ |u| ^ pₙ) ^ (2 / pₙ)`. -/
theorem yamabeQuotient_model_space (u : F → ℝ) :
    yamabeQuotient 𝓘(ℝ, F) u =
      (conformalCoefficient (finrank ℝ F) * ∫ x, ‖fderiv ℝ u x‖ ^ 2) /
        (∫ x, |u x| ^ criticalExponent (finrank ℝ F)) ^
          (2 / criticalExponent (finrank ℝ F)) := by
  have hnorm (x : F) : ‖mgradient 𝓘(ℝ, F) u x‖ = ‖fderiv ℝ u x‖ := by
    rw [norm_mgradient_eq_norm_gradient_of_eq rfl, gradient, LinearIsometryEquiv.norm_map]
  rw [yamabeQuotient_def, riemannianVolume_model_space]
  simp only [hnorm, scalarCurvature_leviCivitaConnection_model_space, zero_mul, add_zero,
    integral_const_mul]

/-- **Yamabe quotient of the Aubin–Talenti bubbles.** On an `n`-dimensional real inner product space
with `n > 2`, every bubble `U_{t,b}` of scale `t > 0` centred at `b` has Yamabe quotient equal to
the sphere Yamabe constant `Y(Sⁿ)`. -/
theorem yamabeQuotient_bubble (hn : 2 < finrank ℝ F) {t : ℝ} (ht : 0 < t) (b : F) :
    yamabeQuotient 𝓘(ℝ, F) (bubble t b) = sphereYamabeConstant (finrank ℝ F) := by
  have habs (x : F) : |bubble t b x| = bubble t b x := abs_of_pos (bubble_pos ht b x)
  rw [yamabeQuotient_model_space]
  simp_rw [habs]
  rw [conformalCoefficient_mul_integral_norm_fderiv_bubble_sq_eq_sphereYamabeConstant hn ht b,
    integral_bubble_rpow_criticalExponent_eq_roundSphereVolume (by omega) hn.ne' ht b,
    mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos (roundSphereVolume_pos _) _).ne']

end Euclidean

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- On the unit round `n`-sphere, the constant function `1` has Yamabe quotient `Y(Sⁿ)` in every
dimension `n`. -/
@[simp]
theorem yamabeQuotient_sphere_one [MeasurableSpace E] [BorelSpace E] :
    yamabeQuotient (𝓡 n) (fun _ : sphere (0 : E) 1 ↦ (1 : ℝ)) = sphereYamabeConstant n := by
  rw [yamabeQuotient_one, finrank_euclideanSpace_fin, riemannianTotalVolume_sphere]
  simp_rw [scalarCurvature_sphere]
  rw [integral_const, smul_eq_mul, ← riemannianTotalVolume_def, riemannianTotalVolume_sphere,
    mul_comm (roundSphereVolume n)]
  rcases eq_or_ne n 0 with rfl | hn₀
  · simp [sphereYamabeConstant_def]
  · exact (sphereYamabeConstant_eq_div hn₀).symm

/-- **Yamabe quotient of constant functions on the unit round sphere.** In every dimension `n ≠ 2`,
every nonzero constant function on the unit round `n`-sphere has Yamabe quotient equal to the sphere
Yamabe constant `Y(Sⁿ)`. -/
theorem yamabeQuotient_sphere_const [MeasurableSpace E] [BorelSpace E] (hn : n ≠ 2)
    {c : ℝ} (hc : c ≠ 0) :
    yamabeQuotient (𝓡 n) (fun _ : sphere (0 : E) 1 ↦ c) = sphereYamabeConstant n := by
  rcases eq_or_ne n 0 with rfl | hn₀
  · rw [yamabeQuotient_def, finrank_euclideanSpace_fin]
    simp [mgradient_const, scalarCurvature_sphere, sphereYamabeConstant_def]
  · have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E = n + 1)
    have : Nonempty (sphere (0 : E) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
    rw [yamabeQuotient_const_of_scalarCurvature_eq_const
      (by rwa [finrank_euclideanSpace_fin]) (by rwa [finrank_euclideanSpace_fin])
      scalarCurvature_sphere hc,
      riemannianTotalVolume_sphere, finrank_euclideanSpace_fin, sphereYamabeConstant_def]

/-- **Yamabe quotient of constant functions on the round sphere of radius `r`.** Carrying the round
metric `TauCeti.sphereRoundMetricOfRadius r hr` of any radius `r > 0`, every nonzero constant
function on the `n`-sphere (`n ≠ 2`) has Yamabe quotient `Y(Sⁿ)`. -/
theorem yamabeQuotient_sphereRoundMetricOfRadius_const (hn : n ≠ 2) {r : ℝ} (hr : 0 < r)
    {c : ℝ} (hc : c ≠ 0) :
    yamabeQuotient (𝓡 n)
        (fun _ : WithMetric (sphereRoundMetricOfRadius (E := E) (n := n) r hr) ↦ c) =
      sphereYamabeConstant n := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have hcomp :
      (fun _ : WithMetric (sphereRoundMetricOfRadius (E := E) (n := n) r hr) ↦ c) =
        (fun _ : sphere (0 : E) 1 ↦ c) ∘
          (WithMetric.ofWithMetric :
            WithMetric (sphereRoundMetricOfRadius (E := E) (n := n) r hr) → sphere (0 : E) 1) := by
    ext
    simp
  rw [hcomp, sphereRoundMetricOfRadius_def, yamabeQuotient_rescale_const _ (pow_pos hr 2),
    WithMetric.yamabeQuotient_comp_ofWithMetric_of_riemannianBundle_eq
      (ContMDiffRiemannianMetric.toRiemannianMetric_ofLE _ _).symm,
    yamabeQuotient_sphere_const hn hc]

omit [FiniteDimensional ℝ E] in
/-- **Stereographic volume Jacobian as a bubble power.** In dimension `n ≠ 2`, the Euclidean
Jacobian of inverse stereographic projection `(↑) ∘ (stereographic' n v).symm` at `y ∈ ℝⁿ`
equals `U_{2,0}(y) ^ pₙ`, where `U_{2,0}` is the Yamabe bubble of scale `2` centred at the
origin. -/
theorem normDet_fderiv_coe_comp_stereographic'_symm_eq_bubble_rpow_criticalExponent
    (hn : n ≠ 2) (v : sphere (0 : E) 1) (y : EuclideanSpace ℝ (Fin n)) :
    (fderiv ℝ (((↑) : sphere (0 : E) 1 → E) ∘ (stereographic' n v).symm) y).normDet =
      bubble 2 (0 : EuclideanSpace ℝ (Fin n)) y ^ criticalExponent n := by
  have hb := bubble_rpow_criticalExponent (E := EuclideanSpace ℝ (Fin n))
    (by rwa [finrank_euclideanSpace_fin]) two_pos 0 y
  rw [finrank_euclideanSpace_fin, sub_zero] at hb
  rw [normDet_fderiv_coe_comp_stereographic'_symm, hb]
  congr 1
  ring

/-- **Stereographic integration weighted by the Yamabe bubble.** For `1 ≤ n` with `n ≠ 2` and any
pole `v ∈ Sⁿ`, integrating a Banach-space-valued function over `Sⁿ` against its Riemannian volume
equals integrating its stereographic expression over `ℝⁿ` weighted by `U_{2,0} ^ pₙ`. -/
theorem integral_riemannianVolume_sphere_eq_integral_bubble_rpow_criticalExponent
    [MeasurableSpace E] [BorelSpace E] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (hn₁ : 1 ≤ n) (hn₂ : n ≠ 2) (v : sphere (0 : E) 1) (φ : sphere (0 : E) 1 → G) :
    ∫ x, φ x ∂riemannianVolume (𝓡 n) (sphere (0 : E) 1) =
      ∫ y, bubble 2 (0 : EuclideanSpace ℝ (Fin n)) y ^ criticalExponent n •
        φ ((stereographic' n v).symm y) ∂volume := by
  rw [integral_riemannianVolume_sphere_eq_stereographic' hn₁ v]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  dsimp only
  rw [← normDet_fderiv_coe_comp_stereographic'_symm v y,
    normDet_fderiv_coe_comp_stereographic'_symm_eq_bubble_rpow_criticalExponent hn₂ v y]

/-- **Critical `L ^ pₙ` pullback along stereographic projection.** For `1 ≤ n` with `n ≠ 2` and any
pole `v ∈ Sⁿ`, `∫_{Sⁿ} |φ| ^ pₙ dV = ∫_{ℝⁿ} |U_{2,0} · (φ ∘ σ⁻¹)| ^ pₙ dy`. -/
theorem integral_abs_rpow_criticalExponent_sphere_eq_stereographic'
    [MeasurableSpace E] [BorelSpace E] (hn₁ : 1 ≤ n) (hn₂ : n ≠ 2)
    (v : sphere (0 : E) 1) (φ : sphere (0 : E) 1 → ℝ) :
    ∫ x, |φ x| ^ criticalExponent n ∂riemannianVolume (𝓡 n) (sphere (0 : E) 1) =
      ∫ y, |bubble 2 (0 : EuclideanSpace ℝ (Fin n)) y *
        φ ((stereographic' n v).symm y)| ^ criticalExponent n ∂volume := by
  rw [integral_riemannianVolume_sphere_eq_integral_bubble_rpow_criticalExponent hn₁ hn₂ v]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  dsimp only
  have hpos : 0 ≤ bubble 2 (0 : EuclideanSpace ℝ (Fin n)) y := (bubble_pos two_pos 0 y).le
  rw [smul_eq_mul, abs_mul, abs_of_nonneg hpos, Real.mul_rpow hpos (abs_nonneg _)]

end Sphere

end ModelValues

end TauCeti.Yamabe
