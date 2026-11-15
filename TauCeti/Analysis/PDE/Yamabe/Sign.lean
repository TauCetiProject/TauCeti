/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.ConformalInvariance
import TauCeti.Analysis.PDE.Yamabe.LowerBound
import TauCeti.Geometry.Manifold.ContMDiff.RPow
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.MeasureTheory.Integral.AbsRpow

/-!
# The sign of the Yamabe quotient and eigenfunctions of the conformal Laplacian

Let `(M, g)` be a Riemannian manifold of dimension `n > 2`, with conformal Laplacian
`L_g = aₙ Δ⁺_g + Scal_g` and Yamabe quotient
`Q_g(w) = (∫ (aₙ |grad w|² + Scal_g w²) dV_g) / (∫ |w| ^ pₙ dV_g) ^ (2 / pₙ)`, where
`aₙ = 4 (n - 1) / (n - 2)` and `pₙ = 2 n / (n - 2)`. This file shows that a positive eigenfunction
of `L_g` determines the sign of the Yamabe quotient.

Let `u` be a positive smooth function with `L_g u = λ u`, for instance a first eigenfunction of
`L_g` on a connected closed manifold. By the transformation law of scalar curvature, the conformal
metric `ĝ = u ^ (4 / (n - 2)) g` has scalar curvature `Scal_ĝ = λ u ^ (-4 / (n - 2))`, which has the
sign of `λ` everywhere, although it is generally not constant. The Yamabe quotient is conformally
invariant, `Q_ĝ(v) = Q_g(u v)`, so writing an arbitrary function as `w = u (w / u)` turns
statements about the sign of `Scal_ĝ` into statements about `Q_g`:

* if `λ < 0`, then `Q_g(u) < 0`, since `∫ u L_g u dV = λ ∫ u² dV`;
* if `λ ≥ 0`, then `Q_ĝ ≥ 0` because `Scal_ĝ ≥ 0`, hence `Q_g ≥ 0`, and `Q_g(u) = 0` if `λ = 0`;
* if `λ > 0`, then `Scal_ĝ` is bounded below by a positive constant on a closed manifold, and the
  Sobolev inequality `‖v‖_{pₙ} ≤ K (‖grad v‖₂ + ‖v‖₂)` for `ĝ` bounds `Q_ĝ`, hence `Q_g`, below by a
  positive constant.

Consequently, on a nonempty closed manifold, the infimum of `Q_g` over nonzero `C²` functions has
the sign of `λ`. The quotient is compared on `C²` functions, the regularity at which the energy
identity and the conformal invariance are proved; the comparison with the infimum over the Sobolev
space `H¹` is not made here.

As in `TauCeti.Yamabe.integral_energy_rescale`, the two metrics `g` and `ĝ` are installed one at a
time as the `RiemannianBundle` instance of the tangent bundle of `M`.

## Main results

In the namespace `TauCeti.Yamabe`:

* `sign_yamabeQuotient_of_conformalLaplacian_eq_mul`: an eigenfunction `L_g u = λ u` has `Q_g(u)` of
  the sign of `λ`.

In the namespace `Bundle.ContMDiffRiemannianMetric`, for a smooth metric `g`:

* `yamabeQuotient_nonneg_of_conformalLaplacian_eq_mul` and
  `exists_pos_le_yamabeQuotient_of_conformalLaplacian_eq_mul`: a positive eigenfunction with
  `λ ≥ 0`, respectively `λ > 0`, makes `Q_g` nonnegative, respectively bounded below by a positive
  constant.
* `sign_sInf_yamabeQuotient_of_conformalLaplacian_eq_mul`: the infimum of `Q_g` over nonzero `C²`
  functions has the sign of `λ`.

The scalar curvature of `ĝ` is computed in
`Bundle.ContMDiffRiemannianMetric.scalarCurvature_rescale_of_conformalLaplacian_eq_mul`, and the
conformal invariance `Q_ĝ(v) = Q_g(u v)` is
`Bundle.ContMDiffRiemannianMetric.yamabeQuotient_rescale`. The positive lower bound on `Q_g` for
positive scalar curvature is `TauCeti.Yamabe.exists_pos_le_yamabeQuotient_of_scalarCurvature_pos`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91
  (the Yamabe functional, its conformal invariance, and the sign of the first eigenvalue of the
  conformal Laplacian).
-/

public section

open Bundle MeasureTheory Module TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Yamabe

section Closed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- **The Yamabe quotient of an eigenfunction.** On a closed manifold of dimension `n > 2`, a
nonzero `C²` solution `u` of `L_g u = λ u` has a Yamabe quotient `Q_g(u)` of the sign of `λ`. -/
theorem sign_yamabeQuotient_of_conformalLaplacian_eq_mul (hn : 2 < finrank ℝ E) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) 2 u) (hu0 : u ≠ 0) {c : ℝ}
    (h : ∀ x, conformalLaplacian I u x = c * u x) :
    SignType.sign (yamabeQuotient I u) = SignType.sign c := by
  have hN : 0 < (∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M) ^
      (2 / criticalExponent (finrank ℝ E)) :=
    Real.rpow_pos_of_pos (integral_abs_rpow_pos hu.continuous hu0 (criticalExponent_pos hn)) _
  have hu2 : 0 < ∫ x, u x ^ 2 ∂riemannianVolume I M := by
    simpa only [Real.rpow_two, sq_abs] using integral_abs_rpow_pos hu.continuous hu0 two_pos
  have hpt (x : M) : u x * conformalLaplacian I u x = c * u x ^ 2 := by
    rw [h x]
    ring
  rw [yamabeQuotient_def, ← integral_mul_conformalLaplacian_self hu
    (HasCompactSupport.of_compactSpace u)]
  simp only [hpt, integral_const_mul]
  rw [div_eq_mul_inv, sign_mul, sign_mul, sign_pos hu2, sign_pos (inv_pos.2 hN), mul_one,
    mul_one]

end Closed

end TauCeti.Yamabe

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti TauCeti.Yamabe

section Eigenfunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- **A nonnegative eigenvalue gives nonnegative Yamabe quotients.** In dimension `n > 2`, let `u`
be a positive smooth solution of `L_g u = λ u` with `λ ≥ 0` on a manifold without boundary. Then
`Q_g(w) ≥ 0` for every compactly supported `C²` function `w`. -/
theorem yamabeQuotient_nonneg_of_conformalLaplacian_eq_mul (hn : 2 < finrank ℝ E) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hu_pos : ∀ x, 0 < u x) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      conformalLaplacian I u x) = c * u x)
    {w : M → ℝ} (hw : ContMDiff I 𝓘(ℝ) 2 w) (hwc : HasCompactSupport w) :
    0 ≤ (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
          (F := E) (V := fun x : M ↦ TangentSpace I x);
      yamabeQuotient I w) := by
  have hn2 : finrank ℝ E ≠ 2 := by omega
  have hf := hu.rpow_const_of_ne (fun x ↦ (hu_pos x).ne') (4 / ((finrank ℝ E : ℝ) - 2))
  have hf_pos (x : M) := Real.rpow_pos_of_pos (hu_pos x) (4 / ((finrank ℝ E : ℝ) - 2))
  -- The scalar curvature of `ĝ` is `λ u ^ (-4 / (n - 2)) ≥ 0`.
  have hS (x : M) := ((g.rescale _ hf hf_pos).scalarCurvature_def x).symm.trans
    (g.scalarCurvature_rescale_of_conformalLaplacian_eq_mul hu_pos (h x))
  rw [g.yamabeQuotient_eq_rescale_inv_mul hn2 hu hu_pos hw hwc]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.rescale _ hf hf_pos).toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  exact yamabeQuotient_nonneg_of_scalarCurvature_nonneg _ fun x ↦ by
    rw [hS x]
    exact mul_nonneg hc (Real.rpow_nonneg (hu_pos x).le _)

variable [CompactSpace M]

/-- **A positive eigenvalue bounds the Yamabe quotient away from zero.** On a closed manifold of
dimension `n > 2`, let `u` be a positive smooth solution of `L_g u = λ u` with `λ > 0`. Then there
is a constant `C > 0` such that `C ≤ Q_g(w)` for every nonzero `C²` function `w`. -/
theorem exists_pos_le_yamabeQuotient_of_conformalLaplacian_eq_mul (hn : 2 < finrank ℝ E)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hu_pos : ∀ x, 0 < u x) {c : ℝ} (hc : 0 < c)
    (h : ∀ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      conformalLaplacian I u x) = c * u x) :
    ∃ C, 0 < C ∧ ∀ w : M → ℝ, ContMDiff I 𝓘(ℝ) 2 w → w ≠ 0 →
      C ≤ (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
            (F := E) (V := fun x : M ↦ TangentSpace I x);
        yamabeQuotient I w) := by
  have hn2 : finrank ℝ E ≠ 2 := by omega
  have hf := hu.rpow_const_of_ne (fun x ↦ (hu_pos x).ne') (4 / ((finrank ℝ E : ℝ) - 2))
  have hf_pos (x : M) := Real.rpow_pos_of_pos (hu_pos x) (4 / ((finrank ℝ E : ℝ) - 2))
  -- The scalar curvature of `ĝ` is `λ u ^ (-4 / (n - 2)) > 0`.
  have hS (x : M) := ((g.rescale _ hf hf_pos).scalarCurvature_def x).symm.trans
    (g.scalarCurvature_rescale_of_conformalLaplacian_eq_mul hu_pos (h x))
  obtain ⟨C, hC, hCQ⟩ :=
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.rescale _ hf hf_pos).toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
    exists_pos_le_yamabeQuotient_of_scalarCurvature_pos (I := I) (M := M) hn fun x ↦ by
      rw [hS x]
      exact mul_pos hc (Real.rpow_pos_of_pos (hu_pos x) _)
  refine ⟨C, hC, fun w hw hw0 ↦ ?_⟩
  rw [g.yamabeQuotient_eq_rescale_inv_mul hn2 hu hu_pos hw (HasCompactSupport.of_compactSpace w)]
  refine hCQ _ ((((hu.of_le (by simp)).inv₀ fun x ↦ (hu_pos x).ne').mul hw).of_le one_le_two)
    fun hv ↦ hw0 (funext fun x ↦ ?_)
  have hx := congrFun hv x
  simpa [(hu_pos x).ne'] using hx

/-- **The sign of the Yamabe quotient's infimum.** On a nonempty closed manifold of dimension
`n > 2`, let `u` be a positive smooth solution of `L_g u = λ u`. Then the infimum of the Yamabe
quotient `Q_g` over nonzero `C²` functions has the sign of `λ`. -/
theorem sign_sInf_yamabeQuotient_of_conformalLaplacian_eq_mul [Nonempty M] (hn : 2 < finrank ℝ E)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hu_pos : ∀ x, 0 < u x) {c : ℝ}
    (h : ∀ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      conformalLaplacian I u x) = c * u x) :
    SignType.sign (sInf ((letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩;
      letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
          (F := E) (V := fun x : M ↦ TangentSpace I x);
      yamabeQuotient I) '' {w : M → ℝ | ContMDiff I 𝓘(ℝ) 2 w ∧ w ≠ 0})) =
      SignType.sign c := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  have hu0 : u ≠ 0 := fun h0 ↦ (hu_pos (Classical.arbitrary M)).ne' (congrFun h0 _)
  have hmem : yamabeQuotient I u ∈
      yamabeQuotient I '' {w : M → ℝ | ContMDiff I 𝓘(ℝ) 2 w ∧ w ≠ 0} :=
    ⟨u, ⟨hu.of_le (by simp), hu0⟩, rfl⟩
  have hsub : {w : M → ℝ | ContMDiff I 𝓘(ℝ) 2 w ∧ w ≠ 0} ⊆
      {w : M → ℝ | ContMDiff I 𝓘(ℝ) 1 w ∧ w ≠ 0} := fun w hw ↦ ⟨hw.1.of_le one_le_two, hw.2⟩
  have hbdd : BddBelow (yamabeQuotient I '' {w : M → ℝ | ContMDiff I 𝓘(ℝ) 2 w ∧ w ≠ 0}) :=
    (bddBelow_image_yamabeQuotient hn).mono (Set.image_mono hsub)
  have hQu := sign_yamabeQuotient_of_conformalLaplacian_eq_mul hn (hu.of_le (by simp)) hu0 h
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · rw [sign_neg hc, sign_eq_neg_one_iff]
    rw [sign_neg hc, sign_eq_neg_one_iff] at hQu
    exact (csInf_le hbdd hmem).trans_lt hQu
  · rw [sign_zero, sign_eq_zero_iff]
    rw [sign_zero, sign_eq_zero_iff] at hQu
    refine le_antisymm (hQu ▸ csInf_le hbdd hmem) (le_csInf ⟨_, hmem⟩ ?_)
    rintro _ ⟨w, hw, rfl⟩
    exact g.yamabeQuotient_nonneg_of_conformalLaplacian_eq_mul hn hu hu_pos le_rfl h hw.1
      (HasCompactSupport.of_compactSpace w)
  · rw [sign_pos hc, sign_eq_one_iff]
    obtain ⟨C, hC, hCQ⟩ := g.exists_pos_le_yamabeQuotient_of_conformalLaplacian_eq_mul hn hu
      hu_pos hc h
    refine hC.trans_le (le_csInf ⟨_, hmem⟩ ?_)
    rintro _ ⟨w, hw, rfl⟩
    exact hCQ w hw.1 hw.2

end Eigenfunction

end Bundle.ContMDiffRiemannianMetric
