/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Quotient
import TauCeti.Analysis.PDE.Yamabe.LowerBound
import TauCeti.Geometry.Manifold.ContMDiff.RPow
import TauCeti.Geometry.Manifold.Riemannian.Sobolev
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.WithMetric
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

All in the namespace `TauCeti.Yamabe`.

* `scalarCurvature_rescale_of_conformalLaplacian_eq_mul`: if `L_g u = λ u`, then
  `Scal_ĝ = λ u ^ (-4 / (n - 2))`; `sign_scalarCurvature_rescale_of_conformalLaplacian_eq_mul`:
  its sign is that of `λ`.
* `yamabeQuotient_rescale`: the conformal invariance `Q_ĝ(v) = Q_g(u v)` on compactly supported `C²`
  functions.
* `sign_yamabeQuotient_of_conformalLaplacian_eq_mul`: an eigenfunction `L_g u = λ u` has `Q_g(u)` of
  the sign of `λ`.
* `exists_pos_le_yamabeQuotient_of_scalarCurvature_pos`: on a closed manifold of positive scalar
  curvature, `Q_g` is bounded below by a positive constant on nonzero `C¹` functions.
* `yamabeQuotient_nonneg_of_conformalLaplacian_eq_mul` and
  `exists_pos_le_yamabeQuotient_of_conformalLaplacian_eq_mul`: a positive eigenfunction with
  `λ ≥ 0`, respectively `λ > 0`, makes `Q_g` nonnegative, respectively bounded below by a positive
  constant.
* `sign_sInf_yamabeQuotient_of_conformalLaplacian_eq_mul`: the infimum of `Q_g` over nonzero `C²`
  functions has the sign of `λ`.

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

section Rescale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- **Scalar curvature from an eigenfunction of the conformal Laplacian.** In dimension `n ≠ 2`,
let `u` be a positive function such that `ĝ = u ^ (4 / (n - 2)) g` is a smooth metric. At a point
where `L_g u = λ u`, the scalar curvature of `ĝ` is `Scal_ĝ = λ u ^ (-4 / (n - 2))`. -/
theorem scalarCurvature_rescale_of_conformalLaplacian_eq_mul
    (hn : finrank ℝ E ≠ 2) {u : M → ℝ} (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))} {c : ℝ} {x : M}
    (h : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      conformalLaplacian I u x) = c * u x) :
    (g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos).scalarCurvature x =
      c * u x ^ (-(4 / ((finrank ℝ E : ℝ) - 2))) := by
  have hn' : (finrank ℝ E : ℝ) - 2 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hn)
  rw [scalarCurvature_rescale_eq_rpow_mul_conformalLaplacian g hn hu_pos x, h, mul_left_comm,
    ← Real.rpow_add_one (hu_pos x).ne']
  congr 2
  field_simp
  ring

/-- **The sign of the scalar curvature from an eigenfunction.** In dimension `n ≠ 2`, let `u` be a
positive function such that `ĝ = u ^ (4 / (n - 2)) g` is a smooth metric. At a point where
`L_g u = λ u`, the scalar curvature of `ĝ` has the sign of `λ`. -/
theorem sign_scalarCurvature_rescale_of_conformalLaplacian_eq_mul
    (hn : finrank ℝ E ≠ 2) {u : M → ℝ} (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))} {c : ℝ} {x : M}
    (h : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      conformalLaplacian I u x) = c * u x) :
    SignType.sign
        ((g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos).scalarCurvature x) =
      SignType.sign c := by
  rw [scalarCurvature_rescale_of_conformalLaplacian_eq_mul g hn hu_pos h, sign_mul,
    sign_pos (Real.rpow_pos_of_pos (hu_pos x) _), mul_one]

variable [I.Boundaryless] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Conformal invariance of the Yamabe quotient.** In dimension `n ≠ 2`, let `u` be a positive
function such that `ĝ = u ^ (4 / (n - 2)) g` is a smooth metric on a manifold without boundary.
Then `Q_ĝ(v) = Q_g(u v)` for every compactly supported `C²` function `v`. -/
theorem yamabeQuotient_rescale (hn : finrank ℝ E ≠ 2) {u : M → ℝ} (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))} {v : M → ℝ}
    (hv : ContMDiff I 𝓘(ℝ) 2 v) (hvc : HasCompactSupport v) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf
          hf_pos).toRiemannianMetric⟩;
      letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
          (F := E) (V := fun x : M ↦ TangentSpace I x);
      yamabeQuotient I v) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
          (F := E) (V := fun x : M ↦ TangentSpace I x);
      yamabeQuotient I (u * v)) := by
  have hnum := integral_energy_rescale g hn hu_pos (hf := hf) (hf_pos := hf_pos) hv hvc
  have hden := WithMetric.integral_abs_rpow_rescale_rpow (g := g) (fun x ↦ (hu_pos x).le)
    (hf := hf) (hf_pos := hf_pos) v
  rw [WithMetric.integral_comp_ofWithMetric _ fun y ↦
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale _ hf hf_pos).toRiemannianMetric⟩;
        conformalCoefficient (finrank ℝ E) * ‖mgradient I v y‖ ^ 2) +
        (g.rescale _ hf hf_pos).scalarCurvature y * v y ^ 2,
    WithMetric.integral_comp_ofWithMetric g fun y ↦
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        conformalCoefficient (finrank ℝ E) * ‖mgradient I (u * v) y‖ ^ 2) +
        g.scalarCurvature y * (u * v) y ^ 2] at hnum
  rw [WithMetric.integral_comp_ofWithMetric _ fun y ↦ |v y| ^
      (2 * (finrank ℝ E : ℝ) / ((finrank ℝ E : ℝ) - 2)),
    WithMetric.integral_comp_ofWithMetric g fun y ↦ |u y * v y| ^
      (2 * (finrank ℝ E : ℝ) / ((finrank ℝ E : ℝ) - 2))] at hden
  simp only [ContMDiffRiemannianMetric.scalarCurvature_def] at hnum
  simp only [yamabeQuotient_def, criticalExponent_def]
  exact congrArg₂ _ hnum (congrArg (· ^ _) hden)

end Rescale

section Closed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

omit [I.Boundaryless] [T2Space M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- A nonzero continuous function on a compact Riemannian manifold has positive `L²` norm. -/
private theorem integral_sq_pos {u : M → ℝ} (hu : Continuous u) (hu0 : u ≠ 0) :
    0 < ∫ x, u x ^ 2 ∂riemannianVolume I M := by
  simpa only [Real.rpow_two, sq_abs] using integral_abs_rpow_pos hu hu0 two_pos

/-- **The Yamabe quotient of an eigenfunction.** On a closed manifold of dimension `n > 2`, a
nonzero `C²` solution `u` of `L_g u = λ u` has a Yamabe quotient `Q_g(u)` of the sign of `λ`. -/
theorem sign_yamabeQuotient_of_conformalLaplacian_eq_mul (hn : 2 < finrank ℝ E) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) 2 u) (hu0 : u ≠ 0) {c : ℝ}
    (h : ∀ x, conformalLaplacian I u x = c * u x) :
    SignType.sign (yamabeQuotient I u) = SignType.sign c := by
  have hN : 0 < (∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M) ^
      (2 / criticalExponent (finrank ℝ E)) :=
    Real.rpow_pos_of_pos (integral_abs_rpow_pos hu.continuous hu0 (criticalExponent_pos hn)) _
  have hpt (x : M) : u x * conformalLaplacian I u x = c * u x ^ 2 := by
    rw [h x]
    ring
  rw [yamabeQuotient_def, ← integral_mul_conformalLaplacian_self hu
    (HasCompactSupport.of_compactSpace u)]
  simp only [hpt, integral_const_mul]
  rw [div_eq_mul_inv, sign_mul, sign_mul, sign_pos (integral_sq_pos hu.continuous hu0),
    sign_pos (inv_pos.2 hN), mul_one, mul_one]

omit [T2Space M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The Sobolev inequality on a closed manifold of dimension `n > 2`, squared and written with
integrals: there is a constant `K > 0` with
`(∫ |u| ^ pₙ dV) ^ (2 / pₙ) ≤ K (∫ |grad u|² dV + ∫ u² dV)` for every `C¹` function `u`. -/
private theorem exists_integral_abs_rpow_rpow_le (hn : 2 < finrank ℝ E) :
    ∃ K, 0 < K ∧ ∀ u : M → ℝ, ContMDiff I 𝓘(ℝ) 1 u →
      (∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M) ^
          (2 / criticalExponent (finrank ℝ E)) ≤
        K * (∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I M +
          ∫ x, u x ^ 2 ∂riemannianVolume I M) := by
  set p := criticalExponent (finrank ℝ E)
  have hp : 2 < p := two_lt_criticalExponent hn
  obtain ⟨K, hK⟩ := exists_eLpNorm_le_mul_eLpNorm_mgradient_two_add (I := I) (M := M) hn
  refine ⟨2 * ((K : ℝ) + 1) ^ 2, by positivity, fun u hu ↦ ?_⟩
  set A := ∫ x, |u x| ^ p ∂riemannianVolume I M
  set B := ∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I M
  set D := ∫ x, u x ^ 2 ∂riemannianVolume I M
  have hA : 0 ≤ A := integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hB : 0 ≤ B := integral_nonneg fun _ ↦ sq_nonneg _
  have hD : 0 ≤ D := integral_nonneg fun _ ↦ sq_nonneg _
  have hgc : Continuous fun x ↦ ‖mgradient I u x‖ := continuous_norm_mgradient hu
  -- The Sobolev inequality in real numbers: `A ^ (1 / p) ≤ K (B ^ (1 / 2) + D ^ (1 / 2))`.
  have hsob : A ^ p⁻¹ ≤ K * (B ^ (2 : ℝ)⁻¹ + D ^ (2 : ℝ)⁻¹) := by
    have h := hK u hu
    have hpe : ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2)) = ENNReal.ofReal p := by
      simp only [p, criticalExponent_def]
    rw [hpe, MemLp.eLpNorm_eq_integral_rpow_norm (by simp; linarith) ENNReal.ofReal_ne_top
        (hu.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
        (hgc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
        (hu.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_le_ofReal_iff (by positivity),
      ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofNat] at h
    simpa only [Real.norm_eq_abs, norm_norm, Real.rpow_two, sq_abs] using h
  have hsq (X : ℝ) (hX : 0 ≤ X) (q : ℝ) (hq : q ≠ 0) : (X ^ q⁻¹) ^ 2 = X ^ (2 / q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX]
    congr 1
    field_simp
    norm_num
  -- Squaring, with `(y + z) ^ 2 ≤ 2 (y ^ 2 + z ^ 2)`.
  have h2 := pow_le_pow_left₀ (by positivity) hsob 2
  rw [hsq A hA p (by linarith)] at h2
  have hB2 := hsq B hB 2 two_ne_zero
  have hD2 := hsq D hD 2 two_ne_zero
  rw [div_self two_ne_zero, Real.rpow_one] at hB2 hD2
  set y := B ^ (2 : ℝ)⁻¹
  set z := D ^ (2 : ℝ)⁻¹
  calc A ^ (2 / p) ≤ (K * (y + z)) ^ 2 := h2
    _ ≤ ((K : ℝ) + 1) ^ 2 * (2 * (y ^ 2 + z ^ 2)) := by
      rw [mul_pow]
      gcongr
      · linarith [K.coe_nonneg]
      · nlinarith [sq_nonneg (y - z)]
    _ = 2 * ((K : ℝ) + 1) ^ 2 * (B + D) := by
      rw [hB2, hD2]
      ring

/-- **Positive scalar curvature bounds the Yamabe quotient away from zero.** On a closed manifold
of dimension `n > 2` with positive scalar curvature, there is a constant `C > 0` such that
`C ≤ Q_g(u)` for every nonzero `C¹` function `u`. -/
theorem exists_pos_le_yamabeQuotient_of_scalarCurvature_pos (hn : 2 < finrank ℝ E)
    (hS : ∀ x, 0 < (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x) :
    ∃ C, 0 < C ∧ ∀ u : M → ℝ, ContMDiff I 𝓘(ℝ) 1 u → u ≠ 0 → C ≤ yamabeQuotient I u := by
  set S := (CovariantDerivative.leviCivitaConnection I M).scalarCurvature
  set μ := riemannianVolume I M
  set a := conformalCoefficient (finrank ℝ E)
  have hSc : Continuous S :=
    (CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature.continuous
  obtain ⟨s, hs, hsS⟩ := isCompact_univ.exists_forall_le' hSc.continuousOn fun x _ ↦ hS x
  obtain ⟨K, hK, hKu⟩ := exists_integral_abs_rpow_rpow_le (I := I) (M := M) hn
  set m := min a s
  have hm : 0 < m := lt_min (conformalCoefficient_pos hn) hs
  refine ⟨m / K, by positivity, fun u hu hu0 ↦ ?_⟩
  set B := ∫ x, ‖mgradient I u x‖ ^ 2 ∂μ
  set D := ∫ x, u x ^ 2 ∂μ
  have hgc : Continuous fun x ↦ ‖mgradient I u x‖ := continuous_norm_mgradient hu
  -- Since `m ≤ aₙ` and `m ≤ Scal_g`, the numerator of `Q_g(u)` is at least `m (B + D)`.
  have hnum : m * (B + D) ≤ ∫ x, (a * ‖mgradient I u x‖ ^ 2 + S x * u x ^ 2) ∂μ := by
    have hint {f : M → ℝ} (hf : Continuous f) : Integrable f μ :=
      hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
    rw [mul_add, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hint (f := fun x ↦ m * ‖mgradient I u x‖ ^ 2)
        (continuous_const.mul (hgc.pow 2)))
        (hint (f := fun x ↦ m * u x ^ 2) (continuous_const.mul (hu.continuous.pow 2)))]
    refine integral_mono (hint ((continuous_const.mul (hgc.pow 2)).add
      (continuous_const.mul (hu.continuous.pow 2))))
      (hint ((continuous_const.mul (hgc.pow 2)).add (hSc.mul (hu.continuous.pow 2)))) fun x ↦ ?_
    exact add_le_add (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
      (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (hsS x (Set.mem_univ x)))
        (sq_nonneg _))
  rw [yamabeQuotient_def, le_div_iff₀ (Real.rpow_pos_of_pos
    (integral_abs_rpow_pos hu.continuous hu0 (criticalExponent_pos hn)) _)]
  calc m / K * (∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂μ) ^
        (2 / criticalExponent (finrank ℝ E))
      ≤ m / K * (K * (B + D)) := by gcongr; exact hKu u hu
    _ = m * (B + D) := by field_simp
    _ ≤ _ := hnum

end Closed

section Eigenfunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- Dividing by a positive smooth eigenfunction `u` writes `w = u (w / u)`, and the Yamabe quotient
of `g` at `w` is the Yamabe quotient of `ĝ = u ^ (4 / (n - 2)) g` at `w / u`. -/
private theorem yamabeQuotient_eq_rescale_inv_mul (hn : finrank ℝ E ≠ 2) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hu_pos : ∀ x, 0 < u x) {w : M → ℝ}
    (hw : ContMDiff I 𝓘(ℝ) 2 w) (hwc : HasCompactSupport w) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
          (F := E) (V := fun x : M ↦ TangentSpace I x);
      yamabeQuotient I w) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2)))
          (hu.rpow_const_of_ne (fun x ↦ (hu_pos x).ne') _)
          (fun x ↦ Real.rpow_pos_of_pos (hu_pos x) _)).toRiemannianMetric⟩;
      letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
          (F := E) (V := fun x : M ↦ TangentSpace I x);
      yamabeQuotient I fun x ↦ (u x)⁻¹ * w x) := by
  have huv : (u * fun x ↦ (u x)⁻¹ * w x) = w :=
    funext fun x ↦ mul_inv_cancel_left₀ (hu_pos x).ne' (w x)
  rw [yamabeQuotient_rescale g hn hu_pos (v := fun x ↦ (u x)⁻¹ * w x)
    (((hu.of_le (by simp)).inv₀ fun x ↦ (hu_pos x).ne').mul hw) hwc.mul_left, huv]

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
    (scalarCurvature_rescale_of_conformalLaplacian_eq_mul g hn2 hu_pos (h x))
  rw [yamabeQuotient_eq_rescale_inv_mul g hn2 hu hu_pos hw hwc]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.rescale _ hf hf_pos).toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  exact yamabeQuotient_nonneg_of_scalarCurvature_nonneg hn _ fun x ↦ by
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
    (scalarCurvature_rescale_of_conformalLaplacian_eq_mul g hn2 hu_pos (h x))
  obtain ⟨C, hC, hCQ⟩ :=
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.rescale _ hf hf_pos).toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
    exists_pos_le_yamabeQuotient_of_scalarCurvature_pos (I := I) (M := M) hn fun x ↦ by
      rw [hS x]
      exact mul_pos hc (Real.rpow_pos_of_pos (hu_pos x) _)
  refine ⟨C, hC, fun w hw hw0 ↦ ?_⟩
  rw [yamabeQuotient_eq_rescale_inv_mul g hn2 hu hu_pos hw (HasCompactSupport.of_compactSpace w)]
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
    exact yamabeQuotient_nonneg_of_conformalLaplacian_eq_mul g hn hu hu_pos le_rfl h hw.1
      (HasCompactSupport.of_compactSpace w)
  · rw [sign_pos hc, sign_eq_one_iff]
    obtain ⟨C, hC, hCQ⟩ := exists_pos_le_yamabeQuotient_of_conformalLaplacian_eq_mul g hn hu
      hu_pos hc h
    refine hC.trans_le (le_csInf ⟨_, hmem⟩ ?_)
    rintro _ ⟨w, hw, rfl⟩
    exact hCQ w hw.1 hw.2

end Eigenfunction

end TauCeti.Yamabe
