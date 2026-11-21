/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.ConformalInvariance
public import TauCeti.Analysis.PDE.Yamabe.PositiveApproximation
public import TauCeti.Analysis.PDE.Yamabe.UpperBound
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Embedding
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Multiplication
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Schrodinger
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.WithMetric
import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Isometry
import TauCeti.MeasureTheory.Integral.AbsRpow
import TauCeti.MeasureTheory.Integral.ContinuousMap

/-!
# The Yamabe quotient on the Sobolev space `H¹`

On a closed smooth Riemannian manifold `(M, g)` of dimension `n`, the weak form of the conformal
Laplacian `L_g = aₙ Δ⁺_g + Scal_g` on `H¹(M)` (`TauCeti.Manifold.SobolevH1`) is the continuous
symmetric bilinear form `E_g(w, v) = aₙ D_g(w, v) + ∫ Scal_g w v dV_g`
(`TauCeti.Yamabe.energyForm`). Dividing `E_g(w, w)` by `(∫ |w| ^ pₙ dV_g) ^ (2 / pₙ)`
(`pₙ = 2 n / (n - 2)`) defines the **weak Yamabe quotient** `TauCeti.Yamabe.weakYamabeQuotient` on
`H¹(M)`.

In dimension `n > 2`, the critical Sobolev embedding `SobolevH1.toLpOfLE` makes the denominator
finite, norm-continuous, and positive away from `0`. We establish:
* **Isometry and conformal invariance** (`energyForm_compRiemannianIsometry`,
  `weakYamabeQuotient_compRiemannianIsometry`, `conformalMulEquiv`, `energyForm_conformalMulEquiv`,
  `weakYamabeQuotient_conformalMulEquiv`, `sInf_weakYamabeQuotient_eq_of_mem_conformalClass`);
* **First variation and weak Euler–Lagrange equation** (`hasDerivAt_weakYamabeQuotient_add_smul`,
  `forall_hasDerivAt_weakYamabeQuotient_add_smul_iff_exists_energyForm_eq`,
  `forall_ofSmooth_hasDerivAt_weakYamabeQuotient_iff_exists_energyForm_eq`,
  `weakYamabeQuotient_eq_of_energyForm_eq`);
* **Lower bounds, equality of weak and smooth infima, and Aubin's bound**
  (`neg_integral_scalarCurvature_negPart_rpow_le_weakYamabeQuotient`,
  `sInf_weakYamabeQuotient_eq_sInf_yamabeQuotient`,
  `sInf_weakYamabeQuotient_eq_sInf_yamabeQuotient_pos`, `exists_yamabeQuotient_lt`,
  `sInf_weakYamabeQuotient_le_sphereYamabeConstant`).

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §2–§3.
* T. Aubin, *Équations différentielles non linéaires et problème de Yamabe concernant la courbure
  scalaire*, J. Math. Pures Appl. 55 (1976), 269–296.
-/

public section

open Bundle Filter MeasureTheory Module Set TauCeti.Manifold
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti.Yamabe

section EnergyAndQuotient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The scalar curvature of `M` packaged as an element of `L^∞(M)`. -/
private def scalarCurvatureLp : Lp ℝ ⊤ (riemannianVolume I M) :=
  ContinuousMap.toLp ⊤ (riemannianVolume I M) ℝ
    ⟨(CovariantDerivative.leviCivitaConnection I M).scalarCurvature,
      (CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature.continuous⟩

/-- The **weak Yamabe energy form** `E_g(w, v) = aₙ D_g(w, v) + ∫ Scal_g w v dV_g` on `H¹(M)`, the
continuous symmetric bilinear form associated with the conformal Laplacian `aₙ Δ⁺_g + Scal_g`. -/
def energyForm : SobolevH1 I M →L[ℝ] SobolevH1 I M →L[ℝ] ℝ :=
  conformalCoefficient (finrank ℝ E) • SobolevH1.dirichletForm +
    SobolevH1.potentialForm (scalarCurvatureLp I)

variable {I}

/-- Formula for `TauCeti.Yamabe.energyForm` in terms of `SobolevH1.dirichletForm` and the `L²`
scalar-curvature integral. -/
theorem energyForm_apply (w v : SobolevH1 I M) :
    energyForm I w v =
      conformalCoefficient (finrank ℝ E) * SobolevH1.dirichletForm w v +
        ∫ x, (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x *
          SobolevH1.toLp w x * SobolevH1.toLp v x ∂riemannianVolume I M := by
  rw [energyForm, add_apply, add_apply, smul_apply, smul_apply, smul_eq_mul,
    SobolevH1.potentialForm_apply]
  congr 1
  exact integral_congr_ae <| (ContinuousMap.coeFn_toLp (p := ⊤) (𝕜 := ℝ) (riemannianVolume I M)
    ⟨(CovariantDerivative.leviCivitaConnection I M).scalarCurvature,
      (CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature.continuous⟩).mono
    fun x hx ↦ by dsimp only; rw [scalarCurvatureLp, hx, ContinuousMap.coe_mk]

/-- The weak Yamabe energy form is symmetric. -/
theorem energyForm_comm (w v : SobolevH1 I M) : energyForm I w v = energyForm I v w := by
  rw [energyForm, add_apply, add_apply, add_apply, add_apply, smul_apply, smul_apply,
    smul_apply, smul_apply, SobolevH1.dirichletForm_comm, SobolevH1.potentialForm_comm]

/-- Quadratic expansion of `energyForm` on a sum. -/
theorem energyForm_add_self (w v : SobolevH1 I M) :
    energyForm I (w + v) (w + v) =
      energyForm I w w + 2 * energyForm I w v + energyForm I v v := by
  simp only [map_add, add_apply, energyForm_comm v w]; ring

/-- On smooth functions `u` and `v`, `energyForm` is the classical Yamabe bilinear energy
`∫ (aₙ ⟪grad u, grad v⟫ + Scal_g u v) dV_g`. -/
@[simp]
theorem energyForm_ofSmooth (u v : C^∞⟮I, M; ℝ⟯) :
    energyForm I (SobolevH1.ofSmooth u) (SobolevH1.ofSmooth v) =
      ∫ x, (conformalCoefficient (finrank ℝ E) * inner ℝ (mgradient I u x) (mgradient I v x) +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (u x * v x))
        ∂riemannianVolume I M := by
  have h1 : Continuous fun x ↦
      conformalCoefficient (finrank ℝ E) * inner ℝ (mgradient I u x) (mgradient I v x) :=
    continuous_const.mul (continuous_inner_mgradient (u.contMDiff.of_le (by simp))
      (v.contMDiff.of_le (by simp)))
  have h2 : Continuous fun x ↦
      (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (u x * v x) :=
    (CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature.continuous.mul
      ((map_continuous u).mul (map_continuous v))
  have hpot : ∫ x, (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x *
      SobolevH1.toLp (SobolevH1.ofSmooth u) x *
      SobolevH1.toLp (SobolevH1.ofSmooth v) x ∂riemannianVolume I M =
      ∫ x, (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (u x * v x)
        ∂riemannianVolume I M := by
    refine integral_congr_ae ?_
    filter_upwards [SobolevH1.toLp_ofSmooth_ae_eq u, SobolevH1.toLp_ofSmooth_ae_eq v] with x hu hv
    rw [hu, hv, mul_assoc]
  rw [energyForm_apply, SobolevH1.dirichletForm_ofSmooth, hpot, ← integral_const_mul,
    ← integral_add h1.integrable_of_compactSpace h2.integrable_of_compactSpace]

/-- On the diagonal of a smooth function `u`, `energyForm` is the classical Yamabe energy
`∫ (aₙ |grad u|² + Scal_g u²) dV_g`. -/
theorem energyForm_ofSmooth_self (u : C^∞⟮I, M; ℝ⟯) :
    energyForm I (SobolevH1.ofSmooth u) (SobolevH1.ofSmooth u) =
      ∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I u x‖ ^ 2 +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x ^ 2)
        ∂riemannianVolume I M := by
  simp only [energyForm_ofSmooth, real_inner_self_eq_norm_sq, sq]

/-- **Green's identity for the weak Yamabe energy form.** On a closed manifold, pairing `w ∈ H¹(M)`
with a smooth test function `φ` in `energyForm` integrates `toLp w` against
`conformalLaplacian I φ`. -/
theorem energyForm_ofSmooth_right [I.Boundaryless] (w : SobolevH1 I M) (φ : C^∞⟮I, M; ℝ⟯) :
    energyForm I w (SobolevH1.ofSmooth φ) =
      ∫ x, SobolevH1.toLp w x * conformalLaplacian I φ x ∂riemannianVolume I M := by
  have hint {f : M → ℝ} (hf : Continuous f) :
      Integrable (fun x ↦ SobolevH1.toLp w x * f x) (riemannianVolume I M) :=
    (Lp.memLp (SobolevH1.toLp w)).integrable_mul
      (hf.memLp_of_hasCompactSupport (p := 2) (.of_compactSpace _))
  have h1 : Integrable (fun x ↦ conformalCoefficient (finrank ℝ E) *
      (SobolevH1.toLp w x * -laplaceBeltrami I φ x)) (riemannianVolume I M) :=
    (hint (continuous_laplaceBeltrami (φ.contMDiff.of_le (by simp))).neg).const_mul _
  have h2 : Integrable (fun x ↦ SobolevH1.toLp w x *
      ((CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * φ x))
      (riemannianVolume I M) :=
    hint ((CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature.continuous.mul
      (map_continuous φ))
  have hpot : ∫ x, (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x *
      SobolevH1.toLp w x * SobolevH1.toLp (SobolevH1.ofSmooth φ) x ∂riemannianVolume I M =
      ∫ x, SobolevH1.toLp w x *
        ((CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * φ x)
        ∂riemannianVolume I M :=
    integral_congr_ae <| (SobolevH1.toLp_ofSmooth_ae_eq φ).mono fun x hx ↦ by
      dsimp only; rw [hx]; ring
  rw [energyForm_apply, SobolevH1.dirichletForm_ofSmooth_right, hpot, ← integral_const_mul,
    ← integral_add h1 h2]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by
    dsimp only [Pi.add_apply]; rw [conformalLaplacian_def]; ring)

/-- Nonnegative scalar curvature makes `energyForm` nonnegative on the diagonal. -/
theorem energyForm_self_nonneg_of_scalarCurvature_nonneg (w : SobolevH1 I M)
    (hS : ∀ x, 0 ≤ (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x) :
    0 ≤ energyForm I w w := by
  rw [energyForm_apply]
  refine add_nonneg (mul_nonneg (conformalCoefficient_nonneg _)
    (SobolevH1.dirichletForm_self_nonneg w)) (integral_nonneg fun x ↦ ?_)
  dsimp only [Pi.zero_apply]; rw [mul_assoc]
  exact mul_nonneg (hS x) (mul_self_nonneg (SobolevH1.toLp w x))

variable (I) in
/-- The **weak Yamabe quotient** `Q_g(w) = E_g(w, w) / (∫ |w| ^ pₙ dV_g) ^ (2 / pₙ)` of an element
`w ∈ H¹(M)` on a closed Riemannian manifold of dimension `n`, where `pₙ = 2 n / (n - 2)`. -/
def weakYamabeQuotient (w : SobolevH1 I M) : ℝ :=
  energyForm I w w /
    (∫ x, |SobolevH1.toLp w x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M) ^
      (2 / criticalExponent (finrank ℝ E))

variable (I) in
/-- Unfolding lemma for `TauCeti.Yamabe.weakYamabeQuotient`. -/
theorem weakYamabeQuotient_def (w : SobolevH1 I M) :
    weakYamabeQuotient I w =
      energyForm I w w /
        (∫ x, |SobolevH1.toLp w x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M) ^
          (2 / criticalExponent (finrank ℝ E)) := (rfl)

/-- On smooth functions, `weakYamabeQuotient` agrees with `yamabeQuotient`. -/
@[simp]
theorem weakYamabeQuotient_ofSmooth (u : C^∞⟮I, M; ℝ⟯) :
    weakYamabeQuotient I (SobolevH1.ofSmooth u) = yamabeQuotient I u := by
  rw [weakYamabeQuotient_def, yamabeQuotient_def, energyForm_ofSmooth_self]
  congr 2
  exact integral_congr_ae <| (SobolevH1.toLp_ofSmooth_ae_eq u).mono fun x hx ↦ by
    dsimp only; rw [hx]

@[simp]
theorem weakYamabeQuotient_zero : weakYamabeQuotient I (0 : SobolevH1 I M) = 0 := by
  simp [weakYamabeQuotient_def]

/-- Nonnegative scalar curvature makes `weakYamabeQuotient` nonnegative on all of `H¹(M)`. -/
theorem weakYamabeQuotient_nonneg_of_scalarCurvature_nonneg (w : SobolevH1 I M)
    (hS : ∀ x, 0 ≤ (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x) :
    0 ≤ weakYamabeQuotient I w :=
  div_nonneg (energyForm_self_nonneg_of_scalarCurvature_nonneg w hS)
    (Real.rpow_nonneg (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _) _)

/-- **Scale invariance of the weak Yamabe quotient.** In dimension `n > 2`, multiplying `w ∈ H¹(M)`
by a nonzero constant `c` preserves `weakYamabeQuotient`. -/
theorem weakYamabeQuotient_smul (hn : 2 < finrank ℝ E) {w : SobolevH1 I M} {c : ℝ} (hc : c ≠ 0) :
    weakYamabeQuotient I (c • w) = weakYamabeQuotient I w := by
  have hp := criticalExponent_pos hn
  have hnum : energyForm I (c • w) (c • w) = c ^ 2 * energyForm I w w := by
    simp only [map_smul, smul_apply, smul_eq_mul]; ring
  have hden : ∫ x, |SobolevH1.toLp (c • w) x| ^ criticalExponent (finrank ℝ E)
      ∂riemannianVolume I M =
      |c| ^ criticalExponent (finrank ℝ E) *
        ∫ x, |SobolevH1.toLp w x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M := by
    rw [← integral_const_mul]
    exact integral_congr_ae <|
      (map_smul SobolevH1.toLp c w ▸ Lp.coeFn_smul c (SobolevH1.toLp w)).mono fun x hx ↦ by
        dsimp only
        rw [hx, Pi.smul_apply, smul_eq_mul, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  have hc2 : (|c| ^ criticalExponent (finrank ℝ E)) ^ (2 / criticalExponent (finrank ℝ E)) =
      c ^ 2 := by
    rw [← Real.rpow_mul (abs_nonneg _), mul_div_cancel₀ _ hp.ne', Real.rpow_two, sq_abs]
  rw [weakYamabeQuotient_def, weakYamabeQuotient_def, hnum, hden,
    Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _)
      (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _),
    hc2, mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

/-- **Norm continuity of the weak Yamabe quotient away from zero.** On a closed manifold of
dimension `n > 2`, `weakYamabeQuotient I` is continuous at every nonzero `w ∈ H¹(M)`. -/
theorem continuousAt_weakYamabeQuotient [I.Boundaryless] (hn : 2 < finrank ℝ E)
    {w : SobolevH1 I M} (hw : w ≠ 0) :
    ContinuousAt (weakYamabeQuotient I) w := by
  have hp2 := two_lt_criticalExponent hn
  have hN_cont : Continuous fun v : SobolevH1 I M ↦
      ∫ x, |SobolevH1.toLp v x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M :=
    SobolevH1.continuous_integral_abs_toLp_rpow hn (by linarith) (criticalExponent_def _).le
  have hN_pos := (SobolevH1.integral_abs_toLp_rpow_pos_iff hn (criticalExponent_pos hn)
    (criticalExponent_def _).le).2 hw
  exact ((energyForm I).continuous.clm_apply continuous_id).continuousAt.div
    (hN_cont.continuousAt.rpow_const (Or.inl hN_pos.ne')) (Real.rpow_pos_of_pos hN_pos _).ne'

end EnergyAndQuotient

/-! ### Isometry and conformal invariance on `H¹` -/

section Invariance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]

section Isometry

variable [T2Space M] [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N] [CompactSpace N]
  [IsManifold I' ∞ N] [MeasurableSpace N] [BorelSpace N]
  [RiemannianBundle (fun y : N ↦ TangentSpace I' y)]
  [IsContMDiffRiemannianBundle I' ∞ E (fun y : N ↦ TangentSpace I' y)]
  [IsContinuousRiemannianBundle E (fun y : N ↦ TangentSpace I' y)]

/-- **Isometry invariance of the weak Yamabe energy form.** Pullback along a Riemannian isometry
`Φ : M → N` preserves `energyForm`. -/
@[simp]
theorem energyForm_compRiemannianIsometry (Φ : RiemannianIsometry I I' M N)
    (w v : SobolevH1 I' N) :
    energyForm I (SobolevH1.compRiemannianIsometry Φ w) (SobolevH1.compRiemannianIsometry Φ v) =
      energyForm I' w v := by
  have hmp := Φ.measurePreserving_riemannianVolume
  rw [energyForm_apply, energyForm_apply, SobolevH1.dirichletForm_compRiemannianIsometry]; congr 1
  rw [← hmp.integral_comp Φ.toDiffeomorph.toHomeomorph.measurableEmbedding (fun y ↦
    (CovariantDerivative.leviCivitaConnection I' N).scalarCurvature y *
      SobolevH1.toLp w y * SobolevH1.toLp v y)]
  refine integral_congr_ae ?_
  filter_upwards [SobolevH1.toLp_compRiemannianIsometry Φ w ▸
      Lp.coeFn_compMeasurePreserving (SobolevH1.toLp w) hmp,
    SobolevH1.toLp_compRiemannianIsometry Φ v ▸
      Lp.coeFn_compMeasurePreserving (SobolevH1.toLp v) hmp] with x hxw hxv
  rw [hxw, hxv, Function.comp_apply, Function.comp_apply,
    Φ.isLocalRiemannianIsometry.scalarCurvature_map x]

/-- **Isometry invariance of the weak Yamabe quotient.** Pullback along a Riemannian isometry
`Φ : M → N` preserves `weakYamabeQuotient`. -/
@[simp]
theorem weakYamabeQuotient_compRiemannianIsometry (Φ : RiemannianIsometry I I' M N)
    (w : SobolevH1 I' N) :
    weakYamabeQuotient I (SobolevH1.compRiemannianIsometry Φ w) = weakYamabeQuotient I' w := by
  have hmp := Φ.measurePreserving_riemannianVolume
  rw [weakYamabeQuotient_def, weakYamabeQuotient_def, energyForm_compRiemannianIsometry]; congr 2
  rw [← hmp.integral_comp Φ.toDiffeomorph.toHomeomorph.measurableEmbedding
    (fun y ↦ |SobolevH1.toLp w y| ^ criticalExponent (finrank ℝ E))]
  exact integral_congr_ae <| (SobolevH1.toLp_compRiemannianIsometry Φ w ▸
    Lp.coeFn_compMeasurePreserving (SobolevH1.toLp w) hmp).mono fun x hx ↦ by
      dsimp only; rw [hx, Function.comp_apply]

end Isometry

section ConformalCarrier

variable [IsManifold I 1 M]

/-- **Conformal transport on `H¹`.** Given a positive smooth function `u` on `M` with conformal
metric `ĝ = u ^ (4 / (n - 2)) g`, transporting along `SobolevH1.congrRescale` and multiplying by
`u` defines a continuous linear equivalence `H¹(WithMetric ĝ) ≃L[ℝ] H¹(WithMetric g)`. -/
def conformalMulEquiv
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))} :
    SobolevH1 I
        (WithMetric (g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos)) ≃L[ℝ]
      SobolevH1 I (WithMetric g) :=
  let uM : C^∞⟮I, M; ℝ⟯ := ⟨u, hu⟩
  (SobolevH1.congrRescale g hf hf_pos).trans
    (SobolevH1.mulLeftEquiv
      (uM.comp (WithMetric.diffeomorph g ∞).toContMDiffMap)
      fun x ↦ by
        rw [ContMDiffMap.comp_apply, Diffeomorph.coe_coe, WithMetric.coe_diffeomorph]
        exact (hu_pos x.ofWithMetric).ne')

@[simp]
theorem conformalMulEquiv_ofSmooth
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    (v : C^∞⟮I, WithMetric (g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos);
      ℝ⟯) :
    conformalMulEquiv g hu hu_pos (SobolevH1.ofSmooth v) =
      SobolevH1.ofSmooth
        (ContMDiffMap.comp ⟨u, hu⟩ (WithMetric.diffeomorph g ∞).toContMDiffMap *
          v.comp (WithMetric.diffeomorphWithMetric g
            (g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos)
            ∞).toContMDiffMap) := by
  simp [conformalMulEquiv]

/-- Under `conformalMulEquiv`, the `L²` value on `WithMetric g` is almost everywhere `u` times the
`L²` value on `WithMetric ĝ`. -/
theorem toLp_conformalMulEquiv_ae_eq
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    (w : SobolevH1 I
      (WithMetric (g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos))) :
    SobolevH1.toLp (conformalMulEquiv g hu hu_pos w) =ᵐ[riemannianVolume I (WithMetric g)]
      fun x ↦ u x.ofWithMetric *
        SobolevH1.toLp w
          (WithMetric.toWithMetric
            (g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos)
            x.ofWithMetric) := by
  let uM : C^∞⟮I, M; ℝ⟯ := ⟨u, hu⟩
  have hmul : conformalMulEquiv g hu hu_pos w =
      SobolevH1.mulLeft (uM.comp (WithMetric.diffeomorph g ∞).toContMDiffMap)
        (SobolevH1.congrRescale g hf hf_pos w) :=
    DFunLike.congr_fun (SobolevH1.coe_mulLeftEquiv _ _) _
  filter_upwards [hmul ▸ SobolevH1.toLp_mulLeft_ae_eq
      (uM.comp (WithMetric.diffeomorph g ∞).toContMDiffMap)
      (SobolevH1.congrRescale g hf hf_pos w),
    SobolevH1.toLp_congrRescale_ae_eq g hf hf_pos w] with x hx1 hx2
  refine hx1.trans ?_
  rw [ContMDiffMap.comp_apply, Diffeomorph.coe_coe, WithMetric.coe_diffeomorph, hx2]
  rfl

end ConformalCarrier

variable [IsManifold I ∞ M]

/-- **Conformal invariance of the critical `Lᵖ` integral on `H¹`.** Under `conformalMulEquiv`, the
integral of `|toLp ·| ^ pₙ` is preserved. -/
theorem integral_abs_toLp_conformalMulEquiv_rpow
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    (w : SobolevH1 I
      (WithMetric (g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos))) :
    ∫ x, |SobolevH1.toLp (conformalMulEquiv g hu hu_pos w) x| ^
        criticalExponent (finrank ℝ E) ∂riemannianVolume I (WithMetric g) =
      ∫ x, |SobolevH1.toLp w x| ^ criticalExponent (finrank ℝ E)
        ∂riemannianVolume I
          (WithMetric (g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos)) := by
  let ĝ := g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos
  have hvol := WithMetric.integral_abs_rpow_rescale_rpow (g := g) (fun x ↦ (hu_pos x).le)
    (hf := hf) (hf_pos := hf_pos) (fun y ↦ SobolevH1.toLp w (WithMetric.toWithMetric ĝ y))
  simp only [WithMetric.toWithMetric_ofWithMetric, ← criticalExponent_def] at hvol
  rw [hvol]
  exact integral_congr_ae <| (toLp_conformalMulEquiv_ae_eq g hu hu_pos w).mono fun x hx ↦ by
    dsimp only; rw [hx]

variable [T2Space M] [MeasurableSpace M] [BorelSpace M]

/-- Smooth energy on `WithMetric g` written as an integral over `WithMetric g` using `g` on `M`. -/
private theorem energyForm_ofSmooth_withMetric
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : C^∞⟮I, M; ℝ⟯) :
    energyForm I (SobolevH1.ofSmooth (φ.comp (WithMetric.diffeomorph g ∞).toContMDiffMap))
        (SobolevH1.ofSmooth (φ.comp (WithMetric.diffeomorph g ∞).toContMDiffMap)) =
      ∫ x, ((letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          conformalCoefficient (finrank ℝ E) * ‖mgradient I φ x.ofWithMetric‖ ^ 2) +
          g.scalarCurvature x.ofWithMetric * φ x.ofWithMetric ^ 2)
        ∂riemannianVolume I (WithMetric g) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    instIsContMDiffRiemannianBundle g
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have hcomp : φ.comp (WithMetric.diffeomorph g ∞).toContMDiffMap =
      φ.comp (WithMetric.riemannianIsometry g).toDiffeomorph.toContMDiffMap := by ext x; simp
  rw [hcomp, ← SobolevH1.compRiemannianIsometry_ofSmooth, energyForm_compRiemannianIsometry,
    energyForm_ofSmooth_self, WithMetric.integral_comp_ofWithMetric g fun y ↦
      conformalCoefficient (finrank ℝ E) * ‖mgradient I φ y‖ ^ 2 + g.scalarCurvature y * φ y ^ 2]
  simp only [g.scalarCurvature_def]

/-- **Conformal invariance of the diagonal weak Yamabe energy.** On a closed manifold of dimension
`n ≠ 2`, `conformalMulEquiv` preserves `w ↦ energyForm I w w`. -/
theorem energyForm_conformalMulEquiv_self [I.Boundaryless]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    (w : SobolevH1 I
      (WithMetric (g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos))) :
    energyForm I (conformalMulEquiv g hu hu_pos w) (conformalMulEquiv g hu hu_pos w) =
      energyForm I w w := by
  let ĝ := g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos
  refine SobolevH1.induction_on w
    (isClosed_eq (((energyForm I).continuous.comp
      (conformalMulEquiv g hu hu_pos).continuous).clm_apply
      (conformalMulEquiv g hu hu_pos).continuous)
      ((energyForm I).continuous.clm_apply continuous_id)) fun v ↦ ?_
  let vM : C^∞⟮I, M; ℝ⟯ := v.comp (WithMetric.diffeomorph ĝ ∞).symm.toContMDiffMap
  let uM : C^∞⟮I, M; ℝ⟯ := ⟨u, hu⟩
  let uvM : C^∞⟮I, M; ℝ⟯ := uM * vM
  have hv : v = vM.comp (WithMetric.diffeomorph ĝ ∞).toContMDiffMap := by ext x; simp [vM]
  have huv : ContMDiffMap.comp ⟨u, hu⟩ (WithMetric.diffeomorph g ∞).toContMDiffMap *
      v.comp (WithMetric.diffeomorphWithMetric g ĝ ∞).toContMDiffMap =
      uvM.comp (WithMetric.diffeomorph g ∞).toContMDiffMap := by
    have hv' : v.comp (WithMetric.diffeomorphWithMetric g ĝ ∞).toContMDiffMap =
        vM.comp (WithMetric.diffeomorph g ∞).toContMDiffMap := by ext x; simp [vM]
    rw [hv']
    exact (ContMDiffMap.mul_comp uM vM (WithMetric.diffeomorph g ∞).toContMDiffMap).symm
  have huv_coe : (uvM : M → ℝ) = u * vM := ContMDiffMap.coe_mul uM vM
  rw [conformalMulEquiv_ofSmooth, huv, energyForm_ofSmooth_withMetric g uvM, hv,
    energyForm_ofSmooth_withMetric ĝ vM, huv_coe]
  exact (integral_energy_rescale g hn hu_pos (hf := hf) (hf_pos := hf_pos)
    (vM.contMDiff.of_le (by simp)) (HasCompactSupport.of_compactSpace _)).symm

/-- **Conformal invariance of the weak Yamabe energy form.** On a closed manifold of dimension
`n ≠ 2`, `conformalMulEquiv` preserves the bilinear form `energyForm`. -/
theorem energyForm_conformalMulEquiv [I.Boundaryless]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    (w v : SobolevH1 I
      (WithMetric (g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos))) :
    energyForm I (conformalMulEquiv g hu hu_pos w) (conformalMulEquiv g hu hu_pos v) =
      energyForm I w v := by
  have hsum := energyForm_conformalMulEquiv_self g hn hu hu_pos (hf := hf) (hf_pos := hf_pos)
    (w + v)
  rw [map_add (conformalMulEquiv g hu hu_pos), energyForm_add_self, energyForm_add_self,
    energyForm_conformalMulEquiv_self g hn hu hu_pos (hf := hf) (hf_pos := hf_pos) w,
    energyForm_conformalMulEquiv_self g hn hu hu_pos (hf := hf) (hf_pos := hf_pos) v] at hsum
  linarith

/-- **Conformal invariance of the weak Yamabe quotient on `H¹`.** On a closed manifold of dimension
`n ≠ 2`, let `ĝ = u ^ (4 / (n - 2)) g` for a positive smooth function `u`. Then
`Q_g(conformalMulEquiv w) = Q_ĝ(w)` for every `w ∈ H¹(WithMetric ĝ)`. -/
theorem weakYamabeQuotient_conformalMulEquiv [I.Boundaryless]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    (w : SobolevH1 I
      (WithMetric (g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos))) :
    weakYamabeQuotient I (conformalMulEquiv g hu hu_pos w) = weakYamabeQuotient I w := by
  rw [weakYamabeQuotient_def, weakYamabeQuotient_def,
    energyForm_conformalMulEquiv_self g hn hu hu_pos w,
    integral_abs_toLp_conformalMulEquiv_rpow g hu hu_pos w]

/-- **Conformal metrics have the same nonzero weak Yamabe quotients.** On a closed manifold of
dimension `n ≠ 2`, if `g' ∈ g.conformalClass`, the set of values of `weakYamabeQuotient` on
nonzero elements of `H¹(WithMetric g')` equals that on `H¹(WithMetric g)`. -/
theorem image_weakYamabeQuotient_eq_of_mem_conformalClass [I.Boundaryless]
    (hn : finrank ℝ E ≠ 2)
    {g g' : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg' : g' ∈ g.conformalClass) :
    weakYamabeQuotient I '' {w : SobolevH1 I (WithMetric g') | w ≠ 0} =
      weakYamabeQuotient I '' {w : SobolevH1 I (WithMetric g) | w ≠ 0} := by
  let p := 4 / ((finrank ℝ E : ℝ) - 2)
  have hp : p ≠ 0 := div_ne_zero four_ne_zero (sub_ne_zero.2 (by exact_mod_cast hn))
  obtain ⟨u, hu, hu_pos, rfl⟩ :=
    (ContMDiffRiemannianMetric.mem_conformalClass_iff_exists_rpow hp).mp hg'
  let Φ := conformalMulEquiv g hu hu_pos
    (hf := hu.rpow_const_of_ne (fun x ↦ (hu_pos x).ne') p)
    (hf_pos := fun x ↦ Real.rpow_pos_of_pos (hu_pos x) p)
  ext q; constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨Φ w, (map_ne_zero_iff Φ Φ.injective).2 hw,
      weakYamabeQuotient_conformalMulEquiv g hn hu hu_pos w⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨Φ.symm w, (map_ne_zero_iff Φ.symm Φ.symm.injective).2 hw, ?_⟩
    simpa only [Φ, ContinuousLinearEquiv.apply_symm_apply] using
      (weakYamabeQuotient_conformalMulEquiv g hn hu hu_pos (Φ.symm w)).symm

/-- **Conformal invariance of the weak Yamabe infimum.** On a closed manifold of dimension `n ≠ 2`,
the infimum of `weakYamabeQuotient` over nonzero `H¹` elements depends only on the conformal class
of the metric. -/
theorem sInf_weakYamabeQuotient_eq_of_mem_conformalClass [I.Boundaryless]
    (hn : finrank ℝ E ≠ 2)
    {g g' : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg' : g' ∈ g.conformalClass) :
    sInf (weakYamabeQuotient I '' {w : SobolevH1 I (WithMetric g') | w ≠ 0}) =
      sInf (weakYamabeQuotient I '' {w : SobolevH1 I (WithMetric g) | w ≠ 0}) :=
  congrArg sInf (image_weakYamabeQuotient_eq_of_mem_conformalClass hn hg')

end Invariance

/-! ### First variation and weak Euler–Lagrange equation on `H¹` -/

section FirstVariation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- Quadratic derivative of `t ↦ energyForm I (w + t • v) (w + t • v)` at `t = 0`. -/
private theorem hasDerivAt_energyForm_add_smul (w v : SobolevH1 I M) :
    HasDerivAt (fun t : ℝ ↦ energyForm I (w + t • v) (w + t • v))
      (2 * energyForm I v w) 0 := by
  have hquad (t : ℝ) : energyForm I (w + t • v) (w + t • v) =
      energyForm I w w + t * (2 * energyForm I v w) + t ^ 2 * energyForm I v v := by
    simp only [energyForm_add_self, map_smul, smul_apply, smul_eq_mul, energyForm_comm w v]; ring
  simp_rw [hquad]
  convert (((hasDerivAt_id (0 : ℝ)).mul_const (2 * energyForm I v w)).const_add
    (energyForm I w w)).add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (energyForm I v v)) using 1
  · funext t; simp only [Pi.add_apply, id]
  · simp

/-- **First variation of the weak Yamabe quotient on `H¹`.** On a closed manifold of dimension
`n > 2`, for `w ≠ 0` and `v` in `H¹(M)` with `N(w) = ∫ |toLp w| ^ pₙ dV`, the derivative of
`t ↦ weakYamabeQuotient I (w + t • v)` at `t = 0` is
`2 (E_g(v, w) / N(w) ^ (2 / pₙ) - Q_g(w) (∫ |w| ^ (pₙ - 2) w v dV) / N(w))`. -/
theorem hasDerivAt_weakYamabeQuotient_add_smul [I.Boundaryless] (hn : 2 < finrank ℝ E)
    {w : SobolevH1 I M} (hw : w ≠ 0) (v : SobolevH1 I M) :
    HasDerivAt (fun t : ℝ ↦ weakYamabeQuotient I (w + t • v))
      (2 * (energyForm I v w /
          (∫ x, |SobolevH1.toLp w x| ^ criticalExponent (finrank ℝ E)
            ∂riemannianVolume I M) ^ (2 / criticalExponent (finrank ℝ E)) -
        weakYamabeQuotient I w *
          (∫ x, |SobolevH1.toLp w x| ^ (criticalExponent (finrank ℝ E) - 2) *
            SobolevH1.toLp w x * SobolevH1.toLp v x ∂riemannianVolume I M) /
          ∫ x, |SobolevH1.toLp w x| ^ criticalExponent (finrank ℝ E)
            ∂riemannianVolume I M)) 0 := by
  set p := criticalExponent (finrank ℝ E)
  set μ := riemannianVolume I M
  have hp : 2 < p := two_lt_criticalExponent hn
  have hmw := SobolevH1.memLp_toLp hn (ENNReal.ofReal_le_ofReal (criticalExponent_def _).le) w
  have hmv := SobolevH1.memLp_toLp hn (ENNReal.ofReal_le_ofReal (criticalExponent_def _).le) v
  have hN_eq (t : ℝ) : ∫ x, |SobolevH1.toLp (w + t • v) x| ^ p ∂μ =
      ∫ x, |SobolevH1.toLp w x + t * SobolevH1.toLp v x| ^ p ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [map_add SobolevH1.toLp w (t • v) ▸
        Lp.coeFn_add (SobolevH1.toLp w) (SobolevH1.toLp (t • v)),
      map_smul SobolevH1.toLp t v ▸ Lp.coeFn_smul t (SobolevH1.toLp v)] with x h1 h2
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul]
  set N := ∫ x, |SobolevH1.toLp w x| ^ p ∂μ
  have hN0 : 0 < N := (SobolevH1.integral_abs_toLp_rpow_pos_iff hn (by linarith)
    (criticalExponent_def _).le).2 hw
  have hN_deriv : HasDerivAt (fun t : ℝ ↦ ∫ x, |SobolevH1.toLp (w + t • v) x| ^ p ∂μ)
      (p * ∫ x, |SobolevH1.toLp w x| ^ (p - 2) * SobolevH1.toLp w x *
        SobolevH1.toLp v x ∂μ) 0 := by
    simp_rw [hN_eq]; exact hmw.hasDerivAt_integral_abs_add_mul_rpow hmv (by linarith)
  have h0 : ∫ x, |SobolevH1.toLp (w + (0 : ℝ) • v) x| ^ p ∂μ = N := by simp [N]
  have hQ := (hasDerivAt_energyForm_add_smul w v).div
    (hN_deriv.rpow_const (p := 2 / p) (Or.inl (h0 ▸ hN0.ne')))
    (h0 ▸ (Real.rpow_pos_of_pos hN0 _).ne')
  have hE0 : energyForm I (w + (0 : ℝ) • v) (w + (0 : ℝ) • v) = energyForm I w w := by simp
  rw [h0, hE0] at hQ
  convert hQ using 1
  · exact funext fun t ↦ weakYamabeQuotient_def I (w + t • v)
  · have hQw : weakYamabeQuotient I w = energyForm I w w / N ^ (2 / p) := weakYamabeQuotient_def I w
    rw [hQw, Real.rpow_sub_one hN0.ne']
    have : p ≠ 0 := by linarith
    dsimp only [μ]; field_simp

/-- **Multiplier of the weak Euler–Lagrange equation.** In dimension `n > 2`, if `w ∈ H¹(M)`
satisfies `E_g(w, v) = c ∫ |w| ^ (pₙ - 2) w v dV` for all `v ∈ H¹(M)`, then
`Q_g(w) = c (∫ |w| ^ pₙ dV) ^ (1 - 2 / pₙ)`. -/
theorem weakYamabeQuotient_eq_of_energyForm_eq (hn : 2 < finrank ℝ E) {w : SobolevH1 I M} {c : ℝ}
    (h : ∀ v : SobolevH1 I M, energyForm I w v =
      c * ∫ x, |SobolevH1.toLp w x| ^ (criticalExponent (finrank ℝ E) - 2) *
        SobolevH1.toLp w x * SobolevH1.toLp v x ∂riemannianVolume I M) :
    weakYamabeQuotient I w =
      c * (∫ x, |SobolevH1.toLp w x| ^ criticalExponent (finrank ℝ E)
        ∂riemannianVolume I M) ^ (1 - 2 / criticalExponent (finrank ℝ E)) := by
  have hp := two_lt_criticalExponent hn
  have hww : ∫ x, |SobolevH1.toLp w x| ^ (criticalExponent (finrank ℝ E) - 2) *
      SobolevH1.toLp w x * SobolevH1.toLp w x ∂riemannianVolume I M =
      ∫ x, |SobolevH1.toLp w x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M :=
    integral_congr_ae (Eventually.of_forall fun x ↦ by
      dsimp only
      rw [mul_assoc, ← sq, ← sq_abs, ← Real.rpow_two,
        ← Real.rpow_add' (abs_nonneg _) (by linarith), sub_add_cancel])
  rw [weakYamabeQuotient_def, h w, hww]
  rcases (integral_nonneg fun x ↦ Real.rpow_nonneg (abs_nonneg (SobolevH1.toLp w x))
    (criticalExponent (finrank ℝ E)) :
      0 ≤ ∫ x, |SobolevH1.toLp w x| ^ criticalExponent (finrank ℝ E)
        ∂riemannianVolume I M).eq_or_lt with hN | hN
  · have : 2 / criticalExponent (finrank ℝ E) < 1 := (div_lt_one (by linarith)).2 hp
    rw [← hN, Real.zero_rpow (by positivity), Real.zero_rpow (by linarith)]; simp
  · rw [Real.rpow_sub hN, Real.rpow_one, mul_div_assoc]

/-- **Multiplier of the weak Euler–Lagrange equation at unit critical norm.** If `w ∈ H¹(M)` solves
`E_g(w, v) = c ∫ |w| ^ (pₙ - 2) w v dV` with `∫ |w| ^ pₙ dV = 1`, then
`weakYamabeQuotient I w = c`. -/
theorem weakYamabeQuotient_eq_of_energyForm_eq_of_integral_eq_one (hn : 2 < finrank ℝ E)
    {w : SobolevH1 I M} {c : ℝ}
    (h : ∀ v : SobolevH1 I M, energyForm I w v =
      c * ∫ x, |SobolevH1.toLp w x| ^ (criticalExponent (finrank ℝ E) - 2) *
        SobolevH1.toLp w x * SobolevH1.toLp v x ∂riemannianVolume I M)
    (h1 : ∫ x, |SobolevH1.toLp w x| ^ criticalExponent (finrank ℝ E)
      ∂riemannianVolume I M = 1) :
    weakYamabeQuotient I w = c := by
  rw [weakYamabeQuotient_eq_of_energyForm_eq hn h, h1, Real.one_rpow, mul_one]

/-- **Equivalence of variational and distributional weak solutions.** On a closed manifold of
dimension `n > 2`, an element `w ∈ H¹(M)` satisfies `E_g(w, v) = c ∫ |w| ^ (pₙ - 2) w v dV` for
every `v ∈ H¹(M)` if and only if it satisfies the integrated-by-parts identity
`∫ w (L_g φ) dV = c ∫ |w| ^ (pₙ - 2) w φ dV` against every smooth function `φ`. -/
theorem forall_energyForm_eq_iff_forall_contMDiff_integral_conformalLaplacian_eq
    [I.Boundaryless] (hn : 2 < finrank ℝ E) (w : SobolevH1 I M) (c : ℝ) :
    (∀ v : SobolevH1 I M, energyForm I w v =
        c * ∫ x, |SobolevH1.toLp w x| ^ (criticalExponent (finrank ℝ E) - 2) *
          SobolevH1.toLp w x * SobolevH1.toLp v x ∂riemannianVolume I M) ↔
      ∀ φ : C^∞⟮I, M; ℝ⟯,
        ∫ x, SobolevH1.toLp w x * conformalLaplacian I φ x ∂riemannianVolume I M =
          c * ∫ x, |SobolevH1.toLp w x| ^ (criticalExponent (finrank ℝ E) - 2) *
            SobolevH1.toLp w x * φ x ∂riemannianVolume I M := by
  have hp2 := two_lt_criticalExponent hn
  have hφ_rhs (φ : C^∞⟮I, M; ℝ⟯) :
      ∫ x, |SobolevH1.toLp w x| ^ (criticalExponent (finrank ℝ E) - 2) *
          SobolevH1.toLp w x * SobolevH1.toLp (SobolevH1.ofSmooth φ) x ∂riemannianVolume I M =
        ∫ x, |SobolevH1.toLp w x| ^ (criticalExponent (finrank ℝ E) - 2) *
          SobolevH1.toLp w x * φ x ∂riemannianVolume I M :=
    integral_congr_ae <| (SobolevH1.toLp_ofSmooth_ae_eq φ).mono fun x hx ↦ by
      dsimp only; rw [hx]
  refine ⟨fun h φ ↦ by rw [← energyForm_ofSmooth_right w φ, h (SobolevH1.ofSmooth φ), hφ_rhs],
    fun h v ↦ SobolevH1.induction_on v
      (isClosed_eq (energyForm I w).continuous
        (continuous_const.mul (SobolevH1.continuous_integral_abs_toLp_rpow_sub_two_mul hn
          (by linarith) (criticalExponent_def _).le w)))
      fun φ ↦ by rw [energyForm_ofSmooth_right w φ, h φ, hφ_rhs]⟩

/-- Smooth-direction stationarity implies the weak Euler–Lagrange equation on all of `H¹`. -/
private theorem exists_energyForm_eq_of_forall_ofSmooth_hasDerivAt [I.Boundaryless]
    (hn : 2 < finrank ℝ E) {w : SobolevH1 I M} (hw : w ≠ 0)
    (hcrit : ∀ φ : C^∞⟮I, M; ℝ⟯,
      HasDerivAt (fun t : ℝ ↦ weakYamabeQuotient I (w + t • SobolevH1.ofSmooth φ)) 0 0) :
    ∃ c : ℝ, ∀ v : SobolevH1 I M, energyForm I w v =
      c * ∫ x, |SobolevH1.toLp w x| ^ (criticalExponent (finrank ℝ E) - 2) *
        SobolevH1.toLp w x * SobolevH1.toLp v x ∂riemannianVolume I M := by
  let p := criticalExponent (finrank ℝ E)
  let N := ∫ x, |SobolevH1.toLp w x| ^ p ∂riemannianVolume I M
  have hp := two_lt_criticalExponent hn
  have hN0 : 0 < N := (SobolevH1.integral_abs_toLp_rpow_pos_iff hn (by linarith)
    (criticalExponent_def _).le).2 hw
  have hNp : 0 < N ^ (2 / p) := Real.rpow_pos_of_pos hN0 _
  let c₀ := weakYamabeQuotient I w * N ^ (2 / p) / N
  refine ⟨c₀, fun v ↦ SobolevH1.induction_on v
    (isClosed_eq (energyForm I w).continuous
      (continuous_const.mul (SobolevH1.continuous_integral_abs_toLp_rpow_sub_two_mul hn
        (by linarith) (criticalExponent_def _).le w))) fun φ ↦ ?_⟩
  have h0 := (hasDerivAt_weakYamabeQuotient_add_smul hn hw (SobolevH1.ofSmooth φ)).unique (hcrit φ)
  have hsub := sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left two_ne_zero)
  rw [energyForm_comm (SobolevH1.ofSmooth φ) w, div_eq_iff hNp.ne'] at hsub
  rw [hsub]; dsimp only [c₀]; ring

/-- **The weak Euler–Lagrange equation of the Yamabe quotient on `H¹`.** On a closed manifold of
dimension `n > 2`, a nonzero `w ∈ H¹(M)` has vanishing directional derivative of
`weakYamabeQuotient` in every `H¹` direction `v` if and only if it satisfies
`E_g(w, v) = c ∫ |w| ^ (pₙ - 2) w v dV` for some constant `c` and all `v ∈ H¹(M)`. -/
theorem forall_hasDerivAt_weakYamabeQuotient_add_smul_iff_exists_energyForm_eq
    [I.Boundaryless] (hn : 2 < finrank ℝ E) {w : SobolevH1 I M} (hw : w ≠ 0) :
    (∀ v : SobolevH1 I M,
        HasDerivAt (fun t : ℝ ↦ weakYamabeQuotient I (w + t • v)) 0 0) ↔
      ∃ c : ℝ, ∀ v : SobolevH1 I M, energyForm I w v =
        c * ∫ x, |SobolevH1.toLp w x| ^ (criticalExponent (finrank ℝ E) - 2) *
          SobolevH1.toLp w x * SobolevH1.toLp v x ∂riemannianVolume I M := by
  refine ⟨fun h ↦ exists_energyForm_eq_of_forall_ofSmooth_hasDerivAt hn hw
    fun φ ↦ h (SobolevH1.ofSmooth φ), ?_⟩
  rintro ⟨c, hc⟩ v
  let p := criticalExponent (finrank ℝ E)
  let N := ∫ x, |SobolevH1.toLp w x| ^ p ∂riemannianVolume I M
  have hp := two_lt_criticalExponent hn
  have hN0 : 0 < N := (SobolevH1.integral_abs_toLp_rpow_pos_iff hn (by linarith)
    (criticalExponent_def _).le).2 hw
  have hNp : 0 < N ^ (2 / p) := Real.rpow_pos_of_pos hN0 _
  have hc₀ : weakYamabeQuotient I w * N ^ (2 / p) / N = c := by
    rw [weakYamabeQuotient_eq_of_energyForm_eq hn hc, mul_assoc,
      ← Real.rpow_add hN0, sub_add_cancel, Real.rpow_one, mul_div_cancel_right₀ c hN0.ne']
  convert hasDerivAt_weakYamabeQuotient_add_smul hn hw v using 1
  rw [energyForm_comm v w, hc v, ← hc₀]
  have hNne : (∫ x, |SobolevH1.toLp w x| ^ criticalExponent (finrank ℝ E)
      ∂riemannianVolume I M) ≠ 0 := hN0.ne'
  have hNpne : (∫ x, |SobolevH1.toLp w x| ^ criticalExponent (finrank ℝ E)
      ∂riemannianVolume I M) ^ (2 / criticalExponent (finrank ℝ E)) ≠ 0 := hNp.ne'
  dsimp only [N, p]; field_simp; ring

/-- **Smooth-direction stationarity suffices on `H¹`.** On a closed manifold of dimension `n > 2`,
a nonzero `w ∈ H¹(M)` is stationary for `weakYamabeQuotient` along all smooth perturbations
`ofSmooth φ` if and only if it satisfies the weak Euler–Lagrange equation against all
`v ∈ H¹(M)`. -/
theorem forall_ofSmooth_hasDerivAt_weakYamabeQuotient_iff_exists_energyForm_eq
    [I.Boundaryless] (hn : 2 < finrank ℝ E) {w : SobolevH1 I M} (hw : w ≠ 0) :
    (∀ φ : C^∞⟮I, M; ℝ⟯,
        HasDerivAt (fun t : ℝ ↦ weakYamabeQuotient I (w + t • SobolevH1.ofSmooth φ)) 0 0) ↔
      ∃ c : ℝ, ∀ v : SobolevH1 I M, energyForm I w v =
        c * ∫ x, |SobolevH1.toLp w x| ^ (criticalExponent (finrank ℝ E) - 2) *
          SobolevH1.toLp w x * SobolevH1.toLp v x ∂riemannianVolume I M :=
  ⟨exists_energyForm_eq_of_forall_ofSmooth_hasDerivAt hn hw, fun h φ ↦
    (forall_hasDerivAt_weakYamabeQuotient_add_smul_iff_exists_energyForm_eq hn hw).2 h
      (SobolevH1.ofSmooth φ)⟩

/-- **Weak Euler–Lagrange equation for almost everywhere nonnegative `H¹` functions.** When
`0 ≤ᵐ toLp w`, criticality of `w ≠ 0` is equivalent to the weak Yamabe equation
`E_g(w, v) = c ∫ w ^ (pₙ - 1) v dV`. -/
theorem forall_hasDerivAt_weakYamabeQuotient_add_smul_iff_exists_energyForm_eq_of_ae_nonneg
    [I.Boundaryless] (hn : 2 < finrank ℝ E) {w : SobolevH1 I M} (hw : w ≠ 0)
    (hnn : 0 ≤ᵐ[riemannianVolume I M] SobolevH1.toLp w) :
    (∀ v : SobolevH1 I M,
        HasDerivAt (fun t : ℝ ↦ weakYamabeQuotient I (w + t • v)) 0 0) ↔
      ∃ c : ℝ, ∀ v : SobolevH1 I M, energyForm I w v =
        c * ∫ x, SobolevH1.toLp w x ^ (criticalExponent (finrank ℝ E) - 1) *
          SobolevH1.toLp v x ∂riemannianVolume I M := by
  have hp := two_lt_criticalExponent hn
  have hae (v : SobolevH1 I M) :
      ∫ x, |SobolevH1.toLp w x| ^ (criticalExponent (finrank ℝ E) - 2) *
          SobolevH1.toLp w x * SobolevH1.toLp v x ∂riemannianVolume I M =
        ∫ x, SobolevH1.toLp w x ^ (criticalExponent (finrank ℝ E) - 1) *
          SobolevH1.toLp v x ∂riemannianVolume I M :=
    integral_congr_ae <| hnn.mono fun x hx ↦ by
      dsimp only [Pi.zero_apply] at hx ⊢
      rw [abs_of_nonneg hx, ← Real.rpow_add_one' hx (by linarith)]; ring_nf
  simpa only [hae] using
    forall_hasDerivAt_weakYamabeQuotient_add_smul_iff_exists_energyForm_eq hn hw

end FirstVariation

/-! ### Lower bounds, equality of weak and smooth infima, and Aubin's bound -/

section InvariantAndBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- Smooth density and norm continuity propagate any lower bound from nonzero smooth functions to
nonzero `H¹` elements. -/
private theorem le_weakYamabeQuotient_of_forall_ofSmooth (hn : 2 < finrank ℝ E) {c : ℝ}
    (hc : ∀ u : C^∞⟮I, M; ℝ⟯, (u : M → ℝ) ≠ 0 → c ≤ yamabeQuotient I u)
    {w : SobolevH1 I M} (hw : w ≠ 0) :
    c ≤ weakYamabeQuotient I w := by
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  have hnhds : {v : SobolevH1 I M | v ≠ 0 ∧
      weakYamabeQuotient I v < weakYamabeQuotient I w + ε} ∈ 𝓝 w :=
    Filter.inter_mem (isOpen_ne.mem_nhds hw)
      ((continuousAt_weakYamabeQuotient hn hw).eventually
        (gt_mem_nhds (lt_add_of_pos_right _ hε)))
  obtain ⟨_, ⟨hne, hlt⟩, u, rfl⟩ :=
    mem_closure_iff_nhds.1 (SobolevH1.denseRange_ofSmooth w) _ hnhds
  rw [weakYamabeQuotient_ofSmooth] at hlt
  refine (hc u fun h ↦ hne ?_).trans_lt hlt
  have hu0 : u = 0 := ContMDiffMap.ext (congrFun h)
  simp [hu0]

/-- **Scalar-curvature lower bound on `H¹`.** On a closed manifold of dimension `n > 2`, every
`w ∈ H¹(M)` satisfies `Q_g(w) ≥ -‖Scal_g⁻‖_{L^{n/2}}`. -/
theorem neg_integral_scalarCurvature_negPart_rpow_le_weakYamabeQuotient
    (hn : 2 < finrank ℝ E) (w : SobolevH1 I M) :
    -(∫ x, ((CovariantDerivative.leviCivitaConnection I M).scalarCurvature x)⁻ ^
        ((finrank ℝ E : ℝ) / 2) ∂riemannianVolume I M) ^ (2 / (finrank ℝ E : ℝ)) ≤
      weakYamabeQuotient I w := by
  rcases eq_or_ne w 0 with rfl | hw
  · rw [weakYamabeQuotient_zero]
    exact neg_nonpos.2 (Real.rpow_nonneg
      (integral_nonneg fun _ ↦ Real.rpow_nonneg (negPart_nonneg _) _) _)
  · exact le_weakYamabeQuotient_of_forall_ofSmooth hn
      (fun u _ ↦ neg_integral_scalarCurvature_negPart_rpow_le_yamabeQuotient hn
        (u.contMDiff.of_le (by simp))) hw

/-- On a closed manifold of dimension `n > 2`, the weak Yamabe quotients of nonzero `H¹` elements
are bounded below. -/
theorem bddBelow_image_weakYamabeQuotient (hn : 2 < finrank ℝ E) :
    BddBelow (weakYamabeQuotient I '' {w : SobolevH1 I M | w ≠ 0}) :=
  ⟨_, fun _ ⟨w, _, h⟩ ↦ h ▸ neg_integral_scalarCurvature_negPart_rpow_le_weakYamabeQuotient hn w⟩

/-- **Positive scalar curvature bounds the weak Yamabe quotient away from zero.** On a closed
manifold of dimension `n > 2` with `Scal_g > 0`, there is a constant `C > 0` such that
`C ≤ weakYamabeQuotient I w` for every nonzero `w ∈ H¹(M)`. -/
theorem exists_pos_le_weakYamabeQuotient_of_scalarCurvature_pos (hn : 2 < finrank ℝ E)
    (hS : ∀ x, 0 < (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x) :
    ∃ C, 0 < C ∧ ∀ w : SobolevH1 I M, w ≠ 0 → C ≤ weakYamabeQuotient I w := by
  obtain ⟨C, hC0, hCu⟩ := exists_pos_le_yamabeQuotient_of_scalarCurvature_pos (I := I) hn hS
  exact ⟨C, hC0, fun w hw ↦ le_weakYamabeQuotient_of_forall_ofSmooth hn
    (fun u hu0 ↦ hCu u (u.contMDiff.of_le (by simp)) hu0) hw⟩

/-- **Equality of weak and smooth Yamabe infima.** On a closed manifold of dimension `n > 2`, the
infimum of `weakYamabeQuotient` over nonzero `H¹` elements equals the infimum of `yamabeQuotient`
over nonzero smooth functions. -/
theorem sInf_weakYamabeQuotient_eq_sInf_yamabeQuotient (hn : 2 < finrank ℝ E) :
    sInf (weakYamabeQuotient I '' {w : SobolevH1 I M | w ≠ 0}) =
      sInf (yamabeQuotient I '' {u : M → ℝ | ContMDiff I 𝓘(ℝ) ∞ u ∧ u ≠ 0}) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · rw [eq_empty_of_forall_notMem (s := {w : SobolevH1 I M | w ≠ 0})
        fun w hw ↦ hw (Subsingleton.elim w 0),
      eq_empty_of_forall_notMem (s := {u : M → ℝ | ContMDiff I 𝓘(ℝ) ∞ u ∧ u ≠ 0})
        fun u hu ↦ hu.2 (Subsingleton.elim u 0), image_empty, image_empty]
  let W := weakYamabeQuotient I '' {w : SobolevH1 I M | w ≠ 0}
  let S := yamabeQuotient I '' {u : M → ℝ | ContMDiff I 𝓘(ℝ) ∞ u ∧ u ≠ 0}
  have hSW : S ⊆ W := by
    rintro _ ⟨u, ⟨hu, hu0⟩, rfl⟩
    let u' : C^∞⟮I, M; ℝ⟯ := ⟨u, hu⟩
    have heq : ∫ x, |SobolevH1.toLp (SobolevH1.ofSmooth u') x| ^
        criticalExponent (finrank ℝ E) ∂riemannianVolume I M =
        ∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M :=
      integral_congr_ae <| (SobolevH1.toLp_ofSmooth_ae_eq u').mono fun x hx ↦ by
        dsimp only; rw [hx]; rfl
    exact ⟨SobolevH1.ofSmooth u',
      (SobolevH1.integral_abs_toLp_rpow_pos_iff hn (criticalExponent_pos hn)
        (criticalExponent_def _).le).1
        (heq ▸ integral_abs_rpow_pos hu.continuous hu0 (criticalExponent_pos hn)),
      weakYamabeQuotient_ofSmooth u'⟩
  have hS_ne : S.Nonempty := ⟨_, ⟨fun _ ↦ 1, ⟨contMDiff_const,
    fun h ↦ one_ne_zero (congrFun h (Classical.arbitrary M))⟩, rfl⟩⟩
  have hbW : BddBelow W := bddBelow_image_weakYamabeQuotient hn
  refine le_antisymm (csInf_le_csInf hbW hS_ne hSW) (le_csInf (hS_ne.mono hSW) ?_)
  rintro _ ⟨w, hw, rfl⟩
  exact le_weakYamabeQuotient_of_forall_ofSmooth hn
    (fun u hu0 ↦ csInf_le (hbW.mono hSW) ⟨u, ⟨u.contMDiff, hu0⟩, rfl⟩) hw

/-- **Equality of the weak Yamabe infimum and the positive smooth Yamabe infimum.** On a closed
manifold of dimension `n > 2`, the infimum of `weakYamabeQuotient` over `{w : H¹(M) | w ≠ 0}` equals
the infimum of `yamabeQuotient` over strictly positive smooth functions. -/
theorem sInf_weakYamabeQuotient_eq_sInf_yamabeQuotient_pos (hn : 2 < finrank ℝ E) :
    sInf (weakYamabeQuotient I '' {w : SobolevH1 I M | w ≠ 0}) =
      sInf (yamabeQuotient I '' {u : M → ℝ | ContMDiff I 𝓘(ℝ) ∞ u ∧ ∀ x, 0 < u x}) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · have hR : {u : M → ℝ | ContMDiff I 𝓘(ℝ) ∞ u ∧ ∀ x, 0 < u x} = {0} :=
      Set.ext fun u ↦ ⟨fun _ ↦ Subsingleton.elim u 0,
        fun hu ↦ hu ▸ ⟨contMDiff_const, fun x ↦ hM.elim x⟩⟩
    rw [eq_empty_of_forall_notMem (s := {w : SobolevH1 I M | w ≠ 0})
        fun w hw ↦ hw (Subsingleton.elim w 0),
      image_empty, Real.sInf_empty, hR, image_singleton, csInf_singleton]
    simpa using (weakYamabeQuotient_ofSmooth (I := I) (0 : C^∞⟮I, M; ℝ⟯))
  · rw [sInf_weakYamabeQuotient_eq_sInf_yamabeQuotient hn,
      ← sInf_yamabeQuotient_pos_eq hn (by simp : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))]

/-- **Aubin's universal upper bound for positive smooth functions.** On a closed manifold of
dimension `n > 2`, for every `ε > 0` there is a strictly positive smooth function `u` with
`yamabeQuotient I u < sphereYamabeConstant n + ε`. -/
theorem exists_yamabeQuotient_lt (hn : 2 < finrank ℝ E) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ u ∧ (∀ x, 0 < u x) ∧
      yamabeQuotient I u < sphereYamabeConstant (finrank ℝ E) + ε := by
  rcases isEmpty_or_nonempty M with hM | hM
  · refine ⟨0, contMDiff_const, fun x ↦ hM.elim x, ?_⟩
    have h0 : yamabeQuotient I (0 : M → ℝ) = 0 := by
      simpa using (weakYamabeQuotient_ofSmooth (I := I) (0 : C^∞⟮I, M; ℝ⟯)).symm
    rw [h0]
    exact add_pos (sphereYamabeConstant_pos (by omega)) hε
  obtain ⟨v, hv, -, -, -, hv_pos, hvQ⟩ :=
    exists_contMDiff_hasCompactSupport_yamabeQuotient_lt (I := I) (M := M) hn isOpen_univ
      (univ_nonempty (α := M)) hε
  exact exists_contMDiff_pos_yamabeQuotient_lt hn (by simp) hv
    (fun h ↦ by subst h; simp [Real.zero_rpow (criticalExponent_pos hn).ne'] at hv_pos) hvQ

/-- **Aubin's bound for the smooth Yamabe invariant.** On a closed manifold of dimension `n > 2`,
the infimum of `yamabeQuotient` over strictly positive smooth functions is at most
`sphereYamabeConstant n`. -/
theorem sInf_yamabeQuotient_pos_le_sphereYamabeConstant (hn : 2 < finrank ℝ E) :
    sInf (yamabeQuotient I '' {u : M → ℝ | ContMDiff I 𝓘(ℝ) ∞ u ∧ ∀ x, 0 < u x}) ≤
      sphereYamabeConstant (finrank ℝ E) := by
  have hb : BddBelow (yamabeQuotient I '' {u : M → ℝ | ContMDiff I 𝓘(ℝ) ∞ u ∧ ∀ x, 0 < u x}) :=
    ⟨_, fun _ ⟨u, hu, h⟩ ↦
      h ▸ neg_integral_scalarCurvature_negPart_rpow_le_yamabeQuotient hn (hu.1.of_le (by simp))⟩
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨u, hu, hu_pos, huQ⟩ := exists_yamabeQuotient_lt (I := I) (M := M) hn hε
  exact (csInf_le hb ⟨u, ⟨hu, hu_pos⟩, rfl⟩).trans_lt huQ

/-- **Aubin's bound for the weak Yamabe invariant.** On a closed manifold of dimension `n > 2`, the
infimum of `weakYamabeQuotient` over nonzero `H¹` elements is at most `sphereYamabeConstant n`. -/
theorem sInf_weakYamabeQuotient_le_sphereYamabeConstant (hn : 2 < finrank ℝ E) :
    sInf (weakYamabeQuotient I '' {w : SobolevH1 I M | w ≠ 0}) ≤
      sphereYamabeConstant (finrank ℝ E) := by
  rw [sInf_weakYamabeQuotient_eq_sInf_yamabeQuotient_pos hn]
  exact sInf_yamabeQuotient_pos_le_sphereYamabeConstant hn

end InvariantAndBounds

end TauCeti.Yamabe
