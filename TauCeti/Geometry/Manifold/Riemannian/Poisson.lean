/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LaxMilgram
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.H1
import TauCeti.Geometry.Manifold.Riemannian.Poincare
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.ContinuousMap

/-!
# The Poisson equation on a closed Riemannian manifold

Let `M` be a compact connected manifold without boundary, with a continuous Riemannian metric, its
Riemannian volume `dV` and the Sobolev space `H¹(M)` (`TauCeti.Manifold.SobolevH1`). This file
inverts the nonnegative Laplacian `Δ⁺ = -div grad` on functions of mean zero, in the weak sense.

The weak form of the Poisson equation `Δ⁺w = f`, for `f ∈ L²(M)`, asks for `w ∈ H¹(M)` with

`D(w, v) = ∫ f v dV` for every `v ∈ H¹(M)`,

where `D` is the Dirichlet form (`TauCeti.Manifold.SobolevH1.dirichletForm`), the continuous
extension of `∫ ⟪∇w, ∇v⟫ dV`. Testing against the constant function `1` shows that `∫ f dV = 0` is
necessary, and the solution can only be unique up to an additive constant, since constants have
vanishing Dirichlet energy. Conversely, for `∫ f dV = 0` there is exactly one weak solution of
mean zero (`TauCeti.Manifold.SobolevH1.existsUnique_dirichletForm_eq`).

The proof is the Lax–Milgram theorem, applied on all of `H¹(M)` to the form
`B(w, v) = D(w, v) + (∫ w dV) (∫ v dV)`. Its coercivity is the Poincaré–Wirtinger inequality of
`TauCeti/Geometry/Manifold/Riemannian/Poincare.lean`, which extends from smooth functions to
`H¹(M)` by continuity in the form

`‖w‖²_{L²} ≤ C D(w, w) + (∫ w dV)² / Vol(M)`

(`TauCeti.Manifold.SobolevH1.exists_norm_toLp_sq_le`). For a `C¹` metric, Green's identity turns
the weak equation against a smooth test function `φ` into the distributional one,
`∫ w Δ⁺φ dV = ∫ f φ dV` (`TauCeti.Manifold.SobolevH1.exists_integral_mul_neg_laplaceBeltrami_eq`).

## Main results

* `TauCeti.Manifold.SobolevH1.exists_norm_toLp_sq_le`: the Poincaré–Wirtinger inequality on
  `H¹(M)`.
* `TauCeti.Manifold.SobolevH1.existsUnique_dirichletForm_eq`: existence and uniqueness of the weak
  solution of mean zero of `Δ⁺w = f` for `∫ f dV = 0`.
* `TauCeti.Manifold.SobolevH1.exists_forall_dirichletForm_eq_iff`: the weak equation `Δ⁺w = f`
  is solvable exactly when `∫ f dV = 0`.
* `TauCeti.Manifold.SobolevH1.exists_integral_mul_neg_laplaceBeltrami_eq`: the distributional
  form of the solution.

## References

* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), Theorem 4.7.
* J. L. Kazdan and F. W. Warner, *Curvature functions for compact 2-manifolds*, Ann. of Math. 99
  (1974), 14–47, §2.
-/

public section

open Bundle MeasureTheory Set
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace TauCeti.Manifold.SobolevH1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The integral `∫ w dV` of the value of an element of `H¹(M)`, as a continuous linear
functional. -/
private def integralCLM : StrongDual ℝ (SobolevH1 I M) :=
  (innerSL ℝ (toLp (ofSmooth (1 : C^∞⟮I, M; ℝ⟯)))).comp toLp

private theorem integralCLM_apply (w : SobolevH1 I M) :
    integralCLM w = ∫ x, toLp w x ∂riemannianVolume I M := by
  rw [integralCLM, ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm,
    inner_toLp_ofSmooth_right]
  simp

/-- The value of the constant function `1` has integral `Vol(M)`. -/
private theorem integral_toLp_ofSmooth_one :
    ∫ x, toLp (ofSmooth (1 : C^∞⟮I, M; ℝ⟯)) x ∂riemannianVolume I M =
      (riemannianVolume I M).real univ := by
  rw [integral_congr_ae (toLp_ofSmooth_ae_eq 1)]
  simp

/-- The form `B(w, v) = D(w, v) + (∫ w dV) (∫ v dV)` on `H¹(M)`. -/
private def poissonForm : SobolevH1 I M →L[ℝ] SobolevH1 I M →L[ℝ] ℝ :=
  dirichletForm + (ContinuousLinearMap.mul ℝ ℝ).bilinearComp integralCLM integralCLM

private theorem poissonForm_apply (w v : SobolevH1 I M) :
    poissonForm w v = dirichletForm w v + integralCLM w * integralCLM v :=
  (rfl)

variable [I.Boundaryless] [PreconnectedSpace M]

/-- **The Poincaré–Wirtinger inequality on `H¹(M)`.** On a closed connected manifold with a
continuous metric there is a constant `C` such that every `w ∈ H¹(M)` satisfies
`‖w‖²_{L²} ≤ C D(w, w) + (∫ w dV)² / Vol(M)`, where `D` is the Dirichlet form. -/
theorem exists_norm_toLp_sq_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : SobolevH1 I M,
      ‖toLp w‖ ^ 2 ≤ C * dirichletForm w w +
        ((riemannianVolume I M).real univ)⁻¹ * (∫ x, toLp w x ∂riemannianVolume I M) ^ 2 := by
  obtain ⟨C, hC⟩ := exists_integral_sq_sub_average_le_mul_integral_norm_sq_mgradient
    (I := I) (M := M)
  refine ⟨C, C.2, fun w ↦ ?_⟩
  simp only [← integralCLM_apply]
  refine induction_on w (isClosed_le (by fun_prop) (by fun_prop)) fun u ↦ ?_
  set μ := riemannianVolume I M
  set V := μ.real univ
  have hu := u.contMDiff.of_le (n := ∞) (m := 1) (by simp)
  -- For a smooth function, `∫ u² = ∫ (u - ū)² + V ū²`, with `V ū² = (∫ u)² / V`.
  have hu2 : Integrable (fun x ↦ u x ^ 2) μ :=
    Continuous.integrable_of_compactSpace ((map_continuous u).pow 2)
  have hsplit := TauCeti.setIntegral_norm_sub_sq_eq_setIntegral_norm_sub_setAverage_sq_add
    (μ := μ) (s := univ) (f := u) (measure_ne_top μ univ)
    (Continuous.integrable_of_compactSpace (μ := μ) (map_continuous u)).integrableOn (c := 0)
    (by simpa using hu2)
  simp only [Measure.restrict_univ, sub_zero, Real.norm_eq_abs, sq_abs] at hsplit
  have hmean : V * (⨍ y, u y ∂μ) ^ 2 = V⁻¹ * (∫ x, u x ∂μ) ^ 2 := by
    rw [average_eq, smul_eq_mul]
    rcases eq_or_ne V 0 with hV | hV
    · simp [hV]
    · rw [mul_pow, ← mul_assoc, sq V⁻¹, ← mul_assoc, mul_inv_cancel₀ hV, one_mul]
  rw [← real_inner_self_eq_norm_sq, inner_toLp_ofSmooth, dirichletForm_ofSmooth, integralCLM_apply,
    integral_congr_ae (toLp_ofSmooth_ae_eq u)]
  simp only [← sq, real_inner_self_eq_norm_sq]
  rw [hsplit, hmean]
  linarith [hC u hu]

/-- The form `D(w, v) + (∫ w dV) (∫ v dV)` is coercive on `H¹(M)`, by the Poincaré–Wirtinger
inequality. -/
private theorem isCoercive_poissonForm : IsCoercive (poissonForm (I := I) (M := M)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_toLp_sq_le (I := I) (M := M)
  set V := (riemannianVolume I M).real univ
  have hV : 0 ≤ V⁻¹ := inv_nonneg.2 measureReal_nonneg
  refine ⟨(C + 1 + V⁻¹)⁻¹, by positivity, fun w ↦ ?_⟩
  have hD := dirichletForm_self_nonneg w
  have hw := hC w
  rw [← integralCLM_apply] at hw
  have hnorm := norm_sq_eq_dirichletForm_add w
  rw [poissonForm_apply, mul_assoc, ← sq, inv_mul_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (integralCLM w)]

/-- **The weak Poisson equation on a closed manifold.** On a closed connected manifold with a
continuous metric, let `f ∈ L²(M)` have integral zero. Then there is exactly one `w ∈ H¹(M)` of
integral zero solving `Δ⁺w = f` weakly, that is, with `D(w, v) = ∫ f v dV` for every
`v ∈ H¹(M)`, where `D` is the Dirichlet form. -/
theorem existsUnique_dirichletForm_eq (f : Lp ℝ 2 (riemannianVolume I M))
    (hf : ∫ x, f x ∂riemannianVolume I M = 0) :
    ∃! w : SobolevH1 I M, ∫ x, toLp w x ∂riemannianVolume I M = 0 ∧
      ∀ v, dirichletForm w v = ∫ x, f x * toLp v x ∂riemannianVolume I M := by
  -- The right-hand side as a continuous linear functional.
  set ℓ : StrongDual ℝ (SobolevH1 I M) := (innerSL ℝ f).comp toLp
  have hℓ (v : SobolevH1 I M) : ℓ v = ∫ x, f x * toLp v x ∂riemannianVolume I M := by
    simp [ℓ, L2.inner_def, mul_comm]
  obtain ⟨w, hw, huniq⟩ := isCoercive_poissonForm.existsUnique_forall_eq ℓ
  -- Testing against `1` shows that the Lax–Milgram solution has integral zero.
  have hw0 : integralCLM w = 0 := by
    have h1 := hw (ofSmooth 1)
    rw [poissonForm_apply, dirichletForm_ofSmooth_one, zero_add, integralCLM_apply,
      integralCLM_apply, integral_toLp_ofSmooth_one, hℓ,
      integral_congr_ae ((toLp_ofSmooth_ae_eq 1).mono fun x hx ↦ congrArg (f x * ·) hx)] at h1
    simp only [ContMDiffMap.coe_one, Pi.one_apply, mul_one, hf] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · rwa [integralCLM_apply]
    · have hμ : riemannianVolume I M = 0 := by
        rw [← Measure.measure_univ_eq_zero]
        exact (measureReal_eq_zero_iff (measure_ne_top _ univ)).1 h
      rw [integralCLM_apply]
      refine integral_eq_zero_of_ae ?_
      rw [Filter.EventuallyEq, ae_eq_bot.2 hμ]
      exact Filter.eventually_bot
  refine ⟨w, ⟨by rwa [← integralCLM_apply], fun v ↦ ?_⟩, fun w' ⟨hw'0, hw'⟩ ↦ huniq w' fun v ↦ ?_⟩
  · rw [← hℓ, ← hw v, poissonForm_apply, hw0, zero_mul, add_zero]
  · rw [poissonForm_apply, integralCLM_apply w', hw'0, zero_mul, add_zero, hw', hℓ]

/-- **Solvability of the weak Poisson equation.** On a closed connected manifold with a
continuous metric, the equation `Δ⁺w = f` has a weak solution `w ∈ H¹(M)` exactly when
`∫ f dV = 0`. -/
theorem exists_forall_dirichletForm_eq_iff (f : Lp ℝ 2 (riemannianVolume I M)) :
    (∃ w : SobolevH1 I M,
        ∀ v, dirichletForm w v = ∫ x, f x * toLp v x ∂riemannianVolume I M) ↔
      ∫ x, f x ∂riemannianVolume I M = 0 := by
  refine ⟨fun ⟨w, hw⟩ ↦ ?_, fun hf ↦ (existsUnique_dirichletForm_eq f hf).exists.imp
    fun w hw ↦ hw.2⟩
  have h1 := hw (ofSmooth 1)
  rw [dirichletForm_ofSmooth_one,
    integral_congr_ae ((toLp_ofSmooth_ae_eq 1).mono fun x hx ↦ congrArg (f x * ·) hx)] at h1
  simpa using h1.symm

variable [IsManifold I ∞ M] [T2Space M]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **The distributional Poisson equation.** On a closed connected manifold with a `C¹` metric,
let `f ∈ L²(M)` have integral zero. Then there is `w ∈ H¹(M)` of integral zero with
`∫ w Δ⁺φ dV = ∫ f φ dV` for every smooth function `φ`, where `Δ⁺ = -div grad`. -/
theorem exists_integral_mul_neg_laplaceBeltrami_eq (f : Lp ℝ 2 (riemannianVolume I M))
    (hf : ∫ x, f x ∂riemannianVolume I M = 0) :
    ∃ w : SobolevH1 I M, ∫ x, toLp w x ∂riemannianVolume I M = 0 ∧
      ∀ φ : C^∞⟮I, M; ℝ⟯, ∫ x, toLp w x * -laplaceBeltrami I φ x ∂riemannianVolume I M =
        ∫ x, f x * φ x ∂riemannianVolume I M := by
  obtain ⟨w, ⟨hw0, hw⟩, -⟩ := existsUnique_dirichletForm_eq f hf
  refine ⟨w, hw0, fun φ ↦ ?_⟩
  rw [← dirichletForm_ofSmooth_right, hw]
  exact integral_congr_ae ((toLp_ofSmooth_ae_eq φ).mono fun x hx ↦ congrArg (f x * ·) hx)

end TauCeti.Manifold.SobolevH1
