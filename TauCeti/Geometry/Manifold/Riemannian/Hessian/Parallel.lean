/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hessian.Riccati
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric

/-!
# Differentiating Hessians in parallel fields

For two parallel tangent fields along a differentiable curve, the derivative of the Hessian
pairing is the corresponding second covariant derivative of the gradient. On an integral curve
of a constant-speed eikonal gradient, the intrinsic Riccati identity therefore gives the actual
parallel-frame scalar entries `H' = -A² - R`.

The statements use native tangent fields, their total-space differentiability, the native
Levi-Civita derivative and the native curvature tensor.
-/

public noncomputable section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff InnerProductSpace Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {γ : ℝ → M} {P Q : ∀ s, TangentSpace I (γ s)} {t : ℝ}

omit [T2Space M] in
/-- On an open smoothness domain, a Hessian pairing in parallel fields differentiates by
its native induced Hom connection. -/
theorem hasDerivAt_hessian_parallel_on {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ) ∞ f U) (hx : γ t ∈ U)
    (hγ : MDiffAt γ t)
    (hP : MDifferentiableAt 𝓘(ℝ) I.tangent (fun s ↦ TotalSpace.mk' E (γ s) (P s)) t)
    (hQ : MDifferentiableAt 𝓘(ℝ) I.tangent (fun s ↦ TotalSpace.mk' E (γ s) (Q s)) t)
    (hP₀ : alongCurve (leviCivitaConnection I M) γ P t = 0)
    (hQ₀ : alongCurve (leviCivitaConnection I M) γ Q t = 0) :
    HasDerivAt (fun s ↦ hessian I f (γ s) (P s) (Q s))
      ⟪(leviCivitaConnection I M).hom (leviCivitaConnection I M)
        (fun x ↦ leviCivitaConnection I M (mgradient I f) x)
        (γ t) (curveVelocity I γ t) (P t), Q t⟫_ℝ t := by
  let cov := leviCivitaConnection I M
  let G := mgradient I f
  let A := fun x ↦ cov G x
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hG : CMDiff[U] ∞ (T% G) := by
    intro y hy
    exact (contMDiffAt_mgradient (n := ∞)
      (by simpa using hf.contMDiffAt (hU.mem_nhds hy))).contMDiffWithinAt
  have hA := contMDiffOn_leviCivitaConnection (I := I) (n := ∞) (m := ∞) (k := ∞)
    hU (by simp) (by simp) (by simpa using hG)
  have hAx := (hA.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hAP := (hAx.comp t hγ).clm_bundle_apply hP
  have hcoordAP := differentiableAt_sectionCoord γ (fun s ↦ A (γ s) (P s)) hAP
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hcoordQ := differentiableAt_sectionCoord γ Q hQ
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hd := (isMetricCompatible_leviCivitaConnection I).hasDerivAt_inner_alongCurve
    hγ hcoordAP hcoordQ
  rw [alongCurve_clm_apply cov γ P A hAx hP,
    hP₀, map_zero, add_zero, hQ₀, inner_zero_right, add_zero] at hd
  simpa only [hessian_def] using hd

/-- The actual parallel-field Hessian entries satisfy Riccati on a local eikonal domain. -/
theorem hasDerivAt_hessian_riccati_parallel_on {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ) ∞ f U) (hx : γ t ∈ U) {c : ℝ}
    (hc : ∀ x ∈ U, ‖mgradient I f x‖ ^ 2 = c) (hγ : MDiffAt γ t)
    (hγ' : curveVelocity I γ t = mgradient I f (γ t))
    (hP : MDifferentiableAt 𝓘(ℝ) I.tangent (fun s ↦ TotalSpace.mk' E (γ s) (P s)) t)
    (hQ : MDifferentiableAt 𝓘(ℝ) I.tangent (fun s ↦ TotalSpace.mk' E (γ s) (Q s)) t)
    (hP₀ : alongCurve (leviCivitaConnection I M) γ P t = 0)
    (hQ₀ : alongCurve (leviCivitaConnection I M) γ Q t = 0) :
    HasDerivAt (fun s ↦ hessian I f (γ s) (P s) (Q s))
      (-(⟪leviCivitaConnection I M (mgradient I f) (γ t) (P t),
          leviCivitaConnection I M (mgradient I f) (γ t) (Q t)⟫_ℝ +
        ⟪(leviCivitaConnection I M).curvatureTensor (γ t) (P t)
          (mgradient I f (γ t)) (mgradient I f (γ t)), Q t⟫_ℝ)) t := by
  let cov := leviCivitaConnection I M
  let G := mgradient I f
  have hric := hom_mgradient_riccati_on hU hf hc hx (P t)
  have hpair := congrArg (fun w : TangentSpace I (γ t) ↦ ⟪w, Q t⟫_ℝ) hric
  simp only [inner_add_left, inner_zero_left] at hpair
  have hsym : ⟪cov G (γ t) (cov G (γ t) (P t)), Q t⟫_ℝ =
      ⟪cov G (γ t) (P t), cov G (γ t) (Q t)⟫_ℝ := by
    simpa only [hessian_def, real_inner_comm] using
      hessian_symm (γ t) ((hf.contMDiffAt (hU.mem_nhds hx)).of_le (by simp : (2 : ℕ∞ω) ≤ ∞))
        (cov G (γ t) (P t)) (Q t)
  have hval : ⟪cov.hom cov (fun x ↦ cov G x) (γ t) (G (γ t)) (P t), Q t⟫_ℝ =
      -(⟪cov G (γ t) (P t), cov G (γ t) (Q t)⟫_ℝ +
        ⟪cov.curvatureTensor (γ t) (P t) (G (γ t)) (G (γ t)), Q t⟫_ℝ) := by
    dsimp only [cov, G] at hsym ⊢
    rw [hsym] at hpair
    linarith
  have hd := hasDerivAt_hessian_parallel_on hU hf hx hγ hP hQ hP₀ hQ₀
  rw [hγ'] at hd
  dsimp only [cov, G] at hval
  rwa [hval] at hd

/-- Differentiating a Hessian pairing in parallel fields gives the gradient's second derivative. -/
theorem hasDerivAt_hessian_parallel (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hγ : MDiffAt γ t)
    (hP : MDifferentiableAt 𝓘(ℝ) I.tangent (fun s ↦ TotalSpace.mk' E (γ s) (P s)) t)
    (hQ : MDifferentiableAt 𝓘(ℝ) I.tangent (fun s ↦ TotalSpace.mk' E (γ s) (Q s)) t)
    (hP₀ : alongCurve (leviCivitaConnection I M) γ P t = 0)
    (hQ₀ : alongCurve (leviCivitaConnection I M) γ Q t = 0) :
    HasDerivAt (fun s ↦ hessian I f (γ s) (P s) (Q s))
      ⟪(leviCivitaConnection I M).secondCovariantDerivative (leviCivitaConnection I M)
        (mgradient I f) (γ t) (curveVelocity I γ t) (P t), Q t⟫_ℝ t := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  rw [secondCovariantDerivative_eq_hom_apply _ _
    (contMDiff_mgradient (I := I) (n := ∞) (by simpa using hf))]
  exact hasDerivAt_hessian_parallel_on isOpen_univ hf.contMDiffOn (mem_univ _) hγ hP hQ hP₀ hQ₀

/-- The entries of the eikonal Hessian satisfy the Riccati equation in actual parallel fields. -/
theorem hasDerivAt_hessian_riccati_parallel (hf : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : ∀ x, ‖mgradient I f x‖ ^ 2 = c) (hγ : MDiffAt γ t)
    (hγ' : curveVelocity I γ t = mgradient I f (γ t))
    (hP : MDifferentiableAt 𝓘(ℝ) I.tangent (fun s ↦ TotalSpace.mk' E (γ s) (P s)) t)
    (hQ : MDifferentiableAt 𝓘(ℝ) I.tangent (fun s ↦ TotalSpace.mk' E (γ s) (Q s)) t)
    (hP₀ : alongCurve (leviCivitaConnection I M) γ P t = 0)
    (hQ₀ : alongCurve (leviCivitaConnection I M) γ Q t = 0) :
    HasDerivAt (fun s ↦ hessian I f (γ s) (P s) (Q s))
      (-(⟪leviCivitaConnection I M (mgradient I f) (γ t) (P t),
          leviCivitaConnection I M (mgradient I f) (γ t) (Q t)⟫_ℝ +
        ⟪(leviCivitaConnection I M).curvatureTensor (γ t) (P t)
          (mgradient I f (γ t)) (mgradient I f (γ t)), Q t⟫_ℝ)) t := by
  exact hasDerivAt_hessian_riccati_parallel_on isOpen_univ hf.contMDiffOn (mem_univ _)
    (fun x _ ↦ hc x) hγ hγ' hP hQ hP₀ hQ₀

end TauCeti.Manifold
