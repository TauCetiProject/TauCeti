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
Levi-Civita derivative and the native curvature tensor. They apply within arbitrary parameter
sets, including at interval endpoints; unrestricted derivatives follow on the full parameter line.
The induced Hom formula needs only pointwise `C³` regularity of the function on a `C³` manifold
with a `C²` metric.
-/

public noncomputable section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff InnerProductSpace Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {γ : ℝ → M} {P Q : ∀ r, TangentSpace I (γ r)} {s : Set ℝ} {t : ℝ}

section FiniteRegularity

variable [IsManifold I 3 M]
  [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]

/-- Within a parameter set, a Hessian pairing in parallel fields differentiates by its induced
Hom connection. Pointwise `C³` regularity of the function and a `C²` metric suffice. -/
theorem hasDerivWithinAt_hessian_parallel_hom (hf : ContMDiffAt I 𝓘(ℝ) 3 f (γ t))
    (hP : MDifferentiableWithinAt 𝓘(ℝ) I.tangent (fun r ↦ TotalSpace.mk' E (γ r) (P r)) s t)
    (hQ : MDifferentiableWithinAt 𝓘(ℝ) I.tangent (fun r ↦ TotalSpace.mk' E (γ r) (Q r)) s t)
    (hP₀ : alongCurveWithin (leviCivitaConnection I M) γ P s t = 0)
    (hQ₀ : alongCurveWithin (leviCivitaConnection I M) γ Q s t = 0) :
    HasDerivWithinAt (fun s ↦ hessian I f (γ s) (P s) (Q s))
      ⟪(leviCivitaConnection I M).hom (leviCivitaConnection I M)
        (fun x ↦ leviCivitaConnection I M (mgradient I f) x)
        (γ t) (curveVelocityWithin I γ s t) (P t), Q t⟫_ℝ s t := by
  let cov := leviCivitaConnection I M
  let G := mgradient I f
  let A := fun x ↦ cov G x
  by_cases hs : UniqueDiffWithinAt ℝ s t
  swap
  · exact hasDerivWithinAt_iff_hasFDerivWithinAt.2
      (.of_not_accPt (mt AccPt.uniqueDiffWithinAt hs))
  have hγ : MDifferentiableWithinAt 𝓘(ℝ) I γ s t :=
    (Bundle.mdifferentiableAt_proj (fun x : M ↦ TangentSpace I x)).comp_mdifferentiableWithinAt
      t hP
  obtain ⟨U, hU, hx, hfU⟩ :=
    (contMDiffWithinAt_univ.2 hf).contMDiffOn' le_rfl (by simp)
  simp only [insert_eq_of_mem (mem_univ _), univ_inter] at hfU
  have : IsManifold I (2 + 1) M := by
    norm_num
    infer_instance
  have hG : CMDiff[U] 2 (T% G) := by
    intro y hy
    exact (contMDiffAt_mgradient (n := 2)
      (by convert hfU.contMDiffAt (hU.mem_nhds hy) using 1; norm_num)).contMDiffWithinAt
  have hA := contMDiffOn_leviCivitaConnection (I := I) (n := 1) (m := 3) (k := 2)
    hU (by norm_num) (by norm_num) (by convert hG using 1; norm_num)
  have hAx := (hA.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hAP := (hAx.comp_mdifferentiableWithinAt t hγ).clm_bundle_apply hP
  have hcoordAP := differentiableWithinAt_sectionCoord γ (fun s ↦ A (γ s) (P s)) hAP
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hcoordQ := differentiableWithinAt_sectionCoord γ Q hQ
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hd := (isMetricCompatible_leviCivitaConnection I).hasDerivWithinAt_inner_alongCurveWithin
    hγ hcoordAP hcoordQ
  rw [alongCurveWithin_clm_apply cov γ P A hs hAx hP,
    hP₀, map_zero, add_zero, hQ₀, inner_zero_right, add_zero] at hd
  simpa only [hessian_def] using hd

/-- A Hessian pairing in parallel fields differentiates by its induced
Hom connection. Pointwise `C³` regularity of the function and a `C²` metric suffice. -/
theorem hasDerivAt_hessian_parallel_hom (hf : ContMDiffAt I 𝓘(ℝ) 3 f (γ t))
    (hP : MDifferentiableAt 𝓘(ℝ) I.tangent (fun r ↦ TotalSpace.mk' E (γ r) (P r)) t)
    (hQ : MDifferentiableAt 𝓘(ℝ) I.tangent (fun r ↦ TotalSpace.mk' E (γ r) (Q r)) t)
    (hP₀ : alongCurve (leviCivitaConnection I M) γ P t = 0)
    (hQ₀ : alongCurve (leviCivitaConnection I M) γ Q t = 0) :
    HasDerivAt (fun s ↦ hessian I f (γ s) (P s) (Q s))
      ⟪(leviCivitaConnection I M).hom (leviCivitaConnection I M)
        (fun x ↦ leviCivitaConnection I M (mgradient I f) x)
        (γ t) (curveVelocity I γ t) (P t), Q t⟫_ℝ t := by
  simpa only [hasDerivWithinAt_univ, alongCurveWithin_univ, curveVelocityWithin_univ] using
    hasDerivWithinAt_hessian_parallel_hom (s := univ) hf hP.mdifferentiableWithinAt
      hQ.mdifferentiableWithinAt (by simpa using hP₀) (by simpa using hQ₀)

end FiniteRegularity

section Smooth

variable [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Within a parameter set, parallel-field Hessian entries satisfy Riccati on a local
eikonal domain. -/
theorem hasDerivWithinAt_hessian_riccati_parallel_on {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ) ∞ f U) (hx : γ t ∈ U) {c : ℝ}
    (hc : ∀ x ∈ U, ‖mgradient I f x‖ ^ 2 = c)
    (hγ' : curveVelocityWithin I γ s t = mgradient I f (γ t))
    (hP : MDifferentiableWithinAt 𝓘(ℝ) I.tangent (fun r ↦ TotalSpace.mk' E (γ r) (P r)) s t)
    (hQ : MDifferentiableWithinAt 𝓘(ℝ) I.tangent (fun r ↦ TotalSpace.mk' E (γ r) (Q r)) s t)
    (hP₀ : alongCurveWithin (leviCivitaConnection I M) γ P s t = 0)
    (hQ₀ : alongCurveWithin (leviCivitaConnection I M) γ Q s t = 0) :
    HasDerivWithinAt (fun s ↦ hessian I f (γ s) (P s) (Q s))
      (-(⟪leviCivitaConnection I M (mgradient I f) (γ t) (P t),
          leviCivitaConnection I M (mgradient I f) (γ t) (Q t)⟫_ℝ +
        ⟪(leviCivitaConnection I M).curvatureTensor (γ t) (P t)
          (mgradient I f (γ t)) (mgradient I f (γ t)), Q t⟫_ℝ)) s t := by
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
  have hd := hasDerivWithinAt_hessian_parallel_hom
    ((hf.contMDiffAt (hU.mem_nhds hx)).of_le (by simp)) hP hQ hP₀ hQ₀
  rw [hγ'] at hd
  dsimp only [cov, G] at hval
  rwa [hval] at hd

/-- The actual parallel-field Hessian entries satisfy Riccati on a local eikonal domain. -/
theorem hasDerivAt_hessian_riccati_parallel_on {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ) ∞ f U) (hx : γ t ∈ U) {c : ℝ}
    (hc : ∀ x ∈ U, ‖mgradient I f x‖ ^ 2 = c)
    (hγ' : curveVelocity I γ t = mgradient I f (γ t))
    (hP : MDifferentiableAt 𝓘(ℝ) I.tangent (fun r ↦ TotalSpace.mk' E (γ r) (P r)) t)
    (hQ : MDifferentiableAt 𝓘(ℝ) I.tangent (fun r ↦ TotalSpace.mk' E (γ r) (Q r)) t)
    (hP₀ : alongCurve (leviCivitaConnection I M) γ P t = 0)
    (hQ₀ : alongCurve (leviCivitaConnection I M) γ Q t = 0) :
    HasDerivAt (fun s ↦ hessian I f (γ s) (P s) (Q s))
      (-(⟪leviCivitaConnection I M (mgradient I f) (γ t) (P t),
          leviCivitaConnection I M (mgradient I f) (γ t) (Q t)⟫_ℝ +
        ⟪(leviCivitaConnection I M).curvatureTensor (γ t) (P t)
          (mgradient I f (γ t)) (mgradient I f (γ t)), Q t⟫_ℝ)) t := by
  simpa only [hasDerivWithinAt_univ, alongCurveWithin_univ, curveVelocityWithin_univ] using
    hasDerivWithinAt_hessian_riccati_parallel_on (s := univ) hU hf hx hc (by simpa using hγ')
      hP.mdifferentiableWithinAt hQ.mdifferentiableWithinAt
      (by simpa using hP₀) (by simpa using hQ₀)

/-- Within a parameter set, differentiating a Hessian pairing in parallel fields gives the
gradient's second covariant derivative. -/
theorem hasDerivWithinAt_hessian_parallel (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hP : MDifferentiableWithinAt 𝓘(ℝ) I.tangent (fun r ↦ TotalSpace.mk' E (γ r) (P r)) s t)
    (hQ : MDifferentiableWithinAt 𝓘(ℝ) I.tangent (fun r ↦ TotalSpace.mk' E (γ r) (Q r)) s t)
    (hP₀ : alongCurveWithin (leviCivitaConnection I M) γ P s t = 0)
    (hQ₀ : alongCurveWithin (leviCivitaConnection I M) γ Q s t = 0) :
    HasDerivWithinAt (fun s ↦ hessian I f (γ s) (P s) (Q s))
      ⟪(leviCivitaConnection I M).secondCovariantDerivative (leviCivitaConnection I M)
        (mgradient I f) (γ t) (curveVelocityWithin I γ s t) (P t), Q t⟫_ℝ s t := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  rw [secondCovariantDerivative_eq_hom_apply _ _
    (contMDiff_mgradient (I := I) (n := ∞) (by simpa using hf))]
  exact hasDerivWithinAt_hessian_parallel_hom (hf.contMDiffAt.of_le (by simp)) hP hQ hP₀ hQ₀

/-- Differentiating a Hessian pairing in parallel fields gives the gradient's second derivative. -/
theorem hasDerivAt_hessian_parallel (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hP : MDifferentiableAt 𝓘(ℝ) I.tangent (fun r ↦ TotalSpace.mk' E (γ r) (P r)) t)
    (hQ : MDifferentiableAt 𝓘(ℝ) I.tangent (fun r ↦ TotalSpace.mk' E (γ r) (Q r)) t)
    (hP₀ : alongCurve (leviCivitaConnection I M) γ P t = 0)
    (hQ₀ : alongCurve (leviCivitaConnection I M) γ Q t = 0) :
    HasDerivAt (fun s ↦ hessian I f (γ s) (P s) (Q s))
      ⟪(leviCivitaConnection I M).secondCovariantDerivative (leviCivitaConnection I M)
        (mgradient I f) (γ t) (curveVelocity I γ t) (P t), Q t⟫_ℝ t := by
  simpa only [hasDerivWithinAt_univ, alongCurveWithin_univ, curveVelocityWithin_univ] using
    hasDerivWithinAt_hessian_parallel (s := univ) hf hP.mdifferentiableWithinAt
      hQ.mdifferentiableWithinAt (by simpa using hP₀) (by simpa using hQ₀)

/-- Within a parameter set, the entries of the eikonal Hessian satisfy Riccati in parallel
fields. -/
theorem hasDerivWithinAt_hessian_riccati_parallel (hf : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : ∀ x, ‖mgradient I f x‖ ^ 2 = c)
    (hγ' : curveVelocityWithin I γ s t = mgradient I f (γ t))
    (hP : MDifferentiableWithinAt 𝓘(ℝ) I.tangent (fun r ↦ TotalSpace.mk' E (γ r) (P r)) s t)
    (hQ : MDifferentiableWithinAt 𝓘(ℝ) I.tangent (fun r ↦ TotalSpace.mk' E (γ r) (Q r)) s t)
    (hP₀ : alongCurveWithin (leviCivitaConnection I M) γ P s t = 0)
    (hQ₀ : alongCurveWithin (leviCivitaConnection I M) γ Q s t = 0) :
    HasDerivWithinAt (fun s ↦ hessian I f (γ s) (P s) (Q s))
      (-(⟪leviCivitaConnection I M (mgradient I f) (γ t) (P t),
          leviCivitaConnection I M (mgradient I f) (γ t) (Q t)⟫_ℝ +
        ⟪(leviCivitaConnection I M).curvatureTensor (γ t) (P t)
          (mgradient I f (γ t)) (mgradient I f (γ t)), Q t⟫_ℝ)) s t := by
  exact hasDerivWithinAt_hessian_riccati_parallel_on isOpen_univ hf.contMDiffOn (mem_univ _)
    (fun x _ ↦ hc x) hγ' hP hQ hP₀ hQ₀

/-- The entries of the eikonal Hessian satisfy the Riccati equation in actual parallel fields. -/
theorem hasDerivAt_hessian_riccati_parallel (hf : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : ∀ x, ‖mgradient I f x‖ ^ 2 = c)
    (hγ' : curveVelocity I γ t = mgradient I f (γ t))
    (hP : MDifferentiableAt 𝓘(ℝ) I.tangent (fun r ↦ TotalSpace.mk' E (γ r) (P r)) t)
    (hQ : MDifferentiableAt 𝓘(ℝ) I.tangent (fun r ↦ TotalSpace.mk' E (γ r) (Q r)) t)
    (hP₀ : alongCurve (leviCivitaConnection I M) γ P t = 0)
    (hQ₀ : alongCurve (leviCivitaConnection I M) γ Q t = 0) :
    HasDerivAt (fun s ↦ hessian I f (γ s) (P s) (Q s))
      (-(⟪leviCivitaConnection I M (mgradient I f) (γ t) (P t),
          leviCivitaConnection I M (mgradient I f) (γ t) (Q t)⟫_ℝ +
        ⟪(leviCivitaConnection I M).curvatureTensor (γ t) (P t)
          (mgradient I f (γ t)) (mgradient I f (γ t)), Q t⟫_ℝ)) t := by
  simpa only [hasDerivWithinAt_univ, alongCurveWithin_univ, curveVelocityWithin_univ] using
    hasDerivWithinAt_hessian_riccati_parallel (s := univ) hf hc (by simpa using hγ')
      hP.mdifferentiableWithinAt hQ.mdifferentiableWithinAt
      (by simpa using hP₀) (by simpa using hQ₀)

end Smooth

end TauCeti.Manifold
