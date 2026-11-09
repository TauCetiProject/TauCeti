/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hessian.Eikonal
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Hessian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The Riccati identity for an eikonal gradient

For a smooth function with constant gradient length, its Hessian endomorphism satisfies the
intrinsic Riccati identity along the gradient. Writing `G = grad f`, `A(v) = ∇_v G` and using
the second covariant derivative,

`∇²G(G,v) + A(A(v)) + R(v,G)G = 0`.

The first term is the covariant derivative of `A` in direction `G`. In a parallel frame along
an integral curve of `G`, this is the matrix identity `A' + A² + R = 0`. The identity uses the
curvature convention `R(u,v)w = ∇_u∇_v w - ∇_v∇_u w - ∇_[u,v]w`.

See J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 11.
-/

public noncomputable section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The Hessian endomorphism of a constant-speed eikonal function satisfies the intrinsic
Riccati identity along its gradient. -/
theorem secondCovariantDerivative_mgradient_riccati {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : ∀ x, ‖mgradient I f x‖ ^ 2 = c) (x : M) (v : TangentSpace I x) :
    (leviCivitaConnection I M).secondCovariantDerivative (leviCivitaConnection I M)
        (mgradient I f) x (mgradient I f x) v +
      leviCivitaConnection I M (mgradient I f) x
        (leviCivitaConnection I M (mgradient I f) x v) +
      (leviCivitaConnection I M).curvatureTensor x v (mgradient I f x) (mgradient I f x) =
        0 := by
  let cov := leviCivitaConnection I M
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hG : CMDiff ∞ (T% (mgradient I f)) := contMDiff_mgradient (by simpa using hf)
  have hzero (y : M) : cov (mgradient I f) y (mgradient I f y) = 0 := by
    apply ext_inner_right ℝ
    intro w
    simpa only [inner_zero_left, hessian_def] using
      hessian_mgradient_eq_zero_of_eventually_norm_sq_eq_const
        ((hf.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contMDiffAt)
        (Filter.Eventually.of_forall hc) w
  have hz : (fun y ↦ cov (mgradient I f) y (mgradient I f y)) = 0 := funext hzero
  have hsecond := cov.secondCovariantDerivative_apply cov hG x hG v
  rw [hz, cov.zero, Pi.zero_apply, zero_apply, zero_sub] at hsecond
  have ht : cov.IsTorsionFree := (isTorsionFree_iff_torsion_eq_zero cov).2
    (torsion_leviCivitaConnection_eq_zero I)
  have hR := cov.secondCovariantDerivative_sub_swap_of_isTorsionFree cov ht hG x v
    (mgradient I f x)
  rw [hsecond] at hR
  change cov.secondCovariantDerivative cov (mgradient I f) x (mgradient I f x) v +
    cov (mgradient I f) x (cov (mgradient I f) x v) +
    cov.curvatureTensor x v (mgradient I f x) (mgradient I f x) = 0
  rw [← hR]
  abel

/-- On an open eikonal domain, the induced Hom derivative of the Hessian endomorphism
satisfies the Riccati identity. This local form does not require a globally smooth function. -/
theorem hom_mgradient_riccati_on {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ) ∞ f U) {c : ℝ}
    (hc : ∀ x ∈ U, ‖mgradient I f x‖ ^ 2 = c) {x : M} (hx : x ∈ U)
    (v : TangentSpace I x) :
    (leviCivitaConnection I M).hom (leviCivitaConnection I M)
        (fun y ↦ leviCivitaConnection I M (mgradient I f) y) x (mgradient I f x) v +
      leviCivitaConnection I M (mgradient I f) x
        (leviCivitaConnection I M (mgradient I f) x v) +
      (leviCivitaConnection I M).curvatureTensor x v (mgradient I f x) (mgradient I f x) =
        0 := by
  let cov := leviCivitaConnection I M
  let G := mgradient I f
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hG : CMDiff[U] ∞ (T% G) := by
    intro y hy
    exact (contMDiffAt_mgradient (n := ∞)
      (by simpa using hf.contMDiffAt (hU.mem_nhds hy))).contMDiffWithinAt
  have hA := contMDiffOn_leviCivitaConnection (I := I) (n := ∞) (m := ∞) (k := ∞)
    hU (by simp) (by simp) (by simpa using hG)
  have hS := hA.clm_bundle_apply hG
  have hzero (y : M) (hy : y ∈ U) : cov G y (G y) = 0 := by
    apply ext_inner_right ℝ
    intro w
    simpa only [inner_zero_left, hessian_def] using
      hessian_mgradient_eq_zero_of_eventually_norm_sq_eq_const
        ((hf.contMDiffAt (hU.mem_nhds hy)).of_le (by simp))
        (Filter.eventually_of_mem (hU.mem_nhds hy) (fun z hz ↦ hc z hz)) w
  have hSzero : cov (fun y ↦ cov G y (G y)) x = 0 := by
    have heq := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      ((hS.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      ((contMDiff_zeroSection (n := 1) ℝ (TangentSpace I : M → Type _)).mdifferentiable (by simp) x)
      (Filter.univ_mem) (Filter.eventually_of_mem (hU.mem_nhds hx) hzero)
    change cov (fun y ↦ cov G y (G y)) x =
      cov (0 : Π y : M, TangentSpace I y) x at heq
    simpa only [cov.zero, Pi.zero_apply] using heq
  obtain ⟨Y, hY, hv⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ v
  have hGx := (hG.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hYx := hY.mdifferentiable (by simp) x
  have hhom := hom_apply cov cov
    ((hA.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)) hYx (G x)
  have hR := cov.curvatureTensor_apply_of_contMDiffOn x hU hx hY.contMDiffOn hG hG
  rw [curvatureOperator_apply, hSzero, zero_apply, zero_sub] at hR
  have ht : cov.IsTorsionFree := (isTorsionFree_iff_torsion_eq_zero cov).mpr
    (torsion_leviCivitaConnection_eq_zero I)
  have hbracket := ((isTorsionFree_iff cov).mp ht hYx hGx).symm
  rw [hbracket, map_sub] at hR
  rw [hv] at hR hhom
  change cov.hom cov (fun y ↦ cov G y) x (G x) v + cov G x (cov G x v) +
    cov.curvatureTensor x v (G x) (G x) = 0
  rw [hhom, hR]
  abel

end TauCeti.Manifold
