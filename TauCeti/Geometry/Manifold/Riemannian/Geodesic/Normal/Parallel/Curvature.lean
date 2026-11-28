/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Parallel.Joint
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.AlongCurve
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Smoothness

/-!
# Curvature components in the radial parallel frame

Transporting tangent vectors from the centre of a normal domain gives smooth curvature
components on its fixed initial tangent space. Their first derivative consists of the intrinsic
covariant derivative of curvature and one connection correction for each of the four slots.
The frame is the actual radial parallel frame constructed from the native transport equation.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Lemma 5.7.
* Formalization references: https://github.com/frenzymath/lean-eval-submissions and
  https://github.com/frenzymath/PoincareConjecture.
-/

public noncomputable section

open Bundle CovariantDerivative Set
open scoped ContDiff InnerProductSpace Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  {p : M} {U : Set (TangentSpace I p)}
  [I.Boundaryless] [T2Space M]

namespace IsNormalDomain

/-- Real-valued components of the Riemann curvature tensor in the frame obtained by radial
parallel transport from the centre. The four inputs are vectors in the fixed initial tangent
space. Outside the normal domain, the value is totalized by the zero endpoint transport. -/
def radialCurvatureComponent (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (a u v z x : TangentSpace I p) : ℝ :=
  ⟪h.radialParallelEndpoint b x a,
    (leviCivitaConnection I M).curvatureTensor (riemannianExp I M p x)
      (h.radialParallelEndpoint b x u) (h.radialParallelEndpoint b x v)
      (h.radialParallelEndpoint b x z)⟫_ℝ

/-- A radial-frame curvature component is the native curvature tensor evaluated on the four
radially transported tangent vectors. -/
theorem radialCurvatureComponent_apply (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (a u v z x : TangentSpace I p) :
    h.radialCurvatureComponent b a u v z x =
      ⟪h.radialParallelEndpoint b x a,
        (leviCivitaConnection I M).curvatureTensor (riemannianExp I M p x)
          (h.radialParallelEndpoint b x u) (h.radialParallelEndpoint b x v)
          (h.radialParallelEndpoint b x z)⟫_ℝ := by rfl

section

variable (h : IsNormalDomain I M p U) (b : OrthonormalBasis ι ℝ (TangentSpace I p))
  (a a' u u' v v' z z' x : TangentSpace I p) (c : ℝ)

/-- Radial curvature is additive in the vector paired with the curvature output. -/
@[simp]
theorem radialCurvatureComponent_add_a :
    h.radialCurvatureComponent b (a + a') u v z x =
      h.radialCurvatureComponent b a u v z x + h.radialCurvatureComponent b a' u v z x := by
  simp [radialCurvatureComponent_apply, inner_add_left]

/-- Radial curvature is additive in the first curvature direction. -/
@[simp]
theorem radialCurvatureComponent_add_u :
    h.radialCurvatureComponent b a (u + u') v z x =
      h.radialCurvatureComponent b a u v z x + h.radialCurvatureComponent b a u' v z x := by
  simp [radialCurvatureComponent_apply, inner_add_right]

/-- Radial curvature is additive in the second curvature direction. -/
@[simp]
theorem radialCurvatureComponent_add_v :
    h.radialCurvatureComponent b a u (v + v') z x =
      h.radialCurvatureComponent b a u v z x + h.radialCurvatureComponent b a u v' z x := by
  simp [radialCurvatureComponent_apply, inner_add_right]

/-- Radial curvature is additive in the vector on which curvature acts. -/
@[simp]
theorem radialCurvatureComponent_add_z :
    h.radialCurvatureComponent b a u v (z + z') x =
      h.radialCurvatureComponent b a u v z x + h.radialCurvatureComponent b a u v z' x := by
  simp [radialCurvatureComponent_apply, inner_add_right]

/-- A real scalar on the vector paired with the curvature output factors out. -/
@[simp]
theorem radialCurvatureComponent_smul_a :
    h.radialCurvatureComponent b (c • a) u v z x = c * h.radialCurvatureComponent b a u v z x := by
  simp [radialCurvatureComponent_apply, real_inner_smul_left]

/-- A real scalar on the first curvature direction factors out. -/
@[simp]
theorem radialCurvatureComponent_smul_u :
    h.radialCurvatureComponent b a (c • u) v z x = c * h.radialCurvatureComponent b a u v z x := by
  simp [radialCurvatureComponent_apply, real_inner_smul_right]

/-- A real scalar on the second curvature direction factors out. -/
@[simp]
theorem radialCurvatureComponent_smul_v :
    h.radialCurvatureComponent b a u (c • v) z x = c * h.radialCurvatureComponent b a u v z x := by
  simp [radialCurvatureComponent_apply, real_inner_smul_right]

/-- A real scalar on the vector on which curvature acts factors out. -/
@[simp]
theorem radialCurvatureComponent_smul_z :
    h.radialCurvatureComponent b a u v (c • z) x = c * h.radialCurvatureComponent b a u v z x := by
  simp [radialCurvatureComponent_apply, real_inner_smul_right]

/-- Pairing the radial curvature output with the zero vector gives zero. -/
@[simp]
theorem radialCurvatureComponent_zero_a : h.radialCurvatureComponent b 0 u v z x = 0 := by
  simp [radialCurvatureComponent_apply]

/-- Radial curvature vanishes when its first curvature direction is zero. -/
@[simp]
theorem radialCurvatureComponent_zero_u : h.radialCurvatureComponent b a 0 v z x = 0 := by
  simp [radialCurvatureComponent_apply]

/-- Radial curvature vanishes when its second curvature direction is zero. -/
@[simp]
theorem radialCurvatureComponent_zero_v : h.radialCurvatureComponent b a u 0 z x = 0 := by
  simp [radialCurvatureComponent_apply]

/-- Acting on the zero vector gives zero radial curvature. -/
@[simp]
theorem radialCurvatureComponent_zero_z : h.radialCurvatureComponent b a u v 0 x = 0 := by
  simp [radialCurvatureComponent_apply]

end

/-- With the four initial vectors fixed, radial curvature components are independent of the
auxiliary orthonormal basis used to construct transport. -/
theorem radialCurvatureComponent_eq (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    {κ : Type*} [Fintype κ] [LinearOrder κ] [LocallyFiniteOrderBot κ]
    (b' : OrthonormalBasis κ ℝ (TangentSpace I p)) (a u v z x : TangentSpace I p) :
    h.radialCurvatureComponent b a u v z x = h.radialCurvatureComponent b' a u v z x := by
  simp only [radialCurvatureComponent_apply, h.radialParallelEndpoint_eq b b']

/-- Actual radial-frame curvature components are smooth on the normal domain. -/
theorem contDiffOn_radialCurvatureComponent (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (a u v z : TangentSpace I p) :
    ContDiffOn ℝ ∞ (h.radialCurvatureComponent b a u v z) U := by
  have hR := (leviCivitaConnection I M).contMDiffOn_curvatureTensor (by simp)
    (h.contMDiffOn_radialParallelEndpoint_apply b u)
    (h.contMDiffOn_radialParallelEndpoint_apply b v)
    (h.contMDiffOn_radialParallelEndpoint_apply b z)
  have hc : ContMDiffOn 𝓘(ℝ, TangentSpace I p) 𝓘(ℝ) ∞
      (h.radialCurvatureComponent b a u v z) U :=
    ContMDiffOn.inner_bundle (IM := 𝓘(ℝ, TangentSpace I p)) (IB := I)
      (F := E) (E := fun x : M ↦ TangentSpace I x)
      (h.contMDiffOn_radialParallelEndpoint_apply b a) hR
  exact hc.contDiffOn

/-- Differentiating actual radial-frame curvature along a parameter curve gives the native
covariant curvature derivative and the four frame-connection corrections. -/
theorem hasDerivAt_radialCurvatureComponent (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (a u v z : TangentSpace I p)
    {η : ℝ → TangentSpace I p} {t : ℝ} (hη : DifferentiableAt ℝ η t) (hηU : η t ∈ U) :
    let γ := fun s ↦ riemannianExp I M p (η s)
    let S := fun c s ↦ h.radialParallelEndpoint b (η s) c
    let D := fun c ↦ (leviCivitaConnection I M).alongCurve γ (S c) t
    HasDerivAt (fun s ↦ h.radialCurvatureComponent b a u v z (η s))
      (⟪D a, (leviCivitaConnection I M).curvatureTensor (γ t) (S u t) (S v t) (S z t)⟫_ℝ +
        ⟪S a t, (leviCivitaConnection I M).derivCurvatureTensor (leviCivitaConnection I M)
          (γ t) (curveVelocity I γ t) (S u t) (S v t) (S z t)⟫_ℝ +
        ⟪S a t, (leviCivitaConnection I M).curvatureTensor (γ t)
          (D u) (S v t) (S z t)⟫_ℝ +
        ⟪S a t, (leviCivitaConnection I M).curvatureTensor (γ t)
          (S u t) (D v) (S z t)⟫_ℝ +
        ⟪S a t, (leviCivitaConnection I M).curvatureTensor (γ t)
          (S u t) (S v t) (D z)⟫_ℝ) t := by
  dsimp only
  let γ := fun s ↦ riemannianExp I M p (η s)
  let S := fun c s ↦ h.radialParallelEndpoint b (η s) c
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
    ((contMDiffAt_riemannianExp (h.subset_expDomain hηU)).mdifferentiableAt
      (by simp)).comp t hη.mdifferentiableAt
  have hS (c : TangentSpace I p) :
      MDifferentiableAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E))
        (fun s ↦ TotalSpace.mk' E (γ s) (S c s)) t :=
    (((h.contMDiffOn_radialParallelEndpoint_apply b c).contMDiffAt
      (h.isOpen.mem_nhds hηU)).mdifferentiableAt (by simp)).comp t hη.mdifferentiableAt
  have hc (c : TangentSpace I p) :
      DifferentiableAt ℝ (sectionCoord ℝ (F := E) γ (S c) (γ t)) t :=
    differentiableAt_sectionCoord γ (S c) (hS c)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hRc : DifferentiableAt ℝ (sectionCoord ℝ (F := E) γ
      (fun s ↦ (leviCivitaConnection I M).curvatureTensor (γ s) (S u s) (S v s) (S z s))
      (γ t)) t := by
    apply differentiableWithinAt_univ.mp
    exact (leviCivitaConnection I M).differentiableWithinAt_sectionCoord_curvatureTensor
      hγ.mdifferentiableWithinAt (hc u).differentiableWithinAt
      (hc v).differentiableWithinAt (hc z).differentiableWithinAt
  have hR := (leviCivitaConnection I M).alongCurveWithin_curvatureTensor
    (s := univ) uniqueDiffWithinAt_univ hγ.mdifferentiableWithinAt
    (hc u).differentiableWithinAt (hc v).differentiableWithinAt (hc z).differentiableWithinAt
  simp only [alongCurveWithin_univ, curveVelocityWithin_univ] at hR
  have hd := (isMetricCompatible_leviCivitaConnection I).hasDerivAt_inner_alongCurve hγ (hc a) hRc
  rw [hR] at hd
  simpa only [radialCurvatureComponent_apply, γ, S, inner_add_right, add_assoc] using hd

/-- Along a radial geodesic all four frame corrections vanish, so differentiating the actual
transported curvature component gives precisely the intrinsic covariant curvature derivative. -/
theorem hasDerivAt_radialCurvatureComponent_radial (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (a u v z : TangentSpace I p)
    {x : TangentSpace I p} {t : ℝ} (ht : t • x ∈ U) :
    let γ := fun s : ℝ ↦ riemannianExp I M p (s • x)
    let S := fun c ↦ h.radialParallelEndpoint b (t • x) c
    HasDerivAt (fun s : ℝ ↦ h.radialCurvatureComponent b a u v z (s • x))
      ⟪S a, (leviCivitaConnection I M).derivCurvatureTensor (leviCivitaConnection I M)
        (γ t) (curveVelocity I γ t) (S u) (S v) (S z)⟫_ℝ t := by
  have hη : DifferentiableAt ℝ (fun s : ℝ ↦ s • x) t :=
    differentiableAt_id.smul_const x
  have hd := h.hasDerivAt_radialCurvatureComponent b a u v z hη
    ht
  simpa only [h.alongCurve_radialParallelEndpoint_eq_zero b ht,
    inner_zero_left, map_zero, LinearMap.zero_apply, inner_zero_right, zero_add, add_zero]
    using hd

end IsNormalDomain

end TauCeti.Manifold
