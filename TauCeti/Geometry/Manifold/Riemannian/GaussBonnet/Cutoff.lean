/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Cutoff
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Integral
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Polarization
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.RankTwo
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Total curvature against a cutoff in an orthonormal frame

Let `(e₀, e₁)` be a smooth positively oriented orthonormal frame on an open subset `U` of an
oriented boundaryless surface, and let `ω = A¹₀`, `ω(X) = ⟪e₁, ∇_X e₀⟫`, be its connection
one-form for a metric connection `∇`. For a compactly supported `C¹` function `φ` with
`tsupport φ ⊆ U`, the form `φ ω` is a compactly supported `C¹` one-form on the whole surface, so
Stokes's theorem gives `∫ d(φ ω) = 0`. With the Leibniz rule `d(φ ω) = dφ ∧ ω + φ dω` and the
structure equation `dω = -K vol` this is

`∫ dφ ∧ ω = ∫ φ K dV`,

where `K = Scal / 2` is the Gaussian curvature of `∇`
(`IsLocalFrameOn.integralTopForm_mextDeriv_ofFunction_wedge_connectionForm`).

This is the Stokes step of Chern's proof of the Gauss–Bonnet theorem: with `e₀ = X / ‖X‖` for a
vector field `X` with finitely many zeros, and `φ = 1` away from small discs around the zeros, it
reduces the total curvature to integrals over those discs, which see only the local behaviour of
`X` at its zeros.

## Main results

* `IsLocalFrameOn.mextDeriv_connectionForm_eq_neg_smul_riemannianVolumeForm`: the structure
  equation `dω = -K vol` as an equality of two-forms on the frame domain.
* `IsLocalFrameOn.integralTopForm_mextDeriv_ofFunction_wedge_connectionForm`:
  `∫ dφ ∧ ω = ∫ φ K dV` for a compactly supported `C¹` function `φ` supported in the frame domain.

## References

* S.-S. Chern, *A simple intrinsic proof of the Gauss–Bonnet formula for closed Riemannian
  manifolds*, Ann. of Math. 45 (1944), 747–752.
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Springer, 2018, Chapter 9.
-/

public section

noncomputable section

open Bundle CovariantDerivative MeasureTheory Set TauCeti
open scoped ContDiff Manifold Topology

namespace IsLocalFrameOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]
  {s : Fin 2 → Π x : M, TangentSpace I x} {u : Set M}
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  [ContMDiffCovariantDerivative cov ∞]

/-- On the domain of a local frame of a surface, the Gaussian curvature `Scal / 2` of a metric
connection is the sectional curvature of the frame. -/
private theorem sectionalCurvature_eq_scalarCurvature_div_two
    (o : Manifold.Orientation I M (Fin 2)) (hs : IsLocalFrameOn I E ∞ s u)
    (hcov : IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov) {x : M} (hx : x ∈ u) :
    cov.sectionalCurvature hcov x (s 0 x) (s 1 x) = cov.scalarCurvature x / 2 :=
  (cov.hasSectionalCurvatureAt_scalarCurvature_div_two hcov
    (by simpa using o.finrank_tangentSpace_eq x)).sectionalCurvature_eq _ _ (by
      -- `FinVec.etaExpand_eq` is Mathlib's eta rule `![v 0, v 1] = v` for `Fin 2` tuples.
      convert hs.linearIndependent hx using 1
      exact FinVec.etaExpand_eq fun i ↦ s i x)

/-- A continuous function supported in the domain of a local frame of a surface, times the
Gaussian curvature `Scal / 2` of a metric connection, is continuous: on the frame domain the
curvature is the sectional curvature of the frame. -/
private theorem continuous_mul_scalarCurvature_div_two (o : Manifold.Orientation I M (Fin 2))
    (hs : IsLocalFrameOn I E ∞ s u) (hu : IsOpen u)
    (hcov : IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov) {φ : M → ℝ}
    (hφ : Continuous φ) (hφu : tsupport φ ⊆ u) :
    Continuous fun x ↦ φ x * (cov.scalarCurvature x / 2) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  by_cases hx : x ∈ u
  · refine hφ.continuousAt.mul (ContinuousAt.congr ?_ (Filter.eventually_of_mem (hu.mem_nhds hx)
      fun y hy ↦ sectionalCurvature_eq_scalarCurvature_div_two o hs hcov hy))
    exact (cov.contMDiffAt_sectionalCurvature hcov (n := 2)
      ((hs.contMDiffAt hu hx 0).of_le (by simp)) ((hs.contMDiffAt hu hx 1).of_le (by simp)) (by
        convert hs.linearIndependent hx using 1
        exact FinVec.etaExpand_eq fun i ↦ s i x)).continuousAt
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hx (hφu h))] with y hy
    simp [hy]

variable [ContMDiffCovariantDerivative cov 1]

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]
  [ContMDiffCovariantDerivative cov ∞] in
/-- The connection one-form `A¹₀` of a smooth frame, for a `C¹` connection, is a `C¹` form on the
open frame domain. -/
private theorem contMDiffAt_connectionForm_zero_one (hs : IsLocalFrameOn I E ∞ s u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) 1
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (hs.connectionForm cov 0 1 y)) x :=
  have : ContMDiffCovariantDerivativeOn E 1 cov.toFun u :=
    cov.contMDiffCovariantDerivativeOn_of_isOpen (n := 1) hu
  hs.contMDiffAt_connectionForm cov (by simp) hu hx 0 1

/-- **The structure equation of an oriented surface.** For a metric connection and a smooth local
frame `(e₀, e₁)`, orthonormal and positively oriented on its open domain, the connection one-form
`ω = A¹₀`, `ω(X) = ⟪e₁, ∇_X e₀⟫`, satisfies `dω = -K vol` on the frame domain, where
`K = Scal / 2` is the Gaussian curvature of the connection. Positive orientation is stated as
`vol(e₀, e₁) = 1`; for unit vectors this is `e₁ = J e₀`
(`TauCeti.Manifold.Orientation.eq_rightAngleRotation_iff_riemannianVolumeForm_eq_one`). -/
theorem mextDeriv_connectionForm_eq_neg_smul_riemannianVolumeForm
    (o : Manifold.Orientation I M (Fin 2)) (hs : IsLocalFrameOn I E ∞ s u) (hu : IsOpen u)
    (ho : ∀ y ∈ u, Orthonormal ℝ (fun i ↦ s i y))
    (hor : ∀ y ∈ u, riemannianVolumeForm o y ![s 0 y, s 1 y] = 1)
    (hcov : IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov) {x : M} (hx : x ∈ u) :
    mextDeriv (hs.connectionForm cov 0 1) x =
      -(cov.scalarCurvature x / 2) • riemannianVolumeForm o x := by
  let b := hs.toBasisAt hx
  have hb : (b : Fin 2 → TangentSpace I x) = ![s 0 x, s 1 x] := by
    funext i
    fin_cases i <;> simp [b]
  -- Both sides are top-degree forms, so they agree once they agree on the basis `(e₀, e₁)`.
  ext v
  have hvol := (riemannianVolumeForm o x).apply_eq_det_mul b v
  rw [hb, hor x hx, mul_one] at hvol
  rw [(mextDeriv (hs.connectionForm cov 0 1) x).apply_eq_det_mul b v, hb,
    hs.mextDeriv_connectionForm_eq_neg_sectionalCurvature hu ho hcov hx,
    sectionalCurvature_eq_scalarCurvature_div_two o hs hcov hx, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, hvol, mul_comm]

variable [SigmaCompactSpace M] [BoundarylessManifold I M] [MeasurableSpace M] [BorelSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- **Total curvature against a cutoff.** Let `(e₀, e₁)` be a smooth orthonormal local frame of an
oriented boundaryless surface, positively oriented on its open domain `U`, and `ω = A¹₀`,
`ω(X) = ⟪e₁, ∇_X e₀⟫`, its connection one-form for a metric connection `∇`. Then every compactly
supported `C¹` function `φ` with `tsupport φ ⊆ U` satisfies `∫ dφ ∧ ω = ∫ φ K dV`, where
`K = Scal / 2` is the Gaussian curvature of `∇`. Positive orientation is stated as
`vol(e₀, e₁) = 1`, as in `IsLocalFrameOn.mextDeriv_connectionForm_eq_neg_smul_riemannianVolumeForm`.
-/
theorem integralTopForm_mextDeriv_ofFunction_wedge_connectionForm
    (o : Manifold.Orientation I M (Fin 2)) (hs : IsLocalFrameOn I E ∞ s u) (hu : IsOpen u)
    (ho : ∀ y ∈ u, Orthonormal ℝ (fun i ↦ s i y))
    (hor : ∀ y ∈ u, riemannianVolumeForm o y ![s 0 y, s 1 y] = 1)
    (hcov : IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov) {φ : M → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ) 1 φ) (hφc : HasCompactSupport φ) (hφu : tsupport φ ⊆ u) :
    integralTopForm o
        ((mextDeriv (RoughForm.ofFunction I φ)).wedge (hs.connectionForm cov 0 1)) =
      ∫ x, φ x * (cov.scalarCurvature x / 2) ∂riemannianVolume I M := by
  let bE : Module.Basis (Fin 2) ℝ E :=
    Module.finBasisOfFinrankEq ℝ E (by simpa using o.card_eq.symm)
  have hKc := continuous_mul_scalarCurvature_div_two o hs hu hcov hφ.continuous hφu
  have hKs : HasCompactSupport fun x ↦ φ x * (cov.scalarCurvature x / 2) := hφc.mul_right
  have hi := (isSmoothForm_smul_riemannianVolumeForm o hKc).integrableTopForm
    (hKs.isCompact.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left _
      (show M → E [⋀^Fin 2]→L[ℝ] ℝ from riemannianVolumeForm o))) bE
  -- Only this identification of `φ dω` uses the surface structure equation.
  have heq : (fun x ↦ φ x • mextDeriv (hs.connectionForm cov 0 1) x) =
      -(fun x ↦ (φ x * (cov.scalarCurvature x / 2)) • riemannianVolumeForm o x) := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [hs.mextDeriv_connectionForm_eq_neg_smul_riemannianVolumeForm o hu ho hor hcov
        (hφu hx), smul_smul]
      simp
    · simp [image_eq_zero_of_notMem_tsupport hx]
  calc
    _ = -integralTopForm o (fun x ↦ φ x • mextDeriv (hs.connectionForm cov 0 1) x) :=
      TauCeti.integralTopForm_mextDeriv_ofFunction_wedge_eq_neg o
        (fun _ hx ↦ contMDiffAt_connectionForm_zero_one (cov := cov) hs hu (hφu hx))
        hφ hφc (by rw [heq]; exact hi.neg)
    _ = _ := by
      rw [heq, ← neg_one_smul ℝ (fun x ↦
        (φ x * (cov.scalarCurvature x / 2)) • riemannianVolumeForm o x),
        integralTopForm_smul, neg_one_mul, neg_neg,
        integralTopForm_smul_riemannianVolumeForm o hKc hKs]

end IsLocalFrameOn
