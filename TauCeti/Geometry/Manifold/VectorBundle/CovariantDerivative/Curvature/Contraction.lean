/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearTensor
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchi
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Derivative
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The first contracted second Bianchi identity

Covariant differentiation commutes with the trace defining Ricci curvature. This file expresses
that fact on tangent vectors, and contracts the second Bianchi identity to obtain

`∑ᵢ ⟨eᵢ, (∇_{eᵢ} R)(u, v) w⟩ = (∇_u Ric)(v, w) - (∇_v Ric)(u, w)`.

For a metric-compatible torsion-free connection, lowering the output index gives the usual
Riemannian divergence formula

`∑ᵢ (∇_{eᵢ} Rm)(eᵢ, u, v, w) = (∇_w Ric)(u, v) - (∇_v Ric)(u, w)`.

The trace identity holds for every smooth affine connection. The first, output-contracted
identity needs only vanishing torsion: its orthonormal basis merely computes an ordinary trace.
The Riemannian divergence formula additionally uses metric compatibility. These are the
differential curvature identities underlying the divergence of the Weyl tensor and the Cotton
tensor.

The construction uses the existing covariant derivative of bilinear tensors and transfers
`CovariantDerivative.exists_frame_sum_derivCurvature` from its local frame to the invariant
tensor `CovariantDerivative.derivCurvatureTensor`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7 (the second Bianchi identity and its contractions).
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

/-- The covariant derivative of Ricci curvature, with the direction of differentiation last:
`derivRicciTensor x u v w = (∇_w Ric)(u, v)`. -/
def derivRicciTensor (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  cov.derivBilinearTensor (fun y ↦ (cov.ricciTensor y).toContinuousBilinearMap) x

/-- The covariant derivative of Ricci curvature uses the native bilinear-tensor derivative. -/
theorem derivRicciTensor_def (x : M) :
    cov.derivRicciTensor x =
      cov.derivBilinearTensor (fun y ↦ (cov.ricciTensor y).toContinuousBilinearMap) x :=
  (rfl)

/-- On vector fields differentiable at `x`, the derivative of Ricci curvature is the
directional derivative of its evaluation minus the two connection corrections. -/
theorem derivRicciTensor_apply {σ τ : Π y : M, TangentSpace I y} {x : M}
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) (v : TangentSpace I x) :
    cov.derivRicciTensor x (σ x) (τ x) v =
      mvfderiv I (fun y ↦ cov.ricciTensor y (σ y) (τ y)) x v -
        cov.ricciTensor x (cov σ x v) (τ x) - cov.ricciTensor x (σ x) (cov τ x v) := by
  rw [derivRicciTensor_def]
  exact cov.derivBilinearTensor_apply
    (fun _ _ h₁ h₂ ↦ cov.mdifferentiableAt_ricciTensor_apply h₁ h₂) hσ hτ v

/-- Covariant differentiation commutes with the trace defining Ricci curvature:
`(∇_v Ric)(u, w) = tr (z ↦ (∇_v R)(z, u) w)`. No metric is needed. -/
theorem derivRicciTensor_eq_trace (x : M) (u w v : TangentSpace I x) :
    cov.derivRicciTensor x u w v =
      LinearMap.trace ℝ (TangentSpace I x)
        (((cov.derivCurvatureTensor cov x v).flip u).flip w) := by
  classical
  obtain ⟨F, c, hF, -, hsum, htr⟩ := exists_frame_sum_derivCurvature (cov := cov) x
  obtain ⟨B, hB, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E u
  obtain ⟨C, hC, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E w
  let D := ((cov.derivCurvatureTensor cov x v).flip (B x)).flip (C x)
  -- The local frame resolves the identity; apply `D` to this resolution and take its trace.
  have hD : D = ∑ i, (c i).smulRight (D (F i x)) := by
    ext z
    conv_lhs => rw [← hsum z]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hDi (i) : D (F i x) = cov.derivCurvature x v (F i) B C := by
    rw [LinearMap.flip_apply, LinearMap.flip_apply,
      derivCurvatureTensor_apply cov cov x v (hF i) hB hC, derivCurvature_apply]
  have ht := htr (X := FiberBundle.extend E v) hB hC
  simp only [FiberBundle.extend_apply_self] at ht
  rw [derivRicciTensor_apply cov (hB.mdifferentiableAt (by simp))
    (hC.mdifferentiableAt (by simp))]
  calc
    _ = ∑ i, c i (D (F i x)) := by simpa only [hDi] using ht.symm
    _ = LinearMap.trace ℝ (TangentSpace I x) D := by
      conv_rhs => rw [hD]
      simp only [map_sum, LinearMap.trace_smulRight]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- In any orthonormal basis, contracting the first curvature argument of `∇R` against the
output gives `∇Ric`. The connection need not preserve the metric. -/
theorem sum_inner_derivCurvatureTensor_eq_derivRicciTensor {ι : Type*} [Fintype ι]
    (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (u w v : TangentSpace I x) :
    ∑ i, inner ℝ (b i) (cov.derivCurvatureTensor cov x v (b i) u w) =
      cov.derivRicciTensor x u w v := by
  rw [derivRicciTensor_eq_trace, LinearMap.trace_eq_sum_inner _ b]
  rfl

/-- The first contracted second Bianchi identity in an arbitrary orthonormal basis. The
connection is torsion-free, but metric compatibility is not required. -/
theorem sum_inner_derivCurvatureTensor_eq_sub {ι : Type*} [Fintype ι]
    (ht : cov.torsion = 0) (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (u v w : TangentSpace I x) :
    ∑ i, inner ℝ (b i) (cov.derivCurvatureTensor cov x (b i) u v w) =
      cov.derivRicciTensor x v w u - cov.derivRicciTensor x u w v := by
  have h (i : ι) :
      inner ℝ (b i) (cov.derivCurvatureTensor cov x (b i) u v w) =
        inner ℝ (b i) (cov.derivCurvatureTensor cov x u (b i) v w) -
          inner ℝ (b i) (cov.derivCurvatureTensor cov x v (b i) u w) := by
    have hcyc := congrArg (fun L ↦ inner ℝ (b i) (L w))
      (cov.derivCurvatureTensor_cyclic_eq_zero cov ht x (b i) u v)
    rw [cov.derivCurvatureTensor_antisymm cov x u v (b i)] at hcyc
    simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.zero_apply,
      inner_add_right, inner_neg_right, inner_zero_right] at hcyc
    linarith
  simp_rw [h]
  rw [Finset.sum_sub_distrib, sum_inner_derivCurvatureTensor_eq_derivRicciTensor,
    sum_inner_derivCurvatureTensor_eq_derivRicciTensor]

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {cov}

/-- For a metric-compatible torsion-free connection, the covariant derivative of Ricci is
symmetric in the two Ricci arguments. -/
theorem IsMetricCompatible.derivRicciTensor_comm
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (x : M) (u v : TangentSpace I x) :
    cov.derivRicciTensor x u v = cov.derivRicciTensor x v u := by
  simp only [derivRicciTensor_def]
  exact cov.derivBilinearTensor_apply_comm
    (fun y a b ↦ IsMetricCompatible.ricciTensor_comm (cov := cov) hcov ht y a b) u v

/-- Pair interchange for the metric-lowered covariant derivative of curvature:
`(∇_d Rm)(u, v, w, z) = (∇_d Rm)(w, z, u, v)`. -/
theorem IsMetricCompatible.inner_derivCurvatureTensor_swap_pairs
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (x : M) (d u v w z : TangentSpace I x) :
    inner ℝ (cov.derivCurvatureTensor cov x d u v w) z =
      inner ℝ (cov.derivCurvatureTensor cov x d w z u) v := by
  obtain ⟨D, -, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E d
  obtain ⟨U, hU, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E u
  obtain ⟨V, hV, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E v
  obtain ⟨W, hW, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E w
  obtain ⟨Z, hZ, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E z
  rw [derivCurvatureTensor_apply cov cov x (D x) hU hV hW,
    derivCurvatureTensor_apply cov cov x (D x) hW hZ hU]
  simpa only [derivCurvature_apply] using
    hcov.inner_derivCurvature_swap_pairs ht D hU hV hW hZ x

/-- The divergence of the metric-lowered Riemann tensor is the antisymmetrized derivative of
Ricci curvature. The sign uses `Rm(u, v, w, z) = ⟨R(u, v)w, z⟩`. -/
theorem IsMetricCompatible.sum_inner_derivCurvatureTensor_eq_sub {ι : Type*} [Fintype ι]
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (u v w : TangentSpace I x) :
    ∑ i, inner ℝ (cov.derivCurvatureTensor cov x (b i) (b i) u v) w =
      cov.derivRicciTensor x u v w - cov.derivRicciTensor x u w v := by
  have h (i : ι) :
      inner ℝ (cov.derivCurvatureTensor cov x (b i) (b i) u v) w =
        -inner ℝ (b i) (cov.derivCurvatureTensor cov x (b i) v w u) := by
    rw [cov.derivCurvatureTensor_antisymm cov x (b i) (b i) u,
      LinearMap.neg_apply, inner_neg_left,
      hcov.inner_derivCurvatureTensor_swap_pairs ht, real_inner_comm]
  simp_rw [h]
  rw [Finset.sum_neg_distrib, cov.sum_inner_derivCurvatureTensor_eq_sub ht,
    hcov.derivRicciTensor_comm ht x w u, hcov.derivRicciTensor_comm ht x v u]
  ring

end CovariantDerivative
