/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SecondCovariantDerivative
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.SecondCovariantDerivative
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Curvature identities for pure-trace Hessians

For a smooth real function satisfying `Hess f = a g`, differentiate
`∇ grad f = a Id` and apply the Ricci identity. Tracing gives
`Ric(v, grad f) = (1 - n) da(v)` in dimension `n`.
-/

public noncomputable section

open Bundle CovariantDerivative
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

local notation "∇" => leviCivitaConnection I M

/-- If `Hess f = a g`, the second covariant derivative of the gradient is `da ⊗ Id`. -/
theorem secondCovariantDerivative_mgradient_of_hessian_eq_mul_inner {f a : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x : M} (ha : MDiffAt a x)
    (h : ∀ x (u v : TangentSpace I x), hessian I f x u v = a x * inner ℝ u v)
    (u v : TangentSpace I x) :
    ∇.secondCovariantDerivative ∇ (mgradient I f) x u v = mvfderiv I a x u • v := by
  obtain ⟨V, hV, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ v
  have : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have hG : CMDiff ∞ (T% (mgradient I f)) :=
    contMDiff_mgradient (n := ∞) (by simpa using hf)
  have heq : (fun y ↦ ∇ (mgradient I f) y (V y)) = a • V := by
    funext y
    exact leviCivitaConnection_mgradient_of_hessian_eq_mul_inner (h y) (V y)
  rw [∇.secondCovariantDerivative_apply ∇ hG x hV, heq,
    ∇.isCovariantDerivativeOnUniv.leibniz (hV.mdifferentiableAt (by simp))
      ha,
    leviCivitaConnection_mgradient_of_hessian_eq_mul_inner (h x)]
  simp

/-- The Ricci identity for a pure-trace Hessian: `R(u,v) grad f = da(u) v - da(v) u`. -/
theorem curvatureTensor_mgradient_of_hessian_eq_mul_inner {f a : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x : M} (ha : MDiffAt a x)
    (h : ∀ x (u v : TangentSpace I x), hessian I f x u v = a x * inner ℝ u v)
    (u v : TangentSpace I x) :
    ∇.curvatureTensor x u v (mgradient I f x) =
      mvfderiv I a x u • v - mvfderiv I a x v • u := by
  have ht : ∇.IsTorsionFree := (isTorsionFree_iff_torsion_eq_zero ∇).2
    (torsion_leviCivitaConnection_eq_zero I)
  have : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have hG : CMDiff ∞ (T% (mgradient I f)) :=
    contMDiff_mgradient (n := ∞) (by simpa using hf)
  rw [← ∇.secondCovariantDerivative_sub_swap_of_isTorsionFree ∇ ht hG x u v,
    secondCovariantDerivative_mgradient_of_hessian_eq_mul_inner hf ha h,
    secondCovariantDerivative_mgradient_of_hessian_eq_mul_inner hf ha h]

/-- Tracing the pure-trace Hessian identity gives `Ric(v, grad f) = (1 - n) da(v)`. -/
theorem ricciTensor_mgradient_of_hessian_eq_mul_inner {f a : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x : M} (ha : MDiffAt a x)
    (h : ∀ x (u v : TangentSpace I x), hessian I f x u v = a x * inner ℝ u v)
    (v : TangentSpace I x) :
    ∇.ricciTensor x v (mgradient I f x) =
      (1 - Module.finrank ℝ E : ℝ) * mvfderiv I a x v := by
  have heq : ((∇.curvatureTensor x).flip v).flip (mgradient I f x) =
      (mvfderiv I a x).toLinearMap.smulRight v -
        mvfderiv I a x v • LinearMap.id := by
    ext u
    exact curvatureTensor_mgradient_of_hessian_eq_mul_inner hf ha h u v
  rw [∇.ricciTensor_apply, heq, map_sub, LinearMap.trace_smulRight, map_smul,
    LinearMap.trace_id, TauCeti.finrank_tangentSpace]
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul]
  ring

end TauCeti.Manifold
