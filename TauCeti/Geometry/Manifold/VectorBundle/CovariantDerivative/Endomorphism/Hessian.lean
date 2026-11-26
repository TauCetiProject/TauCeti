/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Otis Chodosh
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Endomorphism
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trivial
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SecondCovariantDerivative.Composition
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# Hessians of traces of endomorphisms

Covariant differentiation of a smooth endomorphism section commutes with its ordinary trace.
Combining this contraction rule with the second covariant product rule gives a pointwise
formula for the Hessian of `tr(A²)`. These identities require no metric on the vector bundle
and no metric compatibility of its connection. Trace commutes with the second covariant
derivative for any tangent connection. The scalar Hessian identities specialize this to the
Levi-Civita connection of the base metric.

These identities build on an original local formalization by Otis Chodosh.
-/

public noncomputable section

open Bundle FiberBundle Filter Manifold
open scoped ContDiff Topology

namespace CovariantDerivative

open TauCeti.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  {A B : Π x : M, V x →L[ℝ] V x}

variable (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]

/-- Fibrewise trace intertwines the second covariant derivative on endomorphisms with the
second covariant derivative on the trivial line, for any tangent connection. -/
theorem secondCovariantDerivative_trace_endomorphism
    (covT : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun z ↦ V z →L[ℝ] V z) y (A y)))
    (x : M) (u v : TangentSpace I x) :
    (trivial (I := I) ℝ).secondCovariantDerivative covT
        (fun y ↦ LinearMap.trace ℝ (V y) (A y).toLinearMap) x u v =
      LinearMap.trace ℝ (V x)
        (((cov.hom cov).secondCovariantDerivative covT A x u v).toLinearMap) := by
  obtain ⟨Y, hY, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ v
  have hD := (cov.hom cov).contMDiff_apply hY hA
  have heq : (fun y ↦ mvfderiv I
      (fun z ↦ LinearMap.trace ℝ (V z) (A z).toLinearMap) y (Y y)) =
      fun y ↦ LinearMap.trace ℝ (V y) (cov.hom cov A y (Y y)).toLinearMap :=
    funext fun y ↦ cov.mvfderiv_trace_eq_trace_hom (hA.mdifferentiable (by simp) y) (Y y)
  rw [secondCovariantDerivative_apply _ covT
      (Trivial.contMDiff_mk_iff.mpr ⟨contMDiff_id, hA.trace_clm_bundle⟩) x hY,
    secondCovariantDerivative_apply (cov.hom cov) covT hA x hY]
  simp only [trivial_apply, heq,
    cov.mvfderiv_trace_eq_trace_hom (hD.mdifferentiable (by simp) x),
    cov.mvfderiv_trace_eq_trace_hom (hA.mdifferentiable (by simp) x),
    ContinuousLinearMap.toLinearMap_sub, map_sub]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The scalar Hessian of the trace is the trace of the second covariant derivative. -/
theorem hessian_trace_endomorphism
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun z ↦ V z →L[ℝ] V z) y (A y)))
    (x : M) (u v : TangentSpace I x) :
    hessian I (fun y ↦ LinearMap.trace ℝ (V y) (A y).toLinearMap) x u v =
      LinearMap.trace ℝ (V x)
        (((cov.hom cov).secondCovariantDerivative (leviCivitaConnection I M)
          A x u v).toLinearMap) := by
  obtain ⟨Y, hY, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ v
  rw [← cov.secondCovariantDerivative_trace_endomorphism (leviCivitaConnection I M) hA,
    secondCovariantDerivative_apply _ _
      (Trivial.contMDiff_mk_iff.mpr ⟨contMDiff_id, hA.trace_clm_bundle⟩) x hY]
  have hh := hessian_apply_eq_mvfderiv_sub x ((hA.trace_clm_bundle x).of_le (by simp))
    (FiberBundle.extend E u) Y (hY.mdifferentiable (by simp) x)
  simpa only [FiberBundle.extend_apply_self, trivial_apply] using hh

/-- The Hessian of a trace square is twice the derivative pairing plus twice the pairing of
`A` with its second covariant derivative. This is an ordinary trace identity, with no inner
product on endomorphisms. -/
theorem hessian_trace_comp_self
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun z ↦ V z →L[ℝ] V z) y (A y)))
    (x : M) (u v : TangentSpace I x) :
    hessian I (fun y ↦ LinearMap.trace ℝ (V y) ((A y).comp (A y)).toLinearMap) x u v =
      2 * LinearMap.trace ℝ (V x)
        ((cov.hom cov A x u).comp (cov.hom cov A x v)).toLinearMap +
      2 * LinearMap.trace ℝ (V x) ((A x).comp
        ((cov.hom cov).secondCovariantDerivative (leviCivitaConnection I M)
          A x u v)).toLinearMap := by
  have : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  rw [cov.hessian_trace_endomorphism (hA.clm_bundle_comp hA),
    secondCovariantDerivative_comp cov cov cov (leviCivitaConnection I M) hA hA]
  simp only [ContinuousLinearMap.toLinearMap_add, map_add, ContinuousLinearMap.toLinearMap_comp]
  rw [LinearMap.trace_comp_comm'
      (((cov.hom cov).secondCovariantDerivative (leviCivitaConnection I M) A x u v).toLinearMap)
      (A x).toLinearMap,
    LinearMap.trace_comp_comm' (cov.hom cov A x v).toLinearMap (cov.hom cov A x u).toLinearMap]
  ring

end CovariantDerivative
