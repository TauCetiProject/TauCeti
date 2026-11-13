/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import TauCeti.Geometry.Symplectic.JHolomorphic.Varying
public import TauCeti.Geometry.Symplectic.Prod.Skew

/-!
# Holomorphic graphs in skew products

Let `J₁` be a family of almost complex structures on `V`, and let `J₂(p)` and `A(p) : V →ₗ[ℝ] W`
depend on a point `p` of `V × W`. Put on `V × W` the pointwise skew product
`J(p) = J₁(p.1).skewProd (J₂ p) (A p)` of `TauCeti.Geometry.Symplectic.Prod.Skew`. This is Gromov's
graph construction: the graph `z ↦ (z, u z)` of a map `u : V → W` is `J`-holomorphic at `z`
exactly when `u` is differentiable there and `du(z) - A(z, u z)` is complex linear from `J₁(z)` to
`J₂(z, u z)` (`TauCeti.AlmostComplexStructure.isJHolomorphicAt_graph_skewProd_iff`). Choosing
`A` turns an inhomogeneous Cauchy–Riemann equation for `u` into the holomorphicity of its graph.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1.
-/

public section

namespace TauCeti.AlmostComplexStructure

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {J₁ : V → AlmostComplexStructure V} {J₂ : V × W → AlmostComplexStructure W}
  {A : V × W → V →ₗ[ℝ] W} {u : V → W}

/-- **Gromov's graph construction.** The graph of `u` is holomorphic at `z` into the pointwise
skew product of `J₁` and `J₂` along `A` exactly when `u` is differentiable at `z` and
`du(z) - A(z, u z)` is complex linear from `J₁(z)` to `J₂(z, u z)`. -/
theorem isJHolomorphicAt_graph_skewProd_iff {z : V} :
    IsJHolomorphicAt J₁ (fun p ↦ (J₁ p.1).skewProd (J₂ p) (A p)) (fun w ↦ (w, u w)) z ↔
      DifferentiableAt ℝ u z ∧
        IsComplexLinearMap (J₁ z) (J₂ (z, u z)) ((fderiv ℝ u z : V →ₗ[ℝ] W) - A (z, u z)) := by
  have hgraph (hu : DifferentiableAt ℝ u z) :
      HasFDerivAt (fun w ↦ (w, u w)) ((ContinuousLinearMap.id ℝ V).prod (fderiv ℝ u z)) z :=
    (hasFDerivAt_id z).prodMk hu.hasFDerivAt
  have hlin : IsComplexLinearMap (J₁ z) ((J₁ z).skewProd (J₂ (z, u z)) (A (z, u z)))
        ((ContinuousLinearMap.id ℝ V).prod (fderiv ℝ u z) : V →ₗ[ℝ] V × W) ↔
      IsComplexLinearMap (J₁ z) (J₂ (z, u z)) ((fderiv ℝ u z : V →ₗ[ℝ] W) - A (z, u z)) := by
    rw [ContinuousLinearMap.coe_prod, ContinuousLinearMap.coe_id,
      isComplexLinearMap_id_prod_skewProd_iff]
  rw [isJHolomorphicAt_iff]
  constructor
  · rintro ⟨f', hf', hf'lin⟩
    have hu : DifferentiableAt ℝ u z := hf'.differentiableAt.snd
    rw [hf'.unique (hgraph hu)] at hf'lin
    exact ⟨hu, hlin.mp hf'lin⟩
  · rintro ⟨hu, hulin⟩
    exact ⟨_, hgraph hu, hlin.mpr hulin⟩

/-- **Gromov's graph construction, globally.** The graph of `u` is holomorphic into the pointwise
skew product of `J₁` and `J₂` along `A` exactly when `u` is differentiable and
`du(z) - A(z, u z)` is complex linear from `J₁(z)` to `J₂(z, u z)` at every `z`. -/
theorem isJHolomorphic_graph_skewProd_iff :
    IsJHolomorphic J₁ (fun p ↦ (J₁ p.1).skewProd (J₂ p) (A p)) (fun w ↦ (w, u w)) ↔
      Differentiable ℝ u ∧
        ∀ z, IsComplexLinearMap (J₁ z) (J₂ (z, u z)) ((fderiv ℝ u z : V →ₗ[ℝ] W) - A (z, u z)) := by
  simp only [isJHolomorphic_iff, isJHolomorphicAt_graph_skewProd_iff]
  exact forall_and

end TauCeti.AlmostComplexStructure
