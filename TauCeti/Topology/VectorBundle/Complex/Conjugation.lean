/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Complex.RealStructure

/-!
# Clutching numbers of complex vector bundles with a conjugation

A complex vector bundle `E` over `X` with finite-dimensional model fibre `F` and a
**conjugation**, a family of conjugate-linear automorphisms `c x : E x ≃ E x` continuous on the
total space, has vanishing clutching numbers on `π₂(X, x)`
(`TauCeti.clutchingNumberHom_eq_zero_of_conjugateLinear`, in
`TauCeti.Topology.VectorBundle.Complex.RealStructure`): its first Chern number vanishes on every
sphere. This file applies that vanishing to complex structures on real vector bundles.

The motivating instance is a real vector bundle `V` with a continuous complex structure `J` and a
continuous automorphism `c` anticommuting with `J`, `c ∘ J = -J ∘ c`: then `c` is a conjugation of
the complex vector bundle `J.Fiber`, whose clutching numbers therefore vanish
(`TauCeti.Bundle.ContinuousComplexStructure.clutchingNumberHom_eq_zero_of_anticommute`). For the
tangent bundle of a symplectic manifold with a tame almost complex structure `J` and a Lagrangian
distribution `L`, such as the vertical distribution of a cotangent bundle, the reflection of
`TM = L ⊕ J L` in `L` is such an automorphism. This is how the first Chern number of a cotangent
bundle vanishes on spheres: along the zero section its tangent bundle is the complexification of the
tangent bundle of the base.

## Main results

* `TauCeti.Bundle.ContinuousComplexStructure.clutchingNumberHom_eq_zero_of_anticommute`: a complex
  structure on a real vector bundle with an anticommuting continuous automorphism has vanishing
  clutching numbers.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the Chern classes of the conjugate bundle) and §15 (the complexification
  of a real vector bundle is isomorphic to its conjugate).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.2 (the canonical grading of the Floer
  homology of a cotangent bundle).
-/

public section

noncomputable section

open Bundle Module

namespace TauCeti

/-! ### Complex structures with an anticommuting automorphism -/

section ComplexStructure

variable {X : Type*} [TopologicalSpace X]
  {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [FiniteDimensional ℝ F₀]
  {V : X → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F₀ V)] [FiberBundle F₀ V] [VectorBundle ℝ F₀ V]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [Fact (finrank ℝ F₀ = 2 * finrank ℂ F)]

namespace Bundle.ContinuousComplexStructure

variable (J : Bundle.ContinuousComplexStructure F₀ V)

/-- An automorphism `c` of `V b` anticommuting with `J b` is conjugate-linear on `J.Fiber b`. -/
private def conjOfAnticommute (c : ∀ x, V x ≃L[ℝ] V x)
    (hc : ∀ x v, c x (J x v) = -J x (c x v)) (b : X) : J.Fiber b ≃SL[starRingEnd ℂ] J.Fiber b where
  toFun v := (J.fiberEquiv b).symm (c b (J.fiberEquiv b v))
  invFun v := (J.fiberEquiv b).symm ((c b).symm (J.fiberEquiv b v))
  map_add' v w := by simp only [map_add]
  map_smul' z v := by
    -- `z • v = re z • v + im z • J v`, and `c` commutes with `re z` and anticommutes with `J`.
    apply (J.fiberEquiv b).injective
    simp [fiberEquiv_smul, hc]
  left_inv v := by simp
  right_inv v := by simp
  continuous_toFun := (J.fiberEquiv b).symm.continuous.comp
    ((c b).continuous.comp (J.fiberEquiv b).continuous)
  continuous_invFun := (J.fiberEquiv b).symm.continuous.comp
    ((c b).symm.continuous.comp (J.fiberEquiv b).continuous)

/-- **A complex structure with an anticommuting automorphism has vanishing clutching numbers.**
If a continuous family of automorphisms `c x` of the real vector bundle `V`, continuous on the
total space, anticommutes with the complex structure `J`, `c ∘ J = -J ∘ c`, then the complex vector
bundle `J.Fiber` has vanishing clutching numbers: `c` is a conjugation of it. -/
theorem clutchingNumberHom_eq_zero_of_anticommute (c : ∀ x, V x ≃L[ℝ] V x)
    (hc : ∀ x v, c x (J x v) = -J x (c x v))
    (hcont : Continuous fun v : TotalSpace F₀ V ↦ TotalSpace.mk' F₀ v.proj (c v.proj v.snd))
    (x : X) : clutchingNumberHom F J.Fiber x = 0 := by
  refine clutchingNumberHom_eq_zero_of_conjugateLinear (F := F) (E := J.Fiber)
    (J.conjOfAnticommute c hc)
    ((((J.totalSpaceHomeomorph F).symm.continuous.comp hcont).comp
      (J.totalSpaceHomeomorph F).continuous).congr fun v ↦ ?_) x
  simp [conjOfAnticommute]

end Bundle.ContinuousComplexStructure

end ComplexStructure

end TauCeti
