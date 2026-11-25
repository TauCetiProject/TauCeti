/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cayley.Smooth
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ComplexTangentBundle
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Topology.VectorBundle.Complex.Intertwiner

/-!
# The clutching number of a tame almost complex structure

An almost complex structure `J` on a manifold `M` makes the tangent bundle a complex vector bundle
`(TM, J)` (`TauCeti.ContMDiffAlmostComplexStructure.toContinuousComplexStructure`), and its
clutching number on a sphere `p : Ω^ (Fin 2) M x` is the first Chern number `c₁(TM, J)` of the
sphere (`TauCeti.clutchingNumberHom`). This file shows that it is an invariant of the symplectic
form alone: two almost complex structures tamed by a common symplectic form, even one varying
discontinuously from point to point, give the same clutching number homomorphism
`π₂(M, x) → ℤ` (`TauCeti.ContMDiffAlmostComplexStructure.clutchingNumberHom_eq_of_tames`). This
generalizes `TauCeti.SmoothTwoForm.Tames.clutchingNumberHom_eq`, where the taming form is a smooth
two-form and the structures are smooth.

The proof does not deform one structure into the other. If `ω` tames `J` and `K` at a point, then
`1 - K J` is injective, since `ω(v, K (v - K J v)) = ω(v, K v) + ω(v, J v)` is positive for
`v ≠ 0`; so the complex-linear part `(1 - K J) / 2` of the identity is a complex-linear
isomorphism `(TM, J) ≃ (TM, K)`, continuous in the point
(`TauCeti.Bundle.ContinuousComplexStructure.clutchingNumberHom_eq_of_isUnit_intertwiner`).

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford (2017),
  Section 2.6 (the first Chern class of a symplectic vector bundle does not depend on the choice of
  tame complex structure).
-/

public section

noncomputable section

open Module
open scoped ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  (G G' : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [NormedAddCommGroup G'] [NormedSpace ℂ G'] [FiniteDimensional ℂ G']
  [Fact (finrank ℝ E = 2 * finrank ℂ G)] [Fact (finrank ℝ E = 2 * finrank ℂ G')]

/-- **The clutching number does not depend on the tame almost complex structure.** If at every
point of `M` one symplectic form on the tangent space tames both `J` and `K`, then the complex
vector bundles `(TM, J)` and `(TM, K)` have the same clutching number homomorphism
`π₂(M, x) → ℤ`, for any choice of model fibres `G` and `G'`. The forms need not vary continuously.
-/
theorem ContMDiffAlmostComplexStructure.clutchingNumberHom_eq_of_tames {n m : ℕ∞}
    {J : ContMDiffAlmostComplexStructure I n M} {K : ContMDiffAlmostComplexStructure I m M}
    (σ : ∀ y, SymplecticForm (TangentSpace I y))
    (hJ : ∀ y, (σ y).Tames (J.almostComplexStructureAt y))
    (hK : ∀ y, (σ y).Tames (K.almostComplexStructureAt y)) (x : M) :
    clutchingNumberHom G' K.toContinuousComplexStructure.Fiber x =
      clutchingNumberHom G J.toContinuousComplexStructure.Fiber x := by
  refine J.toContinuousComplexStructure.clutchingNumberHom_eq_of_isUnit_intertwiner
    K.toContinuousComplexStructure G G' (fun y ↦ ?_) x
  rw [Bundle.ContinuousComplexStructure.isUnit_intertwiner_iff]
  -- The tangent space `TangentSpace I y` is the model space `E`, where the operator-norm form of
  -- the invertibility of `1 - K J` is stated.
  exact SymplecticForm.Tames.isUnit_one_sub_mul_of_toLinearMap (V := E) (hK y) (hJ y)
    (LinearMap.ext fun v ↦ (K.toContinuousComplexStructure_apply y v).trans
      (K.almostComplexStructureAt_apply y v).symm)
    (LinearMap.ext fun v ↦ (J.toContinuousComplexStructure_apply y v).trans
      (J.almostComplexStructureAt_apply y v).symm)

end TauCeti
