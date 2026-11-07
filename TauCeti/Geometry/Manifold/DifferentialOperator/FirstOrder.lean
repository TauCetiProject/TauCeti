/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorField.Derivation
public import TauCeti.RingTheory.Derivation.FirstOrder
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# First-order scalar operators on smooth functions

On a finite-dimensional Hausdorff boundaryless real manifold, a real-linear endomorphism of
smooth functions has vanishing double commutators with multiplication if and only if it has
the form `f ↦ df(X) + cf` for a unique smooth vector field `X` and smooth function `c`.
The coefficient `c` is necessarily the value of the operator on the constant function one.
No continuity of the endomorphism is assumed.

This file combines the algebraic splitting `firstOrderOperatorsEquivDerivationProd` with
`derivationEquivSmoothVectorField`. The resulting geometric splitting also shows that these
operators depend only on the value and differential of their input at each point, and in
particular are local.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §3 (derivations and vector fields) and §19 (linear differential operators).
-/

public section

noncomputable section

open Filter Manifold
open scoped ContDiff Manifold Topology

attribute [local instance] LieRing.ofAssociativeRing

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

/-- A first-order scalar operator splits into a smooth vector field and multiplication by a
smooth function. The second coordinate is its value on one. -/
def firstOrderOperatorsEquivSmoothVectorFieldProd :
    firstOrderOperators ℝ C^∞⟮I, M; ℝ⟯ ≃ₗ[ℝ]
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ × C^∞⟮I, M; ℝ⟯ :=
  ((firstOrderOperatorsEquivDerivationProd ℝ C^∞⟮I, M; ℝ⟯).restrictScalars ℝ).trans
    ((derivationEquivSmoothVectorField.restrictScalars ℝ).prodCongr (LinearEquiv.refl ℝ _))

/-- The multiplication coefficient of a first-order scalar operator is its value on one. -/
@[simp]
theorem firstOrderOperatorsEquivSmoothVectorFieldProd_snd
    (D : firstOrderOperators ℝ C^∞⟮I, M; ℝ⟯) :
    (firstOrderOperatorsEquivSmoothVectorFieldProd D).2 = D.val 1 := by
  simp [firstOrderOperatorsEquivSmoothVectorFieldProd]

/-- Reconstructing an operator from a field and a function adds directional differentiation
and multiplication. -/
@[simp]
theorem firstOrderOperatorsEquivSmoothVectorFieldProd_symm_apply
    (p : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ × C^∞⟮I, M; ℝ⟯) :
    ((firstOrderOperatorsEquivSmoothVectorFieldProd.symm p).val) =
      (vectorFieldDerivation p.1).toLinearMap + LinearMap.mulLeft ℝ p.2 := by
  simp [firstOrderOperatorsEquivSmoothVectorFieldProd]

/-- The geometric splitting acts by `D f = df(X) + cf`. -/
theorem firstOrderOperatorsEquivSmoothVectorFieldProd_apply
    (D : firstOrderOperators ℝ C^∞⟮I, M; ℝ⟯) (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    D.val f x =
      mvfderiv I f x ((firstOrderOperatorsEquivSmoothVectorFieldProd D).1 x) +
        f x * D.val 1 x := by
  have h := congrArg (fun T : Module.End ℝ C^∞⟮I, M; ℝ⟯ ↦ T f x)
    (firstOrderOperatorsEquivSmoothVectorFieldProd_symm_apply
      (firstOrderOperatorsEquivSmoothVectorFieldProd D))
  simpa [mul_comm] using h

/-- Vanishing double commutators characterize the unique expression of a scalar operator as
a smooth vector field plus multiplication. -/
theorem _root_.LinearMap.mem_firstOrderOperators_iff_existsUnique_vectorField_mul
    (D : Module.End ℝ C^∞⟮I, M; ℝ⟯) :
    D ∈ firstOrderOperators ℝ C^∞⟮I, M; ℝ⟯ ↔
      ∃! p : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ × C^∞⟮I, M; ℝ⟯,
        ∀ (f : C^∞⟮I, M; ℝ⟯) (x : M),
          D f x = mvfderiv I f x (p.1 x) + f x * p.2 x := by
  have hrep (p : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ × C^∞⟮I, M; ℝ⟯) :
      (∀ (f : C^∞⟮I, M; ℝ⟯) (x : M),
        D f x = mvfderiv I f x (p.1 x) + f x * p.2 x) ↔
      D = (firstOrderOperatorsEquivSmoothVectorFieldProd.symm p).val := by
    rw [firstOrderOperatorsEquivSmoothVectorFieldProd_symm_apply]
    constructor
    · intro h
      ext f x
      simpa [mul_comm] using h f x
    · intro h f x
      simp [h, mul_comm]
  constructor
  · intro hD
    let d : firstOrderOperators ℝ C^∞⟮I, M; ℝ⟯ := ⟨D, hD⟩
    refine ⟨firstOrderOperatorsEquivSmoothVectorFieldProd d, ?_, ?_⟩
    · exact (hrep _).mpr (by simp [d])
    · intro p hp
      apply firstOrderOperatorsEquivSmoothVectorFieldProd.symm.injective
      apply Subtype.ext
      simpa [d] using ((hrep p).mp hp).symm
  · rintro ⟨p, hp, -⟩
    rw [(hrep p).mp hp]
    exact (firstOrderOperatorsEquivSmoothVectorFieldProd.symm p).property

namespace firstOrderOperators

/-- A first-order scalar operator depends only on the value and differential of its input. -/
theorem apply_eq_of_value_differential_eq
    (D : firstOrderOperators ℝ C^∞⟮I, M; ℝ⟯) {f g : C^∞⟮I, M; ℝ⟯} {x : M}
    (hvalue : f x = g x) (hdifferential : mvfderiv I f x = mvfderiv I g x) :
    D.val f x = D.val g x := by
  rw [firstOrderOperatorsEquivSmoothVectorFieldProd_apply D f,
    firstOrderOperatorsEquivSmoothVectorFieldProd_apply D g, hvalue, hdifferential]

/-- First-order scalar operators are local: inputs with the same germ have the same output
at the point. -/
theorem apply_eq_of_eventuallyEq
    (D : firstOrderOperators ℝ C^∞⟮I, M; ℝ⟯) {f g : C^∞⟮I, M; ℝ⟯} {x : M}
    (h : (f : M → ℝ) =ᶠ[𝓝 x] g) : D.val f x = D.val g x :=
  apply_eq_of_value_differential_eq D h.eq_of_nhds h.mvfderiv_eq

/-- A first-order scalar operator is multiplication precisely when its vector-field part
vanishes. -/
theorem fst_eq_zero_iff
    (D : firstOrderOperators ℝ C^∞⟮I, M; ℝ⟯) :
    (firstOrderOperatorsEquivSmoothVectorFieldProd D).1 = 0 ↔
      D.val = LinearMap.mulLeft ℝ (D.val 1) := by
  constructor
  · intro h
    have heq : D = firstOrderOperatorsEquivSmoothVectorFieldProd.symm (0, D.val 1) := by
      apply firstOrderOperatorsEquivSmoothVectorFieldProd.injective
      simpa using Prod.ext h (firstOrderOperatorsEquivSmoothVectorFieldProd_snd D)
    simpa using congrArg Subtype.val heq
  · intro h
    have heq : D = firstOrderOperatorsEquivSmoothVectorFieldProd.symm (0, D.val 1) := by
      apply Subtype.ext
      simpa using h
    rw [heq, LinearEquiv.apply_symm_apply]

end firstOrderOperators

end TauCeti
