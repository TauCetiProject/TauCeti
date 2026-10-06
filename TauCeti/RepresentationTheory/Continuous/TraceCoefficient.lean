/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.LinHom
public import Mathlib.Analysis.InnerProductSpace.LinearMap
-- Private: `InnerProductSpace.rankOne_comp` and `ContinuousLinearMap.adjoint` are used only inside
-- proofs.
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The trace coefficient of an operator against a continuous representation

A finite-dimensional continuous representation `π` of `G` on `V` pairs an operator
`T : V →L[𝕜] V` with the function

`traceCoeff π hπ T : x ↦ trace (T ∘ π x⁻¹)`,

its **trace coefficient**. The pairing is linear in `T`, lands in `C(G, 𝕜)`, and sends the rank-one
operator `rankOne 𝕜 w v` to the matrix coefficient `x ↦ ⟪π x v, w⟫` of
`TauCeti/RepresentationTheory/Continuous/MatrixCoefficient.lean` when `π` is unitary
(`ContRepresentation.traceCoeff_rankOne`). An operator is the sum of the rank-one operators built
from an orthonormal basis and its own values on that basis, so a trace coefficient is a sum of
`dim V` matrix coefficients (`ContRepresentation.traceCoeff_eq_sum`) and the two pairings span the
same functions; what the operator form adds is that the *whole* space of operators is the parameter
space, with no choice of basis and no sesquilinearity to track.

The reason to name it is the two-sided symmetry. The operators carry the `G × G`-action
`(g, h) • T = π g ∘ T ∘ π h⁻¹` of `ContRepresentation.biLinHom π π`, built in
`TauCeti/RepresentationTheory/Continuous/LinHom.lean`. Under the trace coefficient that action
becomes **bi-translation** of functions,

`traceCoeff π hπ ((g, h) • T) x = traceCoeff π hπ T (g⁻¹ * x * h)`

(`ContRepresentation.traceCoeff_biLinHom_apply`): the cyclicity of the trace moves `π g` from the
left of `T` to the right of it, where it meets `π h⁻¹ ∘ π x⁻¹`. No inner product is needed for that,
only the group law; so the trace coefficient and its bi-translation identities are stated for a
finite-dimensional normed space over a complete nontrivially normed field, and the inner product
enters only in the comparison with the matrix coefficients. Composed with `ContinuousMap.toLp`
this is the equivariance of the Peter-Weyl block of a compact group, in
`TauCeti/RepresentationTheory/Compact/TraceCoefficient/Basic.lean`.

## Main definitions

* `ContRepresentation.traceCoeff`: the trace coefficient `T ↦ (x ↦ trace (T ∘ π x⁻¹))`, as a linear
  map into `C(G, 𝕜)`.

## Main statements

* `ContRepresentation.traceCoeff_rankOne`: the trace coefficient of a rank-one operator is a matrix
  coefficient, for a unitary representation.
* `ContRepresentation.traceCoeff_eq_sum`: a trace coefficient expands over an orthonormal basis as
  a sum of matrix coefficients.
* `ContRepresentation.traceCoeff_biLinHom_apply` and
  `ContRepresentation.traceCoeff_biLinHom`: **the two-sided Hom action becomes bi-translation of
  the trace coefficient.**
* `ContRepresentation.traceCoeff_one`: the trace coefficient of the identity operator is the
  character, read at the inverse.

## References

* Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open scoped InnerProductSpace

open TauCeti TauCeti.ContRepresentation

namespace ContRepresentation

section TraceCoeff

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- **The trace coefficient** of an operator against a representation with continuous
operator-valued action: `T ↦ (x ↦ trace (T ∘ π x⁻¹))`, a linear map from the operators of `V` to
`C(G, 𝕜)`.

The inverse in the argument is what makes the pairing covariant on both sides; see
`ContRepresentation.traceCoeff_biLinHom_apply`. -/
noncomputable def traceCoeff (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    (V →L[𝕜] V) →ₗ[𝕜] C(G, 𝕜) where
  toFun T :=
    { toFun x := traceCLM 𝕜 V (T ∘L π x⁻¹)
      continuous_toFun :=
        (traceCLM 𝕜 V).continuous.comp (continuous_const.clm_comp (hπ.comp continuous_inv)) }
  map_add' T₁ T₂ := by ext x; simp [ContinuousLinearMap.add_comp]
  map_smul' c T := by ext x; simp [ContinuousLinearMap.smul_comp]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- Evaluation of a trace coefficient. -/
@[simp]
theorem traceCoeff_apply (T : V →L[𝕜] V) (x : G) :
    traceCoeff π hπ T x = traceCLM 𝕜 V (T ∘L π x⁻¹) :=
  (rfl)

/-- A trace coefficient at the identity is the trace of its operator. -/
theorem traceCoeff_apply_one (T : V →L[𝕜] V) :
    traceCoeff π hπ T 1 = LinearMap.trace 𝕜 V (T : V →ₗ[𝕜] V) := by
  simp [Module.End.one_eq_id]

/-- The trace coefficient of the identity operator is the character, read at the inverse. -/
theorem traceCoeff_one :
    traceCoeff π hπ 1 = (character π hπ).comp ⟨Inv.inv, continuous_inv⟩ := by
  ext x
  simp [character_apply, Module.End.one_eq_id]

end TraceCoeff

/-! ### Comparison with the matrix coefficients -/

section MatrixCoeff

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- **The trace coefficient of a rank-one operator is a matrix coefficient** of a unitary
representation: `rankOne 𝕜 w v` pairs to `x ↦ ⟪π x v, w⟫`. Unitarity enters through the adjoint of
`π x⁻¹`, which it identifies with `π x`. -/
theorem traceCoeff_rankOne (hunitary : IsUnitary π) (v w : V) :
    traceCoeff π hπ (InnerProductSpace.rankOne 𝕜 w v) = matrixCoeff π hπ v w := by
  have := FiniteDimensional.complete 𝕜 V
  ext x
  rw [traceCoeff_apply, matrixCoeff_apply, InnerProductSpace.rankOne_comp,
    hunitary.adjoint_eq_inv, inv_inv, traceCLM_apply, InnerProductSpace.trace_rankOne]

/-- **A trace coefficient expands over an orthonormal basis as a sum of matrix coefficients**, one
for each basis vector. So the trace coefficients of `π` span exactly the same subspace of
`C(G, 𝕜)` as its matrix coefficients.

The expansion `T = ∑ᵢ T eᵢ ⊗ eᵢ*` of the operator is Mathlib's resolution of the identity
`OrthonormalBasis.sum_rankOne_eq_id`, composed with `T` through
`InnerProductSpace.comp_rankOne`. -/
theorem traceCoeff_eq_sum {ι : Type*} [Fintype ι] (hunitary : IsUnitary π)
    (e : OrthonormalBasis ι 𝕜 V) (T : V →L[𝕜] V) :
    traceCoeff π hπ T = ∑ i, matrixCoeff π hπ (e i) (T (e i)) := by
  have hT : ∑ i, InnerProductSpace.rankOne 𝕜 (T (e i)) (e i) = T := by
    simp only [← InnerProductSpace.comp_rankOne, ← ContinuousLinearMap.comp_finsetSum,
      e.sum_rankOne_eq_id, ContinuousLinearMap.comp_id]
  conv_lhs => rw [← hT]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => traceCoeff_rankOne π hπ hunitary (e i) (T (e i))

end MatrixCoeff

/-! ### Bi-translation -/

section Bitranslation

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- **The two-sided Hom action becomes bi-translation of the trace coefficient**: pairing
`(g, h) • T = π g ∘ T ∘ π h⁻¹` with `π` gives the function `x ↦ traceCoeff π hπ T (g⁻¹ * x * h)`.

The trace is cyclic, so `π g` passes from the left of `T` to its right, where the three remaining
factors multiply to `π ((g⁻¹ * x * h)⁻¹)`. Nothing is assumed beyond the group law; in particular
no unitarity. -/
theorem traceCoeff_biLinHom_apply (p : G × G) (T : V →L[𝕜] V) (x : G) :
    traceCoeff π hπ (biLinHom π π p T) x = traceCoeff π hπ T (p.1⁻¹ * x * p.2) := by
  have h₁ : ((biLinHom π π p T) ∘L π x⁻¹ : V →ₗ[𝕜] V) =
      (π p.1 : V →ₗ[𝕜] V) * ((T ∘L π (p.2⁻¹ * x⁻¹) : V →L[𝕜] V) : V →ₗ[𝕜] V) := by
    ext v
    simp [map_mul]
  have h₂ : ((T ∘L π (p.2⁻¹ * x⁻¹) : V →L[𝕜] V) : V →ₗ[𝕜] V) * (π p.1 : V →ₗ[𝕜] V) =
      ((T ∘L π (p.1⁻¹ * x * p.2)⁻¹ : V →L[𝕜] V) : V →ₗ[𝕜] V) := by
    ext v
    simp [map_mul, mul_inv_rev, mul_assoc]
  rw [traceCoeff_apply, traceCoeff_apply, traceCLM_apply, traceCLM_apply, h₁,
    LinearMap.trace_mul_comm, h₂]

/-- **The two-sided Hom action becomes bi-translation of the trace coefficient**, as an identity of
continuous functions. This is `ContRepresentation.traceCoeff_biLinHom_apply` in the form the
`L²`-level equivariance consumes. -/
theorem traceCoeff_biLinHom (p : G × G) (T : V →L[𝕜] V) :
    traceCoeff π hπ (biLinHom π π p T) =
      (traceCoeff π hπ T).comp
        ⟨fun x => p.1⁻¹ * x * p.2,
          continuous_const.mul continuous_id |>.mul continuous_const⟩ :=
  ContinuousMap.ext fun x => traceCoeff_biLinHom_apply π hπ p T x

end Bitranslation

end ContRepresentation
