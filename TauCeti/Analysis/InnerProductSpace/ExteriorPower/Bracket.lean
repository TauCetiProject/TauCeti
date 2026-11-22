/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum
import TauCeti.LinearAlgebra.BilinearMap.Multilinear
import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.CliffordExteriorSquare
import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors
import TauCeti.LinearAlgebra.ExteriorPower.Square

/-!
# The bracket of the orthogonal Lie algebra on bivectors

Let `V` be a finite-dimensional real inner product space. Each two-vector `X ∈ ⋀² V` acts on `V`
by the skew endomorphism `A_X = twoVectorContraction X`, `u ↦ u ⌟ X`; on a pure wedge
`A_(a ∧ b) u = ⟪a, u⟫ b - ⟪b, u⟫ a` (`TauCeti.twoVectorContraction_ιMulti_two_apply`). The map
`X ↦ A_X` is injective (`TauCeti.twoVectorContraction_injective`), and it carries the inner
product of `⋀² V` to the scalar product `-½ tr (A B)` used by Böhm and Wilking
(`TauCeti.trace_twoVectorContraction_mul_twoVectorContraction`). This is the
standard identification of `⋀² V` with the orthogonal Lie algebra `so(V)`. This file packages the
Lie bracket of `so(V)` on bivectors as a linear map `TauCeti.bivectorAd : ⋀² (⋀² V) → ⋀² V`,
`X ∧ Y ↦ [X, Y]`, the map called `ad` by Böhm and Wilking, and computes its adjoint.

The bracket is the commutator bracket of quadratic Clifford elements, transported to `⋀² V` by
`CliffordAlgebra.bivectorLieEquiv` for the form `v ↦ -‖v‖² / 2`, whose polar form is `-⟪u, v⟫`.
For this form the commutator action of the Clifford bivector of `X` on generators is exactly
`A_X`, so the bracket is characterized by `A_[X, Y] = ⁅A_X, A_Y⁆`
(`TauCeti.twoVectorContraction_bivectorAd_ιMulti`), equivalently by
`⟪[X, Y], u ∧ v⟫ = ⟪A_X u, A_Y v⟫ - ⟪A_Y u, A_X v⟫` (`TauCeti.inner_bivectorAd_ιMulti`).

The adjoint `ad*` of the bracket sends `u ∧ v` to `∑ₚ (u ∧ eₚ) ∧ (v ∧ eₚ)` for every orthonormal
basis `(eₚ)` of `V` (`TauCeti.adjoint_bivectorAd_ιMulti`). This is the formula that turns the
operator `R# = ad ∘ (R ∧ R) ∘ ad*` of the Ricci-flow reaction term into a contraction of curvature
tensors.

## Main definitions

* `TauCeti.bivectorAd`: the bracket `X ∧ Y ↦ [X, Y]` of `so(V)` on `⋀² V`.

## Main results

* `TauCeti.twoVectorContraction_bivectorAd_ιMulti`: `A_[X, Y] = ⁅A_X, A_Y⁆`.
* `TauCeti.inner_bivectorAd_ιMulti`: `⟪[X, Y], u ∧ v⟫ = ⟪A_X u, A_Y v⟫ - ⟪A_Y u, A_X v⟫`.
* `TauCeti.adjoint_bivectorAd_ιMulti`: `ad* (u ∧ v) = ∑ₚ (u ∧ eₚ) ∧ (v ∧ eₚ)`.

## References

* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*,
  Ann. of Math. 167 (2008), 1079–1097, Section 2.
-/

public section

open exteriorPower
open scoped RealInnerProductSpace

noncomputable section

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### The Clifford model of the bracket -/

variable (V) in
/-- The quadratic form `v ↦ -‖v‖² / 2`, with polar form `-⟪u, v⟫`. -/
private def negHalfNormSq : QuadraticForm ℝ V :=
  LinearMap.BilinMap.toQuadraticMap ((-(2 : ℝ)⁻¹) • innerₗ V)

omit [FiniteDimensional ℝ V] in
private theorem polar_negHalfNormSq (u v : V) :
    QuadraticMap.polar (negHalfNormSq V) u v = -⟪u, v⟫ := by
  rw [negHalfNormSq, LinearMap.BilinMap.polar_toQuadraticMap]
  simp only [LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul, real_inner_comm u v]
  ring

attribute [local instance 100] LieRing.ofAssociativeRing

/-- For the form `negHalfNormSq`, the commutator of the Clifford bivector of `X` with a generator
is the generator of `A_X`. -/
private theorem lie_bivectorExterior_ι (X : ⋀[ℝ]^2 V) (x : V) :
    ⁅CliffordAlgebra.bivectorExterior (negHalfNormSq V) X, CliffordAlgebra.ι (negHalfNormSq V) x⁆ =
      CliffordAlgebra.ι (negHalfNormSq V) (twoVectorContraction X x) := by
  -- Both sides are linear in `X`, so it suffices to compare them on pure wedges.
  have key : (LinearMap.mulRight ℝ (CliffordAlgebra.ι (negHalfNormSq V) x) -
      LinearMap.mulLeft ℝ (CliffordAlgebra.ι (negHalfNormSq V) x)) ∘ₗ
        CliffordAlgebra.bivectorExterior (negHalfNormSq V) =
      CliffordAlgebra.ι (negHalfNormSq V) ∘ₗ LinearMap.applyₗ x ∘ₗ twoVectorContractionₗ V := by
    refine linearMap_ext_ιMulti_two fun a b ↦ ?_
    have h := CliffordAlgebra.bivector_lie_ι (negHalfNormSq V) a b x
    rw [Ring.lie_def] at h
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.mulRight_apply,
      LinearMap.mulLeft_apply, CliffordAlgebra.bivectorExterior_apply_ιMulti, h,
      LinearMap.applyₗ_apply_apply, twoVectorContractionₗ_apply,
      twoVectorContraction_ιMulti_two_apply, polar_negHalfNormSq]
    congr 1
    module
  simpa only [Ring.lie_def, LinearMap.coe_comp, Function.comp_apply, LinearMap.sub_apply,
    LinearMap.mulRight_apply, LinearMap.mulLeft_apply, LinearMap.applyₗ_apply_apply,
    twoVectorContractionₗ_apply] using LinearMap.congr_fun key X

/-! ### The bracket -/

/-- The bracket of `so(V)` on bivectors, transported from the Clifford commutator. -/
private def bivectorBracket : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V :=
  letI := CliffordAlgebra.bivectorLieRing (negHalfNormSq V)
  letI := CliffordAlgebra.bivectorLieAlgebra (negHalfNormSq V)
  (LieModule.toEnd ℝ (⋀[ℝ]^2 V) (⋀[ℝ]^2 V) : ⋀[ℝ]^2 V →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V))

private theorem twoVectorContraction_bivectorBracket (X Y : ⋀[ℝ]^2 V) :
    twoVectorContraction (bivectorBracket X Y) =
      ⁅twoVectorContraction X, twoVectorContraction Y⁆ := by
  let := CliffordAlgebra.bivectorLieRing (negHalfNormSq V)
  let := CliffordAlgebra.bivectorLieAlgebra (negHalfNormSq V)
  ext x
  apply CliffordAlgebra.ι_injective (negHalfNormSq V)
  have hcoe (Z : ⋀[ℝ]^2 V) : ((CliffordAlgebra.bivectorLieEquiv (negHalfNormSq V) Z :
      CliffordAlgebra.quadraticLieSubalgebra (negHalfNormSq V)) : CliffordAlgebra _) =
      CliffordAlgebra.bivectorExterior (negHalfNormSq V) Z := by
    simp
  have hbr : CliffordAlgebra.bivectorExterior (negHalfNormSq V) (bivectorBracket X Y) =
      ⁅CliffordAlgebra.bivectorExterior (negHalfNormSq V) X,
        CliffordAlgebra.bivectorExterior (negHalfNormSq V) Y⁆ := by
    rw [← hcoe, ← hcoe, ← hcoe, ← LieSubalgebra.coe_bracket, ← LieEquiv.map_lie, bivectorBracket,
      LieHom.coe_toLinearMap, LieModule.toEnd_apply_apply]
  rw [← lie_bivectorExterior_ι, hbr, lie_lie, lie_bivectorExterior_ι, lie_bivectorExterior_ι,
    lie_bivectorExterior_ι, lie_bivectorExterior_ι, Ring.lie_def, LinearMap.sub_apply, map_sub,
    mul_apply_eq_comp, mul_apply_eq_comp]

omit [FiniteDimensional ℝ V] in
private theorem isAlt_bivectorBracket : (bivectorBracket (V := V)).IsAlt := fun X ↦ by
  let := CliffordAlgebra.bivectorLieRing (negHalfNormSq V)
  let := CliffordAlgebra.bivectorLieAlgebra (negHalfNormSq V)
  exact lie_self X

/-- The bracket of the orthogonal Lie algebra `so(V)` on bivectors, as the linear map
`⋀² (⋀² V) → ⋀² V`, `X ∧ Y ↦ [X, Y]`, called `ad` by Böhm and Wilking. Under the identification
`X ↦ A_X = twoVectorContraction X` of `⋀² V` with `so(V)` it is the commutator,
`A_[X, Y] = ⁅A_X, A_Y⁆` (`TauCeti.twoVectorContraction_bivectorAd_ιMulti`), which determines
it. -/
def bivectorAd : ⋀[ℝ]^2 (⋀[ℝ]^2 V) →ₗ[ℝ] ⋀[ℝ]^2 V :=
  alternatingMapLinearEquiv
    (LinearMap.IsAlt.toAlternatingMap isAlt_bivectorBracket)

omit [FiniteDimensional ℝ V] in
private theorem bivectorAd_ιMulti (X Y : ⋀[ℝ]^2 V) :
    bivectorAd (ιMulti ℝ 2 ![X, Y]) = bivectorBracket X Y := by
  rw [bivectorAd, alternatingMapLinearEquiv_apply_ιMulti, LinearMap.IsAlt.toAlternatingMap_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]

/-- **The bracket of `so(V)`**: the skew endomorphism of `[X, Y]` is the commutator of those of
`X` and `Y`, `A_[X, Y] = ⁅A_X, A_Y⁆`. -/
theorem twoVectorContraction_bivectorAd_ιMulti (X Y : ⋀[ℝ]^2 V) :
    twoVectorContraction (bivectorAd (ιMulti ℝ 2 ![X, Y])) =
      ⁅twoVectorContraction X, twoVectorContraction Y⁆ := by
  rw [bivectorAd_ιMulti, twoVectorContraction_bivectorBracket]

/-- The bracket of `so(V)` against a pure wedge:
`⟪[X, Y], u ∧ v⟫ = ⟪A_X u, A_Y v⟫ - ⟪A_Y u, A_X v⟫`. -/
theorem inner_bivectorAd_ιMulti (X Y : ⋀[ℝ]^2 V) (u v : V) :
    ⟪bivectorAd (ιMulti ℝ 2 ![X, Y]), ιMulti ℝ 2 ![u, v]⟫ =
      ⟪twoVectorContraction X u, twoVectorContraction Y v⟫ -
        ⟪twoVectorContraction Y u, twoVectorContraction X v⟫ := by
  rw [← inner_twoVectorContraction_apply, twoVectorContraction_bivectorAd_ιMulti, Ring.lie_def,
    LinearMap.sub_apply, inner_sub_left, mul_apply_eq_comp, mul_apply_eq_comp,
    inner_twoVectorContraction_apply_left X (twoVectorContraction Y u),
    inner_twoVectorContraction_apply_left Y (twoVectorContraction X u)]
  ring

/-- **The adjoint of the bracket**: for every orthonormal basis `(eₚ)` of `V`,
`ad* (u ∧ v) = ∑ₚ (u ∧ eₚ) ∧ (v ∧ eₚ)`. -/
theorem adjoint_bivectorAd_ιMulti {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (u v : V) :
    LinearMap.adjoint bivectorAd (ιMulti ℝ 2 ![u, v]) =
      ∑ p, ιMulti ℝ 2 ![ιMulti ℝ 2 ![u, b p], ιMulti ℝ 2 ![v, b p]] := by
  refine ext_inner_ιMulti_two fun X Y ↦ ?_
  rw [LinearMap.adjoint_inner_left, real_inner_comm, inner_bivectorAd_ιMulti, sum_inner]
  simp only [inner_ιMulti_two (E := ⋀[ℝ]^2 V)]
  simp only [real_inner_comm X, real_inner_comm Y, ← inner_twoVectorContraction_apply,
    Finset.sum_sub_distrib, b.real_sum_inner_mul_inner]

end TauCeti
