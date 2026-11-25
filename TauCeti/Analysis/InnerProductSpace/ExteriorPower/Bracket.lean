/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.Analysis.InnerProductSpace.Nondegenerate
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum
import TauCeti.LinearAlgebra.BilinearMap.Multilinear
import TauCeti.LinearAlgebra.ExteriorPower.Square

/-!
# The bracket of the orthogonal Lie algebra on bivectors

Let `V` be a finite-dimensional real inner product space. Each two-vector `X ∈ ⋀² V` acts on `V`
by the skew endomorphism `A_X = twoVectorContraction X`, `u ↦ u ⌟ X`; on a pure wedge
`A_(a ∧ b) u = ⟪u, a⟫ b - ⟪u, b⟫ a` (`TauCeti.twoVectorContraction_ιMulti`). The map
`X ↦ A_X` is injective (`TauCeti.twoVectorContraction_injective`), and it carries the inner
product of `⋀² V` to the scalar product `-½ tr (A B)` used by Böhm and Wilking
(`TauCeti.trace_twoVectorContraction_mul_twoVectorContraction`). This is the
standard identification of `⋀² V` with the orthogonal Lie algebra `so(V)`. This file packages the
Lie bracket of `so(V)` on bivectors as a linear map `TauCeti.bivectorAd : ⋀² (⋀² V) → ⋀² V`,
`X ∧ Y ↦ [X, Y]`, the map called `ad` by Böhm and Wilking, and computes its adjoint.

The bracket is the commutator of skew-adjoint endomorphisms, transported to `⋀² V` by the
identification `LinearMap.BilinForm.exteriorSquareEquivSkewAdjoint` for the inner product, which
sends `X` to `-A_X` (`TauCeti.twoVectorContraction_eq_neg_exteriorSquareEquivSkewAdjoint`). So the
bracket is characterized by `A_[X, Y] = ⁅A_X, A_Y⁆`
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

attribute [local instance 100] LieRing.ofAssociativeRing

variable (V) in
/-- The identification of `⋀² V` with the skew-adjoint endomorphisms of `V`; it sends `X` to
`-A_X`. -/
private abbrev skewEquiv : ⋀[ℝ]^2 V ≃ₗ[ℝ] skewAdjointLieSubalgebra (innerₗ V) :=
  LinearMap.BilinForm.exteriorSquareEquivSkewAdjoint (innerₗ V) bijective_innerₗ
    (LinearMap.BilinForm.isSymm_iff.mpr isSymm_inner)

/-- The bracket of `so(V)` on bivectors, transported from the commutator of skew-adjoint
endomorphisms. -/
private def bivectorBracket : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V :=
  LinearMap.mk₂ ℝ (fun X Y ↦ -(skewEquiv V).symm ⁅skewEquiv V X, skewEquiv V Y⁆)
    (fun _ _ _ ↦ by simp only [map_add, add_lie, neg_add])
    (fun _ _ _ ↦ by simp only [map_smul, smul_lie, smul_neg])
    (fun _ _ _ ↦ by simp only [map_add, lie_add, neg_add])
    (fun _ _ _ ↦ by simp only [map_smul, lie_smul, smul_neg])

private theorem twoVectorContraction_bivectorBracket (X Y : ⋀[ℝ]^2 V) :
    twoVectorContraction (bivectorBracket X Y) =
      ⁅twoVectorContraction X, twoVectorContraction Y⁆ := by
  simp only [bivectorBracket, LinearMap.mk₂_apply, map_neg, LinearEquiv.apply_symm_apply,
    twoVectorContraction_eq_neg_exteriorSquareEquivSkewAdjoint, NegMemClass.coe_neg, neg_neg,
    LieSubalgebra.coe_bracket, neg_lie, lie_neg]

private theorem isAlt_bivectorBracket : (bivectorBracket (V := V)).IsAlt := fun X ↦ by
  simp [bivectorBracket]

/-- The bracket of the orthogonal Lie algebra `so(V)` on bivectors, as the linear map
`⋀² (⋀² V) → ⋀² V`, `X ∧ Y ↦ [X, Y]`, called `ad` by Böhm and Wilking. Under the identification
`X ↦ A_X = twoVectorContraction X` of `⋀² V` with `so(V)` it is the commutator,
`A_[X, Y] = ⁅A_X, A_Y⁆` (`TauCeti.twoVectorContraction_bivectorAd_ιMulti`), which determines
it. -/
def bivectorAd : ⋀[ℝ]^2 (⋀[ℝ]^2 V) →ₗ[ℝ] ⋀[ℝ]^2 V :=
  alternatingMapLinearEquiv
    (LinearMap.IsAlt.toAlternatingMap isAlt_bivectorBracket)

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
