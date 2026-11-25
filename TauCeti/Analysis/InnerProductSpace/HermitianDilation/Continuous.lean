/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import TauCeti.Analysis.InnerProductSpace.HermitianDilation.Basic
public import TauCeti.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.Normed.Operator.Compact.ProdLp
import TauCeti.Analysis.Normed.Operator.Compact.HilbertAdjoint

/-!
# Bounded Hermitian dilations on `L²` products

A bounded linear operator `A : E →L[𝕜] F` between Hilbert spaces determines a bounded
self-adjoint endomorphism `A.hermitianDilation` of the orthogonal direct sum `WithLp 2 (E × F)`
with block matrix `[[0, A†], [A, 0]]`, the infinite-dimensional bounded counterpart of
`LinearMap.hermitianDilation` (`ContinuousLinearMap.toLinearMap_hermitianDilation`). Its square is
the diagonal block sum `(A† ∘L A) ⊕ (A ∘L A†)`, its operator norm equals `‖A‖`, and it is compact
if and only if `A` is compact.

This file also records the graded anticommutation identities between `(F ⊕ -F)` and
`[[0, D], [D, 0]]` used when doubling contractions into self-adjoint involutions.

## Main definitions

* `ContinuousLinearMap.hermitianDilation`: the bounded operator `(x, y) ↦ (A† y, A x)` on
  `WithLp 2 (E × F)`.

## Main statements

* `ContinuousLinearMap.toLinearMap_hermitianDilation`: in finite dimensions, the underlying linear
  map of `A.hermitianDilation` agrees with `LinearMap.hermitianDilation`.
* `ContinuousLinearMap.isSelfAdjoint_hermitianDilation`: the Hermitian dilation is self-adjoint.
* `ContinuousLinearMap.hermitianDilation_comp_self`, `IsSelfAdjoint.hermitianDilation_mul_self`:
  squaring `A.hermitianDilation` yields `(A† ∘L A).withLpProdMap 2 (A ∘L A†)`.
* `ContinuousLinearMap.norm_hermitianDilation`: `‖A.hermitianDilation‖ = ‖A‖`.
* `ContinuousLinearMap.isCompactOperator_hermitianDilation_iff`: `A.hermitianDilation` is compact
  if and only if `A` is compact.
-/

public section

open scoped ENNReal InnerProduct InnerProductSpace

namespace ContinuousLinearMap

section HermitianDilation

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The bounded **Hermitian dilation** of `A : E →L[𝕜] F` on the Hilbert direct sum
`WithLp 2 (E × F)`, with block matrix `[[0, A†], [A, 0]]`. -/
noncomputable def hermitianDilation (A : E →L[𝕜] F) :
    WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap ∘L
    ((A† ∘L snd 𝕜 E F).prod (A ∘L fst 𝕜 E F)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 𝕜 E F).toContinuousLinearMap

theorem hermitianDilation_def (A : E →L[𝕜] F) :
    A.hermitianDilation =
      (WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap ∘L
        ((A† ∘L snd 𝕜 E F).prod (A ∘L fst 𝕜 E F)) ∘L
        (WithLp.prodContinuousLinearEquiv 2 𝕜 E F).toContinuousLinearMap :=
  (rfl)

@[simp]
theorem hermitianDilation_apply (A : E →L[𝕜] F) (x : WithLp 2 (E × F)) :
    A.hermitianDilation x = WithLp.toLp 2 ((A†) x.snd, A x.fst) :=
  (rfl)

/-- Block-matrix representation of `A.hermitianDilation` as `[[0, A†], [A, 0]]`. -/
theorem hermitianDilation_eq_blockL2 (A : E →L[𝕜] F) :
    A.hermitianDilation = WithLp.blockL2 0 (A†) A 0 := by
  ext x
  simp

/-- In finite dimensions, the underlying linear map of `A.hermitianDilation` agrees with
`LinearMap.hermitianDilation`. -/
@[simp]
theorem toLinearMap_hermitianDilation [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (A : E →L[𝕜] F) :
    (A.hermitianDilation : WithLp 2 (E × F) →ₗ[𝕜] WithLp 2 (E × F)) =
      (A : E →ₗ[𝕜] F).hermitianDilation := by
  ext x
  simp only [coe_coe, hermitianDilation_apply, LinearMap.hermitianDilation_apply,
    WithLp.ofLp_fst, WithLp.ofLp_snd]
  exact congrArg (fun u ↦ WithLp.toLp 2 (u, A x.fst))
    (congrFun (congrArg DFunLike.coe A.adjoint_toLinearMap.symm) x.snd)

@[simp]
theorem hermitianDilation_zero : hermitianDilation (0 : E →L[𝕜] F) = 0 := by
  ext x
  simp [← WithLp.toLp_zero]

@[simp]
theorem hermitianDilation_neg (A : E →L[𝕜] F) : (-A).hermitianDilation = -A.hermitianDilation := by
  ext x
  simp [← WithLp.toLp_neg]

@[simp]
theorem hermitianDilation_add (A B : E →L[𝕜] F) :
    (A + B).hermitianDilation = A.hermitianDilation + B.hermitianDilation := by
  ext x
  simp [← WithLp.toLp_add]

@[simp]
theorem hermitianDilation_sub (A B : E →L[𝕜] F) :
    (A - B).hermitianDilation = A.hermitianDilation - B.hermitianDilation := by
  ext x
  simp [← WithLp.toLp_sub]

/-- Real scalar multiplication commutes with `hermitianDilation`. -/
theorem hermitianDilation_smul_real (t : ℝ) (A : E →L[𝕜] F) :
    ((t : 𝕜) • A).hermitianDilation = (t : 𝕜) • A.hermitianDilation := by
  ext x
  simp [← WithLp.toLp_smul, map_smulₛₗ]

/-- The Hermitian dilation of a bounded operator is self-adjoint. -/
theorem isSelfAdjoint_hermitianDilation (A : E →L[𝕜] F) :
    IsSelfAdjoint A.hermitianDilation := by
  rw [IsSelfAdjoint, star_eq_adjoint]
  refine ((eq_adjoint_iff _ _).mpr fun x y ↦ ?_).symm
  simp only [hermitianDilation_apply, WithLp.prod_inner_apply, WithLp.fst, WithLp.snd,
    adjoint_inner_left, adjoint_inner_right]
  exact add_comm _ _

@[simp]
theorem adjoint_hermitianDilation (A : E →L[𝕜] F) :
    A.hermitianDilation† = A.hermitianDilation :=
  star_eq_adjoint A.hermitianDilation ▸ A.isSelfAdjoint_hermitianDilation.star_eq

@[simp]
theorem star_hermitianDilation (A : E →L[𝕜] F) :
    star A.hermitianDilation = A.hermitianDilation :=
  A.isSelfAdjoint_hermitianDilation.star_eq

/-- Squaring the Hermitian dilation yields the diagonal block sum of the two Gram operators
`A† ∘L A` and `A ∘L A†`. -/
theorem hermitianDilation_comp_self (A : E →L[𝕜] F) :
    A.hermitianDilation ∘L A.hermitianDilation = (A† ∘L A).withLpProdMap 2 (A ∘L A†) := by
  ext x
  simp

/-- Multiplicative form of `hermitianDilation_comp_self`. -/
theorem hermitianDilation_mul_self (A : E →L[𝕜] F) :
    A.hermitianDilation * A.hermitianDilation = (A† ∘L A).withLpProdMap 2 (A ∘L A†) :=
  A.hermitianDilation_comp_self

/-- For a self-adjoint operator `D`, squaring `D.hermitianDilation` yields `(D * D) ⊕ (D * D)`. -/
theorem _root_.IsSelfAdjoint.hermitianDilation_mul_self {D : E →L[𝕜] E} (hD : IsSelfAdjoint D) :
    D.hermitianDilation * D.hermitianDilation = (D * D).withLpProdMap 2 (D * D) := by
  have hD' : D† = D := star_eq_adjoint D ▸ hD.star_eq
  rw [D.hermitianDilation_mul_self, hD', ← mul_def]

/-- The operator norm of `A.hermitianDilation` equals `‖A‖`. -/
@[simp]
theorem norm_hermitianDilation (A : E →L[𝕜] F) : ‖A.hermitianDilation‖ = ‖A‖ := by
  have hAA : ‖A ∘L A†‖ = ‖A‖ * ‖A‖ := by simpa using norm_adjoint_comp_self (A†)
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), sq, sq,
    ← CStarRing.norm_star_mul_self, star_hermitianDilation, hermitianDilation_mul_self,
    norm_withLpProdMap, norm_adjoint_comp_self, hAA, max_self]

/-- Multiplying `A.hermitianDilation` on the right by a block sum `B ⊕ 0` produces the off-diagonal
operator `(x, y) ↦ (0, A (B x))`, which is compact if and only if `A ∘L B` is compact. -/
theorem isCompactOperator_hermitianDilation_comp_withLpProdMap_zero_right
    {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    (A : E →L[𝕜] F) (B : G →L[𝕜] E) :
    IsCompactOperator ⇑(A.hermitianDilation ∘L B.withLpProdMap 2 (0 : F →L[𝕜] F)) ↔
      IsCompactOperator ⇑(A ∘L B) := by
  set T := A.hermitianDilation ∘L B.withLpProdMap 2 (0 : F →L[𝕜] F)
  have h₁₁ : WithLp.fstL 2 𝕜 E F ∘L T ∘L WithLp.inlL 2 𝕜 G F = 0 := by ext x; simp [T]
  have h₁₂ : WithLp.fstL 2 𝕜 E F ∘L T ∘L WithLp.inrL 2 𝕜 G F = 0 := by ext x; simp [T]
  have h₂₁ : WithLp.sndL 2 𝕜 E F ∘L T ∘L WithLp.inlL 2 𝕜 G F = A ∘L B := by ext x; simp [T]
  have h₂₂ : WithLp.sndL 2 𝕜 E F ∘L T ∘L WithLp.inrL 2 𝕜 G F = 0 := by ext x; simp [T]
  rw [isCompactOperator_withLp_prod_iff, h₁₁, h₁₂, h₂₁, h₂₂]
  simp [isCompactOperator_zero]

/-- The Hermitian dilation `A.hermitianDilation` is compact if and only if `A` is compact. -/
@[simp]
theorem isCompactOperator_hermitianDilation_iff {A : E →L[𝕜] F} :
    IsCompactOperator A.hermitianDilation ↔ IsCompactOperator A := by
  have h₁₁ : WithLp.fstL 2 𝕜 E F ∘L A.hermitianDilation ∘L WithLp.inlL 2 𝕜 E F = 0 := by
    ext x; simp
  have h₁₂ : WithLp.fstL 2 𝕜 E F ∘L A.hermitianDilation ∘L WithLp.inrL 2 𝕜 E F = A† := by
    ext x; simp
  have h₂₁ : WithLp.sndL 2 𝕜 E F ∘L A.hermitianDilation ∘L WithLp.inlL 2 𝕜 E F = A := by
    ext x; simp
  have h₂₂ : WithLp.sndL 2 𝕜 E F ∘L A.hermitianDilation ∘L WithLp.inrL 2 𝕜 E F = 0 := by
    ext x; simp
  rw [isCompactOperator_withLp_prod_iff, h₁₁, h₁₂, h₂₁, h₂₂]
  exact ⟨fun ⟨_, _, hA, _⟩ ↦ hA,
    fun hA ↦ ⟨isCompactOperator_zero, hA.adjoint, hA, isCompactOperator_zero⟩⟩

/-- If a self-adjoint operator `D` commutes with `F`, then `F ⊕ (-F)` anticommutes with
`D.hermitianDilation`. -/
theorem withLpProdMap_neg_mul_hermitianDilation_add {F D : E →L[𝕜] E} (hD : IsSelfAdjoint D)
    (hc : Commute F D) :
    F.withLpProdMap 2 (-F) * D.hermitianDilation +
      D.hermitianDilation * F.withLpProdMap 2 (-F) = 0 := by
  have hD' : D† = D := star_eq_adjoint D ▸ hD.star_eq
  have hFD (x : E) : F (D x) = D (F x) := congr($hc.eq x)
  ext x
  simp [mul_def, hD', hFD, ← WithLp.toLp_add, ← WithLp.toLp_zero]

/-- Rewriting form of `withLpProdMap_neg_mul_hermitianDilation_add`: if a self-adjoint `D`
commutes with `γ`, then `(γ ⊕ -γ) * D.hermitianDilation = -(D.hermitianDilation * (γ ⊕ -γ))`. -/
theorem withLpProdMap_neg_mul_hermitianDilation_eq_neg {γ D : E →L[𝕜] E} (hD : IsSelfAdjoint D)
    (hc : Commute γ D) :
    γ.withLpProdMap 2 (-γ) * D.hermitianDilation =
      -(D.hermitianDilation * γ.withLpProdMap 2 (-γ)) :=
  eq_neg_of_add_eq_zero_left (withLpProdMap_neg_mul_hermitianDilation_add hD hc)

end HermitianDilation

end ContinuousLinearMap
