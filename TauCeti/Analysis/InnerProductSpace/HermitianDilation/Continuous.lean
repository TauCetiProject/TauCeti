/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Normed.Lp.ProdLp
import TauCeti.Analysis.Normed.Operator.Compact.HilbertAdjoint

/-!
# Bounded Hermitian dilations and block operators on `L²` products

A bounded linear operator `A : E →L[𝕜] F` between Hilbert spaces determines a bounded
self-adjoint endomorphism `A.hermitianDilation` of the orthogonal direct sum `WithLp 2 (E × F)`
with block matrix `[[0, A†], [A, 0]]`, the infinite-dimensional bounded counterpart of
`LinearMap.hermitianDilation`. Its square is the diagonal block sum `(A† ∘L A) ⊕ (A ∘L A†)`,
its operator norm equals `‖A‖`, and it is compact if and only if `A` is compact.

Alongside the off-diagonal dilation, this file records the algebraic, adjoint, star, and
compactness properties of diagonal block sums `f.withLpProdMap p g`, together with the graded
commutation identities between `(F ⊕ -F)` and `[[0, D], [D, 0]]` used when doubling contractions
into self-adjoint involutions.

## Main definitions

* `ContinuousLinearMap.hermitianDilation`: the bounded operator `(x, y) ↦ (A† y, A x)` on
  `WithLp 2 (E × F)`.

## Main statements

* `ContinuousLinearMap.withLpProdMap_comp`, `ContinuousLinearMap.withLpProdMap_mul`,
  `ContinuousLinearMap.adjoint_withLpProdMap`, `ContinuousLinearMap.star_withLpProdMap`:
  composition, multiplication, and Hilbert-space adjoints of block sums.
* `ContinuousLinearMap.isCompactOperator_withLpProdMap_iff`: a block sum is compact if and only
  if both blocks are compact.
* `ContinuousLinearMap.isSelfAdjoint_hermitianDilation`: the Hermitian dilation is self-adjoint.
* `ContinuousLinearMap.hermitianDilation_comp_self`: squaring `A.hermitianDilation` yields
  `(A† ∘L A).withLpProdMap 2 (A ∘L A†)`.
* `ContinuousLinearMap.norm_hermitianDilation`: `‖A.hermitianDilation‖ = ‖A‖`.
* `ContinuousLinearMap.isCompactOperator_hermitianDilation_iff`: `A.hermitianDilation` is compact
  if and only if `A` is compact.
-/

public section

open scoped ENNReal InnerProduct InnerProductSpace

namespace ContinuousLinearMap

section BlockSum

variable {p : ℝ≥0∞} {𝕜 E₁ E₂ F₁ F₂ G₁ G₂ : Type*}

section Topological

variable [Semiring 𝕜]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module 𝕜 F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module 𝕜 F₂]
  [TopologicalSpace G₁] [AddCommGroup G₁] [Module 𝕜 G₁]
  [TopologicalSpace G₂] [AddCommGroup G₂] [Module 𝕜 G₂]

/-- The block sum of identity operators is the identity operator. -/
@[simp]
theorem withLpProdMap_id :
    (ContinuousLinearMap.id 𝕜 E₁).withLpProdMap p (ContinuousLinearMap.id 𝕜 E₂) =
      ContinuousLinearMap.id 𝕜 (WithLp p (E₁ × E₂)) := by
  ext ⟨a, b⟩
  simp

/-- The block sum of `1` and `1` is `1`. -/
@[simp]
theorem withLpProdMap_one :
    (1 : E₁ →L[𝕜] E₁).withLpProdMap p (1 : E₂ →L[𝕜] E₂) = 1 :=
  withLpProdMap_id

/-- Block sums compose componentwise. -/
theorem withLpProdMap_comp (f₂ : F₁ →L[𝕜] G₁) (g₂ : F₂ →L[𝕜] G₂)
    (f₁ : E₁ →L[𝕜] F₁) (g₁ : E₂ →L[𝕜] F₂) :
    (f₂.withLpProdMap p g₂).comp (f₁.withLpProdMap p g₁) =
      (f₂.comp f₁).withLpProdMap p (g₂.comp g₁) := by
  ext x
  simp

/-- Block sums of endomorphisms multiply componentwise. -/
theorem withLpProdMap_mul (f₁ f₂ : E₁ →L[𝕜] E₁) (g₁ g₂ : E₂ →L[𝕜] E₂) :
    f₁.withLpProdMap p g₁ * f₂.withLpProdMap p g₂ = (f₁ * f₂).withLpProdMap p (g₁ * g₂) :=
  withLpProdMap_comp f₁ g₁ f₂ g₂

end Topological

section NormedSMul

variable [Fact (1 ≤ p)] [NormedField 𝕜]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
  [SeminormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [SeminormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]

/-- Block sums commute with scalar multiplication. -/
theorem withLpProdMap_smul (c : 𝕜) (f : E₁ →L[𝕜] F₁) (g : E₂ →L[𝕜] F₂) :
    (c • f).withLpProdMap p (c • g) = c • f.withLpProdMap p g := by
  ext x
  simp [← WithLp.toLp_smul]

end NormedSMul

section Compact

variable [Fact (1 ≤ p)] [Semiring 𝕜]
  [SeminormedAddCommGroup E₁] [Module 𝕜 E₁]
  [SeminormedAddCommGroup E₂] [Module 𝕜 E₂]
  [SeminormedAddCommGroup F₁] [Module 𝕜 F₁]
  [SeminormedAddCommGroup F₂] [Module 𝕜 F₂]

/-- An `L^p` block sum is a compact operator if and only if both blocks are compact operators. -/
@[simp]
theorem isCompactOperator_withLpProdMap_iff {f : E₁ →L[𝕜] F₁} {g : E₂ →L[𝕜] F₂} :
    IsCompactOperator ⇑(f.withLpProdMap p g) ↔ IsCompactOperator f ∧ IsCompactOperator g := by
  constructor
  · intro h
    have hf : f = WithLp.fstL p 𝕜 F₁ F₂ ∘L f.withLpProdMap p g ∘L
        ((WithLp.prodContinuousLinearEquiv p 𝕜 E₁ E₂).symm.toContinuousLinearMap ∘L
          inl 𝕜 E₁ E₂) := by
      ext x
      simp
    have hg : g = WithLp.sndL p 𝕜 F₁ F₂ ∘L f.withLpProdMap p g ∘L
        ((WithLp.prodContinuousLinearEquiv p 𝕜 E₁ E₂).symm.toContinuousLinearMap ∘L
          inr 𝕜 E₁ E₂) := by
      ext x
      simp
    exact ⟨by
        rw [hf]
        exact (h.comp_clm ((WithLp.prodContinuousLinearEquiv p 𝕜 E₁ E₂).symm.toContinuousLinearMap
          ∘L inl 𝕜 E₁ E₂)).clm_comp (WithLp.fstL p 𝕜 F₁ F₂),
      by
        rw [hg]
        exact (h.comp_clm ((WithLp.prodContinuousLinearEquiv p 𝕜 E₁ E₂).symm.toContinuousLinearMap
          ∘L inr 𝕜 E₁ E₂)).clm_comp (WithLp.sndL p 𝕜 F₁ F₂)⟩
  · rintro ⟨hf, hg⟩
    have hfg : f.withLpProdMap p g =
        (((WithLp.prodContinuousLinearEquiv p 𝕜 F₁ F₂).symm.toContinuousLinearMap ∘L
          inl 𝕜 F₁ F₂) ∘L f ∘L WithLp.fstL p 𝕜 E₁ E₂) +
        (((WithLp.prodContinuousLinearEquiv p 𝕜 F₁ F₂).symm.toContinuousLinearMap ∘L
          inr 𝕜 F₁ F₂) ∘L g ∘L WithLp.sndL p 𝕜 E₁ E₂) := by
      ext x
      simp [← WithLp.toLp_add]
    rw [hfg, FunLike.coe_add]
    exact ((hf.comp_clm (WithLp.fstL p 𝕜 E₁ E₂)).clm_comp
      ((WithLp.prodContinuousLinearEquiv p 𝕜 F₁ F₂).symm.toContinuousLinearMap ∘L inl 𝕜 F₁ F₂)).add
      ((hg.comp_clm (WithLp.sndL p 𝕜 E₁ E₂)).clm_comp
        ((WithLp.prodContinuousLinearEquiv p 𝕜 F₁ F₂).symm.toContinuousLinearMap ∘L inr 𝕜 F₁ F₂))

end Compact

section Adjoint

variable {𝕜 E₁ E₂ F₁ F₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
  [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [CompleteSpace F₂]

/-- **Adjoint of a Hilbert block sum.** `(f ⊕ g)† = f† ⊕ g†`. -/
@[simp]
theorem adjoint_withLpProdMap (f : E₁ →L[𝕜] F₁) (g : E₂ →L[𝕜] F₂) :
    (f.withLpProdMap 2 g)† = (f†).withLpProdMap 2 (g†) := by
  refine ((eq_adjoint_iff _ _).mpr fun x y ↦ ?_).symm
  simp [WithLp.prod_inner_apply, adjoint_inner_left]

/-- **Star of a Hilbert block sum.** `star (f ⊕ g) = star f ⊕ star g`. -/
@[simp]
theorem star_withLpProdMap (f : E₁ →L[𝕜] E₁) (g : E₂ →L[𝕜] E₂) :
    star (f.withLpProdMap 2 g) = (star f).withLpProdMap 2 (star g) := by
  simp only [star_eq_adjoint, adjoint_withLpProdMap]

/-- A Hilbert block sum is self-adjoint if and only if both blocks are self-adjoint. -/
@[simp]
theorem isSelfAdjoint_withLpProdMap_iff {f : E₁ →L[𝕜] E₁} {g : E₂ →L[𝕜] E₂} :
    IsSelfAdjoint (f.withLpProdMap 2 g) ↔ IsSelfAdjoint f ∧ IsSelfAdjoint g := by
  refine ⟨fun h ↦ ?_, fun ⟨hf, hg⟩ ↦ ?_⟩
  · have h' := h.star_eq
    rw [star_withLpProdMap] at h'
    refine ⟨?_, ?_⟩
    · ext x
      simpa [IsSelfAdjoint] using congrArg WithLp.fst congr($h' (WithLp.toLp 2 (x, 0)))
    · ext y
      simpa [IsSelfAdjoint] using congrArg WithLp.snd congr($h' (WithLp.toLp 2 (0, y)))
  · rw [IsSelfAdjoint, star_withLpProdMap, hf.star_eq, hg.star_eq]

end Adjoint

end BlockSum

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

@[simp]
theorem hermitianDilation_apply (A : E →L[𝕜] F) (x : WithLp 2 (E × F)) :
    A.hermitianDilation x = WithLp.toLp 2 ((A†) x.snd, A x.fst) :=
  (rfl)

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
  have hfac : A.hermitianDilation ∘L B.withLpProdMap 2 (0 : F →L[𝕜] F) =
      ((WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap ∘L
        inr 𝕜 E F) ∘L (A ∘L B) ∘L WithLp.fstL 2 𝕜 G F := by
    ext x
    simp
  have hrec : A ∘L B = WithLp.sndL 2 𝕜 E F ∘L
      (A.hermitianDilation ∘L B.withLpProdMap 2 (0 : F →L[𝕜] F)) ∘L
      ((WithLp.prodContinuousLinearEquiv 2 𝕜 G F).symm.toContinuousLinearMap ∘L inl 𝕜 G F) := by
    ext x
    simp
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [hrec]
    exact (h.comp_clm ((WithLp.prodContinuousLinearEquiv 2 𝕜 G F).symm.toContinuousLinearMap ∘L
      inl 𝕜 G F)).clm_comp (WithLp.sndL 2 𝕜 E F)
  · rw [hfac]
    exact (h.comp_clm (WithLp.fstL 2 𝕜 G F)).clm_comp
      ((WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap ∘L inr 𝕜 E F)

/-- The Hermitian dilation `A.hermitianDilation` is compact if and only if `A` is compact. -/
@[simp]
theorem isCompactOperator_hermitianDilation_iff {A : E →L[𝕜] F} :
    IsCompactOperator A.hermitianDilation ↔ IsCompactOperator A := by
  constructor
  · intro h
    have hA : A = WithLp.sndL 2 𝕜 E F ∘L A.hermitianDilation ∘L
        ((WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap ∘L inl 𝕜 E F) := by
      ext x
      simp
    rw [hA]
    exact (h.comp_clm ((WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap ∘L
      inl 𝕜 E F)).clm_comp (WithLp.sndL 2 𝕜 E F)
  · intro h
    have hD : A.hermitianDilation =
        (((WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap ∘L
          inl 𝕜 E F) ∘L (A†) ∘L WithLp.sndL 2 𝕜 E F) +
        (((WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap ∘L
          inr 𝕜 E F) ∘L A ∘L WithLp.fstL 2 𝕜 E F) := by
      ext x
      simp [← WithLp.toLp_add]
    rw [hD, FunLike.coe_add]
    exact ((h.adjoint.comp_clm (WithLp.sndL 2 𝕜 E F)).clm_comp
      ((WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap ∘L inl 𝕜 E F)).add
      ((h.comp_clm (WithLp.fstL 2 𝕜 E F)).clm_comp
        ((WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap ∘L inr 𝕜 E F))

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
