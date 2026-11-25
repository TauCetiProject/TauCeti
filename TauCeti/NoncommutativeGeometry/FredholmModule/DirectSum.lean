/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.Normed.Operator.Compact.ProdLp
public import TauCeti.NoncommutativeGeometry.FredholmModule.Basic

/-!
# Orthogonal direct sums of Fredholm modules

Two odd (or even) Fredholm modules `M₁` on `H₁` and `M₂` on `H₂` over the same `*`-algebra `A`
combine on the Hilbert direct sum `WithLp 2 (H₁ × H₂)` into an orthogonal direct-sum Fredholm
module `M₁.prod M₂` with representation `π₁ ⊕ π₂` (`NonUnitalStarAlgHom.prodStarRep`) and operator
`F₁ ⊕ F₂` (`ContinuousLinearMap.withLpProdMap`), plus grading `γ₁ ⊕ γ₂` in the even case.

Normalization (`IsNormalized`) and degeneracy (`IsDegenerate`) are preserved under orthogonal
direct sums. This file also defines the degenerate summand `EvenFredholmModule.negZeroRep`
`(H, 0, -F, -γ)` used when connecting `M ⊕ (H, 0, -F, -γ)` to the doubled module `M.double`.

## Main definitions

* `TauCeti.FredholmModule.prod`: orthogonal direct sum of odd Fredholm modules on
  `WithLp 2 (H₁ × H₂)`.
* `TauCeti.EvenFredholmModule.prod`: orthogonal direct sum of even Fredholm modules on
  `WithLp 2 (H₁ × H₂)`.
* `TauCeti.EvenFredholmModule.negZeroRep`: the degenerate even module `(H, 0, -F, -γ)`.
-/

public section

noncomputable section

open ContinuousLinearMap

namespace TauCeti

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Module ℂ A] [Star A]
variable {H H₁ H₂ : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

namespace FredholmModule

/-- **Orthogonal direct sum** of two odd Fredholm modules on `WithLp 2 (H₁ × H₂)`. -/
def prod (M₁ : FredholmModule A H₁) (M₂ : FredholmModule A H₂) :
    FredholmModule A (WithLp 2 (H₁ × H₂)) where
  rep := M₁.rep.prodStarRep M₂.rep
  operator := M₁.operator.withLpProdMap 2 M₂.operator
  isSelfAdjoint_operator :=
    (isSelfAdjoint_withLpProdMap_iff _ _).mpr
      ⟨M₁.isSelfAdjoint_operator, M₂.isSelfAdjoint_operator⟩
  isCompactOperator_commutator a := by
    let Φ := withLpProdMapStarAlgHom (𝕜 := ℂ) (E₁ := H₁) (E₂ := H₂)
    have hΦ (S : H₁ →L[ℂ] H₁) (T : H₂ →L[ℂ] H₂) : S.withLpProdMap 2 T = Φ (S, T) :=
      (withLpProdMapStarAlgHom_apply (S, T)).symm
    rw [NonUnitalStarAlgHom.prodStarRep_apply]
    simp only [hΦ, ← map_mul, ← map_sub]
    rw [withLpProdMapStarAlgHom_apply]
    exact isCompactOperator_withLpProdMap_iff.mpr
      ⟨M₁.isCompactOperator_commutator a, M₂.isCompactOperator_commutator a⟩
  isCompactOperator_mul_self_sub_one_mul a := by
    let Φ := withLpProdMapStarAlgHom (𝕜 := ℂ) (E₁ := H₁) (E₂ := H₂)
    have hΦ (S : H₁ →L[ℂ] H₁) (T : H₂ →L[ℂ] H₂) : S.withLpProdMap 2 T = Φ (S, T) :=
      (withLpProdMapStarAlgHom_apply (S, T)).symm
    rw [NonUnitalStarAlgHom.prodStarRep_apply]
    simp only [hΦ, ← map_one Φ, ← map_mul, ← map_sub]
    rw [withLpProdMapStarAlgHom_apply]
    exact isCompactOperator_withLpProdMap_iff.mpr
      ⟨M₁.isCompactOperator_mul_self_sub_one_mul a, M₂.isCompactOperator_mul_self_sub_one_mul a⟩

@[simp]
theorem prod_rep_apply (M₁ : FredholmModule A H₁) (M₂ : FredholmModule A H₂) (a : A) :
    (M₁.prod M₂).rep a = (M₁.rep a).withLpProdMap 2 (M₂.rep a) :=
  NonUnitalStarAlgHom.prodStarRep_apply M₁.rep M₂.rep a

@[simp]
theorem prod_operator (M₁ : FredholmModule A H₁) (M₂ : FredholmModule A H₂) :
    (M₁.prod M₂).operator = M₁.operator.withLpProdMap 2 M₂.operator :=
  (rfl)

theorem IsNormalized.prod {M₁ : FredholmModule A H₁} {M₂ : FredholmModule A H₂}
    (h₁ : M₁.IsNormalized) (h₂ : M₂.IsNormalized) : (M₁.prod M₂).IsNormalized := by
  rw [isNormalized_iff, prod_operator, ← withLpProdMapStarAlgHom_apply (M₁.operator, M₂.operator),
    ← map_mul]
  simp [h₁.operator_mul_operator, h₂.operator_mul_operator]

theorem IsDegenerate.prod {M₁ : FredholmModule A H₁} {M₂ : FredholmModule A H₂}
    (h₁ : M₁.IsDegenerate) (h₂ : M₂.IsDegenerate) : (M₁.prod M₂).IsDegenerate where
  commutator_eq_zero a := by
    let Φ := withLpProdMapStarAlgHom (𝕜 := ℂ) (E₁ := H₁) (E₂ := H₂)
    have hΦ (S : H₁ →L[ℂ] H₁) (T : H₂ →L[ℂ] H₂) : S.withLpProdMap 2 T = Φ (S, T) :=
      (withLpProdMapStarAlgHom_apply (S, T)).symm
    rw [prod_operator, prod_rep_apply]
    simp only [hΦ, ← map_mul, ← map_sub]
    simp [Φ, h₁.commutator_eq_zero a, h₂.commutator_eq_zero a]
  mul_self_sub_one_mul_eq_zero a := by
    let Φ := withLpProdMapStarAlgHom (𝕜 := ℂ) (E₁ := H₁) (E₂ := H₂)
    have hΦ (S : H₁ →L[ℂ] H₁) (T : H₂ →L[ℂ] H₂) : S.withLpProdMap 2 T = Φ (S, T) :=
      (withLpProdMapStarAlgHom_apply (S, T)).symm
    rw [prod_operator, prod_rep_apply]
    simp only [hΦ, ← map_one Φ, ← map_mul, ← map_sub]
    simp [Φ, h₁.mul_self_sub_one_mul_eq_zero a, h₂.mul_self_sub_one_mul_eq_zero a]

end FredholmModule

namespace EvenFredholmModule

/-- **Orthogonal direct sum** of two even Fredholm modules on `WithLp 2 (H₁ × H₂)`. -/
def prod (M₁ : EvenFredholmModule A H₁) (M₂ : EvenFredholmModule A H₂) :
    EvenFredholmModule A (WithLp 2 (H₁ × H₂)) where
  toFredholmModule := M₁.toFredholmModule.prod M₂.toFredholmModule
  grading := M₁.grading.withLpProdMap 2 M₂.grading
  isSelfAdjoint_grading :=
    (isSelfAdjoint_withLpProdMap_iff _ _).mpr
      ⟨M₁.isSelfAdjoint_grading, M₂.isSelfAdjoint_grading⟩
  grading_mul_grading := by
    rw [← withLpProdMapStarAlgHom_apply (M₁.grading, M₂.grading), ← map_mul]
    simp [M₁.grading_mul_grading, M₂.grading_mul_grading]
  commute_grading_rep a := by
    let Φ := withLpProdMapStarAlgHom (𝕜 := ℂ) (E₁ := H₁) (E₂ := H₂)
    have hΦ (S : H₁ →L[ℂ] H₁) (T : H₂ →L[ℂ] H₂) : S.withLpProdMap 2 T = Φ (S, T) :=
      (withLpProdMapStarAlgHom_apply (S, T)).symm
    rw [Commute, SemiconjBy, FredholmModule.prod_rep_apply]
    simp only [hΦ, ← map_mul]
    simp [(M₁.commute_grading_rep a).eq, (M₂.commute_grading_rep a).eq]
  grading_mul_operator := by
    let Φ := withLpProdMapStarAlgHom (𝕜 := ℂ) (E₁ := H₁) (E₂ := H₂)
    have hΦ (S : H₁ →L[ℂ] H₁) (T : H₂ →L[ℂ] H₂) : S.withLpProdMap 2 T = Φ (S, T) :=
      (withLpProdMapStarAlgHom_apply (S, T)).symm
    rw [FredholmModule.prod_operator]
    simp only [hΦ, ← map_mul, ← map_neg]
    simp [M₁.grading_mul_operator, M₂.grading_mul_operator]

@[simp]
theorem prod_toFredholmModule (M₁ : EvenFredholmModule A H₁) (M₂ : EvenFredholmModule A H₂) :
    (M₁.prod M₂).toFredholmModule = M₁.toFredholmModule.prod M₂.toFredholmModule :=
  (rfl)

@[simp]
theorem prod_grading (M₁ : EvenFredholmModule A H₁) (M₂ : EvenFredholmModule A H₂) :
    (M₁.prod M₂).grading = M₁.grading.withLpProdMap 2 M₂.grading :=
  (rfl)

/-- Degenerate even Fredholm module `(H, 0, -F, -γ)` used as the zero-representation summand in
`EvenFredholmModule.doubleHomotopy`. -/
def negZeroRep (M : EvenFredholmModule A H) : EvenFredholmModule A H :=
  zeroRep A (-M.operator) (-M.grading) M.isSelfAdjoint_operator.neg M.isSelfAdjoint_grading.neg
    (by rw [neg_mul_neg, M.grading_mul_grading])
    (by rw [neg_mul_neg, mul_neg, neg_mul, neg_neg, M.grading_mul_operator])

@[simp]
theorem negZeroRep_toFredholmModule (M : EvenFredholmModule A H) :
    M.negZeroRep.toFredholmModule =
      FredholmModule.zeroRep A (-M.operator) M.isSelfAdjoint_operator.neg := by
  simp [negZeroRep]

@[simp]
theorem negZeroRep_grading (M : EvenFredholmModule A H) : M.negZeroRep.grading = -M.grading := by
  simp [negZeroRep]

theorem isDegenerate_negZeroRep (M : EvenFredholmModule A H) : M.negZeroRep.IsDegenerate :=
  EvenFredholmModule.isDegenerate_zeroRep (-M.operator) (-M.grading) _ _ _ _

end EvenFredholmModule

end TauCeti
