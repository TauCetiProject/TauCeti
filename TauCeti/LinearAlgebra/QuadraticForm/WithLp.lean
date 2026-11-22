/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Isometric equivalences of quadratic maps on `WithLp` products

When a quadratic map `Q` on `WithLp p (M₁ × M₂)` decomposes orthogonally as
`Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2`, `WithLp.linearEquiv` identifies `Q`
isometrically with `Q₁.prod Q₂`, and the structural equivalences of Cartesian products (swapping
factors, reassociating iterated `WithLp` products, and deleting trivial factors) lift to isometric
equivalences of quadratic maps on `WithLp` (`withLpProd`, `withLpProdComm`, `withLpProdAssoc`,
`withLpUniqueProd`, `withLpProdUnique`), together with their comparisons to
`LinearIsometryEquiv` and their base-change compatibility diagrams. We also record
`QuadraticMap.apply_eq_neg_norm_sq_of_withLp_prod` for orthogonal sums of negative
norm-squared forms on `WithLp 2 (U × V)`.
-/

public section

open scoped ENNReal

namespace QuadraticMap.IsometryEquiv

section Binary

variable {p : ℝ≥0∞} {R M₁ M₂ P : Type*} [CommSemiring R]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommMonoid P] [Module R M₁] [Module R M₂] [Module R P]
  {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P} {Q : QuadraticMap R (WithLp p (M₁ × M₂)) P}

/-- `WithLp.linearEquiv` as an isometric equivalence of quadratic maps when
`Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2`. -/
def withLpProd (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) :
    Q.IsometryEquiv (Q₁.prod Q₂) where
  toLinearEquiv := WithLp.linearEquiv p R (M₁ × M₂)
  map_app' x := (hQ x).symm

/-- The underlying linear equivalence of `QuadraticMap.IsometryEquiv.withLpProd`. -/
@[simp]
theorem toLinearEquiv_withLpProd (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) :
    (withLpProd hQ).toLinearEquiv = WithLp.linearEquiv p R (M₁ × M₂) := (rfl)

/-- `QuadraticMap.IsometryEquiv.withLpProd` unwraps `WithLp`. -/
@[simp]
theorem withLpProd_apply (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (x : WithLp p (M₁ × M₂)) : withLpProd hQ x = WithLp.ofLp x := (rfl)

/-- The inverse of `QuadraticMap.IsometryEquiv.withLpProd` wraps a pair in `WithLp`. -/
@[simp]
theorem withLpProd_symm_apply (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (x : M₁ × M₂) : (withLpProd hQ).symm x = WithLp.toLp p x := (rfl)

/-- Exchanging the factors of `WithLp p (M₁ × M₂)` as an isometric equivalence of quadratic maps. -/
def withLpProdComm {Q' : QuadraticMap R (WithLp p (M₂ × M₁)) P}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ' : ∀ y, Q' y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2) : Q.IsometryEquiv Q' :=
  ((withLpProd hQ).trans (QuadraticMap.IsometryEquiv.prodComm Q₁ Q₂)).trans (withLpProd hQ').symm

/-- The underlying linear equivalence of `QuadraticMap.IsometryEquiv.withLpProdComm`. -/
@[simp]
theorem toLinearEquiv_withLpProdComm {Q' : QuadraticMap R (WithLp p (M₂ × M₁)) P}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ' : ∀ y, Q' y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2) :
    (withLpProdComm hQ hQ').toLinearEquiv = (LinearEquiv.prodComm R M₁ M₂).withLpCongr p :=
  LinearEquiv.ext fun x ↦ by
    rw [coe_toLinearEquiv, withLpProdComm, LinearEquiv.coe_withLpCongr]
    simp [WithLp.map, LinearEquiv.prodComm_apply]

/-- `QuadraticMap.IsometryEquiv.withLpProdComm` swaps the two coordinates inside `WithLp`. -/
@[simp]
theorem withLpProdComm_apply {Q' : QuadraticMap R (WithLp p (M₂ × M₁)) P}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ' : ∀ y, Q' y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2) (x : WithLp p (M₁ × M₂)) :
    withLpProdComm hQ hQ' x = WithLp.toLp p ((WithLp.ofLp x).2, (WithLp.ofLp x).1) := by
  rw [← coe_toLinearEquiv, toLinearEquiv_withLpProdComm, LinearEquiv.coe_withLpCongr]
  simp only [WithLp.map, LinearEquiv.prodComm_apply, WithLp.ofLp_snd, WithLp.ofLp_fst,
    WithLp.toLp.injEq]
  ext <;> simp

/-- The inverse of `QuadraticMap.IsometryEquiv.withLpProdComm` swaps the two coordinates back. -/
@[simp]
theorem withLpProdComm_symm_apply {Q' : QuadraticMap R (WithLp p (M₂ × M₁)) P}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ' : ∀ y, Q' y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2) (y : WithLp p (M₂ × M₁)) :
    (withLpProdComm hQ hQ').symm y = WithLp.toLp p ((WithLp.ofLp y).2, (WithLp.ofLp y).1) := by
  rw [symm_apply_eq, withLpProdComm_apply]

/-- Deleting a trivial left factor from `WithLp p (M₁ × M₂)` as a quadratic isometric
equivalence. -/
def withLpUniqueProd [Unique M₁] (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) :
    Q.IsometryEquiv Q₂ :=
  (withLpProd hQ).trans (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂)

/-- `QuadraticMap.IsometryEquiv.withLpUniqueProd` extracts the second coordinate. -/
@[simp]
theorem withLpUniqueProd_apply [Unique M₁]
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) (x : WithLp p (M₁ × M₂)) :
    withLpUniqueProd hQ x = (WithLp.ofLp x).2 := by
  rw [withLpUniqueProd, ← coe_toLinearEquiv]
  simp

/-- The inverse of `QuadraticMap.IsometryEquiv.withLpUniqueProd` inserts zero in the trivial left
coordinate. -/
@[simp]
theorem withLpUniqueProd_symm_apply [Unique M₁]
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) (m : M₂) :
    (withLpUniqueProd hQ).symm m = WithLp.toLp p (0, m) := by
  rw [symm_apply_eq, withLpUniqueProd_apply]

/-- The underlying linear equivalence of `QuadraticMap.IsometryEquiv.withLpUniqueProd`. -/
@[simp]
theorem toLinearEquiv_withLpUniqueProd [Unique M₁]
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) :
    (withLpUniqueProd hQ).toLinearEquiv =
      (WithLp.linearEquiv p R (M₁ × M₂)).trans LinearEquiv.uniqueProd :=
  LinearEquiv.ext fun x ↦ by simp [coe_toLinearEquiv]

/-- Deleting a trivial right factor from `WithLp p (M₁ × M₂)` as a quadratic isometric
equivalence. -/
def withLpProdUnique [Unique M₂] (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) :
    Q.IsometryEquiv Q₁ :=
  (withLpProd hQ).trans (QuadraticMap.IsometryEquiv.prodUnique Q₁ Q₂)

/-- `QuadraticMap.IsometryEquiv.withLpProdUnique` extracts the first coordinate. -/
@[simp]
theorem withLpProdUnique_apply [Unique M₂]
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) (x : WithLp p (M₁ × M₂)) :
    withLpProdUnique hQ x = (WithLp.ofLp x).1 := by
  rw [withLpProdUnique, ← coe_toLinearEquiv]
  simp

/-- The inverse of `QuadraticMap.IsometryEquiv.withLpProdUnique` inserts zero in the trivial right
coordinate. -/
@[simp]
theorem withLpProdUnique_symm_apply [Unique M₂]
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) (m : M₁) :
    (withLpProdUnique hQ).symm m = WithLp.toLp p (m, 0) := by
  rw [symm_apply_eq, withLpProdUnique_apply]

/-- The underlying linear equivalence of `QuadraticMap.IsometryEquiv.withLpProdUnique`. -/
@[simp]
theorem toLinearEquiv_withLpProdUnique [Unique M₂]
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) :
    (withLpProdUnique hQ).toLinearEquiv =
      (WithLp.linearEquiv p R (M₁ × M₂)).trans LinearEquiv.prodUnique :=
  LinearEquiv.ext fun x ↦ by simp [coe_toLinearEquiv]

end Binary

section Assoc

variable {p : ℝ≥0∞} {R M₁ M₂ M₃ P : Type*} [CommSemiring R]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommMonoid P]
  [Module R M₁] [Module R M₂] [Module R M₃] [Module R P]
  {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P} {Q₃ : QuadraticMap R M₃ P}
  {Q₁₂ : QuadraticMap R (WithLp p (M₁ × M₂)) P} {Q₂₃ : QuadraticMap R (WithLp p (M₂ × M₃)) P}
  {Q₁₂_₃ : QuadraticMap R (WithLp p (WithLp p (M₁ × M₂) × M₃)) P}
  {Q₁_₂₃ : QuadraticMap R (WithLp p (M₁ × WithLp p (M₂ × M₃))) P}

/-- Reassociating `WithLp p (WithLp p (M₁ × M₂) × M₃)` as `WithLp p (M₁ × WithLp p (M₂ × M₃))` as
an isometric equivalence of quadratic maps. -/
def withLpProdAssoc (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ₁₂_₃ : ∀ x, Q₁₂_₃ x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ₁_₂₃ : ∀ x, Q₁_₂₃ x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2) :
    Q₁₂_₃.IsometryEquiv Q₁_₂₃ :=
  ((withLpProd hQ₁₂_₃).trans
    (((withLpProd hQ₁₂).prod (QuadraticMap.IsometryEquiv.refl Q₃)).trans
      ((QuadraticMap.IsometryEquiv.prodAssoc Q₁ Q₂ Q₃).trans
        ((QuadraticMap.IsometryEquiv.refl Q₁).prod (withLpProd hQ₂₃).symm)))).trans
    (withLpProd hQ₁_₂₃).symm

/-- Application formula for `QuadraticMap.IsometryEquiv.withLpProdAssoc`. -/
@[simp]
theorem withLpProdAssoc_apply (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ₁₂_₃ : ∀ x, Q₁₂_₃ x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ₁_₂₃ : ∀ x, Q₁_₂₃ x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2)
    (x : WithLp p (WithLp p (M₁ × M₂) × M₃)) :
    withLpProdAssoc hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃ x =
      WithLp.toLp p ((WithLp.ofLp (WithLp.ofLp x).1).1,
        WithLp.toLp p ((WithLp.ofLp (WithLp.ofLp x).1).2, (WithLp.ofLp x).2)) := by
  rw [withLpProdAssoc, ← coe_toLinearEquiv]
  simp

/-- Inverse application formula for `QuadraticMap.IsometryEquiv.withLpProdAssoc`. -/
@[simp]
theorem withLpProdAssoc_symm_apply
    (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ₁₂_₃ : ∀ x, Q₁₂_₃ x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ₁_₂₃ : ∀ x, Q₁_₂₃ x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2)
    (y : WithLp p (M₁ × WithLp p (M₂ × M₃))) :
    (withLpProdAssoc hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).symm y =
      WithLp.toLp p (WithLp.toLp p ((WithLp.ofLp y).1, (WithLp.ofLp (WithLp.ofLp y).2).1),
        (WithLp.ofLp (WithLp.ofLp y).2).2) := by
  rw [symm_apply_eq, withLpProdAssoc_apply]

/-- The underlying linear equivalence of `QuadraticMap.IsometryEquiv.withLpProdAssoc`. -/
@[simp]
theorem toLinearEquiv_withLpProdAssoc
    (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ₁₂_₃ : ∀ x, Q₁₂_₃ x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ₁_₂₃ : ∀ x, Q₁_₂₃ x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2) :
    (withLpProdAssoc hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).toLinearEquiv =
      ((WithLp.linearEquiv p R (WithLp p (M₁ × M₂) × M₃)).trans
        (((WithLp.linearEquiv p R (M₁ × M₂)).prodCongr (LinearEquiv.refl R M₃)).trans
          ((LinearEquiv.prodAssoc R M₁ M₂ M₃).trans
            ((LinearEquiv.refl R M₁).prodCongr (WithLp.linearEquiv p R (M₂ × M₃)).symm)))).trans
        (WithLp.linearEquiv p R (M₁ × WithLp p (M₂ × M₃))).symm :=
  LinearEquiv.ext fun x ↦ by simp [coe_toLinearEquiv]

end Assoc

section BaseChange

variable {p : ℝ≥0∞} {R A M₁ M₂ M₃ : Type*} [CommRing R] [Invertible (2 : R)]
  [CommRing A] [Algebra R A]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module R M₁] [Module R M₂] [Module R M₃]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q₃ : QuadraticForm R M₃}
  {Q : QuadraticForm R (WithLp p (M₁ × M₂))}

/-- Deleting a trivial left factor commutes with base change of `WithLp` products. -/
theorem baseChangeProd_trans_uniqueProd [Unique M₁]
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) :
    ((withLpProd hQ).baseChangeProd A).trans
        (uniqueProd (Q₁.baseChange A) (Q₂.baseChange A)) =
      (withLpUniqueProd hQ).baseChange A := by
  apply DFunLike.ext
  intro x
  have hlin :
      (((withLpProd hQ).baseChangeProd A).trans
          (uniqueProd (Q₁.baseChange A) (Q₂.baseChange A))).toLinearEquiv.toLinearMap =
        ((withLpUniqueProd hQ).baseChange A).toLinearEquiv.toLinearMap :=
    TensorProduct.AlgebraTensorModule.ext fun a m ↦ by simp
  exact LinearMap.congr_fun hlin x

/-- Deleting a trivial right factor commutes with base change of `WithLp` products. -/
theorem baseChangeProd_trans_prodUnique [Unique M₂]
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) :
    ((withLpProd hQ).baseChangeProd A).trans
        (prodUnique (Q₁.baseChange A) (Q₂.baseChange A)) =
      (withLpProdUnique hQ).baseChange A := by
  apply DFunLike.ext
  intro x
  have hlin :
      (((withLpProd hQ).baseChangeProd A).trans
          (prodUnique (Q₁.baseChange A) (Q₂.baseChange A))).toLinearEquiv.toLinearMap =
        ((withLpProdUnique hQ).baseChange A).toLinearEquiv.toLinearMap :=
    TensorProduct.AlgebraTensorModule.ext fun a m ↦ by simp
  exact LinearMap.congr_fun hlin x

/-- Swapping factors commutes with base change of `WithLp` products. -/
theorem baseChange_withLpProdComm_trans_baseChangeProd
    {Q' : QuadraticForm R (WithLp p (M₂ × M₁))}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ' : ∀ y, Q' y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2) :
    ((withLpProdComm hQ hQ').baseChange A).trans ((withLpProd hQ').baseChangeProd A) =
      ((withLpProd hQ).baseChangeProd A).trans (prodComm (Q₁.baseChange A) (Q₂.baseChange A)) := by
  apply DFunLike.ext
  intro x
  have hlin :
      (((withLpProdComm hQ hQ').baseChange A).trans
          ((withLpProd hQ').baseChangeProd A)).toLinearEquiv.toLinearMap =
        (((withLpProd hQ).baseChangeProd A).trans
          (prodComm (Q₁.baseChange A) (Q₂.baseChange A))).toLinearEquiv.toLinearMap :=
    TensorProduct.AlgebraTensorModule.ext fun a m ↦ by simp
  exact LinearMap.congr_fun hlin x

/-- Reassociating iterated `WithLp` products commutes with base change. -/
theorem baseChangeProd_trans_prodAssoc
    {Q₁₂ : QuadraticForm R (WithLp p (M₁ × M₂))} {Q₂₃ : QuadraticForm R (WithLp p (M₂ × M₃))}
    {Q₁₂_₃ : QuadraticForm R (WithLp p (WithLp p (M₁ × M₂) × M₃))}
    {Q₁_₂₃ : QuadraticForm R (WithLp p (M₁ × WithLp p (M₂ × M₃)))}
    (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ₁₂_₃ : ∀ x, Q₁₂_₃ x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ₁_₂₃ : ∀ x, Q₁_₂₃ x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2) :
    (((withLpProd hQ₁₂_₃).baseChangeProd A).trans
        (((withLpProd hQ₁₂).baseChangeProd A).prod (refl (Q₃.baseChange A)))).trans
        (prodAssoc (Q₁.baseChange A) (Q₂.baseChange A) (Q₃.baseChange A)) =
      ((withLpProdAssoc hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).baseChange A).trans
        (((withLpProd hQ₁_₂₃).baseChangeProd A).trans
          ((refl (Q₁.baseChange A)).prod ((withLpProd hQ₂₃).baseChangeProd A))) := by
  apply DFunLike.ext
  intro x
  have hlin :
      (((((withLpProd hQ₁₂_₃).baseChangeProd A).trans
          (((withLpProd hQ₁₂).baseChangeProd A).prod (refl (Q₃.baseChange A)))).trans
          (prodAssoc (Q₁.baseChange A) (Q₂.baseChange A)
            (Q₃.baseChange A))).toLinearEquiv).toLinearMap =
        ((((withLpProdAssoc hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).baseChange A).trans
          (((withLpProd hQ₁_₂₃).baseChangeProd A).trans
            ((refl (Q₁.baseChange A)).prod
              ((withLpProd hQ₂₃).baseChangeProd A)))).toLinearEquiv).toLinearMap :=
    TensorProduct.AlgebraTensorModule.ext fun a m ↦ by simp
  exact LinearMap.congr_fun hlin x

end BaseChange

section LinearIsometryEquiv

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {R M₁ M₂ M₃ P : Type*} [CommSemiring R]
  [SeminormedAddCommGroup M₁] [SeminormedAddCommGroup M₂] [SeminormedAddCommGroup M₃]
  [AddCommMonoid P] [Module R M₁] [Module R M₂] [Module R M₃] [Module R P]
  {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P} {Q₃ : QuadraticMap R M₃ P}
  {Q : QuadraticMap R (WithLp p (M₁ × M₂)) P} {Q' : QuadraticMap R (WithLp p (M₂ × M₁)) P}

/-- The underlying linear equivalence of `QuadraticMap.IsometryEquiv.withLpProdComm` is that of
`LinearIsometryEquiv.withLpProdComm`. -/
theorem toLinearEquiv_withLpProdComm_eq_linearIsometryEquiv
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ' : ∀ y, Q' y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2) :
    (withLpProdComm hQ hQ').toLinearEquiv =
      (LinearIsometryEquiv.withLpProdComm p R M₁ M₂).toLinearEquiv :=
  LinearEquiv.ext fun x ↦ by
    simp only [toLinearEquiv_withLpProdComm, LinearEquiv.coe_withLpCongr, WithLp.map,
      LinearEquiv.prodComm_apply, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.withLpProdComm_apply, WithLp.toLp.injEq]
    ext <;> simp

/-- The underlying linear equivalence of `QuadraticMap.IsometryEquiv.withLpUniqueProd` is that of
`LinearIsometryEquiv.withLpUniqueProd`. -/
theorem toLinearEquiv_withLpUniqueProd_eq_linearIsometryEquiv [Unique M₁]
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) :
    (withLpUniqueProd hQ).toLinearEquiv =
      (LinearIsometryEquiv.withLpUniqueProd p R M₁ M₂).toLinearEquiv :=
  LinearEquiv.ext fun x ↦ by simp

/-- The underlying linear equivalence of `QuadraticMap.IsometryEquiv.withLpProdUnique` is that of
`LinearIsometryEquiv.withLpProdUnique`. -/
theorem toLinearEquiv_withLpProdUnique_eq_linearIsometryEquiv [Unique M₂]
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) :
    (withLpProdUnique hQ).toLinearEquiv =
      (LinearIsometryEquiv.withLpProdUnique p R M₁ M₂).toLinearEquiv :=
  LinearEquiv.ext fun x ↦ by simp

/-- The underlying linear equivalence of `QuadraticMap.IsometryEquiv.withLpProdAssoc` is that of
`LinearIsometryEquiv.withLpProdAssoc`. -/
theorem toLinearEquiv_withLpProdAssoc_eq_linearIsometryEquiv
    {Q₁₂ : QuadraticMap R (WithLp p (M₁ × M₂)) P} {Q₂₃ : QuadraticMap R (WithLp p (M₂ × M₃)) P}
    {Q₁₂_₃ : QuadraticMap R (WithLp p (WithLp p (M₁ × M₂) × M₃)) P}
    {Q₁_₂₃ : QuadraticMap R (WithLp p (M₁ × WithLp p (M₂ × M₃))) P}
    (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ₁₂_₃ : ∀ x, Q₁₂_₃ x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ₁_₂₃ : ∀ x, Q₁_₂₃ x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2) :
    (withLpProdAssoc hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).toLinearEquiv =
      (LinearIsometryEquiv.withLpProdAssoc p R M₁ M₂ M₃).toLinearEquiv :=
  LinearEquiv.ext fun x ↦ by simp

end LinearIsometryEquiv

end QuadraticMap.IsometryEquiv

namespace QuadraticMap

/-- The orthogonal sum of negative norm-squared quadratic forms on `U` and `V` is again negative
norm-squared on `WithLp 2 (U × V)`. -/
theorem apply_eq_neg_norm_sq_of_withLp_prod {U V : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {Q₁ : QuadraticForm ℝ U} {Q₂ : QuadraticForm ℝ V}
    (Q : QuadraticForm ℝ (WithLp 2 (U × V)))
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₁ : ∀ u, Q₁ u = -‖u‖ ^ 2) (hQ₂ : ∀ v, Q₂ v = -‖v‖ ^ 2) :
    ∀ x, Q x = -‖x‖ ^ 2 := fun x ↦ by
  rw [hQ x, hQ₁, hQ₂, WithLp.prod_norm_sq_eq_of_L2, WithLp.ofLp_fst, WithLp.ofLp_snd]
  ring

end QuadraticMap
