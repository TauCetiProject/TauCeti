/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import TauCeti.Analysis.Normed.Lp.WithLp
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Structural quadratic isometries on `WithLp` products

When `Q` on `WithLp p (M₁ × M₂)` decomposes as `Q x = Q₁ x.1 + Q₂ x.2`, `WithLp.linearEquiv`
identifies `Q` with `Q₁.prod Q₂`, and the structural equivalences of binary `WithLp` products
(swap, associator, and projection away from a subsingleton summand) are quadratic isometries. No
metric assumption is needed for the isometries or for their scalar-extension compatibility laws
with `QuadraticMap.IsometryEquiv.uniqueProd`, `prodUnique`, `prodComm`, and `prodAssoc`. For
`p = 2`, the `L²` norm formula gives `Q x = -‖x‖ ^ 2` from the factors' formulas.

## Main definitions

* `QuadraticMap.IsometryEquiv.withLpProd`: `Q.IsometryEquiv (Q₁.prod Q₂)` via `WithLp.linearEquiv`.
* `QuadraticMap.IsometryEquiv.withLpProdComm`: `Q₁₂.IsometryEquiv Q₂₁` swapping `M₁` and `M₂`.
* `QuadraticMap.IsometryEquiv.withLpProdAssoc`: `Q_L.IsometryEquiv Q_R` reassociating triple sums.
* `QuadraticMap.IsometryEquiv.withLpSubsingletonProd` and
  `QuadraticMap.IsometryEquiv.withLpProdSubsingleton`: deleting a subsingleton summand.

## Main results

* `QuadraticMap.IsometryEquiv.withLpSubsingletonProd_toIsometry_baseChange`,
  `QuadraticMap.IsometryEquiv.withLpProdSubsingleton_toIsometry_baseChange`,
  `QuadraticMap.IsometryEquiv.withLpProdComm_toIsometry_baseChange`, and
  `QuadraticMap.IsometryEquiv.withLpProdAssoc_toIsometry_baseChange`: compatibility of the
  structural `WithLp` isometries with `baseChange` and `baseChangeProd`.
* `QuadraticForm.withLpProd_eq_neg_norm_sq` and
  `QuadraticForm.eq_neg_norm_sq_of_subsingleton`: `L²` negative-norm-squared formulas.
-/

public section

open scoped ENNReal

namespace QuadraticMap.IsometryEquiv

section Algebraic

variable {p : ℝ≥0∞} {R M₁ M₂ M₃ P : Type*} [CommSemiring R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
  [AddCommMonoid P] [Module R P]
  {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P} {Q₃ : QuadraticMap R M₃ P}

section Prod

variable {Q : QuadraticMap R (WithLp p (M₁ × M₂)) P}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)

/-- `WithLp.linearEquiv p R (M₁ × M₂)` as a quadratic isometry `Q.IsometryEquiv (Q₁.prod Q₂)` when
`Q x = Q₁ x.1 + Q₂ x.2`. -/
def withLpProd : Q.IsometryEquiv (Q₁.prod Q₂) where
  toLinearEquiv := WithLp.linearEquiv p R (M₁ × M₂)
  map_app' x := by rw [QuadraticMap.prod_apply, hQ x]; rfl

/-- `withLpProd` unwraps `WithLp.ofLp`. -/
@[simp]
theorem withLpProd_apply (x : WithLp p (M₁ × M₂)) : withLpProd hQ x = WithLp.ofLp x := (rfl)

/-- The inverse of `withLpProd` wraps a pair with `WithLp.toLp p`. -/
@[simp]
theorem withLpProd_symm_apply (x : M₁ × M₂) : (withLpProd hQ).symm x = WithLp.toLp p x := (rfl)

/-- Projecting `WithLp p (M₁ × M₂)` onto `M₂` is a quadratic isometry when `M₁` is a subsingleton.
-/
def withLpSubsingletonProd (hM₁ : Subsingleton M₁ := by infer_instance) : Q.IsometryEquiv Q₂ :=
  letI : Unique M₁ := @uniqueOfSubsingleton M₁ hM₁ 0
  (withLpProd hQ).trans (uniqueProd Q₁ Q₂)

/-- `withLpSubsingletonProd` projects onto the second coordinate. -/
@[simp]
theorem withLpSubsingletonProd_apply (hM₁ : Subsingleton M₁) (x : WithLp p (M₁ × M₂)) :
    withLpSubsingletonProd hQ hM₁ x = (WithLp.ofLp x).2 := by
  let : Unique M₁ := @uniqueOfSubsingleton M₁ hM₁ 0
  exact IsometryEquiv.uniqueProd_apply Q₁ Q₂ (withLpProd hQ x)

/-- The inverse of `withLpSubsingletonProd` embeds `m₂` as `(0, m₂)`. -/
@[simp]
theorem withLpSubsingletonProd_symm_apply (hM₁ : Subsingleton M₁) (m₂ : M₂) :
    (withLpSubsingletonProd hQ hM₁).symm m₂ = WithLp.toLp p (0, m₂) := by
  let : Unique M₁ := @uniqueOfSubsingleton M₁ hM₁ 0
  exact (withLpSubsingletonProd hQ hM₁).symm_apply_eq.mpr
    (withLpSubsingletonProd_apply hQ hM₁ (WithLp.toLp p (0, m₂))).symm

/-- Projecting `WithLp p (M₁ × M₂)` onto `M₁` is a quadratic isometry when `M₂` is a subsingleton.
-/
def withLpProdSubsingleton (hM₂ : Subsingleton M₂ := by infer_instance) : Q.IsometryEquiv Q₁ :=
  letI : Unique M₂ := @uniqueOfSubsingleton M₂ hM₂ 0
  (withLpProd hQ).trans (prodUnique Q₁ Q₂)

/-- `withLpProdSubsingleton` projects onto the first coordinate. -/
@[simp]
theorem withLpProdSubsingleton_apply (hM₂ : Subsingleton M₂) (x : WithLp p (M₁ × M₂)) :
    withLpProdSubsingleton hQ hM₂ x = (WithLp.ofLp x).1 := by
  let : Unique M₂ := @uniqueOfSubsingleton M₂ hM₂ 0
  exact IsometryEquiv.prodUnique_apply Q₁ Q₂ (withLpProd hQ x)

/-- The inverse of `withLpProdSubsingleton` embeds `m₁` as `(m₁, 0)`. -/
@[simp]
theorem withLpProdSubsingleton_symm_apply (hM₂ : Subsingleton M₂) (m₁ : M₁) :
    (withLpProdSubsingleton hQ hM₂).symm m₁ = WithLp.toLp p (m₁, 0) := by
  let : Unique M₂ := @uniqueOfSubsingleton M₂ hM₂ 0
  exact (withLpProdSubsingleton hQ hM₂).symm_apply_eq.mpr
    (withLpProdSubsingleton_apply hQ hM₂ (WithLp.toLp p (m₁, 0))).symm

end Prod

section Comm

variable {Q₁₂ : QuadraticMap R (WithLp p (M₁ × M₂)) P}
  {Q₂₁ : QuadraticMap R (WithLp p (M₂ × M₁)) P}
  (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ₂₁ : ∀ y, Q₂₁ y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2)

/-- Swapping the factors of `WithLp p (M₁ × M₂)` is a quadratic isometry between orthogonal-sum
forms. -/
def withLpProdComm : Q₁₂.IsometryEquiv Q₂₁ where
  toLinearEquiv := (LinearEquiv.prodComm R M₁ M₂).withLpCongr p
  map_app' x := by rw [hQ₂₁, hQ₁₂]; exact add_comm _ _

/-- `withLpProdComm` swaps `(m₁, m₂)` to `(m₂, m₁)`. -/
@[simp]
theorem withLpProdComm_apply (x : WithLp p (M₁ × M₂)) :
    withLpProdComm hQ₁₂ hQ₂₁ x = WithLp.toLp p ((WithLp.ofLp x).2, (WithLp.ofLp x).1) := (rfl)

/-- The inverse of `withLpProdComm` swaps `(m₂, m₁)` to `(m₁, m₂)`. -/
@[simp]
theorem withLpProdComm_symm_apply (y : WithLp p (M₂ × M₁)) :
    (withLpProdComm hQ₁₂ hQ₂₁).symm y = WithLp.toLp p ((WithLp.ofLp y).2, (WithLp.ofLp y).1) :=
  (rfl)

end Comm

section Assoc

variable {Q₁₂ : QuadraticMap R (WithLp p (M₁ × M₂)) P}
  {Q₂₃ : QuadraticMap R (WithLp p (M₂ × M₃)) P}
  {Q_L : QuadraticMap R (WithLp p (WithLp p (M₁ × M₂) × M₃)) P}
  {Q_R : QuadraticMap R (WithLp p (M₁ × WithLp p (M₂ × M₃))) P}
  (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ_L : ∀ x, Q_L x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ_R : ∀ x, Q_R x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2)

/-- `LinearEquiv.withLpProdAssoc` as a quadratic isometry between left- and right-associated
`WithLp` orthogonal sums. -/
def withLpProdAssoc : Q_L.IsometryEquiv Q_R where
  toLinearEquiv := LinearEquiv.withLpProdAssoc p R M₁ M₂ M₃
  map_app' x := by simp [LinearEquiv.withLpProdAssoc_apply, hQ_R, hQ₂₃, hQ_L, hQ₁₂, add_assoc]

/-- `withLpProdAssoc` reassociates `((m₁, m₂), m₃)` to `(m₁, (m₂, m₃))`. -/
@[simp]
theorem withLpProdAssoc_apply (x : WithLp p (WithLp p (M₁ × M₂) × M₃)) :
    withLpProdAssoc hQ₁₂ hQ₂₃ hQ_L hQ_R x =
      WithLp.toLp p ((WithLp.ofLp (WithLp.ofLp x).1).1,
        WithLp.toLp p ((WithLp.ofLp (WithLp.ofLp x).1).2, (WithLp.ofLp x).2)) :=
  LinearEquiv.withLpProdAssoc_apply x

/-- The inverse of `withLpProdAssoc` reassociates `(m₁, (m₂, m₃))` to `((m₁, m₂), m₃)`. -/
@[simp]
theorem withLpProdAssoc_symm_apply (x : WithLp p (M₁ × WithLp p (M₂ × M₃))) :
    (withLpProdAssoc hQ₁₂ hQ₂₃ hQ_L hQ_R).symm x =
      WithLp.toLp p (WithLp.toLp p ((WithLp.ofLp x).1, (WithLp.ofLp (WithLp.ofLp x).2).1),
        (WithLp.ofLp (WithLp.ofLp x).2).2) :=
  LinearEquiv.withLpProdAssoc_symm_apply x

end Assoc

end Algebraic

section BaseChange

open scoped TensorProduct

variable {p : ℝ≥0∞} {R : Type*} (A : Type*) [CommRing R] [Invertible (2 : R)]
  [CommRing A] [Algebra R A]
  {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₃] [Module R M₃]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q₃ : QuadraticForm R M₃}

/-- Scalar extension of `withLpSubsingletonProd` commutes with `baseChangeProd` and `uniqueProd`. -/
theorem withLpSubsingletonProd_toIsometry_baseChange
    {Q : QuadraticForm R (WithLp p (M₁ × M₂))}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hM₁ : Subsingleton M₁) [Unique (A ⊗[R] M₁)] :
    (uniqueProd (Q₁.baseChange A) (Q₂.baseChange A)).toIsometry.comp
        ((withLpProd hQ).baseChangeProd A).toIsometry =
      (withLpSubsingletonProd hQ hM₁).toIsometry.baseChange A :=
  QuadraticMap.Isometry.ext fun y ↦
    DFunLike.congr_fun (TensorProduct.AlgebraTensorModule.ext fun c x ↦ by
      rcases x with ⟨⟨v, w⟩⟩
      simp [baseChangeProd_tmul]) y

/-- Scalar extension of `withLpProdSubsingleton` commutes with `baseChangeProd` and `prodUnique`. -/
theorem withLpProdSubsingleton_toIsometry_baseChange
    {Q : QuadraticForm R (WithLp p (M₁ × M₂))}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hM₂ : Subsingleton M₂) [Unique (A ⊗[R] M₂)] :
    (prodUnique (Q₁.baseChange A) (Q₂.baseChange A)).toIsometry.comp
        ((withLpProd hQ).baseChangeProd A).toIsometry =
      (withLpProdSubsingleton hQ hM₂).toIsometry.baseChange A :=
  QuadraticMap.Isometry.ext fun y ↦
    DFunLike.congr_fun (TensorProduct.AlgebraTensorModule.ext fun c x ↦ by
      rcases x with ⟨⟨v, w⟩⟩
      simp [baseChangeProd_tmul]) y

/-- Scalar extension of `withLpProdComm` commutes with `baseChangeProd` and `prodComm`. -/
theorem withLpProdComm_toIsometry_baseChange
    {Q₁₂ : QuadraticForm R (WithLp p (M₁ × M₂))} {Q₂₁ : QuadraticForm R (WithLp p (M₂ × M₁))}
    (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₁ : ∀ y, Q₂₁ y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2) :
    ((withLpProd hQ₂₁).baseChangeProd A).toIsometry.comp
        ((withLpProdComm hQ₁₂ hQ₂₁).toIsometry.baseChange A) =
      (prodComm (Q₁.baseChange A) (Q₂.baseChange A)).toIsometry.comp
        ((withLpProd hQ₁₂).baseChangeProd A).toIsometry :=
  QuadraticMap.Isometry.ext fun y ↦
    DFunLike.congr_fun (TensorProduct.AlgebraTensorModule.ext fun c x ↦ by
      rcases x with ⟨⟨v, w⟩⟩
      simp [baseChangeProd_tmul]) y

/-- Scalar extension of `withLpProdAssoc` commutes with `baseChangeProd` and `prodAssoc`. -/
theorem withLpProdAssoc_toIsometry_baseChange
    {Q₁₂ : QuadraticForm R (WithLp p (M₁ × M₂))}
    {Q₂₃ : QuadraticForm R (WithLp p (M₂ × M₃))}
    {Q_L : QuadraticForm R (WithLp p (WithLp p (M₁ × M₂) × M₃))}
    {Q_R : QuadraticForm R (WithLp p (M₁ × WithLp p (M₂ × M₃)))}
    (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ_L : ∀ x, Q_L x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ_R : ∀ x, Q_R x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2) :
    (prodAssoc (Q₁.baseChange A) (Q₂.baseChange A) (Q₃.baseChange A)).toIsometry.comp
        ((((withLpProd hQ₁₂).baseChangeProd A).toIsometry.prodMap
            (QuadraticMap.Isometry.id (Q₃.baseChange A))).comp
          ((withLpProd hQ_L).baseChangeProd A).toIsometry) =
      (((QuadraticMap.Isometry.id (Q₁.baseChange A)).prodMap
            ((withLpProd hQ₂₃).baseChangeProd A).toIsometry).comp
          ((withLpProd hQ_R).baseChangeProd A).toIsometry).comp
        ((withLpProdAssoc hQ₁₂ hQ₂₃ hQ_L hQ_R).toIsometry.baseChange A) :=
  QuadraticMap.Isometry.ext fun y ↦
    DFunLike.congr_fun (TensorProduct.AlgebraTensorModule.ext fun c x ↦ by
      rcases x with ⟨⟨⟨⟨u, v⟩⟩, w⟩⟩
      simp [baseChangeProd_tmul]) y

end BaseChange

end QuadraticMap.IsometryEquiv

namespace QuadraticForm

section L2

/-- If `Q` on `WithLp 2 (V × W)` decomposes as `Q (v, w) = Q₁ v + Q₂ w` with `Q₁ v = -‖v‖ ^ 2`
and `Q₂ w = -‖w‖ ^ 2`, then `Q x = -‖x‖ ^ 2`. -/
theorem withLpProd_eq_neg_norm_sq
    {V W : Type*} [SeminormedAddCommGroup V] [Module ℝ V]
    [SeminormedAddCommGroup W] [Module ℝ W]
    {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (x : WithLp 2 (V × W)) : Q x = -‖x‖ ^ 2 := by
  rw [hQ x, hQ₁, hQ₂, WithLp.prod_norm_sq_eq_of_L2]
  dsimp only [WithLp.fst, WithLp.snd]
  ring

/-- On a subsingleton normed space, every real quadratic form satisfies `Q v = -‖v‖ ^ 2`. -/
theorem eq_neg_norm_sq_of_subsingleton
    {V : Type*} [SeminormedAddCommGroup V] [Module ℝ V] [Subsingleton V]
    (Q : QuadraticForm ℝ V) (v : V) :
    Q v = -‖v‖ ^ 2 := by
  rw [Subsingleton.elim v 0, map_zero, norm_zero]
  ring

end L2

end QuadraticForm

