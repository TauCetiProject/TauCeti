/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.Analysis.Normed.Lp.WithLp

/-!
# Structural quadratic isometries on `WithLp` products

When a quadratic map `Q` on `WithLp p (M₁ × M₂)` decomposes as the orthogonal sum
`Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2`, `WithLp.linearEquiv` identifies `Q` with
`Q₁.prod Q₂`, and the structural equivalences of binary `WithLp` products — exchange of factors,
reassociation of triple products, and projection away from a subsingleton summand — are quadratic
isometries. No norm or inner-product structure is needed for the quadratic isometries themselves;
when the summands are seminormed groups and `1 ≤ p`, each structural equivalence also preserves the
`Lᵖ` norm.

## Main definitions

* `QuadraticMap.IsometryEquiv.withLpProd`: `Q.IsometryEquiv (Q₁.prod Q₂)` via `WithLp.linearEquiv`.
* `QuadraticMap.IsometryEquiv.withLpProdComm`: `Q₁₂.IsometryEquiv Q₂₁` swapping `M₁` and `M₂`.
* `QuadraticMap.IsometryEquiv.withLpProdAssoc`: `Q_L.IsometryEquiv Q_R` reassociating
  `(M₁ ⊕ M₂) ⊕ M₃` to `M₁ ⊕ (M₂ ⊕ M₃)`.
* `QuadraticMap.IsometryEquiv.withLpSubsingletonProd` and
  `QuadraticMap.IsometryEquiv.withLpProdSubsingleton`: deleting a subsingleton left or right
  summand.
-/

public section

open scoped ENNReal

namespace QuadraticMap.IsometryEquiv

section Algebraic

variable {p : ℝ≥0∞} {R M₁ M₂ M₃ P : Type*} [CommSemiring R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
  [AddCommMonoid P] [Module R P]
  {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P} {Q₃ : QuadraticMap R M₃ P}

/-- `WithLp.linearEquiv p R (M₁ × M₂)` as a quadratic isometry `Q.IsometryEquiv (Q₁.prod Q₂)` when
`Q x = Q₁ x.1 + Q₂ x.2`. -/
def withLpProd {Q : QuadraticMap R (WithLp p (M₁ × M₂)) P}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) :
    Q.IsometryEquiv (Q₁.prod Q₂) where
  toLinearEquiv := WithLp.linearEquiv p R (M₁ × M₂)
  map_app' x := by
    rw [QuadraticMap.prod_apply, hQ x]
    rfl

/-- `withLpProd` unwraps `WithLp.ofLp`. -/
@[simp]
theorem withLpProd_apply {Q : QuadraticMap R (WithLp p (M₁ × M₂)) P}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) (x : WithLp p (M₁ × M₂)) :
    withLpProd hQ x = WithLp.ofLp x :=
  (rfl)

/-- The inverse of `withLpProd` wraps a pair with `WithLp.toLp p`. -/
@[simp]
theorem withLpProd_symm_apply {Q : QuadraticMap R (WithLp p (M₁ × M₂)) P}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) (x : M₁ × M₂) :
    (withLpProd hQ).symm x = WithLp.toLp p x :=
  (rfl)

/-- Swapping the factors of `WithLp p (M₁ × M₂)` is a quadratic isometry between orthogonal-sum
forms. -/
def withLpProdComm {Q₁₂ : QuadraticMap R (WithLp p (M₁ × M₂)) P}
    {Q₂₁ : QuadraticMap R (WithLp p (M₂ × M₁)) P}
    (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₁ : ∀ y, Q₂₁ y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2) :
    Q₁₂.IsometryEquiv Q₂₁ where
  toLinearEquiv := (LinearEquiv.prodComm R M₁ M₂).withLpCongr p
  map_app' x := by
    rw [hQ₂₁, hQ₁₂]
    exact add_comm _ _

/-- `withLpProdComm` swaps `(m₁, m₂)` to `(m₂, m₁)`. -/
@[simp]
theorem withLpProdComm_apply {Q₁₂ : QuadraticMap R (WithLp p (M₁ × M₂)) P}
    {Q₂₁ : QuadraticMap R (WithLp p (M₂ × M₁)) P}
    (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₁ : ∀ y, Q₂₁ y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2)
    (x : WithLp p (M₁ × M₂)) :
    withLpProdComm hQ₁₂ hQ₂₁ x = WithLp.toLp p ((WithLp.ofLp x).2, (WithLp.ofLp x).1) :=
  (rfl)

/-- The inverse of `withLpProdComm` swaps `(m₂, m₁)` to `(m₁, m₂)`. -/
@[simp]
theorem withLpProdComm_symm_apply {Q₁₂ : QuadraticMap R (WithLp p (M₁ × M₂)) P}
    {Q₂₁ : QuadraticMap R (WithLp p (M₂ × M₁)) P}
    (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₁ : ∀ y, Q₂₁ y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2)
    (y : WithLp p (M₂ × M₁)) :
    (withLpProdComm hQ₁₂ hQ₂₁).symm y = WithLp.toLp p ((WithLp.ofLp y).2, (WithLp.ofLp y).1) :=
  (rfl)

/-- `LinearEquiv.withLpProdAssoc` as a quadratic isometry between left- and right-associated
`WithLp` orthogonal sums. -/
def withLpProdAssoc {Q₁₂ : QuadraticMap R (WithLp p (M₁ × M₂)) P}
    {Q₂₃ : QuadraticMap R (WithLp p (M₂ × M₃)) P}
    {Q_L : QuadraticMap R (WithLp p (WithLp p (M₁ × M₂) × M₃)) P}
    {Q_R : QuadraticMap R (WithLp p (M₁ × WithLp p (M₂ × M₃))) P}
    (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ_L : ∀ x, Q_L x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ_R : ∀ x, Q_R x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2) :
    Q_L.IsometryEquiv Q_R where
  toLinearEquiv := LinearEquiv.withLpProdAssoc p R M₁ M₂ M₃
  map_app' x := by
    simp [LinearEquiv.withLpProdAssoc_apply, hQ_R, hQ₂₃, hQ_L, hQ₁₂, add_assoc]

/-- `withLpProdAssoc` reassociates `((m₁, m₂), m₃)` to `(m₁, (m₂, m₃))`. -/
@[simp]
theorem withLpProdAssoc_apply {Q₁₂ : QuadraticMap R (WithLp p (M₁ × M₂)) P}
    {Q₂₃ : QuadraticMap R (WithLp p (M₂ × M₃)) P}
    {Q_L : QuadraticMap R (WithLp p (WithLp p (M₁ × M₂) × M₃)) P}
    {Q_R : QuadraticMap R (WithLp p (M₁ × WithLp p (M₂ × M₃))) P}
    (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ_L : ∀ x, Q_L x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ_R : ∀ x, Q_R x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2)
    (x : WithLp p (WithLp p (M₁ × M₂) × M₃)) :
    withLpProdAssoc hQ₁₂ hQ₂₃ hQ_L hQ_R x =
      WithLp.toLp p ((WithLp.ofLp (WithLp.ofLp x).1).1,
        WithLp.toLp p ((WithLp.ofLp (WithLp.ofLp x).1).2, (WithLp.ofLp x).2)) :=
  LinearEquiv.withLpProdAssoc_apply x

/-- The inverse of `withLpProdAssoc` reassociates `(m₁, (m₂, m₃))` to `((m₁, m₂), m₃)`. -/
@[simp]
theorem withLpProdAssoc_symm_apply {Q₁₂ : QuadraticMap R (WithLp p (M₁ × M₂)) P}
    {Q₂₃ : QuadraticMap R (WithLp p (M₂ × M₃)) P}
    {Q_L : QuadraticMap R (WithLp p (WithLp p (M₁ × M₂) × M₃)) P}
    {Q_R : QuadraticMap R (WithLp p (M₁ × WithLp p (M₂ × M₃))) P}
    (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ_L : ∀ x, Q_L x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ_R : ∀ x, Q_R x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2)
    (x : WithLp p (M₁ × WithLp p (M₂ × M₃))) :
    (withLpProdAssoc hQ₁₂ hQ₂₃ hQ_L hQ_R).symm x =
      WithLp.toLp p (WithLp.toLp p ((WithLp.ofLp x).1, (WithLp.ofLp (WithLp.ofLp x).2).1),
        (WithLp.ofLp (WithLp.ofLp x).2).2) :=
  LinearEquiv.withLpProdAssoc_symm_apply x

/-- Projecting `WithLp p (M₁ × M₂)` onto `M₂` is a quadratic isometry when `M₁` is a subsingleton.
-/
def withLpSubsingletonProd {Q : QuadraticMap R (WithLp p (M₁ × M₂)) P}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hM₁ : Subsingleton M₁ := by infer_instance) :
    Q.IsometryEquiv Q₂ where
  toFun x := (WithLp.ofLp x).2
  invFun m₂ := WithLp.toLp p (0, m₂)
  left_inv x := WithLp.ofLp_injective p (Prod.ext (hM₁.elim _ _) rfl)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_app' x := by rw [hQ x, hM₁.elim (WithLp.ofLp x).1 0, map_zero, zero_add]

/-- `withLpSubsingletonProd` projects onto the second coordinate. -/
@[simp]
theorem withLpSubsingletonProd_apply {Q : QuadraticMap R (WithLp p (M₁ × M₂)) P}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) (hM₁ : Subsingleton M₁)
    (x : WithLp p (M₁ × M₂)) :
    withLpSubsingletonProd hQ hM₁ x = (WithLp.ofLp x).2 :=
  (rfl)

/-- The inverse of `withLpSubsingletonProd` embeds `m₂` as `(0, m₂)`. -/
@[simp]
theorem withLpSubsingletonProd_symm_apply {Q : QuadraticMap R (WithLp p (M₁ × M₂)) P}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) (hM₁ : Subsingleton M₁)
    (m₂ : M₂) :
    (withLpSubsingletonProd hQ hM₁).symm m₂ = WithLp.toLp p (0, m₂) :=
  (rfl)

/-- Projecting `WithLp p (M₁ × M₂)` onto `M₁` is a quadratic isometry when `M₂` is a subsingleton.
-/
def withLpProdSubsingleton {Q : QuadraticMap R (WithLp p (M₁ × M₂)) P}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hM₂ : Subsingleton M₂ := by infer_instance) :
    Q.IsometryEquiv Q₁ where
  toFun x := (WithLp.ofLp x).1
  invFun m₁ := WithLp.toLp p (m₁, 0)
  left_inv x := WithLp.ofLp_injective p (Prod.ext rfl (hM₂.elim _ _))
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_app' x := by rw [hQ x, hM₂.elim (WithLp.ofLp x).2 0, map_zero, add_zero]

/-- `withLpProdSubsingleton` projects onto the first coordinate. -/
@[simp]
theorem withLpProdSubsingleton_apply {Q : QuadraticMap R (WithLp p (M₁ × M₂)) P}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) (hM₂ : Subsingleton M₂)
    (x : WithLp p (M₁ × M₂)) :
    withLpProdSubsingleton hQ hM₂ x = (WithLp.ofLp x).1 :=
  (rfl)

/-- The inverse of `withLpProdSubsingleton` embeds `m₁` as `(m₁, 0)`. -/
@[simp]
theorem withLpProdSubsingleton_symm_apply {Q : QuadraticMap R (WithLp p (M₁ × M₂)) P}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) (hM₂ : Subsingleton M₂)
    (m₁ : M₁) :
    (withLpProdSubsingleton hQ hM₂).symm m₁ = WithLp.toLp p (m₁, 0) :=
  (rfl)

end Algebraic

section Norm

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {R M₁ M₂ M₃ P : Type*} [CommSemiring R]
  [SeminormedAddCommGroup M₁] [Module R M₁]
  [SeminormedAddCommGroup M₂] [Module R M₂]
  [SeminormedAddCommGroup M₃] [Module R M₃]
  [AddCommMonoid P] [Module R P]
  {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P} {Q₃ : QuadraticMap R M₃ P}

/-- `withLpProdComm` preserves the `Lᵖ` seminorm. -/
theorem norm_withLpProdComm {Q₁₂ : QuadraticMap R (WithLp p (M₁ × M₂)) P}
    {Q₂₁ : QuadraticMap R (WithLp p (M₂ × M₁)) P}
    (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₁ : ∀ y, Q₂₁ y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2)
    (x : WithLp p (M₁ × M₂)) :
    ‖withLpProdComm hQ₁₂ hQ₂₁ x‖ = ‖x‖ :=
  (LinearIsometryEquiv.withLpProdComm p R M₁ M₂).norm_map x

/-- `withLpProdAssoc` preserves the `Lᵖ` seminorm. -/
theorem norm_withLpProdAssoc {Q₁₂ : QuadraticMap R (WithLp p (M₁ × M₂)) P}
    {Q₂₃ : QuadraticMap R (WithLp p (M₂ × M₃)) P}
    {Q_L : QuadraticMap R (WithLp p (WithLp p (M₁ × M₂) × M₃)) P}
    {Q_R : QuadraticMap R (WithLp p (M₁ × WithLp p (M₂ × M₃))) P}
    (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ_L : ∀ x, Q_L x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ_R : ∀ x, Q_R x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2)
    (x : WithLp p (WithLp p (M₁ × M₂) × M₃)) :
    ‖withLpProdAssoc hQ₁₂ hQ₂₃ hQ_L hQ_R x‖ = ‖x‖ := by
  rw [← (LinearIsometryEquiv.withLpProdAssoc p R M₁ M₂ M₃).norm_map x]
  simp

/-- `withLpSubsingletonProd` preserves the `Lᵖ` seminorm. -/
theorem norm_withLpSubsingletonProd {Q : QuadraticMap R (WithLp p (M₁ × M₂)) P}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) (hM₁ : Subsingleton M₁)
    (x : WithLp p (M₁ × M₂)) :
    ‖withLpSubsingletonProd hQ hM₁ x‖ = ‖x‖ := by
  let : Unique M₁ := uniqueOfSubsingleton (0 : M₁)
  exact (LinearIsometryEquiv.withLpUniqueProd p R M₁ M₂).norm_map x

/-- `withLpProdSubsingleton` preserves the `Lᵖ` seminorm. -/
theorem norm_withLpProdSubsingleton {Q : QuadraticMap R (WithLp p (M₁ × M₂)) P}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) (hM₂ : Subsingleton M₂)
    (x : WithLp p (M₁ × M₂)) :
    ‖withLpProdSubsingleton hQ hM₂ x‖ = ‖x‖ := by
  let : Unique M₂ := uniqueOfSubsingleton (0 : M₂)
  exact (LinearIsometryEquiv.withLpProdUnique p R M₁ M₂).norm_map x

end Norm

end QuadraticMap.IsometryEquiv
