/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.WithLp
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Structural quadratic isometries on `WithLp` products

When `Q` on `WithLp p (M₁ × M₂)` decomposes as `Q x = Q₁ x.1 + Q₂ x.2`, `WithLp.linearEquiv`
identifies `Q` with `Q₁.prod Q₂`, and the structural equivalences of binary `WithLp` products
(swap, associator, and projection away from a subsingleton summand) are quadratic isometries. No
metric or seminorm assumption is needed for the isometries or for their scalar-extension
compatibility laws with `QuadraticMap.IsometryEquiv.uniqueProd`, `prodUnique`, `prodComm`, and
`prodAssoc`. For the `L²` negative-norm-squared formula, see
`TauCeti/LinearAlgebra/QuadraticForm/WithLp/L2.lean`.

## Main definitions

* `QuadraticMap.IsometryEquiv.withLpProd`: `Q.IsometryEquiv (Q₁.prod Q₂)` via `WithLp.linearEquiv`.
* `QuadraticMap.IsometryEquiv.withLpProdComm`: `Q₁₂.IsometryEquiv Q₂₁` swapping `M₁` and `M₂`.
* `QuadraticMap.IsometryEquiv.withLpProdAssoc`: `Q_L.IsometryEquiv Q_R` reassociating triple sums.
* `QuadraticMap.IsometryEquiv.withLpSubsingletonProd` and
  `QuadraticMap.IsometryEquiv.withLpProdSubsingleton`: deleting a subsingleton summand.

## Main results

* `QuadraticMap.IsometryEquiv.toLinearEquiv_withLpProd`,
  `QuadraticMap.IsometryEquiv.toLinearEquiv_withLpSubsingletonProd`,
  `QuadraticMap.IsometryEquiv.toLinearEquiv_withLpProdSubsingleton`,
  `QuadraticMap.IsometryEquiv.toLinearEquiv_withLpProdComm`, and
  `QuadraticMap.IsometryEquiv.toLinearEquiv_withLpProdAssoc`: bundled `toLinearEquiv` normal forms.
* `QuadraticMap.IsometryEquiv.withLpSubsingletonProd_toIsometry_baseChange`,
  `QuadraticMap.IsometryEquiv.withLpProdSubsingleton_toIsometry_baseChange`,
  `QuadraticMap.IsometryEquiv.withLpProdComm_toIsometry_baseChange`, and
  `QuadraticMap.IsometryEquiv.withLpProdAssoc_toIsometry_baseChange`: compatibility of the
  structural `WithLp` isometries with `baseChange` and `baseChangeProd`.
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
  map_app' x := by simp [QuadraticMap.prod_apply, hQ x]

/-- The underlying linear equivalence of `withLpProd` is `WithLp.linearEquiv`. -/
@[simp]
theorem toLinearEquiv_withLpProd :
    (withLpProd hQ).toLinearEquiv = WithLp.linearEquiv p R (M₁ × M₂) :=
  (rfl)

/-- `withLpProd` unwraps `WithLp.ofLp`. -/
@[simp]
theorem withLpProd_apply (x : WithLp p (M₁ × M₂)) : withLpProd hQ x = WithLp.ofLp x := (rfl)

/-- The inverse of `withLpProd` wraps a pair with `WithLp.toLp p`. -/
@[simp]
theorem withLpProd_symm_apply (x : M₁ × M₂) : (withLpProd hQ).symm x = WithLp.toLp p x := (rfl)

/-- Projecting `WithLp p (M₁ × M₂)` onto `M₂` is a quadratic isometry when `M₁` is a subsingleton.
-/
def withLpSubsingletonProd [Subsingleton M₁] : Q.IsometryEquiv Q₂ :=
  letI : Unique M₁ := uniqueOfSubsingleton 0
  (withLpProd hQ).trans (uniqueProd Q₁ Q₂)

/-- `withLpSubsingletonProd` projects onto the second coordinate. -/
@[simp]
theorem withLpSubsingletonProd_apply [Subsingleton M₁] (x : WithLp p (M₁ × M₂)) :
    withLpSubsingletonProd hQ x = (WithLp.ofLp x).2 := by
  let : Unique M₁ := uniqueOfSubsingleton 0
  exact IsometryEquiv.uniqueProd_apply Q₁ Q₂ (withLpProd hQ x)

/-- The inverse of `withLpSubsingletonProd` embeds `m₂` as `(0, m₂)`. -/
@[simp]
theorem withLpSubsingletonProd_symm_apply [Subsingleton M₁] (m₂ : M₂) :
    (withLpSubsingletonProd hQ).symm m₂ = WithLp.toLp p (0, m₂) :=
  (withLpSubsingletonProd hQ).symm_apply_eq.mpr
    (withLpSubsingletonProd_apply hQ (WithLp.toLp p (0, m₂))).symm

/-- The underlying linear equivalence of `withLpSubsingletonProd` is `WithLp.linearEquiv`
composed with `LinearEquiv.uniqueProd`. -/
@[simp]
theorem toLinearEquiv_withLpSubsingletonProd [Subsingleton M₁] :
    (withLpSubsingletonProd hQ).toLinearEquiv =
      letI : Unique M₁ := uniqueOfSubsingleton 0
      (WithLp.linearEquiv p R (M₁ × M₂)).trans LinearEquiv.uniqueProd := by
  let : Unique M₁ := uniqueOfSubsingleton 0
  ext x
  simp

/-- Projecting `WithLp p (M₁ × M₂)` onto `M₁` is a quadratic isometry when `M₂` is a subsingleton.
-/
def withLpProdSubsingleton [Subsingleton M₂] : Q.IsometryEquiv Q₁ :=
  letI : Unique M₂ := uniqueOfSubsingleton 0
  (withLpProd hQ).trans (prodUnique Q₁ Q₂)

/-- `withLpProdSubsingleton` projects onto the first coordinate. -/
@[simp]
theorem withLpProdSubsingleton_apply [Subsingleton M₂] (x : WithLp p (M₁ × M₂)) :
    withLpProdSubsingleton hQ x = (WithLp.ofLp x).1 := by
  let : Unique M₂ := uniqueOfSubsingleton 0
  exact IsometryEquiv.prodUnique_apply Q₁ Q₂ (withLpProd hQ x)

/-- The inverse of `withLpProdSubsingleton` embeds `m₁` as `(m₁, 0)`. -/
@[simp]
theorem withLpProdSubsingleton_symm_apply [Subsingleton M₂] (m₁ : M₁) :
    (withLpProdSubsingleton hQ).symm m₁ = WithLp.toLp p (m₁, 0) :=
  (withLpProdSubsingleton hQ).symm_apply_eq.mpr
    (withLpProdSubsingleton_apply hQ (WithLp.toLp p (m₁, 0))).symm

/-- The underlying linear equivalence of `withLpProdSubsingleton` is `WithLp.linearEquiv`
composed with `LinearEquiv.prodUnique`. -/
@[simp]
theorem toLinearEquiv_withLpProdSubsingleton [Subsingleton M₂] :
    (withLpProdSubsingleton hQ).toLinearEquiv =
      letI : Unique M₂ := uniqueOfSubsingleton 0
      (WithLp.linearEquiv p R (M₁ × M₂)).trans LinearEquiv.prodUnique := by
  let : Unique M₂ := uniqueOfSubsingleton 0
  ext x
  simp

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

/-- The underlying linear equivalence of `withLpProdComm` is `LinearEquiv.prodComm` lifted to
`WithLp`. -/
@[simp]
theorem toLinearEquiv_withLpProdComm :
    (withLpProdComm hQ₁₂ hQ₂₁).toLinearEquiv = (LinearEquiv.prodComm R M₁ M₂).withLpCongr p :=
  (rfl)

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

/-- The underlying linear equivalence of `withLpProdAssoc` is `LinearEquiv.withLpProdAssoc`. -/
@[simp]
theorem toLinearEquiv_withLpProdAssoc :
    (withLpProdAssoc hQ₁₂ hQ₂₃ hQ_L hQ_R).toLinearEquiv =
      LinearEquiv.withLpProdAssoc p R M₁ M₂ M₃ :=
  (rfl)

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
    [Subsingleton M₁] :
    (uniqueProd (Q₁.baseChange A) (Q₂.baseChange A)).toIsometry.comp
        ((withLpProd hQ).baseChangeProd A).toIsometry =
      (withLpSubsingletonProd hQ).toIsometry.baseChange A := by
  refine QuadraticMap.Isometry.baseChange_ext fun x ↦ ?_
  obtain ⟨⟨v, w⟩, rfl⟩ := WithLp.toLp_surjective p x
  simp [baseChangeProd_tmul]

/-- Scalar extension of `withLpProdSubsingleton` commutes with `baseChangeProd` and `prodUnique`. -/
theorem withLpProdSubsingleton_toIsometry_baseChange
    {Q : QuadraticForm R (WithLp p (M₁ × M₂))}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    [Subsingleton M₂] :
    (prodUnique (Q₁.baseChange A) (Q₂.baseChange A)).toIsometry.comp
        ((withLpProd hQ).baseChangeProd A).toIsometry =
      (withLpProdSubsingleton hQ).toIsometry.baseChange A := by
  refine QuadraticMap.Isometry.baseChange_ext fun x ↦ ?_
  obtain ⟨⟨v, w⟩, rfl⟩ := WithLp.toLp_surjective p x
  simp [baseChangeProd_tmul]

/-- Scalar extension of `withLpProdComm` commutes with `baseChangeProd` and `prodComm`. -/
theorem withLpProdComm_toIsometry_baseChange
    {Q₁₂ : QuadraticForm R (WithLp p (M₁ × M₂))} {Q₂₁ : QuadraticForm R (WithLp p (M₂ × M₁))}
    (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₁ : ∀ y, Q₂₁ y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2) :
    ((withLpProd hQ₂₁).baseChangeProd A).toIsometry.comp
        ((withLpProdComm hQ₁₂ hQ₂₁).toIsometry.baseChange A) =
      (prodComm (Q₁.baseChange A) (Q₂.baseChange A)).toIsometry.comp
        ((withLpProd hQ₁₂).baseChangeProd A).toIsometry := by
  refine QuadraticMap.Isometry.baseChange_ext fun x ↦ ?_
  obtain ⟨⟨v, w⟩, rfl⟩ := WithLp.toLp_surjective p x
  simp [baseChangeProd_tmul]

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
        ((withLpProdAssoc hQ₁₂ hQ₂₃ hQ_L hQ_R).toIsometry.baseChange A) := by
  refine QuadraticMap.Isometry.baseChange_ext fun x ↦ ?_
  obtain ⟨⟨x₁₂, w⟩, rfl⟩ := WithLp.toLp_surjective p x
  obtain ⟨⟨u, v⟩, rfl⟩ := WithLp.toLp_surjective p x₁₂
  simp [baseChangeProd_tmul]

end BaseChange

end QuadraticMap.IsometryEquiv
