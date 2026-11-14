/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Isometric equivalences of quadratic maps on `WithLp` products

When a quadratic map `Q` on `WithLp p (M₁ × M₂)` decomposes orthogonally as
`Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2`, `WithLp.linearEquiv` identifies `Q`
isometrically with `Q₁.prod Q₂`, and the structural equivalences of Cartesian products (swapping
factors, reassociating iterated `WithLp` products, and deleting trivial factors) lift to isometric
equivalences of quadratic maps on `WithLp`.

## Main definitions

* `QuadraticMap.IsometryEquiv.withLpProd`: `WithLp.linearEquiv` as an isometric equivalence
  `Q.IsometryEquiv (Q₁.prod Q₂)`.
* `QuadraticMap.IsometryEquiv.withLpProdComm`: swapping the factors of `WithLp p (M₁ × M₂)`.
* `QuadraticMap.IsometryEquiv.withLpProdAssoc`: reassociating
  `WithLp p (WithLp p (M₁ × M₂) × M₃)` as `WithLp p (M₁ × WithLp p (M₂ × M₃))`.
* `QuadraticMap.IsometryEquiv.withLpUniqueProd` and `QuadraticMap.IsometryEquiv.withLpProdUnique`:
  deleting a trivial left or right factor from `WithLp p (M₁ × M₂)`.
-/

public section

open scoped ENNReal

namespace QuadraticMap.IsometryEquiv

section Binary

variable {p : ℝ≥0∞} {R M₁ M₂ P : Type*} [CommSemiring R]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommMonoid P]
  [Module R M₁] [Module R M₂] [Module R P]
  {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P}
  {Q : QuadraticMap R (WithLp p (M₁ × M₂)) P}

/-- `WithLp.linearEquiv` as an isometric equivalence of quadratic maps when
`Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2`. -/
def withLpProd (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) :
    Q.IsometryEquiv (Q₁.prod Q₂) where
  toLinearEquiv := WithLp.linearEquiv p R (M₁ × M₂)
  map_app' x := (hQ x).symm

/-- The underlying linear equivalence of `QuadraticMap.IsometryEquiv.withLpProd` is
`WithLp.linearEquiv`. -/
@[simp]
theorem toLinearEquiv_withLpProd (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) :
    (withLpProd hQ).toLinearEquiv = WithLp.linearEquiv p R (M₁ × M₂) :=
  (rfl)

/-- `QuadraticMap.IsometryEquiv.withLpProd` unwraps `WithLp`. -/
@[simp]
theorem withLpProd_apply (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (x : WithLp p (M₁ × M₂)) :
    withLpProd hQ x = WithLp.ofLp x :=
  (rfl)

/-- The inverse of `QuadraticMap.IsometryEquiv.withLpProd` wraps a pair in `WithLp`. -/
@[simp]
theorem withLpProd_symm_apply (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (x : M₁ × M₂) :
    (withLpProd hQ).symm x = WithLp.toLp p x :=
  (rfl)

/-- Exchanging the factors of `WithLp p (M₁ × M₂)` as an isometric equivalence of quadratic maps. -/
def withLpProdComm {Q' : QuadraticMap R (WithLp p (M₂ × M₁)) P}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ' : ∀ y, Q' y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2) :
    Q.IsometryEquiv Q' where
  toLinearEquiv := (LinearEquiv.prodComm R M₁ M₂).withLpCongr p
  map_app' x := by simp [hQ, hQ', add_comm]

/-- The underlying linear equivalence of `QuadraticMap.IsometryEquiv.withLpProdComm`. -/
@[simp]
theorem toLinearEquiv_withLpProdComm {Q' : QuadraticMap R (WithLp p (M₂ × M₁)) P}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ' : ∀ y, Q' y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2) :
    (withLpProdComm hQ hQ').toLinearEquiv = (LinearEquiv.prodComm R M₁ M₂).withLpCongr p :=
  (rfl)

/-- `QuadraticMap.IsometryEquiv.withLpProdComm` swaps the two coordinates inside `WithLp`. -/
@[simp]
theorem withLpProdComm_apply {Q' : QuadraticMap R (WithLp p (M₂ × M₁)) P}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ' : ∀ y, Q' y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2)
    (x : WithLp p (M₁ × M₂)) :
    withLpProdComm hQ hQ' x = WithLp.toLp p ((WithLp.ofLp x).2, (WithLp.ofLp x).1) := by
  simp [← QuadraticMap.IsometryEquiv.coe_toLinearEquiv, toLinearEquiv_withLpProdComm]
  rfl

/-- Deleting a trivial left factor from `WithLp p (M₁ × M₂)` as a quadratic isometric
equivalence. -/
def withLpUniqueProd [Unique M₁]
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) :
    Q.IsometryEquiv Q₂ where
  toLinearEquiv := (WithLp.linearEquiv p R (M₁ × M₂)).trans LinearEquiv.uniqueProd
  map_app' x := by
    rw [hQ x, Subsingleton.elim (WithLp.ofLp x).1 0]
    simp

/-- The underlying linear equivalence of `QuadraticMap.IsometryEquiv.withLpUniqueProd`. -/
@[simp]
theorem toLinearEquiv_withLpUniqueProd [Unique M₁]
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) :
    (withLpUniqueProd hQ).toLinearEquiv =
      (WithLp.linearEquiv p R (M₁ × M₂)).trans LinearEquiv.uniqueProd :=
  (rfl)

/-- `QuadraticMap.IsometryEquiv.withLpUniqueProd` extracts the second coordinate. -/
@[simp]
theorem withLpUniqueProd_apply [Unique M₁]
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (x : WithLp p (M₁ × M₂)) :
    withLpUniqueProd hQ x = (WithLp.ofLp x).2 :=
  LinearEquiv.uniqueProd_apply (R := R) (WithLp.ofLp x)

/-- Deleting a trivial right factor from `WithLp p (M₁ × M₂)` as a quadratic isometric
equivalence. -/
def withLpProdUnique [Unique M₂]
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) :
    Q.IsometryEquiv Q₁ where
  toLinearEquiv := (WithLp.linearEquiv p R (M₁ × M₂)).trans LinearEquiv.prodUnique
  map_app' x := by
    rw [hQ x, Subsingleton.elim (WithLp.ofLp x).2 0]
    simp

/-- The underlying linear equivalence of `QuadraticMap.IsometryEquiv.withLpProdUnique`. -/
@[simp]
theorem toLinearEquiv_withLpProdUnique [Unique M₂]
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2) :
    (withLpProdUnique hQ).toLinearEquiv =
      (WithLp.linearEquiv p R (M₁ × M₂)).trans LinearEquiv.prodUnique :=
  (rfl)

/-- `QuadraticMap.IsometryEquiv.withLpProdUnique` extracts the first coordinate. -/
@[simp]
theorem withLpProdUnique_apply [Unique M₂]
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (x : WithLp p (M₁ × M₂)) :
    withLpProdUnique hQ x = (WithLp.ofLp x).1 :=
  LinearEquiv.prodUnique_apply (R := R) (WithLp.ofLp x)

end Binary

section Assoc

variable {p : ℝ≥0∞} {R M₁ M₂ M₃ P : Type*} [CommSemiring R]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommMonoid P]
  [Module R M₁] [Module R M₂] [Module R M₃] [Module R P]
  {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P} {Q₃ : QuadraticMap R M₃ P}
  {Q₁₂ : QuadraticMap R (WithLp p (M₁ × M₂)) P}
  {Q₂₃ : QuadraticMap R (WithLp p (M₂ × M₃)) P}
  {Q₁₂_₃ : QuadraticMap R (WithLp p (WithLp p (M₁ × M₂) × M₃)) P}
  {Q₁_₂₃ : QuadraticMap R (WithLp p (M₁ × WithLp p (M₂ × M₃))) P}

/-- Reassociating `WithLp p (WithLp p (M₁ × M₂) × M₃)` as `WithLp p (M₁ × WithLp p (M₂ × M₃))` as
an isometric equivalence of quadratic maps. -/
def withLpProdAssoc
    (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ₁₂_₃ : ∀ x, Q₁₂_₃ x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ₁_₂₃ : ∀ x, Q₁_₂₃ x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2) :
    Q₁₂_₃.IsometryEquiv Q₁_₂₃ where
  toLinearEquiv :=
    ((WithLp.linearEquiv p R (WithLp p (M₁ × M₂) × M₃)).trans
      (((WithLp.linearEquiv p R (M₁ × M₂)).prodCongr (LinearEquiv.refl R M₃)).trans
        ((LinearEquiv.prodAssoc R M₁ M₂ M₃).trans
          ((LinearEquiv.refl R M₁).prodCongr
            (WithLp.linearEquiv p R (M₂ × M₃)).symm)))).trans
      (WithLp.linearEquiv p R (M₁ × WithLp p (M₂ × M₃))).symm
  map_app' x := by simp [hQ₁₂_₃, hQ₁₂, hQ₁_₂₃, hQ₂₃, add_assoc]

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
            ((LinearEquiv.refl R M₁).prodCongr
              (WithLp.linearEquiv p R (M₂ × M₃)).symm)))).trans
        (WithLp.linearEquiv p R (M₁ × WithLp p (M₂ × M₃))).symm :=
  (rfl)

/-- Application formula for `QuadraticMap.IsometryEquiv.withLpProdAssoc`. -/
@[simp]
theorem withLpProdAssoc_apply
    (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ₁₂_₃ : ∀ x, Q₁₂_₃ x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
    (hQ₁_₂₃ : ∀ x, Q₁_₂₃ x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2)
    (x : WithLp p (WithLp p (M₁ × M₂) × M₃)) :
    withLpProdAssoc hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃ x =
      WithLp.toLp p ((WithLp.ofLp (WithLp.ofLp x).1).1,
        WithLp.toLp p ((WithLp.ofLp (WithLp.ofLp x).1).2, (WithLp.ofLp x).2)) := by
  simp [← QuadraticMap.IsometryEquiv.coe_toLinearEquiv, toLinearEquiv_withLpProdAssoc]

end Assoc

end QuadraticMap.IsometryEquiv
