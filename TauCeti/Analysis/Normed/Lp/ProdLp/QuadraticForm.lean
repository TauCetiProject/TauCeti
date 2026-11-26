/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Structural quadratic isometries on `WithLp` products

This file packages `WithLp.linearEquiv` as a `QuadraticMap.IsometryEquiv`
(`QuadraticMap.IsometryEquiv.withLpProd`) identifying an additive quadratic map
`Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2` on `WithLp p (V × W)` with `Q₁.prod Q₂`, and
composes it with `prodComm`, `prodAssoc`, `uniqueProd`, and `prodUnique` to obtain the structural
quadratic isometries of `WithLp` products.

The algebraic isometries work for arbitrary `p : ℝ≥0∞`, commutative semiring `R`, additive groups
`U, V, W`, and codomain `P`. When the factors are seminormed and `Fact (1 ≤ p)`, their underlying
linear equivalences match `LinearIsometryEquiv.withLp*` and they preserve norms (`norm_withLp*`).

For `p = 2` on seminormed modules, additive forms preserve `c * ‖·‖²` (and `-‖·‖²`), and every
real-valued quadratic map on a subsingleton module equals `c * ‖·‖²`.

## Main definitions

* `QuadraticMap.IsometryEquiv.withLpProd`: `WithLp.linearEquiv` as an isometry `Q ≃ Q₁.prod Q₂`.
* `QuadraticMap.IsometryEquiv.withLpProdComm`, `withLpProdAssoc`, `withLpUniqueProd`,
  `withLpProdUnique`: structural `QuadraticMap.IsometryEquiv` equivalences on `WithLp` products,
  defined as composites of `withLpProd` with `prodComm`, `prodAssoc`, `uniqueProd`, and
  `prodUnique`.

## Main results

* Application, inverse, composition, underlying linear-equivalence, and norm-preservation
  (`norm_withLp*`) lemmas identifying the structural isometries with `LinearIsometryEquiv.withLp*`.
* `QuadraticMap.eq_mul_norm_sq_of_withLpProd`, `QuadraticMap.eq_neg_norm_sq_of_withLpProd`,
  `QuadraticMap.eq_mul_norm_sq_of_subsingleton`, and `QuadraticMap.eq_neg_norm_sq_of_subsingleton`.
-/

public section

open scoped ENNReal

namespace QuadraticMap

namespace IsometryEquiv

section Algebraic
variable {p : ℝ≥0∞} {R U V W P : Type*} [CommSemiring R]
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommMonoid P] [Module R P]

section Binary
variable {Q₁ : QuadraticMap R V P} {Q₂ : QuadraticMap R W P}
  {Q : QuadraticMap R (WithLp p (V × W)) P}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)

include hQ in
/-- Identifying an additive quadratic map `Q (v, w) = Q₁ v + Q₂ w` on `WithLp p (V × W)` with the
orthogonal product `Q₁.prod Q₂` via `WithLp.linearEquiv`. -/
def withLpProd : Q.IsometryEquiv (Q₁.prod Q₂) where
  toLinearEquiv := WithLp.linearEquiv p R (V × W)
  map_app' x := (hQ x).symm

/-- Applying `QuadraticMap.IsometryEquiv.withLpProd` unwraps `WithLp`. -/
@[simp] theorem withLpProd_apply (x : WithLp p (V × W)) :
    withLpProd hQ x = WithLp.ofLp x := (rfl)

/-- Applying the inverse of `QuadraticMap.IsometryEquiv.withLpProd` wraps a pair in `WithLp`. -/
@[simp] theorem withLpProd_symm_apply (x : V × W) :
    (withLpProd hQ).symm x = WithLp.toLp p x := (rfl)

/-- The linear equivalence underlying `QuadraticMap.IsometryEquiv.withLpProd`. -/
@[simp] theorem toLinearEquiv_withLpProd :
    (withLpProd hQ).toLinearEquiv = WithLp.linearEquiv p R (V × W) := (rfl)

section ProdComm
variable {Q' : QuadraticMap R (WithLp p (W × V)) P}
  (hQ' : ∀ y, Q' y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2)

include hQ hQ' in
/-- Swapping the two coordinates of `WithLp p (V × W)` as a quadratic isometry equivalence between
additive quadratic maps `Q (v, w) = Q₁ v + Q₂ w` and `Q' (w, v) = Q₂ w + Q₁ v`. -/
def withLpProdComm : Q.IsometryEquiv Q' :=
  (withLpProd hQ).trans <| (prodComm Q₁ Q₂).trans (withLpProd hQ').symm

/-- Applying `QuadraticMap.IsometryEquiv.withLpProdComm` swaps the two `WithLp` coordinates. -/
@[simp] theorem withLpProdComm_apply (x : WithLp p (V × W)) :
    withLpProdComm hQ hQ' x = WithLp.toLp p (x.snd, x.fst) := (rfl)

/-- The inverse of `QuadraticMap.IsometryEquiv.withLpProdComm` swaps in the other direction. -/
@[simp] theorem withLpProdComm_symm : (withLpProdComm hQ hQ').symm = withLpProdComm hQ' hQ :=
  DFunLike.ext _ _ fun _ ↦ rfl

/-- The linear equivalence underlying `QuadraticMap.IsometryEquiv.withLpProdComm`. -/
@[simp] theorem toLinearEquiv_withLpProdComm :
    (withLpProdComm hQ hQ').toLinearEquiv = (LinearEquiv.prodComm R V W).withLpCongr p := (rfl)

/-- `QuadraticMap.IsometryEquiv.withLpProd` intertwines `withLpProdComm` with `prodComm`. -/
theorem withLpProdComm_trans_withLpProd :
    (withLpProdComm hQ hQ').trans (withLpProd hQ') = (withLpProd hQ).trans (prodComm Q₁ Q₂) :=
  DFunLike.ext _ _ fun _ ↦ rfl
end ProdComm

include hQ in
/-- Deleting a trivial left factor from `WithLp p (V × W)` as a quadratic isometry `Q ≃ Q₂`. -/
def withLpUniqueProd [Unique V] : Q.IsometryEquiv Q₂ :=
  (withLpProd hQ).trans (uniqueProd Q₁ Q₂)

/-- Unfolding `QuadraticMap.IsometryEquiv.withLpUniqueProd` through `withLpProd` and
`uniqueProd`. -/
theorem withLpUniqueProd_def [Unique V] :
    withLpUniqueProd hQ = (withLpProd hQ).trans (uniqueProd Q₁ Q₂) := (rfl)

/-- Applying `QuadraticMap.IsometryEquiv.withLpUniqueProd` projects onto the second coordinate. -/
@[simp] theorem withLpUniqueProd_apply [Unique V] (x : WithLp p (V × W)) :
    withLpUniqueProd hQ x = x.snd :=
  uniqueProd_apply Q₁ Q₂ (WithLp.ofLp x)

/-- The inverse of `QuadraticMap.IsometryEquiv.withLpUniqueProd` pairs a vector with `default`. -/
@[simp] theorem withLpUniqueProd_symm_apply [Unique V] (w : W) :
    (withLpUniqueProd hQ).symm w = WithLp.toLp p (default, w) :=
  congrArg (WithLp.toLp p) (uniqueProd_symm_apply Q₁ Q₂ w)

/-- The linear equivalence underlying `QuadraticMap.IsometryEquiv.withLpUniqueProd`. -/
@[simp] theorem toLinearEquiv_withLpUniqueProd [Unique V] :
    (withLpUniqueProd hQ).toLinearEquiv =
      (WithLp.linearEquiv p R (V × W)).trans LinearEquiv.uniqueProd :=
  LinearEquiv.ext fun x ↦ by simp

include hQ in
/-- Deleting a trivial right factor from `WithLp p (V × W)` as a quadratic isometry `Q ≃ Q₁`. -/
def withLpProdUnique [Unique W] : Q.IsometryEquiv Q₁ :=
  (withLpProd hQ).trans (prodUnique Q₁ Q₂)

/-- Unfolding `QuadraticMap.IsometryEquiv.withLpProdUnique` through `withLpProd` and
`prodUnique`. -/
theorem withLpProdUnique_def [Unique W] :
    withLpProdUnique hQ = (withLpProd hQ).trans (prodUnique Q₁ Q₂) := (rfl)

/-- Applying `QuadraticMap.IsometryEquiv.withLpProdUnique` projects onto the first coordinate. -/
@[simp] theorem withLpProdUnique_apply [Unique W] (x : WithLp p (V × W)) :
    withLpProdUnique hQ x = x.fst :=
  prodUnique_apply Q₁ Q₂ (WithLp.ofLp x)

/-- The inverse of `QuadraticMap.IsometryEquiv.withLpProdUnique` pairs a vector with `default`. -/
@[simp] theorem withLpProdUnique_symm_apply [Unique W] (v : V) :
    (withLpProdUnique hQ).symm v = WithLp.toLp p (v, default) :=
  congrArg (WithLp.toLp p) (prodUnique_symm_apply Q₁ Q₂ v)

/-- The linear equivalence underlying `QuadraticMap.IsometryEquiv.withLpProdUnique`. -/
@[simp] theorem toLinearEquiv_withLpProdUnique [Unique W] :
    (withLpProdUnique hQ).toLinearEquiv =
      (WithLp.linearEquiv p R (V × W)).trans LinearEquiv.prodUnique :=
  LinearEquiv.ext fun x ↦ by simp
end Binary

section ProdAssoc
variable {Q₁ : QuadraticMap R U P} {Q₂ : QuadraticMap R V P} {Q₃ : QuadraticMap R W P}
  {Q₁₂ : QuadraticMap R (WithLp p (U × V)) P} {Q₂₃ : QuadraticMap R (WithLp p (V × W)) P}
  {Q₁₂_₃ : QuadraticMap R (WithLp p (WithLp p (U × V) × W)) P}
  {Q₁_₂₃ : QuadraticMap R (WithLp p (U × WithLp p (V × W))) P}
  (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ₁₂_₃ : ∀ x, Q₁₂_₃ x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ₁_₂₃ : ∀ x, Q₁_₂₃ x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2)

include hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃ in
/-- Reassociating `((U × V) × W) ≃ (U × (V × W))` on `WithLp` products as a quadratic isometry
equivalence between iterated additive quadratic maps. -/
def withLpProdAssoc : Q₁₂_₃.IsometryEquiv Q₁_₂₃ :=
  (withLpProd hQ₁₂_₃).trans <|
    ((withLpProd hQ₁₂).prod (refl Q₃)).trans <|
      (prodAssoc Q₁ Q₂ Q₃).trans <|
        ((refl Q₁).prod (withLpProd hQ₂₃).symm).trans (withLpProd hQ₁_₂₃).symm

/-- Applying `QuadraticMap.IsometryEquiv.withLpProdAssoc` reassociates coordinates to the right. -/
@[simp] theorem withLpProdAssoc_apply (x : WithLp p (WithLp p (U × V) × W)) :
    withLpProdAssoc hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃ x =
      WithLp.toLp p (x.fst.fst, WithLp.toLp p (x.fst.snd, x.snd)) := by
  simp [withLpProdAssoc]

/-- Applying the inverse of `QuadraticMap.IsometryEquiv.withLpProdAssoc` reassociates left. -/
@[simp] theorem withLpProdAssoc_symm_apply (y : WithLp p (U × WithLp p (V × W))) :
    (withLpProdAssoc hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).symm y =
      WithLp.toLp p (WithLp.toLp p (y.fst, y.snd.fst), y.snd.snd) :=
  (withLpProdAssoc hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).symm_apply_eq.mpr
    (by simp [← WithLp.ofLp_fst, ← WithLp.ofLp_snd])
end ProdAssoc
end Algebraic

section Normed
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {R U V W P : Type*} [CommSemiring R]
  [SeminormedAddCommGroup U] [Module R U] [SeminormedAddCommGroup V] [Module R V]
  [SeminormedAddCommGroup W] [Module R W] [AddCommMonoid P] [Module R P]

section Binary
variable {Q₁ : QuadraticMap R V P} {Q₂ : QuadraticMap R W P}
  {Q : QuadraticMap R (WithLp p (V × W)) P}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)

section ProdComm
variable {Q' : QuadraticMap R (WithLp p (W × V)) P}
  (hQ' : ∀ y, Q' y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2)

/-- `withLpProdComm` has the same underlying linear equivalence as
`LinearIsometryEquiv.withLpProdComm`. -/
theorem toLinearEquiv_withLpProdComm_eq_linearIsometryEquiv :
    (withLpProdComm hQ hQ').toLinearEquiv =
      (LinearIsometryEquiv.withLpProdComm p R V W).toLinearEquiv := (rfl)

/-- `QuadraticMap.IsometryEquiv.withLpProdComm` preserves norms. -/
theorem norm_withLpProdComm (x : WithLp p (V × W)) : ‖withLpProdComm hQ hQ' x‖ = ‖x‖ :=
  (LinearIsometryEquiv.withLpProdComm p R V W).norm_map x
end ProdComm

/-- `withLpUniqueProd` has the same underlying linear equivalence as
`LinearIsometryEquiv.withLpUniqueProd`. -/
theorem toLinearEquiv_withLpUniqueProd_eq_linearIsometryEquiv [Unique V] :
    (withLpUniqueProd hQ).toLinearEquiv =
      (LinearIsometryEquiv.withLpUniqueProd p R V W).toLinearEquiv :=
  LinearEquiv.ext fun x ↦ by simp

/-- `QuadraticMap.IsometryEquiv.withLpUniqueProd` preserves norms. -/
theorem norm_withLpUniqueProd [Unique V] (x : WithLp p (V × W)) :
    ‖withLpUniqueProd hQ x‖ = ‖x‖ := by
  simpa using (LinearIsometryEquiv.withLpUniqueProd p R V W).norm_map x

/-- `withLpProdUnique` has the same underlying linear equivalence as
`LinearIsometryEquiv.withLpProdUnique`. -/
theorem toLinearEquiv_withLpProdUnique_eq_linearIsometryEquiv [Unique W] :
    (withLpProdUnique hQ).toLinearEquiv =
      (LinearIsometryEquiv.withLpProdUnique p R V W).toLinearEquiv :=
  LinearEquiv.ext fun x ↦ by simp

/-- `QuadraticMap.IsometryEquiv.withLpProdUnique` preserves norms. -/
theorem norm_withLpProdUnique [Unique W] (x : WithLp p (V × W)) :
    ‖withLpProdUnique hQ x‖ = ‖x‖ := by
  simpa using (LinearIsometryEquiv.withLpProdUnique p R V W).norm_map x
end Binary

section ProdAssoc
variable {Q₁ : QuadraticMap R U P} {Q₂ : QuadraticMap R V P} {Q₃ : QuadraticMap R W P}
  {Q₁₂ : QuadraticMap R (WithLp p (U × V)) P} {Q₂₃ : QuadraticMap R (WithLp p (V × W)) P}
  {Q₁₂_₃ : QuadraticMap R (WithLp p (WithLp p (U × V) × W)) P}
  {Q₁_₂₃ : QuadraticMap R (WithLp p (U × WithLp p (V × W))) P}
  (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ₁₂_₃ : ∀ x, Q₁₂_₃ x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ₁_₂₃ : ∀ x, Q₁_₂₃ x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2)

/-- `withLpProdAssoc` has the same underlying linear equivalence as
`LinearIsometryEquiv.withLpProdAssoc`. -/
theorem toLinearEquiv_withLpProdAssoc_eq_linearIsometryEquiv :
    (withLpProdAssoc hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).toLinearEquiv =
      (LinearIsometryEquiv.withLpProdAssoc p R U V W).toLinearEquiv :=
  LinearEquiv.ext fun x ↦ by simp

/-- `QuadraticMap.IsometryEquiv.withLpProdAssoc` preserves norms. -/
theorem norm_withLpProdAssoc (x : WithLp p (WithLp p (U × V) × W)) :
    ‖withLpProdAssoc hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃ x‖ = ‖x‖ := by
  simpa using (LinearIsometryEquiv.withLpProdAssoc p R U V W).norm_map x
end ProdAssoc
end Normed

end IsometryEquiv

section NormSq
variable {R V W : Type*} [CommSemiring R] [Module R ℝ]
  [SeminormedAddCommGroup V] [Module R V] [SeminormedAddCommGroup W] [Module R W]

section Prod
variable {Q₁ : QuadraticMap R V ℝ} {Q₂ : QuadraticMap R W ℝ}
  {Q : QuadraticMap R (WithLp 2 (V × W)) ℝ}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)

include hQ in
/-- When `Q₁ v = c * ‖v‖²` and `Q₂ w = c * ‖w‖²`, an additive quadratic form on
`WithLp 2 (V × W)` satisfies `Q x = c * ‖x‖²`. -/
theorem eq_mul_norm_sq_of_withLpProd {c : ℝ}
    (hQ₁ : ∀ v, Q₁ v = c * ‖v‖ ^ 2) (hQ₂ : ∀ w, Q₂ w = c * ‖w‖ ^ 2) (x : WithLp 2 (V × W)) :
    Q x = c * ‖x‖ ^ 2 := by
  rw [hQ, hQ₁, hQ₂, WithLp.ofLp_fst, WithLp.ofLp_snd, WithLp.prod_norm_sq_eq_of_L2, mul_add]

include hQ in
/-- When `Q₁ v = -‖v‖²` and `Q₂ w = -‖w‖²`, an additive quadratic form `Q (v, w) = Q₁ v + Q₂ w` on
`WithLp 2 (V × W)` satisfies `Q x = -‖x‖²`. -/
theorem eq_neg_norm_sq_of_withLpProd
    (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (x : WithLp 2 (V × W)) :
    Q x = -‖x‖ ^ 2 := by
  simpa using eq_mul_norm_sq_of_withLpProd hQ (c := -1) (by simpa using hQ₁) (by simpa using hQ₂) x
end Prod

/-- On a subsingleton seminormed module, every real-valued quadratic map satisfies
`Q v = c * ‖v‖²`. -/
theorem eq_mul_norm_sq_of_subsingleton [Subsingleton V] (Q : QuadraticMap R V ℝ) (c : ℝ) (v : V) :
    Q v = c * ‖v‖ ^ 2 := by
  simp [Subsingleton.elim v 0]

/-- On a subsingleton seminormed module, every real-valued quadratic map satisfies
`Q v = -‖v‖²`. -/
theorem eq_neg_norm_sq_of_subsingleton [Subsingleton V] (Q : QuadraticMap R V ℝ) (v : V) :
    Q v = -‖v‖ ^ 2 := by
  simpa using eq_mul_norm_sq_of_subsingleton Q (-1) v
end NormSq

end QuadraticMap
