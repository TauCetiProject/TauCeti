/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Structural quadratic-form isometries on `WithLp` products

On a `WithLp p` product of modules carrying a quadratic form `Q` that decomposes additively as
`Q x = Q₁ x.fst + Q₂ x.snd`, the structural equivalences of `WithLp` upgrade to quadratic
isometric equivalences (`QuadraticMap.IsometryEquiv`), paralleling
`QuadraticMap.IsometryEquiv.{uniqueProd,prodUnique,prodAssoc,prodComm,baseChangeProd}` on bare
Cartesian products:

* `TauCeti.withLpProdIsometryEquiv` and `TauCeti.baseChangeWithLpProdIsometryEquiv`: comparison of
  `Q` on `WithLp p (V × W)` with `Q₁.prod Q₂` on `V × W`, and its base change
  `A ⊗ (V ⊕ W) ≃ (A ⊗ V) × (A ⊗ W)`.
* `TauCeti.withLpUniqueProdIsometryEquiv` and `TauCeti.withLpProdUniqueIsometryEquiv`: left and
  right unit quadratic isometries when one factor is `[Unique]`.
* `TauCeti.withLpProdAssocIsometryEquiv`: associativity `((U ⊕ V) ⊕ W) ≃ (U ⊕ (V ⊕ W))`.
* `TauCeti.withLpProdCommIsometryEquiv`: symmetry `(V ⊕ W) ≃ (W ⊕ V)`.
* `TauCeti.apply_eq_neg_norm_sq_of_withLp_prod`: for `p = 2` on real seminormed spaces, the
  orthogonal sum of two `-‖·‖²` forms is `-‖·‖²`.

The underlying equivalences require only module structures, while norm preservation holds whenever
`1 ≤ p` and the factors are seminormed additive commutative groups.
-/

public section

noncomputable section

open scoped ENNReal TensorProduct

namespace TauCeti

section Prod

variable {p : ℝ≥0∞} {R V W : Type*} [CommSemiring R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {Q₁ : QuadraticForm R V} {Q₂ : QuadraticForm R W} {Q : QuadraticForm R (WithLp p (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)

/-- `WithLp.linearEquiv p R (V × W)` as a quadratic isometric equivalence `Q.IsometryEquiv
(Q₁.prod Q₂)` when `Q x = Q₁ x.fst + Q₂ x.snd`. -/
def withLpProdIsometryEquiv : Q.IsometryEquiv (Q₁.prod Q₂) where
  toLinearEquiv := WithLp.linearEquiv p R (V × W)
  map_app' x := by simp [hQ x]

/-- Forward application of `TauCeti.withLpProdIsometryEquiv`. -/
@[simp]
theorem withLpProdIsometryEquiv_apply (x : WithLp p (V × W)) :
    withLpProdIsometryEquiv hQ x = WithLp.ofLp x :=
  (rfl)

/-- Inverse application of `TauCeti.withLpProdIsometryEquiv`. -/
@[simp]
theorem withLpProdIsometryEquiv_symm_apply (x : V × W) :
    (withLpProdIsometryEquiv hQ).symm x = WithLp.toLp p x :=
  (rfl)

/-- Underlying linear equivalence of `TauCeti.withLpProdIsometryEquiv`. -/
@[simp]
theorem toLinearEquiv_withLpProdIsometryEquiv :
    (withLpProdIsometryEquiv hQ).toLinearEquiv = WithLp.linearEquiv p R (V × W) :=
  (rfl)

end Prod

section BaseChange

variable {p : ℝ≥0∞} {R V W : Type*} [CommRing R] [Invertible (2 : R)]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {Q₁ : QuadraticForm R V} {Q₂ : QuadraticForm R W} {Q : QuadraticForm R (WithLp p (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (A : Type*) [CommRing A] [Algebra R A]

/-- Base change of `TauCeti.withLpProdIsometryEquiv` to an `R`-algebra `A`: the quadratic
isometry `A ⊗ (V ⊕ W) ≃ (A ⊗ V) × (A ⊗ W)`, `a ⊗ (v, w) ↦ (a ⊗ v, a ⊗ w)`. -/
def baseChangeWithLpProdIsometryEquiv :
    (Q.baseChange A).IsometryEquiv ((Q₁.baseChange A).prod (Q₂.baseChange A)) :=
  (withLpProdIsometryEquiv hQ).baseChangeProd A

/-- On a pure tensor `a ⊗ x`, `TauCeti.baseChangeWithLpProdIsometryEquiv` splits into the two
`WithLp` components. -/
@[simp]
theorem baseChangeWithLpProdIsometryEquiv_tmul (a : A) (x : WithLp p (V × W)) :
    baseChangeWithLpProdIsometryEquiv hQ A (a ⊗ₜ[R] x) =
      (a ⊗ₜ[R] (WithLp.ofLp x).1, a ⊗ₜ[R] (WithLp.ofLp x).2) :=
  QuadraticMap.IsometryEquiv.baseChangeProd_tmul _ a x

/-- Inverse evaluation of `TauCeti.baseChangeWithLpProdIsometryEquiv` on a pair of pure tensors
with the same scalar factor. -/
@[simp]
theorem baseChangeWithLpProdIsometryEquiv_symm_tmul (a : A) (v : V) (w : W) :
    (baseChangeWithLpProdIsometryEquiv hQ A).symm (a ⊗ₜ[R] v, a ⊗ₜ[R] w) =
      a ⊗ₜ[R] WithLp.toLp p (v, w) := by
  apply (baseChangeWithLpProdIsometryEquiv hQ A).injective
  simp

end BaseChange

section UniqueProd

variable {p : ℝ≥0∞} {R V W : Type*} [CommSemiring R]
  [AddCommGroup V] [Module R V] [Unique V] [AddCommGroup W] [Module R W]
  {Q₁ : QuadraticForm R V} {Q₂ : QuadraticForm R W} {Q : QuadraticForm R (WithLp p (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)

/-- When `V` is trivial (`[Unique V]`), projecting `WithLp p (V × W)` onto `W` is a quadratic
isometric equivalence `Q.IsometryEquiv Q₂`. -/
def withLpUniqueProdIsometryEquiv : Q.IsometryEquiv Q₂ where
  toLinearEquiv := (WithLp.linearEquiv p R (V × W)).trans LinearEquiv.uniqueProd
  map_app' x := by
    rw [hQ x, Subsingleton.elim (WithLp.ofLp x).1 0]
    simp

/-- `TauCeti.withLpUniqueProdIsometryEquiv` projects onto the `W` coordinate. -/
@[simp]
theorem withLpUniqueProdIsometryEquiv_apply (x : WithLp p (V × W)) :
    withLpUniqueProdIsometryEquiv hQ x = (WithLp.ofLp x).2 := by
  simp [withLpUniqueProdIsometryEquiv, ← QuadraticMap.IsometryEquiv.coe_toLinearEquiv]

/-- Inverse of `TauCeti.withLpUniqueProdIsometryEquiv`. -/
@[simp]
theorem withLpUniqueProdIsometryEquiv_symm_apply (w : W) :
    (withLpUniqueProdIsometryEquiv hQ).symm w = WithLp.toLp p (0, w) := by
  apply (withLpUniqueProdIsometryEquiv hQ).injective
  simp

/-- Underlying linear equivalence of `TauCeti.withLpUniqueProdIsometryEquiv`. -/
@[simp]
theorem toLinearEquiv_withLpUniqueProdIsometryEquiv :
    (withLpUniqueProdIsometryEquiv hQ).toLinearEquiv =
      (WithLp.linearEquiv p R (V × W)).trans LinearEquiv.uniqueProd :=
  (rfl)

end UniqueProd

section NormUniqueProd

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {R V W : Type*} [CommSemiring R]
  [SeminormedAddCommGroup V] [Module R V] [Unique V]
  [SeminormedAddCommGroup W] [Module R W]
  {Q₁ : QuadraticForm R V} {Q₂ : QuadraticForm R W} {Q : QuadraticForm R (WithLp p (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)

/-- `TauCeti.withLpUniqueProdIsometryEquiv` preserves norms. -/
theorem norm_withLpUniqueProdIsometryEquiv (x : WithLp p (V × W)) :
    ‖withLpUniqueProdIsometryEquiv hQ x‖ = ‖x‖ := by
  simpa using (LinearIsometryEquiv.withLpUniqueProd p R V W).norm_map x

end NormUniqueProd

section ProdUnique

variable {p : ℝ≥0∞} {R V W : Type*} [CommSemiring R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] [Unique W]
  {Q₁ : QuadraticForm R V} {Q₂ : QuadraticForm R W} {Q : QuadraticForm R (WithLp p (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)

/-- When `W` is trivial (`[Unique W]`), projecting `WithLp p (V × W)` onto `V` is a quadratic
isometric equivalence `Q.IsometryEquiv Q₁`. -/
def withLpProdUniqueIsometryEquiv : Q.IsometryEquiv Q₁ where
  toLinearEquiv := (WithLp.linearEquiv p R (V × W)).trans LinearEquiv.prodUnique
  map_app' x := by
    rw [hQ x, Subsingleton.elim (WithLp.ofLp x).2 0]
    simp

/-- `TauCeti.withLpProdUniqueIsometryEquiv` projects onto the `V` coordinate. -/
@[simp]
theorem withLpProdUniqueIsometryEquiv_apply (x : WithLp p (V × W)) :
    withLpProdUniqueIsometryEquiv hQ x = (WithLp.ofLp x).1 := by
  simp [withLpProdUniqueIsometryEquiv, ← QuadraticMap.IsometryEquiv.coe_toLinearEquiv]

/-- Inverse of `TauCeti.withLpProdUniqueIsometryEquiv`. -/
@[simp]
theorem withLpProdUniqueIsometryEquiv_symm_apply (v : V) :
    (withLpProdUniqueIsometryEquiv hQ).symm v = WithLp.toLp p (v, 0) := by
  apply (withLpProdUniqueIsometryEquiv hQ).injective
  simp

/-- Underlying linear equivalence of `TauCeti.withLpProdUniqueIsometryEquiv`. -/
@[simp]
theorem toLinearEquiv_withLpProdUniqueIsometryEquiv :
    (withLpProdUniqueIsometryEquiv hQ).toLinearEquiv =
      (WithLp.linearEquiv p R (V × W)).trans LinearEquiv.prodUnique :=
  (rfl)

end ProdUnique

section NormProdUnique

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {R V W : Type*} [CommSemiring R]
  [SeminormedAddCommGroup V] [Module R V]
  [SeminormedAddCommGroup W] [Module R W] [Unique W]
  {Q₁ : QuadraticForm R V} {Q₂ : QuadraticForm R W} {Q : QuadraticForm R (WithLp p (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)

/-- `TauCeti.withLpProdUniqueIsometryEquiv` preserves norms. -/
theorem norm_withLpProdUniqueIsometryEquiv (x : WithLp p (V × W)) :
    ‖withLpProdUniqueIsometryEquiv hQ x‖ = ‖x‖ := by
  simpa using (LinearIsometryEquiv.withLpProdUnique p R V W).norm_map x

end NormProdUnique

section Assoc

variable {p : ℝ≥0∞} {R U V W : Type*} [CommSemiring R]
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {Q₁ : QuadraticForm R U} {Q₂ : QuadraticForm R V} {Q₃ : QuadraticForm R W}
  {Q₁₂ : QuadraticForm R (WithLp p (U × V))}
  {Q₂₃ : QuadraticForm R (WithLp p (V × W))}
  {Q_L : QuadraticForm R (WithLp p (WithLp p (U × V) × W))}
  {Q_R : QuadraticForm R (WithLp p (U × WithLp p (V × W)))}
  (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ_L : ∀ x, Q_L x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ_R : ∀ x, Q_R x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2)

/-- `LinearEquiv.withLpProdAssoc p R U V W` as a quadratic isometric equivalence
`Q_L.IsometryEquiv Q_R` between `(U ⊕ V) ⊕ W` and `U ⊕ (V ⊕ W)`. -/
def withLpProdAssocIsometryEquiv : Q_L.IsometryEquiv Q_R where
  toLinearEquiv := LinearEquiv.withLpProdAssoc p R U V W
  map_app' x := by simp [hQ_R, hQ₂₃, hQ_L, hQ₁₂, add_assoc]

/-- Forward evaluation of `TauCeti.withLpProdAssocIsometryEquiv`. -/
@[simp]
theorem withLpProdAssocIsometryEquiv_apply (x : WithLp p (WithLp p (U × V) × W)) :
    withLpProdAssocIsometryEquiv hQ₁₂ hQ₂₃ hQ_L hQ_R x =
      WithLp.toLp p (x.fst.fst, WithLp.toLp p (x.fst.snd, x.snd)) := by
  simp [withLpProdAssocIsometryEquiv, ← QuadraticMap.IsometryEquiv.coe_toLinearEquiv]

/-- Inverse evaluation of `TauCeti.withLpProdAssocIsometryEquiv`. -/
@[simp]
theorem withLpProdAssocIsometryEquiv_symm_apply (x : WithLp p (U × WithLp p (V × W))) :
    (withLpProdAssocIsometryEquiv hQ₁₂ hQ₂₃ hQ_L hQ_R).symm x =
      WithLp.toLp p (WithLp.toLp p (x.fst, x.snd.fst), x.snd.snd) := by
  rcases x with ⟨u, ⟨v, w⟩⟩
  apply (withLpProdAssocIsometryEquiv hQ₁₂ hQ₂₃ hQ_L hQ_R).injective
  simp

/-- Underlying linear equivalence of `TauCeti.withLpProdAssocIsometryEquiv`. -/
@[simp]
theorem toLinearEquiv_withLpProdAssocIsometryEquiv :
    (withLpProdAssocIsometryEquiv hQ₁₂ hQ₂₃ hQ_L hQ_R).toLinearEquiv =
      LinearEquiv.withLpProdAssoc p R U V W :=
  (rfl)

end Assoc

section NormAssoc

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {R U V W : Type*} [CommSemiring R]
  [SeminormedAddCommGroup U] [Module R U]
  [SeminormedAddCommGroup V] [Module R V]
  [SeminormedAddCommGroup W] [Module R W]
  {Q₁ : QuadraticForm R U} {Q₂ : QuadraticForm R V} {Q₃ : QuadraticForm R W}
  {Q₁₂ : QuadraticForm R (WithLp p (U × V))}
  {Q₂₃ : QuadraticForm R (WithLp p (V × W))}
  {Q_L : QuadraticForm R (WithLp p (WithLp p (U × V) × W))}
  {Q_R : QuadraticForm R (WithLp p (U × WithLp p (V × W)))}
  (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ_L : ∀ x, Q_L x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ_R : ∀ x, Q_R x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2)

/-- `TauCeti.withLpProdAssocIsometryEquiv` preserves norms. -/
theorem norm_withLpProdAssocIsometryEquiv (x : WithLp p (WithLp p (U × V) × W)) :
    ‖withLpProdAssocIsometryEquiv hQ₁₂ hQ₂₃ hQ_L hQ_R x‖ = ‖x‖ := by
  simpa using (LinearIsometryEquiv.withLpProdAssoc p R U V W).norm_map x

end NormAssoc

section Comm

variable {p : ℝ≥0∞} {R V W : Type*} [CommSemiring R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {Q₁ : QuadraticForm R V} {Q₂ : QuadraticForm R W}
  {Q_VW : QuadraticForm R (WithLp p (V × W))}
  {Q_WV : QuadraticForm R (WithLp p (W × V))}
  (hQ_VW : ∀ x, Q_VW x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ_WV : ∀ y, Q_WV y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2)

/-- `(LinearEquiv.prodComm R V W).withLpCongr p` as a quadratic isometric equivalence
`Q_VW.IsometryEquiv Q_WV` between `V ⊕ W` and `W ⊕ V`. -/
def withLpProdCommIsometryEquiv : Q_VW.IsometryEquiv Q_WV where
  toLinearEquiv := (LinearEquiv.prodComm R V W).withLpCongr p
  map_app' x := by simp [hQ_WV, hQ_VW, add_comm]

/-- Forward evaluation of `TauCeti.withLpProdCommIsometryEquiv` swaps the two coordinates. -/
@[simp]
theorem withLpProdCommIsometryEquiv_apply (x : WithLp p (V × W)) :
    withLpProdCommIsometryEquiv hQ_VW hQ_WV x = WithLp.toLp p (x.snd, x.fst) := by
  rcases x with ⟨v, w⟩
  simp [withLpProdCommIsometryEquiv, ← QuadraticMap.IsometryEquiv.coe_toLinearEquiv]

/-- The inverse of `TauCeti.withLpProdCommIsometryEquiv` is the swap in the opposite direction. -/
@[simp]
theorem withLpProdCommIsometryEquiv_symm :
    (withLpProdCommIsometryEquiv hQ_VW hQ_WV).symm =
      withLpProdCommIsometryEquiv hQ_WV hQ_VW := by
  apply DFunLike.ext
  intro x
  rcases x with ⟨w, v⟩
  apply (withLpProdCommIsometryEquiv hQ_VW hQ_WV).injective
  simp

/-- Underlying linear equivalence of `TauCeti.withLpProdCommIsometryEquiv`. -/
@[simp]
theorem toLinearEquiv_withLpProdCommIsometryEquiv :
    (withLpProdCommIsometryEquiv hQ_VW hQ_WV).toLinearEquiv =
      (LinearEquiv.prodComm R V W).withLpCongr p :=
  (rfl)

end Comm

section NormComm

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {R V W : Type*} [CommSemiring R]
  [SeminormedAddCommGroup V] [Module R V]
  [SeminormedAddCommGroup W] [Module R W]
  {Q₁ : QuadraticForm R V} {Q₂ : QuadraticForm R W}
  {Q_VW : QuadraticForm R (WithLp p (V × W))}
  {Q_WV : QuadraticForm R (WithLp p (W × V))}
  (hQ_VW : ∀ x, Q_VW x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ_WV : ∀ y, Q_WV y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2)

/-- `TauCeti.withLpProdCommIsometryEquiv` preserves norms. -/
theorem norm_withLpProdCommIsometryEquiv (x : WithLp p (V × W)) :
    ‖withLpProdCommIsometryEquiv hQ_VW hQ_WV x‖ = ‖x‖ := by
  simpa using (LinearIsometryEquiv.withLpProdComm p R V W).norm_map x

end NormComm

section NegNormSq

variable {V W : Type*} [SeminormedAddCommGroup V] [Module ℝ V]
  [SeminormedAddCommGroup W] [Module ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}

/-- On `WithLp 2 (V × W)`, the orthogonal sum of two negative-squared-norm forms is minus the
squared `L²` norm. -/
theorem apply_eq_neg_norm_sq_of_withLp_prod
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (x : WithLp 2 (V × W)) :
    Q x = -‖x‖ ^ 2 := by
  simp only [hQ x, hQ₁, hQ₂, WithLp.prod_norm_sq_eq_of_L2, WithLp.ofLp_fst, WithLp.ofLp_snd]
  ring

end NegNormSq

end TauCeti
