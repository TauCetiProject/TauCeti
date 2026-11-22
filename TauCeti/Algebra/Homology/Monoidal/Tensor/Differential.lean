/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# The differential of a tensor product of complexes

For two complexes `X` and `Y` whose tensor product exists, `[X.HasTensor Y]`, Mathlib's
`HomologicalComplex.tensorObj X Y` totalizes their degreewise tensor product. Its signs are the
tensor signs of the complex shape, `ε₁ (p, q) = 1` and `ε₂ (p, q) = ε p`: this is `p.negOnePow` for
cochain complexes indexed by `ℤ` and `(-1) ^ p` for chain complexes indexed by `ℕ`. Mathlib's
`HomologicalComplex.monoidalCategoryStruct`, under the conditions on all graded objects listed in
the implementation notes, takes `tensorObj X Y` as the tensor product `X ⊗ Y`. The full monoidal
instance `HomologicalComplex.monoidalCategory` assumes further conditions, and when it is available
its tensor product is this same `X ⊗ Y`. This file records the resulting differential on a
homogeneous summand, `d (x ⊗ y) = d x ⊗ y + ε p • x ⊗ d y` for `x` of degree `p`, in any monoidal
preadditive category. For complexes of any shape with tensor signs it is a rewrite rule that
applies when both factors have a differential out of their degrees, `c.Rel p p'` and `c.Rel q q'`,
and both land in the same total degree `j'`, that is `p' + q = j'` and `p + q' = j'`. Two boundary
rules cover a summand where one factor has no differential out of its degree, such as degree `0`
of a chain complex indexed by `ℕ`: only the other term remains. For cochain complexes indexed by
`ℤ`, the sign is evaluated to `(-1)^p`. For chain complexes indexed by `ℕ`, the differential is
also given as its two parts `HomologicalComplex.mapBifunctor.D₁` and
`HomologicalComplex.mapBifunctor.D₂`, where a part vanishes on a summand whose factor of degree
zero it would differentiate.

## Main results

* `HomologicalComplex.ιTensorObj_d_of_rel`: the differential of `HomologicalComplex.tensorObj X Y`
  restricted to the summand `X.X p ⊗ Y.X q`, for complexes of any shape `c` with tensor signs whose
  tensor product exists, given `c.Rel p p'` and `c.Rel q q'` with `p' + q = j'` and `p + q' = j'`
  for the target degree `j'`.
* `HomologicalComplex.ιTensorObj_d_of_not_rel_left` and
  `HomologicalComplex.ιTensorObj_d_of_not_rel_right`: the same differential on a summand where the
  first, respectively second, factor has no differential out of its degree.
* `HomologicalComplex.ιTensorObj_d`: the differential of `HomologicalComplex.tensorObj X Y`
  restricted to the summand `X.X p ⊗ Y.X q`, for cochain complexes indexed by `ℤ` whose tensor
  product exists.
* `HomologicalComplex.tensor_d`: the differential of the monoidal tensor product `X ⊗ Y` is that
  of `HomologicalComplex.tensorObj X Y`, for complexes of any shape with tensor signs.
* `HomologicalComplex.ιTensorObj_tensor_d` and `HomologicalComplex.ιTensorObj_tensor_d'`: the
  formula for the monoidal tensor product `X ⊗ Y` of cochain complexes indexed by `ℤ`, through
  `HomologicalComplex.tensor_d`; the primed form takes arbitrary names for the successor degrees.
* `ChainComplex.ιTensorObj_D₁_succ`, `ChainComplex.ιTensorObj_D₁_zero`,
  `ChainComplex.ιTensorObj_D₂_succ` and `ChainComplex.ιTensorObj_D₂_zero`: the two parts of the
  differential of `HomologicalComplex.tensorObj K₁ K₂` on a homogeneous summand, for chain
  complexes indexed by `ℕ` whose tensor product exists.

## Implementation notes

The rules for `HomologicalComplex.tensorObj X Y` only assume that the tensor product of the given
pair of complexes exists, `[X.HasTensor Y]`. A monoidal structure on all complexes needs much
more, and it can fail where pairwise tensor products exist: for bounded complexes of
finite-dimensional vector spaces, the tensor product of two arbitrary graded objects can need
infinite coproducts. The corollaries `HomologicalComplex.ιTensorObj_tensor_d` and
`HomologicalComplex.ιTensorObj_tensor_d'` restate only the specializations to cochain complexes
indexed by `ℤ` for `X ⊗ Y` in Mathlib's `HomologicalComplex.monoidalCategoryStruct`: the first is
`HomologicalComplex.ιTensorObj_d`, the second `HomologicalComplex.ιTensorObj_d_of_rel` at
`ComplexShape.up ℤ` with the sign evaluated. They exist because `rw` and `simp` do not see through
`X ⊗ Y` to `HomologicalComplex.tensorObj X Y`; for other shapes, rewrite with
`HomologicalComplex.tensor_d`, which records that identification for complexes of any shape. Their
section variables are exactly the instances that structure takes: a zero object, the coproducts
`GradedObject.HasTensor`, preservation of the initial object by `- ⊗ X₂`, and the conditions
`GradedObject.HasGoodTensor₁₂Tensor` and `GradedObject.HasGoodTensorTensor₂₃`. For `ModuleCat R`,
instance search finds all of them once `Mathlib.Algebra.Category.ModuleCat.Colimits`,
`Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed` and
`Mathlib.CategoryTheory.Monoidal.Closed.Braided` are imported.

The unprimed cochain formulas are `simp` lemmas, derived from
`HomologicalComplex.ιTensorObj_d_of_rel`, which needs the target degrees as arguments. That lemma,
the two boundary rules and the primed cochain formula, whose successor degrees are arbitrary, are
meant to be passed explicitly to `rw` or `simp only` with the hypotheses that fix those degrees.
-/

public section

open CategoryTheory Limits MonoidalCategory

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]

namespace HomologicalComplex

section HasTensor

section Shape

variable {I : Type*} [AddMonoid I] [DecidableEq I] {c : ComplexShape I} [c.TensorSigns]
  (X Y : HomologicalComplex C c) [X.HasTensor Y]

/-- The differential of the tensor product `HomologicalComplex.tensorObj X Y` of two complexes of
any shape with tensor signs, on the summand `X.X p ⊗ Y.X q`, is the sum of the two factor
differentials towards degrees `p'` and `q'`, with the sign `c.ε p` on the second term. It applies
when both factors have a differential out of their degrees, `c.Rel p p'` and `c.Rel q q'`, and both
land in the target degree `j'`; where one factor has none, use
`HomologicalComplex.ιTensorObj_d_of_not_rel_left` or
`HomologicalComplex.ιTensorObj_d_of_not_rel_right`. -/
@[reassoc]
lemma ιTensorObj_d_of_rel {p q j p' q' j' : I} (hpq : p + q = j) (hp : c.Rel p p')
    (hq : c.Rel q q') (hp' : p' + q = j') (hq' : p + q' = j') :
    ιTensorObj X Y p q j hpq ≫ (tensorObj X Y).d j j' =
      (X.d p p' ▷ Y.X q) ≫ ιTensorObj X Y p' q j' hp' +
        c.ε p • ((X.X p ◁ Y.d q q') ≫ ιTensorObj X Y p q' j' hq') := by
  simp [mapBifunctor.d_eq, mapBifunctor.d₁_eq X Y _ c hp q j' hp',
    mapBifunctor.d₂_eq X Y _ c p hq j' hq']

/-- The differential of the tensor product `HomologicalComplex.tensorObj X Y` on the summand
`X.X p ⊗ Y.X q`, when the first factor has no differential out of degree `p`: only the
differential of the second factor towards degree `q'` remains, with the sign `c.ε p`. -/
@[reassoc]
lemma ιTensorObj_d_of_not_rel_left {p q j q' j' : I} (hpq : p + q = j)
    (hp : ¬ c.Rel p (c.next p)) (hq : c.Rel q q') (hq' : p + q' = j') :
    ιTensorObj X Y p q j hpq ≫ (tensorObj X Y).d j j' =
      c.ε p • ((X.X p ◁ Y.d q q') ≫ ιTensorObj X Y p q' j' hq') := by
  simp [mapBifunctor.d_eq, mapBifunctor.d₁_eq_zero X Y _ c p q j' hp,
    mapBifunctor.d₂_eq X Y _ c p hq j' hq']

/-- The differential of the tensor product `HomologicalComplex.tensorObj X Y` on the summand
`X.X p ⊗ Y.X q`, when the second factor has no differential out of degree `q`: only the
differential of the first factor towards degree `p'` remains. -/
@[reassoc]
lemma ιTensorObj_d_of_not_rel_right {p q j p' j' : I} (hpq : p + q = j) (hp : c.Rel p p')
    (hq : ¬ c.Rel q (c.next q)) (hp' : p' + q = j') :
    ιTensorObj X Y p q j hpq ≫ (tensorObj X Y).d j j' =
      (X.d p p' ▷ Y.X q) ≫ ιTensorObj X Y p' q j' hp' := by
  simp [mapBifunctor.d_eq, mapBifunctor.d₁_eq X Y _ c hp q j' hp',
    mapBifunctor.d₂_eq_zero X Y _ c p q j' hq]

end Shape

variable (X Y : CochainComplex C ℤ) [X.HasTensor Y]

/-- The differential of the tensor product `HomologicalComplex.tensorObj X Y` of two cochain
complexes on a homogeneous summand is the sum of the two factor differentials, with the Koszul
sign on the second term. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_d (p q j : ℤ) (hpq : p + q = j) :
    ιTensorObj X Y p q j hpq ≫ (tensorObj X Y).d j (j + 1) =
      (X.d p (p + 1) ▷ Y.X q) ≫ ιTensorObj X Y (p + 1) q (j + 1) (by omega) +
        p.negOnePow • ((X.X p ◁ Y.d q (q + 1)) ≫ ιTensorObj X Y p (q + 1) (j + 1) (by omega)) := by
  simpa only [ComplexShape.ε_up_ℤ] using ιTensorObj_d_of_rel X Y hpq (p' := p + 1)
    (q' := q + 1) (j' := j + 1) rfl rfl (by omega) (by omega)

end HasTensor

section Monoidal

variable {I : Type*} [AddMonoid I] [DecidableEq I] {c : ComplexShape I} [c.TensorSigns]
  [HasZeroObject C] [∀ X₁ X₂ : GradedObject I C, GradedObject.HasTensor X₁ X₂]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁ X₂ X₃ : GradedObject I C, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject I C, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- The differential of the monoidal tensor product `X ⊗ Y` of
`HomologicalComplex.monoidalCategoryStruct` is the differential of
`HomologicalComplex.tensorObj X Y`. -/
lemma tensor_d (X Y : HomologicalComplex C c) (i j : I) :
    (X ⊗ Y).d i j = (tensorObj X Y).d i j :=
  (rfl)

end Monoidal

variable [HasZeroObject C] [∀ X₁ X₂ : GradedObject ℤ C, GradedObject.HasTensor X₁ X₂]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- `HomologicalComplex.ιTensorObj_d` for the monoidal tensor product `X ⊗ Y` of
`HomologicalComplex.monoidalCategoryStruct`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_tensor_d (X Y : CochainComplex C ℤ) (p q j : ℤ) (hpq : p + q = j) :
    ιTensorObj X Y p q j hpq ≫ (X ⊗ Y).d j (j + 1) =
      (X.d p (p + 1) ▷ Y.X q) ≫ ιTensorObj X Y (p + 1) q (j + 1) (by omega) +
        p.negOnePow • ((X.X p ◁ Y.d q (q + 1)) ≫ ιTensorObj X Y p (q + 1) (j + 1) (by omega)) := by
  rw [tensor_d]
  exact ιTensorObj_d X Y p q j hpq

/-- `HomologicalComplex.ιTensorObj_d_of_rel` for the monoidal tensor product `X ⊗ Y` of
`HomologicalComplex.monoidalCategoryStruct` of cochain complexes indexed by `ℤ`, with the sign
evaluated: `HomologicalComplex.ιTensorObj_tensor_d` with arbitrary indices `p'`, `q'` and `j'` for
the successors of `p`, `q` and `j`. Unlike `HomologicalComplex.ιTensorObj_tensor_d`, it is not a
`simp` lemma: pass it explicitly to `rw` or `simp only`. -/
@[reassoc]
lemma ιTensorObj_tensor_d' (X Y : CochainComplex C ℤ) {p q j p' q' j' : ℤ}
    (hpq : p + q = j) (hp : p + 1 = p') (hq : q + 1 = q') (hj : j + 1 = j') :
    ιTensorObj X Y p q j hpq ≫ (X ⊗ Y).d j j' =
      (X.d p p' ▷ Y.X q) ≫ ιTensorObj X Y p' q j' (by omega) +
        p.negOnePow • ((X.X p ◁ Y.d q q') ≫ ιTensorObj X Y p q' j' (by omega)) := by
  rw [tensor_d]
  simpa only [ComplexShape.ε_up_ℤ] using ιTensorObj_d_of_rel X Y hpq hp hq (by omega) (by omega)

end HomologicalComplex

namespace ChainComplex

open HomologicalComplex

variable (K₁ K₂ : ChainComplex C ℕ) [K₁.HasTensor K₂]

/-- The first part of the differential of a tensor product of chain complexes, on a summand whose
first factor has positive degree, is the differential of the first factor. -/
@[reassoc]
lemma ιTensorObj_D₁_succ (r s n : ℕ) (h : r + 1 + s = n + 1) :
    ιTensorObj K₁ K₂ (r + 1) s (n + 1) h ≫
        mapBifunctor.D₁ K₁ K₂ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n =
      (K₁.d (r + 1) r ▷ K₂.X s) ≫ ιTensorObj K₁ K₂ r s n (by omega) := by
  have hr : (ComplexShape.down ℕ).Rel (r + 1) r := by simp
  rw [mapBifunctor.ι_D₁, mapBifunctor.d₁_eq _ _ _ _
    hr _ _ (by simp; omega)]
  simp

/-- The first part of the differential of a tensor product of chain complexes vanishes on a
summand whose first factor has degree zero. -/
@[reassoc]
lemma ιTensorObj_D₁_zero (n : ℕ) :
    ιTensorObj K₁ K₂ 0 (n + 1) (n + 1) (by omega) ≫
        mapBifunctor.D₁ K₁ K₂ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n = 0 := by
  rw [mapBifunctor.ι_D₁, mapBifunctor.d₁_eq_zero]
  simp

/-- The second part of the differential of a tensor product of chain complexes, on a summand whose
second factor has positive degree, is the differential of the second factor with the Koszul sign
`(-1)^r` of the degree `r` of the first factor. -/
@[reassoc]
lemma ιTensorObj_D₂_succ (r s n : ℕ) (h : r + (s + 1) = n + 1) :
    ιTensorObj K₁ K₂ r (s + 1) (n + 1) h ≫
        mapBifunctor.D₂ K₁ K₂ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n =
      ((-1 : ℤ) ^ r) •
        (K₁.X r ◁ K₂.d (s + 1) s) ≫ ιTensorObj K₁ K₂ r s n (by omega) := by
  have hs : (ComplexShape.down ℕ).Rel (s + 1) s := by simp
  rw [mapBifunctor.ι_D₂, mapBifunctor.d₂_eq _ _ _ _ _
    hs _ (by simp; omega)]
  simp [Units.smul_def]

/-- The second part of the differential of a tensor product of chain complexes vanishes on a
summand whose second factor has degree zero. -/
@[reassoc]
lemma ιTensorObj_D₂_zero (n : ℕ) :
    ιTensorObj K₁ K₂ (n + 1) 0 (n + 1) (by omega) ≫
        mapBifunctor.D₂ K₁ K₂ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n = 0 := by
  rw [mapBifunctor.ι_D₂, mapBifunctor.d₂_eq_zero]
  simp

end ChainComplex
