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
homogeneous summand, `d (x ⊗ y) = d x ⊗ y + (-1)^p x ⊗ d y` for `x` of degree `p`, in any monoidal
preadditive category: as a single rewrite rule for cochain complexes indexed by `ℤ`, and as its two
parts `HomologicalComplex.mapBifunctor.D₁` and `HomologicalComplex.mapBifunctor.D₂` for chain
complexes indexed by `ℕ`, where a part vanishes on a summand whose factor of degree zero it would
differentiate.

## Main results

* `HomologicalComplex.ιTensorObj_d`: the differential of `HomologicalComplex.tensorObj X Y`
  restricted to the summand `X.X p ⊗ Y.X q`, for cochain complexes indexed by `ℤ` whose tensor
  product exists, and `HomologicalComplex.ιTensorObj_d'`, the same formula with arbitrary names
  for the successor degrees.
* `HomologicalComplex.ιTensorObj_tensor_d` and `HomologicalComplex.ιTensorObj_tensor_d'`: the same
  two formulas for the monoidal tensor product `X ⊗ Y`, through
  `HomologicalComplex.tensor_d`, which identifies its differential with that of
  `HomologicalComplex.tensorObj X Y`.
* `ChainComplex.ιTensorObj_D₁_succ`, `ChainComplex.ιTensorObj_D₁_zero`,
  `ChainComplex.ιTensorObj_D₂_succ` and `ChainComplex.ιTensorObj_D₂_zero`: the two parts of the
  differential of `HomologicalComplex.tensorObj K₁ K₂` on a homogeneous summand, for chain
  complexes indexed by `ℕ` whose tensor product exists.

## Implementation notes

`HomologicalComplex.ιTensorObj_d` and `HomologicalComplex.ιTensorObj_d'` only assume that the
tensor product of the given pair of complexes exists, `[X.HasTensor Y]`. A monoidal structure on
all complexes needs much more, and it can fail where pairwise tensor products exist: for bounded
complexes of finite-dimensional vector spaces, the tensor product of two arbitrary graded objects
can need infinite coproducts. The corollaries `HomologicalComplex.ιTensorObj_tensor_d` and
`HomologicalComplex.ιTensorObj_tensor_d'` restate them for `X ⊗ Y` in Mathlib's
`HomologicalComplex.monoidalCategoryStruct`, because `rw` and `simp` do not see through `X ⊗ Y` to
`HomologicalComplex.tensorObj X Y`. Their section variables are exactly the instances that
structure takes: a zero object, the coproducts `GradedObject.HasTensor`, preservation of the
initial object by `- ⊗ X₂`, and the conditions `GradedObject.HasGoodTensor₁₂Tensor` and
`GradedObject.HasGoodTensorTensor₂₃`. For `ModuleCat R`, instance search finds all of them once
`Mathlib.Algebra.Category.ModuleCat.Colimits`, `Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed`
and `Mathlib.CategoryTheory.Monoidal.Closed.Braided` are imported.

The unprimed formulas are `simp` lemmas. The primed ones, whose successor degrees are arbitrary,
are meant to be passed explicitly to `rw` or `simp only` with the equations that fix those degrees.
-/

public section

open CategoryTheory Limits MonoidalCategory

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]

namespace HomologicalComplex

section HasTensor

variable (X Y : CochainComplex C ℤ) [X.HasTensor Y]

/-- The differential of the tensor product `HomologicalComplex.tensorObj X Y` of two cochain
complexes on a homogeneous summand is the sum of the two factor differentials, with the Koszul
sign on the second term. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_d (p q j : ℤ) (hpq : p + q = j) :
    ιTensorObj X Y p q j hpq ≫ (tensorObj X Y).d j (j + 1) =
      (X.d p (p + 1) ▷ Y.X q) ≫ ιTensorObj X Y (p + 1) q (j + 1) (by omega) +
        p.negOnePow • ((X.X p ◁ Y.d q (q + 1)) ≫ ιTensorObj X Y p (q + 1) (j + 1) (by omega)) := by
  simp [mapBifunctor.d_eq,
    -- `dsimp` unfolds the total degree `ComplexShape.π` of the target summands to a sum.
    mapBifunctor.d₁_eq X Y _ (.up ℤ) (ComplexShape.up_mk p (p + 1) rfl) q (j + 1)
      (by dsimp; omega),
    mapBifunctor.d₂_eq X Y _ (.up ℤ) p (ComplexShape.up_mk q (q + 1) rfl) (j + 1)
      (by dsimp; omega)]

/-- `HomologicalComplex.ιTensorObj_d` with arbitrary indices `p'`, `q'` and `j'` for the
successors of `p`, `q` and `j`. -/
@[reassoc]
lemma ιTensorObj_d' {p q j p' q' j' : ℤ}
    (hpq : p + q = j) (hp : p + 1 = p') (hq : q + 1 = q') (hj : j + 1 = j') :
    ιTensorObj X Y p q j hpq ≫ (tensorObj X Y).d j j' =
      (X.d p p' ▷ Y.X q) ≫ ιTensorObj X Y p' q j' (by omega) +
        p.negOnePow • ((X.X p ◁ Y.d q q') ≫ ιTensorObj X Y p q' j' (by omega)) := by
  subst hp hq hj
  exact ιTensorObj_d X Y p q j hpq

end HasTensor

variable [HasZeroObject C] [∀ X₁ X₂ : GradedObject ℤ C, GradedObject.HasTensor X₁ X₂]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- The differential of the monoidal tensor product `X ⊗ Y` of
`HomologicalComplex.monoidalCategoryStruct` is the differential of
`HomologicalComplex.tensorObj X Y`. -/
lemma tensor_d (X Y : CochainComplex C ℤ) (i j : ℤ) : (X ⊗ Y).d i j = (tensorObj X Y).d i j :=
  (rfl)

/-- `HomologicalComplex.ιTensorObj_d` for the monoidal tensor product `X ⊗ Y` of
`HomologicalComplex.monoidalCategoryStruct`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_tensor_d (X Y : CochainComplex C ℤ) (p q j : ℤ) (hpq : p + q = j) :
    ιTensorObj X Y p q j hpq ≫ (X ⊗ Y).d j (j + 1) =
      (X.d p (p + 1) ▷ Y.X q) ≫ ιTensorObj X Y (p + 1) q (j + 1) (by omega) +
        p.negOnePow • ((X.X p ◁ Y.d q (q + 1)) ≫ ιTensorObj X Y p (q + 1) (j + 1) (by omega)) := by
  rw [tensor_d]
  exact ιTensorObj_d X Y p q j hpq

/-- `HomologicalComplex.ιTensorObj_d'` for the monoidal tensor product `X ⊗ Y` of
`HomologicalComplex.monoidalCategoryStruct`. Unlike `HomologicalComplex.ιTensorObj_tensor_d`, it
is not a `simp` lemma: pass it explicitly to `rw` or `simp only`. -/
@[reassoc]
lemma ιTensorObj_tensor_d' (X Y : CochainComplex C ℤ) {p q j p' q' j' : ℤ}
    (hpq : p + q = j) (hp : p + 1 = p') (hq : q + 1 = q') (hj : j + 1 = j') :
    ιTensorObj X Y p q j hpq ≫ (X ⊗ Y).d j j' =
      (X.d p p' ▷ Y.X q) ≫ ιTensorObj X Y p' q j' (by omega) +
        p.negOnePow • ((X.X p ◁ Y.d q q') ≫ ιTensorObj X Y p q' j' (by omega)) := by
  rw [tensor_d]
  exact ιTensorObj_d' X Y hpq hp hq hj

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
