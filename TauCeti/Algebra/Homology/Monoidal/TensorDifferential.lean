/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# The differential of a tensor product of cochain complexes of modules

Mathlib's `HomologicalComplex.monoidalCategory`, instantiated at `ComplexShape.up ℤ`, totalizes
the degreewise tensor product of cochain complexes, with the tensor signs `ε₁ = 1` and
`ε₂ (p, q) = (-1)^p`.  This file records the resulting differential on a homogeneous summand,
`d (x ⊗ y) = d x ⊗ y + (-1)^p x ⊗ d y` for `x` of degree `p`, as a single rewrite rule.

## Main results

* `HomologicalComplex.ι_tensorObj_d`: the differential of `X ⊗ Y` restricted to the summand
  `X.X p ⊗ Y.X q`.

## Implementation notes

`Mathlib.CategoryTheory.Monoidal.Closed.Braided` is imported for the colimit-preservation
instances that make the tensor product of cochain complexes exist at all, exactly as in
`TauCeti/Algebra/Homology/Monoidal/Braiding.lean`.
-/

public section

open CategoryTheory Limits MonoidalCategory

universe v

namespace HomologicalComplex

variable {R : Type v} [CommRing R]

/-- The differential of a tensor product of cochain complexes on a homogeneous summand is the
sum of the two factor differentials, with the Koszul sign on the second term. -/
lemma ι_tensorObj_d (X Y : CochainComplex (ModuleCat.{v} R) ℤ) (p q j : ℤ)
    (hpq : p + q = j) :
    ιTensorObj X Y p q j hpq ≫ (X ⊗ Y).d j (j + 1) =
      ((curriedTensor (ModuleCat.{v} R)).map (X.d p (p + 1))).app (Y.X q) ≫
        ιTensorObj X Y (p + 1) q (j + 1) (by omega) +
      p.negOnePow •
        ((curriedTensor (ModuleCat.{v} R)).obj (X.X p)).map (Y.d q (q + 1)) ≫
          ιTensorObj X Y p (q + 1) (j + 1) (by omega) := by
  have hd : (X ⊗ Y).d j (j + 1) =
      mapBifunctor.D₁ X Y (curriedTensor (ModuleCat.{v} R))
          (ComplexShape.up ℤ) j (j + 1) +
        mapBifunctor.D₂ X Y (curriedTensor (ModuleCat.{v} R))
          (ComplexShape.up ℤ) j (j + 1) :=
    mapBifunctor.d_eq _ _ _ _ j (j + 1)
  rw [hd, Preadditive.comp_add,
    mapBifunctor.ι_D₁,
    mapBifunctor.d₁_eq _ _ _ _
      (ComplexShape.up_mk p (p + 1) rfl) q (j + 1) (by dsimp; omega),
    mapBifunctor.ι_D₂,
    mapBifunctor.d₂_eq _ _ _ _ p
      (ComplexShape.up_mk q (q + 1) rfl) (j + 1) (by dsimp; omega)]
  simp only [ComplexShape.ε₁_def, one_smul, ComplexShape.ε₂_def, ComplexShape.ε_up_ℤ]

end HomologicalComplex
