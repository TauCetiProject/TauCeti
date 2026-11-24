/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Basic
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.SplitK0.Matrix

/-!
# Algebraic `K₀` of a matrix ring

For a ring `R` and a nonempty finite index type `ι` with decidable equality,
`TauCeti.KZero.matrixEquiv R ι` provides the canonical universe-polymorphic isomorphism
`KZero.{u} R ≃+ KZero.{max u v} (Matrix ι ι R)` sending `|ι| • [R]` to `[M_ι(R)]`, and agreeing
with `ModuleCat.matrixEquivalence Rᵐᵒᵖ i` composed with restriction of scalars along
`(RingEquiv.mopMatrix (m := ι) (α := R)).symm` when `ι` lives in the universe of `R`.

## Main definitions

* `TauCeti.KZero.matrixEquiv R ι`: for a nonempty finite index type `ι` with decidable equality,
  canonical universe-polymorphic isomorphism `KZero.{u} R ≃+ KZero.{max u v} (Matrix ι ι R)` for
  right-module algebraic `K₀`.

## Main results

* `TauCeti.KZero.matrixEquiv_card_nsmul_regular` and `TauCeti.KZero.matrixEquiv_eq`:
  `matrixEquiv` sends `|ι| • [R]` to `[Matrix ι ι R]` and, when `ι` lives in the universe of `R`,
  agrees with `ModuleCat.matrixEquivalence` composed with restriction of scalars along
  `(RingEquiv.mopMatrix (m := ι) (α := R)).symm`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2,
  Example 2.1.2 (Morita invariance of `K₀` and `K₀(Mₙ(R)) ≅ K₀(R)`), p. 69.
* T. Y. Lam, *Lectures on Modules and Rings*, GTM 189 (1999), §17B, for the matrix Morita
  equivalence.
-/

public section

namespace TauCeti.KZero

open CategoryTheory

universe u v

section Matrix

variable (R : Type u) [Ring R] (ι : Type v) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **Matrix Morita invariance:** for a nonempty finite index type `ι` with decidable equality, the
canonical isomorphism `KZero.{u} R ≃+ KZero.{max u v} (Matrix ι ι R)` sending `|ι| • [R]` to
`[M_ι(R)]`. -/
noncomputable def matrixEquiv : KZero.{u} R ≃+ KZero.{max u v} (Matrix ι ι R) :=
  (finiteProjectiveModulesMatrixSplitK0Equiv Rᵐᵒᵖ ι).trans
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (RingEquiv.mopMatrix (m := ι) (α := R))).symm.finiteProjectiveModulesSplitK0Equiv

theorem matrixEquiv_apply (x : KZero.{u} R) :
    matrixEquiv R ι x =
      SplitK0.map.{max u v, max u v}
        (RingEquiv.mopMatrix (m := ι) (α := R)).toRingHom.finiteProjectiveModulesExtendScalars
        (finiteProjectiveModulesMatrixSplitK0Equiv Rᵐᵒᵖ ι x) :=
  (DFunLike.congr_fun
    (RingEquiv.splitK0Map_finiteProjectiveModulesExtendScalars_eq_restrictScalars
      (RingEquiv.mopMatrix (m := ι) (α := R))) _).symm

@[simp] theorem matrixEquiv_of (P) : matrixEquiv R ι (SplitK0.of.{u} P) = SplitK0.of.{max u v}
    ((RingEquiv.mopMatrix (m := ι) (α := R)).toRingHom.finiteProjectiveModulesExtendScalars.obj
      ((finiteProjectiveModulesToMatrixFunctor Rᵐᵒᵖ ι).obj P)) := by simp [matrixEquiv_apply]

@[simp] theorem matrixEquiv_card_nsmul_regular :
    matrixEquiv R ι (Fintype.card ι • regular R) = regular (Matrix ι ι R) := by
  simp [matrixEquiv_apply, regular_def]

end Matrix

/-- For every `i : ι`, `matrixEquiv` agrees with `ModuleCat.matrixEquivalence` composed with
restriction of scalars along `(RingEquiv.mopMatrix (m := ι) (α := R)).symm`. -/
theorem matrixEquiv_eq (R : Type u) [Ring R] (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (i : ι) : matrixEquiv R ι =
      (ModuleCat.matrixEquivalence Rᵐᵒᵖ (ι := ι) i).finiteProjectiveModulesSplitK0Equiv.trans
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          (RingEquiv.mopMatrix (m := ι) (α := R))).symm.finiteProjectiveModulesSplitK0Equiv := by
  rw [matrixEquiv, finiteProjectiveModulesMatrixSplitK0Equiv_eq Rᵐᵒᵖ ι i]

end TauCeti.KZero
