/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Basic
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.SplitK0.Matrix

/-!
# Matrix Morita invariance on algebraic `K₀`

For a ring `R : Type u` and a nonempty finite index type `ι : Type v` with decidable equality,
`TauCeti.KZero.matrixEquiv R ι` provides the canonical universe-polymorphic isomorphism
`KZero.{u} R ≃+ KZero.{max u v} (Matrix ι ι R)` sending `|ι| • [R]` to `[M_ι(R)]` and agreeing
with `ModuleCat.matrixEquivalence Rᵐᵒᵖ i` composed with `RingEquiv.mopMatrix`.

## References

* C. A. Weibel, *The K-book*, Chapter II, §2.
-/

public section

open CategoryTheory

universe u v

namespace TauCeti.KZero

section Matrix

variable (R : Type u) [Ring R] (ι : Type v) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **Matrix Morita invariance:** canonical isomorphism
`KZero.{u} R ≃+ KZero.{max u v} (Matrix ι ι R)` sending `|ι| • [R]` to `[M_ι(R)]`. -/
noncomputable def matrixEquiv : KZero.{u} R ≃+ KZero.{max u v} (Matrix ι ι R) :=
  (finiteProjectiveModulesMatrixSplitK0Equiv Rᵐᵒᵖ ι).trans
    (RingEquiv.mopMatrix (m := ι) (α := R)).finiteProjectiveModulesSplitK0Equiv

theorem matrixEquiv_apply (x : KZero.{u} R) :
    matrixEquiv R ι x = (RingEquiv.mopMatrix (m := ι) (α := R)).finiteProjectiveModulesSplitK0Equiv
      (finiteProjectiveModulesMatrixSplitK0Equiv Rᵐᵒᵖ ι x) := (rfl)

@[simp] theorem matrixEquiv_of (P) : matrixEquiv R ι (SplitK0.of.{u} P) = SplitK0.of.{max u v}
    ((RingEquiv.mopMatrix (m := ι) (α := R)).toRingHom.finiteProjectiveModulesExtendScalars.obj
      ((finiteProjectiveModulesToMatrixFunctor Rᵐᵒᵖ ι).obj P)) := by simp [matrixEquiv_apply]

@[simp] theorem matrixEquiv_card_nsmul_regular :
    matrixEquiv R ι (Fintype.card ι • regular R) = regular (Matrix ι ι R) := by
  simp [matrixEquiv_apply, regular_def]

end Matrix

/-- For every `i : ι`, `matrixEquiv` agrees with `ModuleCat.matrixEquivalence` composed with
`RingEquiv.mopMatrix`. -/
theorem matrixEquiv_eq (R : Type u) [Ring R] (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (i : ι) : matrixEquiv R ι =
      (ModuleCat.matrixEquivalence Rᵐᵒᵖ (ι := ι) i).finiteProjectiveModulesSplitK0Equiv.trans
        (RingEquiv.mopMatrix (m := ι) (α := R)).finiteProjectiveModulesSplitK0Equiv := by
  rw [matrixEquiv, finiteProjectiveModulesMatrixSplitK0Equiv_eq Rᵐᵒᵖ ι i]

end TauCeti.KZero
