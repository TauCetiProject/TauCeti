/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# Exactness of coaugmented cochain complexes

For a nonnegative cochain complex `K` coaugmented from `X` by `ι : X[0] ⟶ K`, a
quasi-isomorphism in degree `0` makes `X ⟶ K⁰ ⟶ K¹` exact with `X ⟶ K⁰` a monomorphism, and a
quasi-isomorphism in degree `n + 1` makes `K` exact there. No injectivity of the terms of `K` is
needed. This is the cochain counterpart of `TauCeti/Algebra/Homology/Single/Cokernel.lean`.
The coaugmentations are natural in morphisms of coaugmented complexes
(`CochainComplex.fromSingle₀Equiv_comp_f_zero`).

The argument uses Mathlib's `ShortComplex.quasiIso_iff_of_zeros`.
-/

public section

open CategoryTheory Limits HomologicalComplex

universe v u

namespace CochainComplex

section

variable {C : Type u} [Category.{v} C] [Abelian C] {K : CochainComplex C ℕ} {X : C}
  (ι : (single₀ C).obj X ⟶ K)

private lemma exact_and_mono_f_zero_of_quasiIsoAt [QuasiIsoAt ι 0] :
    (ShortComplex.mk (ι.f 0) (K.d 0 1)
      (HomologicalComplex.single_f_d ι 1)).Exact ∧ Mono (ι.f 0) :=
  (ShortComplex.quasiIso_iff_of_zeros ((shortComplexFunctor' C (ComplexShape.up ℕ) 0 0 1).map ι)
    (single_obj_d (ComplexShape.up ℕ) 0 X 0 0) (single_obj_d (ComplexShape.up ℕ) 0 X 0 1)
    (K.shape _ _ (by simp))).mp ((quasiIsoAt₀_iff ι).mp inferInstance)

/-- A quasi-isomorphism `ι : X[0] ⟶ K` in degree `0` makes `X ⟶ K⁰ ⟶ K¹` exact. -/
lemma exact_f_zero_of_quasiIsoAt [QuasiIsoAt ι 0] :
    (ShortComplex.mk (ι.f 0) (K.d 0 1) (HomologicalComplex.single_f_d ι 1)).Exact :=
  (exact_and_mono_f_zero_of_quasiIsoAt ι).1

/-- A quasi-isomorphism `ι : X[0] ⟶ K` in degree `0` embeds `X` into `K⁰`. -/
instance mono_f_zero_of_quasiIsoAt [QuasiIsoAt ι 0] : Mono (ι.f 0) :=
  (exact_and_mono_f_zero_of_quasiIsoAt ι).2

/-- A morphism `ι : X[0] ⟶ K` which is a quasi-isomorphism in a positive degree makes `K` exact
there. -/
lemma exactAt_succ_of_quasiIsoAt (n : ℕ) [QuasiIsoAt ι (n + 1)] : K.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt ι (n + 1) (exactAt_succ_single_obj _ _)]
  infer_instance

/-- A morphism `ι : X[0] ⟶ K` which is a quasi-isomorphism in degree `n + 1` makes
`Kⁿ ⟶ Kⁿ⁺¹ ⟶ Kⁿ⁺²` exact. -/
lemma exact_succ_of_quasiIsoAt (n : ℕ) [QuasiIsoAt ι (n + 1)] :
    (ShortComplex.mk _ _ (K.d_comp_d n (n + 1) (n + 2))).Exact :=
  (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).1 (exactAt_succ_of_quasiIsoAt ι n)

end

section Naturality

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {K L : CochainComplex C ℕ} {X Y : C} {ι : (single₀ C).obj X ⟶ K} {ι' : (single₀ C).obj Y ⟶ L}
  {f : X ⟶ Y} {φ : K ⟶ L}

/-- Naturality of coaugmentations: if a morphism of complexes `φ : K ⟶ L` lies over
`f : X ⟶ Y`, in the sense that `ι ≫ φ = f[0] ≫ ι'`, then the coaugmentations
`X ⟶ K⁰` and `Y ⟶ L⁰` commute with `f` and `φ⁰`. -/
lemma fromSingle₀Equiv_comp_f_zero (hφ : ι ≫ φ = (single₀ C).map f ≫ ι') :
    (fromSingle₀Equiv K X ι).1 ≫ φ.f 0 = f ≫ (fromSingle₀Equiv L Y ι').1 := by
  simpa using congrArg (fun g ↦ HomologicalComplex.Hom.f g 0) hφ

end Naturality

end CochainComplex
