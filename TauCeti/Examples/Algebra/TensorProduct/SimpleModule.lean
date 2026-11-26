/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.RingTheory.SimpleModule.Rank
public import TauCeti.Algebra.TensorProduct.SimpleModule
public import TauCeti.RingTheory.Semisimple.MatrixDivisionRing

/-!
# Checks for the factorization of simple modules over a tensor product of matrix algebras

Checks for the finite-dimensional step of Flath's factorization
(`TauCeti.exists_tensorProduct_equiv_of_isSimpleModule`, existence, and
`TauCeti.nonempty_linearEquiv_of_tensorPairAction_equiv`, uniqueness) with the matrix algebras
`A₁ = M_r(ℂ)` and `A₂ = M_s(ℂ)`:

* the standard modules `ℂ^r` and `ℂ^s` are simple (`TauCeti.Matrix.isSimpleModule_pi`) and their
  exterior tensor product has dimension `r s`
  (`TauCeti.FiniteCornerChecks.finrank_standard_tensor`);
* taking `A₂ = ℂ`, every simple second factor is one-dimensional
  (`TauCeti.FiniteCornerChecks.finrank_eq_one_of_isSimpleModule_complex`);
* every factorization `V ⊗ W ≅ ℂ^r ⊗ ℂ^s` of the standard module of `M_r(ℂ) ⊗ M_s(ℂ)` into simple
  factors has `dim V = r` and `dim W = s`
  (`TauCeti.FiniteCornerChecks.finrank_factors_of_equiv_standard`).
-/

public section

open scoped TensorProduct

namespace TauCeti.FiniteCornerChecks

open Module

/-- The standard modules of `M_r(ℂ)` and `M_s(ℂ)` are simple. -/
example (r : ℕ) [NeZero r] : IsSimpleModule (Matrix (Fin r) (Fin r) ℂ) (Fin r → ℂ) :=
  inferInstance

/-- The standard modules of `M_r(ℂ)` and `M_s(ℂ)` tensor to dimension `r s`. -/
theorem finrank_standard_tensor (r s : ℕ) :
    finrank ℂ ((Fin r → ℂ) ⊗[ℂ] (Fin s → ℂ)) = r * s := by
  simp [finrank_tensorProduct]

/-- Taking `A₂ = ℂ`: a simple module over `ℂ` is one-dimensional, so the second factor of a
factorization over `A₁ ⊗[ℂ] ℂ` is a line. -/
theorem finrank_eq_one_of_isSimpleModule_complex {W : Type*} [AddCommGroup W] [Module ℂ W]
    [IsSimpleModule ℂ W] : finrank ℂ W = 1 :=
  isSimpleModule_iff_finrank_eq_one.mp ‹_›

/-- **The factors of the standard module of `M_r(ℂ) ⊗ M_s(ℂ)` have dimensions `r` and `s`.**
If simple modules `V` over `M_r(ℂ)` and `W` over `M_s(ℂ)` have exterior tensor product
isomorphic to `ℂ^r ⊗ ℂ^s` as `M_r(ℂ) ⊗ M_s(ℂ)`-modules, then `dim V = r` and `dim W = s`. -/
theorem finrank_factors_of_equiv_standard {r s : ℕ} [NeZero r] [NeZero s]
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [Module (Matrix (Fin r) (Fin r) ℂ) V]
    [IsScalarTower ℂ (Matrix (Fin r) (Fin r) ℂ) V] [IsSimpleModule (Matrix (Fin r) (Fin r) ℂ) V]
    [AddCommGroup W] [Module ℂ W] [Module (Matrix (Fin s) (Fin s) ℂ) W]
    [IsScalarTower ℂ (Matrix (Fin s) (Fin s) ℂ) W] [IsSimpleModule (Matrix (Fin s) (Fin s) ℂ) W]
    (e : V ⊗[ℂ] W ≃ₗ[ℂ] (Fin r → ℂ) ⊗[ℂ] (Fin s → ℂ))
    (he : ∀ (t : Matrix (Fin r) (Fin r) ℂ ⊗[ℂ] Matrix (Fin s) (Fin s) ℂ) x,
      e (BialgebraModule.tensorPairAction ℂ V W t x) =
        BialgebraModule.tensorPairAction ℂ (Fin r → ℂ) (Fin s → ℂ) t (e x)) :
    finrank ℂ V = r ∧ finrank ℂ W = s := by
  obtain ⟨⟨eV⟩, ⟨eW⟩⟩ := nonempty_linearEquiv_of_tensorPairAction_equiv e he
  exact ⟨by simpa using (eV.restrictScalars ℂ).finrank_eq,
    by simpa using (eW.restrictScalars ℂ).finrank_eq⟩

end TauCeti.FiniteCornerChecks
