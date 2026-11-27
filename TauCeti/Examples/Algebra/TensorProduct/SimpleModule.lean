/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
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
  exterior tensor product has dimension `r s`;
* taking `A₂ = ℂ`, the existence theorem factors every finite-dimensional simple
  `M_r(ℂ) ⊗[ℂ] ℂ`-module as `V ⊗ W` with `V` a simple `M_r(ℂ)`-module and `W` a line;
* by the uniqueness theorem, every factorization `V ⊗ W ≅ ℂ^r ⊗ ℂ^s` of the standard module of
  `M_r(ℂ) ⊗ M_s(ℂ)` into simple factors has `dim V = r` and `dim W = s`
  (`TauCeti.FiniteCornerChecks.finrank_eq_and_finrank_eq_of_tensorProduct_equiv_fin_fun`).
-/

public section

open scoped TensorProduct

namespace TauCeti.FiniteCornerChecks

open Module

universe u

/-- The standard modules of `M_r(ℂ)` and `M_s(ℂ)` are simple. -/
example (r : ℕ) [NeZero r] : IsSimpleModule (Matrix (Fin r) (Fin r) ℂ) (Fin r → ℂ) :=
  inferInstance

/-- The standard modules of `M_r(ℂ)` and `M_s(ℂ)` tensor to dimension `r s`. -/
example (r s : ℕ) : finrank ℂ ((Fin r → ℂ) ⊗[ℂ] (Fin s → ℂ)) = r * s := by
  simp [finrank_tensorProduct]

/-- Taking `A₂ = ℂ`: a finite-dimensional simple `M_r(ℂ) ⊗[ℂ] ℂ`-module is the exterior tensor
product of a simple `M_r(ℂ)`-module and a one-dimensional `ℂ`-vector space. -/
example {r : ℕ} {M : Type u} [AddCommGroup M] [Module ℂ M]
    [Module (Matrix (Fin r) (Fin r) ℂ ⊗[ℂ] ℂ) M]
    [IsScalarTower ℂ (Matrix (Fin r) (Fin r) ℂ ⊗[ℂ] ℂ) M] [FiniteDimensional ℂ M]
    [IsSimpleModule (Matrix (Fin r) (Fin r) ℂ ⊗[ℂ] ℂ) M] :
    ∃ (V W : Type u) (_ : AddCommGroup V) (_ : Module ℂ V)
      (_ : Module (Matrix (Fin r) (Fin r) ℂ) V) (_ : IsScalarTower ℂ (Matrix (Fin r) (Fin r) ℂ) V)
      (_ : AddCommGroup W) (_ : Module ℂ W),
      IsSimpleModule (Matrix (Fin r) (Fin r) ℂ) V ∧ finrank ℂ W = 1 ∧
      ∃ e : V ⊗[ℂ] W ≃ₗ[ℂ] M, ∀ (t : Matrix (Fin r) (Fin r) ℂ ⊗[ℂ] ℂ) x,
        e (BialgebraModule.tensorPairAction ℂ V W t x) = t • e x := by
  obtain ⟨V, W, _, _, _, _, _, iW, jW, tW, hV, hW, -, -, e, he⟩ :=
    exists_tensorProduct_equiv_of_isSimpleModule ℂ (Matrix (Fin r) (Fin r) ℂ) ℂ M
  -- The `ℂ`-module structure of `W` as a module over `A₂ = ℂ` is its scalar structure.
  obtain rfl : jW = iW := Module.ext' _ _ fun c w ↦ by
    have h := tW.smul_assoc c (1 : ℂ) w
    rwa [smul_eq_mul, mul_one, one_smul] at h
  exact ⟨V, W, _, _, _, _, _, _, hV, isSimpleModule_iff_finrank_eq_one.mp hW, e, he⟩

/-- **The factors of the standard module of `M_r(ℂ) ⊗ M_s(ℂ)` have dimensions `r` and `s`.**
If simple modules `V` over `M_r(ℂ)` and `W` over `M_s(ℂ)` have exterior tensor product
isomorphic to `ℂ^r ⊗ ℂ^s` as `M_r(ℂ) ⊗ M_s(ℂ)`-modules, then `dim V = r` and `dim W = s`. -/
theorem finrank_eq_and_finrank_eq_of_tensorProduct_equiv_fin_fun {r s : ℕ} [NeZero r] [NeZero s]
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
