/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.Algebra.DualNumber.Grading
public import TauCeti.LinearAlgebra.Graded.LinearMap

/-!
# Base change of the dual numbers

For a commutative `R`-algebra `S`, the dual numbers commute with base change:
`S ⊗[R] R[ε] ≃ₐ[S] S[ε]`, sending `s ⊗ (a + b ε)` to `s • (a + b ε)` with `a` and `b`
mapped into `S`.

The statement and naming are modelled on Mathlib's `MvPolynomial.algebraTensorAlgEquiv`
(in `Mathlib/RingTheory/TensorProduct/MvPolynomial.lean`); the construction here instead
assembles the two directions from `Algebra.TensorProduct.lift` and `DualNumber.lift`.

## Main results

* `TauCeti.dualNumberAlgebraTensorAlgEquiv`: the `S`-algebra equivalence `S ⊗[R] R[ε] ≃ₐ[S] S[ε]`.
* `TauCeti.sndHom_comp_dualNumberAlgebraTensorAlgEquiv`: base change intertwines the canonical
  traces `TrivSqZeroExt.sndHom`.
* `TauCeti.isHomogeneous_dualNumberAlgebraTensorAlgEquiv`: base change is homogeneous of degree
  zero for `TauCeti.dualNumberIntegerGrade`.
-/

public section

open TensorProduct DualNumber TrivSqZeroExt

namespace TauCeti

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- The base change `S ⊗[R] R[ε] ≃ₐ[S] S[ε]` of the dual numbers. -/
noncomputable def dualNumberAlgebraTensorAlgEquiv : S ⊗[R] R[ε] ≃ₐ[S] S[ε] :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (Algebra.ofId S S[ε])
      (lift ⟨(Algebra.ofId R S[ε], ε), eps_mul_eps, fun _ => commute_eps_left _⟩)
      fun _ _ => Commute.all _ _)
    (lift ⟨(Algebra.ofId S (S ⊗[R] R[ε]), 1 ⊗ₜ ε), by simp,
      fun _ => Commute.all (S := S ⊗[R] R[ε]) _ _⟩)
    (DualNumber.algHom_ext (by simp))
    (Algebra.TensorProduct.ext (by ext) (DualNumber.algHom_ext (by simp)))

variable {R S}

/-- The scalar part of the base change of `s ⊗ x`. -/
@[simp]
theorem dualNumberAlgebraTensorAlgEquiv_tmul_fst (s : S) (x : R[ε]) :
    (dualNumberAlgebraTensorAlgEquiv R S (s ⊗ₜ x)).fst = s * algebraMap R S x.fst := by
  simp [dualNumberAlgebraTensorAlgEquiv, lift_apply_apply, algebraMap_eq_inl']

/-- The infinitesimal part of the base change of `s ⊗ x`. -/
@[simp]
theorem dualNumberAlgebraTensorAlgEquiv_tmul_snd (s : S) (x : R[ε]) :
    (dualNumberAlgebraTensorAlgEquiv R S (s ⊗ₜ x)).snd = s * algebraMap R S x.snd := by
  simp [dualNumberAlgebraTensorAlgEquiv, lift_apply_apply, algebraMap_eq_inl']

/-- Base change sends `s ⊗ 1` to the constant `s`. -/
@[simp]
theorem dualNumberAlgebraTensorAlgEquiv_tmul_one (s : S) :
    dualNumberAlgebraTensorAlgEquiv R S (s ⊗ₜ 1) = algebraMap S S[ε] s := by
  simp [dualNumberAlgebraTensorAlgEquiv]

/-- Base change sends `s ⊗ ε` to `s • ε`. -/
@[simp]
theorem dualNumberAlgebraTensorAlgEquiv_tmul_eps (s : S) :
    dualNumberAlgebraTensorAlgEquiv R S (s ⊗ₜ ε) = s • ε := by
  simp [dualNumberAlgebraTensorAlgEquiv, ← Algebra.smul_def]

/-- The inverse of base change sends `ε` to `1 ⊗ ε`. -/
@[simp]
theorem dualNumberAlgebraTensorAlgEquiv_symm_eps :
    (dualNumberAlgebraTensorAlgEquiv R S).symm ε = 1 ⊗ₜ ε := by
  simp [dualNumberAlgebraTensorAlgEquiv, lift_apply_apply]

variable (R S)

/-- Base change `S ⊗[R] R[ε] ≃ₐ[S] S[ε]` intertwines the canonical traces of `R[ε]` and
`S[ε]`. -/
theorem sndHom_comp_dualNumberAlgebraTensorAlgEquiv :
    TrivSqZeroExt.sndHom S S ∘ₗ (dualNumberAlgebraTensorAlgEquiv R S).toLinearMap =
      Module.Dual.baseChange S (TrivSqZeroExt.sndHom R R) :=
  TensorProduct.AlgebraTensorModule.ext fun _ _ ↦ by simp [Algebra.smul_def, mul_comm]

/-- Base change `S ⊗[R] R[ε] ≃ₐ[S] S[ε]` is homogeneous of degree zero between the
base-changed integer grading and `TauCeti.dualNumberIntegerGrade S`. -/
theorem isHomogeneous_dualNumberAlgebraTensorAlgEquiv :
    TauCeti.LinearMap.IsHomogeneous (dualNumberAlgebraTensorAlgEquiv R S).toLinearMap
      (fun p ↦ (dualNumberIntegerGrade R p).baseChange S) (dualNumberIntegerGrade S) 0 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p z hz
  rw [add_zero]
  have hle : (dualNumberIntegerGrade R p).baseChange S ≤
      (dualNumberIntegerGrade S p).comap (dualNumberAlgebraTensorAlgEquiv R S).toLinearMap := by
    rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe] at hx
    rw [SetLike.mem_coe, Submodule.mem_comap, TensorProduct.mk_apply]
    rcases eq_or_ne p 0 with rfl | h0
    · rw [← Nat.cast_zero, dualNumberIntegerGrade_ofNat, mem_dualNumberGrade_zero] at hx ⊢
      simp [hx]
    · rcases eq_or_ne p 2 with rfl | h2
      · rw [← Nat.cast_ofNat, dualNumberIntegerGrade_ofNat, mem_dualNumberGrade_two] at hx ⊢
        simp [hx]
      · rw [dualNumberIntegerGrade_eq_bot R h0 h2] at hx
        simp [(Submodule.mem_bot R).mp hx]
  exact hle hz

end TauCeti
