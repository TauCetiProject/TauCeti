/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.Algebra.Module.GradedModule.TensorProduct.Basic
public import TauCeti.Algebra.Module.GradedModule.Trivial

/-!
# Base change of graded modules and homogeneous functionals

This file records compatibility of internal gradings, even support, homogeneous bases, and
homogeneous linear functionals with scalar extension `S ⊗[R] M`.

## Main results

* `TauCeti.baseChange_eq_bot_of_odd`: scalar extension preserves even support.
* `TauCeti.baseChange_basis_mem_grade`: scalar extension of a homogeneous basis remains homogeneous
  in the same degrees.
* `TauCeti.isHomogeneous_dualBaseChange`: scalar extension preserves the degree of a linear
  functional into the trivial grading.
* `TauCeti.isHomogeneous_dualBaseChange_graded`: over a `ℤ`-graded commutative `R`-algebra `S`,
  the base-changed functional is homogeneous of the same degree into the grading of `S`.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti

section Semiring

variable {R : Type*} (S : Type*) {M : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- Extending scalars to a degree-zero `R`-algebra `S` preserves even support. -/
theorem baseChange_eq_bot_of_odd (ℳ : ℤ → Submodule R M) (hM : ∀ p : ℤ, Odd p → ℳ p = ⊥)
    {p : ℤ} (hp : Odd p) : (ℳ p).baseChange S = ⊥ := by
  rw [hM p hp, Submodule.baseChange_bot]

/-- Base change of a homogeneous basis to an `R`-algebra `S` remains homogeneous in the same
degrees. -/
theorem baseChange_basis_mem_grade {α ι : Type*} (ℳ : α → Submodule R M) (b : Module.Basis ι R M)
    (deg : ι → α) (hb : ∀ i, b i ∈ ℳ (deg i)) (i : ι) :
    b.baseChange S i ∈ (ℳ (deg i)).baseChange S := by
  rw [Module.Basis.baseChange_apply]
  exact Submodule.tmul_mem_baseChange_of_mem (1 : S) (hb i)

end Semiring

section CommSemiring

variable {R : Type*} (S : Type*) {M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] (ℳ : ℤ → Submodule R M)

/-- Extending scalars preserves the degree of a linear functional into the trivial grading. -/
theorem isHomogeneous_dualBaseChange {ε : M →ₗ[R] R} {q : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε ℳ (trivialGrading R R) q) :
    TauCeti.LinearMap.IsHomogeneous (Module.Dual.baseChange S ε)
      (fun p ↦ (ℳ p).baseChange S) (trivialGrading S S) q := by
  rw [isHomogeneous_trivialGrading_iff]
  intro p hp z hz
  have hle : (ℳ p).baseChange S ≤ _root_.LinearMap.ker (Module.Dual.baseChange S ε) := by
    rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, _root_.LinearMap.mem_ker, TensorProduct.mk_apply,
      Module.Dual.baseChange_apply_tmul,
      (isHomogeneous_trivialGrading_iff ℳ ε q).mp hε p hp x hx, zero_smul]
  exact hle hz

/-- Over a `ℤ`-graded commutative `R`-algebra `S` (with grading `𝓢`), the base-changed functional
`Module.Dual.baseChange S ε` is homogeneous of degree `q` from the total-degree grading `𝓢 ⊗ ℳ`
into `𝓢`. -/
theorem isHomogeneous_dualBaseChange_graded (𝓢 : ℤ → Submodule R S)
    [DirectSum.Decomposition 𝓢] [DirectSum.Decomposition ℳ] {ε : M →ₗ[R] R} {q : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε ℳ (trivialGrading R R) q) :
    TauCeti.LinearMap.IsHomogeneous ((Module.Dual.baseChange S ε).restrictScalars R)
      ((InternalGrading.ofDecomposition 𝓢).tensorProduct
        (InternalGrading.ofDecomposition ℳ)).piece 𝓢 q := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro n z hz
  refine (InternalGrading.ofDecomposition 𝓢).tensorProduct_piece_le
    (InternalGrading.ofDecomposition ℳ)
    (C := (𝓢 (n + q)).comap ((Module.Dual.baseChange S ε).restrictScalars R))
    (fun p s hs x hx ↦ ?_) hz
  simp only [InternalGrading.ofDecomposition_piece] at hs hx
  rw [Submodule.mem_comap, _root_.LinearMap.coe_restrictScalars, Module.Dual.baseChange_apply_tmul]
  by_cases hnp : (n - p) + q = 0
  · have hp : p = n + q := by omega
    rw [← hp]
    exact (𝓢 p).smul_mem (ε x) hs
  · rw [(isHomogeneous_trivialGrading_iff ℳ ε q).mp hε (n - p) hnp x hx, zero_smul]
    exact Submodule.zero_mem _

end CommSemiring

end TauCeti
