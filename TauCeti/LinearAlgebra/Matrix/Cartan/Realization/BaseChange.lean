/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Basic
public import TauCeti.LinearAlgebra.Matrix.Rank
public import TauCeti.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Scalar extension of Cartan realizations

A finite-dimensional realization over `K` extends to any field extension `L`: its coroots become
`1 ⊗ hᵢ`
and its roots become the scalar-extended functionals. Both families remain independent,
including when the Cartan matrix is singular. The coroot span and the full Cartan center
commute with scalar extension, and a finite-dimensional realization is minimal after extension
if and only if it was minimal before extension.

In particular, a rational realization gives realizations over every characteristic-zero
field and over the reals, with the central directions retained. The construction uses
Mathlib's `Module.Dual.baseChange` and scalar-extended evaluation from
`TauCeti.LinearAlgebra.Dual.BaseChange`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, §1.1, for realizations
  and their minimal dimension.
-/

public section

open Module
open scoped TensorProduct

namespace TauCeti.CartanRealization

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H]
  [FiniteDimensional K H] {A : Matrix I I K} (R : CartanRealization A H)
  (L : Type*) [Field L] [Algebra K L]

/-- Extend a finite-dimensional realization to a field extension. Roots are extended as
functionals on the full tensor product, not merely on the coroot span. -/
noncomputable def baseChange : CartanRealization (A.map (algebraMap K L)) (L ⊗[K] H) where
  coroot i := 1 ⊗ₜ[K] R.coroot i
  root i := (R.root i).baseChange L
  coroot_linearIndependent := Flat.linearIndependent_one_tmul R.coroot_linearIndependent
  root_linearIndependent := by
    let e := TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := K) (A := L) (M := H)
    have h := (Flat.linearIndependent_one_tmul (S := L) R.root_linearIndependent).map'
      e.toLinearMap e.ker
    dsimp only [e] at h
    simpa only [LinearEquiv.coe_coe, Function.comp_def,
      TauCeti.Module.Dual.baseChangeEvaluationEquiv_apply,
      TauCeti.Module.Dual.baseChangeEvaluation_one_tmul] using h
  root_coroot i j := by simp [Algebra.smul_def]

/-- The extended simple coroot. -/
@[simp]
theorem baseChange_coroot (i : I) : (R.baseChange L).coroot i = 1 ⊗ₜ[K] R.coroot i := (rfl)

/-- The extended simple root as a functional. -/
@[simp]
theorem baseChange_root (i : I) : (R.baseChange L).root i = (R.root i).baseChange L := (rfl)

/-- Extending scalars commutes with taking the span of the simple coroots. -/
@[simp]
theorem corootSpan_baseChange : (R.baseChange L).corootSpan = R.corootSpan.baseChange L := by
  rw [corootSpan_def, corootSpan_def, Submodule.baseChange_span, ← Set.range_comp]
  congr 2

/-- Scalar extension is compatible with transport of the ambient realization by a linear
isomorphism. -/
@[simp]
theorem baseChange_map {H' : Type*} [AddCommGroup H'] [Module K H']
    [FiniteDimensional K H'] (e : H ≃ₗ[K] H') :
    (R.map e).baseChange L = (R.baseChange L).map (e.baseChange K L H H') := by
  apply ext
  · intro i
    simp
  · intro i
    ext h
    simp

variable [Fintype I]

/-- Root evaluation after extension is the base change of root evaluation, followed by the
canonical identification of the extended coordinate space with `L^I`. -/
theorem rootEvaluation_baseChange [DecidableEq I] :
    (R.baseChange L).rootEvaluation =
      (TensorProduct.piScalarRight K L L I).toLinearMap.comp (R.rootEvaluation.baseChange L) := by
  ext h i
  simp [Algebra.smul_def, mul_comm]

omit [Fintype I] in
/-- The full Cartan center commutes with field extension; extra central directions are
not discarded. -/
@[simp]
theorem cartanCenter_baseChange [Finite I] :
    (R.baseChange L).cartanCenter = R.cartanCenter.baseChange L := by
  classical
  let := Fintype.ofFinite I
  simp only [cartanCenter_def]
  rw [rootEvaluation_baseChange, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]
  exact Flat.ker_lTensor_eq L L R.rootEvaluation

/-- Field extension preserves and reflects minimality of a finite-dimensional realization. -/
theorem isMinimal_baseChange : (R.baseChange L).IsMinimal ↔ R.IsMinimal := by
  rw [isMinimal_iff, isMinimal_iff, Module.finrank_baseChange, Matrix.rank_map]

end TauCeti.CartanRealization
