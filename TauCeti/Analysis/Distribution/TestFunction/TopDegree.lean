/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Postcomp
public import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Top-degree test forms and scalar tests

A basis of a finite-dimensional real vector space identifies its top-degree test forms with
scalar test functions. Both directions are continuous for the native LF topology and preserve
the exact support. The coefficient is evaluation on the basis; the inverse multiplies the
basis determinant form by the scalar test. The formulas include dimension zero.

The basis-change and linear-pullback formulas record the signed determinant, not its absolute
value. These coordinates let a functional on top-degree test forms be tested against scalar
tests, as in the local constancy theorem for currents.

The construction uses Mathlib's `TestFunction.postcompCLM` and
`AlternatingMap.eq_smul_basis_det`. See Federer, *Geometric Measure Theory*, §4.1.7 for the
scalar-test description of top-dimensional currents.
-/

public section

namespace TauCeti

open scoped Distributions

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype ι] [DecidableEq ι] {Ω Ω' : TopologicalSpace.Opens E} {n : ℕ∞}

/-- A basis identifies top-degree test forms with scalar tests by evaluation on that basis. -/
noncomputable def _root_.Module.Basis.testTopFormEquiv (b : Module.Basis ι ℝ E) :
    𝓓^{n}(Ω, E [⋀^ι]→L[ℝ] ℝ) ≃L[ℝ] 𝓓^{n}(Ω, ℝ) :=
  TestFunction.postcompCLE b.topFormEquiv

@[simp]
theorem _root_.Module.Basis.testTopFormEquiv_apply (b : Module.Basis ι ℝ E)
    (φ : 𝓓^{n}(Ω, E [⋀^ι]→L[ℝ] ℝ)) (x : E) : b.testTopFormEquiv φ x = φ x b := by
  simp [Module.Basis.testTopFormEquiv]

@[simp]
theorem _root_.Module.Basis.testTopFormEquiv_symm_apply (b : Module.Basis ι ℝ E)
    (f : 𝓓^{n}(Ω, ℝ)) (x : E) (v : ι → E) :
    b.testTopFormEquiv.symm f x v = f x * b.det v := by
  simp [Module.Basis.testTopFormEquiv]

/-- Passing from a top-degree test form to its coefficient preserves its support exactly. -/
@[simp]
theorem _root_.Module.Basis.tsupport_testTopFormEquiv (b : Module.Basis ι ℝ E)
    (φ : 𝓓^{n}(Ω, E [⋀^ι]→L[ℝ] ℝ)) : tsupport (b.testTopFormEquiv φ) = tsupport φ := by
  simp [Module.Basis.testTopFormEquiv]

/-- Multiplication by the basis determinant form preserves the support of a scalar test. -/
@[simp]
theorem _root_.Module.Basis.tsupport_testTopFormEquiv_symm (b : Module.Basis ι ℝ E)
    (f : 𝓓^{n}(Ω, ℝ)) : tsupport (b.testTopFormEquiv.symm f) = tsupport f := by
  simp [Module.Basis.testTopFormEquiv]

/-- The scalar coefficient changes by the signed change-of-basis determinant. -/
theorem _root_.Module.Basis.testTopFormEquiv_changeBasis (b b' : Module.Basis ι ℝ E)
    (φ : 𝓓^{n}(Ω, E [⋀^ι]→L[ℝ] ℝ)) :
    b'.testTopFormEquiv φ = b.det b' • b.testTopFormEquiv φ := by
  ext x
  simpa using (φ x).apply_eq_det_mul b b'

/-- The identification of top-degree tests commutes with extension and lowering regularity. -/
theorem _root_.Module.Basis.testTopFormEquiv_monoCLM (b : Module.Basis ι ℝ E) {m : ℕ∞}
    (φ : 𝓓^{n}(Ω, E [⋀^ι]→L[ℝ] ℝ)) :
    b.testTopFormEquiv (TestFunction.monoCLM ℝ (Ω₂ := Ω') (n₂ := m) φ) =
      TestFunction.monoCLM ℝ (Ω₂ := Ω') (n₂ := m) (b.testTopFormEquiv φ) :=
  TestFunction.postcompCLE_monoCLM b.topFormEquiv φ

/-- Fibrewise pullback by a linear endomorphism multiplies the top-degree coefficient by its
signed determinant. No change of the spatial argument of the test function is made here. -/
theorem _root_.Module.Basis.testTopFormEquiv_postcomp_compContinuousLinearMap
    (b : Module.Basis ι ℝ E) (A : E →L[ℝ] E) (φ : 𝓓^{n}(Ω, E [⋀^ι]→L[ℝ] ℝ)) :
    b.testTopFormEquiv
        (TestFunction.postcompCLM (ContinuousAlternatingMap.compContinuousLinearMapCLM A) φ) =
      A.toLinearMap.det • b.testTopFormEquiv φ := by
  ext x
  simpa using (φ x).compContinuousLinearMap_apply_basis b A

end TauCeti
