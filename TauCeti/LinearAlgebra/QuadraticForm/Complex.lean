/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Quadratic forms over the complex numbers

Over `ℂ`, a regular finite-dimensional quadratic form is determined up to equivalence by its
dimension.  In particular, every form of rank at least two is isotropic.  These facts justify the
omission of complex places from the local predicates used by the global local-to-global theory.

The proofs use Mathlib's algebraically closed classification.  No separate complex quadratic-form
carrier is introduced.
-/

public section
noncomputable section

open QuadraticMap

namespace TauCeti.QuadraticForm

/-- A form over `ℂ` of rank at least two has a nonzero isotropic vector. -/
theorem _root_.QuadraticForm.not_anisotropic_complex {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (Q : QuadraticForm ℂ W)
    (h : 2 ≤ Module.finrank ℂ W) : ¬ Q.Anisotropic := by
  intro hQ
  obtain ⟨e⟩ := Q.equivalent_weightedSumSquares_of_isAlgClosed
    (QuadraticMap.separatingLeft_of_anisotropic Q hQ)
  let k := Module.finrank ℂ W - 2
  have hk : k + 1 + 1 = Module.finrank ℂ W := by
    dsimp [k]
    omega
  have hn : 0 < Module.finrank ℂ W := by omega
  let x₀ : Fin (k + 1 + 1) → ℂ := Fin.cons 1 (Fin.cons Complex.I (fun _ : Fin k => 0))
  let x : Fin (Module.finrank ℂ W) → ℂ :=
    fun i => x₀ (Fin.cast hk.symm i)
  have hx : x ≠ 0 := by
    intro hx
    let i₀ : Fin (Module.finrank ℂ W) := ⟨0, hn⟩
    have hi := congrArg (fun f => f i₀) hx
    simp [x, x₀, i₀] at hi
  have hzero : Q (e.symm x) = 0 := by
    rw [← e.map_app]
    rw [e.apply_symm_apply]
    simp only [weightedSumSquares_apply, Pi.one_apply, one_smul]
    rw [← (finCongr hk).sum_comp (fun i => x i * x i)]
    simp [x, x₀, Fin.sum_univ_succ]
  apply hx
  rw [← e.apply_symm_apply x, hQ _ hzero]
  exact map_zero e

/-- Regular complex quadratic forms on possibly different spaces are equivalent exactly when their
dimensions agree. -/
theorem _root_.QuadraticForm.equivalent_of_finrank_eq_complex {W₁ W₂ : Type*}
    [AddCommGroup W₁] [Module ℂ W₁] [FiniteDimensional ℂ W₁]
    [AddCommGroup W₂] [Module ℂ W₂] [FiniteDimensional ℂ W₂]
    (Q : QuadraticForm ℂ W₁) (R : QuadraticForm ℂ W₂)
    (hQ : Q.Nondegenerate) (hR : R.Nondegenerate)
    (h : Module.finrank ℂ W₁ = Module.finrank ℂ W₂) : Q.Equivalent R := by
  let e : W₁ ≃ₗ[ℂ] W₂ := LinearEquiv.ofFinrankEq W₁ W₂ h
  have hQ' : (QuadraticMap.associated Q).SeparatingLeft :=
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  have hRsep : (QuadraticMap.associated R).SeparatingLeft :=
    (QuadraticMap.nondegenerate_associated_iff.mpr hR).1
  have hR' : (QuadraticMap.associated (R.comp (e : W₁ →ₗ[ℂ] W₂))).SeparatingLeft := by
    rw [QuadraticMap.associated_comp]
    intro x hx
    apply e.injective
    simpa using hRsep (e x) (fun y ↦ by
      simpa [LinearMap.compl₁₂_apply] using hx (e.symm y))
  obtain ⟨e'⟩ := Q.equivalent_of_isAlgClosed (R.comp (e : W₁ →ₗ[ℂ] W₂)) hQ' hR'
  exact ⟨e'.trans (R.isometryEquivOfCompLinearEquiv e).symm⟩

/-- Two regular complex quadratic forms are equivalent precisely when their dimensions agree. -/
@[simp] theorem _root_.QuadraticForm.equivalent_iff_finrank_eq_complex {W₁ W₂ : Type*}
    [AddCommGroup W₁] [Module ℂ W₁] [FiniteDimensional ℂ W₁]
    [AddCommGroup W₂] [Module ℂ W₂] [FiniteDimensional ℂ W₂]
    (Q : QuadraticForm ℂ W₁) (R : QuadraticForm ℂ W₂)
    (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.Equivalent R ↔ Module.finrank ℂ W₁ = Module.finrank ℂ W₂ := by
  constructor
  · rintro ⟨e⟩
    exact e.toLinearEquiv.finrank_eq
  · exact _root_.QuadraticForm.equivalent_of_finrank_eq_complex Q R hQ hR

end TauCeti.QuadraticForm
