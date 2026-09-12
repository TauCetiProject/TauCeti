/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
public import TauCeti.NumberTheory.QuadraticForm.Global.Localization

/-!
# Complex local quadratic forms

Over `ℂ`, a regular finite-dimensional quadratic form is determined up to equivalence by its
dimension.  In particular, a regular form of rank at least two is isotropic.  These facts justify
the omission of complex places from the local predicates used by the global local-to-global theory.

The proofs use Mathlib's algebraically closed classification and the actual complex localization
defined in `Global.Localization`; no separate complex quadratic-form carrier is introduced.
-/

public section
noncomputable section

open QuadraticMap

namespace TauCeti.QuadraticForm

private noncomputable def standardIsometry (n m : ℕ) (h : n = m) :
    IsometryEquiv (weightedSumSquares ℂ (1 : Fin n → ℂ))
      (weightedSumSquares ℂ (1 : Fin m → ℂ)) := by
  let e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin m → ℂ) :=
    LinearEquiv.piCongrLeft ℂ (fun _ : Fin m => ℂ) (finCongr h)
  exact
    { toLinearEquiv := e
      map_app' := by
        intro x
        simp only [weightedSumSquares_apply, Pi.one_apply, one_smul]
        dsimp [e, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft']
        -- The linear reindexing is the inverse reindexing of `finCongr`.
        exact (finCongr h).symm.sum_comp (fun i => x i * x i) }

/-- A regular complex quadratic form of rank at least two has a nonzero isotropic vector. -/
theorem not_anisotropic_complex {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (Q : QuadraticForm ℂ W) (hQ : Q.Nondegenerate)
    (h : 2 ≤ Module.finrank ℂ W) : ¬ Q.Anisotropic := by
  obtain ⟨e⟩ := Q.equivalent_weightedSumSquares_of_isAlgClosed
    ((QuadraticMap.nondegenerate_associated_iff (Q := Q)).mpr hQ).1
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
  refine (QuadraticMap.not_anisotropic_iff_exists Q).mpr ⟨e.symm x, ?_, ?_⟩
  · intro hz
    apply hx
    rw [← e.apply_symm_apply x, hz]
    exact map_zero e
  · rw [← e.map_app]
    rw [e.apply_symm_apply]
    simp only [weightedSumSquares_apply, Pi.one_apply, one_smul]
    rw [← (finCongr hk).sum_comp (fun i => x i * x i)]
    simp [x, x₀, Fin.sum_univ_succ]

private theorem equivalent_standard_complex {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (Q : QuadraticForm ℂ W) (hQ : Q.Nondegenerate) :
    Q.Equivalent (weightedSumSquares ℂ
      (1 : Fin (Module.finrank ℂ W) → ℂ)) :=
  Q.equivalent_weightedSumSquares_of_isAlgClosed
    ((QuadraticMap.nondegenerate_associated_iff (Q := Q)).mpr hQ).1

/-- Regular complex quadratic forms on possibly different spaces are equivalent exactly when their
dimensions agree. -/
theorem equivalent_of_finrank_eq_complex {W₁ W₂ : Type*}
    [AddCommGroup W₁] [Module ℂ W₁] [FiniteDimensional ℂ W₁]
    [AddCommGroup W₂] [Module ℂ W₂] [FiniteDimensional ℂ W₂]
    (Q : QuadraticForm ℂ W₁) (R : QuadraticForm ℂ W₂)
    (hQ : Q.Nondegenerate) (hR : R.Nondegenerate)
    (h : Module.finrank ℂ W₁ = Module.finrank ℂ W₂) : Q.Equivalent R := by
  obtain ⟨eQ⟩ := equivalent_standard_complex Q hQ
  obtain ⟨eR⟩ := equivalent_standard_complex R hR
  exact ⟨eQ.trans ((standardIsometry (Module.finrank ℂ W₁) (Module.finrank ℂ W₂) h).trans eR.symm)⟩

/-- Two regular complex quadratic forms are equivalent precisely when their dimensions agree. -/
theorem equivalent_iff_finrank_eq_complex {W₁ W₂ : Type*}
    [AddCommGroup W₁] [Module ℂ W₁] [FiniteDimensional ℂ W₁]
    [AddCommGroup W₂] [Module ℂ W₂] [FiniteDimensional ℂ W₂]
    (Q : QuadraticForm ℂ W₁) (R : QuadraticForm ℂ W₂)
    (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.Equivalent R ↔ Module.finrank ℂ W₁ = Module.finrank ℂ W₂ := by
  constructor
  · rintro ⟨e⟩
    exact e.toLinearEquiv.finrank_eq
  · exact equivalent_of_finrank_eq_complex Q R hQ hR

end TauCeti.QuadraticForm
