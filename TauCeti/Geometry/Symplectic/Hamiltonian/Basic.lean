/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Duality
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Hamiltonian vector fields on symplectic vector spaces

For a constant symplectic form on a finite-dimensional real normed space, the Hamiltonian
vector field of `H` is obtained by inverting contraction with the symplectic form.
Our sign convention is `ω (X_H x) v = dH(x) v`. For `ω = dq ∧ dp`, this gives the
Hamilton equations `q' = ∂H/∂p`, `p' = -∂H/∂q`.

The characteristic contraction equation determines the field uniquely. Its linearization
is infinitesimally symplectic when `H` is twice continuously differentiable; this is the
identity used to show that Hamiltonian flows preserve the symplectic form.

See McDuff--Salamon, *Introduction to Symplectic Topology*, the discussion of Hamiltonian
vector fields and their flows. The construction uses `SymplecticForm` contraction duality.
-/

public section

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The Hamiltonian vector field, with convention `ι_X ω = dH`.
The derivative is totalized as usual: at a nondifferentiability point this field is zero. -/
noncomputable def hamiltonianVectorField (ω : SymplecticForm V) (H : V → ℝ) (x : V) : V :=
  ω.toBilinForm.toContinuousBilinearMap.inverse (fderiv ℝ H x)

/-- Contraction of the Hamiltonian field is the derivative of the Hamiltonian. -/
@[simp]
theorem apply_hamiltonianVectorField (ω : SymplecticForm V) (H : V → ℝ) (x v : V) :
    ω (ω.hamiltonianVectorField H x) v = fderiv ℝ H x v := by
  exact congrArg (fun L : V →L[ℝ] ℝ ↦ L v)
    (ω.isInvertible_toContinuousBilinearMap.self_apply_inverse (fderiv ℝ H x))

/-- The contraction equation uniquely characterizes the Hamiltonian vector field. -/
theorem eq_hamiltonianVectorField_iff (ω : SymplecticForm V) (H : V → ℝ) (x u : V) :
    u = ω.hamiltonianVectorField H x ↔ ∀ v, ω u v = fderiv ℝ H x v := by
  constructor
  · rintro rfl v
    exact ω.apply_hamiltonianVectorField H x v
  · intro h
    apply ω.isInvertible_toContinuousBilinearMap.injective
    ext v
    exact (h v).trans (ω.apply_hamiltonianVectorField H x v).symm

/-- The Hamiltonian has zero derivative in its own Hamiltonian direction. -/
@[simp]
theorem fderiv_apply_hamiltonianVectorField (ω : SymplecticForm V) (H : V → ℝ) (x : V) :
    fderiv ℝ H x (ω.hamiltonianVectorField H x) = 0 := by
  rw [← ω.apply_hamiltonianVectorField H x, ω.self_eq_zero]

/-- A `C^(n+1)` Hamiltonian has a `C^n` Hamiltonian vector field. -/
theorem contDiff_hamiltonianVectorField (ω : SymplecticForm V) {H : V → ℝ}
    {n : WithTop ℕ∞} (hH : ContDiff ℝ (n + 1) H) :
    ContDiff ℝ n (ω.hamiltonianVectorField H) :=
  ω.toBilinForm.toContinuousBilinearMap.inverse.contDiff.comp
    (hH.fderiv_right le_rfl)

/-- Contracting the linearization of the Hamiltonian vector field gives the Hessian. -/
theorem apply_fderiv_hamiltonianVectorField (ω : SymplecticForm V) {H : V → ℝ}
    {x : V} (hH : DifferentiableAt ℝ (fderiv ℝ H) x) (u v : V) :
    ω (fderiv ℝ (ω.hamiltonianVectorField H) x u) v =
      fderiv ℝ (fderiv ℝ H) x u v := by
  have h := ω.toBilinForm.toContinuousBilinearMap.inverse.hasFDerivAt.comp x hH.hasFDerivAt
  have hX : HasFDerivAt (ω.hamiltonianVectorField H)
      (ω.toBilinForm.toContinuousBilinearMap.inverse.comp (fderiv ℝ (fderiv ℝ H) x)) x := h
  rw [hX.fderiv]
  exact congrArg (fun L : V →L[ℝ] ℝ ↦ L v)
    (ω.isInvertible_toContinuousBilinearMap.self_apply_inverse
      (fderiv ℝ (fderiv ℝ H) x u))

/-- The linearization of a `C²` Hamiltonian vector field is infinitesimally symplectic. -/
theorem apply_fderiv_hamiltonianVectorField_add (ω : SymplecticForm V) {H : V → ℝ}
    {x : V} (hH : ContDiffAt ℝ 2 H x) (u v : V) :
    ω (fderiv ℝ (ω.hamiltonianVectorField H) x u) v +
      ω u (fderiv ℝ (ω.hamiltonianVectorField H) x v) = 0 := by
  have hd := (hH.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [← ω.neg_eq (fderiv ℝ (ω.hamiltonianVectorField H) x v) u,
    ω.apply_fderiv_hamiltonianVectorField hd, ω.apply_fderiv_hamiltonianVectorField hd]
  rw [hH.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField]) u v]
  exact add_neg_cancel _

end TauCeti.SymplecticForm
