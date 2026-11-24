/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic
public import TauCeti.Geometry.Symplectic.Rescale
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# Hamiltonian vector fields under rescaling and linear symplectomorphisms

Our Hamiltonian vector fields follow the convention `ω(X_H, ·) = dH`
(`TauCeti.SymplecticForm.hamiltonianVectorField`). This file records how they change when the
symplectic form is rescaled, and how linear symplectomorphisms carry them.

* **Rescaling.** For `c ≠ 0`, the Hamiltonian vector field of `H` for `c • ω` is `c⁻¹ • X_H`
  (`TauCeti.SymplecticForm.hamiltonianVectorField_rescale`). For `c = -1` this compares the two
  sign conventions for Hamiltonian vector fields in use in the literature: the field `X` with
  `ω(X, ·) = -dH` is the field of `-H` in our convention, and also the field of `H` for `-ω`
  (`TauCeti.SymplecticForm.hamiltonianVectorField_rescale_neg_one`).
* **Naturality.** A linear symplectomorphism `e : (V, ω₁) → (W, ω₂)` carries the Hamiltonian
  vector field of `H` at `x` to the Hamiltonian vector field of `H ∘ e⁻¹` at `e x`
  (`TauCeti.SymplecticForm.IsSymplectomorphism.map_hamiltonianVectorField`), and the field of
  `G ∘ e` is the pullback of the field of `G`
  (`TauCeti.SymplecticForm.IsSymplectomorphism.hamiltonianVectorField_comp`).

Combined, these transport Hamiltonian dynamics between two symplectic vector spaces whose
forms and sign conventions both differ, as for the cotangent space with the forms `dλ` and `-dλ`
of the tautological one-form `λ`.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1 (Hamiltonian vector fields and symplectomorphisms).
-/

public section

namespace TauCeti.SymplecticForm

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-! ### Rescaling the symplectic form -/

/-- **Hamiltonian vector fields of a rescaled form.** For `c ≠ 0`, the Hamiltonian vector field of
`H` for the form `c • ω` is `c⁻¹` times its Hamiltonian vector field for `ω`. -/
@[simp]
theorem hamiltonianVectorField_rescale (ω : SymplecticForm V) {c : ℝ} (hc : c ≠ 0) (H : V → ℝ)
    (x : V) :
    (ω.rescale c hc).hamiltonianVectorField H x = c⁻¹ • ω.hamiltonianVectorField H x := by
  rw [eq_comm, eq_hamiltonianVectorField_iff]
  intro v
  rw [← ω.apply_hamiltonianVectorField H x v]
  simp [hc]

/-- **The two sign conventions for Hamiltonian vector fields.** The field `X` with
`ω(X, ·) = -dH`, which is the Hamiltonian vector field of `H` in the opposite sign convention, is
the Hamiltonian vector field of `H` for the form `-ω` and the Hamiltonian vector field of `-H`
for `ω` in ours. -/
theorem hamiltonianVectorField_rescale_neg_one (ω : SymplecticForm V) (H : V → ℝ) (x : V) :
    (ω.rescale (-1) (by norm_num)).hamiltonianVectorField H x =
      ω.hamiltonianVectorField (-H) x := by
  rw [hamiltonianVectorField_rescale, hamiltonianVectorField_neg, inv_neg, inv_one, neg_one_smul]

/-- The Hamiltonian vector field of `-H` is the field `X` with `ω(X, ·) = -dH`. -/
theorem eq_hamiltonianVectorField_neg_iff (ω : SymplecticForm V) (H : V → ℝ) (x u : V) :
    u = ω.hamiltonianVectorField (-H) x ↔ ∀ v, ω u v = -fderiv ℝ H x v := by
  rw [eq_hamiltonianVectorField_iff]
  simp [fderiv_neg]

/-! ### Linear symplectomorphisms -/

variable {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W} {e : V ≃ₗ[ℝ] W}

/-- **Linear symplectomorphisms carry Hamiltonian vector fields.** If `e : (V, ω₁) → (W, ω₂)` is a
linear symplectomorphism, then `e` carries the Hamiltonian vector field of `H` at `x` to the
Hamiltonian vector field of `H ∘ e⁻¹` at `e x`. -/
theorem IsSymplectomorphism.map_hamiltonianVectorField (he : IsSymplectomorphism ω₁ ω₂ e)
    (H : V → ℝ) (x : V) :
    e (ω₁.hamiltonianVectorField H x) = ω₂.hamiltonianVectorField (H ∘ e.symm) (e x) := by
  rw [eq_hamiltonianVectorField_iff]
  intro w
  -- Both sides are `dH(x)(e⁻¹ w)`: the left one by invariance of the forms, the right one by
  -- the chain rule for the continuous linear equivalence `e⁻¹`.
  have hfd := (e.symm.toContinuousLinearEquiv).comp_right_fderiv (f := H) (x := e x)
  rw [LinearEquiv.coe_toContinuousLinearEquiv'] at hfd
  simp [hfd, ← ω₁.apply_hamiltonianVectorField H x, ← he.apply]

/-- **Pullback of Hamiltonian vector fields along a linear symplectomorphism.** If
`e : (V, ω₁) → (W, ω₂)` is a linear symplectomorphism, the Hamiltonian vector field of `G ∘ e` at
`x` is the pullback along `e` of the Hamiltonian vector field of `G` at `e x`. -/
theorem IsSymplectomorphism.hamiltonianVectorField_comp (he : IsSymplectomorphism ω₁ ω₂ e)
    (G : W → ℝ) (x : V) :
    ω₁.hamiltonianVectorField (G ∘ e) x = e.symm (ω₂.hamiltonianVectorField G (e x)) := by
  rw [eq_comm, LinearEquiv.symm_apply_eq, he.map_hamiltonianVectorField]
  congr 1
  funext y
  simp

end TauCeti.SymplecticForm
