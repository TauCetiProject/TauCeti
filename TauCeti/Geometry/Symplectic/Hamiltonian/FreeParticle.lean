/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Analysis.InnerProductSpace.Dual
public import TauCeti.Geometry.Symplectic.Cotangent.StrongDual
public import TauCeti.Geometry.Symplectic.Hamiltonian.Flow

/-!
# The free particle

A free particle of mass `m` moving in a real Hilbert space `E` has phase space the linear
cotangent space `E × E'`, with `E'` the continuous dual, positions `q` and momenta `p`, and the
canonical symplectic form `ω((v, α), (w, β)) = β(v) - α(w)`
(`TauCeti.strongDualCotangentSymplecticForm`). Its Hamiltonian is the kinetic energy

`H(q, p) = ‖p‖² / (2m)`

(`TauCeti.freeParticleHamiltonian`), where `‖p‖` is the dual norm, equal to the norm of the
Riesz representative `p♯ ∈ E` of `p`. With the convention `ι_(X_H) ω = dH`, Hamilton's equations
are `q' = p♯ / m`, `p' = 0`: the Hamiltonian vector field is the linear field
`(q, p) ↦ (p♯ / m, 0)` (`TauCeti.freeParticleVelocity`), see
`TauCeti.hamiltonianVectorField_freeParticleHamiltonian`. Its flow is the linear free motion

`(q, p) ↦ (q + (t / m) p♯, p)`

(`TauCeti.freeParticleEvolution`), defined for every real time: it satisfies the flow law,
preserves the symplectic form and the energy, and its orbits solve Hamilton's equations. On a
finite-dimensional space it is the Hamiltonian flow `TauCeti.SymplecticForm.hamiltonianFlow` of
`H` (`TauCeti.hamiltonianFlow_freeParticleHamiltonian`).

The physical mass is positive; the definitions use Lean's total division, so all identities
below hold for every real `m`, with `m = 0` giving the zero Hamiltonian and the identity flow.

The generating functions of this motion, of the first kind `-m‖q - Q‖² / (2t)` and of the second
kind `P(q) + t‖P‖² / (2m)`, are in
`TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.FreeParticle`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Springer, 1989,
  §§15 and 40.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap InnerProductSpace
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Hamiltonian vector field `(q, p) ↦ (p♯ / m, 0)` of a free particle of mass `m`, where
`p♯` is the Riesz representative of the covector `p`. -/
def freeParticleVelocity (m : ℝ) : (E × StrongDual ℝ E) →L[ℝ] E × StrongDual ℝ E :=
  (m⁻¹ • toDualSymmL.comp (snd ℝ E (StrongDual ℝ E))).prod 0

@[simp]
theorem freeParticleVelocity_apply (m : ℝ) (x : E × StrongDual ℝ E) :
    freeParticleVelocity m x = (m⁻¹ • (toDual ℝ E).symm x.2, 0) := by
  simp [freeParticleVelocity]

/-- The time-`t` evolution `(q, p) ↦ (q + (t / m) p♯, p)` of a free particle of mass `m`. -/
def freeParticleEvolution (m t : ℝ) : (E × StrongDual ℝ E) →L[ℝ] E × StrongDual ℝ E :=
  (fst ℝ E (StrongDual ℝ E) + (t / m) • toDualSymmL.comp (snd ℝ E (StrongDual ℝ E))).prod
    (snd ℝ E (StrongDual ℝ E))

theorem freeParticleEvolution_apply (m t : ℝ) (x : E × StrongDual ℝ E) :
    freeParticleEvolution m t x = (x.1 + (t / m) • (toDual ℝ E).symm x.2, x.2) := by
  simp [freeParticleEvolution]

@[simp]
theorem freeParticleEvolution_apply_fst (m t : ℝ) (x : E × StrongDual ℝ E) :
    (freeParticleEvolution m t x).1 = x.1 + (t / m) • (toDual ℝ E).symm x.2 := by
  rw [freeParticleEvolution_apply]

/-- Free motion does not change the momentum. -/
@[simp]
theorem freeParticleEvolution_apply_snd (m t : ℝ) (x : E × StrongDual ℝ E) :
    (freeParticleEvolution m t x).2 = x.2 := by
  rw [freeParticleEvolution_apply]

@[simp]
theorem freeParticleEvolution_zero (m : ℝ) :
    freeParticleEvolution (E := E) m 0 = ContinuousLinearMap.id ℝ _ := by
  ext x <;> simp [freeParticleEvolution_apply]

/-- **The flow law.** Free motion for successive times is free motion for their sum. -/
theorem freeParticleEvolution_add (m s t : ℝ) :
    freeParticleEvolution (E := E) m (s + t) =
      (freeParticleEvolution m s).comp (freeParticleEvolution m t) := by
  refine ContinuousLinearMap.ext fun x ↦ Prod.ext ?_ rfl
  simp only [freeParticleEvolution_apply, coe_comp, Function.comp_apply, add_div, add_smul]
  abel

/-- Reversing time inverts free motion. -/
@[simp]
theorem freeParticleEvolution_neg_apply (m t : ℝ) (x : E × StrongDual ℝ E) :
    freeParticleEvolution m (-t) (freeParticleEvolution m t x) = x := by
  rw [← ContinuousLinearMap.comp_apply, ← freeParticleEvolution_add, neg_add_cancel,
    freeParticleEvolution_zero, ContinuousLinearMap.id_apply]

/-- The orbits of free motion are integral curves of the free-particle velocity field. -/
theorem hasDerivAt_freeParticleEvolution (m t : ℝ) (x : E × StrongDual ℝ E) :
    HasDerivAt (fun s ↦ freeParticleEvolution m s x)
      (freeParticleVelocity m (freeParticleEvolution m t x)) t := by
  have h : (fun s ↦ freeParticleEvolution m s x) =
      fun s ↦ x + s • freeParticleVelocity m x := by
    funext s
    ext
    · simp [freeParticleEvolution_apply, smul_smul, div_eq_mul_inv]
    · simp [freeParticleEvolution_apply]
  have hv : freeParticleVelocity m (freeParticleEvolution m t x) = freeParticleVelocity m x := by
    simp [freeParticleEvolution_apply]
  rw [h, hv]
  simpa using ((hasDerivAt_id t).smul_const (freeParticleVelocity m x)).const_add x

/-- Free motion preserves the canonical symplectic form of the cotangent space. -/
theorem strongDualCotangentSymplecticForm_freeParticleEvolution (m t : ℝ)
    (u v : E × StrongDual ℝ E) :
    strongDualCotangentSymplecticForm (freeParticleEvolution m t u)
        (freeParticleEvolution m t v) =
      strongDualCotangentSymplecticForm u v := by
  simp only [strongDualCotangentSymplecticForm_apply, freeParticleEvolution_apply, map_add,
    map_smul, smul_eq_mul, apply_toDual_symm_eq_conj v.2 u.2, RCLike.conj_to_real]
  ring

/-- The kinetic energy `H(q, p) = ‖p‖² / (2m)` of a free particle of mass `m`, the norm being
the dual norm of the covector `p`. -/
def freeParticleHamiltonian (m : ℝ) (x : E × StrongDual ℝ E) : ℝ :=
  ‖x.2‖ ^ 2 / (2 * m)

omit [CompleteSpace E] in
theorem freeParticleHamiltonian_apply (m : ℝ) (x : E × StrongDual ℝ E) :
    freeParticleHamiltonian m x = ‖x.2‖ ^ 2 / (2 * m) :=
  (rfl)

/-- **Conservation of energy** for the free particle. -/
@[simp]
theorem freeParticleHamiltonian_freeParticleEvolution (m t : ℝ) (x : E × StrongDual ℝ E) :
    freeParticleHamiltonian m (freeParticleEvolution m t x) = freeParticleHamiltonian m x := by
  simp [freeParticleHamiltonian_apply]

/-- The derivative of the kinetic energy at `(q, p)` is `(δq, δp) ↦ δp(p♯) / m`. -/
theorem hasFDerivAt_freeParticleHamiltonian (m : ℝ) (x : E × StrongDual ℝ E) :
    HasFDerivAt (freeParticleHamiltonian m)
      (m⁻¹ • (ContinuousLinearMap.apply ℝ ℝ ((toDual ℝ E).symm x.2)).comp
        (snd ℝ E (StrongDual ℝ E))) x := by
  let L : (E × StrongDual ℝ E) →L[ℝ] E := toDualSymmL.comp (snd ℝ E (StrongDual ℝ E))
  have hL (y : E × StrongDual ℝ E) : L y = (toDual ℝ E).symm y.2 := by simp [L]
  have hH : freeParticleHamiltonian (E := E) m = fun y ↦ (2 * m)⁻¹ * ‖L y‖ ^ 2 := by
    funext y
    rw [freeParticleHamiltonian_apply, hL, LinearIsometryEquiv.norm_map, div_eq_inv_mul]
  rw [hH]
  refine ((L.hasFDerivAt.norm_sq).const_mul _).congr_fderiv
    (ContinuousLinearMap.ext fun u ↦ ?_)
  have hu : ⟪(toDual ℝ E).symm x.2, L u⟫ = u.2 ((toDual ℝ E).symm x.2) := by
    rw [hL, real_inner_comm, toDual_symm_apply]
  simp only [_root_.smul_apply, coe_comp, Function.comp_apply, innerSL_apply_apply, hL] at hu ⊢
  rw [hu]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, coe_snd', apply_apply]
  field_simp

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **Hamilton's equations** of the free particle: `q' = p♯ / m`, `p' = 0`. -/
theorem hamiltonianVectorField_freeParticleHamiltonian (m : ℝ) :
    (strongDualCotangentSymplecticForm (V := E)).hamiltonianVectorField
        (freeParticleHamiltonian m) =
      ⇑(freeParticleVelocity (E := E) m) := by
  funext x
  refine (((strongDualCotangentSymplecticForm (V := E)).eq_hamiltonianVectorField_iff _ x _).2
    fun v ↦ ?_).symm
  rw [(hasFDerivAt_freeParticleHamiltonian m x).fderiv]
  simp

/-- The free-particle Hamiltonian vector field is globally Lipschitz, being linear. -/
theorem lipschitzWith_hamiltonianVectorField_freeParticleHamiltonian (m : ℝ) :
    LipschitzWith ‖freeParticleVelocity (E := E) m‖₊
      ((strongDualCotangentSymplecticForm (V := E)).hamiltonianVectorField
        (freeParticleHamiltonian m)) := by
  rw [hamiltonianVectorField_freeParticleHamiltonian]
  exact ContinuousLinearMap.lipschitzWith _

/-- The Hamiltonian flow of the kinetic energy `‖p‖² / (2m)` is free motion. -/
theorem hamiltonianFlow_freeParticleHamiltonian (m : ℝ) {K : NNReal}
    (hX : LipschitzWith K
      ((strongDualCotangentSymplecticForm (V := E)).hamiltonianVectorField
        (freeParticleHamiltonian (E := E) m)))
    (t : ℝ) (x : E × StrongDual ℝ E) :
    (strongDualCotangentSymplecticForm (V := E)).hamiltonianFlow
        (freeParticleHamiltonian m) hX t x =
      freeParticleEvolution m t x := by
  have h := eq_flowOfLipschitz hX (γ := fun s ↦ freeParticleEvolution m s x)
    (fun s ↦ by
      rw [hamiltonianVectorField_freeParticleHamiltonian]
      exact hasDerivAt_freeParticleEvolution m s x) t
  simpa [SymplecticForm.hamiltonianFlow_eq] using h.symm

end FiniteDimensional

end TauCeti
