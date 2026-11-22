/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Hyperregular
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ModelSpace
public import TauCeti.Geometry.Symplectic.Cotangent.SignConvention

/-!
# Hamilton's equations on the cotangent bundle of a normed space

Let `E` be a finite-dimensional real normed space. Its cotangent bundle `T*E`, with the canonical
symplectic form `ω = -dλ` (`TauCeti.CotangentBundle.symplecticForm`), is globally the linear
cotangent space `E × E'` through `(q, p) ↦ (q, p)`
(`TauCeti.CotangentBundle.modelSpaceDiffeomorph`), and this diffeomorphism carries `ω` to the
constant form `TauCeti.strongDualCotangentSymplecticForm`. This file transports the Hamiltonian
dynamics of the linear theory to the manifold `T*E`.

* For every function `h` of the coordinates `(q, p)`, the Hamiltonian vector field of `h(q, p)` on
  `T*E` is, at each covector, the Hamiltonian vector field of `h` on `E × E'`
  (`TauCeti.CotangentBundle.symplecticForm_hamiltonianVectorField_comp_modelSpaceDiffeomorph`),
  and the same holds for Poisson brackets. No differentiability of `h` is needed.
* Hence **Hamilton's equations** `q' = ∂H/∂p`, `p' = -∂H/∂q` hold on `T*E`: if
  `dh(δq, δp) = α(δq) + δp(b)`, then `X_H = (b, -α)`. On the line, read through the coordinates
  `(q, p 1)` of `T*ℝ ≃ ℝ × ℝ` (`TauCeti.CotangentBundle.lineDiffeomorph`), a Hamiltonian with
  partial derivatives `a` in `q` and `b` in `p` has `X_H = (b, -a)`.

The second half works out a particle of mass `m` in a potential `V` on the line. Its Hamiltonian
`H(q, p) = p² / (2 m) + V(q)` has the Hamiltonian vector field `(p / m, -V'(q))`. The Lagrangian
`L(q, v) = (m / 2) v² - V(q)` on `Tℝ` is hyperregular exactly when `m ≠ 0`
(`TauCeti.isHyperregularLagrangian_mul_sq_sub_iff`), its Legendre map is `(q, v) ↦ (q, m v)`
(`TauCeti.lineDiffeomorph_legendreMap_mul_sq_sub`), and its Hamiltonian `E_L ∘ FL⁻¹` is exactly
`p² / (2 m) + V(q)` (`TauCeti.IsHyperregularLagrangian.hamiltonian_mul_sq_sub`). The differential
of the Legendre map is `(δq, δv) ↦ (δq, m δv)`
(`TauCeti.mfderiv_lineDiffeomorph_comp_legendreMap_mul_sq_sub`), so at `p = m v` it sends the
vector `(v, -V'(q) / m)` to the Hamiltonian vector field `(v, -V'(q))` of `H`
(`TauCeti.IsHyperregularLagrangian.mfderiv_legendreMap_mul_sq_sub_eq_hamiltonianVectorField`).
This is the coordinate form, for this Lagrangian, of the conjugation `dFL(X_E) = X_H` of the
Lagrangian and Hamiltonian vector fields
(`TauCeti.IsHyperregularLagrangian.mfderiv_legendreMap_hamiltonianVectorField`).

## Main results

In the namespace `TauCeti.CotangentBundle`:

* `symplecticForm_hamiltonianVectorField_comp_modelSpaceDiffeomorph`,
  `symplecticForm_poissonBracket_comp_modelSpaceDiffeomorph`: Hamiltonian vector fields and
  Poisson brackets on `T*E` in global coordinates.
* `symplecticForm_hamiltonianVectorField_comp_modelSpaceDiffeomorph_of_hasFDerivAt`,
  `mfderiv_lineDiffeomorph_symplecticForm_hamiltonianVectorField_comp_lineDiffeomorph`:
  Hamilton's equations on `T*E` and on `T*ℝ`.
* `mfderiv_lineDiffeomorph_symplecticForm_hamiltonianVectorField_sq_div_add`: the Hamiltonian
  vector field of `p² / (2 m) + V(q)` is `(p / m, -V'(q))`.

In the namespace `TauCeti`:

* `IsHyperregularLagrangian.hamiltonian_mul_sq_sub`: the Hamiltonian of `(m / 2) v² - V(q)` is
  `p² / (2 m) + V(q)`.
* `IsHyperregularLagrangian.mfderiv_legendreMap_mul_sq_sub_eq_hamiltonianVectorField`: the
  differential of its Legendre map sends `(v, -V'(q) / m)` to the Hamiltonian vector field
  `(v, -V'(q))`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 14, 15 and 37.
* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Sections 3.3 and 3.6.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.CotangentBundle

section ModelSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Hamiltonian vector fields on `T*E` in global coordinates.** The Hamiltonian vector field of
`h(q, p)` on the cotangent bundle of `E`, for the canonical symplectic form, is at each covector
the Hamiltonian vector field of `h` on the linear cotangent space `E × E'`. Where `h` is not
differentiable both sides vanish. -/
@[simp]
theorem symplecticForm_hamiltonianVectorField_comp_modelSpaceDiffeomorph
    (h : E × StrongDual ℝ E → ℝ) (z : CotangentBundle 𝓘(ℝ, E) E) :
    (symplecticForm 𝓘(ℝ, E) E).hamiltonianVectorField (h ∘ modelSpaceDiffeomorph E) z =
      strongDualCotangentSymplecticForm.hamiltonianVectorField h (modelSpaceDiffeomorph E z) := by
  by_cases hh : DifferentiableAt ℝ h (modelSpaceDiffeomorph E z)
  · have key := isSymplectic_symplecticForm.isNondegenerate.mfderiv_hamiltonianVectorField_comp
      (SymplecticForm.isNondegenerate_constSmooth strongDualCotangentSymplecticForm)
      (modelSpaceDiffeomorph E).contMDiff (mpullback_modelSpaceDiffeomorph_constSmooth E)
      (by rw [mfderiv_modelSpaceDiffeomorph]; exact Function.surjective_id) hh.mdifferentiableAt
    rwa [mfderiv_modelSpaceDiffeomorph, SymplecticForm.hamiltonianVectorField_constSmooth] at key
  · have hd : ¬MDifferentiableAt (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ)
        (h ∘ modelSpaceDiffeomorph E) z := fun hd ↦ hh <| by
      -- `h` is `h ∘ Φ` read through the inverse of the diffeomorphism `Φ`.
      rw [← (modelSpaceDiffeomorph E).symm_apply_apply z] at hd
      have := hd.comp (modelSpaceDiffeomorph E z)
        ((modelSpaceDiffeomorph E).symm.mdifferentiable (by simp) _)
      rwa [show (h ∘ modelSpaceDiffeomorph E) ∘ (modelSpaceDiffeomorph E).symm = h from
        funext fun w ↦ congrArg h ((modelSpaceDiffeomorph E).apply_symm_apply w),
        mdifferentiableAt_iff_differentiableAt] at this
    rw [SmoothTwoForm.hamiltonianVectorField_eq_zero_of_not_mdifferentiableAt hd]
    exact ((SymplecticForm.hamiltonianVectorField_eq_zero_iff _ _ _).2
      (fderiv_zero_of_not_differentiableAt hh)).symm

/-- **Hamilton's equations on `T*E`.** If `h` has derivative `(δq, δp) ↦ α(δq) + δp(b)` at the
coordinates of a covector `z`, so that `α = ∂h/∂q` and `b = ∂h/∂p`, then the Hamiltonian vector
field of `h(q, p)` on the cotangent bundle at `z` is `(b, -α)`: `q' = ∂h/∂p` and
`p' = -∂h/∂q`. -/
theorem symplecticForm_hamiltonianVectorField_comp_modelSpaceDiffeomorph_of_hasFDerivAt
    {h : E × StrongDual ℝ E → ℝ} {z : CotangentBundle 𝓘(ℝ, E) E} {α : StrongDual ℝ E} {b : E}
    (hh : HasFDerivAt h (α.comp (ContinuousLinearMap.fst ℝ E (StrongDual ℝ E)) +
      (ContinuousLinearMap.apply ℝ ℝ b).comp (ContinuousLinearMap.snd ℝ E (StrongDual ℝ E)))
      (modelSpaceDiffeomorph E z)) :
    (symplecticForm 𝓘(ℝ, E) E).hamiltonianVectorField (h ∘ modelSpaceDiffeomorph E) z =
      (b, -α) := by
  rw [symplecticForm_hamiltonianVectorField_comp_modelSpaceDiffeomorph,
    strongDualCotangentSymplecticForm_hamiltonianVectorField hh]

/-- **Poisson brackets on `T*E` in global coordinates.** The Poisson bracket of `h(q, p)` and
`k(q, p)` on the cotangent bundle of `E` is at each covector the Poisson bracket of `h` and `k` on
the linear cotangent space `E × E'`. -/
@[simp]
theorem symplecticForm_poissonBracket_comp_modelSpaceDiffeomorph
    (h k : E × StrongDual ℝ E → ℝ) (z : CotangentBundle 𝓘(ℝ, E) E) :
    (symplecticForm 𝓘(ℝ, E) E).poissonBracket (h ∘ modelSpaceDiffeomorph E)
        (k ∘ modelSpaceDiffeomorph E) z =
      strongDualCotangentSymplecticForm.poissonBracket h k (modelSpaceDiffeomorph E z) := by
  rw [SmoothTwoForm.poissonBracket_def, SymplecticForm.poissonBracket_def, eval₂_symplecticForm,
    symplecticForm_hamiltonianVectorField_comp_modelSpaceDiffeomorph,
    symplecticForm_hamiltonianVectorField_comp_modelSpaceDiffeomorph]

end ModelSpace

section Line

/-- **Hamilton's equations on `T*ℝ`.** Let `h(q, p)` have partial derivatives `a` in `q` and `b`
in `p` at the coordinates `(q, p 1)` of a covector `z` of the line. Then the Hamiltonian vector
field of `h(q, p 1)` at `z`, read in these coordinates, is `(b, -a)`. -/
theorem mfderiv_lineDiffeomorph_symplecticForm_hamiltonianVectorField_comp_lineDiffeomorph
    {h : ℝ × ℝ → ℝ} {z : CotangentBundle 𝓘(ℝ) ℝ} {a b : ℝ}
    (hh : HasFDerivAt h (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (lineDiffeomorph ℝ z)) :
    mfderiv (𝓘(ℝ).prod 𝓘(ℝ, ℝ →L[ℝ] ℝ)) 𝓘(ℝ, ℝ × ℝ) (lineDiffeomorph ℝ) z
        ((symplecticForm 𝓘(ℝ) ℝ).hamiltonianVectorField (h ∘ lineDiffeomorph ℝ) z) = (b, -a) := by
  -- In the coordinates `(q, p)` of `T*ℝ ≃ ℝ × ℝ'`, the Hamiltonian is `h(q, p 1)`.
  set P : ℝ × StrongDual ℝ ℝ →L[ℝ] ℝ × ℝ := (ContinuousLinearMap.fst ℝ ℝ (StrongDual ℝ ℝ)).prod
    ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ (StrongDual ℝ ℝ)))
  have hPapply (q : ℝ) (p : StrongDual ℝ ℝ) : P (q, p) = (q, p 1) := by simp [P]
  have hP : h ∘ lineDiffeomorph ℝ = (h ∘ P) ∘ modelSpaceDiffeomorph ℝ :=
    funext fun w ↦ by
      simp only [Function.comp_apply, lineDiffeomorph_apply, modelSpaceDiffeomorph_apply]
      exact congrArg h (hPapply w.proj w.snd).symm
  have hz : P (modelSpaceDiffeomorph ℝ z) = lineDiffeomorph ℝ z := by
    rw [modelSpaceDiffeomorph_apply, lineDiffeomorph_apply]
    exact hPapply z.proj z.snd
  rw [← hz] at hh
  have hd : HasFDerivAt (h ∘ P) ((a • ContinuousLinearMap.id ℝ ℝ).comp
      (ContinuousLinearMap.fst ℝ ℝ (StrongDual ℝ ℝ)) + (ContinuousLinearMap.apply ℝ ℝ b).comp
      (ContinuousLinearMap.snd ℝ ℝ (StrongDual ℝ ℝ))) (modelSpaceDiffeomorph ℝ z) := by
    refine (hh.comp (modelSpaceDiffeomorph ℝ z) P.hasFDerivAt).congr_fderiv ?_
    ext v
    · simp [P]
    · simpa [P, mul_comm] using Dual.apply_one_mul_eq (v : Module.Dual ℝ ℝ) b
  rw [hP, symplecticForm_hamiltonianVectorField_comp_modelSpaceDiffeomorph_of_hasFDerivAt hd,
    mfderiv_lineDiffeomorph_apply]
  exact Prod.ext rfl (by simp)

variable {m : ℝ} {V : ℝ → ℝ}

/-- **A particle in a potential on the line, Hamiltonian side.** The Hamiltonian
`H(q, p) = p² / (2 m) + V(q)` on `T*ℝ` has the Hamiltonian vector field `(p / m, -V'(q))` in the
coordinates `(q, p 1)`, at every covector over a point where `V` is differentiable. -/
theorem mfderiv_lineDiffeomorph_symplecticForm_hamiltonianVectorField_sq_div_add
    {z : CotangentBundle 𝓘(ℝ) ℝ} (hV : DifferentiableAt ℝ V z.proj) :
    mfderiv (𝓘(ℝ).prod 𝓘(ℝ, ℝ →L[ℝ] ℝ)) 𝓘(ℝ, ℝ × ℝ) (lineDiffeomorph ℝ) z
        ((symplecticForm 𝓘(ℝ) ℝ).hamiltonianVectorField
          (fun z : CotangentBundle 𝓘(ℝ) ℝ ↦ z.snd (1 : ℝ) ^ 2 / (2 * m) + V z.proj) z) =
      (z.snd (1 : ℝ) / m, -deriv V z.proj) := by
  rw [show (fun z : CotangentBundle 𝓘(ℝ) ℝ ↦ z.snd (1 : ℝ) ^ 2 / (2 * m) + V z.proj) =
      (fun y : ℝ × ℝ ↦ y.2 ^ 2 / (2 * m) + V y.1) ∘ lineDiffeomorph ℝ from
    funext fun w ↦ by simp]
  refine mfderiv_lineDiffeomorph_symplecticForm_hamiltonianVectorField_comp_lineDiffeomorph ?_
  rw [lineDiffeomorph_apply]
  have hq : HasFDerivAt (fun y : ℝ × ℝ ↦ V y.1)
      ((deriv V z.proj) • ContinuousLinearMap.fst ℝ ℝ ℝ) (z.proj, z.snd (1 : ℝ)) :=
    hV.hasDerivAt.comp_hasFDerivAt (z.proj, z.snd (1 : ℝ)) hasFDerivAt_fst
  have hp : HasFDerivAt (fun y : ℝ × ℝ ↦ y.2 ^ 2 / (2 * m))
      ((z.snd (1 : ℝ) / m) • ContinuousLinearMap.snd ℝ ℝ ℝ) (z.proj, z.snd (1 : ℝ)) := by
    simp only [div_eq_mul_inv]
    refine (HasFDerivAt.mul_const (HasFDerivAt.pow
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (z.proj, z.snd (1 : ℝ)))) 2) (2 * m)⁻¹).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp only [smul_apply, ContinuousLinearMap.coe_snd', smul_eq_mul]
    ring
  exact (hp.add hq).congr_fderiv (add_comm _ _)

end Line

end TauCeti.CotangentBundle

namespace TauCeti

open CotangentBundle

/-! ### A particle in a potential on the line, Lagrangian side

The Lagrangian below is `L(q, v) = (m / 2) v² - V(q)` on `Tℝ`. Its velocity `v.snd` lies in the
tangent space `TangentSpace 𝓘(ℝ, ℝ) v.proj`, which is `ℝ` by definition but carries no
multiplication, so the square and the product `m v` are written with explicit real operations. -/

section Particle

variable {m : ℝ} {V : ℝ → ℝ}

/-- The particle Lagrangian `(m / 2) v² - V(q)` is the mechanical Lagrangian with kinetic form
`g(v, w) = m v w`. -/
private theorem mul_sq_sub_eq_mechanicalLagrangian :
    (fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ m / 2 * @HPow.hPow ℝ ℕ ℝ _ v.snd 2 - V v.proj) =
      mechanicalLagrangian (fun _ ↦ m • ContinuousLinearMap.mul ℝ ℝ) V := by
  -- State the identity for a real velocity, which `v.snd` then instantiates.
  have key (w c : ℝ) : m / 2 * w ^ 2 - c = 2⁻¹ * (m • ContinuousLinearMap.mul ℝ ℝ) w w - c := by
    simp only [smul_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
    ring
  exact funext fun v ↦ (key v.snd (V v.proj)).trans
    (mechanicalLagrangian_apply (fun _ ↦ m • ContinuousLinearMap.mul ℝ ℝ) V v).symm

/-- The kinetic form `g(v, w) = m v w` of the particle is symmetric. -/
private theorem smul_mul_symm (_ : ℝ) (v w : ℝ) :
    (m • ContinuousLinearMap.mul ℝ ℝ) v w = (m • ContinuousLinearMap.mul ℝ ℝ) w v := by
  simp only [smul_apply, ContinuousLinearMap.mul_apply', mul_comm v w]

/-- The kinetic form `g(v, w) = m v w` is invertible onto the dual exactly when `m ≠ 0`. -/
private theorem isInvertible_smul_mul_iff :
    (m • ContinuousLinearMap.mul ℝ ℝ).IsInvertible ↔ m ≠ 0 := by
  refine ⟨fun h hm ↦ ?_, fun hm ↦
    .of_inverse (g := m⁻¹ • ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)) ?_ ?_⟩
  · exact one_ne_zero (h.injective (a₁ := 1) (a₂ := 0) (by simp [hm]))
  · ext; simp [hm]
  · ext; simp [hm]

/-- **The particle Lagrangian is hyperregular exactly for nonzero mass.** The Lagrangian
`(m / 2) v² - V(q)` on the line is hyperregular exactly when `m ≠ 0`, for every potential `V`. -/
theorem isHyperregularLagrangian_mul_sq_sub_iff :
    IsHyperregularLagrangian
        (fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ m / 2 * @HPow.hPow ℝ ℕ ℝ _ v.snd 2 - V v.proj) ↔
      m ≠ 0 := by
  rw [mul_sq_sub_eq_mechanicalLagrangian, isHyperregularLagrangian_mechanicalLagrangian_iff
    smul_mul_symm]
  exact ⟨fun h ↦ isInvertible_smul_mul_iff.1 (h 0), fun hm _ ↦ isInvertible_smul_mul_iff.2 hm⟩

/-- **The Legendre map of the particle Lagrangian** `(m / 2) v² - V(q)` is `(q, v) ↦ (q, m v)` in
the coordinates `(q, p 1)` of `T*ℝ`. -/
theorem lineDiffeomorph_legendreMap_mul_sq_sub (v : TangentBundle 𝓘(ℝ, ℝ) ℝ) :
    lineDiffeomorph ℝ (legendreMap
        (fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ m / 2 * @HPow.hPow ℝ ℕ ℝ _ v.snd 2 - V v.proj) v) =
      (v.proj, @HMul.hMul ℝ ℝ ℝ _ m v.snd) := by
  rw [mul_sq_sub_eq_mechanicalLagrangian, legendreMap_mechanicalLagrangian smul_mul_symm,
    lineDiffeomorph_apply]
  -- State the momentum for a real velocity, which `v.snd` then instantiates.
  have key (w : ℝ) : (m • ContinuousLinearMap.mul ℝ ℝ) w 1 = m * w := by simp
  exact Prod.ext rfl (key v.snd)

/-- **The Hamiltonian of the particle Lagrangian.** The Hamiltonian `E_L ∘ FL⁻¹` of the
hyperregular Lagrangian `(m / 2) v² - V(q)` is the total energy `p² / (2 m) + V(q)`. -/
@[simp]
theorem IsHyperregularLagrangian.hamiltonian_mul_sq_sub
    (h : IsHyperregularLagrangian
      fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ m / 2 * @HPow.hPow ℝ ℕ ℝ _ v.snd 2 - V v.proj)
    (z : CotangentBundle 𝓘(ℝ, ℝ) ℝ) :
    h.hamiltonian z = z.snd (1 : ℝ) ^ 2 / (2 * m) + V z.proj := by
  have hm := isHyperregularLagrangian_mul_sq_sub_iff.1 h
  revert h
  rw [mul_sq_sub_eq_mechanicalLagrangian]
  intro h
  rw [h.hamiltonian_mechanicalLagrangian smul_mul_symm]
  -- State the energy identity for a real covector, which `z.snd` then instantiates: the
  -- covector `p` is `g(u, ·)` for the velocity `u = p 1 / m`.
  have key (p : ℝ →L[ℝ] ℝ) (c : ℝ) :
      2⁻¹ * p ((m • ContinuousLinearMap.mul ℝ ℝ).inverse p) + c = p 1 ^ 2 / (2 * m) + c := by
    obtain ⟨u, rfl⟩ := (isInvertible_smul_mul_iff.2 hm).surjective p
    rw [(isInvertible_smul_mul_iff.2 hm).inverse_apply_self]
    simp only [smul_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
    field_simp
  exact key z.snd (V z.proj)

/-- **Hamilton's equations of the particle Lagrangian.** The Hamiltonian vector field of the
Hamiltonian of `(m / 2) v² - V(q)` is `(p / m, -V'(q))` in the coordinates `(q, p 1)` of `T*ℝ`,
at every covector over a point where `V` is differentiable. -/
theorem IsHyperregularLagrangian.mfderiv_lineDiffeomorph_hamiltonianVectorField_mul_sq_sub
    (h : IsHyperregularLagrangian
      fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ m / 2 * @HPow.hPow ℝ ℕ ℝ _ v.snd 2 - V v.proj)
    {z : CotangentBundle 𝓘(ℝ, ℝ) ℝ} (hV : DifferentiableAt ℝ V z.proj) :
    mfderiv (𝓘(ℝ).prod 𝓘(ℝ, ℝ →L[ℝ] ℝ)) 𝓘(ℝ, ℝ × ℝ) (lineDiffeomorph ℝ) z
        ((symplecticForm 𝓘(ℝ) ℝ).hamiltonianVectorField h.hamiltonian z) =
      (z.snd (1 : ℝ) / m, -deriv V z.proj) := by
  rw [funext h.hamiltonian_mul_sq_sub]
  exact mfderiv_lineDiffeomorph_symplecticForm_hamiltonianVectorField_sq_div_add hV

/-- In the global coordinates `(q, v)` of `Tℝ`, given by any of its charts, and `(q, p 1)` of
`T*ℝ`, the Legendre map of `(m / 2) v² - V(q)` is the linear map `(q, v) ↦ (q, m v)`. -/
private theorem lineDiffeomorph_comp_legendreMap_mul_sq_sub (v₀ : TangentBundle 𝓘(ℝ, ℝ) ℝ) :
    lineDiffeomorph ℝ ∘ legendreMap
        (fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ m / 2 * @HPow.hPow ℝ ℕ ℝ _ v.snd 2 - V v.proj) =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (m • ContinuousLinearMap.snd ℝ ℝ ℝ) ∘
        extChartAt 𝓘(ℝ, ℝ).tangent v₀ := by
  funext v
  have hv : extChartAt 𝓘(ℝ, ℝ).tangent v₀ v = (v.proj, v.snd) := by
    rw [extChartAt_coe, Function.comp_apply, tangentBundle_model_space_coe_chartAt,
      ModelWithCorners.tangent, modelWithCorners_prod_coe]
    simp only [TotalSpace.toProd, Equiv.coe_fn_mk, modelWithCornersSelf_coe, Prod.map_apply, id_eq]
    -- Both pairs are `(v.proj, v.snd)`; they differ only in the type of the second entry, the
    -- tangent space `TangentSpace 𝓘(ℝ, ℝ) v.proj`, which is `ℝ` by definition.
    exact rfl
  -- State the linear map for real coordinates, which `(v.proj, v.snd)` then instantiates.
  have key (q w : ℝ) : (q, m * w) =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (m • ContinuousLinearMap.snd ℝ ℝ ℝ) (q, w) := by simp
  rw [Function.comp_apply, lineDiffeomorph_legendreMap_mul_sq_sub, Function.comp_apply, hv]
  exact key v.proj v.snd

/-- **The differential of the Legendre map of the particle Lagrangian.** In the coordinates
`(q, v)` of `Tℝ` and `(q, p 1)` of `T*ℝ`, the differential of the Legendre map of
`(m / 2) v² - V(q)` is `(δq, δv) ↦ (δq, m δv)`, for every potential `V`. -/
theorem mfderiv_lineDiffeomorph_comp_legendreMap_mul_sq_sub (v : TangentBundle 𝓘(ℝ, ℝ) ℝ)
    (w : TangentSpace 𝓘(ℝ, ℝ).tangent v) :
    mfderiv 𝓘(ℝ, ℝ).tangent 𝓘(ℝ, ℝ × ℝ) (lineDiffeomorph ℝ ∘ legendreMap
        (fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ m / 2 * @HPow.hPow ℝ ℕ ℝ _ v.snd 2 - V v.proj)) v w =
      (w.1, m * w.2) := by
  set A := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (m • ContinuousLinearMap.snd ℝ ℝ ℝ)
  -- State the linear map for real coordinates, which `w` then instantiates.
  have key (u : ℝ × ℝ) : A u = (u.1, m * u.2) := by simp [A]
  rw [lineDiffeomorph_comp_legendreMap_mul_sq_sub v, mfderiv_comp_apply v
    A.differentiableAt.mdifferentiableAt (mdifferentiableAt_extChartAt (mem_chart_source _ v)),
    mfderiv_extChartAt_self, mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    NormedSpace.fromTangentSpace_apply, NormedSpace.fromTangentSpace_symm_apply]
  exact key w

/-- **The Legendre map carries the motion of the particle to Hamilton's equations.** For the
hyperregular Lagrangian `(m / 2) v² - V(q)` and a velocity `v` over a point `q` where `V` is
differentiable, the differential of the Legendre map sends `(v, -V'(q) / m)` to the Hamiltonian
vector field of the Hamiltonian `p² / (2 m) + V(q)` at the momentum `p = m v`, whose coordinates
are `(v, -V'(q))`. -/
theorem IsHyperregularLagrangian.mfderiv_legendreMap_mul_sq_sub_eq_hamiltonianVectorField
    (h : IsHyperregularLagrangian
      fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ m / 2 * @HPow.hPow ℝ ℕ ℝ _ v.snd 2 - V v.proj)
    {v : TangentBundle 𝓘(ℝ, ℝ) ℝ} (hV : DifferentiableAt ℝ V v.proj) :
    mfderiv 𝓘(ℝ, ℝ).tangent (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ →L[ℝ] ℝ))
        (legendreMap
          (fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ m / 2 * @HPow.hPow ℝ ℕ ℝ _ v.snd 2 - V v.proj)) v
        ((v.snd, -deriv V v.proj / m) : ℝ × ℝ) =
      (symplecticForm 𝓘(ℝ, ℝ) ℝ).hamiltonianVectorField h.hamiltonian (legendreMap
        (fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ m / 2 * @HPow.hPow ℝ ℕ ℝ _ v.snd 2 - V v.proj) v) := by
  have hm := isHyperregularLagrangian_mul_sq_sub_iff.1 h
  have hz := lineDiffeomorph_legendreMap_mul_sq_sub (m := m) (V := V) v
  rw [lineDiffeomorph_apply, Prod.mk.injEq] at hz
  set L := fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ m / 2 * @HPow.hPow ℝ ℕ ℝ _ v.snd 2 - V v.proj
  -- Compare both sides in the coordinates `(q, p 1)` of `T*ℝ`, which are injective on tangent
  -- vectors since a covector `p` of the line is determined by `p 1`.
  have hinj : Function.Injective (mfderiv (𝓘(ℝ).prod 𝓘(ℝ, ℝ →L[ℝ] ℝ)) 𝓘(ℝ, ℝ × ℝ)
      (lineDiffeomorph ℝ) (legendreMap L v)) :=
    fun x y hxy ↦ by
      have hxy' := (mfderiv_lineDiffeomorph_apply ℝ _ x).symm.trans
        (hxy.trans (mfderiv_lineDiffeomorph_apply ℝ _ y))
      obtain ⟨h1, h2⟩ := Prod.mk.inj hxy'
      exact Prod.ext h1 (ContinuousLinearMap.ext_ring h2)
  have hℓFL : MDifferentiableAt 𝓘(ℝ, ℝ).tangent 𝓘(ℝ, ℝ × ℝ)
      (lineDiffeomorph ℝ ∘ legendreMap L) v := by
    rw [lineDiffeomorph_comp_legendreMap_mul_sq_sub v]
    exact ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (m • ContinuousLinearMap.snd ℝ ℝ ℝ)).differentiableAt.mdifferentiableAt.comp v
        (mdifferentiableAt_extChartAt (mem_chart_source _ v))
  have hFL : MDifferentiableAt 𝓘(ℝ, ℝ).tangent (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ →L[ℝ] ℝ))
      (legendreMap L) v :=
    (((lineDiffeomorph ℝ).symm.mdifferentiable (by simp) _).comp v hℓFL).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u ↦ ((lineDiffeomorph ℝ).symm_apply_apply _).symm)
  -- Left side in coordinates: `d(ℓ ∘ FL)(v, -V'/m) = (v, m (-V'/m)) = (v, -V')`.
  have hlhs : mfderiv (𝓘(ℝ).prod 𝓘(ℝ, ℝ →L[ℝ] ℝ)) 𝓘(ℝ, ℝ × ℝ) (lineDiffeomorph ℝ)
      (legendreMap L v) (mfderiv 𝓘(ℝ, ℝ).tangent (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ →L[ℝ] ℝ)) (legendreMap L) v
        ((v.snd, -deriv V v.proj / m) : ℝ × ℝ)) = ((v.snd, -deriv V v.proj) : ℝ × ℝ) := by
    have hcomp := mfderiv_comp_apply v ((lineDiffeomorph ℝ).mdifferentiable (by simp) _) hFL
      ((v.snd, -deriv V v.proj / m) : ℝ × ℝ)
    exact hcomp.symm.trans ((mfderiv_lineDiffeomorph_comp_legendreMap_mul_sq_sub v _).trans
      (Prod.ext rfl (mul_div_cancel₀ _ hm)))
  -- Right side in coordinates: `dℓ(X_H) = (p / m, -V'(q))`, which is `(v, -V')` at `p = m v`.
  have hrhs : mfderiv (𝓘(ℝ).prod 𝓘(ℝ, ℝ →L[ℝ] ℝ)) 𝓘(ℝ, ℝ × ℝ) (lineDiffeomorph ℝ)
      (legendreMap L v) ((symplecticForm 𝓘(ℝ, ℝ) ℝ).hamiltonianVectorField h.hamiltonian
        (legendreMap L v)) = ((v.snd, -deriv V v.proj) : ℝ × ℝ) := by
    rw [h.mfderiv_lineDiffeomorph_hamiltonianVectorField_mul_sq_sub (hz.1 ▸ hV)]
    exact Prod.ext ((congrArg (· / m) hz.2).trans (mul_div_cancel_left₀ _ hm))
      (congrArg (fun q ↦ -deriv V q) hz.1)
  exact hinj (hlhs.trans hrhs.symm)

end Particle

end TauCeti
