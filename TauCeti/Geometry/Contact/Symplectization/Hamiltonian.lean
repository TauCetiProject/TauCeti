/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Hamiltonian
public import TauCeti.Geometry.Contact.Symplectization.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold

/-!
# Hamiltonian vector fields on the symplectization

Let `α` be a contact form on a finite-dimensional manifold `M`, and let `ℝ × M` carry the
symplectic form `ω = d(eᵗ α)` of its symplectization (`TauCeti.SmoothForm.symplectization`). We use
the conventions `ι_(X_F) ω = dF` and `{F, G} = ω(X_F, X_G)` for symplectic Hamiltonian vector fields
and Poisson brackets, and `α(X_f) = f`, `ι_(X_f) dα = (R_α f) α - df` for contact Hamiltonian
vector fields, where `R_α` is the Reeb vector field.

A function `f` on `M` determines the function `eᵗ f` on `ℝ × M`, homogeneous of degree one for
the positive fibre coordinate `r = eᵗ`. Its symplectic Hamiltonian vector field is

`X_(eᵗ f) = (R_α f) ∂_t - X_f`

(`TauCeti.SmoothForm.IsContactForm.hamiltonianVectorField_symplectization_exp_mul`): it is
independent of `t`, its component along `M` is minus the contact Hamiltonian vector field of `f`,
and its component along the real factor is the Reeb derivative of `f`. In terms of `r`, where
`∂_t = r ∂_r`, this reads `X_(r f) = r (R_α f) ∂_r - X_f`. For `f = 1` it gives
`X_(eᵗ) = -R_α` (`TauCeti.SmoothForm.IsContactForm.hamiltonianVectorField_symplectization_exp`).
The equation `ι_Y ω = d(eᵗ f)` for `Y = (R_α f) ∂_t - X` holds for any contact Hamiltonian
vector field `X` of `f` and any one-form `α`
(`TauCeti.SmoothForm.IsContactHamiltonianVectorField.isHamiltonianVectorField_symplectization`);
the contact condition is only used to identify `Y` with the Hamiltonian vector field.

Consequently the Poisson bracket of two homogeneous functions is again homogeneous:

`{eᵗ f, eᵗ g} = eᵗ (dα(X_f, X_g) + f R_α(g) - g R_α(f))`

(`TauCeti.SmoothForm.IsContactForm.poissonBracket_symplectization_exp_mul`). The bracket on the
right is the Jacobi bracket of the contact form `α`; in terms of `r` the identity reads
`{r f, r g} = r {f, g}_α`. In particular `{eᵗ, eᵗ g} = eᵗ R_α(g)`
(`TauCeti.SmoothForm.IsContactForm.poissonBracket_symplectization_exp`).

## Main results

* `TauCeti.SmoothForm.IsContactHamiltonianVectorField.isHamiltonianVectorField_symplectization`:
  `(R_α f) ∂_t - X` is a Hamiltonian vector field of `eᵗ f`.
* `TauCeti.SmoothForm.IsContactForm.hamiltonianVectorField_symplectization_exp_mul`:
  `X_(eᵗ f) = (R_α f) ∂_t - X_f`.
* `TauCeti.SmoothForm.IsContactForm.hamiltonianVectorField_symplectization_exp`:
  `X_(eᵗ) = -R_α`.
* `TauCeti.SmoothForm.IsContactForm.poissonBracket_symplectization_exp_mul`:
  `{eᵗ f, eᵗ g} = eᵗ (dα(X_f, X_g) + f R_α(g) - g R_α(f))`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Appendix 4 (contact structures, symplectization and contact
  Hamiltonians).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.3 (contact Hamiltonians).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1} {f g : M → ℝ} {X : (x : M) → TangentSpace I x}

/-- **Contraction of `d(eᵗ α)` with the lift of a contact Hamiltonian vector field.** If `X` is a
contact Hamiltonian vector field of `f` for a one-form `α`, and `f` is differentiable at `x`, then
at `(t, x)` the contraction of `d(eᵗ α)` with `(R_α f)(x) ∂_t - X(x)` is the differential of
`(t, x) ↦ eᵗ f(x)`. -/
theorem IsContactHamiltonianVectorField.eval₂_mextDerivₗ_symplectization
    (hX : α.IsContactHamiltonianVectorField f X) {p : ℝ × M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f p.2) (w : TangentSpace (𝓘(ℝ).prod I) p) :
    SmoothBundleForm.eval₂ (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization) p
        ((Manifold.tangentSpaceProdEquiv p).symm
          ((NormedSpace.fromTangentSpace p.1).symm (mvfderiv I f p.2 (α.reebVectorField p.2)),
            -X p.2)) w =
      mvfderiv (𝓘(ℝ).prod I) (fun q : ℝ × M ↦ Real.exp q.1 * f q.2) p w := by
  have hexp (s : TangentSpace 𝓘(ℝ) p.1) :
      mvfderiv 𝓘(ℝ) Real.exp p.1 s = NormedSpace.fromTangentSpace p.1 s * Real.exp p.1 := by
    rw [mvfderiv_eq_fderiv, (Real.hasDerivAt_exp p.1).hasFDerivAt.fderiv]
    -- `ContinuousLinearMap.toSpanSingleton ℝ (eᵗ)` sends `s` to `s • eᵗ`, read through
    -- `NormedSpace.fromTangentSpace`.
    rfl
  rw [SmoothForm.eval₂_mextDerivₗ_symplectization,
    mvfderiv_comp_fst_mul_comp_snd_apply Real.differentiable_exp.differentiableAt.mdifferentiableAt
      hf,
    ContinuousLinearEquiv.apply_symm_apply, SmoothBundleForm.eval₂_neg_left,
    SmoothBundleForm.eval₂_apply, mextDerivₗ_apply, hX.mextDeriv_apply_eq]
  simp only [ContinuousLinearEquiv.apply_symm_apply, apply_neg_vec, hX.apply_eq,
    Manifold.tangentSpaceProdEquiv_apply]
  linear_combination -f p.2 * hexp w.1

/-- **Hamiltonian vector fields of homogeneous functions on the symplectization.** If `X` is a
contact Hamiltonian vector field of a differentiable function `f` for a one-form `α`, then
`(t, x) ↦ (R_α f)(x) ∂_t - X(x)` is a Hamiltonian vector field of `(t, x) ↦ eᵗ f(x)` for
`d(eᵗ α)`. No contact condition on `α` is needed. -/
theorem IsContactHamiltonianVectorField.isHamiltonianVectorField_symplectization
    (hX : α.IsContactHamiltonianVectorField f X) (hf : MDifferentiable I 𝓘(ℝ) f) :
    SmoothTwoForm.IsHamiltonianVectorField (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization)
      (fun p ↦ Real.exp p.1 * f p.2)
      (fun p ↦ (Manifold.tangentSpaceProdEquiv p).symm
        ((NormedSpace.fromTangentSpace p.1).symm (mvfderiv I f p.2 (α.reebVectorField p.2)),
          -X p.2)) :=
  SmoothTwoForm.isHamiltonianVectorField_iff.2 fun p ↦
    hX.eval₂_mextDerivₗ_symplectization (hf p.2)

namespace IsContactForm

variable [FiniteDimensional ℝ E] (hα : α.IsContactForm)
include hα

/-- **The Hamiltonian vector field of a homogeneous function on the symplectization.** For a
contact form `α` and a function `f` differentiable at `x`, the Hamiltonian vector field of
`(t, x) ↦ eᵗ f(x)` for `d(eᵗ α)` at `(t, x)` is `(R_α f) ∂_t - X_f`, where `X_f` is the contact
Hamiltonian vector field of `f`. With `r = eᵗ`, this is `X_(r f) = r (R_α f) ∂_r - X_f`. -/
theorem hamiltonianVectorField_symplectization_exp_mul {p : ℝ × M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f p.2) :
    SmoothTwoForm.hamiltonianVectorField (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization)
        (fun q ↦ Real.exp q.1 * f q.2) p =
      (Manifold.tangentSpaceProdEquiv p).symm
        ((NormedSpace.fromTangentSpace p.1).symm (mvfderiv I f p.2 (α.reebVectorField p.2)),
          -α.contactHamiltonianVectorField f p.2) := by
  have hσ := isNondegenerate_mextDerivₗ_symplectization_iff.2 hα
  -- Both vectors have the same flat, the differential of `eᵗ f`, and the flat is injective.
  refine (hσ.isInvertible_flat p).injective (ContinuousLinearMap.ext fun w ↦ ?_)
  rw [hσ.flat_hamiltonianVectorField, SmoothTwoForm.flat_apply,
    IsContactHamiltonianVectorField.eval₂_mextDerivₗ_symplectization
      (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f) hf]

/-- **The Hamiltonian vector field of the fibre coordinate.** For a contact form `α`, the
Hamiltonian vector field of `(t, x) ↦ eᵗ` for `d(eᵗ α)` is `-R_α`, minus the Reeb vector field
along `M`. -/
@[simp]
theorem hamiltonianVectorField_symplectization_exp (p : ℝ × M) :
    SmoothTwoForm.hamiltonianVectorField (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization)
        (fun q ↦ Real.exp q.1) p =
      (Manifold.tangentSpaceProdEquiv p).symm (0, -α.reebVectorField p.2) := by
  have h := hα.hamiltonianVectorField_symplectization_exp_mul (f := fun _ ↦ 1) (p := p)
    mdifferentiableAt_const
  simp only [mul_one, mvfderiv_const, zero_apply, map_zero,
    hα.contactHamiltonianVectorField_const, Pi.smul_apply, one_smul] at h
  exact h

/-- **Poisson brackets of homogeneous functions on the symplectization.** For a contact form `α`
and functions `f` and `g` differentiable at `x`, the Poisson bracket for `d(eᵗ α)` of
`(t, x) ↦ eᵗ f(x)` and `(t, x) ↦ eᵗ g(x)` is `eᵗ (dα(X_f, X_g) + f R_α(g) - g R_α(f))`, where
`X_f`, `X_g` are the contact Hamiltonian vector fields. With `r = eᵗ`, this is
`{r f, r g} = r {f, g}_α` for the Jacobi bracket `{f, g}_α` of `α`. -/
theorem poissonBracket_symplectization_exp_mul {p : ℝ × M} (hf : MDifferentiableAt I 𝓘(ℝ) f p.2)
    (hg : MDifferentiableAt I 𝓘(ℝ) g p.2) :
    SmoothTwoForm.poissonBracket (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization)
        (fun q ↦ Real.exp q.1 * f q.2) (fun q ↦ Real.exp q.1 * g q.2) p =
      Real.exp p.1 * (mextDeriv α.1 p.2 ![α.contactHamiltonianVectorField f p.2,
          α.contactHamiltonianVectorField g p.2] +
        f p.2 * mvfderiv I g p.2 (α.reebVectorField p.2) -
        g p.2 * mvfderiv I f p.2 (α.reebVectorField p.2)) := by
  rw [SmoothTwoForm.poissonBracket_def, hα.hamiltonianVectorField_symplectization_exp_mul hf,
    hα.hamiltonianVectorField_symplectization_exp_mul hg, eval₂_mextDerivₗ_symplectization]
  simp only [ContinuousLinearEquiv.apply_symm_apply, apply_neg_vec,
    hα.apply_contactHamiltonianVectorField, SmoothBundleForm.eval₂_neg_left,
    SmoothBundleForm.eval₂_neg_right, neg_neg]
  rw [SmoothBundleForm.eval₂_apply, mextDerivₗ_apply]
  ring

/-- **The Poisson bracket with the fibre coordinate.** For a contact form `α` and a
function `g` differentiable at `x`, the Poisson bracket for `d(eᵗ α)` of `(t, x) ↦ eᵗ` and
`(t, x) ↦ eᵗ g(x)` is `eᵗ R_α(g)`. -/
theorem poissonBracket_symplectization_exp {p : ℝ × M} (hg : MDifferentiableAt I 𝓘(ℝ) g p.2) :
    SmoothTwoForm.poissonBracket (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization)
        (fun q ↦ Real.exp q.1) (fun q ↦ Real.exp q.1 * g q.2) p =
      Real.exp p.1 * mvfderiv I g p.2 (α.reebVectorField p.2) := by
  have h := hα.poissonBracket_symplectization_exp_mul (f := fun _ ↦ 1) mdifferentiableAt_const hg
  simp only [mul_one, mvfderiv_const, zero_apply, mul_zero, sub_zero, one_mul,
    hα.contactHamiltonianVectorField_const, Pi.smul_apply, one_smul,
    hα.mextDeriv_reebVectorField_left, zero_add] at h
  exact h

end IsContactForm

end SmoothForm

end TauCeti
