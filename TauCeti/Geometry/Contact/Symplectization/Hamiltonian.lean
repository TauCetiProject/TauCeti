/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Hamiltonian
public import TauCeti.Geometry.Contact.Symplectization.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Hamiltonian dynamics on the symplectization

Let `α` be a one-form on a manifold `M`, and equip `ℝ × M` with the symplectization form
`θ = eᵗ α` and the two-form `ω = dθ` (`TauCeti.SmoothForm.symplectization`). A function `f` on `M`
gives the function `(t, x) ↦ eᵗ f(x)` on `ℝ × M`, homogeneous of degree one under the Liouville
flow of `∂_t`. This file computes its symplectic Hamiltonian vector field for the convention
`ι_(X_F) ω = dF`:

`X_(eᵗ f) = (R_α f) ∂_t - X_f`,

where `R_α` is the Reeb vector field and `X_f` is the contact Hamiltonian vector field of `f`,
with the conventions `α(X_f) = f`, `ι_(X_f) dα = (R_α f) α - df` of
`TauCeti.SmoothForm.IsContactHamiltonianVectorField`. The equation holds for every one-form `α`
and every contact Hamiltonian vector field of `f`
(`TauCeti.SmoothForm.IsContactHamiltonianVectorField.isHamiltonianVectorField_symplectization`);
for a contact form on a finite-dimensional manifold it identifies the Hamiltonian vector field
(`TauCeti.SmoothForm.IsContactForm.hamiltonianVectorField_symplectization`). For `f = 1` it says
that the Hamiltonian vector field of `eᵗ` is minus the Reeb vector field
(`TauCeti.SmoothForm.IsContactForm.hamiltonianVectorField_exp_symplectization`). In the radial
coordinate `r = eᵗ`, for which `ω = d(r α)` and `r ∂_r = ∂_t`, these are the formulas
`X_(r f) = r (R_α f) ∂_r - X_f` and `X_r = -R_α`.

Evaluating `ω` on two such fields compares the Poisson bracket of `ω` with the Jacobi bracket of
the contact form:

`{eᵗ f, eᵗ g}_ω = eᵗ (dα(X_f, X_g) + f R_α(g) - g R_α(f))`

(`TauCeti.SmoothForm.IsContactForm.poissonBracket_symplectization`).

## Main results

* `TauCeti.SmoothForm.IsContactHamiltonianVectorField.isHamiltonianVectorField_symplectization`:
  `(R_α f) ∂_t - X_f` is a Hamiltonian vector field of `eᵗ f`.
* `TauCeti.SmoothForm.IsContactForm.hamiltonianVectorField_symplectization`:
  `X_(eᵗ f) = (R_α f) ∂_t - X_f` for a contact form.
* `TauCeti.SmoothForm.IsContactForm.hamiltonianVectorField_exp_symplectization`:
  `X_(eᵗ) = -R_α`.
* `TauCeti.SmoothForm.IsContactForm.poissonBracket_symplectization`: the Poisson bracket of
  `eᵗ f` and `eᵗ g`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.3 (contact Hamiltonians) and Appendix B (symplectization).
* A. Lichnerowicz, *Les variétés de Jacobi et leurs algèbres de Lie associées*, J. Math. Pures
  Appl. 57 (1978), 453–488 (Jacobi brackets as homogeneous Poisson brackets).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1} {f g : M → ℝ} {X : (x : M) → TangentSpace I x}

omit [IsManifold I ∞ M] in
/-- The derivative of `(t, x) ↦ eᵗ f(x)` at `(t, x)` sends `(s, w)` to `eᵗ (s f(x) + df_x(w))`. -/
private theorem mvfderiv_exp_mul_apply {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x) (t : ℝ)
    (w : TangentSpace (𝓘(ℝ).prod I) (t, x)) :
    mvfderiv (𝓘(ℝ).prod I) (fun p : ℝ × M ↦ Real.exp p.1 * f p.2) (t, x) w =
      Real.exp t *
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) t (Manifold.tangentSpaceProdEquiv (t, x) w).1 * f x +
          mvfderiv I f x (Manifold.tangentSpaceProdEquiv (t, x) w).2) := by
  have hexp : MDifferentiableAt (𝓘(ℝ).prod I) 𝓘(ℝ) (fun p : ℝ × M ↦ Real.exp p.1) (t, x) :=
    ((Real.contDiff_exp (n := 1)).contMDiff.comp contMDiff_fst (t, x)).mdifferentiableAt
      one_ne_zero
  have hf' : MDifferentiableAt (𝓘(ℝ).prod I) 𝓘(ℝ) (fun p : ℝ × M ↦ f p.2) (t, x) :=
    hf.comp (t, x) mdifferentiableAt_snd
  have h₁ : mvfderiv (𝓘(ℝ).prod I) (fun p : ℝ × M ↦ f p.2) (t, x) w =
      mvfderiv I f x (Manifold.tangentSpaceProdEquiv (t, x) w).2 := by
    rw [Manifold.tangentSpaceProdEquiv_apply]
    exact mvfderiv_comp_snd_apply f (t, x) w
  have h₂ : mvfderiv (𝓘(ℝ).prod I) (fun p : ℝ × M ↦ Real.exp p.1) (t, x) w =
      NormedSpace.fromTangentSpace (𝕜 := ℝ) t (Manifold.tangentSpaceProdEquiv (t, x) w).1 *
        Real.exp t := by
    rw [Manifold.tangentSpaceProdEquiv_apply, ← smul_eq_mul]
    exact (Real.hasDerivAt_exp t).mvfderiv_comp_fst_apply w
  rw [mvfderiv_fun_mul hexp hf', add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, h₁,
    h₂]
  ring

omit [IsManifold I ∞ M] in
/-- The components of the vector field `c ∂_t - Y` on `ℝ × M` at `p` are `c` and `-Y`. -/
private theorem tangentSpaceProdEquiv_smul_sub (c : ℝ) (Y : (x : M) → TangentSpace I x)
    (p : ℝ × M) :
    Manifold.tangentSpaceProdEquiv p
        (c • Manifold.prodVectorField (constVectorField (1 : ℝ))
            (0 : (x : M) → TangentSpace I x) p -
          Manifold.prodVectorField (0 : (t : ℝ) → TangentSpace 𝓘(ℝ) t) Y p) =
      ((NormedSpace.fromTangentSpace p.1).symm c, -Y p.2) := by
  rw [map_sub, map_smul, Manifold.tangentSpaceProdEquiv_prodVectorField,
    Manifold.tangentSpaceProdEquiv_prodVectorField, constVectorField_apply]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sub, Prod.smul_fst, Pi.zero_apply, sub_zero]
    rw [← map_smul, smul_eq_mul, mul_one]
  · simp only [Prod.snd_sub, Prod.smul_snd, Pi.zero_apply, smul_zero, zero_sub]

namespace IsContactHamiltonianVectorField

/-- **Hamiltonian vector fields on the symplectization.** If `X` is a contact Hamiltonian vector
field of a differentiable function `f` for a one-form `α`, then `(R_α f) ∂_t - X` is a
Hamiltonian vector field of `(t, x) ↦ eᵗ f(x)` for the exterior derivative of the
symplectization form `eᵗ α`. No contact condition on `α` is needed. -/
theorem isHamiltonianVectorField_symplectization (hX : α.IsContactHamiltonianVectorField f X)
    (hf : MDifferentiable I 𝓘(ℝ) f) :
    SmoothTwoForm.IsHamiltonianVectorField (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization)
      (fun p ↦ Real.exp p.1 * f p.2)
      (fun p ↦ mvfderiv I f p.2 (α.reebVectorField p.2) •
          Manifold.prodVectorField (constVectorField (1 : ℝ)) (0 : (x : M) → TangentSpace I x) p -
        Manifold.prodVectorField (0 : (t : ℝ) → TangentSpace 𝓘(ℝ) t) X p) := by
  rw [SmoothTwoForm.isHamiltonianVectorField_iff]
  rintro ⟨t, x⟩ w
  have hneg : α.1 x ![-X x] = -f x := by
    rw [← degreeOneEquiv_apply_apply_vec, map_neg, degreeOneEquiv_apply_apply_vec, hX.apply_eq x]
  rw [eval₂_mextDerivₗ_symplectization, mvfderiv_exp_mul_apply (hf x),
    tangentSpaceProdEquiv_smul_sub]
  dsimp only
  rw [ContinuousLinearEquiv.apply_symm_apply, hneg,
    SmoothBundleForm.eval₂_neg_left, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply,
    hX.mextDeriv_apply_eq x]
  ring

end IsContactHamiltonianVectorField

namespace IsContactForm

variable [FiniteDimensional ℝ E] (hα : α.IsContactForm)
include hα

/-- **The Hamiltonian vector field of a homogeneous function on the symplectization.** For a
contact form `α` and a differentiable function `f`, the Hamiltonian vector field of
`(t, x) ↦ eᵗ f(x)` for `d(eᵗ α)` is `(R_α f) ∂_t - X_f`, where `X_f` is the contact Hamiltonian
vector field of `f`. In the radial coordinate `r = eᵗ` this is `X_(r f) = r (R_α f) ∂_r - X_f`. -/
theorem hamiltonianVectorField_symplectization (hf : MDifferentiable I 𝓘(ℝ) f) :
    SmoothTwoForm.hamiltonianVectorField (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization)
        (fun p ↦ Real.exp p.1 * f p.2) =
      fun p ↦ mvfderiv I f p.2 (α.reebVectorField p.2) •
          Manifold.prodVectorField (constVectorField (1 : ℝ)) (0 : (x : M) → TangentSpace I x) p -
        Manifold.prodVectorField (0 : (t : ℝ) → TangentSpace 𝓘(ℝ) t)
          (α.contactHamiltonianVectorField f) p :=
  (hα.isSymplectic_mextDerivₗ_symplectization.isNondegenerate.isHamiltonianVectorField_iff_eq.1
    ((hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f
      ).isHamiltonianVectorField_symplectization hf)).symm

/-- **The Hamiltonian vector field of `eᵗ` is minus the Reeb vector field.** For a contact form
`α`, the Hamiltonian vector field of the function `(t, x) ↦ eᵗ` on the symplectization is
`-R_α`, tangent to the factor `M`. In the radial coordinate `r = eᵗ` this is `X_r = -R_α`. -/
theorem hamiltonianVectorField_exp_symplectization :
    SmoothTwoForm.hamiltonianVectorField (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization)
        (fun p ↦ Real.exp p.1) =
      Manifold.prodVectorField (0 : (t : ℝ) → TangentSpace 𝓘(ℝ) t) (-α.reebVectorField) := by
  have h := hα.hamiltonianVectorField_symplectization (f := fun _ ↦ 1) mdifferentiable_const
  simp only [mul_one, mvfderiv_const, zero_apply, zero_smul, zero_sub,
    hα.contactHamiltonianVectorField_const, one_smul] at h
  rw [h]
  funext p
  rw [← Pi.neg_apply, ← Manifold.prodVectorField_neg, neg_zero]

/-- **Poisson brackets on the symplectization.** For a contact form `α` and differentiable
functions `f` and `g`, the Poisson bracket for `d(eᵗ α)` of `(t, x) ↦ eᵗ f(x)` and
`(t, x) ↦ eᵗ g(x)` is `eᵗ (dα(X_f, X_g) + f R_α(g) - g R_α(f))`, where `X_f` and `X_g` are the
contact Hamiltonian vector fields: it is `eᵗ` times the Jacobi bracket of `f` and `g`. In the
radial coordinate `r = eᵗ`, `{r f, r g} = r {f, g}_α`. -/
theorem poissonBracket_symplectization (hf : MDifferentiable I 𝓘(ℝ) f)
    (hg : MDifferentiable I 𝓘(ℝ) g) (p : ℝ × M) :
    SmoothTwoForm.poissonBracket (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization)
        (fun p ↦ Real.exp p.1 * f p.2) (fun p ↦ Real.exp p.1 * g p.2) p =
      Real.exp p.1 *
        ((mextDerivₗ I 1 α).eval₂ p.2 (α.contactHamiltonianVectorField f p.2)
            (α.contactHamiltonianVectorField g p.2) +
          f p.2 * mvfderiv I g p.2 (α.reebVectorField p.2) -
          g p.2 * mvfderiv I f p.2 (α.reebVectorField p.2)) := by
  have hneg (k : M → ℝ) : α.1 p.2 ![-α.contactHamiltonianVectorField k p.2] = -k p.2 := by
    rw [← degreeOneEquiv_apply_apply_vec, map_neg, degreeOneEquiv_apply_apply_vec,
      hα.apply_contactHamiltonianVectorField]
  rw [SmoothTwoForm.poissonBracket_def, hα.hamiltonianVectorField_symplectization hf,
    hα.hamiltonianVectorField_symplectization hg, eval₂_mextDerivₗ_symplectization,
    tangentSpaceProdEquiv_smul_sub, tangentSpaceProdEquiv_smul_sub]
  dsimp only
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply, hneg, hneg,
    SmoothBundleForm.eval₂_neg_left, SmoothBundleForm.eval₂_swap _ _ _ (-_),
    SmoothBundleForm.eval₂_neg_left,
    SmoothBundleForm.eval₂_swap _ _ (α.contactHamiltonianVectorField g p.2)]
  ring

end IsContactForm

end SmoothForm

end TauCeti
