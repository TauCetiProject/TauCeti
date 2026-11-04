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
# Hamiltonian vector fields of homogeneous functions on the symplectization

Let `α` be a one-form on a manifold `M`, with Reeb vector field `R_α`, and let
`(ℝ × M, ω = d(eᵗ α))` be its symplectization (`TauCeti.SmoothForm.symplectization`). Write
`r = eᵗ` for the positive fibre coordinate, so that `ω = d(r α)` and `r ∂_r = ∂_t`. The
Hamiltonian conventions are `ι_(X_F) ω = dF` and `{F, G}_ω = ω(X_F, X_G)` for functions on the
symplectization, and `α(X_f) = f`, `ι_(X_f) dα = (R_α f) α - df` for contact Hamiltonian vector
fields of functions `f` on `M`.

A function `f` on `M` gives the function `r f : (t, x) ↦ eᵗ f(x)` on the symplectization, which is
homogeneous of degree one in `r`. This file identifies its Hamiltonian vector field:

`X_(r f) = r (R_α f) ∂_r - X_f = (R_α f) ∂_t - X_f`.

More precisely, for a differentiable `f` and any one-form `α`, the vector field
`(t, x) ↦ (R_α f)(x) ∂_t - X(x)` is a Hamiltonian vector field of `r f` exactly when `X` is a
contact Hamiltonian vector field of `f`
(`TauCeti.SmoothForm.isHamiltonianVectorField_symplectization_iff`). When `α` is a contact form on
a finite-dimensional manifold both vector fields are unique, so the Hamiltonian vector field of
`r f` is `(R_α f) ∂_t - X_f`
(`TauCeti.SmoothForm.IsContactForm.hamiltonianVectorField_symplectization`).
In particular the Hamiltonian vector field of `r` itself is `X_r = -R_α`
(`TauCeti.SmoothForm.IsContactForm.hamiltonianVectorField_symplectization_exp`). The coefficients
of `X_(r f)` only depend on `x`, and its `M`-component is `-X_f`
(`TauCeti.SmoothForm.IsContactForm.hamiltonianVectorField_symplectization_snd`).

The symplectic Poisson bracket of two such functions is again homogeneous of degree one:

`{r f, r g}_ω = r (dα(X_f, X_g) + f R_α(g) - g R_α(f))`

(`TauCeti.SmoothForm.IsContactForm.poissonBracket_symplectization`). The factor in brackets is the
Jacobi bracket `{f, g}_α` of the contact form. Finally the primitive `λ = -eᵗ α` of `ω` recovers
the Hamiltonian, `λ(X_(r f)) = r f`
(`TauCeti.SmoothForm.IsContactForm.symplectization_apply_hamiltonianVectorField`).

The correspondence `f ↦ X_(r f)` does not depend on the chosen contact form within its positive
conformal class. If `α' = h α` with `h > 0`, the points `(t, x)` of both symplectizations
parametrize the positive half of the annihilator line of `ker α`, through `eᵗ α_x` and `eᵗ α'_x`
respectively, so that the lift `Φ : (t, x) ↦ (t - log h(x), x)` of the identity matches them. It
pulls `d(eᵗ α')` back to `d(eᵗ α)`
(`TauCeti.SmoothForm.mpullback_symplectizationLift_mextDerivₗ_symplectization`) and `eᵗ f` back to
`eᵗ (f / h)`, and its differential carries `X_(eᵗ (f / h))` to `X_(eᵗ f)`
(`TauCeti.SmoothForm.IsContactForm.mfderiv_symplectizationLift_hamiltonianVectorField`).

## Main results

* `TauCeti.mvfderiv_exp_mul_apply`: the differential of `eᵗ f(x)`.
* `TauCeti.SmoothForm.isHamiltonianVectorField_symplectization_iff`: `(R_α f) ∂_t - X` is a
  Hamiltonian vector field of `eᵗ f` exactly when `X` is a contact Hamiltonian vector field of `f`.
* `TauCeti.SmoothForm.IsContactForm.hamiltonianVectorField_symplectization`:
  `X_(r f) = (R_α f) ∂_t - X_f`.
* `TauCeti.SmoothForm.IsContactForm.hamiltonianVectorField_symplectization_exp`: `X_r = -R_α`.
* `TauCeti.SmoothForm.IsContactForm.poissonBracket_symplectization`:
  `{r f, r g}_ω = r (dα(X_f, X_g) + f R_α(g) - g R_α(f))`.
* `TauCeti.SmoothForm.IsContactForm.mfderiv_symplectizationLift_hamiltonianVectorField`: changing
  `α` to `h α` with `h > 0` identifies the Hamiltonian vector fields of `eᵗ (f / h)` and `eᵗ f`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.3 (contact Hamiltonians).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Springer, 1989,
  Appendix 4 (contact structures and their symplectization).
-/

public section

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1} {f g : M → ℝ} {X : (x : M) → TangentSpace I x}

omit [IsManifold I ∞ M] in
/-- The differential of the function `(t, x) ↦ eᵗ f(x)` on `ℝ × M`: it sends a tangent vector
`(s, v)` at `(t, x)` to `eᵗ (s f(x) + df_x(v))`. -/
theorem mvfderiv_exp_mul_apply {p : ℝ × M} (hf : MDifferentiableAt I 𝓘(ℝ) f p.2)
    (v : TangentSpace (𝓘(ℝ).prod I) p) :
    mvfderiv (𝓘(ℝ).prod I) (fun q : ℝ × M ↦ Real.exp q.1 * f q.2) p v =
      Real.exp p.1 *
        (NormedSpace.fromTangentSpace p.1 (Manifold.tangentSpaceProdEquiv p v).1 * f p.2 +
          mvfderiv I f p.2 (Manifold.tangentSpaceProdEquiv p v).2) := by
  have he : MDifferentiableAt (𝓘(ℝ).prod I) 𝓘(ℝ) (fun q : ℝ × M ↦ Real.exp q.1) p :=
    ((Real.contDiff_exp (n := 1)).contMDiff.comp contMDiff_fst p).mdifferentiableAt one_ne_zero
  have hexp : mvfderiv (𝓘(ℝ).prod I) (fun q : ℝ × M ↦ Real.exp q.1) p v =
      NormedSpace.fromTangentSpace p.1 (Manifold.tangentSpaceProdEquiv p v).1 * Real.exp p.1 := by
    rw [Manifold.tangentSpaceProdEquiv_apply]
    exact (Real.hasDerivAt_exp p.1).mvfderiv_comp_fst_apply v
  have hsnd : mvfderiv (𝓘(ℝ).prod I) (fun q : ℝ × M ↦ f q.2) p v =
      mvfderiv I f p.2 (Manifold.tangentSpaceProdEquiv p v).2 := by
    rw [Manifold.tangentSpaceProdEquiv_apply]
    exact mvfderiv_comp_snd_apply f p v
  have hf' : MDifferentiableAt (𝓘(ℝ).prod I) 𝓘(ℝ) (fun q : ℝ × M ↦ f q.2) p :=
    hf.comp p mdifferentiableAt_snd
  rw [mvfderiv_fun_mul he hf', add_apply, smul_apply, smul_apply, hexp, hsnd, smul_eq_mul,
    smul_eq_mul]
  ring

namespace SmoothForm

/-- The defect of the Hamiltonian equation for `eᵗ f` and the vector field `(R_α f) ∂_t - X`,
evaluated on a tangent vector `(s, w)` at `(t, x)`, is `-eᵗ` times
`s (f(x) - α(X)) + (dα(X, w) - (R_α f) α(w) + df(w))`, a combination of the defects of the two
equations defining contact Hamiltonian vector fields. -/
private theorem eval₂_sub_mvfderiv_exp_mul {p : ℝ × M} (hf : MDifferentiableAt I 𝓘(ℝ) f p.2)
    (v : TangentSpace (𝓘(ℝ).prod I) p) :
    (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization).eval₂ p
        ((Manifold.tangentSpaceProdEquiv p).symm
          ((NormedSpace.fromTangentSpace p.1).symm (mvfderiv I f p.2 (α.reebVectorField p.2)),
            -X p.2)) v -
      mvfderiv (𝓘(ℝ).prod I) (fun q : ℝ × M ↦ Real.exp q.1 * f q.2) p v =
      -Real.exp p.1 *
        (NormedSpace.fromTangentSpace p.1 (Manifold.tangentSpaceProdEquiv p v).1 *
            (f p.2 - α.1 p.2 ![X p.2]) +
          (mextDeriv α.1 p.2 ![X p.2, (Manifold.tangentSpaceProdEquiv p v).2] -
            (mvfderiv I f p.2 (α.reebVectorField p.2) *
                α.1 p.2 ![(Manifold.tangentSpaceProdEquiv p v).2] -
              mvfderiv I f p.2 (Manifold.tangentSpaceProdEquiv p v).2))) := by
  -- The form `α` and the two-form `dα` are linear in the slot filled by `-X`.
  have hα : α.1 p.2 ![-X p.2] = -α.1 p.2 ![X p.2] := by
    rw [← degreeOneEquiv_apply_apply_vec, map_neg, degreeOneEquiv_apply_apply_vec]
  have hdα (w : TangentSpace I p.2) :
      (mextDerivₗ I 1 α).eval₂ p.2 (-X p.2) w = -mextDeriv α.1 p.2 ![X p.2, w] := by
    rw [← bilinFormAt_apply, map_neg, LinearMap.neg_apply, bilinFormAt_apply,
      SmoothBundleForm.eval₂_apply, mextDerivₗ_apply]
  rw [eval₂_mextDerivₗ_symplectization, mvfderiv_exp_mul_apply hf]
  simp only [ContinuousLinearEquiv.apply_symm_apply, hα, hdα]
  ring

/-- **Hamiltonian vector fields of homogeneous functions.** For a differentiable function `f` on
`M`, the vector field `(t, x) ↦ (R_α f)(x) ∂_t - X(x)` on the symplectization `ℝ × M` is a
Hamiltonian vector field of `(t, x) ↦ eᵗ f(x)` for `d(eᵗ α)` exactly when `X` is a contact
Hamiltonian vector field of `f` for `α`. In the coordinate `r = eᵗ`, this is
`X_(r f) = r (R_α f) ∂_r - X_f`. No contact condition on `α` is needed. -/
theorem isHamiltonianVectorField_symplectization_iff (hf : MDifferentiable I 𝓘(ℝ) f) :
    SmoothTwoForm.IsHamiltonianVectorField (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization)
        (fun p ↦ Real.exp p.1 * f p.2)
        (fun p ↦ (Manifold.tangentSpaceProdEquiv p).symm
          ((NormedSpace.fromTangentSpace p.1).symm (mvfderiv I f p.2 (α.reebVectorField p.2)),
            -X p.2)) ↔
      α.IsContactHamiltonianVectorField f X := by
  rw [isContactHamiltonianVectorField_iff]
  simp only [SmoothTwoForm.isHamiltonianVectorField_iff, ← sub_eq_zero (b := mvfderiv _ _ _ _),
    eval₂_sub_mvfderiv_exp_mul (hf _), neg_mul, neg_eq_zero, mul_eq_zero,
    (Real.exp_pos _).ne', false_or]
  refine ⟨fun h x ↦ ⟨?_, fun w ↦ ?_⟩, fun h p v ↦ ?_⟩
  · -- Test against the unit vector `∂_t` at `(0, x)`.
    have := h ((0 : ℝ), x) ((Manifold.tangentSpaceProdEquiv ((0 : ℝ), x)).symm
      ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1, 0))
    simp only [ContinuousLinearEquiv.apply_symm_apply, one_mul, map_zero] at this
    have h₀ : mextDeriv α.1 x ![X x, (0 : TangentSpace I x)] = 0 :=
      (mextDeriv α.1 x).map_coord_zero 1 rfl
    have h₁ : α.1 x ![(0 : TangentSpace I x)] = 0 := (α.1 x).map_coord_zero 0 rfl
    rw [h₀, h₁] at this
    linarith
  · -- Test against a vector `(0, w)` at `(0, x)`.
    have := h ((0 : ℝ), x) ((Manifold.tangentSpaceProdEquiv ((0 : ℝ), x)).symm (0, w))
    simp only [ContinuousLinearEquiv.apply_symm_apply, map_zero, zero_mul, zero_add] at this
    linarith
  · rw [(h p.2).1, sub_self, mul_zero, zero_add, (h p.2).2, sub_self]

/-- A contact Hamiltonian vector field `X` of a differentiable function `f` lifts to the
Hamiltonian vector field `(R_α f) ∂_t - X` of `(t, x) ↦ eᵗ f(x)` on the symplectization. -/
theorem IsContactHamiltonianVectorField.isHamiltonianVectorField_symplectization
    (hX : α.IsContactHamiltonianVectorField f X) (hf : MDifferentiable I 𝓘(ℝ) f) :
    SmoothTwoForm.IsHamiltonianVectorField (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization)
        (fun p ↦ Real.exp p.1 * f p.2)
        (fun p ↦ (Manifold.tangentSpaceProdEquiv p).symm
          ((NormedSpace.fromTangentSpace p.1).symm (mvfderiv I f p.2 (α.reebVectorField p.2)),
            -X p.2)) :=
  (isHamiltonianVectorField_symplectization_iff hf).2 hX

namespace IsContactForm

variable [FiniteDimensional ℝ E] (hα : α.IsContactForm)
include hα

/-- **The Hamiltonian vector field of a homogeneous function** on the symplectization of a contact
form: `X_(eᵗ f) = (R_α f) ∂_t - X_f` for a differentiable function `f` on `M`, where `X_f` is the
contact Hamiltonian vector field of `f`. In the coordinate `r = eᵗ`, this is
`X_(r f) = r (R_α f) ∂_r - X_f`. -/
theorem hamiltonianVectorField_symplectization (hf : MDifferentiable I 𝓘(ℝ) f) :
    SmoothTwoForm.hamiltonianVectorField (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization)
        (fun p ↦ Real.exp p.1 * f p.2) =
      fun p ↦ (Manifold.tangentSpaceProdEquiv p).symm
        ((NormedSpace.fromTangentSpace p.1).symm (mvfderiv I f p.2 (α.reebVectorField p.2)),
          -α.contactHamiltonianVectorField f p.2) :=
  ((hα.isSymplectic_mextDerivₗ_symplectization.isNondegenerate.isHamiltonianVectorField_iff_eq).1
    ((hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f
      ).isHamiltonianVectorField_symplectization hf)).symm

/-- The `∂_t`-component of the Hamiltonian vector field of `eᵗ f` on the symplectization of a
contact form is `R_α f`. -/
theorem fromTangentSpace_hamiltonianVectorField_symplectization_fst
    (hf : MDifferentiable I 𝓘(ℝ) f) (p : ℝ × M) :
    NormedSpace.fromTangentSpace p.1 (Manifold.tangentSpaceProdEquiv p
      (SmoothTwoForm.hamiltonianVectorField (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization)
        (fun p ↦ Real.exp p.1 * f p.2) p)).1 = mvfderiv I f p.2 (α.reebVectorField p.2) := by
  rw [hα.hamiltonianVectorField_symplectization hf, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The `M`-component of the Hamiltonian vector field of `eᵗ f` on the symplectization of a
contact form is `-X_f`: the projection to `M` sends `X_(eᵗ f)` to minus the contact Hamiltonian
vector field of `f`. -/
theorem hamiltonianVectorField_symplectization_snd (hf : MDifferentiable I 𝓘(ℝ) f)
    (p : ℝ × M) :
    (Manifold.tangentSpaceProdEquiv p
      (SmoothTwoForm.hamiltonianVectorField (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization)
        (fun p ↦ Real.exp p.1 * f p.2) p)).2 = -α.contactHamiltonianVectorField f p.2 := by
  rw [hα.hamiltonianVectorField_symplectization hf, ContinuousLinearEquiv.apply_symm_apply]

/-- **The Hamiltonian vector field of the fibre coordinate** `r = eᵗ` on the symplectization of a
contact form is minus the Reeb vector field: `X_r = -R_α`, with no `∂_t`-component. -/
theorem hamiltonianVectorField_symplectization_exp :
    SmoothTwoForm.hamiltonianVectorField (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization)
        (fun p : ℝ × M ↦ Real.exp p.1) =
      fun p ↦ (Manifold.tangentSpaceProdEquiv p).symm (0, -α.reebVectorField p.2) := by
  have h := hα.hamiltonianVectorField_symplectization (f := fun _ ↦ (1 : ℝ)) mdifferentiable_const
  simp only [mul_one, mvfderiv_const, zero_apply, map_zero,
    hα.contactHamiltonianVectorField_const, one_smul] at h
  exact h

/-- **The Poisson bracket of homogeneous functions** on the symplectization of a contact form:
for differentiable functions `f` and `g` on `M`,

`{eᵗ f, eᵗ g}_ω = eᵗ (dα(X_f, X_g) + f R_α(g) - g R_α(f))`,

where `X_f` and `X_g` are contact Hamiltonian vector fields. The factor `dα(X_f, X_g) +
f R_α(g) - g R_α(f)` is the Jacobi bracket `{f, g}_α` of the contact form, so in the coordinate
`r = eᵗ` this reads `{r f, r g}_ω = r {f, g}_α`. -/
theorem poissonBracket_symplectization (hf : MDifferentiable I 𝓘(ℝ) f)
    (hg : MDifferentiable I 𝓘(ℝ) g) (p : ℝ × M) :
    SmoothTwoForm.poissonBracket (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization)
        (fun p ↦ Real.exp p.1 * f p.2) (fun p ↦ Real.exp p.1 * g p.2) p =
      Real.exp p.1 *
        (mextDeriv α.1 p.2
            ![α.contactHamiltonianVectorField f p.2, α.contactHamiltonianVectorField g p.2] +
          f p.2 * mvfderiv I g p.2 (α.reebVectorField p.2) -
          g p.2 * mvfderiv I f p.2 (α.reebVectorField p.2)) := by
  have hdα : (mextDerivₗ I 1 α).eval₂ p.2 (-α.contactHamiltonianVectorField f p.2)
      (-α.contactHamiltonianVectorField g p.2) =
        mextDeriv α.1 p.2
          ![α.contactHamiltonianVectorField f p.2, α.contactHamiltonianVectorField g p.2] := by
    rw [← bilinFormAt_apply]
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
    rw [bilinFormAt_apply, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply]
  have hneg (k : M → ℝ) : α.1 p.2 ![-α.contactHamiltonianVectorField k p.2] = -k p.2 := by
    rw [← degreeOneEquiv_apply_apply_vec, map_neg, degreeOneEquiv_apply_apply_vec,
      hα.apply_contactHamiltonianVectorField]
  rw [SmoothTwoForm.poissonBracket_def, hα.hamiltonianVectorField_symplectization hf,
    hα.hamiltonianVectorField_symplectization hg, eval₂_mextDerivₗ_symplectization]
  simp only [ContinuousLinearEquiv.apply_symm_apply, hneg, hdα]
  ring

/-- **The primitive recovers a homogeneous Hamiltonian.** On the symplectization of a contact form,
the symplectization form `eᵗ α` takes the value `-eᵗ f` on the Hamiltonian vector field of
`eᵗ f`, so the primitive `λ = -eᵗ α` of `ω = -dλ` satisfies `λ(X_(r f)) = r f`. -/
theorem symplectization_apply_hamiltonianVectorField (hf : MDifferentiable I 𝓘(ℝ) f)
    (p : ℝ × M) :
    α.symplectization.1 p
        ![SmoothTwoForm.hamiltonianVectorField (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization)
          (fun p ↦ Real.exp p.1 * f p.2) p] =
      -(Real.exp p.1 * f p.2) := by
  rw [symplectization_apply, hα.hamiltonianVectorField_symplectization_snd hf,
    ← degreeOneEquiv_apply_apply_vec, map_neg, degreeOneEquiv_apply_apply_vec,
    hα.apply_contactHamiltonianVectorField, mul_neg]

end IsContactForm

/-! ### Changing the contact form -/

section ChangeOfForm

variable {α' : SmoothForm I M ℝ 1} {h : M → ℝ}

omit [IsManifold I ∞ M] in
/-- The lift `(t, x) ↦ (t - log h(x), x)` of the identity has surjective differential, since the
lift along `h⁻¹` is a smooth right inverse. -/
private theorem surjective_mfderiv_symplectizationLift_id (hh : ContMDiff I 𝓘(ℝ) ∞ h)
    (hh₀ : ∀ x, h x ≠ 0) (p : ℝ × M) :
    Function.Surjective
      (mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (symplectizationLift id h) p) := by
  have hΦ := contMDiff_symplectizationLift contMDiff_id hh hh₀
  have hΨ := contMDiff_symplectizationLift contMDiff_id (hh.inv₀ hh₀) fun x ↦ inv_ne_zero (hh₀ x)
  have hcomp : symplectizationLift id h ∘ symplectizationLift id (fun x ↦ (h x)⁻¹) = id :=
    funext fun q ↦ by simp [Real.log_inv]
  -- The differential is surjective at every point `Ψ q` of the image of the right inverse `Ψ`.
  have key (q : ℝ × M) : Function.Surjective (mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I)
      (symplectizationLift id h) (symplectizationLift id (fun x ↦ (h x)⁻¹) q)) := by
    have hd := mfderiv_comp q ((hΦ _).mdifferentiableAt (by simp))
      ((hΨ q).mdifferentiableAt (by simp))
    rw [hcomp, mfderiv_id] at hd
    exact fun w ↦ ⟨_, (congrArg (· w) hd).symm⟩
  have hΨΦ : symplectizationLift id (fun x ↦ (h x)⁻¹) (symplectizationLift id h p) = p := by
    simp [Real.log_inv]
  exact hΨΦ ▸ key (symplectizationLift id h p)

/-- **The homogeneous Hamiltonian correspondence does not depend on the contact form.** Let
`α' = h α` for a smooth positive function `h`, with `α` a contact form. The lift
`Φ : (t, x) ↦ (t - log h(x), x)` of the identity identifies the two symplectizations: both
parametrize the positive half of the annihilator line of `ker α`, since
`eᵗ α_x = e^(t - log h(x)) α'_x`, and `Φ` pulls `d(eᵗ α')` back to `d(eᵗ α)`. It pulls the
homogeneous function `eᵗ f` back to `eᵗ (f / h)`, and its differential carries the Hamiltonian
vector field of `eᵗ (f / h)` for `d(eᵗ α)` to the Hamiltonian vector field of `eᵗ f` for
`d(eᵗ α')`. -/
theorem IsContactForm.mfderiv_symplectizationLift_hamiltonianVectorField [FiniteDimensional ℝ E]
    (hα : α.IsContactForm) (hh : ContMDiff I 𝓘(ℝ) ∞ h) (hh₀ : ∀ x, 0 < h x)
    (hα' : ∀ x, α'.1 x = h x • α.1 x) (hf : MDifferentiable I 𝓘(ℝ) f) (p : ℝ × M) :
    mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (symplectizationLift id h) p
        (SmoothTwoForm.hamiltonianVectorField (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization)
          (fun q ↦ Real.exp q.1 * (f q.2 / h q.2)) p) =
      SmoothTwoForm.hamiltonianVectorField (mextDerivₗ (𝓘(ℝ).prod I) 1 α'.symplectization)
        (fun q ↦ Real.exp q.1 * f q.2) (symplectizationLift id h p) := by
  have hα'c : α'.IsContactForm :=
    (isContactForm_iff_of_eq_smul (hh.of_le (by simp)) (fun x ↦ (hh₀ x).ne') hα').2 hα
  have hcomp : (fun q : ℝ × M ↦ Real.exp q.1 * f q.2) ∘ symplectizationLift id h =
      fun q ↦ Real.exp q.1 * (f q.2 / h q.2) := by
    funext q
    simp only [Function.comp_apply, symplectizationLift_apply, id_eq, Real.exp_sub,
      Real.exp_log (hh₀ q.2)]
    ring
  have hg : MDifferentiableAt (𝓘(ℝ).prod I) 𝓘(ℝ) (fun q : ℝ × M ↦ Real.exp q.1 * f q.2)
      (symplectizationLift id h p) :=
    (((Real.contDiff_exp (n := 1)).contMDiff.comp contMDiff_fst _).mdifferentiableAt
      one_ne_zero).mul ((hf _).comp _ mdifferentiableAt_snd)
  rw [← hcomp]
  exact (hα.isSymplectic_mextDerivₗ_symplectization.isNondegenerate
    ).mfderiv_hamiltonianVectorField_comp
      hα'c.isSymplectic_mextDerivₗ_symplectization.isNondegenerate _
    (mpullback_symplectizationLift_mextDerivₗ_symplectization contMDiff_id hh hh₀
      fun x ↦ by simpa using hα' x)
    (surjective_mfderiv_symplectizationLift_id hh (fun x ↦ (hh₀ x).ne') p) hg

end ChangeOfForm

end SmoothForm

end TauCeti
