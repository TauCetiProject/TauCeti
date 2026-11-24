/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ModelSpace
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Prod
public import TauCeti.Geometry.Symplectic.Hamiltonian.ExtendedPhaseSpace.Manifold

/-!
# The extended phase space as the cotangent bundle of `Q × ℝ`

Let `Q` be a configuration manifold. The phase space of time-dependent mechanics on `Q` is the
cotangent bundle `T*(Q × ℝ)` of the extended configuration space, with its canonical symplectic
form `ω = -dλ`. A covector `z` at `(q, t)` has a component `z|_Q` along `Q` and the momentum
`p_t = z(0, ∂_t)` conjugate to the time. This file identifies it with the model
`T*Q × T*ℝ = T*Q × (ℝ × ℝ)` of
`TauCeti.Geometry.Symplectic.Hamiltonian.ExtendedPhaseSpace.Manifold`, whose last two coordinates
are the time `t` and its conjugate momentum `e`, with the form `ω_Q ⊕ (dt ∧ de)`
(`TauCeti.SmoothTwoForm.extended`).

The diffeomorphism

`Ψ : T*(Q × ℝ) ≃ T*Q × (ℝ × ℝ)`, `z ↦ (z|_Q, t, p_t)`

(`TauCeti.CotangentBundle.prodRealDiffeomorph`) is the splitting
`T*(Q × ℝ) ≃ T*Q × T*ℝ` of `TauCeti.CotangentBundle.prodDiffeomorph` followed by the global
coordinates `T*ℝ ≃ ℝ × ℝ`, `(t, p) ↦ (t, p 1)` (`TauCeti.CotangentBundle.lineDiffeomorph`). It is
a symplectomorphism: it pulls `ω_Q ⊕ (dt ∧ de)` back to the canonical symplectic form of
`T*(Q × ℝ)` (`TauCeti.CotangentBundle.mpullback_prodRealDiffeomorph_extended`). So no sign or
normalisation changes between the coordinate model and the intrinsic phase space.

Under `Ψ`, the extended Hamiltonian `K(x, t, e) = e + H(t, x)` of a time-dependent Hamiltonian
`H : ℝ → T*Q → ℝ` (`TauCeti.extendedHamiltonian`) becomes the function

`p_t + H(t, q, p)`

on `T*(Q × ℝ)` (`TauCeti.CotangentBundle.extendedHamiltonian_prodRealDiffeomorph`). Hence:

* the Hamiltonian vector field of `p_t + H` is carried by `Ψ` to `(X_{H_t}, 1, -∂_t H)`
  (`TauCeti.CotangentBundle.mfderiv_prodRealDiffeomorph_hamiltonianVectorField`): these are the
  nonautonomous Hamilton equations, in which the time advances at unit speed and `p_t` absorbs the
  change of energy;
* a time-dependent function `F(t, q, p)` on `T*Q`, read on `T*(Q × ℝ)`, has Poisson bracket
  `∂_t F + {F_t, H_t}` with `p_t + H`
  (`TauCeti.CotangentBundle.poissonBracket_extendedHamiltonian_prodRealDiffeomorph`), the
  quantity whose vanishing characterises the conserved quantities of the time-dependent flow
  (`TauCeti.SmoothTwoForm.IsNondegenerate.forall_apply_timeDependentFlowOf_eq_iff`);
* every solution `γ` of the nonautonomous equation `γ' = X_{H_u}(γ)` on `T*Q` lifts, for every
  constant `c`, to the integral curve `u ↦ Ψ⁻¹(γ u, u, c - H(u, γ u))` of the Hamiltonian vector
  field of `p_t + H` (`TauCeti.CotangentBundle.isMIntegralCurve_prodRealDiffeomorph_symm`).

The base `Q` may have boundary or corners and be infinite-dimensional for the identification of
the forms; the statements about Hamiltonian dynamics need its model space to be
finite-dimensional.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 45.
* J. E. Marsden and T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in
  Applied Mathematics 17, Springer, 1999, Section 8.1.
-/

public section

noncomputable section

open Bundle Function
open scoped Manifold ContDiff

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q]
  [IsManifold I ∞ Q]

variable (I Q) in
/-- **The extended phase space.** The smooth diffeomorphism `T*(Q × ℝ) ≃ T*Q × (ℝ × ℝ)` sending a
covector `z` at `(q, t)` to its restriction `z|_Q` to `Q`, the time `t` and the momentum
`p_t = z(0, 1)` conjugate to the time. -/
def prodRealDiffeomorph :
    CotangentBundle (I.prod 𝓘(ℝ)) (Q × ℝ) ≃ₘ⟮(I.prod 𝓘(ℝ)).prod 𝓘(ℝ, E × ℝ →L[ℝ] ℝ),
      (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ, ℝ × ℝ)⟯ CotangentBundle I Q × (ℝ × ℝ) where
  -- `Diffeomorph.prodCongr` needs equal model vector spaces on the two sides of each factor,
  -- which `lineDiffeomorph` does not have, so the product map is assembled directly.
  toEquiv := (prodDiffeomorph I 𝓘(ℝ) Q ℝ).toEquiv.trans
    ((Equiv.refl _).prodCongr (lineDiffeomorph ℝ).toEquiv)
  contMDiff_toFun := (contMDiff_id.prodMap (lineDiffeomorph ℝ).contMDiff).comp
    (prodDiffeomorph I 𝓘(ℝ) Q ℝ).contMDiff
  contMDiff_invFun := (prodDiffeomorph I 𝓘(ℝ) Q ℝ).symm.contMDiff.comp
    (contMDiff_id.prodMap (lineDiffeomorph ℝ).symm.contMDiff)

/-- `prodRealDiffeomorph` is the splitting `T*(Q × ℝ) ≃ T*Q × T*ℝ` followed by the global
coordinates of `T*ℝ`. -/
theorem coe_prodRealDiffeomorph :
    ⇑(prodRealDiffeomorph I Q) = Prod.map id (lineDiffeomorph ℝ) ∘ prodDiffeomorph I 𝓘(ℝ) Q ℝ :=
  (rfl)

/-- `prodRealDiffeomorph` keeps the `T*Q` component of the splitting `T*(Q × ℝ) ≃ T*Q × T*ℝ` and
reads its `T*ℝ` component in the global coordinates of `T*ℝ`. -/
theorem prodRealDiffeomorph_apply (z : CotangentBundle (I.prod 𝓘(ℝ)) (Q × ℝ)) :
    prodRealDiffeomorph I Q z =
      ((prodDiffeomorph I 𝓘(ℝ) Q ℝ z).1, lineDiffeomorph ℝ (prodDiffeomorph I 𝓘(ℝ) Q ℝ z).2) :=
  (rfl)

/-- The component of `prodRealDiffeomorph z` in `T*Q` is the restriction of `z` to `Q`. -/
@[simp]
theorem prodRealDiffeomorph_fst (z : CotangentBundle (I.prod 𝓘(ℝ)) (Q × ℝ)) :
    (prodRealDiffeomorph I Q z).1 = (prodDiffeomorph I 𝓘(ℝ) Q ℝ z).1 := by
  rw [prodRealDiffeomorph_apply]

/-- The time coordinate of `prodRealDiffeomorph z` is the time of the base point of `z`. -/
@[simp]
theorem prodRealDiffeomorph_snd_fst (z : CotangentBundle (I.prod 𝓘(ℝ)) (Q × ℝ)) :
    (prodRealDiffeomorph I Q z).2.1 = z.proj.2 := by
  rw [prodRealDiffeomorph_apply, lineDiffeomorph_apply, proj_prodDiffeomorph_snd]

/-- The momentum coordinate of `prodRealDiffeomorph z` is the value `p_t = z(0, 1)` of `z` on the
unit time vector. -/
@[simp]
theorem prodRealDiffeomorph_snd_snd (z : CotangentBundle (I.prod 𝓘(ℝ)) (Q × ℝ)) :
    (prodRealDiffeomorph I Q z).2.2 = z.snd ((0, 1) : E × ℝ) := by
  -- The vertical slice inclusion `t ↦ (q, t)` sends the unit vector to `(0, 1)`.
  have h : mfderiv 𝓘(ℝ) (I.prod 𝓘(ℝ)) (fun t : ℝ ↦ (z.proj.1, t)) z.proj.2 (1 : ℝ) =
      ((0, 1) : E × ℝ) := by
    rw [mfderiv_prod_right]
    exact ContinuousLinearMap.inr_apply (R := ℝ) (M₁ := E) (M₂ := ℝ) 1
  rw [prodRealDiffeomorph_apply, lineDiffeomorph_apply]
  exact (prodDiffeomorph_snd_snd_apply z (1 : ℝ)).trans (congrArg z.snd h)

/-- The time and the `T*Q` component of `prodRealDiffeomorph z`, the arguments at which a
time-dependent function on `T*Q` is evaluated, are the time of `z` and its restriction to `Q`. -/
private theorem mk_prodRealDiffeomorph_snd_fst_fst (z : CotangentBundle (I.prod 𝓘(ℝ)) (Q × ℝ)) :
    ((prodRealDiffeomorph I Q z).2.1, (prodRealDiffeomorph I Q z).1) =
      (z.proj.2, (prodDiffeomorph I 𝓘(ℝ) Q ℝ z).1) := by
  rw [prodRealDiffeomorph_snd_fst, prodRealDiffeomorph_fst]

/-- A time-dependent function `F` on `T*Q`, read on the model `T*Q × (ℝ × ℝ)` and composed with
`prodRealDiffeomorph`, is `z ↦ F(t, z|_Q)` on `T*(Q × ℝ)`. -/
private theorem comp_prodRealDiffeomorph (F : ℝ → CotangentBundle I Q → ℝ) :
    (fun y : CotangentBundle I Q × (ℝ × ℝ) ↦ F y.2.1 y.1) ∘ prodRealDiffeomorph I Q =
      fun z ↦ F z.proj.2 (prodDiffeomorph I 𝓘(ℝ) Q ℝ z).1 :=
  funext fun z ↦ by rw [comp_apply, prodRealDiffeomorph_snd_fst, prodRealDiffeomorph_fst]

/-- The inverse of `prodRealDiffeomorph` reads the time coordinates `(t, e)` as the covector
`v ↦ v e` at `t` and combines it with the covector on `Q` by the inverse of the splitting
`T*(Q × ℝ) ≃ T*Q × T*ℝ`. -/
theorem prodRealDiffeomorph_symm_apply (w : CotangentBundle I Q × (ℝ × ℝ)) :
    (prodRealDiffeomorph I Q).symm w =
      (prodDiffeomorph I 𝓘(ℝ) Q ℝ).symm (w.1, (lineDiffeomorph ℝ).symm w.2) :=
  (rfl)

/-- The inverse of `prodRealDiffeomorph` lies over the base point of the covector on `Q` and the
time coordinate. -/
@[simp]
theorem proj_prodRealDiffeomorph_symm (w : CotangentBundle I Q × (ℝ × ℝ)) :
    ((prodRealDiffeomorph I Q).symm w).proj = (w.1.proj, w.2.1) := by
  rw [prodRealDiffeomorph_symm_apply, proj_prodDiffeomorph_symm, lineDiffeomorph_symm_apply]

/-- The inverse of `prodRealDiffeomorph` combines a covector `a` on `Q` and the momentum `e`
conjugate to the time into the covector `(δq, δt) ↦ a δq + δt e` on `Q × ℝ`. -/
@[simp]
theorem prodRealDiffeomorph_symm_snd_apply (w : CotangentBundle I Q × (ℝ × ℝ))
    (v : TangentSpace (I.prod 𝓘(ℝ)) ((prodRealDiffeomorph I Q).symm w).proj) :
    ((prodRealDiffeomorph I Q).symm w).snd v = w.1.snd v.1 + v.2 * w.2.2 := by
  refine (prodDiffeomorph_symm_snd_apply (w.1, (lineDiffeomorph ℝ).symm w.2) v).trans ?_
  rw [mfderiv_fst, mfderiv_snd, lineDiffeomorph_symm_apply]
  exact congrArg (w.1.snd v.1 + ·) (smul_eq_mul v.2 w.2.2)

/-- **The extended phase space is the cotangent bundle of `Q × ℝ`.** The diffeomorphism
`T*(Q × ℝ) ≃ T*Q × (ℝ × ℝ)` pulls the form `ω_Q ⊕ (dt ∧ de)` of the extended phase space back to
the canonical symplectic form of `T*(Q × ℝ)`. -/
@[simp]
theorem mpullback_prodRealDiffeomorph_extended :
    SmoothForm.mpullback (prodRealDiffeomorph I Q) (prodRealDiffeomorph I Q).contMDiff
        (symplecticForm I Q).extended =
      symplecticForm (I.prod 𝓘(ℝ)) (Q × ℝ) := by
  have hprod : SmoothForm.mpullback (Prod.map id (lineDiffeomorph ℝ))
      (contMDiff_id.prodMap (lineDiffeomorph ℝ).contMDiff) (symplecticForm I Q).extended =
      SmoothTwoForm.prod (symplecticForm I Q) (symplecticForm 𝓘(ℝ) ℝ) := by
    rw [SmoothTwoForm.extended_def,
      SmoothTwoForm.mpullback_prodMap_prod contMDiff_id (lineDiffeomorph ℝ).contMDiff,
      SmoothForm.mpullback_id,
      LinearMap.id_apply, mpullback_lineDiffeomorph_constSmooth]
  -- Pull back in two steps: through the global coordinates of `T*ℝ`, then through the splitting.
  rw [← mpullback_prodDiffeomorph_symplecticForm, ← hprod, SmoothForm.mpullback_mpullback]
  simp only [coe_prodRealDiffeomorph]

/-- **The extended Hamiltonian on the cotangent bundle of `Q × ℝ`.** Read on `T*(Q × ℝ)`, the
extended Hamiltonian `K(x, t, e) = e + H(t, x)` of a time-dependent Hamiltonian `H` on `T*Q` is
`p_t + H(t, z|_Q)`. -/
theorem extendedHamiltonian_prodRealDiffeomorph (H : ℝ → CotangentBundle I Q → ℝ)
    (z : CotangentBundle (I.prod 𝓘(ℝ)) (Q × ℝ)) :
    extendedHamiltonian H (prodRealDiffeomorph I Q z) =
      z.snd ((0, 1) : E × ℝ) + H z.proj.2 (prodDiffeomorph I 𝓘(ℝ) Q ℝ z).1 := by
  rw [extendedHamiltonian_apply, prodRealDiffeomorph_snd_snd, prodRealDiffeomorph_snd_fst,
    prodRealDiffeomorph_fst]

/-- The differential of `prodRealDiffeomorph` is surjective at every covector. -/
private theorem surjective_mfderiv_prodRealDiffeomorph
    (z : CotangentBundle (I.prod 𝓘(ℝ)) (Q × ℝ)) :
    Surjective (mfderiv ((I.prod 𝓘(ℝ)).prod 𝓘(ℝ, E × ℝ →L[ℝ] ℝ))
      ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ, ℝ × ℝ)) (prodRealDiffeomorph I Q) z) :=
  ((prodRealDiffeomorph I Q).isInvertible_mfderiv (by simp)).surjective

variable [FiniteDimensional ℝ E]

/-- **Hamilton's equations on the extended phase space.** Where the time-dependent Hamiltonian `H`
on `T*Q` is differentiable, `prodRealDiffeomorph` carries the Hamiltonian vector field of
`p_t + H(t, z|_Q)` on `T*(Q × ℝ)` to `(X_{H_t}, 1, -∂_t H)`: the restriction to `Q` moves by the
Hamiltonian vector field of `H_t`, the time advances at unit speed, and the momentum `p_t`
conjugate to the time changes at the rate `-∂_t H`. -/
theorem mfderiv_prodRealDiffeomorph_hamiltonianVectorField {H : ℝ → CotangentBundle I Q → ℝ}
    {z : CotangentBundle (I.prod 𝓘(ℝ)) (Q × ℝ)}
    (hH : MDifferentiableAt (𝓘(ℝ).prod (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))) 𝓘(ℝ) (uncurry H)
      (z.proj.2, (prodDiffeomorph I 𝓘(ℝ) Q ℝ z).1)) :
    mfderiv ((I.prod 𝓘(ℝ)).prod 𝓘(ℝ, E × ℝ →L[ℝ] ℝ)) ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ, ℝ × ℝ))
        (prodRealDiffeomorph I Q) z
        ((symplecticForm (I.prod 𝓘(ℝ)) (Q × ℝ)).hamiltonianVectorField
          (extendedHamiltonian H ∘ prodRealDiffeomorph I Q) z) =
      extendedVectorField H (fun t ↦ (symplecticForm I Q).hamiltonianVectorField (H t))
        (prodRealDiffeomorph I Q z) := by
  have hσ := (isSymplectic_symplecticForm (I := I) (M := Q)).isNondegenerate
  have hH' : MDifferentiableAt (𝓘(ℝ).prod (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))) 𝓘(ℝ) (uncurry H)
      ((prodRealDiffeomorph I Q z).2.1, (prodRealDiffeomorph I Q z).1) := by
    rwa [mk_prodRealDiffeomorph_snd_fst_fst]
  rw [(isSymplectic_symplecticForm (I := I.prod 𝓘(ℝ)) (M := Q × ℝ)).isNondegenerate
    |>.mfderiv_hamiltonianVectorField_comp hσ.extended (prodRealDiffeomorph I Q).contMDiff
      mpullback_prodRealDiffeomorph_extended (surjective_mfderiv_prodRealDiffeomorph z)
      (mdifferentiableAt_extendedHamiltonian hH'),
    hσ.hamiltonianVectorField_extendedHamiltonian hH']

/-- **Time-dependent functions on the extended phase space.** A time-dependent function `F` on
`T*Q`, read on `T*(Q × ℝ)` as `z ↦ F(t, z|_Q)`, has Poisson bracket `∂_t F + {F_t, H_t}` with the
Hamiltonian `p_t + H(t, z|_Q)`, where `F` and `H` are differentiable. -/
theorem poissonBracket_extendedHamiltonian_prodRealDiffeomorph
    {F H : ℝ → CotangentBundle I Q → ℝ} {z : CotangentBundle (I.prod 𝓘(ℝ)) (Q × ℝ)}
    (hF : MDifferentiableAt (𝓘(ℝ).prod (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))) 𝓘(ℝ) (uncurry F)
      (z.proj.2, (prodDiffeomorph I 𝓘(ℝ) Q ℝ z).1))
    (hH : MDifferentiableAt (𝓘(ℝ).prod (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))) 𝓘(ℝ) (uncurry H)
      (z.proj.2, (prodDiffeomorph I 𝓘(ℝ) Q ℝ z).1)) :
    (symplecticForm (I.prod 𝓘(ℝ)) (Q × ℝ)).poissonBracket
        (fun w ↦ F w.proj.2 (prodDiffeomorph I 𝓘(ℝ) Q ℝ w).1)
        (extendedHamiltonian H ∘ prodRealDiffeomorph I Q) z =
      deriv (fun s ↦ F s (prodDiffeomorph I 𝓘(ℝ) Q ℝ z).1) z.proj.2 +
        (symplecticForm I Q).poissonBracket (F z.proj.2) (H z.proj.2)
          (prodDiffeomorph I 𝓘(ℝ) Q ℝ z).1 := by
  have hσ := (isSymplectic_symplecticForm (I := I) (M := Q)).isNondegenerate
  -- Both functions are read on the model `T*Q × (ℝ × ℝ)` and composed with
  -- `prodRealDiffeomorph`, at whose image `F` and `H` are differentiable.
  have hpt := mk_prodRealDiffeomorph_snd_fst_fst (I := I) z
  have hpair : MDifferentiableAt ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ, ℝ × ℝ))
      (𝓘(ℝ).prod (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)))
      (fun y : CotangentBundle I Q × (ℝ × ℝ) ↦ (y.2.1, y.1)) (prodRealDiffeomorph I Q z) :=
    (differentiableAt_fst.mdifferentiableAt.comp _ mdifferentiableAt_snd).prodMk
      mdifferentiableAt_fst
  have hF₀ : MDifferentiableAt (𝓘(ℝ).prod (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))) 𝓘(ℝ) (uncurry F)
      ((prodRealDiffeomorph I Q z).2.1, (prodRealDiffeomorph I Q z).1) := hpt ▸ hF
  have hH' : MDifferentiableAt (𝓘(ℝ).prod (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))) 𝓘(ℝ) (uncurry H)
      ((prodRealDiffeomorph I Q z).2.1, (prodRealDiffeomorph I Q z).1) := hpt ▸ hH
  have hF' : MDifferentiableAt ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ)
      (fun y : CotangentBundle I Q × (ℝ × ℝ) ↦ F y.2.1 y.1) (prodRealDiffeomorph I Q z) :=
    hF₀.comp (f := fun y : CotangentBundle I Q × (ℝ × ℝ) ↦ (y.2.1, y.1)) _ hpair
  rw [← comp_prodRealDiffeomorph]
  refine ((isSymplectic_symplecticForm (I := I.prod 𝓘(ℝ)) (M := Q × ℝ)).isNondegenerate
    |>.poissonBracket_comp hσ.extended (prodRealDiffeomorph I Q).contMDiff
      mpullback_prodRealDiffeomorph_extended (surjective_mfderiv_prodRealDiffeomorph z) hF'
      (mdifferentiableAt_extendedHamiltonian hH')).trans ?_
  rw [hσ.poissonBracket_extendedHamiltonian hF₀ hH', prodRealDiffeomorph_snd_fst,
    prodRealDiffeomorph_fst]

/-- **Solutions of the nonautonomous Hamilton equations on the extended phase space.** Let `γ`
solve `γ' = X_{H_u}(γ)` on `T*Q`, for a jointly differentiable time-dependent Hamiltonian `H`.
Then, for every constant `c`, the curve of covectors on `Q × ℝ` with restriction `γ u` to `Q`,
time `u` and conjugate momentum `p_t = c - H(u, γ u)` is an integral curve of the Hamiltonian
vector field of `p_t + H` on `T*(Q × ℝ)`. -/
theorem isMIntegralCurve_prodRealDiffeomorph_symm {H : ℝ → CotangentBundle I Q → ℝ}
    {γ : ℝ → CotangentBundle I Q}
    (hH : MDifferentiable (𝓘(ℝ).prod (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))) 𝓘(ℝ) (uncurry H))
    (hγ : ∀ u, HasMFDerivAt 𝓘(ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) γ u
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((symplecticForm I Q).hamiltonianVectorField (H u) (γ u))))
    (c : ℝ) :
    IsMIntegralCurve (fun u ↦ (prodRealDiffeomorph I Q).symm (γ u, (u, c - H u (γ u))))
      ((symplecticForm (I.prod 𝓘(ℝ)) (Q × ℝ)).hamiltonianVectorField
        (extendedHamiltonian H ∘ prodRealDiffeomorph I Q)) := by
  have hσ := (isSymplectic_symplecticForm (I := I) (M := Q)).isNondegenerate
  set Ψ := prodRealDiffeomorph I Q
  -- On the model `T*Q × (ℝ × ℝ)`, the lifted curve is an integral curve of `X_K`.
  have hX : (symplecticForm I Q).extended.hamiltonianVectorField (extendedHamiltonian H) =
      extendedVectorField H fun u ↦ (symplecticForm I Q).hamiltonianVectorField (H u) :=
    funext fun _ ↦ hσ.hamiltonianVectorField_extendedHamiltonian (hH _)
  have hK : (extendedHamiltonian H ∘ Ψ) ∘ Ψ.symm = extendedHamiltonian H :=
    funext fun p ↦ congrArg (extendedHamiltonian H) (Ψ.apply_symm_apply p)
  have hmodel := SmoothTwoForm.IsHamiltonianVectorField.isMIntegralCurve_extended
    (fun u ↦ hσ.isHamiltonianVectorField_hamiltonianVectorField (H u)) hH hγ c
  rw [← hX, ← hK] at hmodel
  have hg : ∀ p, MDifferentiableAt ((I.prod 𝓘(ℝ)).prod 𝓘(ℝ, E × ℝ →L[ℝ] ℝ)) 𝓘(ℝ)
      (extendedHamiltonian H ∘ Ψ) (Ψ.symm p) := fun p ↦
    MDifferentiableAt.comp (f := Ψ) (Ψ.symm p)
      (by rw [Ψ.apply_symm_apply]; exact mdifferentiableAt_extendedHamiltonian (hH _))
      (Ψ.mdifferentiable (by simp) _)
  -- Transport it along `Ψ⁻¹`, which pulls the canonical form of `T*(Q × ℝ)` back to the model.
  exact hσ.extended.isMIntegralCurve_comp_hamiltonianVectorField
    (isSymplectic_symplecticForm (I := I.prod 𝓘(ℝ)) (M := Q × ℝ)).isNondegenerate
    Ψ.symm.contMDiff
    (SmoothForm.mpullback_symm_eq_of_mpullback_eq mpullback_prodRealDiffeomorph_extended)
    (fun _ ↦ (Ψ.symm.isInvertible_mfderiv (by simp)).surjective)
    (fun _ ↦ hg _) hmodel

end TauCeti.CotangentBundle
