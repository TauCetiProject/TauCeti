/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Symplectic.Hamiltonian.ExtendedPhaseSpace
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The extended phase space of a time-dependent Hamiltonian on a manifold

Let `(M, σ)` be a manifold with a two-form, symplectic in the main results, and let
`H : ℝ → M → ℝ` be a time-dependent Hamiltonian, with the conventions `ι_{X_f} σ = df` and
`{f, g} = σ(X_f, X_g) = df(X_g)`. The **extended phase space** of `M` is `M × T*ℝ`, where the
cotangent bundle `T*ℝ = ℝ × ℝ` of the time axis has coordinates the time `t` and its conjugate
momentum `e` and carries the form `dt ∧ de`. Its two-form is the product
`σ ⊕ (dt ∧ de)` (`TauCeti.SmoothTwoForm.extended`), which is symplectic when `σ` is. For the
cotangent bundle `M = T*Q` of a configuration manifold this is the phase space `T*(Q × ℝ)` of
time-dependent mechanics: `TauCeti.CotangentBundle.prodDiffeomorph` splits `T*(Q × ℝ)`
symplectically as `T*Q × T*ℝ`, and here `T*ℝ` is written in its global coordinates `(t, e)`; the
comparison of Tau Ceti's cotangent bundle of `ℝ` with this coordinate plane is not made in this
file. This file is the manifold version of the linear model `TauCeti.SymplecticForm.extended` of
`TauCeti.Geometry.Symplectic.Hamiltonian.ExtendedPhaseSpace`.

The **extended Hamiltonian** `K(x, t, e) = e + H(t, x)` (`TauCeti.extendedHamiltonian`) is
autonomous. Its differential is `dK = de + ∂_t H dt + d(H t)`
(`TauCeti.mvfderiv_extendedHamiltonian_apply`), so if each `X t` is a Hamiltonian vector field of
`H t`, then

`X_K(x, t, e) = (X t x, 1, -∂_t H(t, x))`

(`TauCeti.extendedVectorField`) is a Hamiltonian vector field of `K`
(`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.extended`). For nondegenerate `σ` on a
finite-dimensional manifold it is the Hamiltonian vector field of `K`
(`TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianVectorField_extendedHamiltonian`). Along the flow
of `K` the time advances at unit speed, the point of `M` moves by the time-dependent Hamiltonian
vector field, and the momentum `e` of the time absorbs the change of energy:

* every solution `γ` of the nonautonomous equation `γ' = X_{H_u}(γ)` lifts to the integral curve
  `u ↦ (γ u, u, c - H(u, γ u))` of `X_K`, on which `K` has the constant value `c`
  (`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.hasMFDerivAt_extended_of_hasMFDerivAt`,
  `TauCeti.SmoothTwoForm.IsHamiltonianVectorField.isMIntegralCurve_extended`); the
  energy `H(u, γ u)` changes at the rate `∂_t H`
  (`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.hasDerivAt_apply_self_of_hasMFDerivAt`);
* conversely, along an integral curve of `X_K` the time runs at unit speed and the point of `M`
  solves the nonautonomous equation
  (`TauCeti.SmoothTwoForm.IsNondegenerate.hasMFDerivAt_fst_of_hasMFDerivAt_extended`).

A time-dependent function `F(t, x)` is an autonomous function on the extended phase space, and its
Poisson bracket with `K` there is `∂_t F + {F_t, H_t}`
(`TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_extendedHamiltonian`). This is the rate of
change of `F` along every solution of the nonautonomous equation
(`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_apply_of_hasMFDerivAt`). On a Hausdorff
boundaryless finite-dimensional manifold, for a jointly `C²` Hamiltonian, it characterises the
conserved quantities of the maximal time-dependent Hamiltonian flow
`TauCeti.timeDependentFlowOf`: `F` is constant along the flow wherever the flow is defined exactly
when `∂_t F + {F_t, H_t} = 0`
(`TauCeti.SmoothTwoForm.IsNondegenerate.forall_apply_timeDependentFlowOf_eq_iff`). No completeness
of the flow is assumed.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 45.
* J. E. Marsden and T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in
  Applied Mathematics 17, Springer, 1999, Sections 5.5 and 8.1.
-/

public section

open Function Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The extended Hamiltonian is differentiable wherever the time-dependent Hamiltonian is. -/
theorem mdifferentiableAt_extendedHamiltonian {H : ℝ → M → ℝ} {t e : ℝ} {x : M}
    (hH : MDifferentiableAt (𝓘(ℝ).prod I) 𝓘(ℝ) (uncurry H) (t, x)) :
    MDifferentiableAt (I.prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ) (extendedHamiltonian H) (x, (t, e)) := by
  have hsnd : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, ℝ × ℝ) (fun y : M × (ℝ × ℝ) ↦ y.2)
      (x, (t, e)) := mdifferentiableAt_snd
  have htime : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ) (fun y : M × (ℝ × ℝ) ↦ y.2.1)
      (x, (t, e)) := differentiableAt_fst.mdifferentiableAt.comp _ hsnd
  have henergy : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ) (fun y : M × (ℝ × ℝ) ↦ y.2.2)
      (x, (t, e)) := differentiableAt_snd.mdifferentiableAt.comp _ hsnd
  have hK : extendedHamiltonian H = fun y ↦ y.2.2 + uncurry H (y.2.1, y.1) :=
    funext fun y ↦ extendedHamiltonian_apply H y
  rw [hK]
  exact henergy.add (hH.comp (x, (t, e)) (htime.prodMk mdifferentiableAt_fst))

/-- **The differential of the extended Hamiltonian** `K(x, t, e) = e + H(t, x)` on the extended
phase space `M × T*ℝ`: `dK(δx, δt, δe) = δe + ∂_t H(t, x) δt + d(H t)(δx)`. -/
theorem mvfderiv_extendedHamiltonian_apply {H : ℝ → M → ℝ} {t e : ℝ} {x : M}
    (hH : MDifferentiableAt (𝓘(ℝ).prod I) 𝓘(ℝ) (uncurry H) (t, x))
    (w : TangentSpace (I.prod 𝓘(ℝ, ℝ × ℝ)) (x, (t, e))) :
    mvfderiv (I.prod 𝓘(ℝ, ℝ × ℝ)) (extendedHamiltonian H) (x, (t, e)) w =
      w.2.2 + deriv (fun s ↦ H s x) t * w.2.1 + mvfderiv I (H t) x w.1 := by
  -- The two slices of `H` through `(t, x)` are differentiable.
  have hx : MDifferentiableAt I 𝓘(ℝ) (H t) x :=
    hH.comp x (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have ht : DifferentiableAt ℝ (fun s ↦ H s x) t :=
    mdifferentiableAt_iff_differentiableAt.1
      (hH.comp t (mdifferentiableAt_id.prodMk mdifferentiableAt_const))
  -- The derivative in the coordinates `(t, e)` of `T*ℝ`.
  have hTR : HasFDerivAt (fun z : ℝ × ℝ ↦ z.2 + H z.1 x)
      (ContinuousLinearMap.snd ℝ ℝ ℝ +
        deriv (fun s ↦ H s x) t • ContinuousLinearMap.fst ℝ ℝ ℝ) (t, e) :=
    hasFDerivAt_snd.add (ht.hasDerivAt.comp_hasFDerivAt (f := Prod.fst) (t, e) hasFDerivAt_fst)
  -- The derivative along `T*ℝ` reads off the momentum and the time derivative of `H`.
  have hT : ∀ v : TangentSpace 𝓘(ℝ, ℝ × ℝ) (t, e),
      mvfderiv 𝓘(ℝ, ℝ × ℝ) (fun z ↦ extendedHamiltonian H (x, z)) (t, e) v =
        v.2 + deriv (fun s ↦ H s x) t * v.1 := by
    intro v
    have hfun : (fun z : ℝ × ℝ ↦ extendedHamiltonian H (x, z)) = fun z ↦ z.2 + H z.1 x :=
      funext fun z ↦ extendedHamiltonian_apply H (x, z)
    refine (mvfderiv_eq_fderiv_apply _ _ v).trans ?_
    rw [hfun, hTR.fderiv]
    -- `(snd + c • fst) v = v.2 + c * v.1`, with `v` read in `ℝ × ℝ`.
    rfl
  -- The derivative along `M` is that of `H t`, shifted by the constant `e`.
  have hM : ∀ v : TangentSpace I x,
      mvfderiv I (fun y ↦ extendedHamiltonian H (y, (t, e))) x v = mvfderiv I (H t) x v := by
    intro v
    have hfun : (fun y ↦ extendedHamiltonian H (y, (t, e))) = (fun r : ℝ ↦ e + r) ∘ H t :=
      funext fun y ↦ extendedHamiltonian_apply H (y, (t, e))
    refine ((congrArg (fun f ↦ mvfderiv I f x v) hfun).trans
      (mvfderiv_comp_apply_of_differentiableAt (φ := fun r : ℝ ↦ e + r)
        (differentiableAt_id.const_add e) hx v)).trans ?_
    rw [fderiv_const_add, fderiv_fun_id, ContinuousLinearMap.id_apply]
  exact ((mdifferentiableAt_extendedHamiltonian hH).mvfderiv_prod_eq_add_apply w).trans
    ((congrArg₂ (· + ·) (hM w.1) (hT w.2)).trans (by ring))

/-- The vector field `(x, t, e) ↦ (X t x, 1, -∂_t H(t, x))` on the extended phase space `M × T*ℝ`,
built from a time-dependent vector field `X` and a time-dependent Hamiltonian `H`. When each `X t`
is a Hamiltonian vector field of `H t`, it is a Hamiltonian vector field of the extended
Hamiltonian (`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.extended`). -/
noncomputable def extendedVectorField (H : ℝ → M → ℝ) (X : ℝ → (x : M) → TangentSpace I x) :
    (y : M × (ℝ × ℝ)) → TangentSpace (I.prod 𝓘(ℝ, ℝ × ℝ)) y :=
  fun y ↦ (X y.2.1 y.1, (1, -deriv (fun s ↦ H s y.1) y.2.1))

/-- The component of the extended vector field along `M` is `X t x`. -/
@[simp]
theorem extendedVectorField_fst (H : ℝ → M → ℝ) (X : ℝ → (x : M) → TangentSpace I x)
    (y : M × (ℝ × ℝ)) : (extendedVectorField H X y).1 = X y.2.1 y.1 :=
  (rfl)

/-- The time component of the extended vector field is `1`. -/
@[simp]
theorem extendedVectorField_snd_fst (H : ℝ → M → ℝ) (X : ℝ → (x : M) → TangentSpace I x)
    (y : M × (ℝ × ℝ)) : (extendedVectorField H X y).2.1 = 1 :=
  (rfl)

/-- The momentum component of the extended vector field is `-∂_t H(t, x)`. -/
@[simp]
theorem extendedVectorField_snd_snd (H : ℝ → M → ℝ) (X : ℝ → (x : M) → TangentSpace I x)
    (y : M × (ℝ × ℝ)) : (extendedVectorField H X y).2.2 = -deriv (fun s ↦ H s y.1) y.2.1 :=
  (rfl)

/-- The time coordinate of the extended phase space has derivative the time component of a
tangent vector. -/
private theorem mvfderiv_time_apply (p : M × (ℝ × ℝ))
    (v : TangentSpace (I.prod 𝓘(ℝ, ℝ × ℝ)) p) :
    mvfderiv (I.prod 𝓘(ℝ, ℝ × ℝ)) (fun y : M × (ℝ × ℝ) ↦ y.2.1) p v = v.2.1 :=
  (mvfderiv_comp_snd_apply (fun z : ℝ × ℝ ↦ z.1) p v).trans
    ((mvfderiv_eq_fderiv_apply _ _ _).trans (by rw [fderiv_fst]; rfl))

/-- The momentum coordinate of the extended phase space has derivative the momentum component of
a tangent vector. -/
private theorem mvfderiv_momentum_apply (p : M × (ℝ × ℝ))
    (v : TangentSpace (I.prod 𝓘(ℝ, ℝ × ℝ)) p) :
    mvfderiv (I.prod 𝓘(ℝ, ℝ × ℝ)) (fun y : M × (ℝ × ℝ) ↦ y.2.2) p v = v.2.2 :=
  (mvfderiv_comp_snd_apply (fun z : ℝ × ℝ ↦ z.2) p v).trans
    ((mvfderiv_eq_fderiv_apply _ _ _).trans (by rw [fderiv_snd]; rfl))

namespace SmoothTwoForm

variable [IsManifold I ∞ M] {σ : SmoothTwoForm I M}

/-- The two-form `σ ⊕ (dt ∧ de)` of the **extended phase space** `M × T*ℝ` of `(M, σ)`, where the
coordinates `(t, e)` of `T*ℝ = ℝ × ℝ` are the time and its conjugate momentum. -/
noncomputable def extended (σ : SmoothTwoForm I M) :
    SmoothTwoForm (I.prod 𝓘(ℝ, ℝ × ℝ)) (M × (ℝ × ℝ)) :=
  σ.prod (stdSymplecticForm (V := ℝ)).constSmooth

/-- The form of the extended phase space is the product of `σ` with the standard symplectic form
of the plane of the time and its conjugate momentum. -/
theorem extended_def (σ : SmoothTwoForm I M) :
    σ.extended = σ.prod (stdSymplecticForm (V := ℝ)).constSmooth :=
  (rfl)

/-- The form of the extended phase space evaluates on the components of tangent vectors as
`σ(v₁, w₁) + (δt_v δe_w - δe_v δt_w)`. -/
theorem eval₂_extended (σ : SmoothTwoForm I M) (p : M × (ℝ × ℝ))
    (v w : TangentSpace (I.prod 𝓘(ℝ, ℝ × ℝ)) p) :
    σ.extended.eval₂ p v w = σ.eval₂ p.1 v.1 w.1 + (v.2.1 * w.2.2 - v.2.2 * w.2.1) := by
  rw [extended_def, eval₂_prod, Manifold.tangentSpaceProdEquiv_apply,
    Manifold.tangentSpaceProdEquiv_apply, SymplecticForm.fromTangentSpace_constSmooth_apply,
    stdSymplecticForm_apply, NormedSpace.fromTangentSpace_apply,
    NormedSpace.fromTangentSpace_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- The form of the extended phase space of a nondegenerate form is nondegenerate. -/
theorem IsNondegenerate.extended (hσ : σ.IsNondegenerate) : σ.extended.IsNondegenerate :=
  hσ.prod (SymplecticForm.isNondegenerate_constSmooth _)

/-- **The extended phase space of a symplectic manifold is symplectic.** -/
theorem IsSymplectic.extended (hσ : σ.IsSymplectic) : σ.extended.IsSymplectic :=
  hσ.prod (SymplecticForm.isSymplectic_constSmooth _)

/-! ### The extended Hamiltonian vector field -/

/-- **The extended Hamiltonian vector field.** If each `X t` is a Hamiltonian vector field of
`H t` and `H` is jointly differentiable, then `(x, t, e) ↦ (X t x, 1, -∂_t H(t, x))` is a
Hamiltonian vector field of the extended Hamiltonian `K(x, t, e) = e + H(t, x)`. No
nondegeneracy is needed. -/
theorem IsHamiltonianVectorField.extended {H : ℝ → M → ℝ} {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ∀ t, σ.IsHamiltonianVectorField (H t) (X t))
    (hH : MDifferentiable (𝓘(ℝ).prod I) 𝓘(ℝ) (uncurry H)) :
    σ.extended.IsHamiltonianVectorField (extendedHamiltonian H) (extendedVectorField H X) := by
  rw [isHamiltonianVectorField_iff]
  rintro ⟨x, t, e⟩ w
  refine (eval₂_extended σ _ _ w).trans
    (Eq.trans ?_ (mvfderiv_extendedHamiltonian_apply (hH (t, x)) w).symm)
  simp only [extendedVectorField_fst, extendedVectorField_snd_fst, extendedVectorField_snd_snd]
  linear_combination isHamiltonianVectorField_iff.1 (hX t) x w.1

/-- **The Hamiltonian vector field of the extended Hamiltonian.** For a nondegenerate form on a
finite-dimensional manifold, where `H` is differentiable, the Hamiltonian vector field of
`K(x, t, e) = e + H(t, x)` is `X_K(x, t, e) = (X_{H_t}(x), 1, -∂_t H(t, x))`. -/
theorem IsNondegenerate.hamiltonianVectorField_extendedHamiltonian [FiniteDimensional ℝ E]
    (hσ : σ.IsNondegenerate) {H : ℝ → M → ℝ} {p : M × (ℝ × ℝ)}
    (hH : MDifferentiableAt (𝓘(ℝ).prod I) 𝓘(ℝ) (uncurry H) (p.2.1, p.1)) :
    σ.extended.hamiltonianVectorField (extendedHamiltonian H) p =
      extendedVectorField H (fun u ↦ σ.hamiltonianVectorField (H u)) p := by
  obtain ⟨x, t, e⟩ := p
  refine ((hσ.extended.isInvertible_flat _).injective ?_).symm
  rw [hσ.extended.flat_hamiltonianVectorField]
  refine ContinuousLinearMap.ext fun w ↦ (flat_apply _ _ _ w).trans ?_
  refine (eval₂_extended σ _ _ w).trans
    (Eq.trans ?_ (mvfderiv_extendedHamiltonian_apply hH w).symm)
  simp only [extendedVectorField_fst, extendedVectorField_snd_fst, extendedVectorField_snd_snd]
  linear_combination hσ.eval₂_hamiltonianVectorField (H t) x w.1

/-! ### Integral curves -/

/-- **The energy along a solution changes at the rate `∂_t H`.** If `X s` is a Hamiltonian vector
field of `H s` and the curve `γ` solves `γ' = X_s(γ)` at time `s`, then the energy
`u ↦ H(u, γ u)` has derivative `∂_t H(s, γ s)` at `s`. -/
theorem IsHamiltonianVectorField.hasDerivAt_apply_self_of_hasMFDerivAt {H : ℝ → M → ℝ}
    {X : ℝ → (x : M) → TangentSpace I x} {γ : ℝ → M} {s : ℝ}
    (hX : σ.IsHamiltonianVectorField (H s) (X s))
    (hH : MDifferentiableAt (𝓘(ℝ).prod I) 𝓘(ℝ) (uncurry H) (s, γ s))
    (hγ : HasMFDerivAt 𝓘(ℝ) I γ s ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (γ s)))) :
    HasDerivAt (fun u ↦ H u (γ u)) (deriv (fun u ↦ H u (γ s)) s) s := by
  simpa only [hX.mvfderiv_apply_self, add_zero] using hγ.hasDerivAt_comp_graph hH

/-- **Solutions of the nonautonomous equation lift to the extended phase space.** Let `X s` be a
Hamiltonian vector field of `H s`. If the curve `γ` solves `γ' = X_s(γ)` at time `s`, then the
curve `u ↦ (γ u, u, c - H(u, γ u))`, on which the extended Hamiltonian has the constant value
`c`, has velocity `(X_s(γ s), 1, -∂_t H(s, γ s))` at `s`: it is an integral curve at `s` of the
extended vector field. -/
theorem IsHamiltonianVectorField.hasMFDerivAt_extended_of_hasMFDerivAt {H : ℝ → M → ℝ}
    {X : ℝ → (x : M) → TangentSpace I x} {γ : ℝ → M} {s : ℝ}
    (hX : σ.IsHamiltonianVectorField (H s) (X s))
    (hH : MDifferentiableAt (𝓘(ℝ).prod I) 𝓘(ℝ) (uncurry H) (s, γ s))
    (hγ : HasMFDerivAt 𝓘(ℝ) I γ s ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (γ s)))) (c : ℝ) :
    HasMFDerivAt 𝓘(ℝ) (I.prod 𝓘(ℝ, ℝ × ℝ)) (fun u ↦ (γ u, (u, c - H u (γ u)))) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (extendedVectorField H X (γ s, (s, c - H s (γ s))))) := by
  have hE := hX.hasDerivAt_apply_self_of_hasMFDerivAt hH hγ
  have hT : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) (fun u ↦ (u, c - H u (γ u))) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((1 : ℝ), -deriv (fun u ↦ H u (γ s)) s)) := by
    have h := (hasDerivAt_id s).prodMk ((hasDerivAt_const s c).sub hE)
    rw [zero_sub] at h
    exact hasMFDerivAt_iff_hasFDerivAt.2 h.hasFDerivAt
  -- Both derivatives send `r` to `(r • X s (γ s), r • (1, -∂_t H))`.
  exact (hγ.prodMk hT).congr_mfderiv (ContinuousLinearMap.ext fun _ ↦ rfl)

/-- **Solutions of the nonautonomous equation are integral curves of the extended vector field.**
If each `X u` is a Hamiltonian vector field of `H u`, `H` is jointly differentiable and `γ` solves
`γ' = X_u(γ)` at all times, then `u ↦ (γ u, u, c - H(u, γ u))` is an integral curve of the
extended vector field `(x, t, e) ↦ (X t x, 1, -∂_t H(t, x))`. -/
theorem IsHamiltonianVectorField.isMIntegralCurve_extended {H : ℝ → M → ℝ}
    {X : ℝ → (x : M) → TangentSpace I x} {γ : ℝ → M}
    (hX : ∀ u, σ.IsHamiltonianVectorField (H u) (X u))
    (hH : MDifferentiable (𝓘(ℝ).prod I) 𝓘(ℝ) (uncurry H))
    (hγ : ∀ u, HasMFDerivAt 𝓘(ℝ) I γ u ((1 : ℝ →L[ℝ] ℝ).smulRight (X u (γ u)))) (c : ℝ) :
    IsMIntegralCurve (fun u ↦ (γ u, (u, c - H u (γ u)))) (extendedVectorField H X) :=
  fun u ↦ (hX u).hasMFDerivAt_extended_of_hasMFDerivAt (hH _) (hγ u) c

namespace IsNondegenerate

variable [FiniteDimensional ℝ E] (hσ : σ.IsNondegenerate)
include hσ

/-- **Integral curves of the extended Hamiltonian solve the nonautonomous equation.** If `y` is an
integral curve at `s` of the Hamiltonian vector field of the extended Hamiltonian, and `H` is
differentiable at its time and point, then its point `u ↦ (y u).1` solves the nonautonomous
equation `γ' = X_{H_t}(γ)` at `s`, where `t = (y s).2.1` is the time of `y s`. -/
theorem hasMFDerivAt_fst_of_hasMFDerivAt_extended {H : ℝ → M → ℝ} {y : ℝ → M × (ℝ × ℝ)} {s : ℝ}
    (hH : MDifferentiableAt (𝓘(ℝ).prod I) 𝓘(ℝ) (uncurry H) ((y s).2.1, (y s).1))
    (hy : HasMFDerivAt 𝓘(ℝ) (I.prod 𝓘(ℝ, ℝ × ℝ)) y s ((1 : ℝ →L[ℝ] ℝ).smulRight
      (σ.extended.hamiltonianVectorField (extendedHamiltonian H) (y s)))) :
    HasMFDerivAt 𝓘(ℝ) I (fun u ↦ (y u).1) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (σ.hamiltonianVectorField (H (y s).2.1) (y s).1)) := by
  rw [hσ.hamiltonianVectorField_extendedHamiltonian hH] at hy
  exact hy.fst_curve

/-- **The clock of the extended Hamiltonian runs at unit speed.** Along an integral curve of the
Hamiltonian vector field of the extended Hamiltonian, the time coordinate has derivative `1`. -/
theorem hasDerivAt_time_of_hasMFDerivAt_extended {H : ℝ → M → ℝ} {y : ℝ → M × (ℝ × ℝ)} {s : ℝ}
    (hH : MDifferentiableAt (𝓘(ℝ).prod I) 𝓘(ℝ) (uncurry H) ((y s).2.1, (y s).1))
    (hy : HasMFDerivAt 𝓘(ℝ) (I.prod 𝓘(ℝ, ℝ × ℝ)) y s ((1 : ℝ →L[ℝ] ℝ).smulRight
      (σ.extended.hamiltonianVectorField (extendedHamiltonian H) (y s)))) :
    HasDerivAt (fun u ↦ (y u).2.1) 1 s := by
  rw [hσ.hamiltonianVectorField_extendedHamiltonian hH] at hy
  have h := Manifold.hasDerivAt_comp_curve
    (g := fun p : M × (ℝ × ℝ) ↦ p.2.1) (differentiableAt_fst.mdifferentiableAt.comp _
      mdifferentiableAt_snd) hy
  rwa [mvfderiv_time_apply, extendedVectorField_snd_fst] at h

/-! ### Time-dependent functions and conserved quantities -/

/-- **The Poisson bracket with the extended Hamiltonian.** A time-dependent function `F(t, x)`,
read as the function `(x, t, e) ↦ F(t, x)` on the extended phase space, has Poisson bracket
`∂_t F + {F_t, H_t}` with the extended Hamiltonian, where `F` and `H` are differentiable. -/
theorem poissonBracket_extendedHamiltonian {F H : ℝ → M → ℝ} {t : ℝ} {x : M}
    (hF : MDifferentiableAt (𝓘(ℝ).prod I) 𝓘(ℝ) (uncurry F) (t, x))
    (hH : MDifferentiableAt (𝓘(ℝ).prod I) 𝓘(ℝ) (uncurry H) (t, x)) (e : ℝ) :
    σ.extended.poissonBracket (fun y ↦ F y.2.1 y.1) (extendedHamiltonian H) (x, (t, e)) =
      deriv (fun s ↦ F s x) t + σ.poissonBracket (F t) (H t) x := by
  -- `F` read on the extended phase space is the extended Hamiltonian of `F` minus the momentum.
  have hFK : (fun y : M × (ℝ × ℝ) ↦ F y.2.1 y.1) = fun y ↦ extendedHamiltonian F y - y.2.2 :=
    funext fun y ↦ by rw [extendedHamiltonian_apply, add_sub_cancel_left]
  have hsnd : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ) (fun y : M × (ℝ × ℝ) ↦ y.2.2)
      (x, (t, e)) := differentiableAt_snd.mdifferentiableAt.comp _ mdifferentiableAt_snd
  rw [hσ.extended.poissonBracket_eq_mvfderiv, hσ.hamiltonianVectorField_extendedHamiltonian hH,
    hFK, mvfderiv_fun_sub (mdifferentiableAt_extendedHamiltonian hF) hsnd,
    sub_apply, mvfderiv_extendedHamiltonian_apply hF,
    hσ.poissonBracket_eq_mvfderiv]
  simp only [mvfderiv_momentum_apply, extendedVectorField_fst, extendedVectorField_snd_fst,
    extendedVectorField_snd_snd]
  ring

/-- **The rate of change of a time-dependent function along a solution.** If the curve `γ` solves
the nonautonomous equation `γ' = X_{H_s}(γ)` at time `s` and `F` is differentiable at
`(s, γ s)`, then `u ↦ F(u, γ u)` has derivative `∂_t F + {F_s, H_s}` at `s`. -/
theorem hasDerivAt_apply_of_hasMFDerivAt {F H : ℝ → M → ℝ} {γ : ℝ → M} {s : ℝ}
    (hF : MDifferentiableAt (𝓘(ℝ).prod I) 𝓘(ℝ) (uncurry F) (s, γ s))
    (hγ : HasMFDerivAt 𝓘(ℝ) I γ s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (σ.hamiltonianVectorField (H s) (γ s)))) :
    HasDerivAt (fun u ↦ F u (γ u))
      (deriv (fun u ↦ F u (γ s)) s + σ.poissonBracket (F s) (H s) (γ s)) s := by
  rw [hσ.poissonBracket_eq_mvfderiv]
  exact hγ.hasDerivAt_comp_graph hF

/-- **Conserved quantities of a time-dependent Hamiltonian flow.** On a Hausdorff boundaryless
finite-dimensional manifold with a nondegenerate form, let `H` be a jointly `C²` time-dependent
Hamiltonian, with maximal time-dependent flow `φ_{s,t}` of `X_{H_t}`, and let `F` be a jointly
differentiable time-dependent function. Then `F(t, φ_{s,t} x) = F(s, x)` wherever the flow is
defined exactly when `∂_t F + {F_t, H_t} = 0`. -/
theorem forall_apply_timeDependentFlowOf_eq_iff [T2Space M] [BoundarylessManifold I M]
    {F H : ℝ → M → ℝ} (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry H))
    (hF : MDifferentiable (𝓘(ℝ).prod I) 𝓘(ℝ) (uncurry F)) :
    (∀ s t x, ((s, t), x) ∈ timeDependentFlowDomain (fun u ↦ σ.hamiltonianVectorField (H u)) →
        F t (timeDependentFlowOf (fun u ↦ σ.hamiltonianVectorField (H u)) s t x) = F s x) ↔
      ∀ t x, deriv (fun s ↦ F s x) t + σ.poissonBracket (F t) (H t) x = 0 := by
  set X : ℝ → (x : M) → TangentSpace I x := fun u ↦ σ.hamiltonianVectorField (H u)
  have hX : ContMDiff (𝓘(ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)) :=
    hσ.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp) hH
  -- Along the flow from `(s, x)`, `F` changes at the rate `∂_t F + {F_t, H_t}`.
  have hrate : ∀ {s u : ℝ} {x : M}, ((s, u), x) ∈ timeDependentFlowDomain X →
      HasDerivAt (fun r ↦ F r (timeDependentFlowOf X s r x))
        (deriv (fun r ↦ F r (timeDependentFlowOf X s u x)) u +
          σ.poissonBracket (F u) (H u) (timeDependentFlowOf X s u x)) u :=
    fun h ↦ hσ.hasDerivAt_apply_of_hasMFDerivAt (hF _) (hasMFDerivAt_timeDependentFlowOf hX h)
  constructor
  · intro hcons t x
    -- The function `u ↦ F(u, φ_{t,u} x)` is constant near `t`, where the flow is defined.
    have hnhds : {u | ((t, u), x) ∈ timeDependentFlowDomain X} ∈ 𝓝 t :=
      ((isOpen_timeDependentFlowDomain hX).preimage (by fun_prop)).mem_nhds
        (mem_timeDependentFlowDomain_self hX t x)
    have hconst : (fun u ↦ F u (timeDependentFlowOf X t u x)) =ᶠ[𝓝 t] fun _ ↦ F t x :=
      Filter.mem_of_superset hnhds fun u hu ↦ hcons t u x hu
    have h := hrate (mem_timeDependentFlowDomain_self hX t x)
    rw [timeDependentFlowOf_self] at h
    exact h.unique ((hasDerivAt_const t (F t x)).congr_of_eventuallyEq hconst)
  · intro hzero s t x hst
    obtain ⟨a, b, hs, ht, hab⟩ := exists_Ioo_of_mem_timeDependentFlowDomain hst
    -- On an interval of times at which the flow is defined, `F` has zero derivative along it.
    have hderiv : ∀ u ∈ Ioo a b, HasDerivAt (fun r ↦ F r (timeDependentFlowOf X s r x)) 0 u :=
      fun u hu ↦ hzero u _ ▸ hrate (hab u hu)
    have h := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun u hu ↦ (hderiv u hu).differentiableAt.differentiableWithinAt)
      (fun u hu ↦ (hderiv u hu).deriv) ht hs
    rwa [timeDependentFlowOf_self] at h

end IsNondegenerate

end SmoothTwoForm

end TauCeti
