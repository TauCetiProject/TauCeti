/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Legendre.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold

/-!
# The Lagrangian of a one-form

A smooth one-form `α` on a manifold `M` is a function on the tangent bundle, linear on each fibre:
the Lagrangian `L_α(v) = α(v)` (`TauCeti.oneFormLagrangian`). Such a Lagrangian is as degenerate
as possible. Its Legendre map is `α ∘ π`, the section of `T*M` defined by `α` composed with the
projection `π : TM → M` (`TauCeti.legendreMap_oneFormLagrangian`), so its fibre Hessian vanishes
(`TauCeti.fiberHessian_oneFormLagrangian`) and its energy `E_L(v) = FL(v)(v) - L(v)` is zero
(`TauCeti.lagrangianEnergy_oneFormLagrangian`). The Cartan forms are pulled back from `M`:
`θ_L = π^*α` and `ω_L = -π^*dα` (`TauCeti.cartanForm_oneFormLagrangian`,
`TauCeti.cartanTwoForm_oneFormLagrangian`), and `ω_L = 0` exactly when `α` is closed
(`TauCeti.cartanTwoForm_oneFormLagrangian_eq_zero_iff`).

These Lagrangians show that the regularity hypothesis of the Lagrangian vector field cannot be
dropped. For a regular Lagrangian, the Hamiltonian vector field `X_E` of the energy for `ω_L` is
second order, `dπ (X_E v) = v`
(`TauCeti.IsRegularLagrangian.mfderiv_proj_hamiltonianVectorField_lagrangianEnergy`). As soon as
`M` is nonempty and of positive dimension, `L_α` is not regular
(`TauCeti.not_isRegularLagrangian_oneFormLagrangian`). Its energy is zero, so the Hamiltonian
vector field of the energy vanishes for every two-form on `TM`, and its base component is `0`
rather than `v`
(`TauCeti.not_forall_mfderiv_proj_hamiltonianVectorField_lagrangianEnergy_oneFormLagrangian_eq`).
When `α` is closed the equation `ι_X ω_L = dE_L` reads `0 = 0`, so every vector field on `TM`
solves it (`TauCeti.isHamiltonianVectorField_lagrangianEnergy_oneFormLagrangian`), including
fields that are not second order.

The basic example is `L(q, v) = v` on `Q = ℝ`, the Lagrangian of the exact form `dq`
(`TauCeti.snd_eq_oneFormLagrangian_mextDerivₗ_id`): its Cartan one-form is `dq`, its Cartan
two-form and energy vanish (`TauCeti.cartanTwoForm_snd_eq_zero`), and the base component of the
Hamiltonian vector field of its energy is `0`, which differs from `v` for `v ≠ 0`
(`TauCeti.mfderiv_proj_hamiltonianVectorField_lagrangianEnergy_snd_eq_zero`). More generally the
Lagrangian of an exact form `df` is `v ↦ df(v)`, the total time derivative of `f` along a curve
(`TauCeti.oneFormLagrangian_mextDerivₗ_apply`).

## Main declarations

* `TauCeti.oneFormLagrangian`: the Lagrangian `v ↦ α(v)` of a one-form `α`.
* `TauCeti.legendreMap_oneFormLagrangian`, `TauCeti.fiberHessian_oneFormLagrangian`,
  `TauCeti.lagrangianEnergy_oneFormLagrangian`: its Legendre map `α ∘ π`, zero fibre Hessian and
  zero energy.
* `TauCeti.cartanForm_oneFormLagrangian`, `TauCeti.cartanTwoForm_oneFormLagrangian`: its Cartan
  forms `π^*α` and `-π^*dα`.
* `TauCeti.not_isRegularLagrangian_oneFormLagrangian`: it is not regular in positive dimension.
* `TauCeti.not_forall_mfderiv_proj_hamiltonianVectorField_lagrangianEnergy_oneFormLagrangian_eq`:
  the Hamiltonian vector field of its energy is not second order.

## References

* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Section 3.5.
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Section 7.2.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section Basic

variable [IsManifold I 1 M]

/-- The **Lagrangian of a one-form** `α`: the function `v ↦ α(v)` on the tangent bundle, linear on
each fibre. -/
def oneFormLagrangian (α : SmoothForm I M ℝ 1) (v : TangentBundle I M) : ℝ :=
  SmoothForm.degreeOneEquiv α v.proj v.snd

/-- The Lagrangian of a one-form evaluates the form on the tangent vector. -/
theorem oneFormLagrangian_apply (α : SmoothForm I M ℝ 1) (v : TangentBundle I M) :
    oneFormLagrangian α v = SmoothForm.degreeOneEquiv α v.proj v.snd :=
  (rfl)

/-- The Lagrangian of a one-form is smooth. -/
theorem contMDiff_oneFormLagrangian (α : SmoothForm I M ℝ 1) :
    ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ (oneFormLagrangian α) := by
  -- Apply the section `α ∘ π` of the cotangent bundle to `v`, as sections of bundles over `TM`.
  have h := ContMDiff.clm_bundle_apply (E₂ := Trivial M ℝ) (v := fun v : TangentBundle I M ↦ v.snd)
    ((SmoothForm.degreeOneEquiv α).contMDiff.comp (contMDiff_proj (TangentSpace I)))
    contMDiff_id
  exact fun v ↦ (contMDiffAt_totalSpace_iff.1 (h v)).2

/-- **The Legendre map of a one-form is the form.** The Lagrangian `v ↦ α(v)` has Legendre map
`α ∘ π`: it sends a tangent vector at `x` to the covector `α_x`. -/
@[simp]
theorem legendreMap_oneFormLagrangian (α : SmoothForm I M ℝ 1) (v : TangentBundle I M) :
    legendreMap (oneFormLagrangian α) v =
      TotalSpace.mk' (E →L[ℝ] ℝ) v.proj (SmoothForm.degreeOneEquiv α v.proj) := by
  refine CotangentBundle.ext (proj_legendreMap _ v) fun w ↦ ?_
  rw [legendreMap_snd]
  -- On the fibre over `v.proj` the Lagrangian is the continuous linear functional `α_x`.
  exact DFunLike.congr_fun (SmoothForm.degreeOneEquiv α v.proj).fderiv w

/-- The fibre Hessian of the Lagrangian of a one-form vanishes. -/
@[simp]
theorem fiberHessian_oneFormLagrangian (α : SmoothForm I M ℝ 1) (v : TangentBundle I M) :
    fiberHessian (oneFormLagrangian α) v = 0 := by
  -- On the fibre over `v.proj` the Lagrangian is the continuous linear functional `α_x`, whose
  -- derivative is constant.
  obtain ⟨ℓ, h⟩ : ∃ ℓ : E →L[ℝ] ℝ,
      (fun w : E ↦ oneFormLagrangian α (TotalSpace.mk' E v.proj w)) = ℓ :=
    ⟨SmoothForm.degreeOneEquiv α v.proj, funext fun w ↦ oneFormLagrangian_apply α _⟩
  have h' : fderiv ℝ ℓ = fun _ ↦ ℓ := funext fun _ ↦ ℓ.fderiv
  rw [fiberHessian_def, h, h']
  exact fderiv_const_apply ℓ

/-- The energy of the Lagrangian of a one-form vanishes: `FL(v)(v) = α(v) = L(v)`. -/
@[simp]
theorem lagrangianEnergy_oneFormLagrangian (α : SmoothForm I M ℝ 1) :
    lagrangianEnergy (oneFormLagrangian α) = 0 := by
  funext v
  rw [lagrangianEnergy_apply, legendreMap_oneFormLagrangian, oneFormLagrangian_apply, sub_self,
    Pi.zero_apply]

/-- **The Lagrangian of a one-form is not regular** on a nonempty manifold of positive dimension:
its fibre Hessian vanishes. -/
theorem not_isRegularLagrangian_oneFormLagrangian [Nontrivial E] [Nonempty M]
    (α : SmoothForm I M ℝ 1) : ¬IsRegularLagrangian (oneFormLagrangian α) := by
  intro h
  have hv := isRegularLagrangian_iff.1 h (TotalSpace.mk' E (Classical.arbitrary M) (0 : E))
  rw [fiberHessian_oneFormLagrangian, ContinuousLinearMap.isInvertible_zero_iff] at hv
  exact not_subsingleton E hv.1

omit [IsManifold I 1 M] in
/-- The Lagrangian of the differential of a function `f` evaluates `df` on the tangent vector: for
a curve it is the time derivative of `f` along the curve. -/
theorem oneFormLagrangian_mextDerivₗ_apply [IsManifold I 2 M] (f : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯)
    (v : TangentBundle I M) :
    oneFormLagrangian (mextDerivₗ I 0 (SmoothForm.ofFunction f)) v = mvfderiv I f v.proj v.snd := by
  rw [oneFormLagrangian_apply, SmoothForm.degreeOneEquiv_apply_apply_vec, mextDerivₗ_zero_apply,
    SmoothForm.ofFunction_apply_zero]

end Basic

section HamiltonianVectorField

variable [IsManifold I ∞ M]

/-- The Hamiltonian vector field of the energy of the Lagrangian of a one-form vanishes, for every
two-form on the tangent bundle: the energy is zero. -/
theorem hamiltonianVectorField_lagrangianEnergy_oneFormLagrangian (α : SmoothForm I M ℝ 1)
    (σ : SmoothTwoForm I.tangent (TangentBundle I M)) :
    σ.hamiltonianVectorField (lagrangianEnergy (oneFormLagrangian α)) = 0 := by
  rw [lagrangianEnergy_oneFormLagrangian]
  exact SmoothTwoForm.hamiltonianVectorField_const σ 0

/-- **The regularity hypothesis is not removable.** For the Lagrangian of a one-form on a nonempty
manifold of positive dimension, and any two-form `σ` on the tangent bundle, the Hamiltonian vector
field `X_E` of the energy is not second order: `dπ (X_E v) = 0`, which differs from `v` at every
nonzero tangent vector. For regular Lagrangians and `σ = ω_L`, instead `dπ (X_E v) = v`
(`TauCeti.IsRegularLagrangian.mfderiv_proj_hamiltonianVectorField_lagrangianEnergy`). -/
theorem not_forall_mfderiv_proj_hamiltonianVectorField_lagrangianEnergy_oneFormLagrangian_eq
    [Nontrivial E] [Nonempty M] (α : SmoothForm I M ℝ 1)
    (σ : SmoothTwoForm I.tangent (TangentBundle I M)) :
    ¬∀ v : TangentBundle I M, mfderiv I.tangent I (π E (TangentSpace I)) v
      (σ.hamiltonianVectorField (lagrangianEnergy (oneFormLagrangian α)) v) = v.snd := by
  intro h
  obtain ⟨u, hu⟩ := exists_ne (0 : E)
  have hv := h (TotalSpace.mk' E (Classical.arbitrary M) u)
  rw [hamiltonianVectorField_lagrangianEnergy_oneFormLagrangian, Pi.zero_apply, map_zero] at hv
  exact hu hv.symm

/-- **The Cartan one-form of a one-form is its pullback to the tangent bundle**: `θ_L = π^*α` for
the Lagrangian `L(v) = α(v)`. -/
theorem cartanForm_oneFormLagrangian (α : SmoothForm I M ℝ 1)
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ (oneFormLagrangian α)) :
    cartanForm (oneFormLagrangian α) hL =
      SmoothForm.mpullback (π E (TangentSpace I)) (contMDiff_proj (TangentSpace I)) α := by
  apply Subtype.ext
  funext v
  ext ξ
  rw [cartanForm_apply, legendreMap_oneFormLagrangian, SmoothForm.mpullback_apply]
  -- Both sides evaluate `α` at `π v` on the image of the single vector `ξ 0` under `dπ`.
  exact (SmoothForm.degreeOneEquiv_apply_apply α v.proj _).trans
    (congrArg (α.val v.proj) (funext fun i ↦ by rw [Fin.fin_one_eq_zero i]))

/-- **The Cartan two-form of a one-form**: `ω_L = -π^*dα` for the Lagrangian `L(v) = α(v)`. -/
theorem cartanTwoForm_oneFormLagrangian (α : SmoothForm I M ℝ 1)
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ (oneFormLagrangian α)) :
    cartanTwoForm (oneFormLagrangian α) hL =
      -SmoothForm.mpullback (π E (TangentSpace I)) (contMDiff_proj (TangentSpace I))
        (mextDerivₗ I 1 α) := by
  rw [cartanTwoForm_eq_neg_mextDerivₗ, cartanForm_oneFormLagrangian,
    SmoothForm.mextDerivₗ_mpullback]

/-- The Cartan two-form of the Lagrangian of a one-form vanishes exactly when the form is
closed. -/
theorem cartanTwoForm_oneFormLagrangian_eq_zero_iff (α : SmoothForm I M ℝ 1)
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ (oneFormLagrangian α)) :
    cartanTwoForm (oneFormLagrangian α) hL = 0 ↔ α.IsClosed := by
  rw [cartanTwoForm_oneFormLagrangian, neg_eq_zero, SmoothForm.isClosed_iff_mextDerivₗ_eq_zero,
    ← map_zero (SmoothForm.mpullback (π E (TangentSpace I)) (contMDiff_proj (TangentSpace I)))]
  exact SmoothForm.mpullback_proj_injective.eq_iff

/-- **Every vector field solves the Lagrangian equation of a closed one-form.** For the Lagrangian
of a closed one-form, the Cartan two-form and the energy both vanish, so every vector field on
the tangent bundle is a Hamiltonian vector field of the energy for the Cartan two-form. -/
theorem isHamiltonianVectorField_lagrangianEnergy_oneFormLagrangian {α : SmoothForm I M ℝ 1}
    (hα : α.IsClosed) (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ (oneFormLagrangian α))
    (X : (v : TangentBundle I M) → TangentSpace I.tangent v) :
    (cartanTwoForm (oneFormLagrangian α) hL).IsHamiltonianVectorField
      (lagrangianEnergy (oneFormLagrangian α)) X := by
  rw [(cartanTwoForm_oneFormLagrangian_eq_zero_iff α hL).2 hα,
    lagrangianEnergy_oneFormLagrangian, SmoothTwoForm.isHamiltonianVectorField_iff]
  intro v w
  simp [Pi.zero_def, mvfderiv_const]

end HamiltonianVectorField

section Line

/-- The Lagrangian `L(q, v) = v` on the real line is the Lagrangian of the exact one-form `dq`. -/
theorem snd_eq_oneFormLagrangian_mextDerivₗ_id :
    (fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ v.snd) =
      oneFormLagrangian (mextDerivₗ 𝓘(ℝ, ℝ) 0
        (SmoothForm.ofFunction ContMDiffMap.id)) := by
  funext v
  -- The coercion of `ContMDiffMap.id` is `id` by definition.
  have hid : ⇑(ContMDiffMap.id : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) = id := rfl
  rw [oneFormLagrangian_mextDerivₗ_apply, hid, mvfderiv_apply_eq_mfderiv_apply, mfderiv_id,
    ContinuousLinearMap.id_apply]

/-- **The Cartan two-form of `L(q, v) = v` vanishes.** Its Cartan one-form is `dq`, which is
closed. -/
theorem cartanTwoForm_snd_eq_zero :
    cartanTwoForm (fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ v.snd)
      (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)) = 0 := by
  -- The Cartan two-form of the Lagrangian of an exact form vanishes; transport along the equality
  -- of Lagrangians, which also moves the smoothness proof.
  have key : ∀ (f : SmoothForm 𝓘(ℝ, ℝ) ℝ ℝ 0) (L : TangentBundle 𝓘(ℝ, ℝ) ℝ → ℝ)
      (hL : ContMDiff 𝓘(ℝ, ℝ).tangent 𝓘(ℝ, ℝ) ∞ L),
      L = oneFormLagrangian (mextDerivₗ 𝓘(ℝ, ℝ) 0 f) → cartanTwoForm L hL = 0 := by
    rintro f L hL rfl
    exact (cartanTwoForm_oneFormLagrangian_eq_zero_iff _ hL).2 (SmoothForm.isClosed_mextDerivₗ f)
  exact key _ _ _ snd_eq_oneFormLagrangian_mextDerivₗ_id

/-- **The Hamiltonian vector field of the energy of `L(q, v) = v` is not second order.** Its energy
is zero, so for every two-form on the tangent bundle the Hamiltonian vector field of the energy
vanishes and its base component is `0`, not `v`. Since the Cartan two-form also vanishes, the
equation `ι_X ω_L = dE_L` does not force a second-order field: every vector field solves it. -/
theorem mfderiv_proj_hamiltonianVectorField_lagrangianEnergy_snd_eq_zero
    (σ : SmoothTwoForm 𝓘(ℝ, ℝ).tangent (TangentBundle 𝓘(ℝ, ℝ) ℝ)) (v : TangentBundle 𝓘(ℝ, ℝ) ℝ) :
    mfderiv 𝓘(ℝ, ℝ).tangent 𝓘(ℝ, ℝ) (π ℝ (TangentSpace 𝓘(ℝ, ℝ))) v
      (σ.hamiltonianVectorField (lagrangianEnergy fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ v.snd) v) =
      0 := by
  rw [snd_eq_oneFormLagrangian_mextDerivₗ_id,
    hamiltonianVectorField_lagrangianEnergy_oneFormLagrangian, Pi.zero_apply, map_zero]

end Line

end TauCeti
