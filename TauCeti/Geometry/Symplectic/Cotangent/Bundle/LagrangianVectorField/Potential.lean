/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.LagrangianVectorField
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Legendre.Velocity
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Lagrangian vector field of a Lagrangian with a potential

Let `L : TM → ℝ` be a smooth Lagrangian on a manifold `M`, with fibre Hessian `Hess_v` at `v`
(`TauCeti.fiberHessian`), and let `V : M → ℝ` be a potential. Subtracting the potential,
`L_V(v) = L(v) - V(x)` for `v ∈ T_x M`, changes neither the Legendre map nor the Cartan two-form
`ω_L` (`TauCeti.cartanTwoForm_sub_comp_proj`), and it adds the potential to the energy,
`E_{L_V} = E_L + V ∘ π` (`TauCeti.lagrangianEnergy_sub_comp_proj`). So the Lagrangian vector field
of `L_V` is that of `L` plus the Hamiltonian vector field of `V ∘ π` for `ω_L`, the **force** of
the potential. For a regular Lagrangian this file identifies the force as the vertical vector

`F(v) = (0, -Hess_v⁻¹ dV_x)` at `v ∈ T_x M`

(`TauCeti.potentialForce`,
`TauCeti.IsRegularLagrangian.isHamiltonianVectorField_cartanTwoForm_potentialForce`). Indeed `ω_L`
pairs a tangent vector `ξ` of `TM` with the vertical vector `u^v` by `Hess_v(u, dπ ξ)`
(`TauCeti.eval₂_cartanTwoForm_vertical`), so `ω_L(F(v), ξ) = dV_x(dπ ξ) = d(V ∘ π)_v(ξ)`.
Hence (`TauCeti.IsRegularLagrangian.hamiltonianVectorField_lagrangianEnergy_sub_comp_proj`)

`X_{E_{L_V}}(v) = X_{E_L}(v) + (0, -Hess_v⁻¹ dV_x)`.

The Lagrangian vector field of `L_V` is second order like that of `L`
(`TauCeti.IsRegularLagrangian.mfderiv_proj_hamiltonianVectorField_lagrangianEnergy`), and the force
changes only its vertical component: the acceleration of a motion is that of the motion of `L`
with the same velocity, minus `Hess_v⁻¹ dV_x`. For the mechanical Lagrangian `½ g(v, v) - V(x)`
of a metric `g` the fibre Hessian is `g_x` (`TauCeti.fiberHessian_mechanicalLagrangian`), so the
force is `-g_x⁻¹ dV_x`, minus the gradient of `V`.

On a normed space `E`, with tangent vectors written as pairs `(q, v)` of a position and a velocity,
a Lagrangian `f(v)` depending only on the velocity has the uniform motion `(q, v) ↦ (v, 0)` as a
Lagrangian vector field (`TauCeti.isHamiltonianVectorField_lagrangianEnergy_comp_snd`), with no
regularity assumption. With a potential `V(q)` and an invertible second derivative of `f`, the
Lagrangian vector field of `f(v) - V(q)` is therefore

`(q, v) ↦ (v, -D²f(v)⁻¹ DV(q))`

(`TauCeti.hamiltonianVectorField_lagrangianEnergy_comp_snd_sub`), Newton's equation
`D²f(v) q'' = -DV(q)` written as a first-order system.

## Main results

* `TauCeti.potentialForce`: the force `(0, -Hess_v⁻¹ dV_x)` of a potential.
* `TauCeti.IsRegularLagrangian.isHamiltonianVectorField_cartanTwoForm_potentialForce`: the force
  is the Hamiltonian vector field of `V ∘ π` for the Cartan two-form.
* `TauCeti.IsRegularLagrangian.isHamiltonianVectorField_lagrangianEnergy_sub_comp_proj`: adding
  the force to a Lagrangian vector field of `L` gives a Lagrangian vector field of `L - V ∘ π`.
* `TauCeti.IsRegularLagrangian.hamiltonianVectorField_lagrangianEnergy_sub_comp_proj`: the
  Lagrangian vector field of `L - V ∘ π` on a finite-dimensional boundaryless manifold.
* `TauCeti.eval₂_cartanTwoForm_comp_snd`, `TauCeti.mvfderiv_lagrangianEnergy_comp_snd`: the
  Cartan two-form and the differential of the energy of `f(v)` on a normed space.
* `TauCeti.isHamiltonianVectorField_lagrangianEnergy_comp_snd`,
  `TauCeti.hamiltonianVectorField_lagrangianEnergy_comp_snd_sub`: the Lagrangian vector fields of
  `f(v)` and of `f(v) - V(q)` on a normed space.

## References

* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Chapter 3 (Lagrangian systems and mechanics on Riemannian manifolds).
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Chapter 7.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

section Manifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {L : TangentBundle I M → ℝ} {V : M → ℝ}

/-- The **force** of a potential `V` for a Lagrangian `L`: the vertical vector
`(0, -Hess_v⁻¹ dV_x)` of `TM` at `v ∈ T_x M`, where `Hess_v` is the fibre Hessian of `L` at `v`.
For a regular Lagrangian it is the Hamiltonian vector field of `V ∘ π` for the Cartan two-form
(`TauCeti.IsRegularLagrangian.isHamiltonianVectorField_cartanTwoForm_potentialForce`). -/
def potentialForce (L : TangentBundle I M → ℝ) (V : M → ℝ) (v : TangentBundle I M) :
    TangentSpace I.tangent v :=
  ((0 : E), -(fiberHessian L v).inverse (mvfderiv I V v.proj))

/-- The force of a potential is the vertical vector `(0, -Hess_v⁻¹ dV_x)`. -/
theorem potentialForce_def (L : TangentBundle I M → ℝ) (V : M → ℝ) (v : TangentBundle I M) :
    potentialForce L V v = ((0 : E), -(fiberHessian L v).inverse (mvfderiv I V v.proj)) :=
  (rfl)

/-- The force of a potential is vertical: the projection `π : TM → M` sends it to `0`. -/
@[simp]
theorem mfderiv_proj_potentialForce (L : TangentBundle I M → ℝ) (V : M → ℝ)
    (v : TangentBundle I M) :
    mfderiv I.tangent I (π E (TangentSpace I)) v (potentialForce L V v) = 0 := by
  rw [Bundle.mfderiv_proj]
  rfl

/-- The force of a potential, with its fibre component read in the trivialization of `TM` at the
base point; this is the form in which `TauCeti.eval₂_cartanTwoForm_vertical` sees it. -/
private theorem potentialForce_eq_continuousLinearMapAt (L : TangentBundle I M → ℝ) (V : M → ℝ)
    (v : TangentBundle I M) :
    potentialForce L V v =
      ((0 : E), (trivializationAt E (TangentSpace I) v.proj).continuousLinearMapAt ℝ v.proj
        (-(fiberHessian L v).inverse (mvfderiv I V v.proj))) := by
  rw [Manifold.continuousLinearMapAt_trivializationAt_self]
  rfl

namespace IsRegularLagrangian

variable (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) (hreg : IsRegularLagrangian L)
include hreg

/-- **The force of a potential is its Hamiltonian vector field.** For a smooth regular Lagrangian
`L` and a differentiable potential `V`, the Hamiltonian vector field of `V ∘ π` for the Cartan
two-form `ω_L` is the vertical vector field `(0, -Hess_v⁻¹ dV_x)` at `v ∈ T_x M`. -/
theorem isHamiltonianVectorField_cartanTwoForm_potentialForce (hV : MDifferentiable I 𝓘(ℝ) V) :
    (cartanTwoForm L hL).IsHamiltonianVectorField (fun v ↦ V v.proj) (potentialForce L V) := by
  refine SmoothTwoForm.isHamiltonianVectorField_iff.2 fun v ξ ↦ ?_
  -- Pair with `ξ` in the other order: `ω_L(ξ, u^v) = Hess_v(u, dπ ξ)`, and
  -- `Hess_v(-Hess_v⁻¹ dV_x) = -dV_x`.
  rw [SmoothBundleForm.eval₂_swap, potentialForce_eq_continuousLinearMapAt,
    eval₂_cartanTwoForm_vertical hL v ξ, map_neg (fiberHessian L v),
    ((isRegularLagrangian_iff.1 hreg) v).self_apply_inverse, neg_apply, neg_neg]
  -- `d(V ∘ π)_v(ξ) = dV_x(dπ ξ)`.
  exact (mvfderiv_comp_apply (g := V) (f := π E (TangentSpace I)) v (hV v.proj)
    ((contMDiff_proj (n := 1) (TangentSpace I) v).mdifferentiableAt one_ne_zero) ξ).symm

/-- **Adding a potential adds its force.** For a smooth regular Lagrangian `L` and a potential
`V` with `L - V ∘ π` smooth, if `X` is a Lagrangian vector field of `L`, a Hamiltonian vector field
of the energy `E_L` for the Cartan two-form `ω_L`, then adding the force
`(0, -Hess_v⁻¹ dV_x)` at `v ∈ T_x M` gives a Lagrangian vector field of `L - V ∘ π`. -/
theorem isHamiltonianVectorField_lagrangianEnergy_sub_comp_proj
    (hLV : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ (fun v ↦ L v - V v.proj))
    {X : (v : TangentBundle I M) → TangentSpace I.tangent v}
    (hX : (cartanTwoForm L hL).IsHamiltonianVectorField (lagrangianEnergy L) X) :
    (cartanTwoForm (fun v ↦ L v - V v.proj) hLV).IsHamiltonianVectorField
      (lagrangianEnergy fun v ↦ L v - V v.proj) fun v ↦ X v + potentialForce L V v := by
  -- `V` is the difference of `L` and `L - V ∘ π` along the zero section, so it is smooth.
  have hV : ContMDiff I 𝓘(ℝ) ∞ V := by
    have h := (hL.sub hLV).comp (Bundle.contMDiff_zeroSection ℝ (TangentSpace I))
    convert h using 1
    funext x
    simp
  have hF := SmoothTwoForm.isHamiltonianVectorField_iff.1
    (hreg.isHamiltonianVectorField_cartanTwoForm_potentialForce hL (hV.mdifferentiable (by simp)))
  have hE : lagrangianEnergy (fun v ↦ L v - V v.proj) =
      lagrangianEnergy L + fun v ↦ V v.proj :=
    funext (lagrangianEnergy_sub_comp_proj L V)
  refine SmoothTwoForm.isHamiltonianVectorField_iff.2 fun v ξ ↦ ?_
  have hEd : MDifferentiableAt I.tangent 𝓘(ℝ) (lagrangianEnergy L) v :=
    (contMDiff_lagrangianEnergy (m := 1) hL (by simp) v).mdifferentiableAt one_ne_zero
  have hVd : MDifferentiableAt I.tangent 𝓘(ℝ) (fun v : TangentBundle I M ↦ V v.proj) v :=
    (hV.comp (contMDiff_proj (TangentSpace I)) v).mdifferentiableAt (by simp)
  rw [cartanTwoForm_sub_comp_proj hL hLV, SmoothBundleForm.eval₂_add_left,
    SmoothTwoForm.isHamiltonianVectorField_iff.1 hX v ξ, hF v ξ, hE, mvfderiv_add hEd hVd,
    add_apply]

variable [FiniteDimensional ℝ E] [BoundarylessManifold I.tangent (TangentBundle I M)]

/-- **The Lagrangian vector field of a Lagrangian with a potential.** For a smooth regular
Lagrangian `L` on a finite-dimensional boundaryless manifold and a potential `V` with `L - V ∘ π`
smooth, the Lagrangian vector field of `L - V ∘ π` is that of `L` plus the force
`(0, -Hess_v⁻¹ dV_x)` at `v ∈ T_x M`. -/
theorem hamiltonianVectorField_lagrangianEnergy_sub_comp_proj
    (hLV : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ (fun v ↦ L v - V v.proj)) (v : TangentBundle I M) :
    (cartanTwoForm (fun v ↦ L v - V v.proj) hLV).hamiltonianVectorField
        (lagrangianEnergy fun v ↦ L v - V v.proj) v =
      (cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L) v +
        potentialForce L V v := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have hω := (isRegularLagrangian_sub_comp_proj_iff.2 hreg).isSymplectic_cartanTwoForm hLV
  refine congrFun (hω.isNondegenerate.isHamiltonianVectorField_iff_eq.1
    (hreg.isHamiltonianVectorField_lagrangianEnergy_sub_comp_proj hL hLV ?_)).symm v
  exact (hreg.isSymplectic_cartanTwoForm hL).isNondegenerate
    |>.isHamiltonianVectorField_hamiltonianVectorField _

end IsRegularLagrangian

end Manifold

/-! ### Lagrangians on a normed space -/

section VectorSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {V : E → ℝ}

/-- The charts of `TE` read a tangent vector `v ∈ T_q E` as the pair `(q, v)`, so a Lagrangian
`f(v)` reads as `(q, v) ↦ f(v)` in every chart. -/
private theorem comp_extChartAt_symm_comp_snd (f : E → ℝ) (v : TangentBundle 𝓘(ℝ, E) E) :
    ((fun v : TangentBundle 𝓘(ℝ, E) E ↦ f v.snd) ∘ (extChartAt 𝓘(ℝ, E).tangent v).symm) =
      fun y : E × E ↦ f y.2 := by
  funext y
  simp [extChartAt, OpenPartialHomeomorph.extend, tangentBundle_model_space_chartAt]
  -- The inverse chart is `(TotalSpace.toProd E E).symm`, which sends `(q, v)` to `⟨q, v⟩`.
  rfl

/-- The chart of `TE` at `v ∈ T_q E` reads `v` as the pair `(q, v)`. -/
private theorem extChartAt_tangent_self_modelSpace (v : TangentBundle 𝓘(ℝ, E) E) :
    extChartAt 𝓘(ℝ, E).tangent v v = ((v.proj, v.snd) : E × E) := by
  rw [TangentBundle.extChartAt_self, extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id]
  rfl

/-- The Legendre map `(q, v) ↦ (q, Df(v))` of `(q, v) ↦ f(v)` on `E × E` has derivative
`(a, b) ↦ (a, D²f(v) b)` at `(q, v)`. -/
private theorem hasFDerivAt_linearLegendreMap_comp_snd (hf : ContDiff ℝ ∞ f) (y : E × E) :
    HasFDerivAt (linearLegendreMap fun y : E × E ↦ f y.2)
      ((ContinuousLinearMap.fst ℝ E E).prod
        ((fderiv ℝ (fderiv ℝ f) y.2).comp (ContinuousLinearMap.snd ℝ E E))) y := by
  have hLLM : linearLegendreMap (fun y : E × E ↦ f y.2) = fun y ↦ (y.1, fderiv ℝ f y.2) :=
    funext fun y ↦ Prod.ext (linearLegendreMap_fst _ y) (linearLegendreMap_snd _ y)
  rw [hLLM]
  exact hasFDerivAt_fst.prodMk ((((hf.fderiv_right (m := 1) (by simp)).differentiable
    one_ne_zero) y.2).hasFDerivAt.comp y hasFDerivAt_snd)

/-- **The Cartan two-form of a Lagrangian depending only on the velocity.** On a normed space,
for a smooth Lagrangian `f(v)`, the Cartan two-form at `(q, v)` pairs the tangent vectors
`X = (a, b)` and `W = (c, d)` of `TE` by `ω_L(X, W) = D²f(v)(d, a) - D²f(v)(b, c)`. -/
theorem eval₂_cartanTwoForm_comp_snd
    (hL : ContMDiff 𝓘(ℝ, E).tangent 𝓘(ℝ, ℝ) ∞ fun v : TangentBundle 𝓘(ℝ, E) E ↦ f v.snd)
    (v : TangentBundle 𝓘(ℝ, E) E) (X W : TangentSpace 𝓘(ℝ, E).tangent v) :
    SmoothBundleForm.eval₂ (cartanTwoForm _ hL) v X W =
      fderiv ℝ (fderiv ℝ f) v.snd W.2 X.1 - fderiv ℝ (fderiv ℝ f) v.snd X.2 W.1 := by
  -- `f` is smooth: it is `L` along a fibre of `TE`.
  have hf : ContDiff ℝ ∞ f :=
    contMDiff_iff_contDiff.1 (hL.comp (contMDiff_tangentBundle_mk_constBase contMDiff_id 0))
  rw [eval₂_cartanTwoForm_eq_fderiv_linearLegendreMap, comp_extChartAt_symm_comp_snd,
    extChartAt_tangent_self_modelSpace, (hasFDerivAt_linearLegendreMap_comp_snd hf _).fderiv]
  exact strongDualCotangentSymplecticForm_apply _ _

/-- **The differential of the energy of a Lagrangian depending only on the velocity.** On a
normed space, for a smooth Lagrangian `f(v)`, the differential of the energy
`E_L(q, v) = Df(v)(v) - f(v)` at `(q, v)` sends the tangent vector `W = (c, d)` of `TE` to
`D²f(v)(d, v)`. -/
theorem mvfderiv_lagrangianEnergy_comp_snd
    (hL : ContMDiff 𝓘(ℝ, E).tangent 𝓘(ℝ, ℝ) ∞ fun v : TangentBundle 𝓘(ℝ, E) E ↦ f v.snd)
    (v : TangentBundle 𝓘(ℝ, E) E) (W : TangentSpace 𝓘(ℝ, E).tangent v) :
    mvfderiv 𝓘(ℝ, E).tangent (lagrangianEnergy fun v : TangentBundle 𝓘(ℝ, E) E ↦ f v.snd) v W =
      fderiv ℝ (fderiv ℝ f) v.snd W.2 v.snd := by
  have hf : ContDiff ℝ ∞ f :=
    contMDiff_iff_contDiff.1 (hL.comp (contMDiff_tangentBundle_mk_constBase contMDiff_id 0))
  -- In the chart the energy is `(q, v) ↦ Df(v)(v) - f(v)`; the terms `Df(v)(d)` cancel.
  have hE : HasFDerivAt (fun y : E × E ↦ (linearLegendreMap (fun y : E × E ↦ f y.2) y).2 y.2 -
      f y.2) _ ((v.proj, v.snd) : E × E) :=
    ((hasFDerivAt_linearLegendreMap_comp_snd hf _).snd.clm_apply hasFDerivAt_snd).sub
      (((hf.differentiable (by simp)) v.snd).hasFDerivAt.comp ((v.proj, v.snd) : E × E)
        hasFDerivAt_snd)
  rw [mvfderiv_lagrangianEnergy_eq_fderiv hL (by simp), comp_extChartAt_symm_comp_snd,
    extChartAt_tangent_self_modelSpace, hE.fderiv]
  simp
  -- `W` is a pair of the model `E × E`, and `(D²f(v) ∘ snd).flip v` sends it to `D²f(v)(W.2)(v)`.
  rfl

/-- **Uniform motion is Lagrangian for a Lagrangian depending only on the velocity.** On a normed
space, for a smooth Lagrangian `f(v)` that does not depend on the position, the uniform motion
`(q, v) ↦ (v, 0)` is a Hamiltonian vector field of the energy for the Cartan two-form. No
regularity of `f` is needed. -/
theorem isHamiltonianVectorField_lagrangianEnergy_comp_snd
    (hL : ContMDiff 𝓘(ℝ, E).tangent 𝓘(ℝ, ℝ) ∞ fun v : TangentBundle 𝓘(ℝ, E) E ↦ f v.snd) :
    (cartanTwoForm _ hL).IsHamiltonianVectorField
      (lagrangianEnergy fun v : TangentBundle 𝓘(ℝ, E) E ↦ f v.snd)
      fun v ↦ ((v.snd, 0) : TangentSpace 𝓘(ℝ, E).tangent v) := by
  refine SmoothTwoForm.isHamiltonianVectorField_iff.2 fun v W ↦ ?_
  refine (eval₂_cartanTwoForm_comp_snd hL v _ W).trans ?_
  rw [mvfderiv_lagrangianEnergy_comp_snd hL]
  simp

variable [FiniteDimensional ℝ E]

/-- **Newton's equation on a normed space.** For a smooth Lagrangian `f(v) - V(q)` on a
finite-dimensional normed space whose kinetic part `f` has invertible second derivatives, the
Lagrangian vector field is `(q, v) ↦ (v, -D²f(v)⁻¹ DV(q))`, Newton's equation
`D²f(v) q'' = -DV(q)` written as a first-order system. -/
theorem hamiltonianVectorField_lagrangianEnergy_comp_snd_sub
    (hLV : ContMDiff 𝓘(ℝ, E).tangent 𝓘(ℝ, ℝ) ∞
      fun v : TangentBundle 𝓘(ℝ, E) E ↦ f v.snd - V v.proj)
    (hf : ∀ w, (fderiv ℝ (fderiv ℝ f) w).IsInvertible) (v : TangentBundle 𝓘(ℝ, E) E) :
    (cartanTwoForm _ hLV).hamiltonianVectorField
        (lagrangianEnergy fun v : TangentBundle 𝓘(ℝ, E) E ↦ f v.snd - V v.proj) v =
      ((v.snd, -(fderiv ℝ (fderiv ℝ f) v.snd).inverse (fderiv ℝ V v.proj)) :
        TangentSpace 𝓘(ℝ, E).tangent v) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  -- `f` is smooth: up to the constant `V 0`, it is `L` along the fibre of `TE` over `0`.
  have hf' : ContDiff ℝ ∞ f := by
    have h := (contMDiff_iff_contDiff.1
      (hLV.comp (contMDiff_tangentBundle_mk_constBase contMDiff_id 0))).add
      (contDiff_const (c := V 0))
    convert h using 1
    funext w
    simp
  have hL : ContMDiff 𝓘(ℝ, E).tangent 𝓘(ℝ, ℝ) ∞ fun v : TangentBundle 𝓘(ℝ, E) E ↦ f v.snd :=
    hf'.contMDiff.comp (contMDiff_snd_tangentBundle_modelSpace E 𝓘(ℝ, E))
  have hreg : IsRegularLagrangian fun v : TangentBundle 𝓘(ℝ, E) E ↦ f v.snd :=
    (isRegularLagrangian_comp_snd_iff f).2 hf
  have hX := (hreg.isSymplectic_cartanTwoForm hL).isNondegenerate.isHamiltonianVectorField_iff_eq.1
    (isHamiltonianVectorField_lagrangianEnergy_comp_snd hL)
  rw [hreg.hamiltonianVectorField_lagrangianEnergy_sub_comp_proj hL hLV, ← hX,
    potentialForce_def, fiberHessian_comp_snd]
  refine Prod.ext (add_zero _) ((zero_add _).trans ?_)
  rw [mvfderiv_eq_fderiv]
  rfl

end VectorSpace

end TauCeti
