/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Periodic
public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import TauCeti.Geometry.Symplectic.Hamiltonian.CommutingFlow
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# Untwisting Floer cylinders by the Hamiltonian flow

Let `σ` be a two-form on a finite-dimensional boundaryless manifold `M`, `H : ℝ → M → ℝ` a
time-dependent Hamiltonian with Hamiltonian vector fields `X_H(t) = X_{H t}`,
`ι_{X_{H t}} σ = d(H t)`, and `φ_t = timeDependentFlowOf X_H s t` its time-dependent flow from a
fixed initial time `s`, assumed defined for all times. For a map `v : ℝ × ℝ → M` put

`w(s', t) = φ_t (v(s', t))`.

Moving `v` by the flow turns the unperturbed derivative of `v` into the Hamiltonian-perturbed
derivative of `w`: `∂_{s'} w = dφ_t (∂_{s'} v)` and `∂_t w - X_{H t}(w) = dφ_t (∂_t v)`, that is,
`dw - X_H dt = dφ_t ∘ dv`
(`TauCeti.SmoothTwoForm.perturbedMFDeriv_timeDependentFlowOf`). Consequently:

* **Floer's equation.** `w` solves `∂_{s'} w + J_t (∂_t w - X_{H t}(w)) = 0` exactly when `v` solves
  the unperturbed equation `∂_{s'} v + J'_t ∂_t v = 0`, where `J'_t = (dφ_t)⁻¹ J_t dφ_t` is `J_t`
  carried back along the differential of the flow
  (`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_timeDependentFlowOf_iff`).
* **Symplectic data.** If `σ` is symplectic, every differential `dφ_t` is a linear
  symplectomorphism
  (`TauCeti.SmoothTwoForm.IsSymplectic.isSymplectomorphism_timeDependentFlowMFDerivEquiv`), so
  `J'_t` is tamed by, or compatible with, `σ` whenever `J_t` is
  (`TauCeti.SmoothTwoForm.IsSymplectic.tames_transport_timeDependentFlowMFDerivEquiv_symm` and
  `TauCeti.SmoothTwoForm.IsSymplectic.compatible_transport_timeDependentFlowMFDerivEquiv_symm`),
  and the Floer energy density of `w` is the symplectic area density `σ(∂_{s'} v, ∂_t v)` of `v`
  (`TauCeti.SmoothTwoForm.IsSymplectic.floerEnergyDensity_timeDependentFlowOf`).
* **Seam and periodicity.** If `H` is `1`-periodic in time, `φ_{t+1} = φ_t ∘ ψ` for the return map
  `ψ = φ_{s+1}`, so `w` is `1`-periodic in `t` exactly when `v` satisfies the seam condition
  `v(s', t + 1) = ψ⁻¹(v(s', t))`
  (`TauCeti.SmoothTwoForm.forall_timeDependentFlowOf_add_one_eq_iff`).

So Floer cylinders of `H`, which are `1`-periodic in `t`, correspond to solutions of the
unperturbed Cauchy–Riemann equation for the twisted structures `J'_t` with the `ψ⁻¹` seam. This is
the dictionary between Floer cylinders of the Hamiltonian `H` and of the symplectomorphism
`ψ = φ_H^1`, under which the `1`-periodic orbits of `H` correspond to the fixed points of `ψ`
(`TauCeti.periodicSolutionsEquivFixedPoints`), which are the constant maps `v` with the seam
condition.

These are pointwise statements about classical maps; no completion, compactness or transversality
is involved.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. 120 (1989),
  575–611.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1.
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H' M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'} [TopologicalSpace M] [ChartedSpace H' M]
  [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M] {σ : SmoothTwoForm I M}
  {H : ℝ → M → ℝ}

section Equation

variable (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
    (fun p : ℝ × M ↦ (⟨p.2, σ.hamiltonianVectorField (H p.1) p.2⟩ : TangentBundle I M)))
  (hc : IsCompleteVectorField
    (timeDependentSuspensionField fun t ↦ σ.hamiltonianVectorField (H t)))
include hX hc

/-- **Untwisting the perturbed derivative.** Moving a differentiable map `v : ℝ × ℝ → M` by the
time-dependent Hamiltonian flow, `w(s', t) = φ_t (v(s', t))` with `φ_t = φ_{s, t}`, turns its
derivative into the Hamiltonian-perturbed derivative of `w` for the cylindrical perturbation
`K = H_t dt`: `dw - X_{H t} dt = dφ_t ∘ dv`. -/
theorem perturbedMFDeriv_timeDependentFlowOf (s : ℝ) {v : ℝ × ℝ → M} {z : ℝ × ℝ}
    (hv : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I v z) :
    σ.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (fun w ↦ timeDependentFlowOf (fun t ↦ σ.hamiltonianVectorField (H t)) s w.2 (v w)) z =
      mfderiv I I (timeDependentFlowOf (fun t ↦ σ.hamiltonianVectorField (H t)) s z.2) (v z) ∘L
        mfderiv 𝓘(ℝ, ℝ × ℝ) I v z := by
  have hτ : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) Prod.snd z (ContinuousLinearMap.snd ℝ ℝ ℝ) :=
    hasMFDerivAt_iff_hasFDerivAt.2 (hasFDerivAt_snd)
  have hw := hasMFDerivAt_timeDependentFlowOf_comp hc le_rfl hX hτ hv.hasMFDerivAt s
  refine ContinuousLinearMap.ext fun a ↦ ?_
  rw [perturbedMFDeriv_apply, hw.mfderiv]
  simp only [hamiltonianVectorField_const, Pi.zero_apply, smul_zero, sub_zero]
  -- The value of the sum of maps at `a` is the sum of the values, and `snd a = a.2`.
  exact add_sub_cancel_right _ _

/-- **Untwisting Floer's equation.** For a map `v : ℝ × ℝ → M` differentiable at `z` and
`w(s', t) = φ_t (v(s', t))` as in `TauCeti.SmoothTwoForm.perturbedMFDeriv_timeDependentFlowOf`, `w`
solves Floer's equation `∂_{s'} w + J (∂_t w - X_{H t}(w)) = 0` at `z` exactly when `v` solves the
unperturbed equation `∂_{s'} v + J' ∂_t v = 0` there, for the structure `J' = (dφ_t)⁻¹ J dφ_t`
carried back along the differential of the flow. -/
theorem isComplexLinearMap_perturbedMFDeriv_timeDependentFlowOf_iff (s : ℝ) {v : ℝ × ℝ → M}
    {z : ℝ × ℝ} (hv : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I v z)
    (J : AlmostComplexStructure (TangentSpace I
      (timeDependentFlowOf (fun t ↦ σ.hamiltonianVectorField (H t)) s z.2 (v z)))) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (σ.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
          (fun w ↦ timeDependentFlowOf (fun t ↦ σ.hamiltonianVectorField (H t)) s w.2 (v w))
          z).toLinearMap ↔
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J.transport (timeDependentFlowMFDerivEquiv hc le_rfl hX s z.2 (v z)).toLinearEquiv.symm)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I v z : ℝ × ℝ →L[ℝ] TangentSpace I (v z)).toLinearMap := by
  refine (Iff.of_eq (congrArg (IsComplexLinearMap _ J) (LinearMap.ext fun a ↦ ?_))).trans
    (isComplexLinearMap_transport_symm_iff
      (timeDependentFlowMFDerivEquiv hc le_rfl hX s z.2 (v z)).toLinearEquiv).symm
  -- Both sides apply `dφ_t` to `dv a`, once as a continuous linear map and once through the
  -- linear equivalence underlying it.
  exact (DFunLike.congr_fun (perturbedMFDeriv_timeDependentFlowOf hX hc s hv) a).trans
    (timeDependentFlowMFDerivEquiv_apply hc le_rfl hX s z.2 (v z) _).symm

/-- **The seam condition.** If `H` is `1`-periodic in time, the map `w(s', t) = φ_t (v(s', t))`,
with `φ_t = φ_{s, t}`, is `1`-periodic in `t` exactly when `v` satisfies the seam condition
`v(s', t + 1) = ψ⁻¹ (v(s', t))` for the return map `ψ = φ_{s, s + 1}`, whose inverse is the flow
`φ_{s + 1, s}`. -/
theorem forall_timeDependentFlowOf_add_one_eq_iff (hP : Periodic H 1) (s : ℝ)
    (v : ℝ × ℝ → M) :
    (∀ z : ℝ × ℝ, timeDependentFlowOf (fun t ↦ σ.hamiltonianVectorField (H t)) s (z.2 + 1)
        (v (z.1, z.2 + 1)) =
      timeDependentFlowOf (fun t ↦ σ.hamiltonianVectorField (H t)) s z.2 (v z)) ↔
      ∀ z : ℝ × ℝ, v (z.1, z.2 + 1) =
        timeDependentFlowOf (fun t ↦ σ.hamiltonianVectorField (H t)) (s + 1) s (v z) :=
  forall_congr' fun z ↦ timeDependentFlowOf_add_period_eq_iff hX hc
    (fun t ↦ by simp only [hP t]) s z.2 (v z) (v (z.1, z.2 + 1))

end Equation

namespace IsSymplectic

variable [I.Boundaryless] (hσ : σ.IsSymplectic) (hH : ∀ t, ContMDiff I 𝓘(ℝ) 2 (H t))
  (hc : IsCompleteVectorField
    (timeDependentSuspensionField fun t ↦ σ.hamiltonianVectorField (H t)))
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
    (fun p : ℝ × M ↦ (⟨p.2, σ.hamiltonianVectorField (H p.1) p.2⟩ : TangentBundle I M)))
include hσ hH hc hX

/-- **The linearized Hamiltonian flow is symplectic.** For a symplectic form `σ` and a jointly
`C²` field of Hamiltonian vector fields with complete suspension, every differential
`dφ_{s, t}(x) : T_x M → T_{φ_{s, t} x} M` of the time-dependent flow is a linear
symplectomorphism. -/
theorem isSymplectomorphism_timeDependentFlowMFDerivEquiv (s t : ℝ) (x : M) :
    SymplecticForm.IsSymplectomorphism (hσ.isNondegenerate.symplecticFormAt x)
      (hσ.isNondegenerate.symplecticFormAt
        (timeDependentFlowOf (fun t ↦ σ.hamiltonianVectorField (H t)) s t x))
      (timeDependentFlowMFDerivEquiv hc le_rfl (hX.of_le one_le_two) s t x).toLinearEquiv := by
  refine SymplecticForm.isSymplectomorphism_iff.2 fun a b ↦ ?_
  have h := congrArg (fun α ↦ α x ![a, b])
    (mpullback_timeDependentFlowOf_of_isHamiltonianVectorField
      (fun t ↦ hσ.isNondegenerate.isHamiltonianVectorField_hamiltonianVectorField (H t))
      hσ.isClosed hH hc hX s t)
  simp only [mpullback_apply] at h
  simp only [IsNondegenerate.symplecticFormAt_apply, SmoothBundleForm.eval₂_apply]
  convert h using 2
  ext i
  fin_cases i <;> simp

/-- **Twisted structures stay tame.** For a symplectic form `σ`, if `σ` tames a structure `J` at
`φ_{s, t} x`, it tames the structure `J' = (dφ_{s, t})⁻¹ J dφ_{s, t}` carried back to `x` along the
linearized flow. -/
theorem tames_transport_timeDependentFlowMFDerivEquiv_symm (s t : ℝ) (x : M)
    {J : AlmostComplexStructure (TangentSpace I
      (timeDependentFlowOf (fun t ↦ σ.hamiltonianVectorField (H t)) s t x))}
    (hJ : (hσ.isNondegenerate.symplecticFormAt _).Tames J) :
    (hσ.isNondegenerate.symplecticFormAt x).Tames (J.transport
      (timeDependentFlowMFDerivEquiv hc le_rfl (hX.of_le one_le_two) s t x).toLinearEquiv.symm) :=
  SymplecticForm.isSymplectomorphism_iff_transport_eq.1
    (hσ.isSymplectomorphism_timeDependentFlowMFDerivEquiv hH hc hX s t x).symm ▸ hJ.transport _

/-- **Twisted structures stay compatible.** For a symplectic form `σ`, if `J` is compatible with
`σ` at `φ_{s, t} x`, so is the structure `J' = (dφ_{s, t})⁻¹ J dφ_{s, t}` carried back to `x` along
the linearized flow. -/
theorem compatible_transport_timeDependentFlowMFDerivEquiv_symm (s t : ℝ) (x : M)
    {J : AlmostComplexStructure (TangentSpace I
      (timeDependentFlowOf (fun t ↦ σ.hamiltonianVectorField (H t)) s t x))}
    (hJ : (hσ.isNondegenerate.symplecticFormAt _).Compatible J) :
    (hσ.isNondegenerate.symplecticFormAt x).Compatible (J.transport
      (timeDependentFlowMFDerivEquiv hc le_rfl (hX.of_le one_le_two) s t x).toLinearEquiv.symm) :=
  SymplecticForm.isSymplectomorphism_iff_transport_eq.1
    (hσ.isSymplectomorphism_timeDependentFlowMFDerivEquiv hH hc hX s t x).symm ▸ hJ.transport _

/-- **Energy of an untwisted cylinder.** For a symplectic form `σ` and `w(s', t) = φ_t (v(s', t))`
as in `TauCeti.SmoothTwoForm.perturbedMFDeriv_timeDependentFlowOf`, the Floer energy density of
`w` for the perturbation `K = H_t dt` is the symplectic area density `σ(∂_{s'} v, ∂_t v)` of `v`. -/
theorem floerEnergyDensity_timeDependentFlowOf (s : ℝ) {v : ℝ × ℝ → M} {z : ℝ × ℝ}
    (hv : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I v z) :
    σ.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (fun w ↦ timeDependentFlowOf (fun t ↦ σ.hamiltonianVectorField (H t)) s w.2 (v w)) z =
      SmoothBundleForm.eval₂ σ (v z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I v z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I v z stdComplexLineImag) := by
  have h := (hσ.isSymplectomorphism_timeDependentFlowMFDerivEquiv hH hc hX s z.2 (v z)).apply
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I v z stdComplexLineReal) (mfderiv 𝓘(ℝ, ℝ × ℝ) I v z stdComplexLineImag)
  simp only [IsNondegenerate.symplecticFormAt_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
    timeDependentFlowMFDerivEquiv_apply] at h
  rw [floerEnergyDensity_def, perturbedMFDeriv_timeDependentFlowOf (hX.of_le one_le_two) hc s hv]
  exact h

end IsSymplectic

end TauCeti.SmoothTwoForm
