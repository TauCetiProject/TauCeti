/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Related
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ContactType
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reeb
import TauCeti.Topology.FiberBundle.Separation

/-!
# The Reeb flow of the unit cosphere bundle is the cogeodesic flow

Let `M` be a Riemannian manifold without boundary, with cotangent bundle `T*M`, Liouville form
`λ = p dq` and canonical symplectic form `ω = -dλ`. The **kinetic energy** of a covector is
`K(q, p) = ‖p‖² / 2` (`TauCeti.CotangentBundle.kineticEnergy`), where `‖p‖` is the norm of `p` for
the metric. Its Hamiltonian vector field `X_K`, with `ι_(X_K) ω = dK`, generates the
**cogeodesic flow**: in canonical coordinates it reads `dq/dt = p♯`, `dp/dt = -∂_q K`.

The unit cosphere bundle `S*M = {‖p‖ = 1}` is the level `K = 1/2`. It carries the two contact
forms `α_g = λ|S*M` and `α_b = -λ|S*M`, which define opposite coorientations of the same contact
distribution. This file identifies their Reeb vector fields with the cogeodesic field:

* `R_(α_g) = X_K` along `S*M`
  (`TauCeti.CotangentBundle.mfderiv_coe_reebVectorField_cosphereBundle`), so the Reeb flow of
  `α_g` is the forward unit-speed cogeodesic flow
  (`TauCeti.CotangentBundle.coe_flowOf_reebVectorField_cosphereBundle`);
* `R_(α_b) = -R_(α_g) = -X_K` along `S*M`
  (`TauCeti.CotangentBundle.mfderiv_coe_reebVectorField_neg_cosphereBundle`).

The proof applies `TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_reebVectorField_mpullback` to
`θ = λ` and the energy `K`. Two facts about `K` enter. Its differential is `‖p‖ d‖p‖`
(`TauCeti.CotangentBundle.mvfderiv_kineticEnergy`), so on `S*M` its kernel is the tangent space of
`S*M`. And `K` is homogeneous of degree two in the fibres, so the Euler field `Z = p ∂_p` satisfies
`dK(Z) = 2K = ‖p‖²` (`TauCeti.CotangentBundle.mvfderiv_kineticEnergy_vectorBundleEulerField`).
Since `ι_Z ω = -λ`, this gives `λ(X_K) = ω(X_K, Z) = dK(Z) = ‖p‖²`
(`TauCeti.CotangentBundle.liouvilleForm_hamiltonianVectorField_kineticEnergy`), which is `1` on
`S*M`: the Reeb normalization `α_g(R) = 1` holds for `X_K` itself, with no rescaling.

## Main definitions

* `TauCeti.CotangentBundle.kineticEnergy`: the kinetic energy `‖p‖² / 2` of a covector.

## Main results

* `TauCeti.CotangentBundle.liouvilleForm_hamiltonianVectorField_kineticEnergy`: `λ(X_K) = ‖p‖²`.
* `TauCeti.CotangentBundle.mfderiv_coe_reebVectorField_cosphereBundle`: the Reeb field of
  `λ|S*M` is the cogeodesic field.
* `TauCeti.CotangentBundle.mfderiv_coe_reebVectorField_neg_cosphereBundle`: the Reeb field of
  `-λ|S*M` is its opposite.
* `TauCeti.CotangentBundle.coe_flowOf_reebVectorField_cosphereBundle`: the Reeb flow of `λ|S*M`
  is the cogeodesic flow.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (the unit cotangent bundle and the geodesic flow).
* G. P. Paternain, *Geodesic Flows*, Progress in Mathematics 180, Birkhäuser, 1999,
  Chapter 1 (the geodesic flow as a Hamiltonian flow on the cotangent bundle).
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- The **kinetic energy** `K(q, p) = ‖p‖² / 2` of a covector, for the norm of covectors induced
by the Riemannian metric. Its Hamiltonian flow for the canonical symplectic form is the cogeodesic
flow. -/
def kineticEnergy (z : CotangentBundle I M) : ℝ :=
  ‖z.2‖ ^ 2 / 2

@[simp]
theorem kineticEnergy_apply (z : CotangentBundle I M) : kineticEnergy I M z = ‖z.2‖ ^ 2 / 2 :=
  (rfl)

variable [FiniteDimensional ℝ E]

/-- **The kinetic energy is as smooth as the metric.** -/
theorem contMDiff_kineticEnergy {n : ℕ∞ω} [IsManifold I 1 M] [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)] :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) n (kineticEnergy I M) :=
  contMDiff_norm_snd_sq.div_const 2

section Differential

variable [IsManifold I 2 M] [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **The differential of the kinetic energy.** Off the zero section, `dK = ‖p‖ d‖p‖`. -/
theorem mvfderiv_kineticEnergy {z : CotangentBundle I M} (hz : z.2 ≠ 0) :
    mvfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (kineticEnergy I M) z =
      ‖z.2‖ • mvfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (fun z : CotangentBundle I M ↦ ‖z.2‖) z := by
  have : IsManifold I (1 + 1) M := by norm_num; infer_instance
  have hN : MDifferentiableAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ)
      (fun z : CotangentBundle I M ↦ ‖z.2‖) z :=
    (contMDiffAt_norm_snd (n := 1) hz).mdifferentiableAt one_ne_zero
  have hK : kineticEnergy I M = fun z ↦ (2 : ℝ)⁻¹ * (‖z.2‖ * ‖z.2‖) := by
    funext z
    rw [kineticEnergy_apply]
    ring
  rw [hK, mvfderiv_fun_mul (f := fun _ ↦ (2 : ℝ)⁻¹)
    (g := fun z : CotangentBundle I M ↦ ‖z.2‖ * ‖z.2‖) mdifferentiableAt_const (hN.mul hN),
    mvfderiv_fun_mul hN hN, mvfderiv_const]
  ext v
  simp only [add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, zero_apply]
  ring

/-- **Euler's identity for the kinetic energy.** The kinetic energy is homogeneous of degree two
in the fibres, so the Euler vector field `Z = p ∂_p` satisfies `dK(Z) = 2K = ‖p‖²`. -/
theorem mvfderiv_kineticEnergy_vectorBundleEulerField (z : CotangentBundle I M) :
    mvfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (kineticEnergy I M) z (vectorBundleEulerField I z) =
      ‖z.2‖ ^ 2 := by
  obtain ⟨q, p⟩ := z
  rcases eq_or_ne p 0 with rfl | hp
  · have h0 : ‖(0 : TangentSpace I q →L[ℝ] ℝ)‖ = 0 := (ContinuousLinearMap.opNorm_zero_iff _).2 rfl
    rw [vectorBundleEulerField_zero, map_zero, h0, sq, zero_mul]
  rw [mvfderiv_kineticEnergy hp, smul_apply,
    mvfderiv_apply_eq_mfderiv_apply, mfderiv_norm_snd_vectorBundleEulerField hp, smul_eq_mul, sq]

end Differential

section Liouville

variable [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **The Liouville form on the cogeodesic field.** The Liouville form takes the value
`λ(X_K) = ‖p‖² = 2K` on the Hamiltonian vector field of the kinetic energy: in coordinates,
`p(dq/dt) = p(p♯) = ‖p‖²`. -/
theorem liouvilleForm_hamiltonianVectorField_kineticEnergy (z : CotangentBundle I M) :
    (liouvilleForm I M).1 z ![(symplecticForm I M).hamiltonianVectorField (kineticEnergy I M) z] =
      ‖z.2‖ ^ 2 := by
  set X := (symplecticForm I M).hamiltonianVectorField (kineticEnergy I M) z
  -- Contract `ι_Z ω = -λ` with `X_K`, and use `ω(X_K, Z) = dK(Z)`.
  have h := congrArg (fun α ↦ α z ![X]) symplecticForm_interior_vectorBundleEulerField
  simp only [RoughForm.interior_apply, Pi.neg_apply, ContinuousAlternatingMap.neg_apply] at h
  rw [← SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_swap,
    isSymplectic_symplecticForm.isNondegenerate.eval₂_hamiltonianVectorField, neg_inj] at h
  rw [← h, mvfderiv_kineticEnergy_vectorBundleEulerField]

end Liouville

section Cosphere

variable [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless]

/-- **The Reeb field of `λ|S*M` is the cogeodesic field.** The differential of the inclusion of the
unit cosphere bundle sends the Reeb vector field of the contact form `α_g = λ|S*M` to the
Hamiltonian vector field of the kinetic energy. -/
theorem mfderiv_coe_reebVectorField_cosphereBundle (z : cosphereBundle I M) :
    mfderiv 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
        (Subtype.val : cosphereBundle I M → CotangentBundle I M) z
        ((SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
          (isSmoothEmbedding_coe_cosphereBundle (I := I) (M := M)).contMDiff
          (liouvilleForm I M)).reebVectorField z) =
      (symplecticForm I M).hamiltonianVectorField (kineticEnergy I M) z := by
  have hz : ‖z.1.2‖ = 1 := mem_cosphereBundle.1 z.2
  have hlam := liouvilleForm_hamiltonianVectorField_kineticEnergy (I := I) z.1
  rw [hz, one_pow] at hlam
  rw [isSymplectic_symplecticForm.isNondegenerate.mfderiv_reebVectorField_mpullback _
    isContactForm_mpullback_liouvilleForm_cosphereBundle ?_ ?_ (by rw [hlam]; exact one_ne_zero),
    hlam, inv_one, one_smul]
  · rw [symplecticForm_eq_neg_mextDeriv, Pi.neg_apply, neg_neg]
  · rw [range_mfderiv_coe_cosphereBundle, mvfderiv_kineticEnergy (snd_ne_zero_of_mem_cosphereBundle
      z.2), hz, one_smul]
    ext v
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, mvfderiv_apply_eq_mfderiv_apply]
    -- The tangent spaces of `ℝ` are `ℝ` itself.
    exact Iff.rfl

/-- **The Reeb field of `-λ|S*M` is the reversed cogeodesic field.** The differential of the
inclusion of the unit cosphere bundle sends the Reeb vector field of the contact form
`α_b = -λ|S*M` to minus the Hamiltonian vector field of the kinetic energy. -/
theorem mfderiv_coe_reebVectorField_neg_cosphereBundle (z : cosphereBundle I M) :
    mfderiv 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
        (Subtype.val : cosphereBundle I M → CotangentBundle I M) z
        ((SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
          (isSmoothEmbedding_coe_cosphereBundle (I := I) (M := M)).contMDiff
          (-liouvilleForm I M)).reebVectorField z) =
      -(symplecticForm I M).hamiltonianVectorField (kineticEnergy I M) z := by
  rw [map_neg, isContactForm_mpullback_liouvilleForm_cosphereBundle.reebVectorField_neg, map_neg,
    mfderiv_coe_reebVectorField_cosphereBundle]

/-- **The Reeb flow of `λ|S*M` is the cogeodesic flow.** Wherever the Reeb flow of the contact
form `α_g = λ|S*M` is defined, the inclusion of the unit cosphere bundle carries it to the
Hamiltonian flow of the kinetic energy. -/
theorem coe_flowOf_reebVectorField_cosphereBundle [T2Space M] {t : ℝ} {z : cosphereBundle I M}
    (ht : (t, z) ∈ flowDomain ((SmoothForm.mpullback
      (Subtype.val : cosphereBundle I M → CotangentBundle I M)
      (isSmoothEmbedding_coe_cosphereBundle (I := I) (M := M)).contMDiff
      (liouvilleForm I M)).reebVectorField)) :
    (flowOf ((SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
        (isSmoothEmbedding_coe_cosphereBundle (I := I) (M := M)).contMDiff
        (liouvilleForm I M)).reebVectorField) t z).1 =
      flowOf ((symplecticForm I M).hamiltonianVectorField (kineticEnergy I M)) t z.1 := by
  have : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  exact isSmoothEmbedding_coe_cosphereBundle.contMDiff.mdifferentiable (by simp)
    |>.apply_flowOf
      (isSymplectic_symplecticForm.isNondegenerate.contMDiff_hamiltonianVectorField (n := 1)
        (by simp) ((contMDiff_kineticEnergy (n := ∞)).of_le (by simp)))
      mfderiv_coe_reebVectorField_cosphereBundle ht

end Cosphere

end CotangentBundle

end TauCeti
