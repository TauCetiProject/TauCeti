/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Diffeomorph
public import TauCeti.Geometry.Symplectic.Lagrangian.Constructions
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Real polarizations

A **real polarization** of a symplectic manifold `(M, σ)` is a smooth distribution `P ⊆ TM`
which is Lagrangian in every tangent space, `P_x^σ = P_x`, and involutive: the Lie bracket of two
local vector fields tangent to `P` is again tangent to `P`. By the Frobenius theorem it is the
tangent distribution of a foliation of `M` by Lagrangian submanifolds. Real polarizations are the
choice of "half of the variables" of geometric quantization: the polarized sections of a
prequantum line are those that are covariantly constant along `P`, and the observables that can be
quantized on them are those whose Hamiltonian flows preserve `P`
(`TauCeti.Geometry.Symplectic.Polarization.Observable`).

The distribution is recorded, as in `TauCeti.IsContMDiffDistribution`, as a family of subspaces
`P : Π x, Submodule ℝ (T_x M)`, and the three conditions are bundled in the predicate
`TauCeti.SmoothTwoForm.IsNondegenerate.IsRealPolarization`.

## Main definitions

* `TauCeti.SmoothTwoForm.IsNondegenerate.IsRealPolarization hσ P`: `P` is a real polarization of
  the nondegenerate two-form `σ`.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.IsRealPolarization.two_mul_finrank`: a real polarization
  has half the rank of the tangent bundle.
* `TauCeti.SmoothTwoForm.IsNondegenerate.IsRealPolarization.eval₂_eq_zero`: `σ` vanishes on pairs of
  vectors of `P`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.IsRealPolarization.comap_mfderiv`: the pullback of a real
  polarization by a symplectomorphism is a real polarization.
* `TauCeti.SymplecticForm.isRealPolarization_const`: on a finite-dimensional symplectic vector
  space, a Lagrangian subspace taken at every point is a real polarization of the constant form.
  For `ℝ²` with `ω = dq ∧ dp` and the line of the `p`-axis this is the vertical polarization of
  `T*ℝ`.

## References

* M. Schottenloher, *Geometric Quantization*, lecture notes, version 15.6, Definition 9.8.
* N. M. J. Woodhouse, *Geometric Quantization*, 2nd ed., Oxford, 1992, Section 5.4.
-/

public section

open Module
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

namespace IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate)

/-- A **real polarization** of a nondegenerate two-form `σ` is a smooth distribution `P` of
constant rank which is Lagrangian for `σ` at every point and involutive. -/
structure IsRealPolarization (P : Π x : M, Submodule ℝ (TangentSpace I x)) : Prop where
  /-- Each fibre of a real polarization is a Lagrangian subspace of the tangent space. -/
  isLagrangian (x : M) : (hσ.symplecticFormAt x).IsLagrangian (P x)
  /-- A real polarization is a smooth distribution of some constant rank. -/
  exists_isContMDiffDistribution : ∃ k, IsContMDiffDistribution I ∞ k P
  /-- A real polarization is involutive. -/
  isInvolutive : IsInvolutiveDistribution I P

namespace IsRealPolarization

variable {hσ} {P : Π x : M, Submodule ℝ (TangentSpace I x)} (hP : hσ.IsRealPolarization P)
include hP

/-- `σ` vanishes on pairs of vectors of a real polarization. -/
theorem eval₂_eq_zero {x : M} {v w : TangentSpace I x} (hv : v ∈ P x) (hw : w ∈ P x) :
    SmoothBundleForm.eval₂ σ x v w = 0 := by
  rw [← symplecticFormAt_apply hσ]
  exact (hP.isLagrangian x).symplecticForm_apply_eq_zero hv hw

/-- Each fibre of a real polarization is coisotropic. -/
theorem isCoisotropic (x : M) : (hσ.symplecticFormAt x).IsCoisotropic (P x) :=
  (hP.isLagrangian x).isCoisotropic

/-- A real polarization has half the rank of the tangent bundle: `2 dim P_x = dim M`. -/
theorem two_mul_finrank [FiniteDimensional ℝ E] (x : M) :
    2 * finrank ℝ (P x) = finrank ℝ E :=
  (hP.isLagrangian x).two_mul_finrank

/-- A real polarization of a finite-dimensional manifold is a smooth distribution of rank half the
dimension. -/
theorem isContMDiffDistribution [FiniteDimensional ℝ E] :
    IsContMDiffDistribution I ∞ (finrank ℝ E / 2) P := by
  obtain ⟨k, hk⟩ := hP.exists_isContMDiffDistribution
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x⟩⟩
  · exact isContMDiffDistribution_iff.2 fun x ↦ isEmptyElim x
  · have h2 := hP.two_mul_finrank x
    rw [hk.finrank_eq x] at h2
    rwa [← h2, Nat.mul_div_cancel_left k two_pos]

end IsRealPolarization

section Transport

variable {E₂ H₂ M₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  {σ₂ : SmoothTwoForm I₂ M₂} {hσ₂ : σ₂.IsNondegenerate}

/-- **Pullback of a real polarization by a symplectomorphism.** If a diffeomorphism `ψ` pulls `σ₂`
back to `σ` and `P₂` is a real polarization of `σ₂`, then the pulled-back distribution
`x ↦ dψ_x⁻¹(P₂ (ψ x))` is a real polarization of `σ`. -/
theorem IsRealPolarization.comap_mfderiv [CompleteSpace E] [CompleteSpace E₂]
    {P₂ : Π y : M₂, Submodule ℝ (TangentSpace I₂ y)} (hP₂ : hσ₂.IsRealPolarization P₂)
    (ψ : M ≃ₘ⟮I, I₂⟯ M₂) (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ) :
    hσ.IsRealPolarization fun x ↦ (P₂ (ψ x)).comap (mfderiv I I₂ ψ x).toLinearMap where
  isLagrangian x := by
    set e := (ψ.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
    -- The differential of `ψ` at `x` is the linear equivalence `e`, so pulling back along it and
    -- pushing forward again recovers `P₂ (ψ x)`.
    have he : (mfderiv I I₂ ψ x).toLinearMap = e.toLinearMap :=
      (congrArg ContinuousLinearMap.toLinearMap
        (ψ.mfderivToContinuousLinearEquiv_coe (by simp) (x := x))).symm
    rw [← SymplecticForm.isLagrangian_map_transport_iff (e := e), he,
      Submodule.map_comap_eq_of_surjective e.surjective, hσ.symplecticFormAt_transport ψ hψ x]
    exact hP₂.isLagrangian (ψ x)
  exists_isContMDiffDistribution :=
    let ⟨k, hk⟩ := hP₂.exists_isContMDiffDistribution
    ⟨k, hk.comap_mfderiv ψ.isLocalDiffeomorph (by simp)⟩
  isInvolutive := by
    have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
    have : IsManifold I₂ (minSmoothness ℝ 2) M₂ := IsManifold.of_le (n := ∞) (by simp)
    exact (ψ.isInvolutiveDistribution_comap_mfderiv_iff (by simp) P₂).2 hP₂.isInvolutive

end Transport

end IsNondegenerate

end SmoothTwoForm

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The linear model of a real polarization.** On a finite-dimensional symplectic vector space
`(V, ω₀)`, a Lagrangian subspace `L`, taken at every point, is a real polarization of the constant
symplectic form. -/
theorem isRealPolarization_const {ω₀ : SymplecticForm V} {L : Submodule ℝ V}
    (hL : ω₀.IsLagrangian L) :
    (isNondegenerate_constSmooth ω₀).IsRealPolarization (fun _ : V ↦ L) where
  isLagrangian x := by rwa [isNondegenerate_constSmooth_symplecticFormAt]
  exists_isContMDiffDistribution := ⟨_, isContMDiffDistribution_const L⟩
  isInvolutive := isInvolutiveDistribution_const L.isClosed_of_finiteDimensional

end SymplecticForm

end TauCeti
