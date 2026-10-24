/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.CliffordRestriction
public import TauCeti.Analysis.PDE.SeibergWitten.TracePairing

/-!
# The quadratic two-form of the Seiberg–Witten equations

Let `W⁺` be the positive half-spinors of a Hermitian Clifford module over an oriented real inner
product space `V` of dimension four, with `W⁺` of complex dimension two, and let
`C : iΛ⁺ ≃ {T : W⁺ → W⁺ | T* = T, tr T = 0}` be the Clifford isomorphism
(`TauCeti.SeibergWitten.cliffordRestrictionEquiv`) with adjoint `τ = C*`
(`TauCeti.SeibergWitten.cliffordRestrictionAdjoint`). The **quadratic two-form** of a positive
spinor `ψ` is the imaginary self-dual form
`q(ψ) = C⁻¹ Q₀(ψ) = τ(ψψ*) / 4`,
where `Q₀(ψ) = ψψ* - (‖ψ‖² / 2) Id` is `TauCeti.SeibergWitten.quadraticEnd`. The curvature
equation of the Seiberg–Witten equations reads `F_A⁺ = q(ψ) + η`. As for `C`, the imaginary form
`i q(ψ)` is indexed by a real self-dual form.

This file proves the pointwise algebra and calculus of `q` needed by the nonlinear analysis of the
equations, transporting those of `Q₀` through `C`. The map `q` is real-quadratic, so its
polarization `q'(ψ, φ) = τ(B(ψ, φ)) / 4`, with `B` the polarization of `Q₀`, and its derivative
are only real-linear.

## Main definitions

* `TauCeti.SeibergWitten.quadraticTwoForm o ρ hQ hkl ψ`: the self-dual form `q(ψ) = τ(Q₀(ψ)) / 4`.
* `TauCeti.SeibergWitten.quadraticTwoFormPolar o ρ hQ hkl`: its real polarization
  `q'(ψ, φ) = τ(B(ψ, φ)) / 4`, as a continuous real-bilinear map.

## Main results

* `quadraticTwoForm_eq_rankOne`: `q(ψ) = τ(ψψ*) / 4`.
* `cliffordRestriction_quadraticTwoForm`, `quadraticTwoForm_eq_symm_cliffordRestrictionEquiv`:
  `C(i q(ψ)) = Q₀(ψ)`, that is `q = C⁻¹ ∘ Q₀`.
* `cliffordRestriction_quadraticTwoForm_apply_self`: `C(i q(ψ)) ψ = (‖ψ‖² / 2) ψ`.
* `quadraticTwoForm_smul`, `quadraticTwoForm_smul_of_norm_eq_one`: `q(c ψ) = |c|² q(ψ)`; in
  particular `q` is invariant under unit phases.
* `norm_quadraticTwoForm`, `norm_quadraticTwoForm_sq`: `‖q(ψ)‖ = ‖ψ‖² / (2 √2)`, that is
  `‖q(ψ)‖² = ‖ψ‖⁴ / 8`; in particular `q(ψ) = 0` only for `ψ = 0`
  (`quadraticTwoForm_eq_zero_iff`).
* `cliffordRestriction_quadraticTwoFormPolar`: `C(i q'(ψ, φ)) = φψ* + ψφ* - Re⟪ψ, φ⟫ Id`.
* `quadraticTwoForm_add`: `q(ψ + φ) = q(ψ) + q(φ) + q'(ψ, φ)`.
* `quadraticTwoFormPolar_smul_self`: `q'(ψ, c ψ) = 2 Re(c) q(ψ)`, so the derivative of `q` kills
  the infinitesimal gauge directions `ξ ψ` with `ξ` imaginary.
* `norm_quadraticTwoFormPolar_le`: `‖q'(ψ, φ)‖ ≤ ‖ψ‖ ‖φ‖ / √2`.
* `norm_quadraticTwoForm_sub_le`: `q` is locally Lipschitz,
  `‖q(ψ) - q(φ)‖ ≤ ‖ψ - φ‖ (‖ψ‖ + ‖φ‖) / (2 √2)`.
* `hasFDerivAt_quadraticTwoForm`, `contDiff_quadraticTwoForm`: `q` is smooth, with real Fréchet
  derivative `q'(ψ, ·)` at `ψ`.

## References

* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §4.1.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module
open scoped RealInnerProductSpace InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4))
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
  (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

/-! ### The quadratic two-form -/

/-- **The quadratic two-form** `q(ψ) = C⁻¹ Q₀(ψ) = τ(ψψ*) / 4` of a positive spinor, indexed by
real self-dual forms: `C(i q(ψ)) = Q₀(ψ)`. -/
def quadraticTwoForm (ψ : positiveHalfSpinors o ρ) :
    Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 :=
  (4 : ℝ)⁻¹ • cliffordRestrictionAdjoint o ρ hQ hkl (quadraticEnd ψ)

/-- Unfolding lemma for `quadraticTwoForm`. -/
theorem quadraticTwoForm_def (ψ : positiveHalfSpinors o ρ) :
    quadraticTwoForm o ρ hQ hkl ψ =
      (4 : ℝ)⁻¹ • cliffordRestrictionAdjoint o ρ hQ hkl (quadraticEnd ψ) :=
  (rfl)

/-- `q(ψ) = τ(ψψ*) / 4`. -/
theorem quadraticTwoForm_eq_rankOne (ψ : positiveHalfSpinors o ρ) :
    quadraticTwoForm o ρ hQ hkl ψ =
      (4 : ℝ)⁻¹ • cliffordRestrictionAdjoint o ρ hQ hkl (InnerProductSpace.rankOne ℂ ψ ψ) := by
  simp [quadraticTwoForm_def, quadraticEnd_def, map_sub, ← ContinuousLinearMap.one_def]

variable {ρ} in
/-- `C(i q(ψ)) = Q₀(ψ)`. -/
theorem cliffordRestriction_quadraticTwoForm
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (ψ : positiveHalfSpinors o ρ) :
    cliffordRestriction o ρ hQ (quadraticTwoForm o ρ hQ hkl ψ) = quadraticEnd ψ := by
  rw [quadraticTwoForm_def, Submodule.coe_smul, map_smul,
    cliffordRestriction_cliffordRestrictionAdjoint_of_mem_traceFreeSelfAdjoint o hQ hρ hkl h₂
      (quadraticEnd_mem_traceFreeSelfAdjoint h₂ ψ), smul_smul]
  norm_num

variable {ρ} in
/-- `q = C⁻¹ ∘ Q₀`: `q(ψ)` is the self-dual form that the Clifford isomorphism sends to `Q₀(ψ)`. -/
theorem quadraticTwoForm_eq_symm_cliffordRestrictionEquiv
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (ψ : positiveHalfSpinors o ρ) :
    quadraticTwoForm o ρ hQ hkl ψ = (cliffordRestrictionEquiv o hQ hρ hkl h₂).symm
      ⟨quadraticEnd ψ, quadraticEnd_mem_traceFreeSelfAdjoint h₂ ψ⟩ := by
  rw [LinearEquiv.eq_symm_apply]
  exact Subtype.ext ((coe_cliffordRestrictionEquiv_apply o ρ hQ hρ hkl h₂ _).trans
    (cliffordRestriction_quadraticTwoForm o hQ hkl hρ h₂ ψ))

variable {ρ} in
/-- `C(i q(ψ)) ψ = (‖ψ‖² / 2) ψ`. -/
theorem cliffordRestriction_quadraticTwoForm_apply_self
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (ψ : positiveHalfSpinors o ρ) :
    cliffordRestriction o ρ hQ (quadraticTwoForm o ρ hQ hkl ψ) ψ = ((‖ψ‖ : ℂ) ^ 2 / 2) • ψ := by
  rw [cliffordRestriction_quadraticTwoForm o hQ hkl hρ h₂, quadraticEnd_apply_self]

/-- `q` is homogeneous of degree two for the real structure: `q(c ψ) = |c|² q(ψ)`. -/
theorem quadraticTwoForm_smul (c : ℂ) (ψ : positiveHalfSpinors o ρ) :
    quadraticTwoForm o ρ hQ hkl (c • ψ) = ‖c‖ ^ 2 • quadraticTwoForm o ρ hQ hkl ψ := by
  rw [quadraticTwoForm_def, quadraticTwoForm_def, quadraticEnd_smul, map_smul, smul_comm]

/-- `q` is invariant under unit phases: `q(u ψ) = q(ψ)` when `|u| = 1`. -/
theorem quadraticTwoForm_smul_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1)
    (ψ : positiveHalfSpinors o ρ) :
    quadraticTwoForm o ρ hQ hkl (u • ψ) = quadraticTwoForm o ρ hQ hkl ψ := by
  rw [quadraticTwoForm_smul, hu, one_pow, one_smul]

/-- `q(0) = 0`. -/
@[simp]
theorem quadraticTwoForm_zero : quadraticTwoForm o ρ hQ hkl 0 = 0 := by
  simp [quadraticTwoForm_def]

/-- `q(-ψ) = q(ψ)`. -/
@[simp]
theorem quadraticTwoForm_neg (ψ : positiveHalfSpinors o ρ) :
    quadraticTwoForm o ρ hQ hkl (-ψ) = quadraticTwoForm o ρ hQ hkl ψ := by
  simp [quadraticTwoForm_def]

variable {ρ} in
/-- The norm of the quadratic two-form: `‖q(ψ)‖ = ‖ψ‖² / (2 √2)`. -/
theorem norm_quadraticTwoForm (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (ψ : positiveHalfSpinors o ρ) :
    ‖quadraticTwoForm o ρ hQ hkl ψ‖ = ‖ψ‖ ^ 2 / (2 * √2) := by
  have : Nontrivial (positiveHalfSpinors o ρ) := Module.nontrivial_of_finrank_eq_succ h₂
  have h := norm_cliffordRestriction_coe o hQ hρ hkl (quadraticTwoForm o ρ hQ hkl ψ)
  rw [cliffordRestriction_quadraticTwoForm o hQ hkl hρ h₂, norm_quadraticEnd] at h
  rw [eq_div_iff (by positivity)]
  linarith

variable {ρ} in
/-- `‖q(ψ)‖² = ‖ψ‖⁴ / 8`. -/
theorem norm_quadraticTwoForm_sq (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (ψ : positiveHalfSpinors o ρ) :
    ‖quadraticTwoForm o ρ hQ hkl ψ‖ ^ 2 = ‖ψ‖ ^ 4 / 8 := by
  rw [norm_quadraticTwoForm o hQ hkl hρ h₂, div_pow, mul_pow, Real.sq_sqrt zero_le_two]
  ring

variable {ρ} in
/-- `q(ψ)` vanishes exactly when `ψ` does. -/
theorem quadraticTwoForm_eq_zero_iff (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) {ψ : positiveHalfSpinors o ρ} :
    quadraticTwoForm o ρ hQ hkl ψ = 0 ↔ ψ = 0 := by
  rw [← norm_eq_zero, norm_quadraticTwoForm o hQ hkl hρ h₂]
  simp

/-! ### Polarization and derivative -/

/-- The real-bilinear map `(ψ, φ) ↦ L (B(ψ, φ))`. It is stated for an arbitrary complex inner
product space because instance search does not find the real normed-space structure on the
endomorphisms of the submodule `W⁺`. -/
private def postcompQuadraticEndPolar {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : (E →L[ℂ] E) →L[ℝ] F) : E →L[ℝ] E →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ E _ F L).comp quadraticEndPolar

/-- The real polarization of `q`, `(ψ, φ) ↦ τ(B(ψ, φ)) / 4`, as a continuous real-bilinear map:
`C(i q'(ψ, φ)) = φψ* + ψφ* - Re⟪ψ, φ⟫ Id`. It is the real Fréchet derivative of `q` at `ψ`. -/
def quadraticTwoFormPolar :
    positiveHalfSpinors o ρ →L[ℝ] positiveHalfSpinors o ρ →L[ℝ]
      Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 :=
  postcompQuadraticEndPolar ((4 : ℝ)⁻¹ • cliffordRestrictionAdjoint o ρ hQ hkl)

/-- Unfolding lemma for `quadraticTwoFormPolar`: `q'(ψ, φ) = τ(B(ψ, φ)) / 4`. -/
theorem quadraticTwoFormPolar_apply (ψ φ : positiveHalfSpinors o ρ) :
    quadraticTwoFormPolar o ρ hQ hkl ψ φ =
      (4 : ℝ)⁻¹ • cliffordRestrictionAdjoint o ρ hQ hkl (quadraticEndPolar ψ φ) :=
  (rfl)

variable {ρ} in
/-- `C(i q'(ψ, φ)) = B(ψ, φ) = φψ* + ψφ* - Re⟪ψ, φ⟫ Id`. -/
theorem cliffordRestriction_quadraticTwoFormPolar
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (ψ φ : positiveHalfSpinors o ρ) :
    cliffordRestriction o ρ hQ (quadraticTwoFormPolar o ρ hQ hkl ψ φ) = quadraticEndPolar ψ φ := by
  rw [quadraticTwoFormPolar_apply, Submodule.coe_smul, map_smul,
    cliffordRestriction_cliffordRestrictionAdjoint_of_mem_traceFreeSelfAdjoint o hQ hρ hkl h₂
      (quadraticEndPolar_mem_traceFreeSelfAdjoint h₂ ψ φ), smul_smul]
  norm_num

/-- The polarization of `q` is symmetric. -/
theorem quadraticTwoFormPolar_comm (ψ φ : positiveHalfSpinors o ρ) :
    quadraticTwoFormPolar o ρ hQ hkl ψ φ = quadraticTwoFormPolar o ρ hQ hkl φ ψ := by
  rw [quadraticTwoFormPolar_apply, quadraticTwoFormPolar_apply, quadraticEndPolar_comm]

/-- The polarization of `q` restricts on the diagonal to `2 q`. -/
@[simp]
theorem quadraticTwoFormPolar_self (ψ : positiveHalfSpinors o ρ) :
    quadraticTwoFormPolar o ρ hQ hkl ψ ψ = (2 : ℝ) • quadraticTwoForm o ρ hQ hkl ψ := by
  rw [quadraticTwoFormPolar_apply, quadraticEndPolar_self, two_nsmul, ← two_smul ℝ, map_smul,
    quadraticTwoForm_def, smul_comm]

/-- Real polarization of `q`: `q(ψ + φ) = q(ψ) + q(φ) + q'(ψ, φ)`. -/
theorem quadraticTwoForm_add (ψ φ : positiveHalfSpinors o ρ) :
    quadraticTwoForm o ρ hQ hkl (ψ + φ) = quadraticTwoForm o ρ hQ hkl ψ +
      quadraticTwoForm o ρ hQ hkl φ + quadraticTwoFormPolar o ρ hQ hkl ψ φ := by
  rw [quadraticTwoForm_def, quadraticEnd_add, map_add, map_add, smul_add, smul_add,
    ← quadraticTwoForm_def, ← quadraticTwoForm_def, ← quadraticTwoFormPolar_apply]

/-- `q'(ψ, c ψ) = 2 Re(c) q(ψ)`. In particular the derivative of `q` vanishes along the
infinitesimal gauge directions `ξ ψ` with `ξ` imaginary. -/
theorem quadraticTwoFormPolar_smul_self (c : ℂ) (ψ : positiveHalfSpinors o ρ) :
    quadraticTwoFormPolar o ρ hQ hkl ψ (c • ψ) = (2 * c.re) • quadraticTwoForm o ρ hQ hkl ψ := by
  rw [quadraticTwoFormPolar_apply, quadraticEndPolar_smul_self, map_smul, quadraticTwoForm_def,
    smul_comm]

/-- `q'(ψ, i ψ) = 0`: the derivative of `q` vanishes along the infinitesimal phase direction. -/
@[simp]
theorem quadraticTwoFormPolar_I_smul_self (ψ : positiveHalfSpinors o ρ) :
    quadraticTwoFormPolar o ρ hQ hkl ψ (Complex.I • ψ) = 0 := by
  simp [quadraticTwoFormPolar_apply]

variable {ρ} in
/-- The polarization of `q` satisfies `‖q'(ψ, φ)‖ ≤ ‖ψ‖ ‖φ‖ / √2`. -/
theorem norm_quadraticTwoFormPolar_le (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (ψ φ : positiveHalfSpinors o ρ) :
    ‖quadraticTwoFormPolar o ρ hQ hkl ψ φ‖ ≤ ‖ψ‖ * ‖φ‖ / √2 := by
  have : Nontrivial (positiveHalfSpinors o ρ) := Module.nontrivial_of_finrank_eq_succ h₂
  have h := norm_cliffordRestriction_coe o hQ hρ hkl (quadraticTwoFormPolar o ρ hQ hkl ψ φ)
  rw [cliffordRestriction_quadraticTwoFormPolar o hQ hkl hρ h₂] at h
  rw [le_div_iff₀ (by positivity), mul_comm, ← h]
  exact norm_quadraticEndPolar_le ψ φ

/-- `q'(ψ - φ, ψ + φ) = 2 (q(ψ) - q(φ))`. -/
theorem quadraticTwoFormPolar_sub_add (ψ φ : positiveHalfSpinors o ρ) :
    quadraticTwoFormPolar o ρ hQ hkl (ψ - φ) (ψ + φ) =
      (2 : ℝ) • (quadraticTwoForm o ρ hQ hkl ψ - quadraticTwoForm o ρ hQ hkl φ) := by
  rw [map_sub, sub_apply, map_add, map_add, quadraticTwoFormPolar_self,
    quadraticTwoFormPolar_self, quadraticTwoFormPolar_comm o ρ hQ hkl φ ψ]
  module

variable {ρ} in
/-- `q` is locally Lipschitz: `‖q(ψ) - q(φ)‖ ≤ ‖ψ - φ‖ (‖ψ‖ + ‖φ‖) / (2 √2)`. -/
theorem norm_quadraticTwoForm_sub_le (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (ψ φ : positiveHalfSpinors o ρ) :
    ‖quadraticTwoForm o ρ hQ hkl ψ - quadraticTwoForm o ρ hQ hkl φ‖ ≤
      ‖ψ - φ‖ * (‖ψ‖ + ‖φ‖) / (2 * √2) := by
  have h := norm_quadraticTwoFormPolar_le o hQ hkl hρ h₂ (ψ - φ) (ψ + φ)
  rw [quadraticTwoFormPolar_sub_add, norm_smul, Real.norm_two, le_div_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (by positivity)]
  have := norm_add_le ψ φ
  have := norm_nonneg (ψ - φ)
  nlinarith

private theorem quadraticTwoForm_eq_comp :
    quadraticTwoForm o ρ hQ hkl =
      ((4 : ℝ)⁻¹ • cliffordRestrictionAdjoint o ρ hQ hkl) ∘ quadraticEnd := by
  ext1 ψ
  rw [quadraticTwoForm_def, Function.comp_apply, smul_apply]

private theorem quadraticTwoFormPolar_eq_comp (ψ : positiveHalfSpinors o ρ) :
    quadraticTwoFormPolar o ρ hQ hkl ψ =
      ((4 : ℝ)⁻¹ • cliffordRestrictionAdjoint o ρ hQ hkl).comp (quadraticEndPolar ψ) := by
  ext1 φ
  rw [quadraticTwoFormPolar_apply, ContinuousLinearMap.comp_apply,
    smul_apply]

/-- The real Fréchet derivative of `q` at `ψ` is `q'(ψ, ·)`; this holds in the strict sense. -/
theorem hasStrictFDerivAt_quadraticTwoForm (ψ : positiveHalfSpinors o ρ) :
    HasStrictFDerivAt (quadraticTwoForm o ρ hQ hkl) (quadraticTwoFormPolar o ρ hQ hkl ψ) ψ := by
  rw [quadraticTwoForm_eq_comp, quadraticTwoFormPolar_eq_comp]
  exact ((4 : ℝ)⁻¹ • cliffordRestrictionAdjoint o ρ hQ hkl).hasStrictFDerivAt.comp ψ
    (hasStrictFDerivAt_quadraticEnd ψ)

/-- The real Fréchet derivative of `q` at `ψ` is `q'(ψ, ·)`. -/
theorem hasFDerivAt_quadraticTwoForm (ψ : positiveHalfSpinors o ρ) :
    HasFDerivAt (quadraticTwoForm o ρ hQ hkl) (quadraticTwoFormPolar o ρ hQ hkl ψ) ψ :=
  (hasStrictFDerivAt_quadraticTwoForm o ρ hQ hkl ψ).hasFDerivAt

/-- The real Fréchet derivative of `q` at `ψ` is `q'(ψ, ·)`. -/
theorem fderiv_quadraticTwoForm (ψ : positiveHalfSpinors o ρ) :
    fderiv ℝ (quadraticTwoForm o ρ hQ hkl) ψ = quadraticTwoFormPolar o ρ hQ hkl ψ :=
  (hasFDerivAt_quadraticTwoForm o ρ hQ hkl ψ).fderiv

/-- `q` is a smooth map of the underlying real vector space. -/
theorem contDiff_quadraticTwoForm {n : WithTop ℕ∞} :
    ContDiff ℝ n (quadraticTwoForm o ρ hQ hkl) := by
  rw [quadraticTwoForm_eq_comp]
  exact ((4 : ℝ)⁻¹ • cliffordRestrictionAdjoint o ρ hQ hkl).contDiff.comp contDiff_quadraticEnd

end TauCeti.SeibergWitten
