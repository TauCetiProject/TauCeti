/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Spectrum.Operator.Mixed
import TauCeti.Analysis.InnerProductSpace.Variational.Rayleigh
import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov

/-!
# The mixed Laplacian under a Poincaré–Friedrichs inequality

Let `Ω ⊆ ℝⁿ` be open, let `Γ` be a set disjoint from `Ω`, typically a part of its boundary, and
let `-Δ_Γ` be the mixed Laplacian, the realization
`TauCeti.PDE.mixedOperator (memLp_energyIntegrand_const_zero_zero 1) Γ` on `L²(Ω)` of `-Δ` with
the Dirichlet condition on `Γ` and the Neumann condition on the rest of the boundary. This file
studies `-Δ_Γ` when `H¹_Γ(Ω)` satisfies a **Poincaré–Friedrichs inequality**

`‖u‖_{L²(Ω)} ≤ P ‖∇u‖_{L²(Ω)}` for every `u ∈ H¹_Γ(Ω)`.

Then the energy form `∫_Ω ∇u · ∇v` is coercive on `H¹_Γ(Ω)` with no shift
(`TauCeti.PDE.isCoercive_mixedForm_laplacian_of_poincare`), and:

* every `κ` with `κ P² < 1`, in particular `κ = 0`, is a resolvent point of `-Δ_Γ`
  (`TauCeti.PDE.mem_resolventSet_mixedOperator_laplacian_of_poincare`), so `-Δ_Γ` is invertible;
  its inverse `-R(0)` is the solution operator of the mixed problem `-Δu = f`
  (`TauCeti.PDE.resolvent_mixedOperator_laplacian_zero_of_poincare`). This inverse is self-adjoint
  by `IsSelfAdjoint.isSelfAdjoint_resolvent` applied to
  `TauCeti.PDE.isSelfAdjoint_mixedOperator_laplacian`, and it is compact when `Ω` has the Rellich
  property that the value map `H¹(Ω) → L²(Ω)` is compact, by
  `LinearPMap.HasCompactResolvent.isCompactOperator_resolvent` applied to
  `TauCeti.PDE.hasCompactResolvent_mixedOperator_laplacian`;
* on a nonempty `Ω`, `λ₁ = ‖R(0)‖⁻¹ = ‖(-Δ_Γ)⁻¹‖⁻¹` is positive, it is the greatest `C` with
  `C ‖u‖² ≤ ‖∇u‖²` on `H¹_Γ(Ω)`, and `√‖R(0)‖ = λ₁^{-1/2}` is the **optimal Poincaré–Friedrichs
  constant**, the least `P` for which the inequality holds
  (`TauCeti.PDE.isLeast_sqrt_norm_resolvent_mixedOperator_laplacian_zero_of_poincare`);
* under the Rellich property `λ₁` is the least point of the spectrum of `-Δ_Γ`
  (`TauCeti.PDE.isLeast_spectrum_mixedOperator_laplacian_of_poincare`), so the first mixed
  eigenvalue is the reciprocal of the square of the optimal Poincaré–Friedrichs constant.

On a bounded connected Lipschitz domain every hypothesis holds as soon as `Γ` meets the frontier
in a set of positive surface measure: the Poincaré–Friedrichs inequality is
`W1p.exists_norm_value_le_mul_norm_gradient_of_mem_w1pVanishingOnSubmodule_of_affineIsometryEquiv`
and the Rellich property is
`W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_of_affineIsometryEquiv`, both in the
namespace `TauCeti`. The last section records the resulting statements, for an open set carried
onto a Lipschitz domain of the model space `ℝ × E` by an affine isometry. For `Γ = ∂Ω` the mixed
Laplacian is the Dirichlet Laplacian (`TauCeti.PDE.mixedOperator_frontier`). Some condition on `Γ`
is needed: for `Γ = ∅` on a domain of finite measure the constants lie in `H¹_Γ(Ω)` with zero
gradient, so no Poincaré–Friedrichs inequality holds and `0` is an eigenvalue of `-Δ_Γ`.

## Main declarations

* `TauCeti.PDE.isCoercive_mixedForm_laplacian_of_poincare`: the energy form of `-Δ` is coercive
  on `H¹_Γ(Ω)`.
* `TauCeti.PDE.mem_resolventSet_mixedOperator_laplacian_of_poincare`,
  `TauCeti.PDE.zero_mem_resolventSet_mixedOperator_laplacian_of_poincare` and
  `TauCeti.PDE.resolvent_mixedOperator_laplacian_zero_of_poincare`: the spectrum lies in
  `[P⁻², ∞)`, and the inverse of `-Δ_Γ` is the mixed solution operator.
* `TauCeti.PDE.one_le_mul_sq_of_mem_spectrum_mixedOperator_laplacian` and
  `TauCeti.PDE.pos_of_mem_spectrum_mixedOperator_laplacian_of_poincare`: every spectral value `κ`
  has `1 ≤ κ P²`, so it is positive.
* `TauCeti.PDE.isLeast_inv_sqrt_of_isLeast_spectrum_mixedOperator_laplacian`: under the Rellich
  property, a positive least spectral value `λ₁` gives the optimal Poincaré–Friedrichs constant
  `λ₁^{-1/2}`, by the Rayleigh principle
  `TauCeti.PDE.isGreatest_of_isLeast_spectrum_mixedOperator_laplacian`.
* `TauCeti.PDE.isGreatest_inv_norm_resolvent_mixedOperator_laplacian_zero_of_poincare`,
  `TauCeti.PDE.isLeast_sqrt_norm_resolvent_mixedOperator_laplacian_zero_of_poincare` and
  `TauCeti.PDE.isLeast_spectrum_mixedOperator_laplacian_of_poincare`: `λ₁ = ‖R(0)‖⁻¹` is the
  optimal Poincaré constant, the reciprocal square of the optimal Poincaré–Friedrichs constant and
  the least spectral value.
* (in the namespace `TauCeti.PDE`)
  `exists_isLeast_poincare_and_isLeast_spectrum_mixedOperator_laplacian_of_isLipschitzDomainWith`:
  the first mixed eigenvalue on Lipschitz domains. The invertibility there is
  `TauCeti.PDE.zero_mem_resolventSet_mixedOperator_laplacian_of_isLipschitzDomainWith`, in
  `TauCeti/Analysis/PDE/Spectrum/Operator/Mixed.lean`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 9.31 and its proof (the Dirichlet case, whose argument carries over to `H¹_Γ(Ω)`).
* S. Bauer, D. Pauly, M. Schomburg, *The Maxwell compactness property in bounded weak Lipschitz
  domains with mixed boundary conditions*, SIAM J. Math. Anal. 48 (2016), Theorem 4.8 (the
  Poincaré–Friedrichs inequality on `H¹_Γ(Ω)`).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Module Set TopologicalSpace
open scoped NNReal InnerProductSpace

attribute [local instance] W1pVanishingOn.instNormedAddCommGroup
  W1pVanishingOn.instInnerProductSpace

section Poincare

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)} {Γ : Set (EuclideanSpace ℝ ι)}
  {P : ℝ}

/-- The unshifted mixed form of `-Δ` is the Dirichlet integral `∫_Ω ∇u · ∇v`. -/
private theorem mixedForm_laplacian_zero_apply (u v : W1pVanishingOn mu Omega 2 Γ) :
    mixedForm (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ 0 u v =
      ⟪W1p.gradient (u : W1p mu Omega 2), W1p.gradient (v : W1p mu Omega 2)⟫_ℝ := by
  rw [mixedForm_apply, zero_mul, add_zero, energyFormH1_one_zero_zero_eq_inner]

/-- The unshifted mixed form of `-Δ` is symmetric. -/
private theorem mixedForm_laplacian_zero_comm (u v : W1pVanishingOn mu Omega 2 Γ) :
    mixedForm (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ 0 u v =
      mixedForm (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
        (1 : Matrix ι ι ℝ)) Γ 0 v u := by
  rw [mixedForm_laplacian_zero_apply, mixedForm_laplacian_zero_apply, real_inner_comm]

/-- **The Gårding inequality of `-Δ - κ` from a Poincaré–Friedrichs inequality.** If
`‖u‖ ≤ P ‖∇u‖` on `H¹_Γ(Ω)` and `0 ≤ κ`, then
`(1 - κ P²) / (P² + 1) ‖v‖²_{H¹} ≤ ‖∇v‖² - κ ‖v‖²` on `H¹_Γ(Ω)`. -/
private theorem garding_of_poincare
    (hP : ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ, ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖)
    {kappa : ℝ} (hkappa : 0 ≤ kappa) (v : W1pVanishingOn mu Omega 2 Γ) :
    (1 - kappa * P ^ 2) / (P ^ 2 + 1) * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
      energyFormH1 (fun _ ↦ 1) 0 0 (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
        -kappa * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 :=
  mul_norm_sq_le_of_gradient_sub_value_bound (A := 1) (B := kappa) (by linarith)
    (by rw [energyFormH1_one_zero_zero_eq_inner, real_inner_self_eq_norm_sq]; linarith)
    (hP _ v.property)

/-- **The energy form of `-Δ` is coercive on `H¹_Γ(Ω)`** under a Poincaré–Friedrichs inequality
`‖u‖_{L²} ≤ P ‖∇u‖_{L²}` on `H¹_Γ(Ω)`, with constant `1 / (P² + 1)`: no shift by a multiple of
the `L²` inner product is needed. -/
theorem isCoercive_mixedForm_laplacian_of_poincare
    (hP : ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ, ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖) :
    IsCoercive (mixedForm (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ 0) :=
  isCoercive_mixedForm _ (by positivity : (0 : ℝ) < 1 / (P ^ 2 + 1)) fun v ↦ by
    simpa using garding_of_poincare hP le_rfl v

/-- **The spectrum of the mixed Laplacian lies in `[P⁻², ∞)`** under a Poincaré–Friedrichs
inequality `‖u‖_{L²} ≤ P ‖∇u‖_{L²}` on `H¹_Γ(Ω)`: every `κ` with `κ P² < 1` is a resolvent point of
`-Δ_Γ`. No compactness is needed. -/
theorem mem_resolventSet_mixedOperator_laplacian_of_poincare (hΓ : Disjoint Γ Omega)
    (hP : ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ, ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖)
    {kappa : ℝ} (hkappa : kappa * P ^ 2 < 1) :
    kappa ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ).resolventSet := by
  rcases lt_or_ge kappa 0 with hneg | hnonneg
  · exact mem_resolventSet_mixedOperator_laplacian_of_neg hΓ hneg
  have h := neg_mem_resolventSet_mixedOperator
    (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega) (1 : Matrix ι ι ℝ)) hΓ
    (div_pos (sub_pos.2 hkappa) (by positivity)) (garding_of_poincare hP hnonneg)
  rwa [neg_neg] at h

/-- **The mixed Laplacian is invertible** under a Poincaré–Friedrichs inequality on `H¹_Γ(Ω)`:
`0` is a resolvent point of `-Δ_Γ`. -/
theorem zero_mem_resolventSet_mixedOperator_laplacian_of_poincare (hΓ : Disjoint Γ Omega)
    (hP : ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ, ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖) :
    (0 : ℝ) ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ).resolventSet :=
  mem_resolventSet_mixedOperator_laplacian_of_poincare hΓ hP (by rw [zero_mul]; exact one_pos)

/-- **The spectrum of `-Δ_Γ` lies above `1 / P²`** under a Poincaré–Friedrichs inequality
`‖u‖_{L²} ≤ P ‖∇u‖_{L²}` on `H¹_Γ(Ω)`: every `κ` in it has `1 ≤ κ P²`. -/
theorem one_le_mul_sq_of_mem_spectrum_mixedOperator_laplacian (hΓ : Disjoint Γ Omega)
    (hP : ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ, ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖)
    {kappa : ℝ} (hkappa : kappa ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu)
      (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).spectrum) :
    1 ≤ kappa * P ^ 2 :=
  not_lt.1 fun h ↦ (LinearPMap.mem_spectrum_iff _ _).1 hkappa
    (mem_resolventSet_mixedOperator_laplacian_of_poincare hΓ hP h)

/-- **The spectrum of `-Δ_Γ` is positive** under a Poincaré–Friedrichs inequality
`‖u‖_{L²} ≤ P ‖∇u‖_{L²}` on `H¹_Γ(Ω)`. -/
theorem pos_of_mem_spectrum_mixedOperator_laplacian_of_poincare (hΓ : Disjoint Γ Omega)
    (hP : ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ, ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖)
    {kappa : ℝ} (hkappa : kappa ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu)
      (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).spectrum) :
    0 < kappa := by
  have h := one_le_mul_sq_of_mem_spectrum_mixedOperator_laplacian hΓ hP hkappa
  by_contra hle
  nlinarith [mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hle) (sq_nonneg P)]

/-- **The inverse of the mixed Laplacian is the mixed solution operator**: under a
Poincaré–Friedrichs inequality on `H¹_Γ(Ω)`, the resolvent of `-Δ_Γ` at `0` is minus the operator
sending `f` to the solution `u ∈ H¹_Γ(Ω)` of `∫_Ω ∇u · ∇v = ∫_Ω f v` for every `v ∈ H¹_Γ(Ω)`. -/
theorem resolvent_mixedOperator_laplacian_zero_of_poincare (hΓ : Disjoint Γ Omega)
    (hP : ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ, ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖) :
    (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ).resolvent 0 =
      -mixedSolutionOperator _ Γ (isCoercive_mixedForm_laplacian_of_poincare hP) := by
  have h := resolvent_mixedOperator_neg _ hΓ (isCoercive_mixedForm_laplacian_of_poincare hP)
  rwa [neg_zero] at h

/-- The norm of the inverse of the mixed Laplacian is the norm of the mixed solution operator. -/
private theorem norm_resolvent_mixedOperator_laplacian_zero_of_poincare (hΓ : Disjoint Γ Omega)
    (hP : ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ, ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖) :
    ‖(mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ).resolvent 0‖ =
      ‖(isCoercive_mixedForm_laplacian_of_poincare hP).formSolutionOperator
        (W1pVanishingOn.valueL (mu := mu) (Omega := Omega) (p := 2) (Γ := Γ))‖ := by
  rw [resolvent_mixedOperator_laplacian_zero_of_poincare hΓ hP, norm_neg, mixedSolutionOperator_def]

/-- **`λ₁ = ‖(-Δ_Γ)⁻¹‖⁻¹` is positive** on a nonempty open set, under a Poincaré–Friedrichs
inequality on `H¹_Γ(Ω)`. Under the Rellich property `λ₁` is the least point of the spectrum, the
first mixed eigenvalue (`TauCeti.PDE.isLeast_spectrum_mixedOperator_laplacian_of_poincare`). -/
theorem inv_norm_resolvent_mixedOperator_laplacian_zero_pos_of_poincare (hΓ : Disjoint Γ Omega)
    (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty)
    (hP : ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ, ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖) :
    0 < ‖(mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ).resolvent 0‖⁻¹ := by
  rw [norm_resolvent_mixedOperator_laplacian_zero_of_poincare hΓ hP, inv_pos, norm_pos_iff]
  exact (isCoercive_mixedForm_laplacian_of_poincare hP).formSolutionOperator_ne_zero
    (W1pVanishingOn.valueL_ne_zero hΓ hOmega)

/-- **`λ₁ = ‖(-Δ_Γ)⁻¹‖⁻¹` is the optimal Poincaré constant of the Dirichlet integral**: under a
Poincaré–Friedrichs inequality on `H¹_Γ(Ω)`, on a nonempty open set, it is the greatest `C` with
`C ‖u‖²_{L²(Ω)} ≤ ‖∇u‖²_{L²(Ω)}` for every `u ∈ H¹_Γ(Ω)`. No compactness is needed. -/
theorem isGreatest_inv_norm_resolvent_mixedOperator_laplacian_zero_of_poincare
    (hΓ : Disjoint Γ Omega) (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty)
    (hP : ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ, ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖) :
    IsGreatest {C : ℝ | ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ,
        C * ‖W1p.value u‖ ^ 2 ≤ ‖W1p.gradient u‖ ^ 2}
      ‖(mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
        (1 : Matrix ι ι ℝ)) Γ).resolvent 0‖⁻¹ := by
  have hset : {C : ℝ | ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ,
      C * ‖W1p.value u‖ ^ 2 ≤ ‖W1p.gradient u‖ ^ 2} =
      {C : ℝ | ∀ v : W1pVanishingOn mu Omega 2 Γ,
        C * ‖W1pVanishingOn.valueL v‖ ^ 2 ≤
          mixedForm (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
            (1 : Matrix ι ι ℝ)) Γ 0 v v} := by
    ext C
    simp only [mem_ofPred_eq, mixedForm_laplacian_zero_apply, real_inner_self_eq_norm_sq,
      W1pVanishingOn.valueL_apply]
    exact ⟨fun h v ↦ h _ v.property, fun h u hu ↦ h ⟨u, hu⟩⟩
  rw [hset, norm_resolvent_mixedOperator_laplacian_zero_of_poincare hΓ hP]
  exact (isCoercive_mixedForm_laplacian_of_poincare hP).isGreatest_inv_norm_formSolutionOperator
    mixedForm_laplacian_zero_comm (W1pVanishingOn.valueL_ne_zero hΓ hOmega)

/-- **`√‖(-Δ_Γ)⁻¹‖ = λ₁^{-1/2}` is the optimal Poincaré–Friedrichs constant**: if
`‖u‖_{L²(Ω)} ≤ P ‖∇u‖_{L²(Ω)}` on `H¹_Γ(Ω)` for some `P`, on a nonempty open set, the least such
nonnegative constant exists and is `√‖R(0)‖` for the resolvent `R(0)` of `-Δ_Γ` at `0`. -/
theorem isLeast_sqrt_norm_resolvent_mixedOperator_laplacian_zero_of_poincare
    (hΓ : Disjoint Γ Omega) (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty)
    (hP : ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ, ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖) :
    IsLeast {Q : ℝ | 0 ≤ Q ∧ ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ,
        ‖W1p.value u‖ ≤ Q * ‖W1p.gradient u‖}
      √‖(mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
        (1 : Matrix ι ι ℝ)) Γ).resolvent 0‖ := by
  set r := ‖(mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
    (1 : Matrix ι ι ℝ)) Γ).resolvent 0‖
  have hr : 0 < r :=
    inv_pos.1 (inv_norm_resolvent_mixedOperator_laplacian_zero_pos_of_poincare hΓ hOmega hP)
  obtain ⟨hmem, hgreatest⟩ :=
    isGreatest_inv_norm_resolvent_mixedOperator_laplacian_zero_of_poincare hΓ hOmega hP
  refine ⟨⟨Real.sqrt_nonneg r, fun u hu ↦ ?_⟩, fun Q ⟨hQ, hQu⟩ ↦ ?_⟩
  · -- `‖u‖² ≤ r ‖∇u‖²`, and taking square roots gives `‖u‖ ≤ √r ‖∇u‖`.
    have h : ‖W1p.value u‖ ^ 2 ≤ r * ‖W1p.gradient u‖ ^ 2 := (inv_mul_le_iff₀ hr).1 (hmem u hu)
    rw [← Real.sqrt_sq (norm_nonneg (W1p.gradient u)), ← Real.sqrt_mul hr.le]
    exact Real.le_sqrt_of_sq_le h
  · -- A constant `Q` is positive, since some `u` has nonzero value, and `Q⁻²` is a Poincaré
    -- constant of the Dirichlet integral, so `Q⁻² ≤ r⁻¹`.
    obtain ⟨v, hv⟩ : ∃ v : W1pVanishingOn mu Omega 2 Γ, W1pVanishingOn.valueL v ≠ 0 := by
      simpa only [zero_apply] using
        DFunLike.ne_iff.1 (W1pVanishingOn.valueL_ne_zero (p := 2) hΓ hOmega)
    rw [W1pVanishingOn.valueL_apply] at hv
    have hQ0 : 0 < Q := lt_of_le_of_ne hQ fun h ↦ by
      have := hQu _ v.property
      rw [← h, zero_mul, norm_le_zero_iff] at this
      exact hv this
    have hC : (Q ^ 2)⁻¹ ≤ r⁻¹ := hgreatest fun u hu ↦ by
      have h := pow_le_pow_left₀ (norm_nonneg _) (hQu u hu) 2
      rw [mul_pow] at h
      exact (inv_mul_le_iff₀ (by positivity)).2 h
    exact (Real.sqrt_le_left hQ).2 ((inv_le_inv₀ (by positivity) hr).1 hC)

/-- **`λ₁ = ‖(-Δ_Γ)⁻¹‖⁻¹` is the least point of the spectrum of the mixed Laplacian**, under a
Poincaré–Friedrichs inequality on `H¹_Γ(Ω)`, on a nonempty open set with the Rellich property
that the value map `H¹(Ω) → L²(Ω)` is compact. With
`TauCeti.PDE.isLeast_sqrt_norm_resolvent_mixedOperator_laplacian_zero_of_poincare`, the first
mixed eigenvalue is the reciprocal of the square of the optimal Poincaré–Friedrichs constant. -/
theorem isLeast_spectrum_mixedOperator_laplacian_of_poincare (hΓ : Disjoint Γ Omega)
    (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty)
    (hP : ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ, ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2))) :
    IsLeast (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
        (1 : Matrix ι ι ℝ)) Γ).spectrum
      ‖(mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
        (1 : Matrix ι ι ℝ)) Γ).resolvent 0‖⁻¹ := by
  have hB := isCoercive_mixedForm_laplacian_of_poincare (mu := mu) (Omega := Omega) (Γ := Γ) hP
  rw [norm_resolvent_mixedOperator_laplacian_zero_of_poincare hΓ hP]
  refine ⟨?_, fun kappa hkappa ↦ ?_⟩
  · -- `‖S‖⁻¹` is a variational eigenvalue of the Dirichlet integral along the compact value map.
    obtain ⟨u, hu, heq⟩ := hB.exists_ne_zero_forall_apply_eq_inv_norm_smul_inner
      (W1pVanishingOn.isCompactOperator_valueL hK) mixedForm_laplacian_zero_comm
      (W1pVanishingOn.valueL_ne_zero hΓ hOmega)
    refine (mem_spectrum_mixedOperator_laplacian_iff hΓ hK).2 ⟨u, hu, fun v ↦ ?_⟩
    have h := heq v
    rwa [mixedForm_laplacian_zero_apply, W1pVanishingOn.valueL_apply,
      W1pVanishingOn.valueL_apply] at h
  · -- An eigenfunction `u` of `κ` has `κ ‖u‖² = ‖∇u‖² ≥ ‖S‖⁻¹ ‖u‖²`, and `‖u‖ ≠ 0`.
    obtain ⟨u, hu, heq⟩ := (mem_spectrum_mixedOperator_laplacian_iff hΓ hK).1 hkappa
    have hlow := hB.inv_norm_formSolutionOperator_mul_norm_apply_sq_le
      W1pVanishingOn.valueL mixedForm_laplacian_zero_comm u
    rw [mixedForm_laplacian_zero_apply, heq u, real_inner_self_eq_norm_sq,
      W1pVanishingOn.valueL_apply] at hlow
    have hval : W1p.value (u : W1p mu Omega 2) ≠ 0 := fun h ↦
      hu (W1pVanishingOn.valueL_injective (by rw [W1pVanishingOn.valueL_apply, h, map_zero]))
    exact le_of_mul_le_mul_right hlow (by positivity)

/-- **The optimal Poincaré–Friedrichs constant is `λ₁^{-1/2}`.** On a domain with the Rellich
property, if the least point `λ₁` of the spectrum of the mixed Laplacian `-Δ_Γ` is positive, then
`λ₁^{-1/2}` is the least `Q ≥ 0` with `‖u‖_{L²(Ω)} ≤ Q ‖∇u‖_{L²(Ω)}` for every
`u ∈ H¹_Γ(Ω)`. Conversely any such inequality forces `λ₁ > 0`
(`TauCeti.PDE.pos_of_mem_spectrum_mixedOperator_laplacian_of_poincare`). -/
theorem isLeast_inv_sqrt_of_isLeast_spectrum_mixedOperator_laplacian (hΓ : Disjoint Γ Omega)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2))) {lam : ℝ}
    (hlam : IsLeast (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu)
      (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).spectrum lam) (hpos : 0 < lam) :
    IsLeast {Q : ℝ | 0 ≤ Q ∧ ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ,
      ‖W1p.value u‖ ≤ Q * ‖W1p.gradient u‖} (√lam)⁻¹ := by
  have hsqrt : 0 < √lam := Real.sqrt_pos.2 hpos
  refine ⟨⟨by positivity, fun u hu ↦ ?_⟩, fun Q ⟨_, hQ⟩ ↦ ?_⟩
  · have h := (isGreatest_of_isLeast_spectrum_mixedOperator_laplacian hΓ hK hlam).1 ⟨u, hu⟩
    rw [inv_mul_eq_div, le_div_iff₀ hsqrt]
    refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
    rw [mul_pow, Real.sq_sqrt hpos.le, mul_comm]
    exact h
  · have h := one_le_mul_sq_of_mem_spectrum_mixedOperator_laplacian hΓ hQ hlam.1
    rw [inv_le_iff_one_le_mul₀' hsqrt]
    refine (one_le_pow_iff_of_nonneg (by positivity) two_ne_zero).1 ?_
    rwa [mul_pow, Real.sq_sqrt hpos.le]

end Poincare

/-! ### Lipschitz domains

On a bounded connected Lipschitz domain, with a Dirichlet part `Γ` of positive surface measure,
the Poincaré–Friedrichs inequality and the Rellich property hold, so the statements above hold
with no further hypothesis. The domain is an open set `Ω ⊆ EuclideanSpace ℝ ι` carried onto a
bounded Lipschitz domain `V ⊆ ℝ × E` by an affine isometry `e`. -/

section Lipschitz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {V : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}
  {ι : Type*} [Fintype ι] [DecidableEq ι] {Omega : Opens (EuclideanSpace ℝ ι)}
  {Γ : Set (EuclideanSpace ℝ ι)}

omit [DecidableEq ι] in
/-- The hypotheses of the Lipschitz section give a Poincaré–Friedrichs inequality, a nonempty
domain and the Rellich property. -/
private theorem poincare_nonempty_rellich_of_isLipschitzDomainWith
    (hV : (V : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hVb : Bornology.IsBounded (V : Set (WithLp 2 (ℝ × E))))
    (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hVΩ : (V : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' Omega)
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hΓ : (μHE[finrank ℝ E] : Measure (EuclideanSpace ℝ ι))
      (Γ ∩ frontier (Omega : Set (EuclideanSpace ℝ ι))) ≠ 0) :
    (∃ P : ℝ, ∀ u ∈ w1pVanishingOnSubmodule volume Omega 2 Γ,
      ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖) ∧
      (Omega : Set (EuclideanSpace ℝ ι)).Nonempty ∧
      IsCompactOperator (W1p.valueL (mu := volume) (Omega := Omega) (p := 2)) := by
  obtain ⟨P, -, hP⟩ :=
    W1p.exists_norm_value_le_mul_norm_gradient_of_mem_w1pVanishingOnSubmodule_of_affineIsometryEquiv
      (p := 2) ENNReal.ofNat_ne_top hV hVb e hVΩ hconn hΓ
  -- A set of positive measure is nonempty, and a set with a frontier point is nonempty.
  obtain ⟨x, -, hx⟩ := nonempty_of_measure_ne_zero hΓ
  exact ⟨⟨P, hP⟩, closure_nonempty_iff.1 ⟨x, frontier_subset_closure hx⟩,
    W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_of_affineIsometryEquiv hV hVb e hVΩ⟩

/-- **The first mixed eigenvalue on a Lipschitz domain is positive and is the reciprocal square of
the optimal Poincaré–Friedrichs constant.** On a bounded connected Lipschitz domain, with a
Dirichlet part `Γ ⊆ ℝⁿ \ Ω` meeting the frontier in a set of positive surface measure, there is a
least constant `C` with `‖u‖_{L²(Ω)} ≤ C ‖∇u‖_{L²(Ω)}` for every `u ∈ H¹_Γ(Ω)`; it is positive,
and `C⁻²` is the least point of the spectrum of `-Δ_Γ`. Explicitly `C = √‖R(0)‖` for the resolvent
`R(0)` of `-Δ_Γ` at `0`. -/
theorem
    exists_isLeast_poincare_and_isLeast_spectrum_mixedOperator_laplacian_of_isLipschitzDomainWith
    (hV : (V : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hVb : Bornology.IsBounded (V : Set (WithLp 2 (ℝ × E))))
    (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hVΩ : (V : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' Omega)
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hΓ : (μHE[finrank ℝ E] : Measure (EuclideanSpace ℝ ι))
      (Γ ∩ frontier (Omega : Set (EuclideanSpace ℝ ι))) ≠ 0)
    (hΓΩ : Disjoint Γ Omega) :
    ∃ C : ℝ, 0 < C ∧
      IsLeast {Q : ℝ | 0 ≤ Q ∧ ∀ u ∈ w1pVanishingOnSubmodule volume Omega 2 Γ,
        ‖W1p.value u‖ ≤ Q * ‖W1p.gradient u‖} C ∧
      IsLeast (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := volume)
        (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).spectrum (C ^ 2)⁻¹ := by
  obtain ⟨⟨_, hP⟩, hOmega, hK⟩ :=
    poincare_nonempty_rellich_of_isLipschitzDomainWith hV hVb e hVΩ hconn hΓ
  have hr := inv_pos.1 (inv_norm_resolvent_mixedOperator_laplacian_zero_pos_of_poincare hΓΩ
    hOmega hP)
  refine ⟨_, Real.sqrt_pos.2 hr,
    isLeast_sqrt_norm_resolvent_mixedOperator_laplacian_zero_of_poincare hΓΩ hOmega hP, ?_⟩
  rw [Real.sq_sqrt hr.le]
  exact isLeast_spectrum_mixedOperator_laplacian_of_poincare hΓΩ hOmega hP hK

end Lipschitz

end PDE

end TauCeti
