/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Coercive estimates and openness for the trajectory operator over a common domain

Let `ι : D →L[ℝ] H` embed a Banach space `D` into a real Hilbert space `H`, and let
`A : D →L[ℝ] H` be symmetric relative to `ι`, `⟪A x, ι y⟫ = ⟪ι x, A y⟫`. Read `A` as an operator
on `H` with domain `D`, such as the asymptotic operator of a Hamiltonian orbit, which maps loops in
`H¹(S¹)` to loops in `L²(S¹)`. This file sharpens the whole-line `L²` theory of
`TauCeti.WeakDerivStep.domainTrajectoryOperator ι A`, `u ↦ (ι ∘ u)' + A ∘ u`, from
`TauCeti/Analysis/ODE/TrajectoryOperator/CommonDomain.lean`, using only the Pythagorean identity
`‖(∂s ∘ ι + A) u‖² = ‖(ι ∘ u)'‖² + ‖A ∘ u‖²`.

* **The coercive estimate.** If `‖x‖ ≤ C ‖A x‖` on `D`, then `‖u‖ ≤ max C 1 ‖(∂s ∘ ι + A) u‖`
  (`TauCeti.WeakDerivStep.norm_le_max_mul_norm_domainTrajectoryOperator`), so the range is closed
  (`TauCeti.WeakDerivStep.isClosed_range_domainTrajectoryOperator`). No invertibility of `A` is
  needed.
* **Injectivity.** The operator is injective as soon as `ι` and `A` have no common kernel
  (`TauCeti.WeakDerivStep.injective_domainTrajectoryOperator_of_ker`); `ι` need not be injective.
* **The inverse bound.** For invertible `A`, `‖(∂s ∘ ι + A)⁻¹‖ ≤ max ‖A⁻¹‖ 1`
  (`TauCeti.WeakDerivStep.norm_inverse_domainTrajectoryOperator_le_max`), which improves the bound
  `√(1 + ‖A⁻¹‖²)` of `TauCeti.WeakDerivStep.norm_inverse_domainTrajectoryOperator_le`.
* **Openness and small weights.** Invertibility of the trajectory operator is an open condition
  on `A`, over any open `Ω ⊆ ℝ` and exponent `p`
  (`TauCeti.WeakDerivStep.eventually_isInvertible_domainTrajectoryOperator`). Hence for symmetric
  invertible `A` and every `C : D →L[ℝ] H`, the operators `∂s ∘ ι + (A - δ C)` are invertible for
  small `δ` (`TauCeti.WeakDerivStep.eventually_isInvertible_domainTrajectoryOperator_sub_smul`).
  For `C = ι` these are the operators `d/ds + A - δ` into which the exponential weight `e^{δ s}`
  turns `d/ds + A`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the operator `d/ds + A` with an invertible self-adjoint
  asymptotic operator.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc. 27
  (1995), 1–33, on the operators `d/ds + A(s)` with self-adjoint `A(s)`.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open Filter _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology

section Banach

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {mu : Measure ℝ} [IsFiniteMeasureOnCompacts mu] {Omega : Opens ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {ι A : D →L[ℝ] H}

/-- **Invertibility is open in the coefficient.** If `∂s ∘ ι + A` is invertible, so is
`∂s ∘ ι + B` for every `B` close to `A` in operator norm. The domain need not be complete: an
invertible `∂s ∘ ι + A` makes it isomorphic to `Lᵖ(Ω, H)`. -/
theorem eventually_isInvertible_domainTrajectoryOperator
    (hA : (domainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι A).IsInvertible) :
    ∀ᶠ B in 𝓝 A,
      (domainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι B).IsInvertible := by
  obtain ⟨e, -⟩ := id hA
  have : CompleteSpace (WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega))) :=
    (completeSpace_congr (e := e.toEquiv) e.isUniformEmbedding).2 inferInstance
  exact ((continuous_domainTrajectoryOperator ι).tendsto A).eventually hA.eventually_nhds

end Banach

section Symmetric

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {ι A : D →L[ℝ] H}

/-- **The coercive estimate.** If `A` is `ι`-symmetric and `‖x‖ ≤ C ‖A x‖` on `D`, then
`‖u‖ ≤ max C 1 ‖(∂s ∘ ι + A) u‖` on `L²(ℝ)`. -/
theorem norm_le_max_mul_norm_domainTrajectoryOperator
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) {C : ℝ} (hC : ∀ x, ‖x‖ ≤ C * ‖A x‖)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ‖u‖ ≤ max C 1 * ‖domainTrajectoryOperator ι A u‖ := by
  have hprev : ‖prev (ι.compLpL 2 μ₀) u‖ ≤ max C 1 * ‖A.compLpL 2 μ₀ (prev _ u)‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [A.coeFn_compLpL (prev _ u)] with s hs
    rw [hs]
    exact (hC _).trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (norm_nonneg _))
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, norm_domainTrajectoryOperator_sq hSymm,
    norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq]
  have h₁ : ‖prev (ι.compLpL 2 μ₀) u‖ ^ 2 ≤ max C 1 ^ 2 * ‖A.compLpL 2 μ₀ (prev _ u)‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hprev 2
  have h₂ : ‖weakFDeriv (ι.compLpL 2 μ₀) u‖ ^ 2 ≤
      max C 1 ^ 2 * ‖weakFDeriv (ι.compLpL 2 μ₀) u‖ ^ 2 :=
    le_mul_of_one_le_left (by positivity) (one_le_pow₀ (le_max_right C 1))
  linarith

/-- If `A` is `ι`-symmetric and `‖x‖ ≤ C ‖A x‖` on `D`, then `∂s ∘ ι + A` has closed range on
`L²(ℝ)`. -/
theorem isClosed_range_domainTrajectoryOperator
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) {C : ℝ} (hC : ∀ x, ‖x‖ ≤ C * ‖A x‖) :
    IsClosed (Set.range (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A)) := by
  set T := domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A
  exact (T.antilipschitz_of_bound (K := ⟨max C 1, by positivity⟩)
    (norm_le_max_mul_norm_domainTrajectoryOperator hSymm hC)).isClosed_range T.uniformContinuous

/-- If `A` is `ι`-symmetric and `ι` and `A` have no common kernel, then `∂s ∘ ι + A` is injective
on `L²(ℝ)`: a solution of the homogeneous equation has `(ι ∘ u)' = 0` and `A ∘ u = 0` by the
Pythagorean identity, so `ι ∘ u` is a constant in `L²(ℝ, H)`, hence `0`. -/
theorem injective_domainTrajectoryOperator_of_ker
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hker : ∀ x, ι x = 0 → A x = 0 → x = 0) :
    Function.Injective (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu ↦ ?_
  have hw0 : weakFDeriv _ u = 0 := norm_le_zero_iff.mp <| by
    simpa [hu] using norm_weakFDeriv_le_norm_domainTrajectoryOperator hSymm u
  have hA0 : A.compLpL 2 μ₀ (prev _ u) = 0 := norm_le_zero_iff.mp <| by
    simpa [hu] using norm_compLpL_prev_le_norm_domainTrajectoryOperator hSymm u
  have hv0 : toIdL (ι.compLpL 2 μ₀) u = 0 :=
    eq_zero_of_weakFDeriv_eq_zero (p := 2) ENNReal.ofNat_ne_top (by rw [weakFDeriv_toIdL, hw0])
  have hι0 : ι.compLpL 2 μ₀ (prev _ u) = 0 := by
    have h0 := congrArg (prev _) hv0
    rwa [prev_toIdL, prev_zero] at h0
  apply ext
  rw [prev_zero]
  apply Lp.ext
  filter_upwards [ι.coeFn_compLpL (prev _ u), hι0 ▸ Lp.coeFn_zero H 2 _,
    A.coeFn_compLpL (prev _ u), hA0 ▸ Lp.coeFn_zero H 2 _, Lp.coeFn_zero D 2 _]
    with s hι hι' hA hA' hd0
  rw [hd0, Pi.zero_apply]
  exact hker _ (by rw [← hι, hι', Pi.zero_apply]) (by rw [← hA, hA', Pi.zero_apply])

/-- **The inverse bound.** For `ι`-symmetric invertible `A`,
`‖(∂s ∘ ι + A)⁻¹‖ ≤ max ‖A⁻¹‖ 1` on `L²(ℝ)`. -/
theorem norm_inverse_domainTrajectoryOperator_le_max
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hA : A.IsInvertible) :
    ‖(domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).inverse‖ ≤
      max ‖A.inverse‖ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (ContinuousLinearMap.norm_inverse_apply_le_of_forall_norm_le
      (bijective_domainTrajectoryOperator hSymm hA).2
      (norm_le_max_mul_norm_domainTrajectoryOperator hSymm hA.norm_le_norm_inverse_mul_norm))

/-- **Small weights.** For `ι`-symmetric invertible `A` and any `C : D →L[ℝ] H`, the operator
`∂s ∘ ι + (A - δ C)` is invertible on `L²(ℝ)` for every `δ` close to `0`. For `C = ι` this is the
operator `d/ds + A - δ` into which the exponential weight `e^{δ s}` turns `d/ds + A`. -/
theorem eventually_isInvertible_domainTrajectoryOperator_sub_smul
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hA : A.IsInvertible) (C : D →L[ℝ] H) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι
      (A - δ • C)).IsInvertible := by
  have hcont : Continuous fun δ : ℝ ↦ A - δ • C := by fun_prop
  exact (hcont.tendsto' 0 A (by simp)).eventually
    (eventually_isInvertible_domainTrajectoryOperator
      (isInvertible_domainTrajectoryOperator hSymm hA))

end Symmetric

end TauCeti.WeakDerivStep
