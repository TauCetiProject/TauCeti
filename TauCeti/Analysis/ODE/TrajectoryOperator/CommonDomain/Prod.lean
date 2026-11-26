/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain
public import TauCeti.Analysis.Sobolev.GraphStep.Map
public import TauCeti.Analysis.Fredholm.Prod
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index

/-!
# Direct sums of trajectory operators over a common domain

Let `ι₁ : D₁ →L[ℝ] H₁` and `ι₂ : D₂ →L[ℝ] H₂` embed Banach spaces into Banach spaces, and let
`A₁` and `A₂` be essentially bounded families of operators `D₁ →L[ℝ] H₁` and `D₂ →L[ℝ] H₂`, given
as classes `AL₁` and `AL₂` in `L∞`. The trajectory operators
`D_{Aᵢ} u = (ιᵢ ∘ u)' + Aᵢ(s) u(s)` (`TauCeti.WeakDerivStep.familyDomainTrajectoryOperator`) act
from `Lᵖ(Ω, Dᵢ) ∩ W^{1,p}(Ω, Hᵢ)` to `Lᵖ(Ω, Hᵢ)`. On the direct sums `WithLp q (D₁ × D₂)` and
`WithLp q (H₁ × H₂)`, with the embedding `ι₁ ⊕ ι₂` and the block-diagonal family
`A(s) = A₁(s) ⊕ A₂(s)` (`ContinuousLinearMap.withLpProdMap`), the trajectory operator `D_A` is
`D_{A₁} × D_{A₂}`, read through the identifications of the domain
(`TauCeti.WeakDerivStep.withLpProdEquiv`) and of the target (`MeasureTheory.Lp.withLpProdEquiv`)
with products (`TauCeti.WeakDerivStep.withLpProdEquiv_familyDomainTrajectoryOperator`).

Consequently `D_A` is Fredholm exactly when `D_{A₁}` and `D_{A₂}` are
(`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator_withLpProdMap_iff`), and its
index is then the sum of theirs
(`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_withLpProdMap`). For `q = 2` and
Hilbert spaces `Hᵢ`, `WithLp 2 (H₁ × H₂)` is their orthogonal direct sum, and this is the direct
sum law for the index of `∂ₛ + A(s)`, the counterpart for the index of the direct sum law of the
spectral flow of `A`.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, §4 (the operator `d/ds + A(s)` with an unbounded family `A`, and the
  direct sum axiom of the spectral flow).
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal

variable {D₁ D₂ H₁ H₂ : Type*} [NormedAddCommGroup D₁] [NormedSpace ℝ D₁]
  [NormedAddCommGroup D₂] [NormedSpace ℝ D₂] [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
  [CompleteSpace H₁] [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂]
  {mu : Measure ℝ} [IsFiniteMeasureOnCompacts mu] {Omega : Opens ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]
  [Fact (1 ≤ q)] (ι₁ : D₁ →L[ℝ] H₁) (ι₂ : D₂ →L[ℝ] H₂)
  {AL₁ : Lp (D₁ →L[ℝ] H₁) ∞ (mu.restrict Omega)} {AL₂ : Lp (D₂ →L[ℝ] H₂) ∞ (mu.restrict Omega)}
  {AL : Lp (WithLp q (D₁ × D₂) →L[ℝ] WithLp q (H₁ × H₂)) ∞ (mu.restrict Omega)}

/-- **The trajectory operator of a block-diagonal family splits.** If `A(s) = A₁(s) ⊕ A₂(s)` for
almost every `s`, then the components of `(ι ∘ u)' + A u`, for `ι = ι₁ ⊕ ι₂`, are
`(ι₁ ∘ u₁)' + A₁ u₁` and `(ι₂ ∘ u₂)' + A₂ u₂`, where `u₁` and `u₂` are the components of `u`. -/
theorem withLpProdEquiv_familyDomainTrajectoryOperator
    (hAL : ∀ᵐ s ∂(mu.restrict Omega), AL s = (AL₁ s).withLpProdMap q (AL₂ s))
    (u : WeakDerivStep mu Omega p ((ι₁.withLpProdMap q ι₂).compLpL p (mu.restrict Omega))) :
    Lp.withLpProdEquiv ℝ q (mu.restrict Omega)
        (familyDomainTrajectoryOperator (ι₁.withLpProdMap q ι₂) AL u) =
      (familyDomainTrajectoryOperator ι₁ AL₁ (withLpProdEquiv ι₁ ι₂ u).1,
        familyDomainTrajectoryOperator ι₂ AL₂ (withLpProdEquiv ι₁ ι₂ u).2) := by
  have hD := familyDomainTrajectoryOperator_apply_ae (ι₁.withLpProdMap q ι₂) AL u
  have hprev := ContinuousLinearMap.coeFn_compLpL (WithLp.fstL q ℝ D₁ D₂) (prev _ u)
  have hprev' := ContinuousLinearMap.coeFn_compLpL (WithLp.sndL q ℝ D₁ D₂) (prev _ u)
  have hderiv := (ContinuousLinearMap.compL ℝ ℝ _ _ (WithLp.fstL q ℝ H₁ H₂)).coeFn_compLpL
    (p := p) (μ := mu.restrict Omega) (weakFDeriv _ u)
  have hderiv' := (ContinuousLinearMap.compL ℝ ℝ _ _ (WithLp.sndL q ℝ H₁ H₂)).coeFn_compLpL
    (p := p) (μ := mu.restrict Omega) (weakFDeriv _ u)
  refine Prod.ext (Lp.ext ?_) (Lp.ext ?_)
  · filter_upwards [Lp.coeFn_withLpProdEquiv_fst (𝕜 := ℝ)
        (familyDomainTrajectoryOperator (p := p) (ι₁.withLpProdMap q ι₂) AL u), hD,
      familyDomainTrajectoryOperator_apply_ae ι₁ AL₁ (withLpProdEquiv ι₁ ι₂ u).1, hAL, hprev,
      hderiv]
      with s h₁ h₂ h₃ hA hx hd
    rw [h₁, h₂, h₃, prev_withLpProdEquiv_fst, weakFDeriv_withLpProdEquiv_fst, hx, hd, hA]
    simp
  · filter_upwards [Lp.coeFn_withLpProdEquiv_snd (𝕜 := ℝ)
        (familyDomainTrajectoryOperator (p := p) (ι₁.withLpProdMap q ι₂) AL u), hD,
      familyDomainTrajectoryOperator_apply_ae ι₂ AL₂ (withLpProdEquiv ι₁ ι₂ u).2, hAL, hprev',
      hderiv']
      with s h₁ h₂ h₃ hA hx hd
    rw [h₁, h₂, h₃, prev_withLpProdEquiv_snd, weakFDeriv_withLpProdEquiv_snd, hx, hd, hA]
    simp

/-- The trajectory operator of a block-diagonal family is conjugate to the product of the
trajectory operators of its blocks. -/
private theorem comp_familyDomainTrajectoryOperator_withLpProdMap
    (hAL : ∀ᵐ s ∂(mu.restrict Omega), AL s = (AL₁ s).withLpProdMap q (AL₂ s)) :
    ((Lp.withLpProdEquiv ℝ q (mu.restrict Omega) (p := p) (E := H₁) (F := H₂) :
        Lp (WithLp q (H₁ × H₂)) p (mu.restrict Omega) →L[ℝ] _).comp
        (familyDomainTrajectoryOperator (p := p) (ι₁.withLpProdMap q ι₂) AL)) =
      ((familyDomainTrajectoryOperator (p := p) ι₁ AL₁).prodMap
          (familyDomainTrajectoryOperator (p := p) ι₂ AL₂)).comp
        (withLpProdEquiv (mu := mu) (Omega := Omega) (p := p) (q := q) ι₁ ι₂ :
          WeakDerivStep mu Omega p ((ι₁.withLpProdMap q ι₂).compLpL p (mu.restrict Omega)) →L[ℝ]
            _) :=
  ContinuousLinearMap.ext fun u ↦ withLpProdEquiv_familyDomainTrajectoryOperator ι₁ ι₂ hAL u

/-- **A block-diagonal trajectory operator is Fredholm exactly when its blocks are.** -/
theorem isFredholm_familyDomainTrajectoryOperator_withLpProdMap_iff
    (hAL : ∀ᵐ s ∂(mu.restrict Omega), AL s = (AL₁ s).withLpProdMap q (AL₂ s)) :
    (familyDomainTrajectoryOperator (p := p) (ι₁.withLpProdMap q ι₂) AL).IsFredholm ↔
      (familyDomainTrajectoryOperator (p := p) ι₁ AL₁).IsFredholm ∧
        (familyDomainTrajectoryOperator (p := p) ι₂ AL₂).IsFredholm := by
  rw [ContinuousLinearMap.isFredholm_iff_of_comp_eq _ _
      (comp_familyDomainTrajectoryOperator_withLpProdMap ι₁ ι₂ hAL),
    ContinuousLinearMap.isFredholm_prodMap_iff]

/-- **The index of a block-diagonal trajectory operator is the sum of the indices of its blocks.**
If `A(s) = A₁(s) ⊕ A₂(s)` for almost every `s` and the trajectory operators of `A₁` and `A₂` are
Fredholm, then the index of `u ↦ (ι ∘ u)' + A u`, for `ι = ι₁ ⊕ ι₂`, is the sum of their
indices. -/
theorem index_familyDomainTrajectoryOperator_withLpProdMap
    (hAL : ∀ᵐ s ∂(mu.restrict Omega), AL s = (AL₁ s).withLpProdMap q (AL₂ s))
    (h₁ : (familyDomainTrajectoryOperator (p := p) ι₁ AL₁).IsFredholm)
    (h₂ : (familyDomainTrajectoryOperator (p := p) ι₂ AL₂).IsFredholm) :
    (familyDomainTrajectoryOperator (p := p) (ι₁.withLpProdMap q ι₂) AL).index =
      (familyDomainTrajectoryOperator (p := p) ι₁ AL₁).index +
        (familyDomainTrajectoryOperator (p := p) ι₂ AL₂).index := by
  have := h₁.finite_ker
  have := h₁.finite_coker
  have := h₂.finite_ker
  have := h₂.finite_coker
  rw [← ContinuousLinearMap.index_equiv_comp _
      (Lp.withLpProdEquiv ℝ q (mu.restrict Omega) (p := p) (E := H₁) (F := H₂)),
    comp_familyDomainTrajectoryOperator_withLpProdMap ι₁ ι₂ hAL,
    ContinuousLinearMap.index_comp_equiv, ContinuousLinearMap.index_prodMap]

end TauCeti.WeakDerivStep
