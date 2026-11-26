/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain
public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.Analysis.Sobolev.GraphStep.Map
public import TauCeti.MeasureTheory.Function.Lp.ContinuousLinearEquiv
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index

/-!
# Changes of trivialization of the trajectory operator over a common domain

Let `ι : D →L[ℝ] H` embed a Banach space `D` into a Banach space `H`, and let `A` be an
essentially bounded family of operators `D →L[ℝ] H`, given as a class `AL` in `L∞`. The operator
`D_A u = (ι ∘ u)' + A(s) u(s)` from `Lᵖ(Ω, D) ∩ W^{1,p}(Ω, H)` to `Lᵖ(Ω, H)` is
`TauCeti.WeakDerivStep.familyDomainTrajectoryOperator ι AL`.

A change of trivialization consists of isomorphisms `U : H ≃L[ℝ] K` and `V : D ≃L[ℝ] D'` which
intertwine the embeddings, `ι' ∘ V = U ∘ ι`; the conjugated family is `s ↦ U ∘ A(s) ∘ V⁻¹`, of
operators `D' → K`. Composing paths with `V` and `U` identifies the graph spaces
(`TauCeti.WeakDerivStep.mapEquiv`) and the spaces `Lᵖ(Ω, H)` and `Lᵖ(Ω, K)`
(`ContinuousLinearEquiv.compLpL`), and since the derivative commutes with the constant operator
`U`,

`D_{U A V⁻¹} (V ∘ u) = U ∘ D_A u`

(`TauCeti.WeakDerivStep.compLpL_familyDomainTrajectoryOperator`). Hence the conjugated operator
is Fredholm exactly when `D_A` is
(`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator_comp_comp_symm_iff`), and then
it has the same index (`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_comp_comp_symm`).
This is the counterpart for the index of `∂ₛ + A(s)` of the invariance of the spectral flow of `A`
under changes of trivialization (`TauCeti.domainSpectralFlow_comp_comp_symm`). Together with the
direct sum law `TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_withLpProdMap`, it
splits the operator along a decomposition of `D` and `H` that `A` preserves, once `D` and `H` are
identified with direct sums.

The change of trivialization here does not depend on `s`. For the trajectory operator on a
finite-dimensional space, changes of trivialization along a `C¹` path of operators are treated in
`TauCeti.Analysis.ODE.TrajectoryOperator.Gauge`.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, §4.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open MeasureTheory TopologicalSpace
open scoped ENNReal

variable {D D' H K : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup D']
  [NormedSpace ℝ D'] [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
  {mu : Measure ℝ} [IsFiniteMeasureOnCompacts mu] {Omega : Opens ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {ι : D →L[ℝ] H} {ι' : D' →L[ℝ] K} (V : D ≃L[ℝ] D') (U : H ≃L[ℝ] K)
  {AL : Lp (D →L[ℝ] H) ∞ (mu.restrict Omega)} {AL' : Lp (D' →L[ℝ] K) ∞ (mu.restrict Omega)}

/-- **The trajectory operator of a conjugated family.** If `U : H ≃L[ℝ] K` and
`V : D ≃L[ℝ] D'` intertwine the embeddings, `ι' ∘ V = U ∘ ι`, and `A'(s) = U ∘ A(s) ∘ V⁻¹` for
almost every `s`, then `(ι' ∘ (V ∘ u))' + A' (V ∘ u) = U ∘ ((ι ∘ u)' + A u)`. -/
theorem compLpL_familyDomainTrajectoryOperator
    (hUV : ι'.comp (V : D →L[ℝ] D') = (U : H →L[ℝ] K).comp ι)
    (hAL : ∀ᵐ s ∂(mu.restrict Omega),
      AL' s = (U : H →L[ℝ] K).comp ((AL s).comp (V.symm : D' →L[ℝ] D)))
    (u : WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega))) :
    U.compLpL p (mu.restrict Omega) (familyDomainTrajectoryOperator ι AL u) =
      familyDomainTrajectoryOperator ι' AL' (mapEquiv V U hUV u) := by
  refine Lp.ext ?_
  filter_upwards [U.coeFn_compLpL (familyDomainTrajectoryOperator ι AL u),
    familyDomainTrajectoryOperator_apply_ae ι AL u,
    familyDomainTrajectoryOperator_apply_ae ι' AL' (mapEquiv V U hUV u),
    (V : D →L[ℝ] D').coeFn_compLpL (prev _ u),
    (ContinuousLinearMap.compL ℝ ℝ H K (U : H →L[ℝ] K)).coeFn_compLpL (weakFDeriv _ u), hAL]
    with s h₁ h₂ h₃ hprev hderiv hA
  rw [h₁, h₂, h₃, prev_mapEquiv, weakFDeriv_mapEquiv, hprev, hA, hderiv]
  simp

/-- The conjugation identity `U ∘ D_A = D_{U A V⁻¹} ∘ (u ↦ V ∘ u)` as an identity of continuous
linear maps. -/
private theorem compLpL_comp_familyDomainTrajectoryOperator
    (hUV : ι'.comp (V : D →L[ℝ] D') = (U : H →L[ℝ] K).comp ι)
    (hAL : ∀ᵐ s ∂(mu.restrict Omega),
      AL' s = (U : H →L[ℝ] K).comp ((AL s).comp (V.symm : D' →L[ℝ] D))) :
    (U.compLpL p (mu.restrict Omega) : Lp H p (mu.restrict Omega) →L[ℝ]
        Lp K p (mu.restrict Omega)).comp (familyDomainTrajectoryOperator ι AL) =
      (familyDomainTrajectoryOperator ι' AL').comp
        (mapEquiv (mu := mu) (Omega := Omega) (p := p) V U hUV :
          WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega)) →L[ℝ]
            WeakDerivStep mu Omega p (ι'.compLpL p (mu.restrict Omega))) :=
  ContinuousLinearMap.ext fun u ↦ compLpL_familyDomainTrajectoryOperator V U hUV hAL u

/-- **Changes of trivialization preserve the Fredholm property.** If `U : H ≃L[ℝ] K` and
`V : D ≃L[ℝ] D'` intertwine the embeddings, `ι' ∘ V = U ∘ ι`, and `A'(s) = U ∘ A(s) ∘ V⁻¹` for
almost every `s`, then `u ↦ (ι' ∘ u)' + A' u` is Fredholm exactly when `u ↦ (ι ∘ u)' + A u` is. -/
theorem isFredholm_familyDomainTrajectoryOperator_comp_comp_symm_iff
    (hUV : ι'.comp (V : D →L[ℝ] D') = (U : H →L[ℝ] K).comp ι)
    (hAL : ∀ᵐ s ∂(mu.restrict Omega),
      AL' s = (U : H →L[ℝ] K).comp ((AL s).comp (V.symm : D' →L[ℝ] D))) :
    (familyDomainTrajectoryOperator (p := p) ι' AL').IsFredholm ↔
      (familyDomainTrajectoryOperator (p := p) ι AL).IsFredholm :=
  (ContinuousLinearMap.isFredholm_iff_of_comp_eq _ _
    (compLpL_comp_familyDomainTrajectoryOperator V U hUV hAL)).symm

/-- **Changes of trivialization preserve the index.** If `U : H ≃L[ℝ] K` and `V : D ≃L[ℝ] D'`
intertwine the embeddings, `ι' ∘ V = U ∘ ι`, and `A'(s) = U ∘ A(s) ∘ V⁻¹` for almost every `s`,
then `u ↦ (ι' ∘ u)' + A' u` and `u ↦ (ι ∘ u)' + A u` have the same index. -/
theorem index_familyDomainTrajectoryOperator_comp_comp_symm
    (hUV : ι'.comp (V : D →L[ℝ] D') = (U : H →L[ℝ] K).comp ι)
    (hAL : ∀ᵐ s ∂(mu.restrict Omega),
      AL' s = (U : H →L[ℝ] K).comp ((AL s).comp (V.symm : D' →L[ℝ] D))) :
    (familyDomainTrajectoryOperator (p := p) ι' AL').index =
      (familyDomainTrajectoryOperator (p := p) ι AL).index := by
  rw [← ContinuousLinearMap.index_comp_equiv _ (mapEquiv V U hUV),
    ← compLpL_comp_familyDomainTrajectoryOperator V U hUV hAL,
    ContinuousLinearMap.index_equiv_comp]

end TauCeti.WeakDerivStep
