/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.Coordinates
public import TauCeti.Analysis.Sobolev.GraphStep.ZeroAtInfty
public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.MeasureTheory.Function.Lp.Operator.LpMultiplication
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Basic
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Basic
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The trajectory operator over a common domain

When a spatial differential operator `A` is unbounded on a Banach space `H` and bounded only on a
denser Sobolev domain `D` embedded via `ι : D →L[ℝ] H`, `TauCeti.WeakDerivStep.trajectoryOperator`
on `W^{1,p}(Ω, H)` cannot model `∂s + A`. Instead, for `ι A : D →L[ℝ] H` and open `Ω ⊆ ℝ`,
`WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega))` realizes `Lᵖ(Ω, D) ∩ W^{1,p}(Ω, H)`,
where `∂s ∘ ι + A` defines a bounded map `TauCeti.WeakDerivStep.domainTrajectoryOperator ι A` into
`Lᵖ(Ω, H)`. More generally, for an `L∞` family `A : Lp (D →L[ℝ] H) ∞ (mu.restrict Omega)` acting
by `MeasureTheory.Lp.operatorMultiplication`, `u ↦ (ι ∘ u)' + A(s) u(s)` is the bounded map
`TauCeti.WeakDerivStep.familyDomainTrajectoryOperator ι A`; a coefficient almost everywhere equal to
a constant `A₀` gives `domainTrajectoryOperator ι A₀`
(`TauCeti.WeakDerivStep.familyDomainTrajectoryOperator_of_ae_eq_const`), and the basic Banach API of
the autonomous operator is derived from that of the family. Taking `D = H¹(AddCircle T, E)` and
`H = H⁰(AddCircle T, E)` feeds `CircleSobolev.cylinderOperator`
(`TauCeti/Analysis/Sobolev/Circle/LinearODE/Cylinder.lean`).

After proving `1`-Lipschitz dependence on `A`, openness of invertibility in `A` (in particular
for the small weighted shifts `∂s ∘ ι + (A - δ C)` of an invertible `∂s ∘ ι + A`), weak-ODE
characterizations, and mode intertwining over Banach spaces, the second half develops the
whole-line `L²(ℝ)` theory (`Ω = ⊤`, `p = 2`) for Hilbert `H` and `ι`-symmetric `A`
(`⟪A x, ι y⟫ = ⟪ι x, A y⟫`): orthogonality, the integration by parts
`⟪(ι ∘ u)', ι ∘ w⟫ = -⟪ι ∘ u, (ι ∘ w)'⟫`, the Pythagorean identity
`‖(∂s ∘ ι + A) u‖² = ‖(ι ∘ u)'‖² + ‖A ∘ u‖²`, injectivity when `ι` and `A` have no common kernel,
the coercive estimate `‖u‖ ≤ max C 1 ‖(∂s ∘ ι + A) u‖` and closed range under `‖x‖ ≤ C ‖A x‖`,
invertibility with inverse norm `≤ max ‖A⁻¹‖ 1` for invertible `A`, failure of closed range
when `A.ker ≠ ⊥`, and equivalence of closed range / Fredholmness / invertibility with
`A.IsInvertible` for index-`0` Fredholm `A`. Adapts
`TauCeti/Analysis/ODE/TrajectoryOperator.lean`,
`TauCeti/Analysis/Sobolev/GraphStep/Coordinates.lean`,
`TauCeti/Analysis/ODE/EnergyEstimate/Cokernel.lean`, and
`TauCeti/Analysis/ODE/TrajectoryOperator/Degenerate.lean`.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, §§2, 4.
* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open Filter _root_.MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace Topology

section Banach

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {mu : Measure ℝ} [IsFiniteMeasureOnCompacts mu] {Omega : Opens ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "μΩ" => (mu.restrict Omega)

/-- The first-order operator `u ↦ (ι ∘ u)' + A(s) u(s)` from `Lᵖ(Ω, D) ∩ W^{1,p}(Ω, H)` to
`Lᵖ(Ω, H)`, for an `L∞` family `A` of operators from `D` to `H`. It depends only on the almost
everywhere class of `A`. -/
def familyDomainTrajectoryOperator (ι : D →L[ℝ] H) (A : Lp (D →L[ℝ] H) ∞ μΩ) :
    WeakDerivStep mu Omega p (ι.compLpL p μΩ) →L[ℝ] Lp H p μΩ :=
  ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p μΩ).comp (weakFDerivL (ι.compLpL p μΩ)) +
    (Lp.operatorMultiplication p A).comp (prevL (ι.compLpL p μΩ))

/-- Unfolding formula for `familyDomainTrajectoryOperator` as a continuous linear map. -/
theorem familyDomainTrajectoryOperator_def (ι : D →L[ℝ] H) (A : Lp (D →L[ℝ] H) ∞ μΩ) :
    familyDomainTrajectoryOperator (p := p) ι A =
      ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p μΩ).comp (weakFDerivL (ι.compLpL p μΩ)) +
        (Lp.operatorMultiplication p A).comp (prevL (ι.compLpL p μΩ)) := (rfl)

/-- `familyDomainTrajectoryOperator` adds weak-derivative evaluation at `1` to the action of the
coefficient. -/
@[simp] theorem familyDomainTrajectoryOperator_apply (ι : D →L[ℝ] H) (A : Lp (D →L[ℝ] H) ∞ μΩ)
    (u : WeakDerivStep mu Omega p (ι.compLpL p μΩ)) :
    familyDomainTrajectoryOperator ι A u =
      (ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p μΩ (weakFDeriv (ι.compLpL p μΩ) u) +
      Lp.operatorMultiplication p A (prev (ι.compLpL p μΩ) u) := by
  simp [familyDomainTrajectoryOperator_def]

/-- Pointwise almost-everywhere formula for `familyDomainTrajectoryOperator`. -/
theorem familyDomainTrajectoryOperator_apply_ae (ι : D →L[ℝ] H) (A : Lp (D →L[ℝ] H) ∞ μΩ)
    (u : WeakDerivStep mu Omega p (ι.compLpL p μΩ)) :
    familyDomainTrajectoryOperator ι A u =ᵐ[μΩ]
      fun s ↦ weakFDeriv (ι.compLpL p μΩ) u s 1 + A s (prev (ι.compLpL p μΩ) u s) := by
  let base := ι.compLpL p μΩ
  rw [familyDomainTrajectoryOperator_apply]
  filter_upwards [Lp.coeFn_add ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p μΩ
      (weakFDeriv base u)) (Lp.operatorMultiplication p A (prev base u)),
    (ContinuousLinearMap.apply ℝ H (1 : ℝ)).coeFn_compLpL (weakFDeriv base u),
    Lp.operatorMultiplication_ae A (prev base u)] with s hadd hd hA
  rw [hadd, Pi.add_apply, hd, hA, ContinuousLinearMap.apply_apply]

/-- The operator norm of `familyDomainTrajectoryOperator ι A` is at most `1 + ‖A‖`. -/
theorem norm_familyDomainTrajectoryOperator_le (ι : D →L[ℝ] H) (A : Lp (D →L[ℝ] H) ∞ μΩ) :
    ‖familyDomainTrajectoryOperator (p := p) ι A‖ ≤ 1 + ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  rw [familyDomainTrajectoryOperator_apply]; refine (norm_add_le _ _).trans ?_
  rw [ContinuousLinearMap.compLpL_apply, ContinuousLinearMap.norm_apply_one_compLp, one_add_mul]
  exact add_le_add (norm_weakFDeriv_le _ u) ((Lp.norm_operatorMultiplication_apply_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_prev_le _ u) (norm_nonneg _)))

/-- Subtracting two operators over the same domain embedding cancels the derivative part and
leaves the action of the difference of the coefficients. -/
theorem familyDomainTrajectoryOperator_sub (ι : D →L[ℝ] H) (A B : Lp (D →L[ℝ] H) ∞ μΩ) :
    familyDomainTrajectoryOperator (p := p) ι A - familyDomainTrajectoryOperator ι B =
      (Lp.operatorMultiplication p (A - B)).comp (prevL (ι.compLpL p μΩ)) := by
  simp only [familyDomainTrajectoryOperator, map_sub, ContinuousLinearMap.sub_comp]
  abel

/-- Changing the coefficient from `B` to `A` changes `familyDomainTrajectoryOperator ι` by at most
`‖A - B‖` in operator norm. -/
theorem norm_familyDomainTrajectoryOperator_sub_le (ι : D →L[ℝ] H) (A B : Lp (D →L[ℝ] H) ∞ μΩ) :
    ‖familyDomainTrajectoryOperator (p := p) ι A - familyDomainTrajectoryOperator ι B‖ ≤
      ‖A - B‖ := by
  rw [familyDomainTrajectoryOperator_sub]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u ↦ ?_
  rw [ContinuousLinearMap.comp_apply, prevL_apply]
  exact (Lp.norm_operatorMultiplication_apply_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_prev_le _ u) (norm_nonneg _))

/-- `familyDomainTrajectoryOperator ι` is `1`-Lipschitz in its `L∞` coefficient. -/
theorem lipschitzWith_familyDomainTrajectoryOperator (ι : D →L[ℝ] H) :
    LipschitzWith 1 (familyDomainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι) :=
  LipschitzWith.of_dist_le_mul fun A B ↦ by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
      norm_familyDomainTrajectoryOperator_sub_le ι A B

/-- `familyDomainTrajectoryOperator ι` depends continuously on its `L∞` coefficient. -/
@[fun_prop] theorem continuous_familyDomainTrajectoryOperator (ι : D →L[ℝ] H) :
    Continuous (familyDomainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι) :=
  (lipschitzWith_familyDomainTrajectoryOperator ι).continuous

/-- `familyDomainTrajectoryOperator ι A u = f` iff `(ι ∘ u)' = f - A u` weakly. -/
theorem familyDomainTrajectoryOperator_eq_iff_hasWeakLineDerivOn (ι : D →L[ℝ] H)
    (A : Lp (D →L[ℝ] H) ∞ μΩ) (u : WeakDerivStep mu Omega p (ι.compLpL p μΩ)) (f : Lp H p μΩ) :
    familyDomainTrajectoryOperator ι A u = f ↔ HasWeakLineDerivOn mu Omega
      (ι.compLpL p μΩ (prev (ι.compLpL p μΩ) u))
      (fun s ↦ f s - A s (prev (ι.compLpL p μΩ) u s)) 1 := by
  have hd := (hasWeakFDerivOn_base_prev (ι.compLpL p μΩ) u).hasWeakLineDerivOn 1
  refine ⟨fun h ↦ hd.congr_ae_deriv ?_, fun h ↦ Lp.ext ?_⟩
  · filter_upwards [h ▸ familyDomainTrajectoryOperator_apply_ae ι A u] with s hs
    exact eq_sub_iff_add_eq.mpr hs.symm
  · filter_upwards [familyDomainTrajectoryOperator_apply_ae ι A u, hd.ae_eq h] with s hs hd'
    rw [hs, hd', sub_add_cancel]

/-- If `x ∈ Lᵖ(Ω, D)` solves `(ι ∘ x)' = f - A x` weakly on `Ω`, then `x` lifts to `u` with
`familyDomainTrajectoryOperator ι A u = f`. -/
theorem exists_prev_eq_and_familyDomainTrajectoryOperator_eq_of_hasWeakLineDerivOn
    (ι : D →L[ℝ] H) (A : Lp (D →L[ℝ] H) ∞ μΩ) {x : Lp D p μΩ} {f : Lp H p μΩ}
    (h : HasWeakLineDerivOn mu Omega (ι.compLpL p μΩ x) (fun s ↦ f s - A s (x s)) 1) :
    ∃ u : WeakDerivStep mu Omega p (ι.compLpL p μΩ),
      prev (ι.compLpL p μΩ) u = x ∧ familyDomainTrajectoryOperator ι A u = f := by
  let g := f - Lp.operatorMultiplication p A x
  have hg : (fun s ↦ f s - A s (x s)) =ᵐ[μΩ] g := by
    filter_upwards [Lp.coeFn_sub f (Lp.operatorMultiplication p A x),
      Lp.operatorMultiplication_ae A x] with s hs hA
    simp only [g, hs, Pi.sub_apply, hA]
  refine ⟨mkLine _ x g (h.congr_ae_deriv hg), prev_mkLine _ _ _ _, ?_⟩
  rwa [familyDomainTrajectoryOperator_eq_iff_hasWeakLineDerivOn, prev_mkLine]

/-- The autonomous first-order operator `u ↦ (ι ∘ u)' + A ∘ u` from `Lᵖ(Ω, D) ∩ W^{1,p}(Ω, H)` to
`Lᵖ(Ω, H)`. It is `familyDomainTrajectoryOperator` for the constant coefficient `A`
(`familyDomainTrajectoryOperator_toLp_const`). -/
def domainTrajectoryOperator (ι A : D →L[ℝ] H) :
    WeakDerivStep mu Omega p (ι.compLpL p μΩ) →L[ℝ] Lp H p μΩ :=
  ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p μΩ).comp (weakFDerivL (ι.compLpL p μΩ)) +
    (A.compLpL p μΩ).comp (prevL (ι.compLpL p μΩ))

/-- Unfolding formula for `domainTrajectoryOperator` as a continuous linear map. -/
theorem domainTrajectoryOperator_def (ι A : D →L[ℝ] H) :
    domainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι A =
      ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p μΩ).comp (weakFDerivL (ι.compLpL p μΩ)) +
        (A.compLpL p μΩ).comp (prevL (ι.compLpL p μΩ)) := (rfl)

/-- `domainTrajectoryOperator` adds weak-derivative evaluation at `1` to postcomposition by `A`. -/
@[simp] theorem domainTrajectoryOperator_apply (ι A : D →L[ℝ] H)
    (u : WeakDerivStep mu Omega p (ι.compLpL p μΩ)) :
    domainTrajectoryOperator ι A u =
      (ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p μΩ (weakFDeriv (ι.compLpL p μΩ) u) +
      A.compLpL p μΩ (prev (ι.compLpL p μΩ) u) := by simp [domainTrajectoryOperator]

/-- A coefficient that is almost everywhere equal to the constant `A₀` gives the autonomous
operator `domainTrajectoryOperator ι A₀`. -/
theorem familyDomainTrajectoryOperator_of_ae_eq_const (ι : D →L[ℝ] H)
    {A : Lp (D →L[ℝ] H) ∞ μΩ} {A₀ : D →L[ℝ] H} (hA : A =ᵐ[μΩ] fun _ ↦ A₀) :
    familyDomainTrajectoryOperator (p := p) ι A = domainTrajectoryOperator ι A₀ := by
  rw [familyDomainTrajectoryOperator_def, domainTrajectoryOperator_def,
    Lp.operatorMultiplication_of_ae_eq_const hA]

/-- For the constant coefficient `A₀`, `familyDomainTrajectoryOperator` is the autonomous
operator `domainTrajectoryOperator ι A₀`. -/
@[simp] theorem familyDomainTrajectoryOperator_toLp_const (ι A₀ : D →L[ℝ] H) :
    familyDomainTrajectoryOperator (p := p) ι ((memLp_top_const (μ := μΩ) A₀).toLp _) =
      domainTrajectoryOperator ι A₀ :=
  familyDomainTrajectoryOperator_of_ae_eq_const ι (memLp_top_const A₀).coeFn_toLp

omit [CompleteSpace H] [IsFiniteMeasureOnCompacts mu] in
/-- The constant coefficient `A` acts almost everywhere as `A` along any path `x`. -/
private theorem toLp_const_apply_ae (A : D →L[ℝ] H) (x : ℝ → D) :
    (fun s ↦ (memLp_top_const (μ := μΩ) A).toLp _ s (x s)) =ᵐ[μΩ] fun s ↦ A (x s) := by
  filter_upwards [(memLp_top_const (μ := μΩ) A).coeFn_toLp] with s hs
  rw [hs]

/-- Pointwise almost-everywhere formula for `domainTrajectoryOperator`. -/
theorem domainTrajectoryOperator_apply_ae (ι A : D →L[ℝ] H)
    (u : WeakDerivStep mu Omega p (ι.compLpL p μΩ)) :
    domainTrajectoryOperator ι A u =ᵐ[μΩ]
      fun s ↦ weakFDeriv (ι.compLpL p μΩ) u s 1 + A (prev (ι.compLpL p μΩ) u s) := by
  rw [← familyDomainTrajectoryOperator_toLp_const]
  exact (familyDomainTrajectoryOperator_apply_ae ι _ u).trans
    (EventuallyEq.rfl.add (toLp_const_apply_ae A _))

/-- The operators of a coefficient `A` and of a constant `A₀` differ along a path `u` by
`(A(s) - A₀) u(s)`, almost everywhere. -/
theorem familyDomainTrajectoryOperator_sub_domainTrajectoryOperator_ae (ι : D →L[ℝ] H)
    (A : Lp (D →L[ℝ] H) ∞ μΩ) (A₀ : D →L[ℝ] H) (u : WeakDerivStep mu Omega p (ι.compLpL p μΩ)) :
    ⇑(familyDomainTrajectoryOperator ι A u - domainTrajectoryOperator ι A₀ u) =ᵐ[μΩ]
      fun s ↦ (A s - A₀) (prev (ι.compLpL p μΩ) u s) := by
  rw [← familyDomainTrajectoryOperator_toLp_const, ← sub_apply,
    familyDomainTrajectoryOperator_sub, ContinuousLinearMap.comp_apply, prevL_apply]
  filter_upwards [Lp.operatorMultiplication_ae (A - (memLp_top_const (μ := μΩ) A₀).toLp _)
      (prev (ι.compLpL p μΩ) u), Lp.coeFn_sub A ((memLp_top_const (μ := μΩ) A₀).toLp _),
    (memLp_top_const (μ := μΩ) A₀).coeFn_toLp] with s hM hsub hc
  rw [hM, hsub, Pi.sub_apply, hc]

/-- The operator norm of `domainTrajectoryOperator ι A` is at most `1 + ‖A‖`. -/
theorem norm_domainTrajectoryOperator_le (ι A : D →L[ℝ] H) :
    ‖domainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι A‖ ≤ 1 + ‖A‖ := by
  rw [← familyDomainTrajectoryOperator_toLp_const]
  exact (norm_familyDomainTrajectoryOperator_le ι _).trans
    (add_le_add_right (Lp.norm_toLp_memLp_top_const_le A) 1)

/-- Subtracting two operators over the same domain embedding cancels the derivative part. -/
theorem domainTrajectoryOperator_sub (ι A B : D →L[ℝ] H) :
    domainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι A -
      domainTrajectoryOperator ι B = ((A - B).compLpL p μΩ).comp (prevL (ι.compLpL p μΩ)) := by
  rw [← familyDomainTrajectoryOperator_toLp_const, ← familyDomainTrajectoryOperator_toLp_const,
    familyDomainTrajectoryOperator_sub, ← MemLp.toLp_sub, Lp.operatorMultiplication_of_ae_eq_const
      (T := A - B) ((memLp_top_const (μ := μΩ) A).sub (memLp_top_const B)).coeFn_toLp]

/-- Changing `A` to `B` changes `domainTrajectoryOperator ι` by at most `‖A - B‖` in norm. -/
theorem norm_domainTrajectoryOperator_sub_le (ι A B : D →L[ℝ] H) :
    ‖domainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι A -
      domainTrajectoryOperator ι B‖ ≤ ‖A - B‖ := by
  rw [← familyDomainTrajectoryOperator_toLp_const, ← familyDomainTrajectoryOperator_toLp_const]
  refine (norm_familyDomainTrajectoryOperator_sub_le ι _ _).trans ?_
  rw [← MemLp.toLp_sub]
  exact Lp.norm_toLp_memLp_top_const_le (A - B)

/-- `domainTrajectoryOperator ι` is `1`-Lipschitz in its zero-order operator `A`. -/
theorem lipschitzWith_domainTrajectoryOperator (ι : D →L[ℝ] H) :
    LipschitzWith 1 (domainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι) :=
  LipschitzWith.of_dist_le_mul fun A B ↦ by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
      norm_domainTrajectoryOperator_sub_le ι A B

/-- `domainTrajectoryOperator ι` depends continuously on its zero-order operator `A`. -/
@[fun_prop] theorem continuous_domainTrajectoryOperator (ι : D →L[ℝ] H) :
    Continuous (domainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι) :=
  (lipschitzWith_domainTrajectoryOperator ι).continuous

/-- **Invertibility is open in the coefficient.** If `∂s ∘ ι + A` is invertible, so is
`∂s ∘ ι + B` for every `B` close to `A` in operator norm. The domain need not be complete: an
invertible `∂s ∘ ι + A` makes it isomorphic to `Lᵖ(Ω, H)`. -/
theorem eventually_isInvertible_domainTrajectoryOperator {ι A : D →L[ℝ] H}
    (hA : (domainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι A).IsInvertible) :
    ∀ᶠ B in 𝓝 A,
      (domainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι B).IsInvertible := by
  have := ContinuousLinearMap.completeSpace_of_isInvertible hA
  exact ((continuous_domainTrajectoryOperator ι).tendsto A).eventually hA.eventually_nhds

/-- **Small weights.** If `∂s ∘ ι + A` is invertible, then for any `C : D →L[ℝ] H` so is
`∂s ∘ ι + (A - δ C)` for every `δ` close to `0`. For `C = ι` this is the operator `d/ds + A - δ`
into which the exponential weight `e^{δ s}` turns `d/ds + A`. -/
theorem eventually_isInvertible_domainTrajectoryOperator_sub_smul {ι A : D →L[ℝ] H}
    (hA : (domainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι A).IsInvertible)
    (C : D →L[ℝ] H) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), (domainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι
      (A - δ • C)).IsInvertible := by
  have hcont : Continuous fun δ : ℝ ↦ A - δ • C := by fun_prop
  exact (hcont.tendsto' 0 A (by simp)).eventually
    (eventually_isInvertible_domainTrajectoryOperator hA)

/-- `domainTrajectoryOperator ι A u = f` iff `(ι ∘ u)' = f - A ∘ u` weakly. -/
theorem domainTrajectoryOperator_eq_iff_hasWeakLineDerivOn (ι A : D →L[ℝ] H)
    (u : WeakDerivStep mu Omega p (ι.compLpL p μΩ)) (f : Lp H p μΩ) :
    domainTrajectoryOperator ι A u = f ↔ HasWeakLineDerivOn mu Omega
      (ι.compLpL p μΩ (prev (ι.compLpL p μΩ) u))
      (fun s ↦ f s - A (prev (ι.compLpL p μΩ) u s)) 1 := by
  have hc := (EventuallyEq.refl _ (f : ℝ → H)).sub
    (toLp_const_apply_ae (mu := mu) (Omega := Omega) A ⇑(prev (ι.compLpL p μΩ) u))
  rw [← familyDomainTrajectoryOperator_toLp_const,
    familyDomainTrajectoryOperator_eq_iff_hasWeakLineDerivOn]
  exact ⟨fun h ↦ h.congr_ae_deriv hc, fun h ↦ h.congr_ae_deriv hc.symm⟩

/-- If `x ∈ Lᵖ(Ω, D)` solves `(ι ∘ x)' = f - A ∘ x` weakly on `Ω`, `x` lifts to `u` with
`domainTrajectoryOperator ι A u = f`. -/
theorem exists_prev_eq_and_domainTrajectoryOperator_eq_of_hasWeakLineDerivOn (ι A : D →L[ℝ] H)
    {x : Lp D p μΩ} {f : Lp H p μΩ}
    (h : HasWeakLineDerivOn mu Omega (ι.compLpL p μΩ x) (fun s ↦ f s - A (x s)) 1) :
    ∃ u : WeakDerivStep mu Omega p (ι.compLpL p μΩ),
      prev (ι.compLpL p μΩ) u = x ∧ domainTrajectoryOperator ι A u = f := by
  rw [← familyDomainTrajectoryOperator_toLp_const]
  exact exists_prev_eq_and_familyDomainTrajectoryOperator_eq_of_hasWeakLineDerivOn ι _
    (h.congr_ae_deriv (EventuallyEq.rfl.sub (toLp_const_apply_ae A x)).symm)

end Banach

section Modes

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {mu : Measure ℝ} [mu.IsAddHaarMeasure] {Omega : Opens ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "μΩ" => (mu.restrict Omega)

/-- On a single mode `s ↦ w s • a`, `domainTrajectoryOperator ι A` acts as
`s ↦ w' s • ι a + w s • A a`. -/
theorem domainTrajectoryOperator_smulRightBaseW1pL_ae (ι A : D →L[ℝ] H) (a : D)
    (w : W1p mu Omega p) :
    domainTrajectoryOperator ι A (smulRightBaseW1pL ι a w) =ᵐ[μΩ]
      fun s ↦ ⟪W1p.gradient w s, (1 : ℝ)⟫_ℝ • ι a + W1p.value w s • A a := by
  filter_upwards [domainTrajectoryOperator_apply_ae ι A (smulRightBaseW1pL ι a w),
    (smulRightGradientL (ι a)).coeFn_compLpL (W1p.gradient w),
    (ContinuousLinearMap.toSpanSingleton ℝ a).coeFn_compLpL (W1p.value w)] with s hD hg hv
  rw [hD, weakFDeriv_smulRightBaseW1pL, prev_smulRightBaseW1pL, hg, hv,
    smulRightGradientL_apply, ContinuousLinearMap.toSpanSingleton_apply, map_smul]

omit [Fact (1 ≤ p)] in
/-- When `A a = 0`, the squared `L²` norm of `domainTrajectoryOperator ι A` on the scalar
test-function mode `smulRightBaseW1pL ι a (W1p.ofTestFunctionₗ mu Omega 2 φ)` is
`(∫ s, deriv φ s ^ 2 ∂mu) * ‖ι a‖ ^ 2`. -/
theorem norm_domainTrajectoryOperator_smulRightBaseW1pL_ofTestFunctionₗ_sq
    (ι A : D →L[ℝ] H) {a : D} (hAa : A a = 0) (φ : 𝓓(Omega, ℝ)) :
    ‖domainTrajectoryOperator ι A
        (smulRightBaseW1pL ι a (W1p.ofTestFunctionₗ mu Omega 2 φ))‖ ^ 2 =
      (∫ s, deriv (φ : ℝ → ℝ) s ^ 2 ∂mu) * ‖ι a‖ ^ 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq,
    integral_congr_ae (g := fun s ↦ deriv (φ : ℝ → ℝ) s ^ 2 * ‖ι a‖ ^ 2) ?_,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦ by
      simp [← fderiv_apply_one_eq_deriv, fderiv_of_notMem_tsupport ℝ fun h ↦
        hs (φ.tsupport_subset h)],
    MeasureTheory.integral_mul_const]
  filter_upwards [domainTrajectoryOperator_smulRightBaseW1pL_ae ι A a
      (W1p.ofTestFunctionₗ mu Omega 2 φ),
    gradientTestFunctionLp_apply_ae (mu := mu) 2 φ] with s h1 h2
  rw [h1]; simp only [hAa, smul_zero, add_zero, W1p.gradient_ofTestFunctionₗ, h2,
    gradient_eq_deriv', RCLike.inner_apply, RCLike.conj_to_real, one_mul, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]

/-- If `ℓ : H →L[ℝ] ℝ` satisfies `ℓ (A x) = λ * ℓ (ι x)`, projecting `u` via `toW1pL` turns
`domainTrajectoryOperator ι A u` into `u_ℓ' + λ u_ℓ`. -/
theorem compLpL_domainTrajectoryOperator_ae (ι A : D →L[ℝ] H) (ℓ : H →L[ℝ] ℝ) {lam : ℝ}
    (hℓ : ∀ x : D, ℓ (A x) = lam * ℓ (ι x)) (u : WeakDerivStep mu Omega p (ι.compLpL p μΩ)) :
    ℓ.compLpL p μΩ (domainTrajectoryOperator ι A u) =ᵐ[μΩ]
      fun s ↦ ⟪W1p.gradient (toW1pL (ι.compLpL p μΩ) ℓ u) s, (1 : ℝ)⟫_ℝ +
        lam * W1p.value (toW1pL (ι.compLpL p μΩ) ℓ u) s := by
  let base := ι.compLpL p μΩ
  filter_upwards [ℓ.coeFn_compLpL (domainTrajectoryOperator ι A u),
    domainTrajectoryOperator_apply_ae ι A u, inner_gradient_toW1pL_ae base ℓ u,
    ℓ.coeFn_compLpL (base (prev base u)), ι.coeFn_compLpL (prev base u)] with s h1 h2 hgrad hval hι
  rw [h1, h2, map_add, hℓ, value_toW1pL, hval, hι, hgrad 1]

end Modes

section Symmetric

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {ι A : D →L[ℝ] H}

private theorem inner_domainTrajectoryOperator_ofTestFunction_eq
    (e : D ≃L[ℝ] H) (hSymm : ∀ x y : D, ⟪e x, ι y⟫_ℝ = ⟪ι x, e y⟫_ℝ)
    (v : Lp H 2 μ₀) (h : H) (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    ⟪domainTrajectoryOperator ι (e : D →L[ℝ] H)
        (smulRightBaseW1pL ι (e.symm h) (W1p.ofTestFunctionₗ volume ⊤ 2 φ)), v⟫_ℝ =
      ⟪h, (∫ s, lineDeriv ℝ (φ : ℝ → ℝ) s 1 •
            (ι.compLpL 2 μ₀ ((e.symm : H →L[ℝ] D).compLpL 2 μ₀ v)) s) +
          ∫ s, (φ : ℝ → ℝ) s • v s⟫_ℝ := by
  let μ := (volume : Measure ℝ).restrict ((⊤ : Opens ℝ) : Set ℝ)
  let z := ι.compLpL 2 μ ((e.symm : H →L[ℝ] D).compLpL 2 μ v)
  have hsymm' (x y : H) : ⟪ι (e.symm x), y⟫_ℝ = ⟪x, ι (e.symm y)⟫_ℝ := by
    nth_rw 1 [← e.apply_symm_apply y]; rw [← hSymm, e.apply_symm_apply]
  have hi1 := integrable_lineDeriv_smul_of_locallyIntegrableOn
    (Lp.locallyIntegrableOn z (by norm_num)) φ 1
  have hi2 := φ.integrable_smul (Lp.locallyIntegrableOn v (by norm_num))
  rw [inner_add_right, ← integral_inner hi1, ← integral_inner hi2,
    ← integral_add (hi1.const_inner h) (hi2.const_inner h), L2.inner_def]
  refine (integral_congr_ae
    (g := fun s ↦ ⟪h, lineDeriv ℝ (φ : ℝ → ℝ) s 1 • z s⟫_ℝ + ⟪h, (φ : ℝ → ℝ) s • v s⟫_ℝ)
    ?_).trans setIntegral_univ
  let w := W1p.ofTestFunctionₗ volume ⊤ 2 φ
  filter_upwards [domainTrajectoryOperator_smulRightBaseW1pL_ae ι (e : D →L[ℝ] H) (e.symm h) w,
    testFunctionLp_apply_ae (mu := volume) 2 φ, gradientTestFunctionLp_apply_ae (mu := volume) 2 φ,
    ι.coeFn_compLpL ((e.symm : H →L[ℝ] D).compLpL 2 μ v),
    (e.symm : H →L[ℝ] D).coeFn_compLpL v] with s hD hval hgrad hι he
  have hz : z s = ι (e.symm (v s)) := by rw [hι, he, ContinuousLinearEquiv.coe_coe]
  rw [hD]; simp only [w, W1p.value_ofTestFunctionₗ, W1p.gradient_ofTestFunctionₗ]
  simp [hz, hval, hgrad, gradient_eq_deriv', inner_add_left, inner_smul_left, inner_smul_right,
    hsymm']

variable [CompleteSpace D]

/-- When `A` is `ι`-symmetric (`⟪A x, ι y⟫ = ⟪ι x, A y⟫`), `(ι ∘ u)'` and `A ∘ u` are orthogonal in
`L²(ℝ, H)`. -/
theorem inner_weakFDeriv_apply_one_compLpL_eq_zero (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ⟪(ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL 2 μ₀ (weakFDeriv (ι.compLpL 2 μ₀) u),
      A.compLpL 2 μ₀ (prev (ι.compLpL 2 μ₀) u)⟫_ℝ = 0 := by
  let μ := (volume : Measure ℝ).restrict ((⊤ : Opens ℝ) : Set ℝ)
  let base := ι.compLpL 2 μ
  let L : H →L[ℝ] StrongDual ℝ D := ((ContinuousLinearMap.compL ℝ D H ℝ).flip A).comp (innerSL ℝ)
  let B : D →L[ℝ] D →L[ℝ] ℝ := L.comp ι
  have hB : B.flip = B := by
    ext x y; simp only [ContinuousLinearMap.flip_apply, B, L, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply, innerSL_apply_apply]
    rw [real_inner_comm, hSymm x y]
  have hx : MemLp ⇑(prev base u) 2 μ := Lp.memLp (prev base u)
  let d : ℝ → H := fun s ↦ weakFDeriv base u s 1
  have hLd : MemLp (fun s ↦ L (d s)) 2 μ :=
    ((Lp.memLp (weakFDeriv base u)).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ H 1)).continuousLinearMap_comp L
  have hwB : HasWeakLineDerivOn volume ⊤ (fun s ↦ B (prev base u s)) (fun s ↦ L (d s)) 1 :=
    (((hasWeakFDerivOn_base_prev base u).hasWeakLineDerivOn 1).clm_comp L).congr_ae
      ((ι.coeFn_compLp (prev base u)).mono fun s hs ↦ by simp [B, base, hs])
  have hint0 : Integrable (fun s ↦ B (prev base u s) (prev base u s)) volume :=
    (memLp_one_iff_integrable.1 (B.memLp_of_bilin 1 hx hx)).mono_measure (by simp [μ])
  have hint1 : Integrable (fun s ↦ 2 * L (d s) (prev base u s)) volume :=
    ((memLp_one_iff_integrable.1
      ((ContinuousLinearMap.id ℝ (StrongDual ℝ D)).memLp_of_bilin 1 hLd hx)).const_mul 2)
      |>.mono_measure (by simp [μ])
  have hzero := (HasWeakLineDerivOn.bilin_self hB hwB hx hLd).integral_eq_zero_of_integrable
    hint0 hint1
  rw [MeasureTheory.integral_const_mul] at hzero
  have hint_eq : ⟪(ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL 2 μ (weakFDeriv base u),
      A.compLpL 2 μ (prev base u)⟫_ℝ = ∫ s, L (d s) (prev base u s) := by
    rw [L2.inner_def]
    refine (integral_congr_ae (g := fun s ↦ L (d s) (prev base u s)) ?_).trans (by simp [μ])
    filter_upwards [(ContinuousLinearMap.apply ℝ H (1 : ℝ)).coeFn_compLpL (weakFDeriv base u),
      A.coeFn_compLpL (prev base u)] with s hs1 hs2
    rw [hs1, hs2]; simp [L, d]
  rw [hint_eq]; linarith

/-- **Integration by parts in `W^{1,2}(ℝ, H)`.** For paths `u` and `w` of the graph space,
`⟪(ι ∘ u)', ι ∘ w⟫ = -⟪ι ∘ u, (ι ∘ w)'⟫` in `L²(ℝ, H)`. -/
theorem inner_weakFDeriv_apply_one_compLpL_eq_neg_inner
    (u w : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ⟪(ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL 2 μ₀ (weakFDeriv (ι.compLpL 2 μ₀) u),
        ι.compLpL 2 μ₀ (prev (ι.compLpL 2 μ₀) w)⟫_ℝ =
      -⟪ι.compLpL 2 μ₀ (prev (ι.compLpL 2 μ₀) u),
        (ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL 2 μ₀
          (weakFDeriv (ι.compLpL 2 μ₀) w)⟫_ℝ := by
  -- Polarize `⟪(ι ∘ z)', ι ∘ z⟫ = 0`, the case `A = ι` of the orthogonality of `(ι ∘ z)'` and
  -- `A ∘ z`, at `z = u + w`.
  have h (z : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :=
    inner_weakFDeriv_apply_one_compLpL_eq_zero (A := ι) (fun _ _ ↦ rfl) z
  have huw := h (u + w)
  simp only [← weakFDerivL_apply, ← prevL_apply, map_add, inner_add_left, inner_add_right] at huw
  simp only [weakFDerivL_apply, prevL_apply, h u, h w, zero_add, add_zero] at huw
  linarith [real_inner_comm
    ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL 2 μ₀ (weakFDeriv (ι.compLpL 2 μ₀) w))
    (ι.compLpL 2 μ₀ (prev (ι.compLpL 2 μ₀) u))]

/-- Pythagorean identity on `L²(ℝ)` for `ι`-symmetric `A`:
`‖(∂s ∘ ι + A) u‖² = ‖(ι ∘ u)'‖² + ‖A ∘ u‖²`. -/
theorem norm_domainTrajectoryOperator_sq (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ‖domainTrajectoryOperator ι A u‖ ^ 2 =
      ‖weakFDeriv (ι.compLpL 2 μ₀) u‖ ^ 2 + ‖A.compLpL 2 μ₀ (prev (ι.compLpL 2 μ₀) u)‖ ^ 2 := by
  rw [domainTrajectoryOperator_apply, norm_add_sq_real,
    inner_weakFDeriv_apply_one_compLpL_eq_zero hSymm u, mul_zero, add_zero,
    ContinuousLinearMap.compLpL_apply, ContinuousLinearMap.norm_apply_one_compLp]

/-- On `L²(ℝ)` for `ι`-symmetric `A`, `‖(ι ∘ u)'‖ ≤ ‖(∂s ∘ ι + A) u‖`. -/
theorem norm_weakFDeriv_le_norm_domainTrajectoryOperator
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ‖weakFDeriv (ι.compLpL 2 μ₀) u‖ ≤ ‖domainTrajectoryOperator ι A u‖ :=
  le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) <| by
    linarith [norm_domainTrajectoryOperator_sq hSymm u, sq_nonneg ‖A.compLpL 2 μ₀ (prev _ u)‖]

/-- On `L²(ℝ)` for `ι`-symmetric `A`, `‖A ∘ u‖ ≤ ‖(∂s ∘ ι + A) u‖`. -/
theorem norm_compLpL_prev_le_norm_domainTrajectoryOperator
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ‖A.compLpL 2 μ₀ (prev (ι.compLpL 2 μ₀) u)‖ ≤ ‖domainTrajectoryOperator ι A u‖ :=
  le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) <| by
    linarith [norm_domainTrajectoryOperator_sq hSymm u, sq_nonneg ‖weakFDeriv (ι.compLpL 2 μ₀) u‖]

/-- For `ι`-symmetric `A` satisfying `c ‖ι x‖ ≤ ‖A x‖` (`c > 0`),
`‖ι ∘ u‖_{L²(ℝ)} ≤ c⁻¹ ‖(∂s ∘ ι + A) u‖_{L²(ℝ)}`. -/
theorem norm_compLpL_le_inv_mul_norm_domainTrajectoryOperator
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ x : D, c * ‖ι x‖ ≤ ‖A x‖) (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ‖ι.compLpL 2 μ₀ (prev (ι.compLpL 2 μ₀) u)‖ ≤ c⁻¹ * ‖domainTrajectoryOperator ι A u‖ := by
  refine (Lp.norm_le_mul_norm_of_ae_le_mul (c := c⁻¹) (g := A.compLpL 2 _ (prev _ u)) ?_).trans
    (mul_le_mul_of_nonneg_left (norm_compLpL_prev_le_norm_domainTrajectoryOperator hSymm u)
      (inv_nonneg.2 hc.le))
  filter_upwards [ι.coeFn_compLpL (prev _ u), A.coeFn_compLpL (prev _ u)] with s hι hA
  exact hι ▸ hA ▸ (le_inv_mul_iff₀ hc).2 (hgap _)

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
    IsClosed ((domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).range :
      Set (Lp H 2 μ₀)) := by
  set T := domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A
  exact (T.antilipschitz_of_bound (K := ⟨max C 1, by positivity⟩)
    (norm_le_max_mul_norm_domainTrajectoryOperator hSymm hC)).isClosed_range T.uniformContinuous

private theorem eq_zero_of_mem_orthogonal_range_domainTrajectoryOperator
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hA : A.IsInvertible) {v : Lp H 2 μ₀}
    (hv : v ∈ (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).rangeᗮ) :
    v = 0 := by
  obtain ⟨e, rfl⟩ := hA
  let μ := (volume : Measure ℝ).restrict ((⊤ : Opens ℝ) : Set ℝ)
  let x := (e.symm : H →L[ℝ] D).compLpL 2 μ v
  have hweak : HasWeakLineDerivOn volume ⊤ (ι.compLpL 2 μ x) (fun s ↦ v s) 1 := by
    rw [hasWeakLineDerivOn_iff_testFunction]
    refine ⟨inferInstance, Lp.locallyIntegrableOn _ (by norm_num),
      Lp.locallyIntegrableOn v (by norm_num), fun φ ↦ add_eq_zero_iff_eq_neg.mp ?_⟩
    refine (inner_self_eq_zero (𝕜 := ℝ)).mp ?_
    rw [← inner_domainTrajectoryOperator_ofTestFunction_eq e hSymm v _ φ, real_inner_comm]
    exact (Submodule.mem_orthogonal' _ _).mp hv _ ⟨_, rfl⟩
  have hweak' : HasWeakLineDerivOn volume ⊤ (ι.compLpL 2 μ x)
      (fun s ↦ ((2 : ℝ) • v : Lp H 2 μ) s - (e : D →L[ℝ] H) (x s)) 1 := by
    refine hweak.congr_ae_deriv ?_
    filter_upwards [Lp.coeFn_smul (2 : ℝ) v, (e.symm : H →L[ℝ] D).coeFn_compLpL v] with s hsmul hs
    rw [hsmul, Pi.smul_apply, two_smul, hs, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_coe, e.apply_symm_apply, add_sub_cancel_right]
  obtain ⟨w, hwx, hDw⟩ := exists_prev_eq_and_domainTrajectoryOperator_eq_of_hasWeakLineDerivOn
    ι (e : D →L[ℝ] H) (f := (2 : ℝ) • v) hweak'
  have hAw : (e : D →L[ℝ] H).compLpL 2 μ (prev _ w) = v := by
    rw [hwx, ContinuousLinearMap.compLpL_compLpL]; simp
  have hw' : (ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL 2 μ (weakFDeriv _ w) = v := by
    have h1 := domainTrajectoryOperator_apply ι (e : D →L[ℝ] H) w
    rw [hDw, hAw, two_smul] at h1; exact add_right_cancel h1.symm
  have h0 := inner_weakFDeriv_apply_one_compLpL_eq_zero hSymm w
  rwa [hw', hAw, inner_self_eq_zero] at h0

/-- Bijectivity of `∂s ∘ ι + A` on `L²(ℝ)` when `A` is `ι`-symmetric and invertible. -/
theorem bijective_domainTrajectoryOperator (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (hA : A.IsInvertible) :
    Function.Bijective (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A) := by
  have hC := hA.norm_le_norm_inverse_mul_norm
  have := (isClosed_range_domainTrajectoryOperator hSymm hC).completeSpace_coe
  refine ⟨ContinuousLinearMap.injective_of_forall_norm_le
    (norm_le_max_mul_norm_domainTrajectoryOperator hSymm hC), LinearMap.range_eq_top.mp ?_⟩
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  exact fun _ hv ↦ eq_zero_of_mem_orthogonal_range_domainTrajectoryOperator hSymm hA hv

/-- Invertibility of `∂s ∘ ι + A` on `L²(ℝ)` when `A` is `ι`-symmetric and invertible. -/
theorem isInvertible_domainTrajectoryOperator (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (hA : A.IsInvertible) :
    (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).IsInvertible :=
  ContinuousLinearMap.isInvertible_of_surjective_of_forall_norm_le
    (bijective_domainTrajectoryOperator hSymm hA).2
    (norm_le_max_mul_norm_domainTrajectoryOperator hSymm hA.norm_le_norm_inverse_mul_norm)

/-- **The inverse bound.** On `L²(ℝ)`, for `ι`-symmetric invertible `A`,
`‖(∂s ∘ ι + A).inverse‖ ≤ max ‖A.inverse‖ 1`. -/
theorem norm_inverse_domainTrajectoryOperator_le (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (hA : A.IsInvertible) :
    ‖(domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).inverse‖ ≤
      max ‖A.inverse‖ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (ContinuousLinearMap.norm_inverse_apply_le_of_forall_norm_le
      (bijective_domainTrajectoryOperator hSymm hA).2
      (norm_le_max_mul_norm_domainTrajectoryOperator hSymm hA.norm_le_norm_inverse_mul_norm))

/-- On `L²(ℝ)`, when `A` is `ι`-symmetric and invertible, `∂s ∘ ι + A` is Fredholm. -/
theorem isFredholm_domainTrajectoryOperator (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (hA : A.IsInvertible) :
    (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).IsFredholm :=
  (isInvertible_domainTrajectoryOperator hSymm hA).isFredholm

/-- On `L²(ℝ)`, when `A` is `ι`-symmetric and invertible, `(∂s ∘ ι + A).index = 0`. -/
theorem index_domainTrajectoryOperator (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (hA : A.IsInvertible) :
    (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).index = 0 :=
  ContinuousLinearMap.index_eq_zero_of_bijective _ (bijective_domainTrajectoryOperator hSymm hA)

/-- On `L²(ℝ)`, when `ι` is injective, `A` is `ι`-symmetric, and `A.ker ≠ ⊥`, the range of
`domainTrajectoryOperator ι A` is not closed. -/
theorem not_isClosed_range_domainTrajectoryOperator_of_ker_ne_bot (hι : Function.Injective ι)
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hker : A.ker ≠ ⊥) :
    ¬ IsClosed ((domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).range :
      Set (Lp H 2 μ₀)) := by
  intro hclosed; obtain ⟨a, hAa, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hAa
  set T := domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A
  obtain ⟨K, hK⟩ := T.antilipschitz_of_injective_of_isClosed_range
    (injective_domainTrajectoryOperator_of_ker hSymm fun _ hx _ ↦
      hι (hx.trans (map_zero ι).symm)) hclosed
  obtain ⟨C, hplat⟩ := exists_forall_contDiff_plateau
  have ha_pos : 0 < ‖a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.2 ha)
  let r : ℝ := max 0 (((K : ℝ) ^ 2 * C * ‖ι a‖ ^ 2) / (2 * ‖a‖ ^ 2) + 1)
  have hr_gt : ((K : ℝ) ^ 2 * C * ‖ι a‖ ^ 2) / (2 * ‖a‖ ^ 2) < r :=
    lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  obtain ⟨ψ, hψ, hψsupp, hψ2, hψd⟩ := hplat 0 (le_max_left _ _)
  let φ : 𝓓((⊤ : Opens ℝ), ℝ) := ⟨ψ, hψ, (isCompact_closedBall 0 (r + 1)).of_isClosed_subset
    (isClosed_tsupport ψ) hψsupp, subset_univ _⟩
  let u := smulRightBaseW1pL ι a (W1p.ofTestFunctionₗ volume ⊤ 2 φ)
  have hsq : (∫ s, ψ s ^ 2) * ‖a‖ ^ 2 ≤ (K : ℝ) ^ 2 * ((∫ s, deriv ψ s ^ 2) * ‖ι a‖ ^ 2) := by
    have hφ : (φ : ℝ → ℝ) = ψ := TestFunction.coe_mk
    rw [← hφ, ← norm_prev_smulRightBaseW1pL_ofTestFunctionₗ_sq (mu := volume) ι a φ,
      ← norm_domainTrajectoryOperator_smulRightBaseW1pL_ofTestFunctionₗ_sq (mu := volume) ι A hAa φ,
      ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((norm_prev_le _ u).trans (hK.le_mul_norm (map_zero T) u)) 2
  have hhi : (K : ℝ) ^ 2 * ((∫ s, deriv ψ s ^ 2) * ‖ι a‖ ^ 2) ≤ (K : ℝ) ^ 2 * C * ‖ι a‖ ^ 2 := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hψd (sq_nonneg _)) (sq_nonneg _)
  have hlt : (K : ℝ) ^ 2 * C * ‖ι a‖ ^ 2 < 2 * r * ‖a‖ ^ 2 := by
    linarith [(div_lt_iff₀ (mul_pos zero_lt_two ha_pos)).mp hr_gt,
      show r * (2 * ‖a‖ ^ 2) = 2 * r * ‖a‖ ^ 2 by ring]
  exact hlt.not_ge ((mul_le_mul_of_nonneg_right hψ2 (sq_nonneg _)).trans (hsq.trans hhi))

/-- On `L²(ℝ)`, for injective `ι` and `ι`-symmetric index-`0` Fredholm `A`, the range of
`domainTrajectoryOperator ι A` is closed iff `A` is invertible. -/
theorem isClosed_range_domainTrajectoryOperator_iff (hι : Function.Injective ι)
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hAF : A.IsFredholm) (hAi : A.index = 0) :
    IsClosed ((domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).range :
      Set (Lp H 2 μ₀)) ↔ A.IsInvertible :=
  ⟨fun hc ↦ hAF.isInvertible_of_injective_of_index_eq_zero (LinearMap.ker_eq_bot.mp (of_not_not
    fun hker ↦ not_isClosed_range_domainTrajectoryOperator_of_ker_ne_bot hι hSymm hker hc)) hAi,
    fun hA ↦ (isInvertible_domainTrajectoryOperator hSymm hA).isFredholm.isClosed_range⟩

/-- On `L²(ℝ)`, for injective `ι` and `ι`-symmetric index-`0` Fredholm `A`,
`domainTrajectoryOperator ι A` is Fredholm iff `A` is invertible. -/
theorem isFredholm_domainTrajectoryOperator_iff (hι : Function.Injective ι)
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hAF : A.IsFredholm) (hAi : A.index = 0) :
    (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).IsFredholm ↔
      A.IsInvertible :=
  ⟨fun hF ↦ (isClosed_range_domainTrajectoryOperator_iff hι hSymm hAF hAi).mp hF.isClosed_range,
    isFredholm_domainTrajectoryOperator hSymm⟩

/-- On `L²(ℝ)`, for injective `ι` and `ι`-symmetric index-`0` Fredholm `A`,
`domainTrajectoryOperator ι A` is invertible iff `A` is invertible. -/
theorem isInvertible_domainTrajectoryOperator_iff (hι : Function.Injective ι)
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hAF : A.IsFredholm) (hAi : A.index = 0) :
    (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).IsInvertible ↔
      A.IsInvertible :=
  ⟨fun hT ↦ (isFredholm_domainTrajectoryOperator_iff hι hSymm hAF hAi).mp hT.isFredholm,
    isInvertible_domainTrajectoryOperator hSymm⟩

end Symmetric

end TauCeti.WeakDerivStep
