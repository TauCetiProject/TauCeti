/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.BoundaryValue.Sobolev
public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.Fredholm
import TauCeti.Analysis.ODE.BoundaryValue.Rellich
import TauCeti.Analysis.ODE.BoundaryValue.Symmetric
import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.IndexLocalization
import TauCeti.MeasureTheory.Function.Lp.ContinuousLinearEquiv

/-!
# The linearized Floer operator on a strip with Lagrangian boundary conditions

Let `X` be a finite-dimensional real inner product space with an invertible skew-adjoint operator
`J`, such as `ℂⁿ` with multiplication by `i`, and let `F₀` and `F₁` be subspaces of `X` which are
isotropic for `ω(u, v) = ⟪J u, v⟫`, such as two Lagrangian subspaces. In a unitary trivialization
along a strip `u : ℝ × [0, 1] → M` with boundary on two Lagrangians, the linearized Floer operator
is

`ξ ↦ ∂ₛξ + J (∂ₜξ - S(s) ξ)`, `ξ(s, 0) ∈ F₀`, `ξ(s, 1) ∈ F₁`,

for a family `S(s)` of coefficients on `[0, 1]`. This file realizes it on the common domain of
Robbin and Salamon: for each `s`, `J (∂ₜ - S(s))` is the boundary value operator
`TauCeti.PathSobolev.boundaryValueOperator F₀ F₁ (S s)` followed by pointwise multiplication by
`J`, from the Sobolev space `TauCeti.PathSobolev.H1 F₀ F₁` of paths `[0, 1] → X` with boundary
values in `F₀` and `F₁` to `L²((0, 1], X)`, and the strip operator is
`TauCeti.WeakDerivStep.familyDomainTrajectoryOperator (TauCeti.PathSobolev.valueL F₀ F₁) AL`
for the `L∞` class `AL` of this family, acting on `L²(ℝ, H1 F₀ F₁) ∩ W^{1,2}(ℝ, L²((0, 1], X))`.
In the convention `∂ₛ - A(s)` of Robbin and Salamon, `A(s) = -J (∂ₜ - S(s))`.

The coefficients `S(s)` are classes in `L∞((0, 1], X →L[ℝ] X)` depending continuously on `s`,
with limits `S₋` at `-∞` and `S₊` at `∞`, the linearized Hamiltonian vector fields along the chords
at the two ends of the strip. When `S₋` and `S₊` are `J`-symmetric,
`⟪S± t u, J v⟫ = ⟪J u, S± t v⟫`, and the chords are nondegenerate, that is, the boundary value
operators of `S₋` and `S₊` are invertible
(`TauCeti.PathSobolev.isInvertible_boundaryValueOperator_iff`), the hypotheses of the Fredholm
theory of `TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator` hold:

* the value map `H1 F₀ F₁ → L²` is compact, by Rellich's theorem on `[0, 1]`
  (`TauCeti.PathSobolev.isCompactOperator_valueL`);
* the limits `J (∂ₜ - S±)` are symmetric through the value map
  (`TauCeti.PathSobolev.inner_compLpL_comp_boundaryValueOperator_valueL`) and invertible
  (`ContinuousLinearMap.IsInvertible.compLpL`);
* the family converges to its limits, and differs from `J (∂ₜ - S₊)` by the multiplication
  operator `-J (S(s) - S₊)`, which is bounded through the value map
  (`TauCeti.PathSobolev.norm_compLpL_comp_boundaryValueOperator_sub_apply_le`).

## Main results

* `TauCeti.PathSobolev.isInvertible_domainTrajectoryOperator_valueL`: the stationary strip
  operator over a nondegenerate chord is an isomorphism.
* `TauCeti.PathSobolev.isFredholm_familyDomainTrajectoryOperator_valueL`: the strip operator
  between two nondegenerate chords is Fredholm.
* `TauCeti.PathSobolev.index_familyDomainTrajectoryOperator_valueL_eq`: its index depends only
  on the two end chords.
* `TauCeti.PathSobolev.index_familyDomainTrajectoryOperator_valueL_eq_add`: the index is additive
  under catenation of strips.
* `TauCeti.PathSobolev.index_familyDomainTrajectoryOperator_valueL_eq_zero_of_forall_isInvertible`:
  a strip along which every chord is nondegenerate has index zero.

## References

* A. Floer, *Morse theory for Lagrangian intersections*, J. Differential Geom. **28** (1988),
  513–547 (the linearized operator on strips with Lagrangian boundary conditions).
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33 (the Fredholm theory of `∂ₛ - A(s)` over a common domain, §3, and its
  application to Cauchy–Riemann operators on strips with Lagrangian boundary conditions).
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal RealInnerProductSpace Topology NNReal

namespace TauCeti

namespace PathSobolev

local notation "μ₁" => (volume.restrict (Ioc (0 : ℝ) 1))

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

variable {X : Type*} [NormedAddCommGroup X]

/-! ### Dependence on the coefficient -/

section Coefficient

variable [NormedSpace ℝ X] {F₀ F₁ : Submodule ℝ X} {J : X →L[ℝ] X}

/-- Two operators `J (d/dt - A)` and `J (d/dt - A')` differ by the multiplication operator
`-J (A - A')`, so their difference is bounded through the value map:
`‖J (d/dt - A) x - J (d/dt - A') x‖ ≤ ‖J‖ ‖A - A'‖ ‖x‖_{L²}`. -/
theorem norm_compLpL_comp_boundaryValueOperator_sub_apply_le (J : X →L[ℝ] X)
    (A A' : Lp (X →L[ℝ] X) ∞ μ₁) (x : H1 F₀ F₁) :
    ‖((J.compLpL 2 μ₁).comp (boundaryValueOperator F₀ F₁ A) -
        (J.compLpL 2 μ₁).comp (boundaryValueOperator F₀ F₁ A')) x‖ ≤
      ‖J‖ * ‖A - A'‖ * ‖valueL F₀ F₁ x‖ := by
  have h : ((J.compLpL 2 μ₁).comp (boundaryValueOperator F₀ F₁ A) -
      (J.compLpL 2 μ₁).comp (boundaryValueOperator F₀ F₁ A')) x =
      -J.compLpL 2 μ₁ (Lp.operatorMultiplication 2 (A - A') (valueL F₀ F₁ x)) := by
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      boundaryValueOperator_apply, map_sub]
    abel
  rw [h, norm_neg, mul_assoc]
  exact ((J.compLpL 2 μ₁).le_of_opNorm_le J.norm_compLpL_le _).trans
    (by gcongr; exact Lp.norm_operatorMultiplication_apply_le _ _)

/-- The operator `J (d/dt - A)` depends Lipschitz continuously on the coefficient `A` in `L∞`. -/
theorem lipschitzWith_compLpL_comp_boundaryValueOperator (J : X →L[ℝ] X) :
    LipschitzWith (‖J‖₊ * ‖valueL F₀ F₁‖₊)
      fun A : Lp (X →L[ℝ] X) ∞ μ₁ ↦ (J.compLpL 2 μ₁).comp (boundaryValueOperator F₀ F₁ A) := by
  refine LipschitzWith.of_dist_le_mul fun A A' ↦ ?_
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul, coe_nnNorm, coe_nnNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ ?_
  calc _ ≤ ‖J‖ * ‖A - A'‖ * ‖valueL F₀ F₁ x‖ :=
        norm_compLpL_comp_boundaryValueOperator_sub_apply_le J A A' x
    _ ≤ ‖J‖ * ‖A - A'‖ * (‖valueL F₀ F₁‖ * ‖x‖) := by
        gcongr
        exact (valueL F₀ F₁).le_opNorm x
    _ = ‖J‖ * ‖valueL F₀ F₁‖ * ‖A - A'‖ * ‖x‖ := by ring

/-- The family `s ↦ J (d/dt - S(s))` of a continuous coefficient path differs from
`J (d/dt - S₊)` by operators bounded through the value map on every bounded interval. -/
private theorem forall_exists_norm_sub_apply_le {S : ℝ → Lp (X →L[ℝ] X) ∞ μ₁}
    (hS : Continuous S) (Stop : Lp (X →L[ℝ] X) ∞ μ₁) (T : ℝ) :
    ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x : H1 F₀ F₁,
      ‖((J.compLpL 2 μ₁).comp (boundaryValueOperator F₀ F₁ (S s)) -
        (J.compLpL 2 μ₁).comp (boundaryValueOperator F₀ F₁ Stop)) x‖ ≤
        c * ‖valueL F₀ F₁ x‖ := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    (hS.sub continuous_const).continuousOn
  refine ⟨‖J‖ * M, Eventually.of_forall fun s hs x ↦ ?_⟩
  exact (norm_compLpL_comp_boundaryValueOperator_sub_apply_le J _ _ x).trans
    (by gcongr; exact hM s (Ioo_subset_Icc_self hs))

/-- The family `s ↦ J (d/dt - S(s))` converges to `J (d/dt - S₀)` when `S(s)` converges to `S₀`. -/
private theorem tendsto_compLpL_comp_boundaryValueOperator {S : ℝ → Lp (X →L[ℝ] X) ∞ μ₁}
    {l : Filter ℝ} {S₀ : Lp (X →L[ℝ] X) ∞ μ₁} (h : Tendsto S l (𝓝 S₀)) :
    Tendsto (fun s ↦ (J.compLpL 2 μ₁).comp (boundaryValueOperator F₀ F₁ (S s))) l
      (𝓝 ((J.compLpL 2 μ₁).comp (boundaryValueOperator F₀ F₁ S₀))) :=
  ((lipschitzWith_compLpL_comp_boundaryValueOperator (F₀ := F₀) (F₁ := F₁) J).continuous.tendsto
    S₀).comp h

end Coefficient

/-! ### The strip operator -/

variable [InnerProductSpace ℝ X] {F₀ F₁ : Submodule ℝ X} {J : X →L[ℝ] X}

/-- **The stationary strip operator over a nondegenerate chord is an isomorphism.** Let `J` be
invertible and skew-adjoint, let `F₀` and `F₁` be isotropic for `⟪J ·, ·⟫`, and let the
coefficient `A` be `J`-symmetric with uniquely solvable boundary value problem `w' - A w = f`,
`w 0 ∈ F₀`, `w 1 ∈ F₁`. Then `ξ ↦ ∂ₛξ + J (∂ₜξ - A ξ)` is an isomorphism from
`L²(ℝ, H1 F₀ F₁) ∩ W^{1,2}(ℝ, L²((0, 1], X))` onto `L²(ℝ, L²((0, 1], X))`. -/
theorem isInvertible_domainTrajectoryOperator_valueL [CompleteSpace X]
    (hJ : ∀ u v : X, ⟪J u, v⟫ = -⟪u, J v⟫) (hJinv : J.IsInvertible)
    (hF₀ : ∀ u ∈ F₀, ∀ v ∈ F₀, ⟪J u, v⟫ = 0) (hF₁ : ∀ u ∈ F₁, ∀ v ∈ F₁, ⟪J u, v⟫ = 0)
    {A : Lp (X →L[ℝ] X) ∞ μ₁}
    (hSymm : ∀ᵐ t ∂μ₁, ∀ u v : X, ⟪A t u, J v⟫ = ⟪J u, A t v⟫)
    (hA : (boundaryValueOperator F₀ F₁ A).IsInvertible) :
    (WeakDerivStep.domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2)
      (valueL F₀ F₁) ((J.compLpL 2 μ₁).comp (boundaryValueOperator F₀ F₁ A))).IsInvertible :=
  WeakDerivStep.isInvertible_domainTrajectoryOperator
    (inner_compLpL_comp_boundaryValueOperator_valueL hJ hF₀ hF₁ hSymm)
    ((hJinv.compLpL 2 μ₁).comp hA)

variable [FiniteDimensional ℝ X]

local instance : CompleteSpace X := FiniteDimensional.completeSpace ℝ X

/-- **The strip operator between two nondegenerate chords is Fredholm.** Let `J` be invertible
and skew-adjoint, and let `F₀` and `F₁` be isotropic for `⟪J ·, ·⟫`. Let `S(s)` be a continuous
path of coefficients in `L∞((0, 1], X →L[ℝ] X)` converging to `J`-symmetric coefficients `S₋` at
`-∞` and `S₊` at `∞` whose boundary value problems are uniquely solvable, and let `AL` be the
`L∞` class of `s ↦ J (d/dt - S(s))`. Then `ξ ↦ ∂ₛξ + J (∂ₜξ - S(s) ξ)` is a Fredholm operator
from `L²(ℝ, H1 F₀ F₁) ∩ W^{1,2}(ℝ, L²((0, 1], X))` to `L²(ℝ, L²((0, 1], X))`. -/
theorem isFredholm_familyDomainTrajectoryOperator_valueL
    (hJ : ∀ u v : X, ⟪J u, v⟫ = -⟪u, J v⟫) (hJinv : J.IsInvertible)
    (hF₀ : ∀ u ∈ F₀, ∀ v ∈ F₀, ⟪J u, v⟫ = 0) (hF₁ : ∀ u ∈ F₁, ∀ v ∈ F₁, ⟪J u, v⟫ = 0)
    {S : ℝ → Lp (X →L[ℝ] X) ∞ μ₁} (hS : Continuous S) {Sbot Stop : Lp (X →L[ℝ] X) ∞ μ₁}
    (hbot : Tendsto S atBot (𝓝 Sbot)) (htop : Tendsto S atTop (𝓝 Stop))
    (hSymmbot : ∀ᵐ t ∂μ₁, ∀ u v : X, ⟪Sbot t u, J v⟫ = ⟪J u, Sbot t v⟫)
    (hSymmtop : ∀ᵐ t ∂μ₁, ∀ u v : X, ⟪Stop t u, J v⟫ = ⟪J u, Stop t v⟫)
    (hBbot : (boundaryValueOperator F₀ F₁ Sbot).IsInvertible)
    (hBtop : (boundaryValueOperator F₀ F₁ Stop).IsInvertible)
    {AL : Lp (H1 F₀ F₁ →L[ℝ] Lp X 2 μ₁) ∞ μ₀}
    (hAL : AL =ᵐ[μ₀] fun s ↦ (J.compLpL 2 μ₁).comp (boundaryValueOperator F₀ F₁ (S s))) :
    (WeakDerivStep.familyDomainTrajectoryOperator (p := 2) (valueL F₀ F₁) AL).IsFredholm :=
  WeakDerivStep.isFredholm_familyDomainTrajectoryOperator (isCompactOperator_valueL (F₀ := F₀))
    (inner_compLpL_comp_boundaryValueOperator_valueL hJ hF₀ hF₁ hSymmbot)
    ((hJinv.compLpL 2 μ₁).comp hBbot)
    (inner_compLpL_comp_boundaryValueOperator_valueL hJ hF₀ hF₁ hSymmtop)
    ((hJinv.compLpL 2 μ₁).comp hBtop) hAL
    (tendsto_compLpL_comp_boundaryValueOperator hbot)
    (tendsto_compLpL_comp_boundaryValueOperator htop)
    (forall_exists_norm_sub_apply_le hS Stop)

/-- **The index of a strip operator depends only on its end chords.** Under the hypotheses of
`TauCeti.PathSobolev.isFredholm_familyDomainTrajectoryOperator_valueL`, two continuous coefficient
paths `S` and `S'` with the same limits `S₋` at `-∞` and `S₊` at `∞` give strip operators
`ξ ↦ ∂ₛξ + J (∂ₜξ - S(s) ξ)` and `ξ ↦ ∂ₛξ + J (∂ₜξ - S'(s) ξ)` of the same Fredholm index. -/
theorem index_familyDomainTrajectoryOperator_valueL_eq
    (hJ : ∀ u v : X, ⟪J u, v⟫ = -⟪u, J v⟫) (hJinv : J.IsInvertible)
    (hF₀ : ∀ u ∈ F₀, ∀ v ∈ F₀, ⟪J u, v⟫ = 0) (hF₁ : ∀ u ∈ F₁, ∀ v ∈ F₁, ⟪J u, v⟫ = 0)
    {Sbot Stop : Lp (X →L[ℝ] X) ∞ μ₁}
    (hSymmbot : ∀ᵐ t ∂μ₁, ∀ u v : X, ⟪Sbot t u, J v⟫ = ⟪J u, Sbot t v⟫)
    (hSymmtop : ∀ᵐ t ∂μ₁, ∀ u v : X, ⟪Stop t u, J v⟫ = ⟪J u, Stop t v⟫)
    (hBbot : (boundaryValueOperator F₀ F₁ Sbot).IsInvertible)
    (hBtop : (boundaryValueOperator F₀ F₁ Stop).IsInvertible)
    {S S' : ℝ → Lp (X →L[ℝ] X) ∞ μ₁} (hS : Continuous S) (hbot : Tendsto S atBot (𝓝 Sbot))
    (htop : Tendsto S atTop (𝓝 Stop)) (hS' : Continuous S') (hbot' : Tendsto S' atBot (𝓝 Sbot))
    (htop' : Tendsto S' atTop (𝓝 Stop)) {AL AL' : Lp (H1 F₀ F₁ →L[ℝ] Lp X 2 μ₁) ∞ μ₀}
    (hAL : AL =ᵐ[μ₀] fun s ↦ (J.compLpL 2 μ₁).comp (boundaryValueOperator F₀ F₁ (S s)))
    (hAL' : AL' =ᵐ[μ₀] fun s ↦ (J.compLpL 2 μ₁).comp (boundaryValueOperator F₀ F₁ (S' s))) :
    (WeakDerivStep.familyDomainTrajectoryOperator (p := 2) (valueL F₀ F₁) AL).index =
      (WeakDerivStep.familyDomainTrajectoryOperator (p := 2) (valueL F₀ F₁) AL').index :=
  WeakDerivStep.index_familyDomainTrajectoryOperator_eq (isCompactOperator_valueL (F₀ := F₀))
    (inner_compLpL_comp_boundaryValueOperator_valueL hJ hF₀ hF₁ hSymmbot)
    ((hJinv.compLpL 2 μ₁).comp hBbot)
    (inner_compLpL_comp_boundaryValueOperator_valueL hJ hF₀ hF₁ hSymmtop)
    ((hJinv.compLpL 2 μ₁).comp hBtop) hAL
    (tendsto_compLpL_comp_boundaryValueOperator hbot)
    (tendsto_compLpL_comp_boundaryValueOperator htop)
    (forall_exists_norm_sub_apply_le hS Stop) hAL'
    (tendsto_compLpL_comp_boundaryValueOperator hbot')
    (tendsto_compLpL_comp_boundaryValueOperator htop')
    (forall_exists_norm_sub_apply_le hS' Stop)

/-- **Catenation of strips adds indices.** Let `S₀`, `S₁` and `S₂` be `J`-symmetric coefficients
with uniquely solvable boundary value problems, the chords at the ends of three strips: a
continuous coefficient path `S` from `S₀` to `S₁`, a path `S'` from `S₁` to `S₂`, and a path `S''`
from `S₀` to `S₂`. Then the index of the strip operator of `S''` is the sum of those of `S` and
`S'`. -/
theorem index_familyDomainTrajectoryOperator_valueL_eq_add
    (hJ : ∀ u v : X, ⟪J u, v⟫ = -⟪u, J v⟫) (hJinv : J.IsInvertible)
    (hF₀ : ∀ u ∈ F₀, ∀ v ∈ F₀, ⟪J u, v⟫ = 0) (hF₁ : ∀ u ∈ F₁, ∀ v ∈ F₁, ⟪J u, v⟫ = 0)
    {S₀ S₁ S₂ : Lp (X →L[ℝ] X) ∞ μ₁}
    (hSymm₀ : ∀ᵐ t ∂μ₁, ∀ u v : X, ⟪S₀ t u, J v⟫ = ⟪J u, S₀ t v⟫)
    (hSymm₁ : ∀ᵐ t ∂μ₁, ∀ u v : X, ⟪S₁ t u, J v⟫ = ⟪J u, S₁ t v⟫)
    (hSymm₂ : ∀ᵐ t ∂μ₁, ∀ u v : X, ⟪S₂ t u, J v⟫ = ⟪J u, S₂ t v⟫)
    (hB₀ : (boundaryValueOperator F₀ F₁ S₀).IsInvertible)
    (hB₁ : (boundaryValueOperator F₀ F₁ S₁).IsInvertible)
    (hB₂ : (boundaryValueOperator F₀ F₁ S₂).IsInvertible)
    {S S' S'' : ℝ → Lp (X →L[ℝ] X) ∞ μ₁}
    (hS : Continuous S) (hbot : Tendsto S atBot (𝓝 S₀)) (htop : Tendsto S atTop (𝓝 S₁))
    (hS' : Continuous S') (hbot' : Tendsto S' atBot (𝓝 S₁)) (htop' : Tendsto S' atTop (𝓝 S₂))
    (hS'' : Continuous S'') (hbot'' : Tendsto S'' atBot (𝓝 S₀))
    (htop'' : Tendsto S'' atTop (𝓝 S₂)) {AL AL' AL'' : Lp (H1 F₀ F₁ →L[ℝ] Lp X 2 μ₁) ∞ μ₀}
    (hAL : AL =ᵐ[μ₀] fun s ↦ (J.compLpL 2 μ₁).comp (boundaryValueOperator F₀ F₁ (S s)))
    (hAL' : AL' =ᵐ[μ₀] fun s ↦ (J.compLpL 2 μ₁).comp (boundaryValueOperator F₀ F₁ (S' s)))
    (hAL'' : AL'' =ᵐ[μ₀] fun s ↦ (J.compLpL 2 μ₁).comp (boundaryValueOperator F₀ F₁ (S'' s))) :
    (WeakDerivStep.familyDomainTrajectoryOperator (p := 2) (valueL F₀ F₁) AL'').index =
      (WeakDerivStep.familyDomainTrajectoryOperator (p := 2) (valueL F₀ F₁) AL).index +
        (WeakDerivStep.familyDomainTrajectoryOperator (p := 2) (valueL F₀ F₁) AL').index :=
  WeakDerivStep.index_familyDomainTrajectoryOperator_eq_add (isCompactOperator_valueL (F₀ := F₀))
    (inner_compLpL_comp_boundaryValueOperator_valueL hJ hF₀ hF₁ hSymm₀)
    ((hJinv.compLpL 2 μ₁).comp hB₀)
    (inner_compLpL_comp_boundaryValueOperator_valueL hJ hF₀ hF₁ hSymm₁)
    ((hJinv.compLpL 2 μ₁).comp hB₁)
    (inner_compLpL_comp_boundaryValueOperator_valueL hJ hF₀ hF₁ hSymm₂)
    ((hJinv.compLpL 2 μ₁).comp hB₂)
    ⟨‖J‖ * ‖S₁ - S₂‖, norm_compLpL_comp_boundaryValueOperator_sub_apply_le J S₁ S₂⟩
    hAL (tendsto_compLpL_comp_boundaryValueOperator hbot)
    (tendsto_compLpL_comp_boundaryValueOperator htop) (forall_exists_norm_sub_apply_le hS S₁)
    hAL' (tendsto_compLpL_comp_boundaryValueOperator hbot')
    (tendsto_compLpL_comp_boundaryValueOperator htop') (forall_exists_norm_sub_apply_le hS' S₂)
    hAL'' (tendsto_compLpL_comp_boundaryValueOperator hbot'')
    (tendsto_compLpL_comp_boundaryValueOperator htop'') (forall_exists_norm_sub_apply_le hS'' S₂)

/-- **A strip along nondegenerate chords has index zero.** If every coefficient `S(s)` of a
continuous path is `J`-symmetric with uniquely solvable boundary value problem, and so are its
limits `S₋` at `-∞` and `S₊` at `∞`, then the strip operator `ξ ↦ ∂ₛξ + J (∂ₜξ - S(s) ξ)` has
index zero. -/
theorem index_familyDomainTrajectoryOperator_valueL_eq_zero_of_forall_isInvertible
    (hJ : ∀ u v : X, ⟪J u, v⟫ = -⟪u, J v⟫) (hJinv : J.IsInvertible)
    (hF₀ : ∀ u ∈ F₀, ∀ v ∈ F₀, ⟪J u, v⟫ = 0) (hF₁ : ∀ u ∈ F₁, ∀ v ∈ F₁, ⟪J u, v⟫ = 0)
    {S : ℝ → Lp (X →L[ℝ] X) ∞ μ₁} (hS : Continuous S)
    (hSymm : ∀ s, ∀ᵐ t ∂μ₁, ∀ u v : X, ⟪S s t u, J v⟫ = ⟪J u, S s t v⟫)
    (hB : ∀ s, (boundaryValueOperator F₀ F₁ (S s)).IsInvertible)
    {Sbot Stop : Lp (X →L[ℝ] X) ∞ μ₁} (hbot : Tendsto S atBot (𝓝 Sbot))
    (htop : Tendsto S atTop (𝓝 Stop)) (hBbot : (boundaryValueOperator F₀ F₁ Sbot).IsInvertible)
    (hBtop : (boundaryValueOperator F₀ F₁ Stop).IsInvertible)
    {AL : Lp (H1 F₀ F₁ →L[ℝ] Lp X 2 μ₁) ∞ μ₀}
    (hAL : AL =ᵐ[μ₀] fun s ↦ (J.compLpL 2 μ₁).comp (boundaryValueOperator F₀ F₁ (S s))) :
    (WeakDerivStep.familyDomainTrajectoryOperator (p := 2) (valueL F₀ F₁) AL).index = 0 :=
  WeakDerivStep.index_familyDomainTrajectoryOperator_eq_zero_of_forall_isInvertible
    (isCompactOperator_valueL (F₀ := F₀))
    ((lipschitzWith_compLpL_comp_boundaryValueOperator J).continuous.comp hS)
    (fun s ↦ inner_compLpL_comp_boundaryValueOperator_valueL hJ hF₀ hF₁ (hSymm s))
    (fun s ↦ (hJinv.compLpL 2 μ₁).comp (hB s))
    ((hJinv.compLpL 2 μ₁).comp hBbot)
    ((hJinv.compLpL 2 μ₁).comp hBtop) hAL
    (tendsto_compLpL_comp_boundaryValueOperator hbot)
    (tendsto_compLpL_comp_boundaryValueOperator htop)
    (forall_exists_norm_sub_apply_le hS Stop)

end PathSobolev

end TauCeti
