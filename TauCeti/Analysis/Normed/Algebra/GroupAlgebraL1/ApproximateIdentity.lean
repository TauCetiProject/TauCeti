/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Character.ApproximateUnit
public import TauCeti.Analysis.Normed.Algebra.GroupAlgebraL1.Basic
public import TauCeti.MeasureTheory.Group.Convolution.Kernel

/-!
# Chosen approximate identity on the `L¹` group algebra

For a locally compact group `G` with a left Haar measure `μ` and an `RCLike` scalar field `𝕜`
(`ℝ` or `ℂ`), this file packages the shrinking-neighborhood continuous compactly supported kernels
of `TauCeti.MeasureTheory.Group.Convolution.Kernel` as a canonical net
`GroupAlgebraL1.approximateIdentity 𝕜 μ : OpenNhdsOf (1 : G) → GroupAlgebraL1 𝕜 μ` indexed by open
identity neighborhoods ordered by reverse inclusion (`Filter.atBot`), with no countability,
metrizability, or `σ`-finiteness assumption on `G` or `μ`:

* **Kernel properties (`ofConv_approximateIdentity_ae_eq`, `memLp_approximateIdentity`,
  `norm_approximateIdentity`):** Each `u_U` is represented almost everywhere by the nonnegative
  continuous compactly supported function `x ↦ (μ.approximateIdentity U x : 𝕜)` supported inside
  `U`, belongs to `Lᵖ(G, μ; 𝕜)` for every `p : ℝ≥0∞` (in particular `L¹ ∩ L²`), and satisfies
  `‖u_U‖ = 1`.
* **Two-sided convergence (`tendsto_approximateIdentity_mul`, `tendsto_mul_approximateIdentity`,
  `isApproximateUnit_map_approximateIdentity`):** When `μ` is inner regular for compact sets of
  finite measure, `u_U * f → f` in `GroupAlgebraL1 𝕜 μ`; when `μ` is regular, `f * u_U → f` as
  well, so `Filter.atBot.map (approximateIdentity 𝕜 μ)` is a norm-one two-sided approximate unit.
  Applying the isometric anti-automorphism `star` shows that `star (u_U)` is likewise a norm-one
  two-sided approximate identity.
* **Nonunital characters (`tendsto_nonUnitalAlgHom_approximateIdentity`,
  `norm_nonUnitalAlgHom_toContinuousLinearMap`):** Every nonzero algebraic `𝕜`-linear character
  `φ : GroupAlgebraL1 𝕜 μ →ₙₐ[𝕜] 𝕜` is automatically continuous, satisfies `φ u_U → 1` along
  `atBot`, and has operator norm `‖φ.toContinuousLinearMap‖ = 1`.
* **Nondegeneracy (`instFaithfulSMul`, `instFaithfulSMulMulOpposite`):** When `μ` is regular,
  `GroupAlgebraL1 𝕜 μ` has zero left and right annihilators.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., §VII.9, Propositions 9.3–9.6.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., Proposition 2.42.
* V. Runde, *Lectures on Amenability*, Lecture Notes in Mathematics 1774, Appendix A.
-/

public section

noncomputable section

open Filter MeasureTheory MeasureTheory.Measure TopologicalSpace Topology
open scoped ENNReal

namespace TauCeti.GroupAlgebraL1

/-! ### Shrinking-neighborhood kernels in `GroupAlgebraL1` -/

section ChosenKernels

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

variable (𝕜 : Type*) [RCLike 𝕜] (μ : Measure G) [μ.IsHaarMeasure]

/-- **Chosen approximate identity** of `GroupAlgebraL1 𝕜 μ`, indexed by all open neighborhoods
`U : OpenNhdsOf (1 : G)` of the identity (ordered by inclusion, with convergence along
`Filter.atBot`). Each `approximateIdentity 𝕜 μ U` is the `L¹` class of the nonnegative continuous
compactly supported function `x ↦ (μ.approximateIdentity U x : 𝕜)` supported inside `U`. -/
def approximateIdentity (U : OpenNhdsOf (1 : G)) : GroupAlgebraL1 𝕜 μ :=
  toConv (μ.approximateIdentityL1 𝕜 U)

variable {𝕜 μ}

@[simp]
theorem ofConv_approximateIdentity (U : OpenNhdsOf (1 : G)) :
    (approximateIdentity 𝕜 μ U).ofConv = μ.approximateIdentityL1 𝕜 U :=
  (rfl)

/-- `approximateIdentity 𝕜 μ U` is represented `μ`-almost everywhere by the continuous compactly
supported function `x ↦ (μ.approximateIdentity U x : 𝕜)`. -/
theorem ofConv_approximateIdentity_ae_eq (U : OpenNhdsOf (1 : G)) :
    (approximateIdentity 𝕜 μ U).ofConv =ᵐ[μ] fun x => (μ.approximateIdentity U x : 𝕜) :=
  μ.coeFn_approximateIdentityL1 U

/-- The continuous representative `x ↦ (μ.approximateIdentity U x : 𝕜)` of
`approximateIdentity 𝕜 μ U` belongs to `Lᵖ(G, μ; 𝕜)` for every exponent `p : ℝ≥0∞` (in particular
to `L¹ ∩ L²`). -/
theorem memLp_approximateIdentity (U : OpenNhdsOf (1 : G)) (p : ℝ≥0∞) :
    MemLp (fun x => (μ.approximateIdentity U x : 𝕜)) p μ :=
  μ.memLp_ofReal_approximateIdentity 𝕜 U p

/-- Every kernel in `approximateIdentity 𝕜 μ` has `L¹` norm equal to `1`. -/
@[simp]
theorem norm_approximateIdentity (U : OpenNhdsOf (1 : G)) :
    ‖approximateIdentity 𝕜 μ U‖ = 1 := by
  rw [← norm_ofConv, ofConv_approximateIdentity, μ.norm_approximateIdentityL1]

theorem approximateIdentity_ne_zero (U : OpenNhdsOf (1 : G)) :
    approximateIdentity 𝕜 μ U ≠ 0 := by
  intro h
  have h1 : ‖approximateIdentity 𝕜 μ U‖ = 0 := by rw [h, norm_zero]
  rw [norm_approximateIdentity] at h1
  exact one_ne_zero h1

instance instNontrivial : Nontrivial (GroupAlgebraL1 𝕜 μ) :=
  ⟨⟨approximateIdentity 𝕜 μ ⊤, 0, approximateIdentity_ne_zero ⊤⟩⟩

/-- Each kernel `approximateIdentity 𝕜 μ U` vanishes `μ`-almost everywhere outside `U`. -/
theorem approximateIdentity_ae_eq_zero (U : OpenNhdsOf (1 : G)) :
    ∀ᵐ x ∂μ, x ∉ U → (approximateIdentity 𝕜 μ U).ofConv x = 0 :=
  μ.approximateIdentityL1_ae_eq_zero U

/-- Along `atBot` on open identity neighborhoods, `approximateIdentity 𝕜 μ U` eventually vanishes
`μ`-almost everywhere outside any prescribed neighborhood `S ∈ 𝓝 1`. -/
theorem eventually_approximateIdentity_ae_eq_zero {S : Set G} (hS : S ∈ 𝓝 (1 : G)) :
    ∀ᶠ U : OpenNhdsOf (1 : G) in atBot, ∀ᵐ x ∂μ,
      x ∉ S → (approximateIdentity 𝕜 μ U).ofConv x = 0 :=
  μ.eventually_approximateIdentityL1_ae_eq_zero hS

end ChosenKernels

/-! ### Left approximate identity and operator norm of nonunital characters -/

section LeftApproximateIdentity

variable {G 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.InnerRegularCompactLTTop] [RCLike 𝕜]

/-- **Left approximate identity.** Along `Filter.atBot` on open identity neighborhoods,
`approximateIdentity 𝕜 μ U * f → f` in `GroupAlgebraL1 𝕜 μ` for every `f`. -/
theorem tendsto_approximateIdentity_mul (f : GroupAlgebraL1 𝕜 μ) :
    Tendsto (fun U => approximateIdentity 𝕜 μ U * f) atBot (𝓝 f) := by
  refine (((linearIsometryEquiv 𝕜 𝕜 μ).symm.continuous.tendsto f.ofConv).comp
    (μ.tendsto_approximateIdentityL1_convolutionL (𝕜 := 𝕜) ENNReal.one_ne_top f.ofConv)).congr
    fun U => ?_
  rw [Function.comp_apply, linearIsometryEquiv_symm_apply, ← ofConv_approximateIdentity,
    ← ofConv_mul, toConv_ofConv]

/-- Every nonzero algebraic character `φ : GroupAlgebraL1 𝕜 μ →ₙₐ[𝕜] 𝕜` converges to `1` along
`approximateIdentity 𝕜 μ`. -/
theorem tendsto_nonUnitalAlgHom_approximateIdentity {φ : GroupAlgebraL1 𝕜 μ →ₙₐ[𝕜] 𝕜}
    (hφ : φ ≠ 0) :
    Tendsto (fun U => φ (approximateIdentity 𝕜 μ U)) atBot (𝓝 1) := by
  have hφ' : ∃ f, φ f ≠ 0 := by
    rwa [ne_eq, DFunLike.ext_iff, not_forall] at hφ
  exact NonUnitalAlgHom.tendsto_one_of_tendsto_mul_right hφ' tendsto_approximateIdentity_mul

/-- **Every nonzero algebraic character on `GroupAlgebraL1 𝕜 μ` is bounded and has operator norm
`1`.** Automatic continuity is supplied by `NonUnitalAlgHom.instContinuousLinearMapClass`, and the
lower bound follows from `φ (approximateIdentity 𝕜 μ U) → 1` together with
`‖approximateIdentity 𝕜 μ U‖ = 1`. -/
theorem norm_nonUnitalAlgHom_toContinuousLinearMap {φ : GroupAlgebraL1 𝕜 μ →ₙₐ[𝕜] 𝕜}
    (hφ : φ ≠ 0) : ‖φ.toContinuousLinearMap‖ = 1 :=
  NonUnitalAlgHom.norm_toContinuousLinearMap_of_tendsto_mul_right
    (.of_forall fun U => (norm_approximateIdentity U).le) tendsto_approximateIdentity_mul hφ

end LeftApproximateIdentity

/-! ### Two-sided approximate unit, involution, and nondegeneracy -/

section RegularHaar

variable {G 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular] [RCLike 𝕜]

/-- **Right approximate identity.** For a regular left Haar measure `μ`, along `Filter.atBot` on
open identity neighborhoods, `f * approximateIdentity 𝕜 μ U → f` in `GroupAlgebraL1 𝕜 μ` for every
`f`. -/
theorem tendsto_mul_approximateIdentity (f : GroupAlgebraL1 𝕜 μ) :
    Tendsto (fun U => f * approximateIdentity 𝕜 μ U) atBot (𝓝 f) := by
  refine (((linearIsometryEquiv 𝕜 𝕜 μ).symm.continuous.tendsto f.ofConv).comp
    (μ.tendsto_convolutionL_approximateIdentityL1 f.ofConv)).congr fun U => ?_
  rw [Function.comp_apply, linearIsometryEquiv_symm_apply, ← ofConv_approximateIdentity,
    ← ofConv_mul, toConv_ofConv]

/-- Pointwise right-variable formula for `f * approximateIdentity 𝕜 μ U`: on a locally compact
Hausdorff group, `(f * u_U)(x) = ∫ z, c(z) • (f (x * z⁻¹) * u_U z) ∂μ` for `μ`-almost every `x`. -/
theorem ofConv_mul_approximateIdentity_ae_eq [T2Space G] (f : GroupAlgebraL1 𝕜 μ)
    (U : OpenNhdsOf (1 : G)) :
    (f * approximateIdentity 𝕜 μ U).ofConv =ᵐ[μ]
      fun x => ∫ z, (modularCharacter z : ℝ) •
        (f.ofConv (x * z⁻¹) * (μ.approximateIdentity U z : 𝕜)) ∂μ := by
  refine (ofConv_mul_ae_eq_right f (approximateIdentity 𝕜 μ U)).trans (.of_forall fun x => ?_)
  refine integral_congr_ae ((ofConv_approximateIdentity_ae_eq (𝕜 := 𝕜) U).mono fun z hz => ?_)
  dsimp only
  rw [hz]

/-- Pushing `Filter.atBot` forward along `approximateIdentity 𝕜 μ` gives a two-sided approximate
unit in `GroupAlgebraL1 𝕜 μ`. -/
theorem isApproximateUnit_map_approximateIdentity :
    (atBot.map (approximateIdentity 𝕜 μ)).IsApproximateUnit where
  tendsto_mul_left f := by
    simpa only [tendsto_map'_iff, Function.comp_def] using tendsto_mul_approximateIdentity f
  tendsto_mul_right f := by
    simpa only [tendsto_map'_iff, Function.comp_def] using tendsto_approximateIdentity_mul f
  neBot := map_neBot

theorem eventually_norm_eq_one_map_approximateIdentity :
    ∀ᶠ u in atBot.map (approximateIdentity 𝕜 μ), ‖u‖ = 1 :=
  eventually_map.2 (.of_forall norm_approximateIdentity)

/-- `GroupAlgebraL1 𝕜 μ` admits a two-sided approximate unit whose elements all have norm `1`. -/
theorem exists_isApproximateUnit_norm_eq_one :
    ∃ l : Filter (GroupAlgebraL1 𝕜 μ), l.IsApproximateUnit ∧ ∀ᶠ u in l, ‖u‖ = 1 :=
  ⟨atBot.map (approximateIdentity 𝕜 μ), isApproximateUnit_map_approximateIdentity,
    eventually_norm_eq_one_map_approximateIdentity⟩

/-- Because each kernel `approximateIdentity 𝕜 μ U` is real-valued, its group-algebra involution
is simply its modular inversion `Lp.modularInversion`. -/
theorem ofConv_star_approximateIdentity (U : OpenNhdsOf (1 : G)) :
    (star (approximateIdentity 𝕜 μ U)).ofConv =
      Lp.modularInversion μ 1 𝕜 (μ.approximateIdentityL1 𝕜 U) := by
  rw [ofConv_star, ofConv_approximateIdentity, μ.star_approximateIdentityL1]

theorem norm_star_approximateIdentity (U : OpenNhdsOf (1 : G)) :
    ‖star (approximateIdentity 𝕜 μ U)‖ = 1 := by
  rw [norm_star, norm_approximateIdentity]

/-- The involuted kernels `star (approximateIdentity 𝕜 μ U)` also form a left approximate identity
in `GroupAlgebraL1 𝕜 μ`. -/
theorem tendsto_star_approximateIdentity_mul (f : GroupAlgebraL1 𝕜 μ) :
    Tendsto (fun U => star (approximateIdentity 𝕜 μ U) * f) atBot (𝓝 f) := by
  have h := (continuous_star.tendsto (star f)).comp (tendsto_mul_approximateIdentity (star f))
  simpa only [Function.comp_def, star_mul, star_star] using h

/-- The involuted kernels `star (approximateIdentity 𝕜 μ U)` also form a right approximate identity
in `GroupAlgebraL1 𝕜 μ`. -/
theorem tendsto_mul_star_approximateIdentity (f : GroupAlgebraL1 𝕜 μ) :
    Tendsto (fun U => f * star (approximateIdentity 𝕜 μ U)) atBot (𝓝 f) := by
  have h := (continuous_star.tendsto (star f)).comp (tendsto_approximateIdentity_mul (star f))
  simpa only [Function.comp_def, star_mul, star_star] using h

/-- Left multiplication on `GroupAlgebraL1 𝕜 μ` is faithful (the left annihilator vanishes). -/
instance instFaithfulSMul : FaithfulSMul (GroupAlgebraL1 𝕜 μ) (GroupAlgebraL1 𝕜 μ) := by
  have := (isApproximateUnit_map_approximateIdentity (𝕜 := 𝕜) (μ := μ)).neBot
  exact TauCeti.faithfulSMul_of_tendsto_mul_left
    (isApproximateUnit_map_approximateIdentity (𝕜 := 𝕜) (μ := μ)).tendsto_mul_left

/-- Right multiplication on `GroupAlgebraL1 𝕜 μ` is faithful (the right annihilator vanishes). -/
instance instFaithfulSMulMulOpposite :
    FaithfulSMul (GroupAlgebraL1 𝕜 μ)ᵐᵒᵖ (GroupAlgebraL1 𝕜 μ) := by
  have := (isApproximateUnit_map_approximateIdentity (𝕜 := 𝕜) (μ := μ)).neBot
  exact TauCeti.faithfulSMul_mulOpposite_of_tendsto_mul_right
    (isApproximateUnit_map_approximateIdentity (𝕜 := 𝕜) (μ := μ)).tendsto_mul_right

end RegularHaar

end TauCeti.GroupAlgebraL1

end
