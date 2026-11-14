/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Character.Basic
public import TauCeti.Analysis.Normed.Algebra.GroupAlgebra.Basic
public import TauCeti.MeasureTheory.Group.Convolution.Kernel
public import TauCeti.Topology.ApproximateUnit

/-!
# Chosen approximate identities and characters of `L¹(G)`

Let `G` be a locally compact group equipped with a regular left Haar measure `μ` (without assuming
σ-compactness or second countability) and let `𝕜` be an `RCLike` scalar field (`ℝ` or `ℂ`). Using
the shrinking continuous peak kernels `μ.approximateIdentity U` indexed by open neighborhoods
`U : TopologicalSpace.OpenNhdsOf (1 : G)` along `Filter.atBot`, this file constructs a canonical
chosen net approximate identity `L1GroupAlgebra.approximateIdentity 𝕜 μ` on
`TauCeti.L1GroupAlgebra 𝕜 μ`:

* **Regularity and unit norm (`L¹ ∩ L²`):** Each `approximateIdentity 𝕜 μ U` is represented almost
  everywhere by the continuous compactly supported function `x ↦ (μ.approximateIdentity U x : 𝕜)`,
  hence belongs to `Lᵖ(G, μ; 𝕜)` for every `p : ℝ≥0∞` (in particular to `L¹ ∩ L²`,
  `L1GroupAlgebra.memLp_ofConv_approximateIdentity`), has `L¹` norm `1` and Haar integral `1`, and
  vanishes almost everywhere outside `U`.
* **Two-sided `L¹` net convergence:** Along `atBot` on `OpenNhdsOf (1 : G)`, both
  `approximateIdentity 𝕜 μ U * f` and `f * approximateIdentity 𝕜 μ U` converge to `f` in norm
  (`L1GroupAlgebra.tendsto_approximateIdentity_mul`,
  `L1GroupAlgebra.tendsto_mul_approximateIdentity`), making
  `Filter.map (approximateIdentity 𝕜 μ) atBot` a norm-one `Filter.IsApproximateUnit`
  (`L1GroupAlgebra.isApproximateUnit_map_approximateIdentity`). Consequently, both left and right
  multiplication on `L1GroupAlgebra 𝕜 μ` are faithful (`FaithfulSMul`).
* **Explicit right-hand convolution and modular-character formulas:** Right convolution with
  `approximateIdentity 𝕜 μ U` equals the Bochner integral
  `∫ z, μ.approximateIdentity U z • rightTranslation 𝕜 μ z⁻¹ f ∂μ`
  (`L1GroupAlgebra.mul_approximateIdentity_eq_integral_rightTranslation`) and, when `G` is
  Hausdorff, is represented pointwise `μ`-almost everywhere by
  `x ↦ ∫ z, ((Measure.modularCharacter z : ℝ) * μ.approximateIdentity U z) • f.ofConv (x * z⁻¹) ∂μ`
  (`L1GroupAlgebra.ofConv_mul_approximateIdentity_ae_eq`), whose scalar weight integrates to `1` in
  the `atBot` limit
  (`MeasureTheory.Measure.tendsto_integral_modularCharacter_mul_approximateIdentity`).
* **Characters of `L¹(G)`:** Every algebraic character `χ : L1GroupAlgebra 𝕜 μ →ₙₐ[𝕜] 𝕜` is
  automatically continuous and contractive (`NonUnitalAlgHom.instContinuousLinearMapClass`), and
  every nonzero character satisfies `χ (approximateIdentity 𝕜 μ U) → 1` along `atBot` and has
  operator norm `‖χ.toContinuousLinearMap‖ = 1`
  (`L1GroupAlgebra.tendsto_character_approximateIdentity`,
  `L1GroupAlgebra.norm_character_toContinuousLinearMap`). Haar integration
  `L1GroupAlgebra.integralNonUnitalAlgHom 𝕜 μ` provides an explicit nonzero character of norm `1`.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §2.5.
* E. Hewitt and K. A. Ross, *Abstract Harmonic Analysis*, Vol. I, 2nd ed., Springer (1979), §20
  and §23.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, Clarendon Press (2000), §3.3.
-/

public section

noncomputable section

open Filter MeasureTheory MeasureTheory.Measure Topology TopologicalSpace
open scoped ENNReal

namespace TauCeti.L1GroupAlgebra

section Haar

variable {G 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [RCLike 𝕜]

variable (𝕜 μ) in
/-- **Chosen net approximate identity** on `L1GroupAlgebra 𝕜 μ`, indexed by open neighborhoods
`U : OpenNhdsOf (1 : G)` ordered by inclusion along `atBot`, obtained by coercing the nonnegative
compactly supported continuous kernel `μ.approximateIdentity U` into `𝕜`. -/
def approximateIdentity (U : OpenNhdsOf (1 : G)) : L1GroupAlgebra 𝕜 μ :=
  toConv ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).compLp (μ.approximateIdentityLp U))

@[simp]
theorem ofConv_approximateIdentity (U : OpenNhdsOf (1 : G)) :
    (approximateIdentity 𝕜 μ U).ofConv =
      (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).compLp (μ.approximateIdentityLp U) :=
  (rfl)

/-- `approximateIdentity 𝕜 μ U` agrees `μ`-almost everywhere with the continuous compactly supported
kernel `x ↦ (μ.approximateIdentity U x : 𝕜)`. -/
theorem coeFn_ofConv_approximateIdentity (U : OpenNhdsOf (1 : G)) :
    (approximateIdentity 𝕜 μ U).ofConv =ᵐ[μ] fun x ↦ (μ.approximateIdentity U x : 𝕜) := by
  filter_upwards [(RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).coeFn_compLp (μ.approximateIdentityLp U),
    μ.coeFn_approximateIdentityLp U] with x hx₁ hx₂
  rw [ofConv_approximateIdentity, hx₁, hx₂, RCLike.ofRealCLM_apply]

/-- Every kernel `(approximateIdentity 𝕜 μ U).ofConv` belongs to `Lᵖ(G, μ; 𝕜)` for all
`p : ℝ≥0∞` — in particular for `p = 1` and `p = 2` (`L¹ ∩ L²`). -/
theorem memLp_ofConv_approximateIdentity (U : OpenNhdsOf (1 : G)) (p : ℝ≥0∞) :
    MemLp (approximateIdentity 𝕜 μ U).ofConv p μ :=
  (μ.memLp_ofReal_approximateIdentity (𝕜 := 𝕜) U p).ae_eq
    (coeFn_ofConv_approximateIdentity (𝕜 := 𝕜) (μ := μ) U).symm

/-- Each element of the chosen approximate identity has Haar integral `1`. -/
theorem integral_approximateIdentity (U : OpenNhdsOf (1 : G)) :
    ∫ x, (approximateIdentity 𝕜 μ U).ofConv x ∂μ = 1 := by
  simp

/-- `integralCLM 𝕜 μ` evaluates to `1` on each element of the chosen approximate identity. -/
theorem integralCLM_approximateIdentity (U : OpenNhdsOf (1 : G)) :
    integralCLM 𝕜 μ (approximateIdentity 𝕜 μ U) = 1 := by
  simp

/-- Each element of the chosen approximate identity has `L¹` norm `1`. -/
@[simp]
theorem norm_approximateIdentity (U : OpenNhdsOf (1 : G)) :
    ‖approximateIdentity 𝕜 μ U‖ = 1 := by
  rw [norm_eq_integral_norm]
  refine (integral_congr_ae ?_).trans (μ.integral_approximateIdentity U)
  filter_upwards [coeFn_ofConv_approximateIdentity (𝕜 := 𝕜) (μ := μ) U] with x hx
  have hnonneg : 0 ≤ μ.approximateIdentity U x :=
    CompactlySupportedContinuousMap.le_def.1 (μ.approximateIdentity_nonneg U) x
  rw [hx, RCLike.norm_ofReal, abs_of_nonneg hnonneg]

/-- Every element of the chosen approximate identity is nonzero. -/
theorem approximateIdentity_ne_zero (U : OpenNhdsOf (1 : G)) :
    approximateIdentity 𝕜 μ U ≠ 0 := by
  intro h
  have hnorm := congrArg norm h
  simp only [norm_approximateIdentity, norm_zero, one_ne_zero] at hnorm

/-- `L1GroupAlgebra 𝕜 μ` is nontrivial whenever `μ` is a left Haar measure and `𝕜` is `RCLike`. -/
instance instNontrivial : Nontrivial (L1GroupAlgebra 𝕜 μ) :=
  ⟨⟨approximateIdentity 𝕜 μ ⊤, 0, approximateIdentity_ne_zero ⊤⟩⟩

/-- Each kernel `(approximateIdentity 𝕜 μ U).ofConv` vanishes `μ`-almost everywhere outside `U`. -/
theorem ofConv_approximateIdentity_ae_eq_zero (U : OpenNhdsOf (1 : G)) :
    ∀ᵐ x ∂μ, x ∉ U → (approximateIdentity 𝕜 μ U).ofConv x = 0 := by
  filter_upwards [coeFn_ofConv_approximateIdentity (𝕜 := 𝕜) (μ := μ) U,
    μ.coeFn_approximateIdentityLp U, μ.approximateIdentityLp_ae_eq_zero U] with x hx₁ hx₂ hxU hnotU
  rw [hx₁, ← hx₂, hxU hnotU, RCLike.ofReal_zero]

/-- Along `atBot`, the chosen approximate identity eventually vanishes almost everywhere outside
every neighborhood of `1 : G`. -/
theorem eventually_ofConv_approximateIdentity_ae_eq_zero {S : Set G} (hS : S ∈ 𝓝 (1 : G)) :
    ∀ᶠ U : OpenNhdsOf (1 : G) in atBot,
      ∀ᵐ x ∂μ, x ∉ S → (approximateIdentity 𝕜 μ U).ofConv x = 0 := by
  obtain ⟨V, -, hV⟩ := OpenNhdsOf.basis_nhds.mem_iff.1 hS
  filter_upwards [eventually_le_atBot V] with U hU
  filter_upwards [ofConv_approximateIdentity_ae_eq_zero (𝕜 := 𝕜) (μ := μ) U] with x hx hxS
  exact hx fun hxU ↦ hxS (hV (hU hxU))

end Haar

section LeftApproximateIdentity

variable {G 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.InnerRegularCompactLTTop] [RCLike 𝕜]

/-- Convolving on the left with `approximateIdentity 𝕜 μ U` acts on `L¹` via the real kernel
`μ.approximateIdentityLp U`. -/
theorem ofConv_approximateIdentity_mul (U : OpenNhdsOf (1 : G)) (f : L1GroupAlgebra 𝕜 μ) :
    (approximateIdentity 𝕜 μ U * f).ofConv =
      Lp.convolutionL μ 1 ENNReal.one_ne_top (μ.approximateIdentityLp U) f.ofConv :=
  Lp.convolutionL_ofRealCLM_compLp_left (μ.approximateIdentityLp U) f.ofConv

/-- `integralNonUnitalAlgHom 𝕜 μ` evaluates to `1` on each element of the chosen approximate
identity. -/
theorem integralNonUnitalAlgHom_approximateIdentity (U : OpenNhdsOf (1 : G)) :
    integralNonUnitalAlgHom 𝕜 μ (approximateIdentity 𝕜 μ U) = 1 := by
  simp

/-- **Left approximate identity convergence** on `L1GroupAlgebra 𝕜 μ` along `atBot`. -/
theorem tendsto_approximateIdentity_mul (f : L1GroupAlgebra 𝕜 μ) :
    Tendsto (fun U ↦ approximateIdentity 𝕜 μ U * f) atBot (𝓝 f) := by
  have h := (continuous_toConv (𝕜 := 𝕜) (μ := μ).tendsto f.ofConv).comp
    (μ.tendsto_approximateIdentityLp_convolutionL ENNReal.one_ne_top f.ofConv)
  rw [toConv_ofConv] at h
  refine h.congr fun U ↦ ?_
  rw [Function.comp_apply, ← ofConv_approximateIdentity_mul, toConv_ofConv]

end LeftApproximateIdentity

section RegularHaar

variable {G 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular] [RCLike 𝕜]

/-! ### Explicit right-hand convolution and modular-character formulas -/

/-- At the `Lp` level, convolving `f` on the right with `approximateIdentity 𝕜 μ U` is the Bochner
integral of weighted right translates `R_(z⁻¹) f.ofConv` against `μ.approximateIdentity U`. -/
theorem ofConv_mul_approximateIdentity (f : L1GroupAlgebra 𝕜 μ) (U : OpenNhdsOf (1 : G)) :
    (f * approximateIdentity 𝕜 μ U).ofConv =
      ∫ z, μ.approximateIdentity U z • Lp.rightTranslation μ 1 𝕜 z⁻¹ f.ofConv ∂μ := by
  rw [ofConv_mul, ofConv_approximateIdentity,
    Lp.convolutionL_ofRealCLM_compLp_right_eq_integral_smul_rightTranslation_inv]
  refine integral_congr_ae ?_
  filter_upwards [μ.coeFn_approximateIdentityLp U] with z hz
  rw [hz]

/-- **Right convolution with the chosen approximate identity as a Bochner integral** of weighted
right translates in `L1GroupAlgebra 𝕜 μ`. -/
theorem mul_approximateIdentity_eq_integral_rightTranslation (f : L1GroupAlgebra 𝕜 μ)
    (U : OpenNhdsOf (1 : G)) :
    f * approximateIdentity 𝕜 μ U =
      ∫ z, μ.approximateIdentity U z • rightTranslation 𝕜 μ z⁻¹ f ∂μ := by
  apply ofConv_injective
  have hcomm := (linearIsometryEquiv ℝ 𝕜 μ).toContinuousLinearEquiv.integral_comp_comm
    (μ := μ) fun z ↦ μ.approximateIdentity U z • rightTranslation 𝕜 μ z⁻¹ f
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, map_smul, linearIsometryEquiv_apply,
    ofConv_rightTranslation] at hcomm
  rw [ofConv_mul_approximateIdentity, hcomm]

/-- **Pointwise right-hand modular-character formula** for `f * approximateIdentity 𝕜 μ U` on a
locally compact Hausdorff group: at `μ`-almost every `x : G`, it integrates `f.ofConv (x * z⁻¹)`
against the modularly weighted kernel
`(Measure.modularCharacter z : ℝ) * μ.approximateIdentity U z`. -/
theorem ofConv_mul_approximateIdentity_ae_eq [T2Space G] (f : L1GroupAlgebra 𝕜 μ)
    (U : OpenNhdsOf (1 : G)) :
    (f * approximateIdentity 𝕜 μ U).ofConv =ᵐ[μ] fun x ↦
      ∫ z, ((modularCharacter z : ℝ) * μ.approximateIdentity U z) • f.ofConv (x * z⁻¹) ∂μ := by
  filter_upwards [ofConv_mul_ae_eq_modularCharacter f (approximateIdentity 𝕜 μ U)] with x hx
  refine hx.trans (integral_congr_ae ?_)
  filter_upwards [coeFn_ofConv_approximateIdentity (𝕜 := 𝕜) (μ := μ) U] with z hz
  rw [hz, mul_comm (f.ofConv (x * z⁻¹)), ← smul_eq_mul, ← RCLike.algebraMap_eq_ofReal,
    algebraMap_smul, smul_smul]

/-! ### Two-sided net convergence, adjoint kernels, and `Filter.IsApproximateUnit` -/

/-- **Right approximate identity convergence** on `L1GroupAlgebra 𝕜 μ` along `atBot`. -/
theorem tendsto_mul_approximateIdentity (f : L1GroupAlgebra 𝕜 μ) :
    Tendsto (fun U ↦ f * approximateIdentity 𝕜 μ U) atBot (𝓝 f) := by
  have h := (continuous_toConv (𝕜 := 𝕜) (μ := μ).tendsto f.ofConv).comp
    (μ.tendsto_convolutionL_ofRealCLM_compLp_approximateIdentityLp f.ofConv)
  rw [toConv_ofConv] at h
  exact h

/-- Pointwise formula for the modular adjoint `star (approximateIdentity 𝕜 μ U)`. -/
theorem coeFn_ofConv_star_approximateIdentity (U : OpenNhdsOf (1 : G)) :
    (star (approximateIdentity 𝕜 μ U)).ofConv =ᵐ[μ]
      fun x ↦ (((modularCharacter x : ℝ) * μ.approximateIdentity U x⁻¹ : ℝ) : 𝕜) := by
  filter_upwards [coeFn_ofConv_star (approximateIdentity 𝕜 μ U),
    (quasiMeasurePreserving_inv_of_regular μ).ae
      (coeFn_ofConv_approximateIdentity (𝕜 := 𝕜) (μ := μ) U)] with x h₁ h₂
  rw [h₁, h₂, RCLike.star_def, RCLike.conj_ofReal, RCLike.ofReal_mul,
    ← RCLike.algebraMap_eq_ofReal (K := 𝕜), ← algebraMap_smul 𝕜, RCLike.algebraMap_eq_ofReal,
    smul_eq_mul]

/-- Each modular adjoint `star (approximateIdentity 𝕜 μ U)` has Haar integral `1`. -/
theorem integral_star_approximateIdentity (U : OpenNhdsOf (1 : G)) :
    ∫ x, (star (approximateIdentity 𝕜 μ U)).ofConv x ∂μ = 1 := by
  rw [integral_star, integral_approximateIdentity, star_one]

/-- The modular adjoints `star (approximateIdentity 𝕜 μ U)` also form a left approximate identity
along `atBot`. -/
theorem tendsto_star_approximateIdentity_mul (f : L1GroupAlgebra 𝕜 μ) :
    Tendsto (fun U ↦ star (approximateIdentity 𝕜 μ U) * f) atBot (𝓝 f) := by
  have h := (continuous_star.tendsto (star f)).comp (tendsto_mul_approximateIdentity (star f))
  rw [star_star] at h
  refine h.congr fun U ↦ ?_
  rw [Function.comp_apply, star_mul, star_star]

/-- The modular adjoints `star (approximateIdentity 𝕜 μ U)` also form a right approximate identity
along `atBot`. -/
theorem tendsto_mul_star_approximateIdentity (f : L1GroupAlgebra 𝕜 μ) :
    Tendsto (fun U ↦ f * star (approximateIdentity 𝕜 μ U)) atBot (𝓝 f) := by
  have h := (continuous_star.tendsto (star f)).comp (tendsto_approximateIdentity_mul (star f))
  rw [star_star] at h
  refine h.congr fun U ↦ ?_
  rw [Function.comp_apply, star_mul, star_star]

/-- The image filter `Filter.map (approximateIdentity 𝕜 μ) atBot` is a two-sided approximate unit
on `L1GroupAlgebra 𝕜 μ`. -/
theorem isApproximateUnit_map_approximateIdentity :
    (Filter.map (approximateIdentity 𝕜 μ) atBot).IsApproximateUnit where
  tendsto_mul_left f := tendsto_map'_iff.2 (tendsto_mul_approximateIdentity f)
  tendsto_mul_right f := tendsto_map'_iff.2 (tendsto_approximateIdentity_mul f)
  neBot := Filter.map_neBot

/-- Every element along `Filter.map (approximateIdentity 𝕜 μ) atBot` has `L¹` norm `1`. -/
theorem eventually_norm_eq_one_map_approximateIdentity :
    ∀ᶠ u in Filter.map (approximateIdentity 𝕜 μ) atBot, ‖u‖ = 1 :=
  eventually_map.2 (.of_forall norm_approximateIdentity)

/-- `L1GroupAlgebra 𝕜 μ` admits a two-sided approximate unit consisting entirely of norm-one
elements. -/
theorem exists_isApproximateUnit_norm_eq_one :
    ∃ l : Filter (L1GroupAlgebra 𝕜 μ), l.IsApproximateUnit ∧ ∀ᶠ u in l, ‖u‖ = 1 :=
  ⟨Filter.map (approximateIdentity 𝕜 μ) atBot, isApproximateUnit_map_approximateIdentity,
    eventually_norm_eq_one_map_approximateIdentity⟩

/-- Left multiplication on `L1GroupAlgebra 𝕜 μ` is faithful (`f * h = g * h` for all `h` implies
`f = g`), as required to identify double centralizers with multipliers. -/
instance instFaithfulSMul : FaithfulSMul (L1GroupAlgebra 𝕜 μ) (L1GroupAlgebra 𝕜 μ) :=
  have := (isApproximateUnit_map_approximateIdentity (𝕜 := 𝕜) (μ := μ)).neBot
  faithfulSMul_of_tendsto_mul_left
    (isApproximateUnit_map_approximateIdentity (𝕜 := 𝕜) (μ := μ)).tendsto_mul_left

/-- Right multiplication on `L1GroupAlgebra 𝕜 μ` is faithful (`h * f = h * g` for all `h` implies
`f = g`). -/
instance instFaithfulSMulMulOpposite :
    FaithfulSMul (L1GroupAlgebra 𝕜 μ)ᵐᵒᵖ (L1GroupAlgebra 𝕜 μ) :=
  have := (isApproximateUnit_map_approximateIdentity (𝕜 := 𝕜) (μ := μ)).neBot
  faithfulSMul_mulOpposite_of_tendsto_mul_right
    (isApproximateUnit_map_approximateIdentity (𝕜 := 𝕜) (μ := μ)).tendsto_mul_right

/-! ### Characters of `L1GroupAlgebra 𝕜 μ` -/

/-- Every nonzero algebraic character `χ : L1GroupAlgebra 𝕜 μ →ₙₐ[𝕜] 𝕜` tends to `1` along the
chosen approximate identity. -/
theorem tendsto_character_approximateIdentity {χ : L1GroupAlgebra 𝕜 μ →ₙₐ[𝕜] 𝕜} (hχ : χ ≠ 0) :
    Tendsto (fun U ↦ χ (approximateIdentity 𝕜 μ U)) atBot (𝓝 1) := by
  obtain ⟨f, hf⟩ : ∃ f, χ f ≠ 0 := by simpa [DFunLike.ext_iff] using hχ
  exact tendsto_map'_iff.1 <|
    NonUnitalAlgHom.tendsto_one_of_tendsto_mul_right hf
      ((isApproximateUnit_map_approximateIdentity (𝕜 := 𝕜) (μ := μ)).tendsto_mul_right f)

/-- **Every nonzero algebraic character of `L¹(G)` is bounded of operator norm `1`.** No continuity
is assumed on `χ`. -/
theorem norm_character_toContinuousLinearMap {χ : L1GroupAlgebra 𝕜 μ →ₙₐ[𝕜] 𝕜} (hχ : χ ≠ 0) :
    ‖χ.toContinuousLinearMap‖ = 1 := by
  have := (isApproximateUnit_map_approximateIdentity (𝕜 := 𝕜) (μ := μ)).neBot
  exact NonUnitalAlgHom.norm_toContinuousLinearMap_eq_one_of_tendsto_mul_right hχ
    (eventually_norm_eq_one_map_approximateIdentity.mono fun _ hu ↦ hu.le)
    (isApproximateUnit_map_approximateIdentity (𝕜 := 𝕜) (μ := μ)).tendsto_mul_right

@[simp]
theorem toContinuousLinearMap_integralNonUnitalAlgHom :
    (integralNonUnitalAlgHom 𝕜 μ).toContinuousLinearMap = integralCLM 𝕜 μ := by
  ext f
  rw [NonUnitalAlgHom.toContinuousLinearMap_apply, integralNonUnitalAlgHom_apply,
    integralCLM_apply]

/-- Haar integration is a nonzero character on `L1GroupAlgebra 𝕜 μ`. -/
theorem integralNonUnitalAlgHom_ne_zero : integralNonUnitalAlgHom 𝕜 μ ≠ 0 := by
  intro h
  have h1 : integralNonUnitalAlgHom 𝕜 μ (approximateIdentity 𝕜 μ ⊤) = 0 := by simp [h]
  rw [integralNonUnitalAlgHom_approximateIdentity] at h1
  exact one_ne_zero h1

/-- Haar integration on `L1GroupAlgebra 𝕜 μ` has operator norm `1`. -/
@[simp]
theorem norm_integralCLM : ‖integralCLM 𝕜 μ‖ = 1 := by
  rw [← toContinuousLinearMap_integralNonUnitalAlgHom]
  exact norm_character_toContinuousLinearMap integralNonUnitalAlgHom_ne_zero

end RegularHaar

end TauCeti.L1GroupAlgebra
