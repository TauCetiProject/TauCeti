/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.Action.Koopman
public import TauCeti.Dynamics.Ergodic.Action.WeakMixing.Basic
public import TauCeti.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import TauCeti.Analysis.Semigroups.Group.MeanErgodic
import TauCeti.Dynamics.Ergodic.Action.Eigenfunction
import TauCeti.MeasureTheory.Group.ErgodicExtreme
import TauCeti.MeasureTheory.Integral.Prod

/-!
# The multiplier property of weak mixing

Let `ℝ` act jointly measurably on `X` and on `Y`, preserving probability measures `μ` and `ν`, and
let `ℝ` act on `X × Y` diagonally, `t +ᵥ (x, y) = (t +ᵥ x, t +ᵥ y)`. If the action on `X` is weakly
mixing and the action on `Y` is ergodic, then the diagonal action is ergodic for `μ.prod ν`
(`MeasureTheory.Measure.ergodicVAdd_prod_of_isWeaklyMixing`).

The proof goes through the Koopman groups `U_t f = f ∘ (t +ᵥ ·)` on complex `L²`.

* An action preserving a finite measure is ergodic exactly when the only vectors of `L²` fixed
  by the Koopman group are the almost everywhere constant functions
  (`TauCeti.ergodicVAdd_iff_forall_koopmanGroup_eq`).
* For an ergodic action, the continuous-time mean ergodic theorem identifies the limit of the
  averaged correlations: `T⁻¹ ∫₀ᵀ ⟪g, U_t f⟫ dt → (∫ f) conj (∫ g)`
  (`TauCeti.tendsto_average_inner_koopmanGroup_of_ergodicVAdd`).
* For indicators of rectangles `F₁ = 1_{C × D}`, `F₂ = 1_{A × B}`, the correlation
  `⟪F₁, U_t F₂⟫` is the product `c₁(t) c₂(t)` of `c₁(t) = μ((t +ᵥ ·)⁻¹' A ∩ C)` and
  `c₂(t) = ν((t +ᵥ ·)⁻¹' B ∩ D)`. Weak mixing gives `T⁻¹ ∫₀ᵀ |c₁(t) - μ(A) μ(C)| dt → 0`, and
  ergodicity of `Y` gives `T⁻¹ ∫₀ᵀ c₂(t) dt → ν(B) ν(D)`. As `0 ≤ c₂ ≤ 1`, the averaged correlation
  tends to `μ(A) μ(C) ν(B) ν(D) = ⟪F₁, 1⟫ ⟪1, F₂⟫`.
* So the mean ergodic limit `P F₂` of the averages of `U_t F₂` has the same inner products with
  rectangle indicators as `⟪1, F₂⟫ 1`. Indicators of rectangles are total in `L²(μ.prod ν)`
  (`MeasureTheory.Lp.eq_zero_of_forall_inner_indicatorConstLp_prod`, by the Dynkin step
  `TauCeti.setIntegral_eq_zero_of_forall_prod`), so `P F₂ = ⟪1, F₂⟫ 1`. For a vector `F` fixed
  by the Koopman group, `⟪F, F₂⟫ = ⟪F, U_t F₂⟫` for every `t`, hence
  `⟪F, F₂⟫ = ⟪F, P F₂⟫ = ⟪F, 1⟫ ⟪1, F₂⟫`, and the totality of rectangle indicators again shows
  `F = ⟪1, F⟫ 1`.

## Main results

* `Prod.instMeasurableVAdd₂Diagonal`: the diagonal action on a product of jointly measurable
  actions is jointly measurable;
* `MeasureTheory.Lp.eq_zero_of_forall_inner_indicatorConstLp_prod`: indicators of measurable
  rectangles are total in `L²` of a product of finite measures;
* `TauCeti.exists_ae_eq_const_of_koopmanGroup_eq`: Koopman-fixed vectors of an ergodic action are
  almost everywhere constant;
* `TauCeti.ergodicVAdd_of_forall_koopmanGroup_eq`, `TauCeti.ergodicVAdd_iff_forall_koopmanGroup_eq`:
  the converse, and the characterisation of ergodicity by Koopman-fixed vectors;
* `TauCeti.continuous_measureReal_preimage_vadd_inter`: continuity of `t ↦ μ((t +ᵥ ·)⁻¹' A ∩ C)`;
* `TauCeti.tendsto_average_inner_koopmanGroup_of_ergodicVAdd`: averaged correlations of an ergodic
  action;
* `MeasureTheory.Measure.ergodicVAdd_prod_of_isWeaklyMixing`: the multiplier property of weak
  mixing.

## References

* M. Hochman, *Notes on ergodic theory*, 2012, Proposition 6.2.1 (for actions of `ℤ`).
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology ENNReal ComplexConjugate InnerProductSpace

/-! ### The diagonal action -/

/-- The diagonal action on a product of spaces with jointly measurable actions is jointly
measurable. -/
@[to_additive Prod.instMeasurableVAdd₂Diagonal /-- The diagonal additive action on a product of
spaces with jointly measurable additive actions is jointly measurable. -/]
instance Prod.instMeasurableSMul₂Diagonal {M X Y : Type*} [MeasurableSpace M] [MeasurableSpace X]
    [MeasurableSpace Y] [SMul M X] [SMul M Y] [MeasurableSMul₂ M X] [MeasurableSMul₂ M Y] :
    MeasurableSMul₂ M (X × Y) where
  measurable_smul :=
    (measurable_fst.smul (measurable_fst.comp measurable_snd)).prodMk
      (measurable_fst.smul (measurable_snd.comp measurable_snd))

/-! ### Indicators of rectangles are total -/

namespace MeasureTheory.Lp

variable {𝕜 X Y : Type*} [RCLike 𝕜] [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- **Indicators of rectangles are total in `L²` of a product.** A vector of `L²(μ.prod ν)`,
for finite measures `μ` and `ν`, orthogonal to the indicator of every measurable rectangle
`A ×ˢ B` vanishes. -/
theorem eq_zero_of_forall_inner_indicatorConstLp_prod (w : Lp 𝕜 2 (μ.prod ν))
    (h : ∀ (A : Set X) (B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B),
      ⟪indicatorConstLp 2 (hA.prod hB) (measure_ne_top _ _) (1 : 𝕜), w⟫_𝕜 = 0) :
    w = 0 := by
  have hint : Integrable w (μ.prod ν) := (Lp.memLp w).integrable one_le_two
  have hrect : ∀ A, MeasurableSet A → ∀ B, MeasurableSet B →
      ∫ z in A ×ˢ B, w z ∂(μ.prod ν) = 0 := fun A hA B hB => by
    rw [← L2.inner_indicatorConstLp_one (hA.prod hB) (measure_ne_top _ _)]
    exact h A B hA hB
  have hset := TauCeti.setIntegral_eq_zero_of_forall_prod hint hrect
  refine Lp.ext ?_
  refine (ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ _ => hint.integrableOn)
    fun s hs _ => hset s hs).trans (Lp.coeFn_zero 𝕜 2 _).symm

end MeasureTheory.Lp

/-! ### Ergodicity and Koopman-fixed vectors -/

namespace TauCeti

section ConstL2

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The constant function `c` in complex `L²(μ)`, for a finite measure `μ`. -/
private abbrev constL2 [IsFiniteMeasure μ] (c : ℂ) : Lp ℂ 2 μ :=
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) c

private theorem inner_constL2_left [IsFiniteMeasure μ] (c : ℂ) (f : Lp ℂ 2 μ) :
    ⟪(constL2 c : Lp ℂ 2 μ), f⟫_ℂ = conj c * ∫ x, f x ∂μ := by
  rw [L2.inner_indicatorConstLp_eq_inner_setIntegral, Measure.restrict_univ, RCLike.inner_apply,
    mul_comm]

private theorem inner_constL2_right [IsFiniteMeasure μ] (c : ℂ) (f : Lp ℂ 2 μ) :
    ⟪f, (constL2 c : Lp ℂ 2 μ)⟫_ℂ = c * conj (∫ x, f x ∂μ) := by
  rw [← inner_conj_symm, inner_constL2_left, map_mul, Complex.conj_conj]

private theorem integral_constL2 [IsProbabilityMeasure μ] (c : ℂ) :
    ∫ x, (constL2 c : Lp ℂ 2 μ) x ∂μ = c := by
  rw [integral_indicatorConstLp, probReal_univ, one_smul]

private theorem eq_constL2_of_ae_eq_const [IsFiniteMeasure μ] {u : Lp ℂ 2 μ} {c : ℂ}
    (hu : u =ᵐ[μ] Function.const X c) : u = constL2 c := by
  refine Lp.ext (hu.trans ?_)
  rw [constL2, indicatorConstLp_univ]
  exact (Lp.coeFn_const 2 μ c).symm

private theorem ae_eq_const_of_eq_constL2 [IsFiniteMeasure μ] {u : Lp ℂ 2 μ} {c : ℂ}
    (hu : u = constL2 c) : u =ᵐ[μ] Function.const X c := by
  rw [hu, constL2, indicatorConstLp_univ]
  exact Lp.coeFn_const 2 μ c

end ConstL2

/-- The inner product with a time average of an orbit is the time average of the inner
products. -/
private theorem inner_average_orbit {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (U : Semigroups.StronglyContinuousGroup H) (g f : H) (T : ℝ) :
    (innerSL ℂ g ∘ fun T : ℝ => T⁻¹ • ∫ t in (0 : ℝ)..T, U t f) T =
      (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, ⟪g, U t f⟫_ℂ := by
  rw [Function.comp_apply, innerSL_apply_apply, inner_smul_right_eq_smul,
    U.inner_intervalIntegral_orbit, Complex.real_smul]
  push_cast
  rfl

section Unitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {U : Semigroups.StronglyContinuousGroup H}

/-- The averaged correlations `T⁻¹ ∫₀ᵀ ⟪g, U_t f⟫ dt` of a unitary group converge, to `⟪g, L⟫`
for a vector `L` independent of `g` (the projection of `f` onto the fixed vectors). -/
private theorem exists_tendsto_average_inner [CompleteSpace H] (hU : U.IsUnitary) (f : H) :
    ∃ L : H, ∀ g : H, Tendsto (fun T : ℝ => (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, ⟪g, U t f⟫_ℂ) atTop
      (𝓝 ⟪g, L⟫_ℂ) :=
  ⟨_, fun g => (((innerSL ℂ g).continuous.tendsto _).comp
    (hU.tendsto_average_starProjection f)).congr fun T => inner_average_orbit U g f T⟩

/-- The averaged correlations with a vector fixed by a unitary group are constant. -/
private theorem average_inner_of_forall_eq (hU : U.IsUnitary) {F : H} (hF : ∀ t, U t F = F)
    (G : H) {T : ℝ} (hT : T ≠ 0) :
    (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, ⟪F, U t G⟫_ℂ = ⟪F, G⟫_ℂ := by
  have h : ∀ t, ⟪F, U t G⟫_ℂ = ⟪F, G⟫_ℂ := fun t => by
    conv_lhs => rw [← hF t]
    exact hU.inner_map_map t F G
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  simp only [h, intervalIntegral.integral_const, sub_zero, Complex.real_smul]
  field_simp

end Unitary

variable {X : Type*} [MeasurableSpace X] [AddAction ℝ X] [MeasurableVAdd₂ ℝ X]
  {μ : Measure X} [SFinite μ]

/-- The Koopman correlation of two indicators is the measure of an intersection:
`⟪1_C, U_t 1_A⟫ = μ((t +ᵥ ·)⁻¹' A ∩ C)`. -/
private theorem inner_indicatorConstLp_koopmanGroup [IsFiniteMeasure μ]
    [VAddInvariantMeasure ℝ X μ] {A C : Set X} (hA : MeasurableSet A) (hC : MeasurableSet C)
    (t : ℝ) :
    ⟪indicatorConstLp 2 hC (measure_ne_top μ C) (1 : ℂ),
        koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t
          (indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℂ))⟫_ℂ =
      (μ.real ((fun x => t +ᵥ x) ⁻¹' A ∩ C) : ℂ) := by
  rw [koopmanGroup_indicatorConstLp, L2.inner_indicatorConstLp_indicatorConstLp, inter_comm C]
  simp

/-- For a jointly measurable action of `ℝ` preserving a finite measure `μ`, the measure
`μ((t +ᵥ ·)⁻¹' A ∩ C)` depends continuously on `t`. -/
theorem continuous_measureReal_preimage_vadd_inter [IsFiniteMeasure μ]
    [VAddInvariantMeasure ℝ X μ] {A C : Set X} (hA : MeasurableSet A) (hC : MeasurableSet C) :
    Continuous fun t : ℝ => μ.real ((fun x => t +ᵥ x) ⁻¹' A ∩ C) := by
  have h : Continuous fun t : ℝ => ⟪indicatorConstLp 2 hC (measure_ne_top μ C) (1 : ℂ),
      koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t
        (indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℂ))⟫_ℂ :=
    continuous_const.inner ((koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top).continuous_orbit _)
  have h' := Complex.continuous_re.comp h
  simpa only [Function.comp_def, inner_indicatorConstLp_koopmanGroup hA hC, Complex.ofReal_re]
    using h'

/-- **Koopman-fixed vectors of an ergodic action are constant.** For an ergodic jointly
measurable action of `ℝ` preserving `μ`, a vector of complex `L²(μ)` fixed by the Koopman group is
almost everywhere constant. -/
theorem exists_ae_eq_const_of_koopmanGroup_eq [ErgodicVAdd ℝ X μ] (u : Lp ℂ 2 μ)
    (hu : ∀ t : ℝ, koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t u = u) :
    ∃ c : ℂ, u =ᵐ[μ] Function.const X c := by
  have hmem : u ∈ (koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top).eigenspace
      (koopmanGroup_isUnitary μ ℂ).isComplexLinear 0 :=
    (Semigroups.StronglyContinuousGroup.mem_eigenspace_iff _ _ _ _).2 fun t =>
      (Eq.congr_left (hu t)).2 (by simp)
  refine ErgodicVAdd.ae_eq_const_of_forall_ae_eq_comp_vadd₀ ℝ
    (Lp.aestronglyMeasurable u).aemeasurable.nullMeasurable fun t => ?_
  filter_upwards [(mem_eigenspace_koopmanGroup_iff 0 u).1 hmem t] with x hx
  simpa using hx

/-- **Ergodicity from Koopman-fixed vectors.** A jointly measurable action of `ℝ` preserving a
finite measure `μ` is ergodic if every vector of complex `L²(μ)` fixed by the Koopman group is
almost everywhere constant. -/
theorem ergodicVAdd_of_forall_koopmanGroup_eq [VAddInvariantMeasure ℝ X μ] [IsFiniteMeasure μ]
    (h : ∀ u : Lp ℂ 2 μ, (∀ t : ℝ, koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t u = u) →
      ∃ c : ℂ, u =ᵐ[μ] Function.const X c) :
    ErgodicVAdd ℝ X μ where
  aeconst_of_forall_preimage_vadd_ae_eq {s} hs hinv := by
    -- the indicator of `s` is a Koopman-fixed vector, hence almost everywhere constant
    have hcoe := indicatorConstLp_coeFn (p := 2) (μ := μ) (c := (1 : ℂ)) (hs := hs)
      (hμs := measure_ne_top μ s)
    obtain ⟨c, hc⟩ := h (indicatorConstLp 2 hs (measure_ne_top μ s) 1) fun t => by
      rw [koopmanGroup_indicatorConstLp]
      refine Lp.ext ?_
      filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := μ) (c := (1 : ℂ))
          (hs := hs.preimage (measurable_const_vadd t)) (hμs := by
            rw [(measurePreserving_vadd t μ).measure_preimage hs.nullMeasurableSet]
            exact measure_ne_top μ s), hcoe,
        indicator_ae_eq_of_ae_eq_set (f := fun _ : X => (1 : ℂ)) (hinv t)] with x h₁ h₂ h₃
      rw [h₁, h₂, h₃]
    have hfun : (· ∈ s) = (fun z : ℂ => z = 1) ∘ s.indicator fun _ => (1 : ℂ) := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx]
    unfold EventuallyEmptyOrUniv
    rw [hfun]
    exact (eventuallyConst_iff_exists_eventuallyEq.2 ⟨c, hcoe.symm.trans hc⟩).comp _

/-- **Ergodicity and Koopman-fixed vectors.** A jointly measurable action of `ℝ` preserving a
finite measure `μ` is ergodic exactly when every vector of complex `L²(μ)` fixed by the Koopman
group is almost everywhere constant. -/
theorem ergodicVAdd_iff_forall_koopmanGroup_eq [VAddInvariantMeasure ℝ X μ] [IsFiniteMeasure μ] :
    ErgodicVAdd ℝ X μ ↔ ∀ u : Lp ℂ 2 μ,
      (∀ t : ℝ, koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t u = u) →
        ∃ c : ℂ, u =ᵐ[μ] Function.const X c :=
  ⟨fun _ => exists_ae_eq_const_of_koopmanGroup_eq, ergodicVAdd_of_forall_koopmanGroup_eq⟩

/-- **Averaged correlations of an ergodic action.** For an ergodic jointly measurable action of
`ℝ` preserving a probability measure `μ`, and `f g` in complex `L²(μ)`, the averages
`T⁻¹ ∫₀ᵀ ⟪g, U_t f⟫ dt` of the Koopman correlations tend to `(∫ f) conj (∫ g)`. -/
theorem tendsto_average_inner_koopmanGroup_of_ergodicVAdd [IsProbabilityMeasure μ]
    [ErgodicVAdd ℝ X μ] (f g : Lp ℂ 2 μ) :
    Tendsto (fun T : ℝ => (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T,
        ⟪g, koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t f⟫_ℂ) atTop
      (𝓝 ((∫ x, f x ∂μ) * conj (∫ x, g x ∂μ))) := by
  set U := koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top
  have hU : U.IsUnitary := koopmanGroup_isUnitary μ ℂ
  have := Semigroups.StronglyContinuousGroup.hasOrthogonalProjection_fixedSubmodule U
    hU.isComplexLinear
  have hlim := ((innerSL ℂ g).continuous.tendsto _).comp (hU.tendsto_average_starProjection f)
  -- the projection of `f` onto the fixed vectors is the constant `∫ f`
  have hproj : (U.fixedSubmodule hU.isComplexLinear).starProjection f =
      constL2 (∫ x, f x ∂μ) := by
    have hfix : ∀ t : ℝ, U t ((U.fixedSubmodule hU.isComplexLinear).starProjection f) =
        (U.fixedSubmodule hU.isComplexLinear).starProjection f :=
      (Semigroups.StronglyContinuousGroup.mem_fixedSubmodule_iff U _ _).1
        ((U.fixedSubmodule hU.isComplexLinear).starProjection_apply_mem f)
    obtain ⟨c, hc⟩ := exists_ae_eq_const_of_koopmanGroup_eq _ hfix
    have hone : (constL2 1 : Lp ℂ 2 μ) ∈ U.fixedSubmodule hU.isComplexLinear :=
      (Semigroups.StronglyContinuousGroup.mem_fixedSubmodule_iff U _ _).2 fun t =>
        (Eq.congr_left (koopmanGroup_indicatorConstLp μ ℂ 2 ENNReal.ofNat_ne_top .univ
          (measure_ne_top μ univ) 1 t)).2 (by simp only [preimage_univ])
    rw [eq_constL2_of_ae_eq_const hc]
    congr 1
    have := (U.fixedSubmodule hU.isComplexLinear).inner_starProjection_left_eq_right (constL2 1) f
    rw [(U.fixedSubmodule hU.isComplexLinear).starProjection_eq_self_iff.2 hone,
      eq_constL2_of_ae_eq_const hc, inner_constL2_left, inner_constL2_left, integral_constL2,
      map_one, one_mul, one_mul] at this
    exact this.symm
  have hval : (innerSL ℂ g) (constL2 (∫ x, f x ∂μ)) = (∫ x, f x ∂μ) * conj (∫ x, g x ∂μ) := by
    rw [innerSL_apply_apply, inner_constL2_right]
  rw [hproj, hval] at hlim
  refine hlim.congr' (Eventually.of_forall fun T => ?_)
  exact inner_average_orbit U g f T

end TauCeti

/-! ### The multiplier property -/

/-- If `c₁` is Cesàro close to `α` in absolute value and `c₂` is bounded by `1` with Cesàro limit
`β`, then `c₁ c₂` has Cesàro limit `α β`. -/
private theorem tendsto_average_mul_of_tendsto_average_abs_sub {c₁ c₂ : ℝ → ℝ}
    (h₁ : Continuous c₁) (h₂ : Continuous c₂) (hc₂ : ∀ t, |c₂ t| ≤ 1) {α β : ℝ}
    (hα : Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, |c₁ t - α|) atTop (𝓝 0))
    (hβ : Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, c₂ t) atTop (𝓝 β)) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, c₁ t * c₂ t) atTop (𝓝 (α * β)) := by
  have hsplit : ∀ T : ℝ, T⁻¹ * ∫ t in (0 : ℝ)..T, c₁ t * c₂ t =
      T⁻¹ * (∫ t in (0 : ℝ)..T, (c₁ t - α) * c₂ t) + α * (T⁻¹ * ∫ t in (0 : ℝ)..T, c₂ t) := by
    intro T
    have hi₁ : IntervalIntegrable (fun t => (c₁ t - α) * c₂ t) volume 0 T :=
      ((h₁.sub continuous_const).mul h₂).intervalIntegrable 0 T
    have hi₂ : IntervalIntegrable (fun t => α * c₂ t) volume 0 T :=
      (continuous_const.mul h₂).intervalIntegrable 0 T
    have : ∫ t in (0 : ℝ)..T, c₁ t * c₂ t =
        (∫ t in (0 : ℝ)..T, (c₁ t - α) * c₂ t) + ∫ t in (0 : ℝ)..T, α * c₂ t := by
      rw [← intervalIntegral.integral_add hi₁ hi₂]
      congr 1
      ext t
      ring
    rw [this, intervalIntegral.integral_const_mul]
    ring
  simp_rw [hsplit]
  rw [← zero_add (α * β)]
  refine Tendsto.add ?_ (hβ.const_mul α)
  refine squeeze_zero_norm' ?_ hα
  filter_upwards [eventually_ge_atTop 0] with T hT
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.2 hT)]
  gcongr
  refine (intervalIntegral.abs_integral_le_integral_abs hT).trans ?_
  refine intervalIntegral.integral_mono_on hT
    (((h₁.sub continuous_const).mul h₂).abs.intervalIntegrable _ _)
    ((h₁.sub continuous_const).abs.intervalIntegrable _ _) fun t _ => ?_
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hc₂ t)

namespace MeasureTheory.Measure

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [AddAction ℝ X] [AddAction ℝ Y]
  [MeasurableVAdd₂ ℝ X] [MeasurableVAdd₂ ℝ Y] {μ : Measure X} {ν : Measure Y}

/-- The indicator of a measurable rectangle in complex `L²(μ.prod ν)`. -/
private abbrev rectL2 [IsFiniteMeasure μ] [IsFiniteMeasure ν] {A : Set X} {B : Set Y}
    (hA : MeasurableSet A) (hB : MeasurableSet B) : Lp ℂ 2 (μ.prod ν) :=
  indicatorConstLp 2 (hA.prod hB) (measure_ne_top _ _) 1

omit [AddAction ℝ X] [AddAction ℝ Y] [MeasurableVAdd₂ ℝ X] [MeasurableVAdd₂ ℝ Y] in
private theorem integral_rectL2 [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {A : Set X}
    {B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫ z, rectL2 (μ := μ) (ν := ν) hA hB z ∂(μ.prod ν) = (μ.real A * ν.real B : ℝ) := by
  simp only [rectL2, integral_indicatorConstLp, measureReal_prod_prod]
  simp

/-- The Koopman correlation of two rectangles is the product of the correlations of the sides. -/
private theorem inner_rectL2_koopmanGroup [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [VAddInvariantMeasure ℝ X μ] [VAddInvariantMeasure ℝ Y ν] {A C : Set X} {B D : Set Y}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (t : ℝ) :
    ⟪rectL2 hC hD, TauCeti.koopmanGroup (μ.prod ν) ℂ 2 ENNReal.ofNat_ne_top t (rectL2 hA hB)⟫_ℂ =
      ((μ.real ((fun x => t +ᵥ x) ⁻¹' A ∩ C) * ν.real ((fun y => t +ᵥ y) ⁻¹' B ∩ D) : ℝ) :
        ℂ) := by
  rw [TauCeti.koopmanGroup_indicatorConstLp, L2.inner_indicatorConstLp_indicatorConstLp]
  have hpre : (fun z : X × Y => t +ᵥ z) ⁻¹' A ×ˢ B =
      ((fun x => t +ᵥ x) ⁻¹' A) ×ˢ ((fun y => t +ᵥ y) ⁻¹' B) := rfl
  simp only [hpre, prod_inter_prod, measureReal_prod_prod, inter_comm C, inter_comm D]
  simp

/-- The averaged Koopman correlations of two rectangles, for `X` weakly mixing and `Y` ergodic,
tend to `μ(A) μ(C) ν(B) ν(D)`. -/
private theorem tendsto_average_inner_rectL2 [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [VAddInvariantMeasure ℝ X μ] [ErgodicVAdd ℝ Y ν] (hμ : IsWeaklyMixing μ) {A C : Set X}
    {B D : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hD : MeasurableSet D) :
    Tendsto (fun T : ℝ => (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, ⟪rectL2 hC hD,
        TauCeti.koopmanGroup (μ.prod ν) ℂ 2 ENNReal.ofNat_ne_top t (rectL2 hA hB)⟫_ℂ) atTop
      (𝓝 (((μ.real A * μ.real C) * (ν.real B * ν.real D) : ℝ) : ℂ)) := by
  -- the second factor, by ergodicity of `ν`
  have h₂ : Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T,
      ν.real ((fun y => t +ᵥ y) ⁻¹' B ∩ D)) atTop (𝓝 (ν.real B * ν.real D)) := by
    have h := TauCeti.tendsto_average_inner_koopmanGroup_of_ergodicVAdd
      (indicatorConstLp 2 hB (measure_ne_top ν B) (1 : ℂ))
      (indicatorConstLp 2 hD (measure_ne_top ν D) (1 : ℂ))
    simp only [TauCeti.inner_indicatorConstLp_koopmanGroup hB hD,
      intervalIntegral.integral_ofReal, integral_indicatorConstLp] at h
    have h' := (Complex.continuous_re.tendsto _).comp h
    simpa [Function.comp_def] using h'
  have hlim := tendsto_average_mul_of_tendsto_average_abs_sub
    (TauCeti.continuous_measureReal_preimage_vadd_inter hA hC)
    (TauCeti.continuous_measureReal_preimage_vadd_inter hB hD)
    (fun t => by
      rw [abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one) ((isWeaklyMixing_def.1 hμ) A C hA hC) h₂
  simp_rw [inner_rectL2_koopmanGroup hA hB hC hD, intervalIntegral.integral_ofReal]
  refine ((Complex.continuous_ofReal.tendsto _).comp hlim).congr fun T => ?_
  simp

/-- For `X` weakly mixing and `Y` ergodic, the averaged Koopman correlations of any `F` with a
rectangle `G` tend to `(∫ G) conj (∫ F)`. -/
private theorem tendsto_average_inner_koopmanGroup_rectL2 [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [VAddInvariantMeasure ℝ X μ] [ErgodicVAdd ℝ Y ν]
    (hμ : IsWeaklyMixing μ) {A : Set X} {B : Set Y} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (F : Lp ℂ 2 (μ.prod ν)) :
    Tendsto (fun T : ℝ => (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T,
        ⟪F, TauCeti.koopmanGroup (μ.prod ν) ℂ 2 ENNReal.ofNat_ne_top t (rectL2 hA hB)⟫_ℂ) atTop
      (𝓝 ((∫ z, rectL2 (μ := μ) (ν := ν) hA hB z ∂(μ.prod ν)) *
        conj (∫ z, F z ∂(μ.prod ν)))) := by
  obtain ⟨L, hL⟩ :=
    TauCeti.exists_tendsto_average_inner (TauCeti.koopmanGroup_isUnitary (μ.prod ν) ℂ)
      (rectL2 hA hB)
  suffices hLc : L = TauCeti.constL2 (∫ z, rectL2 (μ := μ) (ν := ν) hA hB z ∂(μ.prod ν)) by
    have h := hL F
    rw [hLc] at h
    convert h using 2
    exact (TauCeti.inner_constL2_right _ F).symm
  rw [← sub_eq_zero]
  refine Lp.eq_zero_of_forall_inner_indicatorConstLp_prod _ fun C D hC hD => ?_
  have h₁ := tendsto_nhds_unique (hL (rectL2 hC hD)) (tendsto_average_inner_rectL2 hμ hA hB hC hD)
  rw [inner_sub_right, h₁, TauCeti.inner_constL2_right, integral_rectL2 hA hB,
    integral_rectL2 hC hD, sub_eq_zero, Complex.conj_ofReal]
  push_cast
  ring

/-- **The multiplier property of weak mixing.** Let `ℝ` act jointly measurably on `X` and on `Y`,
preserving probability measures `μ` and `ν`. If the action on `X` is weakly mixing and the action
on `Y` is ergodic, then the diagonal action on `X × Y` is ergodic for `μ.prod ν`. -/
theorem ergodicVAdd_prod_of_isWeaklyMixing [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [VAddInvariantMeasure ℝ X μ] [ErgodicVAdd ℝ Y ν] (hμ : IsWeaklyMixing μ) :
    ErgodicVAdd ℝ (X × Y) (μ.prod ν) := by
  refine TauCeti.ergodicVAdd_of_forall_koopmanGroup_eq fun F hF => ⟨∫ z, F z ∂(μ.prod ν), ?_⟩
  -- `F` minus its integral is orthogonal to every rectangle
  suffices hFc : F = TauCeti.constL2 (∫ z, F z ∂(μ.prod ν)) from
    TauCeti.ae_eq_const_of_eq_constL2 hFc
  rw [← sub_eq_zero]
  refine Lp.eq_zero_of_forall_inner_indicatorConstLp_prod _ fun A B hA hB => ?_
  have hconst : ⟪F, rectL2 hA hB⟫_ℂ =
      (∫ z, rectL2 (μ := μ) (ν := ν) hA hB z ∂(μ.prod ν)) * conj (∫ z, F z ∂(μ.prod ν)) :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun T hT =>
      (TauCeti.average_inner_of_forall_eq (TauCeti.koopmanGroup_isUnitary (μ.prod ν) ℂ) hF
        (rectL2 hA hB) hT).symm)) (tendsto_average_inner_koopmanGroup_rectL2 hμ hA hB F)
  rw [inner_sub_right, TauCeti.inner_constL2_right, ← inner_conj_symm]
  change conj ⟪F, rectL2 hA hB⟫_ℂ - _ = 0
  rw [hconst, map_mul, Complex.conj_conj, mul_comm, sub_self]

end MeasureTheory.Measure
