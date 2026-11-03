/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.SmoothApproximation
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Analysis.Calculus.FDeriv.InfDist
import TauCeti.Analysis.Calculus.FDeriv.LevelSet
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz

/-!
# The sharp isoperimetric inequality for sets of finite volume

Let `E` be a Euclidean space of dimension `n ≥ 1`, write `ω_n = volume (ball 0 1)`, and write
`P(s)` for the perimeter of `s` in the whole space. Every null-measurable set `s` of finite
positive volume satisfies

`n ω_n^(1/n) |s|^(1 - 1/n) ≤ P(s)`

(`TauCeti.ofReal_mul_volume_real_rpow_mul_le_perimeter`). No boundedness, regularity or finite
perimeter is assumed. Equivalently, `P(s)^n ≥ n^n ω_n |s|^(n-1)`
(`TauCeti.finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow_of_volume_ne_zero`), and in
dimension `n ≥ 2` this classical form holds for every set of finite volume
(`TauCeti.finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow`).
Balls attain equality (`TauCeti.perimeter_ball_pow`), which fixes the constant.

The inequality is first proved for a bounded nonempty open set `U = {c < u}` with smooth
boundary, where `u` is smooth and `c` is a regular value
(`TauCeti.ofReal_mul_volume_real_rpow_mul_le_perimeter_of_contDiff`). Write `d` for the distance
to the complement of `U` and `C_t = {t ≤ d}` for the inner parallel sets of `U`. Since
`C_t + ball 0 t ⊆ U`, the Brunn–Minkowski inequality gives
`|U \ C_t| ≥ n ω_n^(1/n) |C_t|^(1 - 1/n) t`. On the other hand the Lipschitz function
`ψ_t = min 1 (d / t)` increases from `0` to `1` across the shell `U \ C_t`, and integrating it by
parts against a test vector field `φ` gives `∫ ψ_t div φ = -∫ Dψ_t(φ)`. Near the boundary the
gradient of `d` points from the nearest boundary point `y` into `U`. At a regular boundary point
this direction is the inner unit normal `∇u(y) / ‖∇u(y)‖`, by the first-order condition for `y`
to minimize the distance to `x` over the sublevel set `{u ≤ c}`. Choosing `φ` to be a smooth
extension of the outer unit normal `-∇u / ‖∇u‖`, its uniform continuity makes `-Dψ_t(φ)` at
least `(1 - ε) / t` almost everywhere on the shell for small `t`. Hence
`(1 - ε) n ω_n^(1/n) |C_t|^(1 - 1/n) ≤ ∫ ψ_t div φ`, and letting `t → 0` bounds the left side
for `U` by `∫_U div φ ≤ P(U)`.

A general set of finite volume is the limit, in volume and in perimeter, of such smooth sets
(`MeasureTheory.NullMeasurableSet.exists_smooth_perimeter_approximation`), and the inequality
passes to the limit.

## Main results

* `TauCeti.ofReal_mul_volume_real_rpow_mul_le_perimeter_of_contDiff`: the inequality for bounded
  open sets with smooth boundary.
* `TauCeti.ofReal_mul_volume_real_rpow_mul_le_perimeter`: the inequality for null-measurable sets
  of finite positive volume, in extended form.
* `TauCeti.mul_volume_real_rpow_mul_le_perimeter_toReal`: the real-valued form, for sets of
  finite perimeter.
* `TauCeti.finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow_of_volume_ne_zero`: the
  form `P(s)^n ≥ n^n ω_n |s|^(n-1)` for sets of finite positive volume.
* `TauCeti.finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow`: the same form in
  dimension `n ≥ 2`, for every set of finite volume.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 13 for the
  approximation by smooth sets and Chapter 14 for the isoperimetric inequality.
* R. J. Gardner, *The Brunn–Minkowski inequality*, Bull. Amer. Math. Soc. **39** (2002),
  355–405, Section 5.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Module Set Filter TopologicalSpace TestFunction InnerProductSpace
open scoped ENNReal Topology RealInnerProductSpace ContDiff Distributions Pointwise symmDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The inner Minkowski bound -/

section Cutoff

variable {X : Type*} [PseudoMetricSpace X]

/-- The cutoff `min 1 (d / t)`, built from the distance `d` to a set, is `t⁻¹`-Lipschitz. -/
private theorem lipschitzWith_min_one_inv_mul_infDist (s : Set X) {t : ℝ} (ht : 0 < t) :
    LipschitzWith (Real.toNNReal t⁻¹) fun x => min 1 (t⁻¹ * infDist x s) := by
  have h1 : LipschitzWith (Real.toNNReal t⁻¹) fun x => t⁻¹ * infDist x s :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.2 ht),
        Real.coe_toNNReal _ (inv_pos.2 ht).le]
      exact mul_le_mul_of_nonneg_left ((lipschitz_infDist_pt s).dist_le_mul x y |>.trans
        (by simp)) (inv_pos.2 ht).le
  exact h1.const_min 1

/-- The cutoff `min 1 (d / t)` equals `1` where the distance `d` to the set is at least `t`. -/
private theorem min_one_inv_mul_infDist_eq_one {s : Set X} {t : ℝ} (ht : 0 < t) {x : X}
    (hx : t ≤ infDist x s) : min 1 (t⁻¹ * infDist x s) = 1 :=
  min_eq_left ((le_inv_mul_iff₀ ht).2 (by simpa using hx))

/-- The cutoff `min 1 (d / t)` vanishes on the set itself. -/
private theorem min_one_inv_mul_infDist_eq_zero {s : Set X} (t : ℝ) {x : X} (hx : x ∈ s) :
    min 1 (t⁻¹ * infDist x s) = 0 := by
  rw [infDist_zero_of_mem hx, mul_zero, min_eq_right zero_le_one]

/-- The inner parallel set `{t ≤ d}` of `U`, where `d` is the distance to the complement,
thickened by the open ball of radius `t`, stays inside `U`. -/
private theorem setOf_le_infDist_compl_add_ball_subset {G : Type*} [SeminormedAddCommGroup G]
    (U : Set G) (t : ℝ) : {x | t ≤ infDist x Uᶜ} + ball (0 : G) t ⊆ U := by
  rintro _ ⟨x, hx, b, hb, rfl⟩
  by_contra h
  have : infDist x Uᶜ ≤ dist x (x + b) := infDist_le_dist_of_mem h
  rw [dist_eq_norm, sub_add_cancel_left, norm_neg] at this
  rw [mem_ball_zero_iff] at hb
  exact absurd ((hx : t ≤ infDist x Uᶜ).trans this) (not_le.2 hb)

end Cutoff

/-- **The cutoff across an inner shell.** Let `U` be an open set other than the whole space, and
let `φ` be a vector field which, at points `x ∈ U` within distance `t₀` of the complement, makes
`-⟪x - y, φ x⟫ ≥ (1 - ε) ‖x - y‖` for every nearest boundary point `y`. For `0 < t ≤ t₀`, the
cutoff `ψ = min 1 (d / t)` built from the distance `d` to the complement then satisfies
`-Dψ(φ) ≥ (1 - ε) / t` almost everywhere on the shell `U \ {t ≤ d}`, and `Dψ = 0` off it. -/
private theorem ae_mul_indicator_le_neg_fderiv_apply {U : Set E} (hU : IsOpen U)
    (hUu : U ≠ univ) {φ : E → E} {ε t t₀ : ℝ} (ht : 0 < t) (htt : t ≤ t₀)
    (hφ : ∀ x ∈ U, ∀ y ∈ frontier U, infDist x Uᶜ < t₀ → infDist x Uᶜ = dist x y →
      (1 - ε) * dist x y ≤ -⟪x - y, φ x⟫) :
    ∀ᵐ x ∂volume, (1 - ε) * t⁻¹ * (U \ {x | t ≤ infDist x Uᶜ}).indicator 1 x ≤
      -fderiv ℝ (fun z => min 1 (t⁻¹ * infDist z Uᶜ)) x (φ x) := by
  set d : E → ℝ := fun x => infDist x Uᶜ
  set ψ : E → ℝ := fun x => min 1 (t⁻¹ * d x)
  have hψ (x : E) : ψ x = min 1 (t⁻¹ * d x) := rfl
  have hdc : Continuous d := (lipschitz_infDist_pt Uᶜ).continuous
  filter_upwards [(lipschitz_infDist_pt Uᶜ).ae_differentiableAt (μ := volume)] with x hdx
  by_cases hx : x ∈ U \ {x | t ≤ d x}
  · obtain ⟨hxU, hxC⟩ := hx
    have hxC' : d x < t := not_le.1 hxC
    -- Near `x` the cutoff is `d / t`, and `d` has derivative `⟪(x - y) / ‖x - y‖, ·⟫`.
    have hloc : ψ =ᶠ[𝓝 x] fun z => t⁻¹ * d z := by
      filter_upwards [(isOpen_lt hdc continuous_const).mem_nhds hxC'] with z hz
      exact min_eq_right ((inv_mul_le_one₀ ht).2 hz.le)
    obtain ⟨y, hyfr, hxy⟩ := exists_mem_frontier_infDist_compl_eq_dist hxU hUu
    have hyU : y ∈ Uᶜ := by
      rw [hU.frontier_eq] at hyfr
      exact hyfr.2
    have hxy0 : x ≠ y := fun h => hyU (h ▸ hxU)
    have h1 : 1 - ε ≤ -⟪x - y, φ x⟫ / dist x y := by
      rw [le_div_iff₀ (dist_pos.2 hxy0)]
      exact hφ x hxU y hyfr (hxC'.trans_le htt) hxy
    rw [indicator_of_mem ((Set.mem_sdiff x).2 ⟨hxU, hxC⟩), Pi.one_apply, mul_one,
      hloc.fderiv_eq, fderiv_const_mul hdx, smul_apply, smul_eq_mul,
      fderiv_infDist_apply hyU hxy hxy0 hdx]
    calc (1 - ε) * t⁻¹ ≤ (-⟪x - y, φ x⟫ / dist x y) * t⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 ht.le)
      _ = -(t⁻¹ * (⟪x - y, φ x⟫ / dist x y)) := by ring
  · rw [indicator_of_notMem hx, mul_zero]
    rw [Set.mem_sdiff, not_and_or, not_not] at hx
    rcases hx with hxU | hxC
    · -- Off `U` the cutoff attains its minimum `0`.
      have h0 : ψ x = 0 := min_one_inv_mul_infDist_eq_zero t hxU
      have hmin : IsLocalMin ψ x := Eventually.of_forall fun z => by
        rw [h0, hψ]
        exact le_min zero_le_one (mul_nonneg (inv_nonneg.2 ht.le) infDist_nonneg)
      simp [hmin.fderiv_eq_zero]
    · -- On `{t ≤ d}` the cutoff attains its maximum `1`.
      have h1 : ψ x = 1 := min_one_inv_mul_infDist_eq_one ht hxC
      have hmax : IsLocalMax ψ x := Eventually.of_forall fun z => by
        rw [h1, hψ]
        exact min_le_left _ _
      simp [hmax.fderiv_eq_zero]

/-- **The inner Minkowski bound at a fixed scale.** Let `U` be an open set of finite volume other
than the whole space, and let `φ` be a test vector field which, at points `x ∈ U` within distance
`t₀` of the complement, makes `-⟪x - y, φ x⟫ ≥ (1 - ε) ‖x - y‖` for every nearest boundary point
`y`. For `0 < t ≤ t₀` with nonempty inner parallel set `C = {t ≤ d}`, where `d` is the distance
to the complement, the cutoff `ψ = min 1 (d / t)` satisfies
`(1 - ε) n ω_n^(1/n) |C|^(1 - 1/n) ≤ ∫ ψ div φ`. -/
private theorem mul_le_integral_divergenceCLM_mul_min {U : Set E} (hn : finrank ℝ E ≠ 0)
    (hU : IsOpen U) (hUu : U ≠ univ) (hUfin : volume U ≠ ⊤) (φ : 𝓓(⊤, E)) {ε t t₀ : ℝ}
    (hε : ε < 1) (ht : 0 < t) (htt : t ≤ t₀) (hCne : {x | t ≤ infDist x Uᶜ}.Nonempty)
    (hφ : ∀ x ∈ U, ∀ y ∈ frontier U, infDist x Uᶜ < t₀ → infDist x Uᶜ = dist x y →
      (1 - ε) * dist x y ≤ -⟪x - y, φ x⟫) :
    (1 - ε) * (finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real {x | t ≤ infDist x Uᶜ} ^ (1 - (finrank ℝ E : ℝ)⁻¹)) ≤
      ∫ x, divergenceCLM φ x * min 1 (t⁻¹ * infDist x Uᶜ) := by
  set C := {x | t ≤ infDist x Uᶜ}
  set ψ : E → ℝ := fun x => min 1 (t⁻¹ * infDist x Uᶜ)
  set K := finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹
  have hψlip := lipschitzWith_min_one_inv_mul_infDist Uᶜ ht
  have hCclosed : IsClosed C := isClosed_le continuous_const (lipschitz_infDist_pt Uᶜ).continuous
  have hCU := setOf_le_infDist_compl_add_ball_subset U t
  have hCsub : C ⊆ U := fun x hx => hCU ⟨x, hx, 0, mem_ball_self ht, add_zero x⟩
  -- Integrate the cutoff by parts against `φ`.
  have hibp := (hψlip.locallyLipschitz.locallyLipschitzOn.hasWeakFDerivOn_fderiv
    (μ := volume) (Ω := ⊤)).integral_divergenceCLM_smul_eq_neg_integral φ
  simp only [smul_eq_mul] at hibp
  rw [hibp, ← integral_neg]
  have hmeasS : MeasurableSet (U \ C) := hU.measurableSet.diff hCclosed.measurableSet
  have hSfin : volume (U \ C) ≠ ⊤ := ne_top_of_le_ne_top hUfin (measure_mono sdiff_subset)
  have hlow : Integrable (fun x => (1 - ε) * t⁻¹ * (U \ C).indicator 1 x) volume :=
    ((integrable_indicator_iff hmeasS).2 (integrableOn_const hSfin)).const_mul _
  have hint : Integrable (fun x => -fderiv ℝ ψ x (φ x)) volume := by
    refine Integrable.neg (Integrable.mono'
      ((φ.continuous.norm.integrable_of_hasCompactSupport φ.hasCompactSupport.norm).const_mul
        t⁻¹) ?_ (Eventually.of_forall fun x => ?_))
    · exact (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).aestronglyMeasurable_comp₂
        (measurable_fderiv ℝ ψ).aestronglyMeasurable φ.continuous.aestronglyMeasurable
    · refine (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      simpa [Real.coe_toNNReal _ (inv_pos.2 ht).le] using
        norm_fderiv_le_of_lipschitz ℝ hψlip (x₀ := x)
  -- Brunn–Minkowski bounds `t K |C|^(1 - 1/n)` by the volume of the shell `U \ C`, which the
  -- cutoff crosses at rate at least `(1 - ε) / t` along `φ`.
  have hBM := mul_volume_real_rpow_mul_le_volume_real_sub_of_add_ball_subset hn hCne
    hCclosed.measurableSet.nullMeasurableSet hUfin ht hCU
  calc (1 - ε) * (K * volume.real C ^ (1 - (finrank ℝ E : ℝ)⁻¹))
      = (1 - ε) * t⁻¹ * (K * volume.real C ^ (1 - (finrank ℝ E : ℝ)⁻¹) * t) := by
        field_simp
    _ ≤ (1 - ε) * t⁻¹ * volume.real (U \ C) := by
        rw [measureReal_sdiff hCsub hCclosed.measurableSet hUfin]
        exact mul_le_mul_of_nonneg_left hBM (mul_nonneg (by linarith) (inv_nonneg.2 ht.le))
    _ = ∫ x, (1 - ε) * t⁻¹ * (U \ C).indicator 1 x := by
        rw [integral_const_mul, integral_indicator_one hmeasS]
    _ ≤ ∫ x, -fderiv ℝ ψ x (φ x) := integral_mono_ae hlow hint
        (ae_mul_indicator_le_neg_fderiv_apply hU hUu ht htt hφ)

/-- **The inner Minkowski bound.** Let `U` be a bounded nonempty open set, and let `φ` be a test
vector field which, at points `x ∈ U` within distance `t₀` of the complement, makes
`-⟪x - y, φ x⟫ ≥ (1 - ε) ‖x - y‖` for every nearest boundary point `y`. Then
`(1 - ε) n ω_n^(1/n) |U|^(1 - 1/n) ≤ ∫_U div φ`. -/
private theorem mul_le_setIntegral_divergenceCLM {U : Set E} (hn : finrank ℝ E ≠ 0)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty) (φ : 𝓓(⊤, E))
    {ε t₀ : ℝ} (hε : ε < 1) (ht₀ : 0 < t₀)
    (hφ : ∀ x ∈ U, ∀ y ∈ frontier U, infDist x Uᶜ < t₀ → infDist x Uᶜ = dist x y →
      (1 - ε) * dist x y ≤ -⟪x - y, φ x⟫) :
    (1 - ε) * (finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real U ^ (1 - (finrank ℝ E : ℝ)⁻¹)) ≤
      ∫ x in U, divergenceCLM φ x := by
  set n := finrank ℝ E
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hn)
  have hUu : U ≠ univ := fun h => NormedSpace.unbounded_univ ℝ E (h ▸ hUb)
  set d : E → ℝ := fun x => infDist x Uᶜ
  have hdpos (x : E) (hx : x ∈ U) : 0 < d x :=
    (hU.isClosed_compl.notMem_iff_infDist_pos (nonempty_compl.2 hUu)).1 (not_not_intro hx)
  have hUfin : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hVpos : 0 < volume.real U :=
    ENNReal.toReal_pos (hU.measure_ne_zero volume hUne) hUfin
  obtain ⟨x₀, hx₀⟩ := hUne
  set t₁ := min t₀ (d x₀)
  have ht₁ : 0 < t₁ := lt_min ht₀ (hdpos x₀ hx₀)
  -- The inner parallel sets `C t = {t ≤ d}`.
  set C : ℝ → Set E := fun t => {x | t ≤ d x}
  set K := n * volume.real (ball (0 : E) 1) ^ (n : ℝ)⁻¹
  -- Let `t → 0` along `t₁ / (k + 1)`. Then `C t` increases to `U` and the cutoff
  -- `min 1 (d / t)` increases to the indicator of `U`.
  set tk : ℕ → ℝ := fun k => t₁ / (k + 1)
  have htk (k : ℕ) : 0 < tk k := by positivity
  have htk1 (k : ℕ) : tk k ≤ t₁ :=
    div_le_self ht₁.le (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
  have htk0 : Tendsto tk atTop (𝓝 0) := by
    simpa [tk, div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul t₁
  have hev (x : E) (hx : x ∈ U) : ∀ᶠ k in atTop, tk k ≤ d x :=
    htk0.eventually (eventually_le_nhds (hdpos x hx))
  have hmono : Monotone fun k => C (tk k) := fun k l hkl x hx =>
    (div_le_div_of_nonneg_left ht₁.le (by positivity) (by gcongr)).trans hx
  have hUnion : ⋃ k, C (tk k) = U :=
    Subset.antisymm (iUnion_subset fun k x hx => setOf_le_infDist_compl_add_ball_subset U _
        ⟨x, hx, 0, mem_ball_self (htk k), add_zero x⟩) fun x hx =>
      mem_iUnion.2 (hev x hx).exists
  have hVk : Tendsto (fun k => volume.real (C (tk k))) atTop (𝓝 (volume.real U)) := by
    have h := tendsto_measure_iUnion_atTop (μ := volume) hmono
    rw [hUnion] at h
    exact (ENNReal.tendsto_toReal hUfin).comp h
  have hIk : Tendsto (fun k => ∫ x, divergenceCLM φ x * min 1 ((tk k)⁻¹ * d x)) atTop
      (𝓝 (∫ x in U, divergenceCLM φ x)) := by
    rw [← integral_indicator hU.measurableSet]
    refine tendsto_integral_of_dominated_convergence (fun x => ‖divergenceCLM φ x‖)
      (fun k => ((divergenceCLM φ).continuous.mul
        (lipschitzWith_min_one_inv_mul_infDist Uᶜ (htk k)).continuous).aestronglyMeasurable)
      ((divergenceCLM φ).continuous.integrable_of_hasCompactSupport
        (divergenceCLM φ).hasCompactSupport).norm (fun k => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · rw [norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      rw [Real.norm_of_nonneg (le_min zero_le_one
        (mul_nonneg (inv_nonneg.2 (htk k).le) infDist_nonneg))]
      exact min_le_left _ _
    · by_cases hx : x ∈ U
      · rw [indicator_of_mem hx]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev x hx] with k hk
        rw [min_one_inv_mul_infDist_eq_one (htk k) hk, mul_one]
      · rw [indicator_of_notMem hx]
        refine tendsto_const_nhds.congr fun k => ?_
        rw [min_one_inv_mul_infDist_eq_zero _ (show x ∈ Uᶜ from hx), mul_zero]
  have hLk : Tendsto (fun k => (1 - ε) * (K * volume.real (C (tk k)) ^ (1 - (n : ℝ)⁻¹)))
      atTop (𝓝 ((1 - ε) * (K * volume.real U ^ (1 - (n : ℝ)⁻¹)))) :=
    (((Real.continuousAt_rpow_const _ _ (Or.inl hVpos.ne')).tendsto.comp hVk).const_mul
      K).const_mul (1 - ε)
  exact le_of_tendsto_of_tendsto' hLk hIk fun k =>
    mul_le_integral_divergenceCLM_mul_min hn hU hUu hUfin φ hε (htk k)
      ((htk1 k).trans (min_le_left _ _)) ⟨x₀, (htk1 k).trans (min_le_right _ _)⟩ hφ

/-! ### Bounded open sets with smooth boundary -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A smooth extension of the outer unit normal.** Let `u` be smooth and `c` a regular value
of `u` on the boundary of the bounded superlevel set `U = {c < u}`. There is a test vector field
`φ` with `‖φ‖ ≤ 1` which equals the outer unit normal `-∇u / ‖∇u‖` on the frontier of `U`. By
uniform continuity, for every `ε > 0` it makes `-⟪x - y, φ x⟫ ≥ (1 - ε) ‖x - y‖` at points
`x ∈ U` close to the complement and their nearest boundary points `y`. -/
private theorem exists_testFunction_outer_normal {u : E → ℝ} {c : ℝ} (hu : ContDiff ℝ ∞ u)
    (hreg : ∀ x, u x = c → fderiv ℝ u x ≠ 0) (hb : Bornology.IsBounded {x | c < u x}) :
    ∃ φ : 𝓓(⊤, E), (∀ x, ‖φ x‖ ≤ 1) ∧ ∀ ε > 0, ∃ t₀ > 0, ∀ x ∈ {x | c < u x},
      ∀ y ∈ frontier {x | c < u x}, infDist x {x | c < u x}ᶜ < t₀ →
        infDist x {x | c < u x}ᶜ = dist x y → (1 - ε) * dist x y ≤ -⟪x - y, φ x⟫ := by
  set U := {x | c < u x}
  set G := gradient u
  have hG : ContDiff ℝ ∞ G := hu.gradient_right (by simp)
  -- The frontier of `U` is a compact part of the level `{u = c}` where `∇u ≠ 0`.
  have hZc : IsCompact (frontier U) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hZlev (y : E) (hy : y ∈ frontier U) : u y = c :=
    (frontier_lt_subset_eq continuous_const hu.continuous hy).symm
  have hZO : frontier U ⊆ {x | G x ≠ 0} := fun x hx h0 => hreg x (hZlev x hx) (by
    rw [← (toDual ℝ E).apply_symm_apply (fderiv ℝ u x)]
    exact (toDual ℝ E).map_eq_zero_iff.2 h0)
  -- A smooth cutoff `χ`, equal to one exactly on the frontier and supported where `∇u ≠ 0`.
  obtain ⟨δ, hδ, hδO⟩ :=
    hZc.exists_cthickening_subset_open (isOpen_ne_fun hG.continuous continuous_const) hZO
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    isOpen_thickening isClosed_frontier (self_subset_thickening hδ (frontier U))
  have hχts : tsupport χ ⊆ cthickening δ (frontier U) := by
    rw [tsupport, hχs]
    exact closure_thickening_subset_cthickening δ _
  -- The field `χ N` with `N = -∇u / ‖∇u‖`.
  set N : E → E := fun x => -(‖G x‖⁻¹ • G x)
  set f : E → E := fun x => χ x • N x
  have hf : ContDiff ℝ ∞ f := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : G x = 0
    · have h0 : f =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1
          fun h => hδO (hχts h) hx] with z hz
        simp [f, hz]
      exact contDiffAt_const.congr_of_eventuallyEq h0
    · have hGx := hG.contDiffAt (x := x)
      exact hχ.contDiffAt.smul ((((contDiffAt_norm ℝ hx).comp x hGx).inv
        (norm_ne_zero_iff.2 hx)).smul hGx).neg
  have hχc : HasCompactSupport χ :=
    hZc.cthickening.of_isClosed_subset (isClosed_tsupport _) hχts
  have hfc : HasCompactSupport f := hχc.smul_right
  have hNle (x : E) : ‖N x‖ ≤ 1 := by
    rw [norm_neg, norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne ‖G x‖ 0 with h | h
    · simp [h]
    · rw [inv_mul_cancel₀ h]
  have hN1 (y : E) (hy : y ∈ frontier U) : ‖N y‖ = 1 := by
    rw [norm_neg, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 (hZO hy))]
  have hfN (y : E) (hy : y ∈ frontier U) : f y = N y := by
    simp [f, (hχ1 y).1 hy]
  refine ⟨⟨f, hf, hfc, by simp⟩, fun x => ?_, fun ε hε => ?_⟩
  · have hχx := hχr ⟨x, rfl⟩
    rw [coe_mk, norm_smul, Real.norm_of_nonneg hχx.1]
    simpa using mul_le_mul hχx.2 (hNle x) (norm_nonneg _) zero_le_one
  obtain ⟨η, hη, hηf⟩ := Metric.uniformContinuous_iff.1
    (hfc.uniformContinuous_of_continuous hf.continuous) ε hε
  refine ⟨η, hη, fun x hx y hyfr hd hxy => ?_⟩
  rw [coe_mk]
  -- At the nearest boundary point, `x - y` is a nonnegative multiple of `∇u(y)`, so of `-N y`.
  have hw : x - y = -‖x - y‖ • N y := by
    have hy : y ∈ Uᶜ := by
      rw [isOpen_lt continuous_const hu.continuous |>.frontier_eq] at hyfr
      exact hyfr.2
    have hmin (z : E) (hz : u z ≤ u y) : dist x y ≤ dist x z :=
      hxy ▸ infDist_le_dist_of_mem (show z ∉ U from not_lt.2 (hz.trans (hZlev y hyfr).le))
    conv_lhs => rw [(hu.differentiable (by simp) y).sub_eq_smul_gradient_of_forall_dist_le
      (hZO hyfr) hmin]
    simp only [N, smul_neg, smul_smul, div_eq_mul_inv, G, neg_mul, neg_smul, neg_neg]
  have hin : 1 - ε ≤ ⟪N y, f x⟫ := by
    have h1 : ⟪N y, f x⟫ = ‖N y‖ ^ 2 + ⟪N y, f x - f y⟫ := by
      rw [inner_sub_right, hfN y hyfr, real_inner_self_eq_norm_sq]
      ring
    have h2 := (abs_le.1 ((abs_real_inner_le_norm (N y) (f x - f y)).trans_eq
      (by rw [hN1 y hyfr, one_mul]))).1
    have h3 : ‖f x - f y‖ < ε := by
      rw [← dist_eq_norm]
      exact hηf (hxy ▸ hd)
    rw [h1, hN1 y hyfr]
    linarith
  have hinner : ⟪x - y, f x⟫ = -‖x - y‖ * ⟪N y, f x⟫ := by
    conv_lhs => rw [hw]
    rw [real_inner_smul_left]
  rw [hinner, dist_eq_norm]
  nlinarith [norm_nonneg (x - y)]

/-- **The isoperimetric inequality for bounded open sets with smooth boundary.** Let `u` be a
smooth function and `c` a regular value of `u`, so that the derivative of `u` vanishes nowhere on
the level `{u = c}`. If the superlevel set `U = {c < u}` is bounded and nonempty, then in
dimension `n ≥ 1` it satisfies `n ω_n^(1/n) |U|^(1 - 1/n) ≤ P(U)`, where
`ω_n = volume (ball 0 1)`. -/
theorem ofReal_mul_volume_real_rpow_mul_le_perimeter_of_contDiff {u : E → ℝ} {c : ℝ}
    (hn : finrank ℝ E ≠ 0) (hu : ContDiff ℝ ∞ u) (hreg : ∀ x, u x = c → fderiv ℝ u x ≠ 0)
    (hb : Bornology.IsBounded {x | c < u x}) (hne : {x | c < u x}.Nonempty) :
    ENNReal.ofReal (finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real {x | c < u x} ^ (1 - (finrank ℝ E : ℝ)⁻¹)) ≤
      perimeter volume ⊤ {x | c < u x} := by
  set U := {x | c < u x}
  set A := (finrank ℝ E : ℝ) * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
    volume.real U ^ (1 - (finrank ℝ E : ℝ)⁻¹)
  have hUo : IsOpen U := isOpen_lt continuous_const hu.continuous
  obtain ⟨φ, hφ1, hnorm⟩ := exists_testFunction_outer_normal hu hreg hb
  -- Each `ε ∈ (0, 1)` gives `(1 - ε) A ≤ ∫_U div φ ≤ P(U)`; let `ε → 0`.
  have hP (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
      ENNReal.ofReal ((1 - ε) * A) ≤ perimeter volume ⊤ U := by
    obtain ⟨t₀, ht₀, h⟩ := hnorm ε hε
    calc ENNReal.ofReal ((1 - ε) * A) ≤ ENNReal.ofReal (∫ x in U, divergenceCLM φ x) :=
          ENNReal.ofReal_le_ofReal (mul_le_setIntegral_divergenceCLM hn hUo hb hne φ hε1 ht₀ h)
      _ ≤ perimeter volume ⊤ U := by
          rw [perimeter_eq_iSup hUo.measurableSet.nullMeasurableSet]
          exact le_iSup₂_of_le (f := fun (φ : 𝓓(⊤, E)) (_ : ∀ x, ‖φ x‖ ≤ 1) =>
            ENNReal.ofReal (∫ x in U, divergenceCLM φ x ∂volume)) φ hφ1 le_rfl
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 - ε) * A)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal A)) := by
    refine ENNReal.tendsto_ofReal ?_
    have : Continuous fun ε : ℝ => (1 - ε) * A := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε using hP ε hε.1 hε.2

/-! ### Sets of finite volume -/

/-- **The isoperimetric inequality.** In dimension `n ≥ 1`, every null-measurable set `s` of
finite positive volume satisfies `n ω_n^(1/n) |s|^(1 - 1/n) ≤ P(s)`, where
`ω_n = volume (ball 0 1)` and `P(s)` is the perimeter of `s` in the whole space. The perimeter may
be infinite, and `s` need not be bounded. -/
theorem ofReal_mul_volume_real_rpow_mul_le_perimeter {s : Set E} (hn : finrank ℝ E ≠ 0)
    (hs : NullMeasurableSet s volume) (hμs : volume s ≠ ⊤) (hs0 : volume s ≠ 0) :
    ENNReal.ofReal (finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real s ^ (1 - (finrank ℝ E : ℝ)⁻¹)) ≤ perimeter volume ⊤ s := by
  obtain ⟨u, t, hprop, hvol, hper⟩ := hs.exists_smooth_perimeter_approximation hμs
  set U : ℕ → Set E := fun k => {x | t k < u k x}
  have hUm (k : ℕ) : NullMeasurableSet (U k) volume :=
    (isOpen_lt continuous_const (hprop k).1.continuous).measurableSet.nullMeasurableSet
  have hUb (k : ℕ) : Bornology.IsBounded (U k) :=
    (hprop k).2.2.2.2.1.isBounded.subset subset_closure
  have hUfin (k : ℕ) : volume (U k) ≠ ⊤ := (hUb k).measure_lt_top.ne
  -- The volumes converge.
  have h0 : Tendsto (fun k => volume.real (U k ∆ s)) atTop (𝓝 0) := by
    simpa [Function.comp_def, measureReal_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hvol
  have hVk : Tendsto (fun k => volume.real (U k)) atTop (𝓝 (volume.real s)) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2
      (squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) h0)
    rw [Real.norm_eq_abs]
    exact abs_measureReal_sub_le_measureReal_symmDiff' (hUm k) hs (hUfin k) hμs
  have hV0 : 0 < volume.real s := ENNReal.toReal_pos hs0 hμs
  -- Eventually the approximations are nonempty, and the smooth case applies.
  have hev : ∀ᶠ k in atTop,
      ENNReal.ofReal (finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real (U k) ^ (1 - (finrank ℝ E : ℝ)⁻¹)) ≤ perimeter volume ⊤ (U k) := by
    filter_upwards [hVk.eventually (lt_mem_nhds hV0)] with k hk
    obtain ⟨hu, -, -, hreg, -⟩ := hprop k
    refine ofReal_mul_volume_real_rpow_mul_le_perimeter_of_contDiff hn hu
      (fun x hx h0 => ?_) (hUb k) (nonempty_of_measure_ne_zero (μ := volume) fun h => ?_)
    · obtain ⟨v, hv⟩ := hreg x hx 1
      simp [h0] at hv
    · exact hk.ne' ((congrArg ENNReal.toReal h).trans ENNReal.toReal_zero)
  exact le_of_tendsto_of_tendsto (ENNReal.tendsto_ofReal
    (((Real.continuousAt_rpow_const _ _ (Or.inl hV0.ne')).tendsto.comp hVk).const_mul _))
    hper hev

/-- **The isoperimetric inequality, in real-valued form.** In dimension `n ≥ 1`, every
null-measurable set `s` of finite positive volume and finite perimeter satisfies
`n ω_n^(1/n) |s|^(1 - 1/n) ≤ P(s)`, where `ω_n = volume (ball 0 1)`. -/
theorem mul_volume_real_rpow_mul_le_perimeter_toReal {s : Set E} (hn : finrank ℝ E ≠ 0)
    (hs : NullMeasurableSet s volume) (hμs : volume s ≠ ⊤) (hs0 : volume s ≠ 0)
    (hP : perimeter volume ⊤ s ≠ ⊤) :
    finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real s ^ (1 - (finrank ℝ E : ℝ)⁻¹) ≤ (perimeter volume ⊤ s).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hP).1
    (ofReal_mul_volume_real_rpow_mul_le_perimeter hn hs hμs hs0)

/-- The isoperimetric bound `n^n ω_n |s|^(n-1)` is the `n`-th power of the real quantity
`n ω_n^(1/n) |s|^(1 - 1/n)`, read in `ℝ≥0∞`, for every set `s` of finite volume in dimension
`n ≥ 1`. Here `ω_n = volume (ball 0 1)`. -/
theorem finrank_pow_mul_volume_ball_mul_volume_pow_eq_ofReal {s : Set E} (hn : finrank ℝ E ≠ 0)
    (hμs : volume s ≠ ⊤) :
    (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
        volume s ^ (finrank ℝ E - 1) =
      ENNReal.ofReal ((finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real s ^ (1 - (finrank ℝ E : ℝ)⁻¹)) ^ finrank ℝ E) := by
  rw [mul_pow, mul_pow, Real.rpow_inv_natCast_pow measureReal_nonneg hn,
    Real.rpow_one_sub_inv_natCast_pow measureReal_nonneg hn]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  simp [ENNReal.ofReal_pow, measure_ball_lt_top.ne, hμs]

/-- **The isoperimetric inequality.** In dimension `n ≥ 1`, every null-measurable set `s` of
finite positive volume satisfies `P(s)^n ≥ n^n ω_n |s|^(n-1)`, where `ω_n = volume (ball 0 1)` and
`P(s)` is the perimeter of `s` in the whole space. -/
theorem finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow_of_volume_ne_zero
    {s : Set E} (hn : finrank ℝ E ≠ 0) (hs : NullMeasurableSet s volume) (hμs : volume s ≠ ⊤)
    (hs0 : volume s ≠ 0) :
    (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
        volume s ^ (finrank ℝ E - 1) ≤ perimeter volume ⊤ s ^ finrank ℝ E := by
  rw [finrank_pow_mul_volume_ball_mul_volume_pow_eq_ofReal hn hμs,
    ENNReal.ofReal_pow (by positivity)]
  exact pow_le_pow_left₀ zero_le (ofReal_mul_volume_real_rpow_mul_le_perimeter hn hs hμs hs0) _

/-- **The isoperimetric inequality.** In dimension `n ≥ 2`, every null-measurable set `s` of finite
volume satisfies `P(s)^n ≥ n^n ω_n |s|^(n-1)`, where `ω_n = volume (ball 0 1)` and `P(s)` is the
perimeter of `s` in the whole space. -/
theorem finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow {s : Set E}
    (hn : 2 ≤ finrank ℝ E) (hs : NullMeasurableSet s volume) (hμs : volume s ≠ ⊤) :
    (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
        volume s ^ (finrank ℝ E - 1) ≤ perimeter volume ⊤ s ^ finrank ℝ E := by
  rcases eq_or_ne (volume s) 0 with hs0 | hs0
  · rw [hs0, zero_pow (by omega), mul_zero]
    exact zero_le
  exact finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow_of_volume_ne_zero (by omega)
    hs hμs hs0

end TauCeti
