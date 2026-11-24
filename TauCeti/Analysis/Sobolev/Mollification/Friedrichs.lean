/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.Rescale
public import TauCeti.Analysis.Calculus.ContDiff.Convolution
public import TauCeti.Analysis.Convolution.Commutator
public import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.Analysis.Calculus.ContDiff.FDerivApply
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.LpSeminorm.FDeriv
import TauCeti.Topology.Algebra.Support
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Friedrichs' lemma on commutators with mollifiers

Let `a : E → (F →L[ℝ] F')` be a `C¹` field of operators that is Lipschitz, `v ∈ E` a direction and
`ρ` a smooth compactly supported kernel. The first-order operator `g ↦ a ∂ᵥ g` does not commute
with mollification `g ↦ ρ ⋆ g`. Friedrichs' lemma is stated for the commutator of `∂ᵥ (ρ ⋆ ·)`
with multiplication by `a`, which has both derivatives on the smooth side and so is defined for
every locally integrable `g`:

`C_ρ g = ∂ᵥ (ρ ⋆ (a g)) - a ∂ᵥ (ρ ⋆ g)`

(`TauCeti.mollifierCommutator`). It is not the commutator of mollification with `a ∂ᵥ`,
`[ρ ⋆ ·, a ∂ᵥ] g = ρ ⋆ (a ∂ᵥ g) - a ∂ᵥ (ρ ⋆ g)`: by the product rule
`∂ᵥ (a g) = (∂ᵥ a) g + a ∂ᵥ g`, so `C_ρ g = [ρ ⋆ ·, a ∂ᵥ] g + ρ ⋆ ((∂ᵥ a) g)`. Where
`[ρ ⋆ ·, a ∂ᵥ] g` tends to `0`, `C_ρ g` tends to `(∂ᵥ a) g`. **Friedrichs' lemma** says that
along normalized bumps `ρᵢ` with a fixed ratio of radii whose outer radii tend to zero (the usual
mollifiers `ε⁻ⁿ ρ (x / ε)`), for every `g ∈ Lᵖ` with `1 ≤ p < ∞`,

`C_{ρᵢ} g → (∂ᵥ a) g` in `Lᵖ`

(`TauCeti.tendsto_eLpNorm_mollifierCommutator_sub`). For `C¹` functions `g` this is the product
rule `∂ᵥ (a g) - a ∂ᵥ g = (∂ᵥ a) g` in the limit; the content is that it persists for every
`g ∈ Lᵖ`, where neither `∂ᵥ (a g)` nor `a ∂ᵥ g` is a function.

Its main consequence is that weak solutions of first-order systems are strong
(`TauCeti.tendsto_eLpNorm_sum_apply_fderiv_convolution_sub`): if `g, f ∈ Lᵖ` and
`∑ⱼ aⱼ ∂_{wⱼ} g = f` in the sense of distributions, then the smooth functions `ρᵢ ⋆ g`, which
converge to `g` in `Lᵖ`, satisfy `∑ⱼ aⱼ ∂_{wⱼ} (ρᵢ ⋆ g) → f` in `Lᵖ`. Combined with an a priori
estimate for an elliptic operator on smooth functions, such as the formal adjoint of a linearized
Floer operator, this shows that the `L²` weak solutions of the operator are Sobolev functions; this
is how the elements of the cokernel of the Sobolev realization of such an operator are shown to
be regular.

The proof is the classical one.

* The commutator is a single integral,
  `C_ρ g x = ∫ (a (x - t) - a x) (∂ᵥ ρ t • g (x - t)) dt`
  (`TauCeti.mollifierCommutator_eq_integral`), since the derivative of `ρ ⋆ h` in the direction
  `v` is `∂ᵥ ρ ⋆ h` (`HasCompactSupport.fderiv_convolution_left_apply`). Since `a` is
  `K`-Lipschitz, Young's inequality bounds it in `Lᵖ` by `K` times the first moment
  `∫ ‖t‖ ‖∂ᵥ ρ t‖ dt` of `∂ᵥ ρ` times `‖g‖_p`
  (`TauCeti.eLpNorm_mollifierCommutator_le`, from
  `MeasureTheory.eLpNorm_integral_sub_apply_smul_le`).
* This moment does not change under rescaling the kernel. Normalized bumps `φ.normed μ` with the
  same ratio of radii are rescalings of each other
  (`ContDiffBump.normed_eq_mul_normed_smul_of_rOut_div_rIn_eq`), so they have the same moment
  (`ContDiffBump.lintegral_eNorm_mul_eNorm_fderiv_normed_apply_eq`). Along bumps with a fixed ratio
  of radii, the usual mollifiers `ε⁻ⁿ ρ (x / ε)`, the commutators are uniformly bounded on `Lᵖ`
  (the moment is finite by `HasCompactSupport.lintegral_eNorm_mul_eNorm_fderiv_apply_ne_top`).
* For `g` smooth with compact support the derivatives can be moved onto `g`:
  `C_ρ g = ρ ⋆ ∂ᵥ (a g) - a (ρ ⋆ ∂ᵥ g)`
  (`TauCeti.mollifierCommutator_eq_sub_of_hasCompactSupport`), which converges in `Lᵖ` to
  `∂ᵥ (a g) - a ∂ᵥ g = (∂ᵥ a) g` (`TauCeti.tendsto_eLpNorm_apply_normed_convolution_sub`), and
  `(∂ᵥ a) g` is bounded on `Lᵖ` (`LipschitzWith.eLpNorm_fderiv_apply_apply_le`).
* Smooth compactly supported functions are dense in `Lᵖ`, and a uniformly bounded family of
  operators that converges on a dense set converges everywhere.

For the weak solutions, testing the weak equation against `y ↦ ρ (x - y)` gives
`∑ⱼ aⱼ ∂_{wⱼ} (ρ ⋆ g) = ρ ⋆ f + ∑ⱼ (ρ ⋆ (∂_{wⱼ} aⱼ) g - C_ρ g)`, and both `ρᵢ ⋆ (∂_{wⱼ} aⱼ) g` and
`C_{ρᵢ} g` tend to `(∂_{wⱼ} aⱼ) g`.

## Main definitions

* `TauCeti.mollifierCommutator`: the commutator `∂ᵥ (ρ ⋆ (a g)) - a ∂ᵥ (ρ ⋆ g)`.

## Main results

* `TauCeti.mollifierCommutator_eq_integral`: the commutator as a single integral.
* `TauCeti.eLpNorm_mollifierCommutator_le`: its `Lᵖ` bound by the first moment of `∂ᵥ ρ`.
* `TauCeti.tendsto_eLpNorm_mollifierCommutator_sub`: Friedrichs' lemma.
* `TauCeti.tendsto_eLpNorm_sum_apply_fderiv_convolution_sub`: weak solutions of first-order
  systems are strong.

## References

* K. O. Friedrichs, *The identity of weak and strong extensions of differential operators*,
  Trans. Amer. Math. Soc. 55 (1944), 132–151.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Lemma 17.1.5.
* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 2, §7.
-/

public section

noncomputable section

open ContinuousLinearMap Filter Metric MeasureTheory Set Topology
open scoped Convolution ENNReal NNReal Pointwise

variable {E F F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']

namespace TauCeti

section Commutator

variable [MeasurableSpace E] {μ : Measure E}

/-- The **commutator of a mollified derivative with an operator field**: for a kernel `ρ`, an
operator field `a : E → (F →L[ℝ] F')` and a direction `v`, the function
`x ↦ ∂ᵥ (ρ ⋆ (a g)) x - a x (∂ᵥ (ρ ⋆ g) x)`. It is the commutator `[∂ᵥ (ρ ⋆ ·), a]` of
`g ↦ ∂ᵥ (ρ ⋆ g)` with multiplication by `a`, which has both derivatives on the smooth side.
For `C¹` `g`, it equals `[ρ ⋆ ·, a ∂ᵥ] g + ρ ⋆ ((∂ᵥ a) g)`, the commutator of mollification
with `a ∂ᵥ` plus the mollification of `(∂ᵥ a) g`, which is why its limit is `(∂ᵥ a) g` rather
than `0`. -/
def mollifierCommutator (μ : Measure E) (ρ : E → ℝ) (a : E → F →L[ℝ] F') (v : E) (g : E → F) :
    E → F' :=
  fun x ↦ fderiv ℝ (ρ ⋆[lsmul ℝ ℝ, μ] fun y ↦ a y (g y)) x v -
    a x (fderiv ℝ (ρ ⋆[lsmul ℝ ℝ, μ] g) x v)

theorem mollifierCommutator_apply (ρ : E → ℝ) (a : E → F →L[ℝ] F') (v : E) (g : E → F) (x : E) :
    mollifierCommutator μ ρ a v g x = fderiv ℝ (ρ ⋆[lsmul ℝ ℝ, μ] fun y ↦ a y (g y)) x v -
      a x (fderiv ℝ (ρ ⋆[lsmul ℝ ℝ, μ] g) x v) :=
  (rfl)

variable [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] [μ.IsNegInvariant]
  [CompleteSpace F] [CompleteSpace F'] {ρ : E → ℝ} {a : E → F →L[ℝ] F'} {g h : E → F}

omit [FiniteDimensional ℝ E] [CompleteSpace F] [CompleteSpace F'] in
/-- The integrand of the commutator is integrable. -/
private theorem integrable_sub_apply_smul (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ)
    (ha : Continuous a) (hg : LocallyIntegrable g μ) (v x : E) :
    Integrable (fun t ↦ (a (x - t) - a x) (fderiv ℝ ρ t v • g (x - t))) μ := by
  -- The integrand is the operator kernel `t ↦ ∂ᵥ ρ t • (a (x - t) - a x)` applied to `g (x - t)`.
  have hk : HasCompactSupport fun t ↦ fderiv ℝ ρ t v • (a (x - t) - a x) :=
    (hρc.fderiv_apply (𝕜 := ℝ) v).smul_right
  have hkc : Continuous fun t ↦ fderiv ℝ ρ t v • (a (x - t) - a x) :=
    (hρ.continuous_fderiv_apply_const one_ne_zero v).smul
      ((ha.comp (continuous_const.sub continuous_id)).sub continuous_const)
  simpa [map_smul] using
    (hk.convolutionExists_left (ContinuousLinearMap.id ℝ (F →L[ℝ] F')) hkc hg x).integrable

/-- **The commutator of `∂ᵥ (ρ ⋆ ·)` with `a` is a single integral.** For a `C¹` compactly
supported kernel `ρ`, a continuous operator field `a` and a locally integrable `g`,
`∂ᵥ (ρ ⋆ (a g)) x - a x (∂ᵥ (ρ ⋆ g) x) = ∫ (a (x - t) - a x) (∂ᵥ ρ t • g (x - t)) dt`. -/
theorem mollifierCommutator_eq_integral (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ)
    (ha : Continuous a) (hg : LocallyIntegrable g μ) (v x : E) :
    mollifierCommutator μ ρ a v g x = ∫ t, (a (x - t) - a x) (fderiv ℝ ρ t v • g (x - t)) ∂μ := by
  have hag : LocallyIntegrable (fun y ↦ a y (g y)) μ := hg.continuous_clm_apply ha
  have h₁ := ((hρc.fderiv_apply (𝕜 := ℝ) v).convolutionExists_left (lsmul ℝ ℝ)
    (hρ.continuous_fderiv_apply_const one_ne_zero v) hag x).integrable
  have h₂ := ((hρc.fderiv_apply (𝕜 := ℝ) v).convolutionExists_left (lsmul ℝ ℝ)
    (hρ.continuous_fderiv_apply_const one_ne_zero v) hg x).integrable
  rw [mollifierCommutator_apply, hρc.fderiv_convolution_left_apply _ hρ hag,
    hρc.fderiv_convolution_left_apply _ hρ hg, convolution_def, convolution_def,
    ← (a x).integral_comp_comm h₂, ← integral_sub h₁ ((a x).integrable_comp h₂)]
  refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
  simp [map_smul, smul_sub]

/-- The commutator is additive in the function it acts on. -/
theorem mollifierCommutator_sub (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ)
    (ha : Continuous a) (hg : LocallyIntegrable g μ) (hh : LocallyIntegrable h μ) (v : E) :
    mollifierCommutator μ ρ a v (g - h) =
      mollifierCommutator μ ρ a v g - mollifierCommutator μ ρ a v h := by
  ext x
  rw [Pi.sub_apply, mollifierCommutator_eq_integral hρc hρ ha (hg.sub hh),
    mollifierCommutator_eq_integral hρc hρ ha hg, mollifierCommutator_eq_integral hρc hρ ha hh,
    ← integral_sub (integrable_sub_apply_smul hρc hρ ha hg v x)
      (integrable_sub_apply_smul hρc hρ ha hh v x)]
  refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
  simp only [Pi.sub_apply, smul_sub, map_sub]

/-- **The `Lᵖ` bound of the commutator.** If `a` is `K`-Lipschitz, then for `1 ≤ p ≤ ∞`,
`‖∂ᵥ (ρ ⋆ (a g)) - a ∂ᵥ (ρ ⋆ g)‖_p ≤ K (∫ ‖t‖ ‖∂ᵥ ρ t‖ dt) ‖g‖_p`. -/
theorem eLpNorm_mollifierCommutator_le {K : ℝ≥0} (hρc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 1 ρ) (ha : LipschitzWith K a) (hg : LocallyIntegrable g μ) (v : E)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (mollifierCommutator μ ρ a v g) p μ ≤
      K * (∫⁻ t, ‖t‖ₑ * ‖fderiv ℝ ρ t v‖ₑ ∂μ) * eLpNorm g p μ := by
  rw [show mollifierCommutator μ ρ a v g = _ from
    funext (mollifierCommutator_eq_integral hρc hρ ha.continuous hg v)]
  exact eLpNorm_integral_sub_apply_smul_le ha
    (hρ.continuous_fderiv_apply_const one_ne_zero v).aestronglyMeasurable
    hg.aestronglyMeasurable hp

omit [μ.IsNegInvariant] [CompleteSpace F] [CompleteSpace F'] in
/-- For a `C¹` compactly supported `h`, the derivatives in the commutator can be moved onto `h`:
`∂ᵥ (ρ ⋆ (a h)) - a ∂ᵥ (ρ ⋆ h) = ρ ⋆ ∂ᵥ (a h) - a (ρ ⋆ ∂ᵥ h)`. -/
theorem mollifierCommutator_eq_sub_of_hasCompactSupport (hρ : LocallyIntegrable ρ μ)
    (ha : ContDiff ℝ 1 a) (hhc : HasCompactSupport h) (hh : ContDiff ℝ 1 h) (v x : E) :
    mollifierCommutator μ ρ a v h x =
      (ρ ⋆[lsmul ℝ ℝ, μ] fun y ↦ fderiv ℝ (fun z ↦ a z (h z)) y v) x -
        a x ((ρ ⋆[lsmul ℝ ℝ, μ] fun y ↦ fderiv ℝ h y v) x) := by
  have hahc : HasCompactSupport fun z ↦ a z (h z) := hhc.mono_of_eq_zero fun z hz ↦ by simp [hz]
  rw [mollifierCommutator_apply, hahc.fderiv_convolution_right_apply _ hρ (ha.clm_apply hh),
    hhc.fderiv_convolution_right_apply _ hρ hh]

omit [μ.IsNegInvariant] in
/-- Friedrichs' lemma for a `C¹` compactly supported function, where it is the product rule in the
limit. -/
private theorem tendsto_eLpNorm_mollifierCommutator_sub_of_hasCompactSupport {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) (ha : ContDiff ℝ 1 a) {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : E)} (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0))
    (hhc : HasCompactSupport h) (hh : ContDiff ℝ 1 h) (v : E) :
    Tendsto (fun i ↦ eLpNorm (mollifierCommutator μ ((φ i).normed μ) a v h -
      fun x ↦ fderiv ℝ a x v (h x)) p μ) l (𝓝 0) := by
  set D : E → F' := fun y ↦ fderiv ℝ (fun z ↦ a z (h z)) y v
  set Dh : E → F := fun y ↦ fderiv ℝ h y v
  have hahc : HasCompactSupport fun z ↦ a z (h z) := hhc.mono_of_eq_zero fun z hz ↦ by simp [hz]
  have hDc : Continuous D :=
    ((ha.clm_apply hh).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDhc : Continuous Dh := (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDs : HasCompactSupport D := hahc.fderiv_apply (𝕜 := ℝ) v
  have hDhs : HasCompactSupport Dh := hhc.fderiv_apply (𝕜 := ℝ) v
  -- The product rule `∂ᵥ (a h) = (∂ᵥ a) h + a ∂ᵥ h`.
  have hD (y : E) : D y = fderiv ℝ a y v (h y) + a y (Dh y) := by
    simp only [D, Dh]
    rw [fderiv_clm_apply ((ha.differentiable one_ne_zero) y) ((hh.differentiable one_ne_zero) y)]
    simp [add_comm]
  -- So the difference is the error of mollifying `∂ᵥ (a h)` minus `a` times that of `∂ᵥ h`.
  have hdec (i : ι) : mollifierCommutator μ ((φ i).normed μ) a v h -
      (fun x ↦ fderiv ℝ a x v (h x)) = ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] D - D) -
        fun x ↦ a x (((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] Dh) x - Dh x) := by
    ext x
    rw [Pi.sub_apply, mollifierCommutator_eq_sub_of_hasCompactSupport
      (φ i).integrable_normed.locallyIntegrable ha hhc hh v x]
    simp only [Pi.sub_apply, map_sub, hD]
    abel
  have h₁ : Tendsto (fun i ↦ eLpNorm ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] D - D) p μ) l (𝓝 0) :=
    tendsto_eLpNorm_normed_convolution_sub hp hφ (hDc.memLp_of_hasCompactSupport hDs)
  have h₂ := tendsto_eLpNorm_apply_normed_convolution_sub (mu := μ) hp ha.continuous hDhs hDhc hφ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [add_zero] using h₁.add h₂) (Eventually.of_forall fun _ ↦ bot_le)
    (Eventually.of_forall fun i ↦ ?_)
  rw [hdec i]
  exact eLpNorm_sub_le Fact.out

/-- **Friedrichs' lemma.** Let `a : E → (F →L[ℝ] F')` be `C¹` and `K`-Lipschitz, let `φ i` be
bumps centred at the origin with a fixed ratio of radii whose outer radii tend to zero, and let
`1 ≤ p < ∞`. Then for every `g ∈ Lᵖ`, the commutators `∂ᵥ (ρᵢ ⋆ (a g)) - a ∂ᵥ (ρᵢ ⋆ g)` with the
normalized bumps `ρᵢ = (φ i).normed μ` converge in `Lᵖ` to `(∂ᵥ a) g`. -/
theorem tendsto_eLpNorm_mollifierCommutator_sub {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {K : ℝ≥0} (ha : ContDiff ℝ 1 a) (haK : LipschitzWith K a) {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : E)} (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) {R : ℝ}
    (hR : ∀ i, (φ i).rOut / (φ i).rIn = R) (hg : MemLp g p μ) (v : E) :
    Tendsto (fun i ↦ eLpNorm (mollifierCommutator μ ((φ i).normed μ) a v g -
      fun x ↦ fderiv ℝ a x v (g x)) p μ) l (𝓝 0) := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact Subsingleton.elim l ⊥ ▸ tendsto_bot
  -- The commutators are uniformly bounded on `Lᵖ`, by `K` times the common first moment `M`.
  set M : ℝ≥0∞ := ∫⁻ t, ‖t‖ₑ * ‖fderiv ℝ ((φ i₀).normed μ) t v‖ₑ ∂μ
  have hM (i : ι) : ∫⁻ t, ‖t‖ₑ * ‖fderiv ℝ ((φ i).normed μ) t v‖ₑ ∂μ = M :=
    (φ i).lintegral_eNorm_mul_eNorm_fderiv_normed_apply_eq (φ i₀) ((hR i).trans (hR i₀).symm) v
  have hMfin : M ≠ ∞ :=
    (φ i₀).hasCompactSupport_normed.lintegral_eNorm_mul_eNorm_fderiv_apply_ne_top
      (φ i₀).contDiff_normed v
  have hg1 : LocallyIntegrable g μ := hg.locallyIntegrable Fact.out
  set B : ℝ≥0∞ := K * M + K * ‖v‖ₑ
  have hB : B ≠ ∞ := by simp [B, ENNReal.mul_ne_top, hMfin]
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  -- Approximate `g` by a smooth compactly supported `h` within `n`, with `n B < ε / 2`.
  obtain ⟨n, hn, hnB⟩ := ENNReal.exists_nnreal_pos_mul_lt hB (ENNReal.half_pos hε.ne').ne'
  obtain ⟨h, hhc, hh, hgh⟩ := hg.exist_eLpNorm_sub_le hp Fact.out (ε := n) (by exact_mod_cast hn)
  rw [ENNReal.ofReal_coe_nnreal] at hgh
  have hhl : LocallyIntegrable h μ := hh.continuous.locallyIntegrable
  filter_upwards [ENNReal.tendsto_nhds_zero.1
    (tendsto_eLpNorm_mollifierCommutator_sub_of_hasCompactSupport (μ := μ) hp ha hφ hhc
      (hh.of_le (by simp)) v) (ε / 2) (ENNReal.half_pos hε.ne')] with i hi
  have hρc := (φ i).hasCompactSupport_normed (μ := μ)
  have hρ := (φ i).contDiff_normed (μ := μ) (n := 1)
  set L : (E → F) → E → F' := fun k x ↦ fderiv ℝ a x v (k x)
  have hL : eLpNorm (L (g - h)) p μ ≤ K * ‖v‖ₑ * eLpNorm (g - h) p μ :=
    haK.eLpNorm_fderiv_apply_apply_le ha
      (hg.aestronglyMeasurable.sub hh.continuous.aestronglyMeasurable) v p
  -- Split `g = (g - h) + h`.
  have hdec : mollifierCommutator μ ((φ i).normed μ) a v g - L g =
      (mollifierCommutator μ ((φ i).normed μ) a v (g - h) +
        (mollifierCommutator μ ((φ i).normed μ) a v h - L h)) - L (g - h) := by
    rw [mollifierCommutator_sub hρc hρ ha.continuous hg1 hhl]
    ext x
    simp only [L, Pi.sub_apply, Pi.add_apply, map_sub]
    abel
  calc eLpNorm (mollifierCommutator μ ((φ i).normed μ) a v g - L g) p μ
      ≤ eLpNorm (mollifierCommutator μ ((φ i).normed μ) a v (g - h)) p μ +
          eLpNorm (mollifierCommutator μ ((φ i).normed μ) a v h - L h) p μ +
          eLpNorm (L (g - h)) p μ := by
        rw [hdec]
        exact (eLpNorm_sub_le Fact.out).trans (by gcongr; exact eLpNorm_add_le Fact.out)
    _ ≤ K * M * n + ε / 2 + K * ‖v‖ₑ * n := by
        gcongr
        · exact (eLpNorm_mollifierCommutator_le hρc hρ haK (hg1.sub hhl) v Fact.out).trans
            (by rw [hM i]; gcongr)
        · exact hL.trans (by gcongr)
    _ = n * B + ε / 2 := by ring
    _ ≤ ε / 2 + ε / 2 := by gcongr
    _ = ε := ENNReal.add_halves ε

omit [CompleteSpace F] [CompleteSpace F'] in
/-- The weak equation `∑ⱼ aⱼ ∂_{wⱼ} g = f`, tested against `y ↦ ρ (x - y)`: the mollification
satisfies `∑ⱼ aⱼ ∂_{wⱼ} (ρ ⋆ g) = ρ ⋆ f + ∑ⱼ (ρ ⋆ (∂_{wⱼ} aⱼ) g - C_ρ g)` at `x`, where `C_ρ` is
the commutator for `aⱼ` and `wⱼ`. -/
private theorem sum_apply_fderiv_convolution_eq {ρ : E → ℝ} (hρc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) {ι' : Type*} (s : Finset ι') {a : ι' → E → F →L[ℝ] F'}
    (ha : ∀ j ∈ s, ContDiff ℝ 1 (a j)) (w : ι' → E) {f : E → F'} (hg : LocallyIntegrable g μ)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      -∑ j ∈ s, ∫ y, (fderiv ℝ ψ y (w j) • a j y (g y) +
        ψ y • fderiv ℝ (a j) y (w j) (g y)) ∂μ = ∫ y, ψ y • f y ∂μ) (x : E) :
    ∑ j ∈ s, a j x (fderiv ℝ (ρ ⋆[lsmul ℝ ℝ, μ] g) x (w j)) =
      (ρ ⋆[lsmul ℝ ℝ, μ] f) x + ∑ j ∈ s, ((ρ ⋆[lsmul ℝ ℝ, μ] fun y ↦
        fderiv ℝ (a j) y (w j) (g y)) x - mollifierCommutator μ ρ (a j) (w j) g x) := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by exact_mod_cast le_top)
  have hint {k : E → ℝ} {u : E → F'} (hkc : HasCompactSupport k) (hk : Continuous k)
      (hu : LocallyIntegrable u μ) : Integrable (fun y ↦ k (x - y) • u y) μ := by
    simpa using ((hkc.convolutionExists_left (lsmul ℝ ℝ) hk hu x).integrable).comp_sub_left x
  have hagj (j : ι') (hj : j ∈ s) : LocallyIntegrable (fun y ↦ a j y (g y)) μ :=
    hg.continuous_clm_apply (ha j hj).continuous
  have hGj (j : ι') (hj : j ∈ s) :
      LocallyIntegrable (fun y ↦ fderiv ℝ (a j) y (w j) (g y)) μ :=
    hg.continuous_clm_apply (((ha j hj).continuous_fderiv one_ne_zero).clm_apply continuous_const)
  -- The derivative of the test function is `-∂ρ (x - ·)`.
  have hdψ (y u : E) : fderiv ℝ (fun y ↦ ρ (x - y)) y u = -fderiv ℝ ρ (x - y) u := by
    have hd : HasFDerivAt (fun y ↦ ρ (x - y))
        ((fderiv ℝ ρ (x - y)).comp (0 - ContinuousLinearMap.id ℝ E)) y :=
      ((hρ1.differentiable one_ne_zero) _).hasFDerivAt.comp y
        ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    rw [hd.fderiv]
    simp
  have hw := hweak (fun y ↦ ρ (x - y)) (hρ.comp (contDiff_const.sub contDiff_id))
    (hρc.comp_homeomorph (Homeomorph.subLeft x))
  simp_rw [hdψ, neg_smul] at hw
  rw [Finset.sum_congr rfl fun j hj ↦ integral_add
    (f := fun y ↦ -(fderiv ℝ ρ (x - y) (w j) • a j y (g y)))
    (g := fun y ↦ ρ (x - y) • fderiv ℝ (a j) y (w j) (g y))
    (hint (hρc.fderiv_apply (𝕜 := ℝ) (w j))
      (hρ1.continuous_fderiv_apply_const one_ne_zero (w j)) (hagj j hj)).neg
      (hint hρc hρ1.continuous (hGj j hj))] at hw
  -- So `∑ⱼ ∂_{wⱼ} (ρ ⋆ aⱼ g) = ρ ⋆ f + ∑ⱼ ρ ⋆ (∂_{wⱼ} aⱼ) g` at `x`.
  have h3 : ∑ j ∈ s, fderiv ℝ (ρ ⋆[lsmul ℝ ℝ, μ] fun y ↦ a j y (g y)) x (w j) =
      (ρ ⋆[lsmul ℝ ℝ, μ] f) x + ∑ j ∈ s, (ρ ⋆[lsmul ℝ ℝ, μ] fun y ↦
        fderiv ℝ (a j) y (w j) (g y)) x := by
    rw [Finset.sum_congr rfl fun j hj ↦ by
      rw [hρc.fderiv_convolution_left_apply _ hρ1 (hagj j hj), convolution_lsmul_swap],
      convolution_lsmul_swap, Finset.sum_congr rfl fun j _ ↦ convolution_lsmul_swap, ← hw]
    simp only [integral_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, neg_add, neg_neg]
    abel
  simp only [mollifierCommutator_apply, Finset.sum_sub_distrib, h3]
  abel

/-- **Weak solutions of first-order systems are strong** (Friedrichs). Let `aⱼ`, for `j ∈ s`, be
`C¹` and Lipschitz operator fields, `wⱼ` directions, and `g, f ∈ Lᵖ` with `1 ≤ p < ∞`. Suppose
that `∑ⱼ aⱼ ∂_{wⱼ} g = f` in the sense of distributions: for every smooth compactly supported
`ψ`,
`-∑ⱼ ∫ (∂_{wⱼ} ψ • aⱼ g + ψ • (∂_{wⱼ} aⱼ) g) = ∫ ψ • f`.
Then the mollifications `ρᵢ ⋆ g` by normalized bumps `ρᵢ = (φ i).normed μ` with a fixed ratio of
radii and outer radii tending to zero, which converge to `g` in `Lᵖ`, satisfy
`∑ⱼ aⱼ ∂_{wⱼ} (ρᵢ ⋆ g) → f` in `Lᵖ`. -/
theorem tendsto_eLpNorm_sum_apply_fderiv_convolution_sub {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) {ι' : Type*} (s : Finset ι') {a : ι' → E → F →L[ℝ] F'} {K : ι' → ℝ≥0}
    (ha : ∀ j ∈ s, ContDiff ℝ 1 (a j)) (haK : ∀ j ∈ s, LipschitzWith (K j) (a j)) (w : ι' → E)
    {f : E → F'} (hg : MemLp g p μ) (hf : MemLp f p μ)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      -∑ j ∈ s, ∫ y, (fderiv ℝ ψ y (w j) • a j y (g y) +
        ψ y • fderiv ℝ (a j) y (w j) (g y)) ∂μ = ∫ y, ψ y • f y ∂μ)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) {R : ℝ} (hR : ∀ i, (φ i).rOut / (φ i).rIn = R) :
    Tendsto (fun i ↦ eLpNorm ((fun x ↦ ∑ j ∈ s,
      a j x (fderiv ℝ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] g) x (w j))) - f) p μ) l (𝓝 0) := by
  have hg1 : LocallyIntegrable g μ := hg.locallyIntegrable Fact.out
  -- The terms `Gⱼ = (∂_{wⱼ} aⱼ) g` are in `Lᵖ`, since `∂_{wⱼ} aⱼ` is continuous and bounded.
  set G : ι' → E → F' := fun j y ↦ fderiv ℝ (a j) y (w j) (g y)
  have hG (j : ι') (hj : j ∈ s) : MemLp (G j) p μ := memLp_iff.2 <|
    ((haK j hj).eLpNorm_fderiv_apply_apply_le (ha j hj) hg.aestronglyMeasurable (w j) p).trans_lt
      (ENNReal.mul_lt_top (by finiteness) (memLp_iff.1 hg))
  -- The weak equation, tested against `y ↦ ρ (x - y)`, identifies `∑ⱼ aⱼ ∂_{wⱼ} (ρ ⋆ g)` with
  -- `ρ ⋆ f + ∑ⱼ (ρ ⋆ Gⱼ - C_ρ g)`, where `C_ρ` is the commutator for `aⱼ` and `wⱼ`.
  have hid (i : ι) (x : E) := sum_apply_fderiv_convolution_eq
    ((φ i).hasCompactSupport_normed (μ := μ)) (φ i).contDiff_normed s ha w hg1 hweak x
  -- Hence `∑ⱼ aⱼ ∂_{wⱼ} (ρ ⋆ g) - f` is a sum of mollification errors and commutator errors.
  have hdec (i : ι) : (fun x ↦ ∑ j ∈ s,
      a j x (fderiv ℝ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] g) x (w j))) - f =
      ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f - f) + ∑ j ∈ s,
        (((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] G j - G j) -
          (mollifierCommutator μ ((φ i).normed μ) (a j) (w j) g - G j)) := by
    ext x
    simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply, hid i x, sub_sub_sub_cancel_right]
    abel
  have hlim : Tendsto (fun i ↦ eLpNorm ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f - f) p μ +
      ∑ j ∈ s, (eLpNorm ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] G j - G j) p μ +
        eLpNorm (mollifierCommutator μ ((φ i).normed μ) (a j) (w j) g - G j) p μ)) l (𝓝 0) := by
    have := (tendsto_eLpNorm_normed_convolution_sub hp hφ hf).add (tendsto_finsetSum s fun j hj ↦
      (tendsto_eLpNorm_normed_convolution_sub hp hφ (hG j hj)).add
        (tendsto_eLpNorm_mollifierCommutator_sub hp (ha j hj) (haK j hj) hφ hR hg (w j)))
    simpa only [add_zero, Finset.sum_const_zero] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ bot_le) (Eventually.of_forall fun i ↦ ?_)
  rw [hdec i]
  refine (eLpNorm_add_le Fact.out).trans ?_
  gcongr
  exact (eLpNorm_sum_le Fact.out).trans (Finset.sum_le_sum fun j _ ↦ eLpNorm_sub_le Fact.out)

end Commutator

end TauCeti
