/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.LogVariation
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import TauCeti.Analysis.PDE.Schrodinger.Stationary
import TauCeti.Analysis.PDE.Vortex.ExteriorEstimate

/-!
# Kernel elements of the vortex operator with prescribed poles

A field `x = (b₁, b₂, p, q)` represents `a = i (b₁ ds + b₂ dt)` and `α = 2 (p + i q)`. At a field
whose holomorphicity rows `∂bar_a α = 0` hold, a variation `y` in the kernel of the gauge-fixed
operator `L_x = d₀* ⊕ d₁` is, off the zeros of `α`, the logarithmic variation of
`η = δα / α`, and `η` solves the Schrödinger equation `Δη = P η`, `P = |α|² / 4`
(`TauCeti.Vortex.laplacian_div_sectionValue_eq_smul`). The function `η` may have poles at the
zeros of `α`, of order less than the multiplicity of the zero: the covariant translations of
`TauCeti.Analysis.PDE.Vortex.TranslationKernel` have simple poles. Conversely a square-integrable
kernel element is determined by the singular part of `η`
(`TauCeti.Vortex.eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto`).

This file constructs square-integrable kernel elements with every admissible pole. Let `x` be
smooth with `∂bar_a α = 0` and `|α| → 1` at infinity, let `z` be a zero of `α` of multiplicity
`n`, and let `j < n`. For every `c ∈ ℂ` there is a smooth kernel element `y ∈ L²` of `L_x` with

`δα = α (c / (w - z)^(j+1) + ξ)`  off `z`,

for a smooth function `ξ` on the whole plane
(`TauCeti.Vortex.exists_gaugeFixedOperator_eq_zero_sectionValue_eq_mul_div_pow_add`). So `δα / α`
has principal part `c / (w - z)^(j+1)` at `z` and no singularity elsewhere. The local factorization
`α = (w - z)ⁿ v` with `v` smooth and nonzero at `z` is supplied for every zero of a nontrivial
smooth vortex section by `TauCeti.Vortex.exists_contDiffAt_sectionValue_eq_pow_mul`. As `c` ranges
over `ℂ` and `(z, j)` over the zeros with `j` below the multiplicity, these principal parts span a
real space of dimension `2m` for a vortex of degree `m`, the dimension of the tangent space of the
divisor space `Sym^m ℂ`: every one of them is realized by a square-integrable kernel element.

The construction cuts the pole off: `η₀ = χ c / (w - z)^(j+1)`, with `χ` a bump equal to one near
`z`, has smooth logarithmic variation `y₀`, because `α` vanishes to order `j + 1` at `z` and
`c / (w - z)^(j+1)` is holomorphic, and `L_x y₀` is smooth with compact support and vanishing
`∂bar` rows. Its two remaining rows are the source of the Schrödinger equation
`Δξ = P ξ + g` for the correction `ξ`, which has a solution in `L²` with `L²` derivative because
`P ≥ 0` is bounded and positive near infinity (`TauCeti.exists_contDiff_laplacian_eq_mul_add`).
Then `y = y₀ + logVariation x ξ`.

## References

* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Metric Set
open scoped Laplacian Topology ContDiff ZeroAtInfty

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- If `α = (w - z)ⁿ v` near `z` with `v` smooth at `z` and `j < n`, then `α = (w - z)^(j+1) q`
on the whole plane for a smooth function `q`. -/
private theorem exists_contDiff_sectionValue_eq_pow_succ_mul (hx : ContDiff ℝ ∞ x) {z : ℂ}
    {n j : ℕ} {v : ℂ → ℂ} (hv : ContDiffAt ℝ ∞ v z)
    (hfac : ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ n * v w) (hj : j < n) :
    ∃ q : ℂ → ℂ, ContDiff ℝ ∞ q ∧ ∀ w, sectionValue x w = (w - z) ^ (j + 1) * q w := by
  classical
  have hα : ContDiff ℝ ∞ (sectionValue x) :=
    contDiff_sectionValue (contDiff_euclidean.1 hx 2) (contDiff_euclidean.1 hx 3)
  have hlin : ContDiff ℝ ∞ fun w : ℂ ↦ w - z := contDiff_id.sub contDiff_const
  set q : ℂ → ℂ := fun w ↦
    if w = z then (w - z) ^ (n - (j + 1)) * v w else sectionValue x w / (w - z) ^ (j + 1)
  have hpow (w : ℂ) : (w - z) ^ n = (w - z) ^ (n - (j + 1)) * (w - z) ^ (j + 1) := by
    rw [← pow_add, Nat.sub_add_cancel hj]
  have hloc : q =ᶠ[𝓝 z] fun w ↦ (w - z) ^ (n - (j + 1)) * v w := by
    filter_upwards [hfac] with w hw
    by_cases hwz : w = z
    · simp [q, hwz]
    · have hne : (w - z) ^ (j + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hwz)
      simp only [q, hwz, ite_false, hw, hpow]
      field_simp
  refine ⟨q, contDiff_iff_contDiffAt.2 fun w ↦ ?_, fun w ↦ ?_⟩
  · by_cases hwz : w = z
    · subst hwz
      exact ((hlin.pow (n - (j + 1))).contDiffAt.mul hv).congr_of_eventuallyEq hloc
    · refine (hα.contDiffAt.mul ((hlin.pow (j + 1)).contDiffAt.inv
        (pow_ne_zero _ (sub_ne_zero.2 hwz)))).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ne.mem_nhds hwz] with w' hw'
      simp [q, hw', div_eq_mul_inv]
  · by_cases hwz : w = z
    · subst hwz
      rw [hfac.self_of_nhds, sub_self, zero_pow (by omega), zero_pow (by omega), zero_mul,
        zero_mul]
    · have hne : (w - z) ^ (j + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hwz)
      simp only [q, hwz, ite_false]
      field_simp

/-- The logarithmic variation of `u + i v` is square integrable when `u`, `v` and their
derivatives are, along a field whose section components are bounded. -/
private theorem memLp_logVariation (hx : Continuous x) {B : ℝ}
    (hB : ∀ w, |x w 2| ≤ B ∧ |x w 3| ≤ B) {u v : ℂ → ℝ} (hu : MemLp u 2 volume)
    (hv : MemLp v 2 volume) (hdu : MemLp (fderiv ℝ u) 2 volume)
    (hdv : MemLp (fderiv ℝ v) 2 volume) :
    MemLp (logVariation x fun w ↦ (u w : ℂ) + v w * I) 2 volume := by
  have hre : (fun w ↦ ((u w : ℂ) + v w * I).re) = u := by funext w; simp
  have him : (fun w ↦ ((u w : ℂ) + v w * I).im) = v := by funext w; simp
  have happ {f : ℂ → ℝ} (hf : MemLp (fderiv ℝ f) 2 volume) (a : ℂ) :
      MemLp (fun w ↦ fderiv ℝ f w a) 2 volume :=
    (ContinuousLinearMap.apply ℝ ℝ a).comp_memLp' hf
  have hxi (i : Fin 4) : Continuous fun w ↦ x w i := by fun_prop
  have hmul {f : ℂ → ℝ} (hf : MemLp f 2 volume) (i : Fin 4) (hi : ∀ w, |x w i| ≤ B) :
      MemLp (fun w ↦ x w i * f w) 2 volume :=
    hf.of_le_mul (c := B) ((hxi i).aestronglyMeasurable.mul hf.aestronglyMeasurable)
      (ae_of_all _ fun w ↦ by rw [norm_mul, Real.norm_eq_abs]; gcongr; exact hi w)
  have h₀ : MemLp (fun w ↦ logVariation x (fun w ↦ (u w : ℂ) + v w * I) w 0) 2 volume := by
    simp only [logVariation_apply_zero, hre, him]
    exact (happ hdv 1).neg.sub (happ hdu I)
  have h₁ : MemLp (fun w ↦ logVariation x (fun w ↦ (u w : ℂ) + v w * I) w 1) 2 volume := by
    simp only [logVariation_apply_one, hre, him]
    exact (happ hdu 1).sub (happ hdv I)
  have h₂ : MemLp (fun w ↦ logVariation x (fun w ↦ (u w : ℂ) + v w * I) w 2) 2 volume := by
    exact ((hmul hu 2 fun w ↦ (hB w).1).sub (hmul hv 3 fun w ↦ (hB w).2)).ae_eq
      (ae_of_all _ fun w ↦ by simp)
  have h₃ : MemLp (fun w ↦ logVariation x (fun w ↦ (u w : ℂ) + v w * I) w 3) 2 volume := by
    exact ((hmul hv 2 fun w ↦ (hB w).1).add (hmul hu 3 fun w ↦ (hB w).2)).ae_eq
      (ae_of_all _ fun w ↦ by simp)
  refine memLp_piLp_iff.2 fun i ↦ ?_
  fin_cases i
  exacts [h₀, h₁, h₂, h₃]

/-- **The cut-off pole.** Let `α = (w - z)^(j+1) q` with `q` smooth. There is a smooth compactly
supported variation `y₀` which, near every `w ≠ z`, is the logarithmic variation of
`c / (w - z)^(j+1) + ζ`, for a smooth function `ζ` on the plane. -/
private theorem exists_cutoffPole (hx : ContDiff ℝ ∞ x) {z : ℂ} {j : ℕ} {q : ℂ → ℂ}
    (hq : ContDiff ℝ ∞ q) (hαq : ∀ w, sectionValue x w = (w - z) ^ (j + 1) * q w) (c : ℂ) :
    ∃ (y₀ : ℂ → EuclideanSpace ℝ (Fin 4)) (ζ : ℂ → ℂ), ContDiff ℝ ∞ y₀ ∧ HasCompactSupport y₀ ∧
      ContDiff ℝ ∞ ζ ∧ ∀ w, w ≠ z →
        y₀ =ᶠ[𝓝 w] logVariation x (fun w ↦ c / (w - z) ^ (j + 1) + ζ w) := by
  -- A cutoff `χ` equal to one on `closedBall z 1` and vanishing outside `ball z 2`.
  let b : ContDiffBump z := ⟨1, 2, one_pos, one_lt_two⟩
  set χ : ℂ → ℂ := fun w ↦ (b w : ℂ)
  have hχ : ContDiff ℝ ∞ χ := ofRealCLM.contDiff.comp b.contDiff
  have hχ₁ : ∀ w ∈ ball z 1, χ w = 1 := fun w hw ↦ by
    simp [χ, b.one_of_mem_closedBall (ball_subset_closedBall hw)]
  have hχ₀ : ∀ w ∉ ball z 2, χ w = 0 := fun w hw ↦ by
    simp [χ, b.zero_of_le_dist (not_lt.1 hw)]
  -- The pole `pp = c / (w - z)^(j+1)` and its cut-off version `η₀ = χ pp = pp + ζ`.
  set pp : ℂ → ℂ := fun w ↦ c / (w - z) ^ (j + 1)
  have hppC (w : ℂ) (hw : w ≠ z) : DifferentiableAt ℂ pp w :=
    (differentiableAt_const c).div ((differentiableAt_id.sub_const z).pow (j + 1))
      (pow_ne_zero _ (sub_ne_zero.2 hw))
  have hlin : ContDiff ℝ ∞ fun w : ℂ ↦ w - z := contDiff_id.sub contDiff_const
  have hpp (w : ℂ) (hw : w ≠ z) : ContDiffAt ℝ ∞ pp w :=
    ((contDiffAt_const (c := c)).mul ((hlin.pow (j + 1)).contDiffAt.inv
      (pow_ne_zero _ (sub_ne_zero.2 hw)))).congr_of_eventuallyEq
      (Eventually.of_forall fun w' ↦ by simp [pp, div_eq_mul_inv])
  set ζ : ℂ → ℂ := fun w ↦ (χ w - 1) * pp w
  set η₀ : ℂ → ℂ := fun w ↦ pp w + ζ w
  have hη₀ (w : ℂ) (hw : w ≠ z) : ContDiffAt ℝ ∞ η₀ w :=
    (hpp w hw).add ((hχ.contDiffAt.sub contDiffAt_const).mul (hpp w hw))
  have hη₀pp (w : ℂ) (hw : w ∈ ball z 1) : η₀ =ᶠ[𝓝 w] pp := by
    filter_upwards [isOpen_ball.mem_nhds hw] with w' hw'
    simp [η₀, ζ, hχ₁ w' hw']
  -- The logarithmic variation of `η₀`, completed at `z` by the smooth field `g₀` with `δα = c q`.
  set g₀ : ℂ → EuclideanSpace ℝ (Fin 4) := fun w ↦
    !₂[0, 0, (c * q w / 2).re, (c * q w / 2).im]
  have hg₀ : ContDiff ℝ ∞ g₀ := by
    have hcq : ContDiff ℝ ∞ fun w ↦ c * q w / 2 := (contDiff_const.mul hq).div_const 2
    refine contDiff_euclidean.2 fun i ↦ ?_
    fin_cases i
    exacts [contDiff_const, contDiff_const, reCLM.contDiff.comp hcq, imCLM.contDiff.comp hcq]
  have hsection_g₀ (w : ℂ) : sectionValue g₀ w = c * q w := by
    rw [sectionValue_apply]
    simp only [g₀]
    apply Complex.ext <;> simp <;> ring
  set y₀ := Function.update (logVariation x η₀) z (g₀ z)
  have hy₀_off (w : ℂ) (hw : w ≠ z) : y₀ =ᶠ[𝓝 w] logVariation x η₀ := by
    filter_upwards [isOpen_ne.mem_nhds hw] with w' hw'
    exact Function.update_of_ne hw' _ _
  -- Near `z`, the logarithmic variation of the holomorphic pole has no connection part.
  have hy₀_near : y₀ =ᶠ[𝓝 z] g₀ := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos)] with w hw
    by_cases hwz : w = z
    · subst hwz
      exact Function.update_self _ _ _
    rw [(hy₀_off w hwz).eq_of_nhds, logVariation_congr_nhds x (hη₀pp w hw)]
    have hcon := logVariation_zero_add_one_mul_I x ((hppC w hwz).restrictScalars ℝ)
    rw [(hppC w hwz).conjWirtingerDeriv_eq_zero, _root_.zero_apply, mul_zero] at hcon
    have h₀ := congrArg re hcon
    have h₁ := congrArg im hcon
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
      zero_re, add_im, mul_im, zero_add, zero_im] at h₀ h₁
    refine apply_eq_of_sectionValue_eq ?_ ?_ ?_
    · simpa [g₀] using h₀
    · simpa [g₀] using h₁
    · have hne : (w - z) ^ (j + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hwz)
      rw [sectionValue_logVariation, hsection_g₀, hαq]
      simp only [pp]
      field_simp
  have hy₀_zero (w : ℂ) (hw : w ∉ closedBall z 2) : y₀ w = 0 := by
    have hwz : w ≠ z := fun h ↦ hw (h ▸ mem_closedBall_self zero_le_two)
    have hη₀0 : η₀ =ᶠ[𝓝 w] 0 := by
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hw] with w' hw'
      simp [η₀, ζ, hχ₀ w' fun h ↦ hw' (ball_subset_closedBall h)]
    rw [(hy₀_off w hwz).eq_of_nhds, logVariation_congr_nhds x hη₀0, logVariation_zero,
      Pi.zero_apply]
  refine ⟨y₀, ζ, contDiff_iff_contDiffAt.2 fun w ↦ ?_,
    HasCompactSupport.intro (isCompact_closedBall z 2) hy₀_zero,
    contDiff_iff_contDiffAt.2 fun w ↦ ?_, hy₀_off⟩
  · by_cases hwz : w = z
    · subst hwz
      exact hg₀.contDiffAt.congr_of_eventuallyEq hy₀_near
    · exact (contDiffAt_logVariation hx.contDiffAt (by simpa using hη₀ w hwz)).congr_of_eventuallyEq
        (hy₀_off w hwz)
  · by_cases hwz : w = z
    · subst hwz
      refine contDiffAt_const (c := 0).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos)] with w hw
      simp [ζ, hχ₁ w hw]
    · exact (hχ.contDiffAt.sub contDiffAt_const).mul (hpp w hwz)

/-- The `∂bar` rows of `L_x y` vanish everywhere when `x` satisfies the holomorphicity rows and
`y` is a `C¹` variation which, near every point other than `z`, is a logarithmic variation. -/
private theorem gaugeFixedOperator_apply_eq_zero_of_eventuallyEq_logVariation
    (hx : Differentiable ℝ x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : ContDiff ℝ 1 y) {z : ℂ} {η : ℂ → ℂ}
    (hη : ∀ w, w ≠ z → DifferentiableAt ℝ η w) (hyη : ∀ w, w ≠ z → y =ᶠ[𝓝 w] logVariation x η)
    (i : Fin 4) (hi : i = 2 ∨ i = 3) (w : ℂ) : gaugeFixedOperator x y w i = 0 := by
  have hoff (w' : ℂ) (hw' : w' ≠ z) : gaugeFixedOperator x y w' i = 0 := by
    rw [gaugeFixedOperator_congr_nhds x (hyη w' hw')]
    obtain ⟨h₂, h₃⟩ := gaugeFixedOperator_logVariation_two_three (hx w') (hη w' hw')
    rcases hi with rfl | rfl
    · simp [h₂, (hhol w').1, (hhol w').2]
    · simp [h₃, (hhol w').1, (hhol w').2]
  have hcont : Continuous fun w ↦ gaugeFixedOperator x y w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
      (continuous_gaugeFixedOperator hx.continuous hy)
  exact congrFun (Continuous.ext_on (dense_compl_singleton z) hcont
    (continuous_const (y := (0 : ℝ))) fun w' hw' ↦ hoff w' hw') w

/-- A continuous potential `P = p² + q²` with `4 P → 1` at infinity is bounded. -/
private theorem exists_forall_le_of_tendsto
    (hP : Continuous fun w ↦ x w 2 ^ 2 + x w 3 ^ 2)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ C, ∀ w, x w 2 ^ 2 + x w 3 ^ 2 ≤ C := by
  have ht : Tendsto (fun w ↦ x w 2 ^ 2 + x w 3 ^ 2 - 1 / 4) (cocompact ℂ) (𝓝 0) := by
    have h := (hlim.const_mul (1 / 4 : ℝ)).sub_const (1 / 4)
    norm_num at h
    simpa [← mul_assoc] using h
  obtain ⟨C, hC⟩ := (⟨⟨_, hP.sub continuous_const⟩, ht⟩ : C₀(ℂ, ℝ)).isBounded_range.exists_norm_le
  refine ⟨C + 1 / 4, fun w ↦ ?_⟩
  have h := hC _ (mem_range_self w)
  simp only [ZeroAtInftyContinuousMap.coe_mk, Real.norm_eq_abs, Pi.sub_apply] at h
  linarith [le_abs_self (x w 2 ^ 2 + x w 3 ^ 2 - 1 / 4)]

/-- **Kernel elements with a prescribed pole.** Let `x` be a smooth field with `∂bar_a α = 0` and
`|α| → 1` at infinity, and let `α = (w - z)ⁿ v` near `z` with `v` smooth at `z`. For `j < n` and
every `c ∈ ℂ` there is a smooth square-integrable `y` with `L_x y = 0` whose section variation
is `δα = α (c / (w - z)^(j+1) + ξ)` off `z`, for a smooth function `ξ` on the plane. Thus
`δα / α` has principal part `c / (w - z)^(j+1)` at `z` and is smooth away from `z`. -/
theorem exists_gaugeFixedOperator_eq_zero_sectionValue_eq_mul_div_pow_add (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {z : ℂ} {n j : ℕ}
    {v : ℂ → ℂ} (hv : ContDiffAt ℝ ∞ v z)
    (hfac : ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ n * v w) (hj : j < n) (c : ℂ) :
    ∃ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ y ∧ MemLp y 2 volume ∧
      (∀ w, gaugeFixedOperator x y w = 0) ∧
      ∃ ξ : ℂ → ℂ, ContDiff ℝ ∞ ξ ∧
        ∀ w, w ≠ z → sectionValue y w = sectionValue x w * (c / (w - z) ^ (j + 1) + ξ w) := by
  obtain ⟨q, hq, hαq⟩ := exists_contDiff_sectionValue_eq_pow_succ_mul hx hv hfac hj
  obtain ⟨y₀, ζ, hy₀, hy₀c, hζ, hy₀η⟩ := exists_cutoffPole hx hq hαq c
  set η₀ : ℂ → ℂ := fun w ↦ c / (w - z) ^ (j + 1) + ζ w
  have hη₀ (w : ℂ) (hw : w ≠ z) : DifferentiableAt ℝ η₀ w :=
    (((differentiableAt_const c).div ((differentiableAt_id.sub_const z).pow (j + 1))
      (pow_ne_zero _ (sub_ne_zero.2 hw))).restrictScalars ℝ).add (hζ.differentiable (by simp) w)
  -- `L_x y₀` is smooth with compact support, and its `∂bar` rows vanish.
  set G := gaugeFixedOperator x y₀
  have hG : ContDiff ℝ ∞ G := contDiff_gaugeFixedOperator hx (by simpa using hy₀)
  have hGc : HasCompactSupport G := by
    refine HasCompactSupport.intro hy₀c.isCompact fun w hw ↦ ?_
    have h0 : y₀ =ᶠ[𝓝 w] 0 := by
      filter_upwards [(isClosed_tsupport y₀).isOpen_compl.mem_nhds hw] with w' hw'
      exact image_eq_zero_of_notMem_tsupport hw'
    simp only [G, gaugeFixedOperator_congr_nhds x h0, gaugeFixedOperator_zero, Pi.zero_apply]
  have hGrow := gaugeFixedOperator_apply_eq_zero_of_eventuallyEq_logVariation
    (hx.differentiable (by simp)) hhol (hy₀.of_le (by simp)) hη₀ hy₀η
  -- The potential `P = |α|² / 4` is smooth, nonnegative, bounded, and at least `1 / 8` far out.
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := contDiff_euclidean.1 hx i
  set P : ℂ → ℝ := fun w ↦ x w 2 ^ 2 + x w 3 ^ 2
  have hP : ContDiff ℝ ∞ P := ((hxi 2).pow 2).add ((hxi 3).pow 2)
  have hP₀ (w : ℂ) : 0 ≤ P w := by positivity
  obtain ⟨R, -, hR⟩ := exists_exterior_lt_mass hlim (by norm_num : (1 : ℝ) / 8 < 1 / 4)
  obtain ⟨C, hPC⟩ := exists_forall_le_of_tendsto hP.continuous hlim
  -- The correction `ξ = ξr + i ξi` solving `Δξ = P ξ + (G₁ + i G₀)`.
  have hsrc (i : Fin 4) : MemLp (fun w ↦ G w i) 2 volume :=
    (contDiff_euclidean.1 hG i).continuous.memLp_of_hasCompactSupport
      (hGc.comp_left (g := fun v : EuclideanSpace ℝ (Fin 4) ↦ v i) (by simp))
  obtain ⟨ξr, hξr, hξr2, hdξr, -, hΔr⟩ := exists_contDiff_laplacian_eq_mul_add (k := ⊤) le_top
    (by simpa using hP) hP₀ hPC (by norm_num : (0 : ℝ) < 1 / 8)
    (fun w hw ↦ (hR w hw).le) (by simpa using contDiff_euclidean.1 hG 1) (hsrc 1)
  obtain ⟨ξi, hξi, hξi2, hdξi, -, hΔi⟩ := exists_contDiff_laplacian_eq_mul_add (k := ⊤) le_top
    (by simpa using hP) hP₀ hPC (by norm_num : (0 : ℝ) < 1 / 8)
    (fun w hw ↦ (hR w hw).le) (by simpa using contDiff_euclidean.1 hG 0) (hsrc 0)
  set ξ : ℂ → ℂ := fun w ↦ (ξr w : ℂ) + ξi w * I
  have hξ : ContDiff ℝ ∞ ξ := (ofRealCLM.contDiff.comp (hξr.of_le le_self_add)).add
    ((ofRealCLM.contDiff.comp (hξi.of_le le_self_add)).mul contDiff_const)
  have hΔre (w : ℂ) : (Δ ξ w).re = Δ ξr w := by
    rw [show ξr = ⇑reCLM ∘ ξ by funext w; simp [ξ],
      ((hξ.of_le (by simp)).contDiffAt (x := w)).laplacian_CLM_comp_left (l := reCLM)]
    rfl
  have hΔim (w : ℂ) : (Δ ξ w).im = Δ ξi w := by
    rw [show ξi = ⇑imCLM ∘ ξ by funext w; simp [ξ],
      ((hξ.of_le (by simp)).contDiffAt (x := w)).laplacian_CLM_comp_left (l := imCLM)]
    rfl
  -- The kernel element `y = y₀ + logVariation x ξ`.
  have hB (w : ℂ) : |x w 2| ≤ √C ∧ |x w 3| ≤ √C := by
    have := hPC w
    exact ⟨Real.abs_le_sqrt (by nlinarith [sq_nonneg (x w 3)]),
      Real.abs_le_sqrt (by nlinarith [sq_nonneg (x w 2)])⟩
  refine ⟨y₀ + logVariation x ξ, hy₀.add (contDiff_logVariation hx (by simpa using hξ)),
    (hy₀.continuous.memLp_of_hasCompactSupport hy₀c).add
      (memLp_logVariation hx.continuous hB hξr2 hξi2 hdξr hdξi), fun w ↦ ?_,
    fun w ↦ ζ w + ξ w, hζ.add hξ, fun w hw ↦ ?_⟩
  · rw [gaugeFixedOperator_add x (hy₀.differentiable (by simp) w)
      ((contDiff_logVariation hx (by simpa using hξ)).differentiable (by simp) w),
      gaugeFixedOperator_logVariation (hx.differentiable (by simp) w) (hξ.contDiffAt.of_le
        (by simp)), (hhol w).1, (hhol w).2, hΔre, hΔim, hΔr, hΔi]
    ext i
    fin_cases i
    · simp [ξ, P, G]
    · simp [ξ, P, G]
    · simpa [G] using hGrow 2 (by simp) w
    · simpa [G] using hGrow 3 (by simp) w
  · have hadd : sectionValue (y₀ + logVariation x ξ) w =
        sectionValue y₀ w + sectionValue (logVariation x ξ) w := by
      simp only [sectionValue_apply, Pi.add_apply, PiLp.add_apply, ofReal_add]
      ring
    rw [hadd, sectionValue_apply, (hy₀η w hw).eq_of_nhds, ← sectionValue_apply,
      sectionValue_logVariation, sectionValue_logVariation]
    ring

end TauCeti.Vortex
