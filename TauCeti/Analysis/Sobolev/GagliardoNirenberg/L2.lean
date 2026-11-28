/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.Sobolev.Embedding
import TauCeti.Analysis.Sobolev.W1p.SobolevEmbedding
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent

/-!
# The `L²`-based Gagliardo–Nirenberg inequality in dimension at least three

Let `E` be a real inner product space of dimension `d ≥ 3` with its Lebesgue measure. For
`0 ≤ θ ≤ 1` and the exponent `q` with `1 / q = 1 / 2 - θ / d`, that is `2 ≤ q ≤ 2 d / (d - 2)` and
`θ = d (1 / 2 - 1 / q)`, this file proves the Gagliardo–Nirenberg inequality

`‖u‖_q ≤ C(d) ^ θ ‖u‖₂ ^ (1 - θ) ‖∇u‖₂ ^ θ`,

first for compactly supported `C¹` maps `u : E → F` into a real inner product space and then on
`W^{1,2}(E)`. The constant `C(d) = TauCeti.sobolevConst d 2` depends on the dimension alone. In
dimension three with `q = 4` and `θ = 3 / 4` this is Ladyzhenskaya's inequality
`‖u‖₄ ≤ C ‖u‖₂ ^ (1 / 4) ‖∇u‖₂ ^ (3 / 4)` with an absolute constant `C`.

Integrating the inequality in time gives the parabolic interpolation inequality: a family `u(t)`
in `W^{1,2}(E)` with `u ∈ L^∞(L²)` and `∇u ∈ L²(L²)` lies in `L^r(L^q)` whenever
`2 / r + d / q = d / 2`, with

`‖u‖_{L^r(L^q)} ≤ C(d) ^ θ ‖u‖_{L^∞(L²)} ^ (1 - θ) ‖∇u‖_{L²(L²)} ^ θ`, `θ = 2 / r`.

The time variable ranges over an arbitrary measure space. These are the bounds through which the
energy class `L^∞(0,T; L²) ∩ L²(0,T; H¹)` of the Navier–Stokes equations controls the convective
term, for instance `L⁴(0,T; L³)` and `L^{10/3}` in dimension three.

## The argument

The inequality interpolates between the trivial endpoint `θ = 0` and the Sobolev inequality
`‖u‖_{2⋆} ≤ C(d) ‖∇u‖₂`, `1 / 2⋆ = 1 / 2 - 1 / d`, at `θ = 1`: logarithmic convexity of the `Lᵖ`
norms (`MeasureTheory.eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow`) gives
`‖u‖_q ≤ ‖u‖₂ ^ (1 - θ) ‖u‖_{2⋆} ^ θ`. The Sobolev inequality for test functions is Mathlib's
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner`; its constant depends on the chosen space and
measure, so it is transported from `EuclideanSpace ℝ (Fin d)` along a linear isometry, which
preserves Lebesgue measure and operator norms. On `W^{1,2}(E)` the Sobolev inequality passes from
test functions by `TauCeti.W1p.eLpNorm_value_le_of_forall_testFunction`, since test functions are
dense in `W^{1,2}(E)` (`TauCeti.W1p.mem_w1p0Submodule_top`).

## Main results

* `TauCeti.sobolevConst`: the dimensional constant `C(d, p)` of the Gagliardo–Nirenberg–Sobolev
  inequality.
* `TauCeti.eLpNorm_le_sobolevConst_mul_eLpNorm_fderiv`: `‖u‖_{p⋆} ≤ C(d, p) ‖Du‖_p` on any
  `d`-dimensional real inner product space.
* `TauCeti.eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_fderiv_rpow`: the Gagliardo–Nirenberg inequality
  for compactly supported `C¹` maps, and `TauCeti.eLpNorm_four_le_of_finrank_eq_three` its case
  `d = 3`, `q = 4`.
* `TauCeti.W1p.eLpNorm_value_le_enorm_rpow_mul_enorm_gradient_rpow`: the inequality on
  `W^{1,2}(E)`, with `TauCeti.W1p.eLpNorm_value_four_le_of_finrank_eq_three` its case `d = 3`,
  `q = 4`, and `TauCeti.W1p.memLp_value_of_three_le_finrank` the embedding
  `W^{1,2}(E) ⊆ L^q(E)` for `2 ≤ q ≤ 2 d / (d - 2)`.
* `TauCeti.W1p.eLpNorm_eLpNorm_value_le_eLpNorm_rpow_mul_eLpNorm_gradient_rpow`: the parabolic
  interpolation inequality.

## References

* E. Gagliardo, *Ulteriori proprietà di alcune classi di funzioni in più variabili*, Ricerche Mat.
  8 (1959).
* L. Nirenberg, *On elliptic partial differential equations*, Ann. Scuola Norm. Sup. Pisa 13
  (1959), Lecture II.
* J. Bedrossian, V. Vicol, *The Mathematical Analysis of the Incompressible Euler and Navier–Stokes
  Equations*, Theorem A.26.
* O. A. Ladyzhenskaya, *The Mathematical Theory of Viscous Incompressible Flow*, 2nd ed., Chapter 1,
  §1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal

/-- The constant `C(d, p)` of the **Gagliardo–Nirenberg–Sobolev inequality**
`‖u‖_{p⋆} ≤ C(d, p) ‖Du‖_p`, `1 / p⋆ = 1 / p - 1 / d`, on a `d`-dimensional real inner product
space with its Lebesgue measure (`TauCeti.eLpNorm_le_sobolevConst_mul_eLpNorm_fderiv`). It depends
on the dimension `d` and the exponent `p` alone; it is Mathlib's constant
`MeasureTheory.eLpNormLESNormFDerivOfEqInnerConst` for `EuclideanSpace ℝ (Fin d)`. -/
def sobolevConst (d : ℕ) (p : ℝ) : ℝ≥0 :=
  eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (EuclideanSpace ℝ (Fin d))) p

/-- `TauCeti.sobolevConst d p` is Mathlib's Gagliardo–Nirenberg–Sobolev constant for the
`d`-dimensional Euclidean space. -/
theorem sobolevConst_def (d : ℕ) (p : ℝ) :
    sobolevConst d p =
      eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (EuclideanSpace ℝ (Fin d))) p :=
  (rfl)

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The Gagliardo–Nirenberg–Sobolev inequality with a dimensional constant.** Let `E` be a real
inner product space of dimension `d > 0` with its Lebesgue measure, `1 ≤ p` and
`1 / p⋆ = 1 / p - 1 / d`. A compactly supported `C¹` map `u` from `E` to a real inner product space
satisfies `‖u‖_{p⋆} ≤ C(d, p) ‖Du‖_p`, where `C(d, p) = TauCeti.sobolevConst d p` depends on `d`
and `p` alone. -/
theorem eLpNorm_le_sobolevConst_mul_eLpNorm_fderiv {u : E → F} (hu : ContDiff ℝ 1 u)
    (h2u : HasCompactSupport u) {p p' : ℝ≥0} (hp : 1 ≤ p) (hn : 0 < finrank ℝ E)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (finrank ℝ E : ℝ)⁻¹) :
    eLpNorm u p' volume ≤ sobolevConst (finrank ℝ E) p * eLpNorm (fderiv ℝ u) p volume := by
  -- Transport Mathlib's inequality on `ℝᵈ` along a linear isometry `ℝᵈ ≃ E`.
  let e := (stdOrthonormalBasis ℝ E).repr.symm
  have he : MeasurePreserving e := e.measurePreserving
  have hv : ContDiff ℝ 1 (u ∘ e) := hu.comp e.contDiff
  have h2v : HasCompactSupport (u ∘ e) :=
    h2u.comp_isClosedEmbedding e.toHomeomorph.isClosedEmbedding
  have key := eLpNorm_le_eLpNorm_fderiv_of_eq_inner volume hv h2v hp
    (by rwa [finrank_euclideanSpace_fin]) (by rwa [finrank_euclideanSpace_fin])
  have hvalue : eLpNorm (u ∘ e) p' volume = eLpNorm u p' volume :=
    eLpNorm_comp_measurePreserving hu.continuous.aestronglyMeasurable he
  have hderiv : eLpNorm (fderiv ℝ (u ∘ e)) p volume = eLpNorm (fderiv ℝ u) p volume := by
    have hcomp : ∀ y, ‖fderiv ℝ (u ∘ e) y‖ = ‖(fderiv ℝ u ∘ e) y‖ := fun y ↦ by
      rw [← e.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.comp_right_fderiv,
        Function.comp_apply]
      exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ e
    rw [← eLpNorm_comp_measurePreserving
      (hu.continuous_fderiv one_ne_zero).aestronglyMeasurable he]
    exact eLpNorm_congr_norm_ae (hv.continuous_fderiv one_ne_zero).aestronglyMeasurable
      ((hu.continuous_fderiv one_ne_zero).comp e.continuous).aestronglyMeasurable
      (.of_forall hcomp)
  rw [hvalue, hderiv] at key
  exact key

/-- The exponent `2⋆` of the Sobolev embedding of `W^{1,2}` in dimension `d ≥ 3`, with
`1 / 2⋆ = 1 / 2 - 1 / d`. -/
private theorem exists_sobolevExponent_two {d : ℕ} (hd : 3 ≤ d) :
    ∃ s : ℝ≥0, (s : ℝ)⁻¹ = 2⁻¹ - (d : ℝ)⁻¹ := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos : 0 < (2 : ℝ)⁻¹ - (d : ℝ)⁻¹ := by
    rw [sub_pos]
    exact inv_strictAnti₀ two_pos (by linarith)
  refine ⟨((2 : ℝ)⁻¹ - (d : ℝ)⁻¹)⁻¹.toNNReal, ?_⟩
  rw [Real.coe_toNNReal _ (inv_pos.2 hpos).le, inv_inv]

/-- The exponent relation `1 / q = (1 - θ) / 2 + θ / 2⋆` behind the interpolation between `L²`
and `L^{2⋆}`, read in `ℝ≥0∞`. -/
private theorem inv_coe_eq_of_inv_eq {d : ℕ} (hd : 3 ≤ d) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    {q s : ℝ≥0} (hq : (q : ℝ)⁻¹ = 2⁻¹ - θ / d) (hs : (s : ℝ)⁻¹ = 2⁻¹ - (d : ℝ)⁻¹) :
    (q : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 - θ) * 2⁻¹ + ENNReal.ofReal θ * (s : ℝ≥0∞)⁻¹ := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdθ : θ / d ≤ 1 / 3 := by
    rw [div_le_iff₀ (by linarith)]
    linarith [hθ.2]
  have hsd : (d : ℝ)⁻¹ ≤ 1 / 3 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hq0 : 0 < (q : ℝ)⁻¹ := by rw [hq]; linarith
  have hs0 : 0 < (s : ℝ)⁻¹ := by rw [hs]; linarith
  have hcoe : ∀ t : ℝ≥0, 0 < (t : ℝ)⁻¹ → (t : ℝ≥0∞)⁻¹ = ENNReal.ofReal (t : ℝ)⁻¹ := fun t ht ↦ by
    rw [ENNReal.ofReal_inv_of_pos (inv_pos.1 ht), ENNReal.ofReal_coe_nnreal]
  rw [hcoe q hq0, hcoe s hs0, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos two_pos,
    ← ENNReal.ofReal_mul (by linarith [hθ.2]), ← ENNReal.ofReal_mul hθ.1,
    ← ENNReal.ofReal_add (mul_nonneg (by linarith [hθ.2]) (by norm_num)) (mul_nonneg hθ.1 hs0.le),
    hq, hs]
  congr 1
  ring

/-- **The Gagliardo–Nirenberg inequality**, `L²` form, in dimension `d ≥ 3`. Let `E` be a real
inner product space of dimension `d ≥ 3` with its Lebesgue measure, `0 ≤ θ ≤ 1` and
`1 / q = 1 / 2 - θ / d`, so that `2 ≤ q ≤ 2 d / (d - 2)`. A compactly supported `C¹` map `u` from
`E` to a real inner product space satisfies

`‖u‖_q ≤ C(d) ^ θ ‖u‖₂ ^ (1 - θ) ‖Du‖₂ ^ θ`

with `C(d) = TauCeti.sobolevConst d 2`. The exponent `θ = d (1 / 2 - 1 / q)` is the one forced by
the dilations `u ↦ u (λ ·)`. -/
theorem eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_fderiv_rpow (hd : 3 ≤ finrank ℝ E) {u : E → F}
    (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    {q : ℝ≥0} (hq : (q : ℝ)⁻¹ = 2⁻¹ - θ / finrank ℝ E) :
    eLpNorm u q volume ≤ (sobolevConst (finrank ℝ E) 2 : ℝ≥0∞) ^ θ *
      eLpNorm u 2 volume ^ (1 - θ) * eLpNorm (fderiv ℝ u) 2 volume ^ θ := by
  obtain ⟨s, hs⟩ := exists_sobolevExponent_two hd
  have hS := eLpNorm_le_sobolevConst_mul_eLpNorm_fderiv (p := 2) hu h2u one_le_two (by omega)
    (by rw [hs, NNReal.coe_inv, NNReal.coe_ofNat])
  rw [NNReal.coe_ofNat, ENNReal.coe_ofNat] at hS
  calc eLpNorm u q volume ≤ eLpNorm u 2 volume ^ (1 - θ) * eLpNorm u s volume ^ θ :=
        eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow hθ (inv_coe_eq_of_inv_eq hd hθ hq hs)
    _ ≤ eLpNorm u 2 volume ^ (1 - θ) *
          ((sobolevConst (finrank ℝ E) 2 : ℝ≥0∞) * eLpNorm (fderiv ℝ u) 2 volume) ^ θ := by
        gcongr
        exact hθ.1
    _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hθ.1]; ring

/-- **Ladyzhenskaya's inequality in dimension three.** On a three-dimensional real inner product
space, a compactly supported `C¹` map `u` into a real inner product space satisfies
`‖u‖₄ ≤ C ‖u‖₂ ^ (1 / 4) ‖Du‖₂ ^ (3 / 4)` with the absolute constant
`C = TauCeti.sobolevConst 3 2 ^ (3 / 4)`. -/
theorem eLpNorm_four_le_of_finrank_eq_three (hE : finrank ℝ E = 3) {u : E → F}
    (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u) :
    eLpNorm u 4 volume ≤ (sobolevConst 3 2 : ℝ≥0∞) ^ (3 / 4 : ℝ) *
      eLpNorm u 2 volume ^ (1 / 4 : ℝ) * eLpNorm (fderiv ℝ u) 2 volume ^ (3 / 4 : ℝ) := by
  have h := eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_fderiv_rpow (q := 4) hE.ge hu h2u
    (θ := 3 / 4) ⟨by norm_num, by norm_num⟩ (by rw [hE]; norm_num)
  rw [hE] at h
  norm_num at h ⊢
  exact h

/-! ### The inequality on `W^{1,2}(E)` -/

/-- **The Gagliardo–Nirenberg inequality on `W^{1,2}(E)`** in dimension `d ≥ 3`. For `0 ≤ θ ≤ 1`
and `1 / q = 1 / 2 - θ / d`, every `u ∈ W^{1,2}(E)` satisfies

`‖u‖_q ≤ C(d) ^ θ ‖u‖₂ ^ (1 - θ) ‖∇u‖₂ ^ θ`

with `C(d) = TauCeti.sobolevConst d 2`. -/
theorem W1p.eLpNorm_value_le_enorm_rpow_mul_enorm_gradient_rpow (hd : 3 ≤ finrank ℝ E)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) {q : ℝ≥0} (hq : (q : ℝ)⁻¹ = 2⁻¹ - θ / finrank ℝ E)
    (u : W1p (volume : Measure E) ⊤ 2) :
    eLpNorm (W1p.value u : E → ℝ) q volume ≤ (sobolevConst (finrank ℝ E) 2 : ℝ≥0∞) ^ θ *
      ‖W1p.value u‖ₑ ^ (1 - θ) * ‖W1p.gradient u‖ₑ ^ θ := by
  obtain ⟨s, hs⟩ := exists_sobolevExponent_two hd
  have hvol : ∀ (f : E → ℝ) (p : ℝ≥0∞),
      eLpNorm f p ((volume : Measure E).restrict (⊤ : Opens E)) = eLpNorm f p volume :=
    fun f p ↦ by rw [Opens.coe_top, Measure.restrict_univ]
  -- The Sobolev inequality at `2⋆`, transferred from test functions.
  have hS : eLpNorm (W1p.value u : E → ℝ) s volume ≤
      sobolevConst (finrank ℝ E) 2 * ‖W1p.gradient u‖ₑ := by
    have h := W1p.eLpNorm_value_le_of_forall_testFunction (q := s)
      (C := sobolevConst (finrank ℝ E) 2) (fun φ ↦ ?_) (W1p.mem_w1p0Submodule_top (by simp) u)
    · rwa [hvol] at h
    have hφ := eLpNorm_le_sobolevConst_mul_eLpNorm_fderiv (p := 2) (φ.contDiff.of_le (by simp))
      φ.hasCompactSupport one_le_two (by omega) (by rw [hs, NNReal.coe_inv, NNReal.coe_ofNat])
    rwa [NNReal.coe_ofNat, ENNReal.coe_ofNat] at hφ
  have hvalue : ‖W1p.value u‖ₑ = eLpNorm (W1p.value u : E → ℝ) 2 volume := by
    rw [Lp.eNorm_def, hvol]
  calc eLpNorm (W1p.value u : E → ℝ) q volume
      ≤ eLpNorm (W1p.value u : E → ℝ) 2 volume ^ (1 - θ) *
          eLpNorm (W1p.value u : E → ℝ) s volume ^ θ :=
        eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow hθ (inv_coe_eq_of_inv_eq hd hθ hq hs)
    _ ≤ ‖W1p.value u‖ₑ ^ (1 - θ) *
          ((sobolevConst (finrank ℝ E) 2 : ℝ≥0∞) * ‖W1p.gradient u‖ₑ) ^ θ := by
        rw [hvalue]
        gcongr
        exact hθ.1
    _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hθ.1]; ring

/-- **Ladyzhenskaya's inequality on `W^{1,2}(E)` in dimension three**: every `u ∈ W^{1,2}(E)`
satisfies `‖u‖₄ ≤ C ‖u‖₂ ^ (1 / 4) ‖∇u‖₂ ^ (3 / 4)` with the absolute constant
`C = TauCeti.sobolevConst 3 2 ^ (3 / 4)`. -/
theorem W1p.eLpNorm_value_four_le_of_finrank_eq_three (hE : finrank ℝ E = 3)
    (u : W1p (volume : Measure E) ⊤ 2) :
    eLpNorm (W1p.value u : E → ℝ) 4 volume ≤ (sobolevConst 3 2 : ℝ≥0∞) ^ (3 / 4 : ℝ) *
      ‖W1p.value u‖ₑ ^ (1 / 4 : ℝ) * ‖W1p.gradient u‖ₑ ^ (3 / 4 : ℝ) := by
  have h := W1p.eLpNorm_value_le_enorm_rpow_mul_enorm_gradient_rpow (q := 4) hE.ge
    (θ := 3 / 4) ⟨by norm_num, by norm_num⟩ (by rw [hE]; norm_num) u
  rw [hE] at h
  norm_num at h ⊢
  exact h

/-- An exponent `q` with `2 ≤ q` and `1 / 2 - 1 / d ≤ 1 / q` is `1 / q = 1 / 2 - θ / d` for some
`0 ≤ θ ≤ 1`, namely `θ = d (1 / 2 - 1 / q)`. -/
private theorem exists_mem_Icc_inv_eq {d : ℕ} (hd : 0 < d) {q : ℝ≥0} (hq2 : 2 ≤ q)
    (hq : 2⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) : ∃ θ ∈ Icc (0 : ℝ) 1, (q : ℝ)⁻¹ = 2⁻¹ - θ / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hq2' : (q : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ two_pos (by exact_mod_cast hq2)
  refine ⟨d * (2⁻¹ - (q : ℝ)⁻¹), ⟨mul_nonneg hd'.le (by linarith), ?_⟩, ?_⟩
  · have := mul_le_mul_of_nonneg_left (show 2⁻¹ - (q : ℝ)⁻¹ ≤ (d : ℝ)⁻¹ by linarith) hd'.le
    rwa [mul_inv_cancel₀ hd'.ne'] at this
  · rw [mul_div_cancel_left₀ _ hd'.ne']
    ring

/-- For `2 ≤ q ≤ 2 d / (d - 2)` the `L^q` norm of `u ∈ W^{1,2}(E)` is bounded by a constant
times the norm of `u`. -/
private theorem W1p.exists_eLpNorm_value_le_mul_enorm (hd : 3 ≤ finrank ℝ E) {q : ℝ≥0}
    (hq2 : 2 ≤ q) (hq : 2⁻¹ - (finrank ℝ E : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ u : W1p (volume : Measure E) ⊤ 2,
      eLpNorm (W1p.value u : E → ℝ) q volume ≤ C * ‖u‖ₑ := by
  obtain ⟨θ, hθ, hqθ⟩ := exists_mem_Icc_inv_eq (by omega) hq2 hq
  refine ⟨sobolevConst (finrank ℝ E) 2 ^ θ, fun u ↦ ?_⟩
  refine (W1p.eLpNorm_value_le_enorm_rpow_mul_enorm_gradient_rpow hd hθ hqθ u).trans ?_
  rw [ENNReal.coe_rpow_of_nonneg _ hθ.1, mul_assoc]
  gcongr
  calc ‖W1p.value u‖ₑ ^ (1 - θ) * ‖W1p.gradient u‖ₑ ^ θ ≤ ‖u‖ₑ ^ (1 - θ) * ‖u‖ₑ ^ θ := by
        gcongr
        exacts [by linarith [hθ.2], W1p.enorm_value_le u, hθ.1, W1p.enorm_gradient_le u]
    _ = ‖u‖ₑ := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith [hθ.2]) hθ.1, sub_add_cancel,
          ENNReal.rpow_one]

/-- **The Sobolev embedding `W^{1,2}(E) ⊆ L^q(E)`** in dimension `d ≥ 3`, for every
`2 ≤ q ≤ 2 d / (d - 2)`, that is `1 / 2 - 1 / d ≤ 1 / q ≤ 1 / 2`. -/
theorem W1p.memLp_value_of_three_le_finrank (hd : 3 ≤ finrank ℝ E) {q : ℝ≥0} (hq2 : 2 ≤ q)
    (hq : 2⁻¹ - (finrank ℝ E : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) (u : W1p (volume : Measure E) ⊤ 2) :
    MemLp (W1p.value u : E → ℝ) q volume := by
  obtain ⟨C, hC⟩ := W1p.exists_eLpNorm_value_le_mul_enorm hd hq2 hq
  exact (hC u).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top eNorm_lt_top)

/-! ### Parabolic interpolation -/

/-- **Parabolic interpolation** in dimension `d ≥ 3`. Let `0 ≤ θ ≤ 1`, `1 / q = 1 / 2 - θ / d` and
`1 / r = θ / 2`, so that `2 / r + d / q = d / 2`. For an almost everywhere strongly measurable
family `u` of elements of `W^{1,2}(E)` indexed by a measure space,

`‖u‖_{L^r(L^q)} ≤ C(d) ^ θ ‖u‖_{L^∞(L²)} ^ (1 - θ) ‖∇u‖_{L²(L²)} ^ θ`

with `C(d) = TauCeti.sobolevConst d 2`. So the energy class `L^∞(0,T; L²) ∩ L²(0,T; W^{1,2})` lies
in `L^r(0,T; L^q)`. -/
theorem W1p.eLpNorm_eLpNorm_value_le_eLpNorm_rpow_mul_eLpNorm_gradient_rpow {α : Type*}
    [MeasurableSpace α] {ν : Measure α} (hd : 3 ≤ finrank ℝ E) {θ : ℝ}
    (hθ : θ ∈ Icc (0 : ℝ) 1) {q : ℝ≥0} (hq : (q : ℝ)⁻¹ = 2⁻¹ - θ / finrank ℝ E) {r : ℝ≥0∞}
    (hr : r⁻¹ = ENNReal.ofReal (θ / 2)) {u : α → W1p (volume : Measure E) ⊤ 2}
    (hu : AEStronglyMeasurable u ν) :
    eLpNorm (fun t ↦ eLpNorm (W1p.value (u t) : E → ℝ) q volume) r ν ≤
      (sobolevConst (finrank ℝ E) 2 : ℝ≥0∞) ^ θ *
        eLpNorm (fun t ↦ W1p.value (u t)) ∞ ν ^ (1 - θ) *
        eLpNorm (fun t ↦ W1p.gradient (u t)) 2 ν ^ θ := by
  set C := sobolevConst (finrank ℝ E) 2
  have hd' : (3 : ℝ) ≤ finrank ℝ E := by exact_mod_cast hd
  have hθd : θ / finrank ℝ E ≤ (finrank ℝ E : ℝ)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_of_le_one_left (by positivity) hθ.2
  have hq0 : 0 < (q : ℝ)⁻¹ := by
    rw [hq]
    have : (finrank ℝ E : ℝ)⁻¹ ≤ 3⁻¹ := inv_anti₀ (by norm_num) hd'
    linarith
  have hq2 : 2 ≤ q := by
    have h : (q : ℝ)⁻¹ ≤ 2⁻¹ := by
      rw [hq]
      linarith [div_nonneg hθ.1 (Nat.cast_nonneg (α := ℝ) (finrank ℝ E))]
    exact_mod_cast (inv_le_inv₀ (inv_pos.1 hq0) two_pos).1 h
  have hqd : 2⁻¹ - (finrank ℝ E : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ := by rw [hq]; linarith
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast one_le_two.trans hq2⟩
  -- The `L^q` norm of `u t` is the norm of its image under the embedding `W^{1,2}(E) ↪ L^q(E)`,
  -- hence measurable in `t`.
  obtain ⟨S, hS⟩ := W1p.exists_lpEmbeddingL_of_eLpNorm_value_le (V := univ) (subset_univ _) <| by
    obtain ⟨K, hK⟩ := W1p.exists_eLpNorm_value_le_mul_enorm hd hq2 hqd
    exact ⟨K, fun v ↦ by simpa only [Measure.restrict_univ] using hK v⟩
  have hf : (fun t ↦ eLpNorm (W1p.value (u t) : E → ℝ) q volume) = fun t ↦ ‖S (u t)‖ₑ := by
    ext t
    rw [Lp.eNorm_def, eLpNorm_congr_ae (hS (u t)), Measure.restrict_univ]
  have hval : AEStronglyMeasurable (fun t ↦ W1p.value (u t)) ν := by
    simpa only [W1p.valueL_apply] using W1p.valueL.continuous.comp_aestronglyMeasurable hu
  have hgrad : AEStronglyMeasurable (fun t ↦ W1p.gradient (u t)) ν := by
    simpa only [W1p.gradientL_apply] using W1p.gradientL.continuous.comp_aestronglyMeasurable hu
  -- Hölder's inequality for the pointwise Gagliardo–Nirenberg bound, with `L^∞` and `L²` in time.
  have h := eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow_of_ae_le (p₀ := ∞) (p₁ := 2) hθ
    (by rw [hr, ENNReal.inv_top, mul_zero, zero_add, ENNReal.ofReal_div_of_pos two_pos,
      ENNReal.ofReal_ofNat, div_eq_mul_inv])
    (hf ▸ (continuous_eNorm.comp S.continuous).comp_aestronglyMeasurable hu) hval
    (hgrad.const_smul (C : ℝ)) (.of_forall fun t ↦ ?_)
  · rw [eLpNorm_const_smul, ENNReal.mul_rpow_of_nonneg _ _ hθ.1] at h
    refine h.trans_eq ?_
    rw [Real.eNorm_eq_ofReal C.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    ring
  · rw [eNorm_eq_self, Pi.smul_apply, eNorm_smul, ENNReal.mul_rpow_of_nonneg _ _ hθ.1,
      Real.eNorm_eq_ofReal C.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    refine (W1p.eLpNorm_value_le_enorm_rpow_mul_enorm_gradient_rpow hd hθ hq (u t)).trans_eq ?_
    ring

end TauCeti
