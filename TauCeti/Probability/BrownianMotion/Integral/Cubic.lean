/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.BrownianMotion.TimeIntegral.Basic
import TauCeti.Probability.BrownianMotion.CubicVariation
import TauCeti.Probability.BrownianMotion.WeightedQuadraticVariation
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The cubic Brownian Itô partition limit

Left-point sums of `B² dB` converge in native real `L²` to
`B_T³ / 3 - ∫₀ᵀ B_s ds`. The time integral here is the ordinary Bochner integral of the
`L²`-valued Brownian evaluation curve. No identification with samplewise time integration,
or construction of a general stochastic integral, is assumed.

The finite-grid error estimate combines the centered weighted quadratic error, the cubic
increment sum and the ordinary time-quadrature error. It applies to every nondecreasing
finite grid starting at `0`, including repeated dates and the empty zero-horizon grid.
Consequently no nestedness or summability of the meshes is required for mean-square convergence.
Only pre-Brownian laws are used; path continuity and filtration conditions are unnecessary.
This polynomial change-of-variables limit is independent of a general
Itô formula.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- Left-point Brownian sums with squared Brownian heights are square integrable. -/
theorem memLp_sum_eval_sq_mul_sub (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (n : ℕ) :
    MemLp (fun ω ↦ ∑ i ∈ range n, B (t i) ω ^ 2 *
      (B (t (i + 1)) ω - B (t i) ω)) 2 P := by
  let : ENNReal.HolderTriple 4 4 2 := .of_toReal (by norm_num [Real.holderTriple_iff])
  exact memLp_finsetSum _ fun i _ ↦
    (hB.memLp_pow_eval (t i) 2 (p := 4) (by norm_num)).fun_mul
      ((hB.hasLaw_sub _ _).memLp (memLp_id_gaussianReal' 4 (by norm_num)))

private theorem toLp_sum_eval_sq_mul_sub_eq (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (n : ℕ) (hzero : t 0 = 0) :
    let Z := fun ω ↦ ∑ i ∈ range n, B (t i) ω *
      ((B (t (i + 1)) ω - B (t i) ω) ^ 2 - ((t (i + 1) : ℝ) - t i))
    let C := fun ω ↦ ∑ i ∈ range n, (B (t (i + 1)) ω - B (t i) ω) ^ 3
    ∀ (hZ : MemLp Z 2 P) (hC : MemLp C 2 P),
      (hB.memLp_sum_eval_sq_mul_sub t n).toLp _ =
        (1 / 3 : ℝ) • (hB.memLp_pow_eval (t n) 3 (by norm_num)).toLp _ - hZ.toLp Z -
          (1 / 3 : ℝ) • hC.toLp C -
            ∑ i ∈ range n, ((t (i + 1) : ℝ) - t i) • hB.toL2 (t i) := by
  intro Z C hZ hC
  -- Telescope the pointwise cubic expansion.
  have hexp (ω : Ω) :
      (B (t n) ω ^ 3 - B (t 0) ω ^ 3) / 3 =
        (∑ i ∈ range n, B (t i) ω ^ 2 * (B (t (i + 1)) ω - B (t i) ω)) +
          Z ω + (∑ i ∈ range n, ((t (i + 1) : ℝ) - t i) * B (t i) ω) + C ω / 3 := by
    rw [← sum_range_sub (fun i ↦ B (t i) ω ^ 3), sum_div]
    simp only [Z, C, sum_div, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  have hrect : ⇑(∑ i ∈ range n, ((t (i + 1) : ℝ) - t i) • hB.toL2 (t i)) =ᵐ[P]
      fun ω ↦ ∑ i ∈ range n, ((t (i + 1) : ℝ) - t i) * B (t i) ω :=
    (Lp.coeFn_finsetSum _ _).trans (by
      simpa only [Finset.sum_fn, Pi.smul_def, smul_eq_mul] using
        (eventuallyEq_sum (s := range n) fun i _ ↦
          (Lp.coeFn_smul ((t (i + 1) : ℝ) - t i) (hB.toL2 (t i))).trans
            ((hB.coeFn_toL2 (t i)).const_smul ((t (i + 1) : ℝ) - t i))))
  apply Lp.ext
  filter_upwards [(hB.memLp_sum_eval_sq_mul_sub t n).coeFn_toLp,
    Lp.coeFn_sub ((1 / 3 : ℝ) • (hB.memLp_pow_eval (t n) 3 (by norm_num)).toLp _ -
      hZ.toLp Z - (1 / 3 : ℝ) • hC.toLp C) _,
    Lp.coeFn_sub ((1 / 3 : ℝ) • (hB.memLp_pow_eval (t n) 3 (by norm_num)).toLp _ -
      hZ.toLp Z) _,
    Lp.coeFn_sub ((1 / 3 : ℝ) •
      (hB.memLp_pow_eval (t n) 3 (p := 2) (by norm_num)).toLp _) (hZ.toLp Z),
    Lp.coeFn_smul (1 / 3 : ℝ) ((hB.memLp_pow_eval (t n) 3 (p := 2) (by norm_num)).toLp _),
    Lp.coeFn_smul (1 / 3 : ℝ) (hC.toLp C),
    (hB.memLp_pow_eval (t n) 3 (p := 2) (by norm_num)).coeFn_toLp,
    hZ.coeFn_toLp, hC.coeFn_toLp, hrect, hB.eval_zero_ae_eq_zero]
    with ω ha hsub₁ hsub₂ hsub₃ hsm₁ hsm₂ hpow hz hc hsum h0
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hsub₁ hsub₂ hsub₃ hsm₁ hsm₂
  rw [ha, hsub₁, hsub₂, hsub₃, hsm₁, hsm₂, hpow, hz, hc, hsum]
  have hx := hexp ω
  rw [hzero, h0] at hx
  linarith

/-- A finite-grid mean-square error bound for the cubic Brownian Itô sums. The error is
at most `6 T² δ + 6 T δ²` when the grid spans `[0,T]` and has mesh at most `δ`.
The time integral is taken in native `L²`. -/
theorem norm_toLp_sum_eval_sq_mul_sub_sub_sq_le (hB : IsPreBrownianReal B P)
    {t : ℕ → ℝ≥0} {n : ℕ} (ht : MonotoneOn t (Set.Iic n)) (hzero : t 0 = 0)
    {δ : ℝ} (hmesh : ∀ i < n, (t (i + 1) : ℝ) - t i ≤ δ) :
    ‖(hB.memLp_sum_eval_sq_mul_sub t n).toLp _ -
      ((1 / 3 : ℝ) • (hB.memLp_pow_eval (t n) 3 (by norm_num)).toLp _ -
        ∫ u in (0 : ℝ)..t n, hB.toL2 u.toNNReal)‖ ^ 2 ≤
      6 * (t n : ℝ) ^ 2 * δ + 6 * (t n : ℝ) * δ ^ 2 := by
  let W := hB
  let Z (ω : Ω) := ∑ i ∈ range n, B (t i) ω *
    ((B (t (i + 1)) ω - B (t i) ω) ^ 2 - ((t (i + 1) : ℝ) - t i))
  let C (ω : Ω) := ∑ i ∈ range n, (B (t (i + 1)) ω - B (t i) ω) ^ 3
  have hZ : MemLp Z 2 P := W.memLp_sum_eval_mul_sq_sub_sub t n
  have hC : MemLp C 2 P := memLp_finsetSum _ fun i _ ↦ W.memLp_cube_sub _ _
  let z := hZ.toLp Z
  let c := hC.toLp C
  let L := ∑ i ∈ range n, W.leftRiemannError (t i) (t (i + 1))
  -- The three previously computed second moments control the three error terms.
  have hz : ‖z‖ ^ 2 ≤ 2 * (t n : ℝ) ^ 2 * δ := by
    have h := W.integral_sq_sum_eval_mul_sq_sub_sub_le ht hmesh
    simp only [hzero, NNReal.coe_zero, sub_zero] at h
    have hfactor : 2 * (t n : ℝ) * (t n : ℝ) * δ = 2 * (t n : ℝ) ^ 2 * δ := by ring
    simpa only [z, MemLp.norm_toLp_sq, Real.norm_eq_abs, sq_abs, Z, hfactor] using h
  have hc : ‖c‖ ^ 2 ≤ 15 * (t n : ℝ) * δ ^ 2 := by
    simpa only [c, MemLp.norm_toLp_sq, Real.norm_eq_abs, sq_abs, C, hzero,
      NNReal.coe_zero, sub_zero] using W.integral_sq_sum_range_cube_sub_le ht hmesh
  have hL : ‖L‖ ^ 2 ≤ (t n : ℝ) * δ ^ 2 / 3 := by
    simpa only [hzero, NNReal.coe_zero, sub_zero] using
      W.norm_sum_leftRiemannError_sq_le ht hmesh
  -- The L² cubic decomposition leaves exactly the time-quadrature error.
  have hR : (∑ i ∈ range n, ((t (i + 1) : ℝ) - t i) • W.toL2 (t i)) -
      (∫ u in (0 : ℝ)..t n, W.toL2 u.toNNReal) = L := by
    simpa only [hzero, NNReal.coe_zero] using (W.sum_leftRiemannError_eq t n).symm
  have heq : (hB.memLp_sum_eval_sq_mul_sub t n).toLp _ -
      ((1 / 3 : ℝ) • (W.memLp_pow_eval (t n) 3 (by norm_num)).toLp _ -
        ∫ u in (0 : ℝ)..t n, W.toL2 u.toNNReal) = -(z + (1 / 3 : ℝ) • c + L) := by
    rw [← hR, W.toLp_sum_eval_sq_mul_sub_eq t n hzero hZ hC]
    abel
  rw [heq, norm_neg]
  have htriangle := (norm_add_le (z + (1 / 3 : ℝ) • c) L).trans
    (add_le_add_left (norm_add_le z ((1 / 3 : ℝ) • c)) ‖L‖)
  rw [norm_smul, Real.norm_eq_abs] at htriangle
  norm_num at htriangle
  have hsquare := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr htriangle
  -- (a+b+c)² ≤ 3(a²+b²+c²); 3(2T²δ + 15Tδ²/9 + Tδ²/3) = 6T²δ + 6Tδ².
  nlinarith [sq_nonneg (‖z‖ - ‖c‖ / 3), sq_nonneg (‖z‖ - ‖L‖),
    sq_nonneg (‖c‖ / 3 - ‖L‖)]

/-- **The cubic Brownian Itô partition limit.** Along every deterministic vanishing-mesh
family spanning `[0,T]`, the sums of `B² dB` converge in `L²` to `B_T³/3 - ∫₀ᵀ B_s ds`.
The integral in the conclusion is an ordinary `L²`-valued time integral. -/
theorem tendsto_toLp_sum_eval_sq_mul_sub (hB : IsPreBrownianReal B P)
    {ι : Type*} {l : Filter ι} {t : ι → ℕ → ℝ≥0} {n : ι → ℕ} {δ : ι → ℝ}
    {T : ℝ≥0} (ht : ∀ k, MonotoneOn (t k) (Set.Iic (n k)))
    (hzero : ∀ k, t k 0 = 0) (hT : ∀ k, t k (n k) = T)
    (hmesh : ∀ k i, i < n k → (t k (i + 1) : ℝ) - t k i ≤ δ k)
    (hlim : Tendsto δ l (𝓝 0)) :
    Tendsto (fun k ↦ (hB.memLp_sum_eval_sq_mul_sub (t k) (n k)).toLp _) l
      (𝓝 ((1 / 3 : ℝ) • (hB.memLp_pow_eval T 3 (by norm_num)).toLp _ -
        ∫ u in (0 : ℝ)..T, hB.toL2 u.toNNReal)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound k := hB.norm_toLp_sum_eval_sq_mul_sub_sub_sq_le (ht k) (hzero k) (hmesh k)
  simp only [hT] at hbound
  have hs := squeeze_zero (fun k ↦ sq_nonneg _) hbound
    (by simpa using ((hlim.const_mul (6 * (T : ℝ) ^ 2)).add
      ((hlim.pow 2).const_mul (6 * (T : ℝ)))))
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt

end ProbabilityTheory.IsPreBrownianReal
