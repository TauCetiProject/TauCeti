/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Elementary
public import TauCeti.Probability.BrownianMotion.TimeIntegral
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
finite grid, including repeated dates and the empty zero-horizon grid. Consequently no
nestedness or summability of the meshes is required for mean-square convergence.
Only filtered pre-Brownian laws are used; path continuity and usual filtration conditions
are unnecessary. This polynomial change-of-variables limit is independent of a general
Itô formula.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped NNReal Topology

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-- Left-point Brownian sums with squared Brownian heights are square integrable. -/
theorem memLp_sum_eval_sq_mul_sub (hB : IsFilteredPreBrownianReal ℱ B P)
    {t : ℕ → ℝ≥0} {n : ℕ} (ht : MonotoneOn t (Set.Iic n)) :
    MemLp (fun ω ↦ ∑ i ∈ range n, B (t i) ω ^ 2 *
      (B (t (i + 1)) ω - B (t i) ω)) 2 P :=
  hB.memLp_sum_mul_sub ht (fun i _ ↦ (hB.adapted (t i)).stronglyMeasurable.pow 2)
    (fun i _ ↦ hB.toIsPreBrownianReal.memLp_pow_eval (t i) 2)

/-- A finite-grid mean-square error bound for the cubic Brownian Itô sums. The error is
at most `6 T² δ + 6 T δ²` when the grid spans `[0,T]` and has mesh at most `δ`.
The time integral is taken in native `L²`. -/
theorem norm_sum_eval_sq_mul_sub_sub_cubic_le (hB : IsFilteredPreBrownianReal ℱ B P)
    {t : ℕ → ℝ≥0} {n : ℕ} (ht : MonotoneOn t (Set.Iic n)) (hzero : t 0 = 0)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hmesh : ∀ i < n, (t (i + 1) : ℝ) - t i ≤ δ) :
    ‖(hB.memLp_sum_eval_sq_mul_sub ht).toLp _ -
      ((1 / 3 : ℝ) • (hB.toIsPreBrownianReal.memLp_pow_eval (t n) 3).toLp _ -
        ∫ u in (0 : ℝ)..t n, hB.toIsPreBrownianReal.toL2 u.toNNReal)‖ ^ 2 ≤
      6 * (t n : ℝ) ^ 2 * δ + 6 * (t n : ℝ) * δ ^ 2 := by
  let W := hB.toIsPreBrownianReal
  let Z (ω : Ω) := ∑ i ∈ range n, B (t i) ω *
    ((B (t (i + 1)) ω - B (t i) ω) ^ 2 - ((t (i + 1) : ℝ) - t i))
  let C (ω : Ω) := ∑ i ∈ range n, (B (t (i + 1)) ω - B (t i) ω) ^ 3
  have hZ : MemLp Z 2 P := memLp_finsetSum _ fun i hi ↦
    hB.memLp_mul_sq_sub_sub (ht (mem_range.mp hi).le (mem_range.mp hi) (Nat.le_succ i))
      (hB.adapted (t i)) ((W.hasLaw_eval (t i)).memLp (memLp_id_gaussianReal 2))
  have hC : MemLp C 2 P := memLp_finsetSum _ fun i _ ↦ W.memLp_cube_sub _ _
  let z := hZ.toLp Z
  let c := hC.toLp C
  let L := ∑ i ∈ range n, W.leftRiemannError (t i) (t (i + 1))
  -- The three previously computed second moments control the three error terms.
  have hz : ‖z‖ ^ 2 ≤ 2 * (t n : ℝ) ^ 2 * δ := by
    simpa only [z, MemLp.norm_toLp_sq, Real.norm_eq_abs, sq_abs, Z] using
      hB.integral_sq_sum_eval_mul_sq_sub_sub_le ht le_rfl hδ hmesh
  have hc : ‖c‖ ^ 2 ≤ 15 * (t n : ℝ) * δ ^ 2 := by
    have hgrid : Monotone (fun i : Fin (n + 1) ↦ t i) :=
      fun i j hij ↦ ht (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt) hij
    have hm (i : Fin n) : (t i.succ : ℝ) - t i.castSucc ≤ (Real.toNNReal δ : ℝ) := by
      simpa only [Real.coe_toNNReal δ hδ, Fin.val_succ, Fin.val_castSucc] using
        hmesh i i.isLt
    have h := W.integral_sq_sum_cube_sub_le hgrid hm
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last, Fin.val_zero, hzero,
      NNReal.coe_zero, sub_zero, Real.coe_toNNReal δ hδ] at h
    have hsum (ω : Ω) := Fin.sum_univ_eq_sum_range
      (fun i ↦ (B (t (i + 1)) ω - B (t i) ω) ^ 3) n
    simp_rw [hsum] at h
    simpa only [c, MemLp.norm_toLp_sq, Real.norm_eq_abs, sq_abs, C] using h
  have hL : ‖L‖ ^ 2 ≤ (t n : ℝ) * δ ^ 2 / 3 := by
    -- Extend the finite grid constantly after its last date to use the quadrature API.
    let s (i : ℕ) := t (min i n)
    have hs : Monotone s := fun i j hij ↦ ht (Set.mem_Iic.mpr (min_le_right _ _))
      (Set.mem_Iic.mpr (min_le_right _ _)) (min_le_min_right n hij)
    have heq : (∑ i ∈ range n, W.leftRiemannError (s i) (s (i + 1))) = L := by
      apply sum_congr rfl
      intro i hi
      simp only [s, min_eq_left (mem_range.mp hi).le,
        min_eq_left (Nat.succ_le_of_lt (mem_range.mp hi))]
    have hm (i : ℕ) (hi : i < n) : (s (i + 1) : ℝ) - s i ≤ δ := by
      simpa only [s, min_eq_left hi.le, min_eq_left (Nat.succ_le_of_lt hi)] using hmesh i hi
    have h := W.norm_sum_leftRiemannError_sq_le s hs n hm
    simpa only [heq, s, min_self, Nat.zero_min, hzero, NNReal.coe_zero, sub_zero] using h
  -- Telescope the cubic expansion. The remaining left rectangles give exactly L.
  have hexp (ω : Ω) :
      (B (t n) ω ^ 3 - B (t 0) ω ^ 3) / 3 =
        (∑ i ∈ range n, B (t i) ω ^ 2 * (B (t (i + 1)) ω - B (t i) ω)) +
          Z ω + (∑ i ∈ range n, ((t (i + 1) : ℝ) - t i) * B (t i) ω) + C ω / 3 := by
    rw [← sum_range_sub (fun i ↦ B (t i) ω ^ 3), sum_div]
    simp only [Z, C, sum_div, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  have hR : (∑ i ∈ range n, ((t (i + 1) : ℝ) - t i) • W.toL2 (t i)) -
      (∫ u in (0 : ℝ)..t n, W.toL2 u.toNNReal) = L := by
    simpa only [hzero, NNReal.coe_zero] using (W.sum_leftRiemannError_eq t n).symm
  have hrect : ⇑(∑ i ∈ range n, ((t (i + 1) : ℝ) - t i) • W.toL2 (t i)) =ᵐ[P]
      fun ω ↦ ∑ i ∈ range n, ((t (i + 1) : ℝ) - t i) * B (t i) ω :=
    (Lp.coeFn_finsetSum _ _).trans (by
      simpa only [Finset.sum_fn, Pi.smul_def, smul_eq_mul] using
        (eventuallyEq_sum (s := range n) fun i _ ↦
          (Lp.coeFn_smul ((t (i + 1) : ℝ) - t i) (W.toL2 (t i))).trans
            ((W.coeFn_toL2 (t i)).const_smul ((t (i + 1) : ℝ) - t i))))
  have heq : (hB.memLp_sum_eval_sq_mul_sub ht).toLp _ -
      ((1 / 3 : ℝ) • (W.memLp_pow_eval (t n) 3).toLp _ -
        ∫ u in (0 : ℝ)..t n, W.toL2 u.toNNReal) = -(z + (1 / 3 : ℝ) • c + L) := by
    rw [← hR]
    suffices h : (hB.memLp_sum_eval_sq_mul_sub ht).toLp _ =
        (1 / 3 : ℝ) • (W.memLp_pow_eval (t n) 3).toLp _ - z - (1 / 3 : ℝ) • c -
          ∑ i ∈ range n, ((t (i + 1) : ℝ) - t i) • W.toL2 (t i) by
      rw [h]
      abel
    apply Lp.ext
    filter_upwards [(hB.memLp_sum_eval_sq_mul_sub ht).coeFn_toLp,
      Lp.coeFn_sub ((1 / 3 : ℝ) • (W.memLp_pow_eval (t n) 3).toLp _ - z - (1 / 3 : ℝ) • c) _,
      Lp.coeFn_sub ((1 / 3 : ℝ) • (W.memLp_pow_eval (t n) 3).toLp _ - z) _,
      Lp.coeFn_sub ((1 / 3 : ℝ) • (W.memLp_pow_eval (t n) 3).toLp _) z,
      Lp.coeFn_smul (1 / 3 : ℝ) ((W.memLp_pow_eval (t n) 3).toLp _),
      Lp.coeFn_smul (1 / 3 : ℝ) c, (W.memLp_pow_eval (t n) 3).coeFn_toLp,
      hZ.coeFn_toLp, hC.coeFn_toLp, hrect, W.eval_zero_ae_eq_zero]
      with ω ha hsub₁ hsub₂ hsub₃ hsm₁ hsm₂ hpow hz hc hsum h0
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, z, c] at *
    rw [ha, hsub₁, hsub₂, hsub₃, hsm₁, hsm₂, hpow, hz, hc, hsum]
    have hx := hexp ω
    rw [hzero, h0] at hx
    linarith
  rw [heq, norm_neg]
  have htriangle := (norm_add_le (z + (1 / 3 : ℝ) • c) L).trans
    (add_le_add_left (norm_add_le z ((1 / 3 : ℝ) • c)) ‖L‖)
  rw [norm_smul, Real.norm_eq_abs] at htriangle
  norm_num at htriangle
  have hsquare := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr htriangle
  nlinarith [sq_nonneg (‖z‖ - ‖c‖ / 3), sq_nonneg (‖z‖ - ‖L‖),
    sq_nonneg (‖c‖ / 3 - ‖L‖)]

/-- **The cubic Brownian Itô partition limit.** Along every deterministic vanishing-mesh
family spanning `[0,T]`, the sums of `B² dB` converge in `L²` to `B_T³/3 - ∫₀ᵀ B_s ds`.
The integral in the conclusion is an ordinary `L²`-valued time integral. -/
theorem tendsto_sum_eval_sq_mul_sub_toLp (hB : IsFilteredPreBrownianReal ℱ B P)
    {ι : Type*} {l : Filter ι} {t : ι → ℕ → ℝ≥0} {n : ι → ℕ} {δ : ι → ℝ}
    {T : ℝ≥0} (ht : ∀ k, MonotoneOn (t k) (Set.Iic (n k)))
    (hzero : ∀ k, t k 0 = 0) (hT : ∀ k, t k (n k) = T)
    (hδ : ∀ k, 0 ≤ δ k)
    (hmesh : ∀ k i, i < n k → (t k (i + 1) : ℝ) - t k i ≤ δ k)
    (hlim : Tendsto δ l (𝓝 0)) :
    Tendsto (fun k ↦ (hB.memLp_sum_eval_sq_mul_sub (ht k)).toLp _) l
      (𝓝 ((1 / 3 : ℝ) • (hB.toIsPreBrownianReal.memLp_pow_eval T 3).toLp _ -
        ∫ u in (0 : ℝ)..T, hB.toIsPreBrownianReal.toL2 u.toNNReal)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound k := hB.norm_sum_eval_sq_mul_sub_sub_cubic_le (ht k) (hzero k) (hδ k) (hmesh k)
  simp only [hT] at hbound
  have hs := squeeze_zero (fun k ↦ sq_nonneg _) hbound
    (by simpa using ((hlim.const_mul (6 * (T : ℝ) ^ 2)).add
      ((hlim.pow 2).const_mul (6 * (T : ℝ)))))
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt

end TauCeti.Probability.IsFilteredPreBrownianReal
