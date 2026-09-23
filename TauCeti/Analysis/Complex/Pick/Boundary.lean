/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pick.Nevanlinna
import Mathlib.Order.SuccPred.IntervalSucc

/-!
# Real boundary values and the support of a Nevanlinna measure

A Nevanlinna representation

`F z = b z + ∫ x, (1 + x z) / (x - z) ∂rho(x) + c`

of a Pick function has imaginary part

`Im F (u + i v) = b v + ∫ x, v (1 + x ^ 2) / |x - (u + i v)| ^ 2 ∂rho(x)`,

a Poisson integral against the weighted measure `(1 + x ^ 2) rho(dx)`.  Where the boundary values
of `F` are real, that Poisson integral must die as `v` tends to `0`, and `rho` can carry no mass
there: this is the vanishing half of the Stieltjes--Perron inversion formula.

The argument here is elementary.  On the interval `[u - v, u + v]` the Poisson kernel is at least
`1 / (2 v)`, so `rho [u - v, u + v] ≤ 2 v * Im F (u + i v)`; covering a compact interval by
`N` such intervals of half-width `v = (b - a) / (2 N)`, on which `Im F (· + i v)` is uniformly
small, bounds `rho [a, b]` by an arbitrarily small multiple of `b - a`.

The consequence recorded here is the one the theory of complete Bernstein functions needs: a Pick
function that continues holomorphically across the positive half-axis and is real there has a
Nevanlinna representation whose measure lives on `(-∞, 0]`.

## Main declarations

* `TauCeti.measureReal_Icc_le_of_eq_nevanlinnaKernel_add`: the Poisson lower bound
  `rho [u - v, u + v] ≤ 2 v * Im F (u + i v)`.
* `TauCeti.measure_Icc_eq_zero_of_eq_nevanlinnaKernel_add`: a Nevanlinna measure gives no mass to
  a compact interval across which its imaginary part is continuous and has zero boundary values.
* `TauCeti.exists_isFiniteMeasure_eq_nevanlinnaKernel_add_of_im_eq_zero`: a Pick function that is
  holomorphic on the slit plane and real on `(0, ∞)` has a Nevanlinna measure vanishing on
  `(0, ∞)`.

## References

* N. I. Akhiezer, *The Classical Moment Problem and Some Related Questions in Analysis*,
  Section 3.1 (the Stieltjes--Perron inversion formula).
* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*,
  2nd ed., Chapter 6.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set Topology

namespace TauCeti

variable {F : ℂ → ℂ} {mu : Measure ℝ} {beta c : ℝ}

/-- **The Poisson lower bound of a Nevanlinna representation.** The mass a Nevanlinna measure
gives to the interval of centre `u` and half-width `v` is at most `2 v` times the imaginary part
of the represented function at `u + i v`. -/
theorem measureReal_Icc_le_of_eq_nevanlinnaKernel_add [IsFiniteMeasure mu] (hbeta : 0 ≤ beta)
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = (beta : ℂ) * z + ∫ x, nevanlinnaKernel z x ∂mu + c)
    (u : ℝ) {v : ℝ} (hv : 0 < v) :
    mu.real (Icc (u - v) (u + v)) ≤ 2 * v * (F ((u : ℂ) + (v : ℂ) * I)).im := by
  set z : ℂ := (u : ℂ) + (v : ℂ) * I with hzdef
  have hzre : z.re = u := by simp [hzdef]
  have hzim : z.im = v := by simp [hzdef]
  have hzmem : z ∈ UpperHalfPlane.upperHalfPlaneSet := by
    simpa [UpperHalfPlane.upperHalfPlaneSet, hzim] using hv
  have hint : Integrable (nevanlinnaKernel z) mu := integrable_nevanlinnaKernel hzmem mu
  have hintim : Integrable (fun x ↦ (nevanlinnaKernel z x).im) mu := hint.im
  have hnonneg : ∀ x : ℝ, 0 ≤ (nevanlinnaKernel z x).im := fun x ↦ by
    rw [nevanlinnaKernel_im, hzim]
    exact div_nonneg (mul_nonneg hv.le (by positivity)) (normSq_nonneg _)
  have hswap : (∫ x, nevanlinnaKernel z x ∂mu).im = ∫ x, (nevanlinnaKernel z x).im ∂mu := by
    simpa using (Complex.imCLM.integral_comp_comm hint).symm
  have hF : (F z).im = beta * v + ∫ x, (nevanlinnaKernel z x).im ∂mu := by
    rw [hrep z hzmem]
    simp [Complex.add_im, Complex.mul_im, hzim, hswap]
  have hlow : (2 * v)⁻¹ * mu.real (Icc (u - v) (u + v)) ≤
      ∫ x in Icc (u - v) (u + v), (nevanlinnaKernel z x).im ∂mu := by
    refine setIntegral_ge_of_const_le_real measurableSet_Icc (measure_ne_top _ _) ?_
      hintim.integrableOn
    rintro x ⟨hx1, hx2⟩
    have hN : normSq ((x : ℂ) - z) = (x - u) ^ 2 + v ^ 2 := by
      simp only [normSq_apply, sub_re, sub_im, ofReal_re, ofReal_im, hzre, hzim]
      ring
    have hNle : (x - u) ^ 2 + v ^ 2 ≤ 2 * v ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ v - (x - u))
        (by linarith : (0 : ℝ) ≤ v + (x - u))]
    rw [nevanlinnaKernel_im, hzim, hN, inv_eq_one_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * v ^ 2) (sq_nonneg x)]
  have hsub : ∫ x in Icc (u - v) (u + v), (nevanlinnaKernel z x).im ∂mu ≤
      ∫ x, (nevanlinnaKernel z x).im ∂mu :=
    setIntegral_le_integral hintim (.of_forall hnonneg)
  have hkey : (2 * v)⁻¹ * mu.real (Icc (u - v) (u + v)) ≤ (F z).im := by
    rw [hF]
    nlinarith [mul_nonneg hbeta hv.le]
  calc mu.real (Icc (u - v) (u + v))
      = 2 * v * ((2 * v)⁻¹ * mu.real (Icc (u - v) (u + v))) := by
        field_simp
    _ ≤ 2 * v * (F z).im := by
        exact mul_le_mul_of_nonneg_left hkey (by positivity)

/-- The covering estimate behind the Stieltjes--Perron vanishing theorem.  If the imaginary part
of the represented function stays below `eps` at every height smaller than `delta` over `[a, b]`,
the Nevanlinna measure of `[a, b]` is at most `(b - a) * eps`: cover `[a, b]` by `N` intervals of
half-width `v = (b - a) / (2 N)` with `v < delta` and apply the Poisson lower bound to each. -/
private theorem measureReal_Icc_le_mul [IsFiniteMeasure mu] (hbeta : 0 ≤ beta)
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = (beta : ℂ) * z + ∫ x, nevanlinnaKernel z x ∂mu + c)
    {a b eps delta : ℝ} (hab : a < b) (hdelta : 0 < delta)
    (hd : ∀ u ∈ Icc a b, ∀ v : ℝ, 0 < v → v < delta →
      (F ((u : ℂ) + (v : ℂ) * I)).im < eps) :
    mu.real (Icc a b) ≤ (b - a) * eps := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / (2 * delta))
  have hNpos : 0 < N := by
    by_contra h
    have hzero : N = 0 := by omega
    rw [hzero, Nat.cast_zero] at hN
    exact absurd hN (not_lt.2 (div_nonneg (by linarith) (by positivity)))
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  set v : ℝ := (b - a) / (2 * N) with hvdef
  have hvpos : 0 < v := by
    rw [hvdef]
    positivity
  have hvlt : v < delta := by
    rw [hvdef, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hN
    nlinarith
  have hbeq : b = a + 2 * (N : ℝ) * v := by
    rw [hvdef]
    field_simp
    ring
  have hmono : Monotone (fun k : ℕ ↦ a + 2 * k * v) := by
    intro k l hkl
    have hklR : (k : ℝ) ≤ l := by exact_mod_cast hkl
    nlinarith [mul_nonneg (sub_nonneg.mpr hklR) hvpos.le]
  have hcover : Icc a b ⊆
      ⋃ k ∈ Finset.range N, Icc (a + 2 * k * v) (a + 2 * (k + 1) * v) := by
    intro x hx
    rcases hx.1.eq_or_lt with hxa | hxa
    · subst x
      simp only [Set.mem_iUnion, Finset.mem_range]
      exact ⟨0, hNpos, by constructor <;> simp [hvpos.le]⟩
    · have hx' : x ∈ ⋃ k ∈ Ico 0 N,
          Ioc (a + 2 * k * v) (a + 2 * (Order.succ k) * v) := by
        rw [hmono.biUnion_Ico_Ioc_map_succ]
        simpa only [Nat.cast_zero, mul_zero, zero_mul, add_zero, ← hbeq] using ⟨hxa, hx.2⟩
      simp only [Set.mem_iUnion, mem_Ico] at hx'
      obtain ⟨k, ⟨-, hkN⟩, hxk⟩ := hx'
      simp only [Set.mem_iUnion, Finset.mem_range]
      exact ⟨k, hkN, Ioc_subset_Icc_self (by simpa using hxk)⟩
  have hstep : ∀ k ∈ Finset.range N,
      mu.real (Icc (a + 2 * k * v) (a + 2 * (k + 1) * v)) ≤ 2 * v * eps := by
    intro k hk
    have hkN : (k : ℝ) + 1 ≤ N := by
      have h := Finset.mem_range.mp hk
      exact_mod_cast h
    set ck : ℝ := a + (2 * k + 1) * v with hck
    have hck1 : a + 2 * (k : ℝ) * v = ck - v := by rw [hck]; ring
    have hck2 : a + 2 * ((k : ℝ) + 1) * v = ck + v := by rw [hck]; ring
    have hckmem : ck ∈ Icc a b := by
      constructor
      · rw [hck]; nlinarith [Nat.cast_nonneg (α := ℝ) k]
      · rw [hck, hbeq]; nlinarith
    rw [hck1, hck2]
    refine (measureReal_Icc_le_of_eq_nevanlinnaKernel_add hbeta hrep ck hvpos).trans ?_
    nlinarith [hd ck hckmem v hvpos hvlt]
  calc mu.real (Icc a b)
      ≤ mu.real (⋃ k ∈ Finset.range N, Icc (a + 2 * k * v) (a + 2 * (k + 1) * v)) :=
        measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ k ∈ Finset.range N, mu.real (Icc (a + 2 * k * v) (a + 2 * (k + 1) * v)) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range N, 2 * v * eps := Finset.sum_le_sum hstep
    _ = (b - a) * eps := by
        have hNv : (N : ℝ) * (2 * v) = b - a := by
          rw [hvdef]
          field_simp
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, hNv]

/-- **The Stieltjes--Perron vanishing theorem.** A Nevanlinna measure gives no mass to a compact
interval over which the imaginary part of the represented function is continuous up to the real
axis and vanishes there.  Continuity is asked for on the closed rectangle of any positive height
`d` over the interval, as a function holomorphic near the interval supplies it. -/
theorem measure_Icc_eq_zero_of_eq_nevanlinnaKernel_add [IsFiniteMeasure mu]
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = (beta : ℂ) * z + ∫ x, nevanlinnaKernel z x ∂mu + c)
    {a b d : ℝ} (hab : a < b) (hd : 0 < d)
    (hcont : ContinuousOn (fun z ↦ (F z).im) (Icc a b ×ℂ Icc 0 d))
    (hzero : ∀ u ∈ Icc a b, (F (u : ℂ)).im = 0) :
    mu (Icc a b) = 0 := by
  let G : ℂ → ℂ := fun z ↦ F z - (beta : ℂ) * z
  have hrepG : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      G z = (0 : ℂ) * z + ∫ x, nevanlinnaKernel z x ∂mu + c := by
    intro z hz
    dsimp only [G]
    rw [hrep z hz]
    ring
  have hcontG : ContinuousOn (fun z ↦ (G z).im) (Icc a b ×ℂ Icc 0 d) := by
    have hlin : ContinuousOn (fun z : ℂ ↦ ((beta : ℂ) * z).im)
        (Icc a b ×ℂ Icc 0 d) := by fun_prop
    refine (hcont.sub hlin).congr ?_
    intro z _
    simp only [Pi.sub_apply, G, Complex.sub_im]
  have hzeroG : ∀ u ∈ Icc a b, (G (u : ℂ)).im = 0 := by
    intro u hu
    simp [G, hzero u hu]
  have hK : IsCompact ((Icc a b : Set ℝ) ×ℂ (Icc 0 d : Set ℝ)) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have huc := hK.uniformContinuousOn_of_continuous hcontG
  -- Uniform continuity on the closed rectangle turns the vanishing boundary values into a
  -- bound on `Im F` that is uniform in the base point, which the covering estimate consumes.
  have hsmall : ∀ eps : ℝ, 0 < eps → mu.real (Icc a b) ≤ (b - a) * eps := by
    intro eps heps
    obtain ⟨delta, hdelta, huniform⟩ := Metric.uniformContinuousOn_iff.mp huc eps heps
    -- Shrinking `delta` below `d` keeps the perturbed point inside the rectangle.
    refine measureReal_Icc_le_mul (le_refl 0) hrepG hab (lt_min hdelta hd)
      fun u hu v hv hvd ↦ ?_
    obtain ⟨hvdelta, hvd'⟩ := lt_min_iff.mp hvd
    have hmem1 : ((u : ℂ) + (v : ℂ) * I) ∈ (Icc a b ×ℂ Icc 0 d : Set ℂ) := by
      refine ⟨?_, ?_⟩ <;> simp [hu, hv.le, hvd'.le]
    have hmem2 : ((u : ℂ)) ∈ (Icc a b ×ℂ Icc 0 d : Set ℂ) := by
      refine ⟨?_, ?_⟩ <;> simp [hu, hd.le]
    have hdist : dist ((u : ℂ) + (v : ℂ) * I) (u : ℂ) < delta := by
      simpa [Complex.dist_eq, abs_of_pos hv] using hvdelta
    have hlt := huniform _ hmem1 _ hmem2 hdist
    simp only [Real.dist_eq, hzeroG u hu, sub_zero] at hlt
    exact (le_abs_self _).trans_lt hlt
  rw [← measureReal_eq_zero_iff (measure_ne_top _ _)]
  by_contra hne
  have hpos : 0 < mu.real (Icc a b) := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hle := hsmall (mu.real (Icc a b) / (2 * (b - a))) (div_pos hpos (by linarith))
  have heq : (b - a) * (mu.real (Icc a b) / (2 * (b - a))) = mu.real (Icc a b) / 2 := by
    field_simp
  rw [heq] at hle
  linarith

/-- The Nevanlinna integral of a finite measure carried by `(-∞, 0]` is continuous at every
point with positive real part.  Although the kernel has a pole on the real axis, that pole stays
a positive distance from the measure's support. -/
theorem continuousAt_integral_nevanlinnaKernel_of_measure_Ioi_eq_zero
    {rho : Measure ℝ} [IsFiniteMeasure rho] (hrho : rho (Ioi 0) = 0) {z₀ : ℂ}
    (hz₀ : 0 < z₀.re) :
    ContinuousAt (fun z : ℂ => ∫ x, nevanlinnaKernel z x ∂rho) z₀ := by
  have hale : ∀ᵐ x ∂rho, x ≤ 0 :=
    (measure_eq_zero_iff_ae_notMem.mp hrho).mono fun x hx => not_lt.mp hx
  refine tendsto_integral_filter_of_norm_le_const ?_ ?_ ?_
  · exact Eventually.of_forall fun z =>
      (measurable_nevanlinnaKernel z).aestronglyMeasurable
  · refine ⟨‖z₀‖ + z₀.re / 2 + (1 + (‖z₀‖ + z₀.re / 2) ^ 2) * (2 / z₀.re), ?_⟩
    filter_upwards [Metric.ball_mem_nhds z₀ (half_pos hz₀)] with z hz
    filter_upwards [hale] with x hx
    rw [Metric.mem_ball, dist_eq_norm] at hz
    exact norm_nevanlinnaKernel_le_of_nonpos_of_norm_sub_lt hz₀ hx hz
  · filter_upwards [hale] with x hx
    apply (continuousAt_nevanlinnaKernel_left ?_).tendsto
    intro h
    have hxt : x ≠ z₀.re := ne_of_lt (lt_of_le_of_lt hx hz₀)
    apply hxt
    simpa using congrArg Complex.re h

/-- A Nevanlinna representation valid on the upper half-plane holds at a positive real parameter
`t` at which `F` is continuous, provided its measure is carried by `(-∞, 0]`. -/
theorem eq_integral_nevanlinnaKernel_add_of_eqOn_upperHalfPlane
    {F : ℂ → ℂ} {rho : Measure ℝ} [IsFiniteMeasure rho] {b c t : ℝ}
    (hF : ContinuousAt F t) (hrho : rho (Ioi 0) = 0) (ht : 0 < t)
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = (b : ℂ) * z + ∫ x, nevanlinnaKernel z x ∂rho + c) :
    F t = (b : ℂ) * t + ∫ x, nevanlinnaKernel t x ∂rho + c := by
  have hnebot : (𝓝[UpperHalfPlane.upperHalfPlaneSet] (t : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (by
      rw [UpperHalfPlane.upperHalfPlaneSet, Complex.closure_setOfPred_lt_im]
      simp)
  have hright : ContinuousAt
      (fun w : ℂ => (b : ℂ) * w + ∫ x, nevanlinnaKernel w x ∂rho + c) t :=
    ((continuousAt_const.mul continuousAt_id).add
      (continuousAt_integral_nevanlinnaKernel_of_measure_Ioi_eq_zero hrho ht)).add
      continuousAt_const
  refine tendsto_nhds_unique' hnebot ?_
    (hright.tendsto.mono_left nhdsWithin_le_nhds)
  exact (hF.tendsto.mono_left nhdsWithin_le_nhds).congr'
    (eventually_nhdsWithin_of_forall hrep)

/-- **The Nevanlinna measure of a Pick function real on the positive half-axis.** A function that
is holomorphic on the slit plane, has nonnegative imaginary part on the upper half-plane and is
real on `(0, ∞)` admits a Nevanlinna representation whose measure vanishes on `(0, ∞)`. -/
theorem exists_isFiniteMeasure_eq_nevanlinnaKernel_add_of_im_eq_zero {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F Complex.slitPlane)
    (him : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ (F z).im)
    (hzero : ∀ t : ℝ, 0 < t → (F (t : ℂ)).im = 0) :
    ∃ (rho : Measure ℝ) (b : ℝ), IsFiniteMeasure rho ∧ 0 ≤ b ∧ rho (Ioi 0) = 0 ∧
      ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
        F z = (b : ℂ) * z + ∫ x, nevanlinnaKernel z x ∂rho + (F I).re := by
  have hsubH : UpperHalfPlane.upperHalfPlaneSet ⊆ Complex.slitPlane := by
    intro z hz
    have hz' : 0 < z.im := hz
    exact Complex.mem_slitPlane_iff.2 (Or.inr hz'.ne')
  obtain ⟨rho, beta, hrho, hbeta, hrep⟩ :=
    exists_isFiniteMeasure_eq_nevanlinnaKernel_add (hF.mono hsubH) him
  refine ⟨rho, beta, hrho, hbeta, ?_, hrep⟩
  have hcover : Ioi (0 : ℝ) ⊆ ⋃ n : ℕ, Icc (((n : ℝ) + 1)⁻¹) ((n : ℝ) + 2) := by
    intro t ht
    obtain ⟨n, hn⟩ := exists_nat_gt (max t t⁻¹)
    refine Set.mem_iUnion.2 ⟨n, ?_, ?_⟩
    · have h1 : t⁻¹ < (n : ℝ) + 1 := by
        have := (max_lt_iff.mp hn).2
        linarith
      have h2 : (1 : ℝ) < t * ((n : ℝ) + 1) := by
        have := mul_lt_mul_of_pos_left h1 ht
        rwa [mul_inv_cancel₀ ht.ne'] at this
      rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
      linarith
    · have := (max_lt_iff.mp hn).1
      linarith
  refine measure_mono_null hcover (measure_iUnion_null fun n ↦ ?_)
  set a : ℝ := ((n : ℝ) + 1)⁻¹ with hadef
  set b : ℝ := (n : ℝ) + 2 with hbdef
  have hapos : 0 < a := by
    rw [hadef]
    positivity
  have hale : a ≤ 1 := by
    rw [hadef, inv_le_one_iff₀]
    right
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hab : a < b := by
    rw [hbdef]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hrect : (Icc a b ×ℂ Icc 0 1 : Set ℂ) ⊆ Complex.slitPlane := by
    rintro z ⟨hz1, hz2⟩
    exact Complex.mem_slitPlane_iff.2 (Or.inl (lt_of_lt_of_le hapos hz1.1))
  refine measure_Icc_eq_zero_of_eq_nevanlinnaKernel_add hrep hab one_pos
    (Complex.continuous_im.comp_continuousOn ((hF.mono hrect).continuousOn))
    fun u hu ↦ hzero u (lt_of_lt_of_le hapos hu.1)

end TauCeti

end

end
