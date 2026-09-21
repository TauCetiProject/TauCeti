/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pick.Nevanlinna

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
  a compact interval across which the represented function is continuous with real values.
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

open Complex MeasureTheory Set

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
    rw [im_nevanlinnaKernel, hzim]
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
    rw [im_nevanlinnaKernel, hzim, hN, inv_eq_one_div,
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

/-- A compact interval is covered by the `N` closed intervals of half-width `v` centred at
`a + (2 k + 1) v`.  This is the covering behind the Stieltjes--Perron estimate below. -/
private theorem Icc_subset_biUnion_Icc (a : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    ∀ N : ℕ, 0 < N → Icc a (a + 2 * N * v) ⊆
      ⋃ k ∈ Finset.range N, Icc (a + 2 * k * v) (a + 2 * (k + 1) * v) := by
  intro N
  induction N with
  | zero => omega
  | succ n ih =>
    intro _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h1 : a ≤ a + 2 * (n : ℝ) * v := by
        have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (Nat.cast_nonneg (α := ℝ) n)) hv
        linarith
      have h2 : a + 2 * (n : ℝ) * v ≤ a + 2 * ((n : ℝ) + 1) * v := by nlinarith
      have hstep : Icc a (a + 2 * ((n : ℝ) + 1) * v) =
          Icc a (a + 2 * (n : ℝ) * v) ∪ Icc (a + 2 * (n : ℝ) * v) (a + 2 * ((n : ℝ) + 1) * v) :=
        (Set.Icc_union_Icc_eq_Icc h1 h2).symm
      rw [Finset.range_add_one, Finset.set_biUnion_insert]
      push_cast
      rw [hstep]
      exact Set.union_subset (Set.subset_union_of_subset_right (ih hn) _) Set.subset_union_left

/-- The covering estimate behind the Stieltjes--Perron vanishing theorem.  If the imaginary part
of the represented function stays below `eps` at every height smaller than `delta` over `[a, b]`,
the Nevanlinna measure of `[a, b]` is at most `(b - a) * eps`: cover `[a, b]` by `N` intervals of
half-width `v = (b - a) / (2 N)` with `v < delta` and apply the Poisson lower bound to each. -/
private theorem measureReal_Icc_le_mul [IsFiniteMeasure mu] (hbeta : 0 ≤ beta)
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = (beta : ℂ) * z + ∫ x, nevanlinnaKernel z x ∂mu + c)
    {a b eps delta : ℝ} (hab : a < b) (hdelta : 0 < delta)
    (hd : ∀ u ∈ Icc a b, ∀ v : ℝ, 0 < v → v < delta → v ≤ 1 →
      (F ((u : ℂ) + (v : ℂ) * I)).im < eps) :
    mu.real (Icc a b) ≤ (b - a) * eps := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max ((b - a) / (2 * delta)) ((b - a) / 2))
  have hNpos : 0 < N := by
    by_contra h
    have hzero : N = 0 := by omega
    simp only [hzero, Nat.cast_zero, max_lt_iff] at hN
    nlinarith [hN.2]
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  set v : ℝ := (b - a) / (2 * N) with hvdef
  have hvpos : 0 < v := by
    rw [hvdef]
    positivity
  have hvlt : v < delta := by
    rw [hvdef, div_lt_iff₀ (by positivity)]
    have h := (max_lt_iff.mp hN).1
    rw [div_lt_iff₀ (by positivity)] at h
    nlinarith
  have hvle : v ≤ 1 := by
    rw [hvdef, div_le_one (by positivity)]
    have h := (max_lt_iff.mp hN).2
    rw [div_lt_iff₀ (by norm_num)] at h
    nlinarith
  have hbeq : b = a + 2 * (N : ℝ) * v := by
    rw [hvdef]
    field_simp
    ring
  have hcover : Icc a b ⊆
      ⋃ k ∈ Finset.range N, Icc (a + 2 * k * v) (a + 2 * (k + 1) * v) := by
    rw [hbeq]
    exact Icc_subset_biUnion_Icc a hvpos.le N hNpos
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
    nlinarith [hd ck hckmem v hvpos hvlt hvle]
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
interval over which the represented function is continuous up to the real axis and has real
boundary values there.  Continuity is asked for on the closed rectangle of unit height over the
interval; any positive height would do, and a function holomorphic near the interval supplies it.
-/
theorem measure_Icc_eq_zero_of_eq_nevanlinnaKernel_add [IsFiniteMeasure mu] (hbeta : 0 ≤ beta)
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = (beta : ℂ) * z + ∫ x, nevanlinnaKernel z x ∂mu + c)
    {a b : ℝ} (hab : a < b) (hcont : ContinuousOn F (Icc a b ×ℂ Icc 0 1))
    (hzero : ∀ u ∈ Icc a b, (F (u : ℂ)).im = 0) :
    mu (Icc a b) = 0 := by
  have hK : IsCompact ((Icc a b : Set ℝ) ×ℂ (Icc 0 1 : Set ℝ)) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have huc := hK.uniformContinuousOn_of_continuous
    (Complex.continuous_im.comp_continuousOn hcont)
  -- Uniform continuity on the closed rectangle turns the vanishing boundary values into a
  -- bound on `Im F` that is uniform in the base point, which the covering estimate consumes.
  have hsmall : ∀ eps : ℝ, 0 < eps → mu.real (Icc a b) ≤ (b - a) * eps := by
    intro eps heps
    obtain ⟨delta, hdelta, hd⟩ := Metric.uniformContinuousOn_iff.mp huc eps heps
    refine measureReal_Icc_le_mul hbeta hrep hab hdelta fun u hu v hv hvd hv1 ↦ ?_
    have hmem1 : ((u : ℂ) + (v : ℂ) * I) ∈ (Icc a b ×ℂ Icc 0 1 : Set ℂ) := by
      refine ⟨?_, ?_⟩ <;> simp [hu, hv.le, hv1]
    have hmem2 : ((u : ℂ)) ∈ (Icc a b ×ℂ Icc 0 1 : Set ℂ) := by
      refine ⟨?_, ?_⟩ <;> simp [hu]
    have hdist : dist ((u : ℂ) + (v : ℂ) * I) (u : ℂ) < delta := by
      simpa [Complex.dist_eq, abs_of_pos hv] using hvd
    have hlt := hd _ hmem1 _ hmem2 hdist
    simp only [Function.comp_apply, Real.dist_eq, hzero u hu, sub_zero] at hlt
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
  refine measure_Icc_eq_zero_of_eq_nevanlinnaKernel_add hbeta hrep hab
    ((hF.mono hrect).continuousOn) fun u hu ↦ hzero u (lt_of_lt_of_le hapos hu.1)

end TauCeti

end

end
