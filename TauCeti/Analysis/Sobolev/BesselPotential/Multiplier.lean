/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Basic
public import TauCeti.Analysis.Distribution.Sobolev
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Analysis.Sobolev.Wkp.Density
import TauCeti.MeasureTheory.Function.Lp.CastMeasure

/-!
# Nondecaying `Cᵏ` multipliers on integer-order Bessel-potential spaces

A `Cᵏ` real coefficient with bounded derivatives through order `k` preserves `H^{k,p}`
for `1 < p < ∞`. In contrast to multiplication by a test function, the coefficient need not
vanish at infinity. This is needed when a differential equation is expanded about a finite-order
background which is not itself integrable.

The result uses test-function density `W^{k,p}_0 = W^{k,p}` on `E`, the classical Leibniz estimate
on `Cᵏ` products with test functions, and the weak-derivative/Bessel-potential comparison. It
provides an actual `Lᵖ` representative of the product, not merely a distributional existence
statement. Only `Cᵏ` regularity and bounds on derivatives through the specified integer order are
required. No bound in the Bessel-potential norm, or statement for noninteger orders, is asserted
here.

## References

* L. C. Evans, *Partial Differential Equations*, §5.2.3 and §5.3.2.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V, §3.
-/

public section

namespace TemperedDistribution

open Filter MeasureTheory Set TauCeti TopologicalSpace
open scoped ContDiff Distributions Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

/-- Pointwise multiplication of a compactly supported test function by a `C^k` function `ψ`
represents an element of `W^{k,p}(⊤)` with norm controlled by `‖ofTestFunctionₗ k φ‖` and a
bound on the derivatives of `ψ` through order `k`. -/
private theorem exists_wkp_mul_testFunction {p : ENNReal} [Fact (1 ≤ p)] (k : ℕ)
    {ψ : E → ℝ} (hψ : ContDiff ℝ k ψ) {M : ℝ}
    (hbound : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j ψ x‖ ≤ M) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    ∃ u : Wkp (volume : Measure E) (⊤ : Opens E) p k,
      (Wkp.value k u : E → ℝ) =ᵐ[(volume : Measure E).restrict (⊤ : Opens E)]
        (fun x ↦ ψ x * φ x) ∧
      ‖u‖ ≤ (∑ i ∈ Finset.range (k + 1), (2 : ℝ) ^ i) * M *
        ‖Wkp.ofTestFunctionₗ (mu := (volume : Measure E)) (p := p) k φ‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound 0 (Nat.zero_le k) 0)
  have hprod : ContDiff ℝ k (fun x ↦ ψ x * φ x) := hψ.mul (φ.contDiff.of_le (by simp))
  have hsupp : HasCompactSupport (fun x ↦ ψ x * φ x) := φ.hasCompactSupport.mul_left
  have hmem (i : ℕ) (hi : i ≤ k) :
      MemLp (iteratedFDeriv ℝ i (fun x ↦ ψ x * φ x)) p
        ((volume : Measure E).restrict (⊤ : Opens E)) := by
    have hcont : Continuous (iteratedFDeriv ℝ i (fun x ↦ ψ x * φ x)) :=
      hprod.continuous_iteratedFDeriv (by exact_mod_cast hi)
    have hcs : HasCompactSupport (iteratedFDeriv ℝ i (fun x ↦ ψ x * φ x)) := by
      refine HasCompactSupport.of_support_subset_isCompact hsupp.isCompact fun x hx ↦ ?_
      by_contra hxn
      have hev : (fun y ↦ ψ y * φ y) =ᶠ[nhds x] 0 := by
        filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hxn] with y hy
        simp [image_eq_zero_of_notMem_tsupport hy]
      exact hx (by rw [hev.iteratedFDeriv ℝ i |>.eq_of_nhds]; simp)
    exact (hcont.memLp_of_hasCompactSupport hcs).restrict _
  obtain ⟨u, hu⟩ := Wkp.exists_value_ae_eq_of_contDiffOn k hprod.contDiffOn hmem
  refine ⟨u, hu, ?_⟩
  refine (Wkp.norm_le_sum_lpNorm_iteratedFDeriv_of_contDiffOn k u hprod.contDiffOn hu).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hof :
      (Wkp.value k (Wkp.ofTestFunctionₗ (mu := volume) (p := p) k φ) : E → ℝ) =ᵐ[volume.restrict ⊤]
        (φ : E → ℝ) := by
    rw [Wkp.value_ofTestFunctionₗ]
    exact testFunctionLp_apply_ae p φ
  have hmemφ := Wkp.memLp_iteratedFDeriv_of_contDiffOn k
    (Wkp.ofTestFunctionₗ (mu := volume) (p := p) k φ) (φ.contDiff.of_le (by simp)).contDiffOn hof
  let a (j : ℕ) : ℝ := (i.choose j : ℝ) * M
  let b (j : ℕ) : E → ℝ := fun x ↦ a j * ‖iteratedFDeriv ℝ (i - j) (φ : E → ℝ) x‖
  have hbmem (j : ℕ) : MemLp (b j) p ((volume : Measure E).restrict (⊤ : Opens E)) :=
    (hmemφ (i - j) ((Nat.sub_le _ _).trans hik)).norm.const_mul (a j)
  have hle : eLpNorm (iteratedFDeriv ℝ i (fun x ↦ ψ x * φ x)) p (volume.restrict (⊤ : Opens E)) ≤
      eLpNorm (∑ j ∈ Finset.range (i + 1), b j) p (volume.restrict (⊤ : Opens E)) := by
    refine eLpNorm_mono_ae
      ((hprod.continuous_iteratedFDeriv (by exact_mod_cast hik)).aestronglyMeasurable)
      (.of_forall fun x ↦ ?_)
    refine (norm_iteratedFDeriv_mul_le hψ (φ.contDiff.of_le (by simp)) x
      (by exact_mod_cast hik)).trans ?_
    simp only [Finset.sum_apply, Real.norm_eq_abs]
    refine (Finset.sum_le_sum fun j hj ↦ ?_).trans (le_abs_self _)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (hbound j ((Nat.le_of_lt_succ (Finset.mem_range.1 hj)).trans hik) x)
        (Nat.cast_nonneg _)) (norm_nonneg _)
  have hsum := memLp_finsetSum' (Finset.range (i + 1)) fun j _ ↦ hbmem j
  have hreal := ENNReal.toReal_mono hsum.eLpNorm_ne_top hle
  calc lpNorm (iteratedFDeriv ℝ i (fun x ↦ ψ x * φ x)) p (volume.restrict (⊤ : Opens E))
      ≤ lpNorm (∑ j ∈ Finset.range (i + 1), b j) p (volume.restrict (⊤ : Opens E)) := by
        simpa only [toReal_eLpNorm] using hreal
    _ ≤ ∑ j ∈ Finset.range (i + 1), lpNorm (b j) p (volume.restrict (⊤ : Opens E)) :=
        lpNorm_sum_le (fun j _ ↦ hbmem j) Fact.out
    _ = ∑ j ∈ Finset.range (i + 1), a j *
          lpNorm (iteratedFDeriv ℝ (i - j) (φ : E → ℝ)) p (volume.restrict (⊤ : Opens E)) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        have hbj : b j = a j • fun x ↦ ‖iteratedFDeriv ℝ (i - j) (φ : E → ℝ) x‖ := by
          ext x
          simp [b, smul_eq_mul]
        rw [hbj, lpNorm_const_smul,
          lpNorm_norm (hmemφ (i - j) ((Nat.sub_le _ _).trans hik)).aestronglyMeasurable,
          Real.nnNorm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hM)]
        rfl
    _ ≤ ∑ j ∈ Finset.range (i + 1),
          a j * ‖Wkp.ofTestFunctionₗ (mu := volume) (p := p) k φ‖ := by
        gcongr with j _
        exact Wkp.lpNorm_iteratedFDeriv_le_of_contDiffOn k _
          (φ.contDiff.of_le (by simp)).contDiffOn hof (i - j) ((Nat.sub_le _ _).trans hik)
    _ = 2 ^ i * M * ‖Wkp.ofTestFunctionₗ (mu := volume) (p := p) k φ‖ := by
        simp only [a, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring

/-- A `Cᵏ` real coefficient whose derivatives through order `k` are bounded preserves
integer-order `H^{k,p}`. The product has a real `Lᵖ` representative with the asserted Sobolev
regularity. The coefficient need not decay or be integrable. -/
theorem exists_mem_realSobolevSubmodule_ae_eq_mul_of_bounded_derivatives
    {p : ENNReal} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ)
    {ψ : E → ℝ} (hψ : ContDiff ℝ k ψ) {M : ℝ}
    (hbound : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j ψ x‖ ≤ M)
    {u : Lp ℝ p (volume : Measure E)} (hu : u ∈ realSobolevSubmodule E k p) :
    ∃ v : Lp ℝ p (volume : Measure E), v ∈ realSobolevSubmodule E k p ∧
      (v : E → ℝ) =ᵐ[volume] fun x ↦ ψ x * u x := by
  obtain ⟨w, hw⟩ := (Lp.memSobolev_natCast_iff_exists_wkp_value_eq hp hp_top k u).mp
    (mem_realSobolevSubmodule.mp hu)
  have hvolume : (volume : Measure E).restrict (⊤ : Opens E) = volume := by simp
  obtain ⟨vseq, hvseq, hlim⟩ := mem_closure_iff_seq_limit.1
    (Wkp.denseRange_ofTestFunctionₗ_top (mu := volume) (p := p) hp_top k w)
  choose φ hφ using hvseq
  have hφ_lim : Tendsto (fun n ↦ Wkp.ofTestFunctionₗ (mu := volume) (p := p) k (φ n))
      atTop (𝓝 w) := by
    simpa only [hφ] using hlim
  choose mulTest hmul_ae hmul_norm using fun δ ↦ exists_wkp_mul_testFunction (p := p) k hψ hbound δ
  set C : ℝ := (∑ i ∈ Finset.range (k + 1), (2 : ℝ) ^ i) * M
  have hsub (n m : ℕ) : mulTest (φ n) - mulTest (φ m) = mulTest (φ n - φ m) := by
    refine Wkp.ext k (Lp.ext ?_)
    rw [← Wkp.valueL_apply, map_sub, Wkp.valueL_apply, Wkp.valueL_apply]
    filter_upwards [Lp.coeFn_sub (Wkp.value k (mulTest (φ n))) (Wkp.value k (mulTest (φ m))),
      hmul_ae (φ n), hmul_ae (φ m), hmul_ae (φ n - φ m)] with x h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3, h4]
    simp [mul_sub]
  have hcauchy : CauchySeq (fun n ↦ mulTest (φ n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hC0 : 0 ≤ C := mul_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity)
      ((norm_nonneg _).trans (hbound 0 (Nat.zero_le k) 0))
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hφ_lim.cauchySeq (ε / (C + 1)) (by positivity)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    rw [dist_eq_norm, hsub]
    refine (hmul_norm (φ m - φ n)).trans_lt ?_
    rw [map_sub, ← dist_eq_norm]
    calc C * dist (Wkp.ofTestFunctionₗ (mu := volume) (p := p) k (φ m))
          (Wkp.ofTestFunctionₗ (mu := volume) (p := p) k (φ n))
        ≤ (C + 1) * dist (Wkp.ofTestFunctionₗ (mu := volume) (p := p) k (φ m))
          (Wkp.ofTestFunctionₗ (mu := volume) (p := p) k (φ n)) :=
          mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
      _ < (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_left (hN m hm n hn) (by positivity)
      _ = ε := mul_div_cancel₀ ε (by positivity)
  obtain ⟨w', hw'⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hinput := (Wkp.valueL (mu := volume) (p := p) k).continuous.tendsto w |>.comp hφ_lim
  have houtput := (Wkp.valueL (mu := volume) (p := p) k).continuous.tendsto w' |>.comp hw'
  obtain ⟨ns, hns, hin⟩ := (tendstoInMeasure_of_tendsto_Lp hinput).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hout⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (houtput.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hterm : ∀ᵐ x ∂volume.restrict (⊤ : Opens E), ∀ j,
      Wkp.value k (mulTest (φ j)) x =
        ψ x * Wkp.value k (Wkp.ofTestFunctionₗ (mu := volume) (p := p) k (φ j)) x := by
    rw [ae_all_iff]
    intro j
    filter_upwards [hmul_ae (φ j), Wkp.value_ofTestFunctionₗ (mu := volume) (p := p) k (φ j) ▸
      testFunctionLp_apply_ae (mu := volume) p (φ j)] with x h1 h2
    rw [h1, h2]
  have hw'_ae : (Wkp.value k w' : E → ℝ) =ᵐ[volume.restrict (⊤ : Opens E)]
      fun x ↦ ψ x * Wkp.value k w x := by
    filter_upwards [hin, hout, hterm] with x hx hy ht
    have hprod := (tendsto_const_nhds (x := ψ x)).mul (hx.comp hms.tendsto_atTop)
    have hprod' : Tendsto (fun j ↦ Wkp.value k (mulTest (φ (ns (ms j)))) x) atTop
        (𝓝 (ψ x * Wkp.value k w x)) := by
      simpa only [Function.comp_def, Wkp.valueL_apply, ht] using hprod
    exact tendsto_nhds_unique (by simpa only [Function.comp_def, Wkp.valueL_apply] using hy) hprod'
  let v : Lp ℝ p (volume : Measure E) := castLpₗᵢ (𝕜 := ℝ) hvolume (Wkp.value k w')
  have hvval (x : E) : v x = Wkp.value k w' x := coeFn_castLpₗᵢ hvolume _ x
  refine ⟨v, mem_realSobolevSubmodule.mpr ?_, ?_⟩
  · exact (Lp.memSobolev_natCast_iff_exists_wkp_value_eq hp hp_top k v).mpr
      ⟨w', Eventually.of_forall fun x ↦ (hvval x).symm⟩
  · have h1 := (ae_restrict_iff' (⊤ : Opens E).isOpen.measurableSet).mp hw'_ae
    filter_upwards [h1, hw] with x hx1 hx2
    rw [hvval x, hx1 (mem_univ x), hx2]

/-- A `Cᵏ` real coefficient whose derivatives through order `k` are bounded preserves the
pointwise representatives of real integer-order `H^{k,p}` functions. The bound on each
derivative may depend on its order. -/
theorem mul_mem_realSobolevFunctions_of_bounded_derivatives
    {p : ENNReal} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ)
    {ψ : E → ℝ} (hψ : ContDiff ℝ k ψ)
    (hbound : ∀ j ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ j ψ x‖ ≤ C)
    {f : E → ℝ} (hf : f ∈ realSobolevFunctions E k p) :
    (fun x ↦ ψ x * f x) ∈ realSobolevFunctions E k p := by
  -- Combine the bounds of the finitely many orders `j ≤ k` into one.
  choose! C hC using fun j (hj : j ∈ Finset.range (k + 1)) ↦
    hbound j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  have hM : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j ψ x‖ ≤ ∑ i ∈ Finset.range (k + 1), |C i| :=
    fun j hj x ↦ (hC j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) x).trans <|
      (le_abs_self _).trans <| Finset.single_le_sum (fun i _ ↦ abs_nonneg (C i))
        (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  obtain ⟨u, huf, hu⟩ := mem_realSobolevFunctions.1 hf
  obtain ⟨v, hv, hvu⟩ := exists_mem_realSobolevSubmodule_ae_eq_mul_of_bounded_derivatives hp
    hp_top k hψ hM
    (mem_realSobolevSubmodule.2 hu)
  refine mem_realSobolevFunctions_of_ae_eq (coeFn_mem_realSobolevFunctions hv) ?_
  filter_upwards [hvu, huf] with x hx hux
  rw [hx, hux]

end TemperedDistribution
