/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Prokhorov subsequential weak limit for Bernstein's theorem

The tightness/compactness step of the Chafaï proof of Bernstein's theorem. Given a sequence of
finite measures on `ℝ`, uniformly bounded in mass, supported on `[0, ∞)`, and tight, a
subsequence converges weakly to a finite limit `μ₀` supported on `[0, ∞)`
(`finite_measure_subseq_limit`). A bounded-continuous surrogate `exp_bcf` for the Laplace kernel
transfers this weak convergence to the Laplace transforms (`tendsto_exp_integral`).

Ported from the sorry-free `mrdouglasny/hille-yosida` (`HilleYosida.BernsteinChafai`, Prokhorov
part). These facts are about general measures on `ℝ` and do not mention complete monotonicity.

## Main declarations

* `TauCeti.finite_measure_subseq_limit`: subsequential weak limit of a tight, mass-bounded,
  `[0,∞)`-supported sequence.
* `TauCeti.tendsto_exp_integral`: weak convergence of the Laplace integrals `∫ e^{-xp}`.

## References

* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace TauCeti

/-- `↑(normalize μ)(A) ≤ ↑μ(A)` when the mass is at least one. -/
private lemma normalize_le (μ : FiniteMeasure ℝ) (hμ : μ ≠ 0)
    (hm : 1 ≤ μ.mass) (A : Set ℝ) :
    (↑μ.normalize : Measure ℝ) A ≤ (↑μ : Measure ℝ) A := by
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero μ hμ, Measure.smul_apply]
  change (↑(μ.mass⁻¹) : ENNReal) * (↑μ : Measure ℝ) A ≤ (↑μ : Measure ℝ) A
  exact mul_le_of_le_one_left (zero_le)
    (ENNReal.coe_le_coe.mpr (inv_le_one_of_one_le₀ hm))

/-- The bounded continuous function `p ↦ e^{-x·max(p,0)}`, agreeing with `p ↦ e^{-xp}` on
`[0,∞)` and bounded by `1`. Used to transfer weak convergence to the Laplace kernel. -/
private noncomputable def exp_bcf (x : ℝ) (hx : 0 ≤ x) : BoundedContinuousFunction ℝ ℝ where
  toFun p := Real.exp (-(x * max p 0))
  continuous_toFun := by
    apply Continuous.rexp; apply Continuous.neg
    exact continuous_const.mul (continuous_id.max continuous_const)
  map_bounded' := by
    use 2; intro p q
    simp only [dist_eq_norm, Real.norm_eq_abs]
    have h1 : Real.exp (-(x * max p 0)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hx (le_max_right _ _)))
    have h2 : Real.exp (-(x * max q 0)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hx (le_max_right _ _)))
    rw [abs_le]; constructor <;> linarith [Real.exp_pos (-(x * max p 0)),
      Real.exp_pos (-(x * max q 0))]

/-- `exp_bcf x hx p = e^{-xp}` for `p ≥ 0`. -/
private lemma exp_bcf_eq (x : ℝ) (hx : 0 ≤ x) (p : ℝ) (hp : 0 ≤ p) :
    exp_bcf x hx p = Real.exp (-(x * p)) := by
  simp [exp_bcf, max_eq_left hp]

/-- The integral of `exp_bcf` equals the integral of `e^{-xp}` for measures supported on
`[0,∞)`. -/
private lemma integral_exp_bcf_eq {μ : Measure ℝ} (hsupp : μ (Iio 0) = 0)
    (x : ℝ) (hx : 0 ≤ x) :
    ∫ p, exp_bcf x hx p ∂μ = ∫ p, Real.exp (-(x * p)) ∂μ := by
  apply MeasureTheory.integral_congr_ae
  refine ae_iff.mpr (measure_mono_null ?_ hsupp)
  intro p hp
  simp only [Set.mem_setOf_eq, Set.mem_Iio] at *
  by_contra h; rw [not_lt] at h
  exact hp (exp_bcf_eq x hx p h)

/-- **Subsequential weak limit extraction** for finite measures. A sequence `σ` of finite
measures on `ℝ` with uniformly bounded mass, supported on `[0,∞)`, and tight has a subsequence
converging weakly to a finite limit `μ₀` that is finite, supported on `[0,∞)`, and has mass
`≤ C`. -/
lemma finite_measure_subseq_limit
    (σ : ℕ → Measure ℝ) (C : ℝ)
    (hfin : ∀ n, IsFiniteMeasure (σ n))
    (hmass : ∀ n, (σ n) univ ≤ ENNReal.ofReal C)
    (hsupp : ∀ n, (σ n) (Iio 0) = 0)
    (htight : ∀ ε, 0 < ε → ∃ K : ℝ, ∀ n, (σ n) (Ioi K) ≤ ENNReal.ofReal ε) :
    ∃ (μ₀ : Measure ℝ) (φ : ℕ → ℕ), IsFiniteMeasure μ₀ ∧ StrictMono φ ∧
      μ₀ (Iio 0) = 0 ∧ μ₀ univ ≤ ENNReal.ofReal C ∧
      ∀ (g : BoundedContinuousFunction ℝ ℝ), Tendsto (fun k => ∫ p, g p ∂(σ (φ k))) atTop
        (nhds (∫ p, g p ∂μ₀)) := by
  let ν : ℕ → FiniteMeasure ℝ := fun n =>
    ⟨σ n + Measure.dirac (-1), MeasureTheory.isFiniteMeasureAdd⟩
  let π : ℕ → ProbabilityMeasure ℝ := fun n => (ν n).normalize
  have h_mass_ge_one : ∀ n, (1 : NNReal) ≤ (ν n).mass := by
    intro n
    change (1 : NNReal) ≤ ((σ n + Measure.dirac (-1) : Measure ℝ) univ).toNNReal
    rw [Measure.add_apply]
    simp only [Measure.dirac_apply, Set.indicator_apply, Set.mem_univ, Pi.one_apply, ite_true]
    have htop : (σ n) univ + 1 ≠ (⊤ : ENNReal) :=
      ENNReal.add_ne_top.2 ⟨measure_ne_top (σ n) univ, by simp⟩
    have hle : (1 : ENNReal) ≤ (σ n) univ + 1 := by simp [add_comm]
    simpa using ENNReal.toNNReal_mono htop hle
  have h_mass_le : ∀ n, ((ν n).mass : ℝ) ≤ max C 0 + 1 := by
    intro n
    have h1 : (((ν n).mass : ENNReal)).toReal = ((ν n).mass : ℝ) := rfl
    rw [← h1, FiniteMeasure.ennreal_mass]
    change ((σ n + Measure.dirac (-1) : Measure ℝ) univ).toReal ≤ max C 0 + 1
    rw [Measure.add_apply]
    simp only [Measure.dirac_apply, Set.indicator_apply, Set.mem_univ, Pi.one_apply, ite_true]
    rw [ENNReal.toReal_add (measure_ne_top (σ n) univ) ENNReal.one_ne_top, ENNReal.toReal_one]
    exact add_le_add
      (ENNReal.toReal_le_of_le_ofReal (by positivity)
        (le_trans (hmass n) (ENNReal.ofReal_le_ofReal (le_max_left C 0)))) le_rfl
  have h_π_tight :
      IsTightMeasureSet {x : Measure ℝ | ∃ μ ∈ Set.range π, (μ : Measure ℝ) = x} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    by_cases hεtop : ε = (⊤ : ENNReal)
    · exact ⟨∅, isCompact_empty, fun μ hμ => by simp [hεtop]⟩
    · obtain ⟨K, hK⟩ := htight ε.toReal (ENNReal.toReal_pos (ne_of_gt hε) hεtop)
      let K' : ℝ := max K (-1)
      refine ⟨Set.Icc (-1) K', isCompact_Icc, ?_⟩
      intro μ hμ
      rcases hμ with ⟨μ', hμ', rfl⟩
      rcases hμ' with ⟨n, rfl⟩
      have hν_nonzero_mass : (ν n).mass ≠ 0 :=
        ne_of_gt (lt_of_lt_of_le zero_lt_one (h_mass_ge_one n))
      have hν_nonzero : ν n ≠ 0 := (FiniteMeasure.mass_nonzero_iff (ν n)).mp hν_nonzero_mass
      have hneg : ((ν n : FiniteMeasure ℝ) : Measure ℝ) (Iio (-1)) = 0 := by
        change (σ n + Measure.dirac (-1) : Measure ℝ) (Iio (-1)) = 0
        rw [Measure.add_apply]
        have hσ : σ n (Iio (-1)) = 0 := by
          apply le_antisymm _ (zero_le)
          calc σ n (Iio (-1)) ≤ σ n (Iio 0) := by
                refine measure_mono ?_
                intro x hx
                simpa [Set.mem_Iio] using (lt_trans hx (by norm_num : (-1 : ℝ) < 0))
            _ = 0 := hsupp n
        have hδ : (Measure.dirac (-1) : Measure ℝ) (Iio (-1)) = 0 := by simp
        simp [hσ, hδ]
      have htail : ((ν n : FiniteMeasure ℝ) : Measure ℝ) (Ioi K') = σ n (Ioi K') := by
        change (σ n + Measure.dirac (-1) : Measure ℝ) (Ioi K') = σ n (Ioi K')
        rw [Measure.add_apply]
        have hδ : (Measure.dirac (-1) : Measure ℝ) (Ioi K') = 0 := by
          have hnot : (-1 : ℝ) ∉ Ioi K' := not_lt_of_ge (le_max_right K (-1))
          simp [hnot]
        simp [hδ]
      have hsubset : (Set.Icc (-1) K')ᶜ ⊆ Iio (-1) ∪ Ioi K' := by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le, Set.mem_union, Set.mem_Iio,
          Set.mem_Ioi] at hx ⊢
        exact hx
      calc ((π n : ProbabilityMeasure ℝ) : Measure ℝ) (Set.Icc (-1) K')ᶜ
            ≤ ((ν n : FiniteMeasure ℝ) : Measure ℝ) (Set.Icc (-1) K')ᶜ := by
              simpa using normalize_le (ν n) hν_nonzero (h_mass_ge_one n) ((Set.Icc (-1) K')ᶜ)
        _ ≤ ((ν n : FiniteMeasure ℝ) : Measure ℝ) (Iio (-1) ∪ Ioi K') := measure_mono hsubset
        _ ≤ ((ν n : FiniteMeasure ℝ) : Measure ℝ) (Iio (-1)) +
              ((ν n : FiniteMeasure ℝ) : Measure ℝ) (Ioi K') := measure_union_le _ _
        _ = σ n (Ioi K') := by rw [hneg, zero_add, htail]
        _ ≤ σ n (Ioi K) := by
            refine measure_mono ?_
            intro x hx
            exact lt_of_le_of_lt (le_max_left K (-1)) hx
        _ ≤ ENNReal.ofReal ε.toReal := hK n
        _ = ε := by rw [ENNReal.ofReal_toReal hεtop]
  have h_compact : IsCompact (closure (Set.range π)) :=
    isCompact_closure_of_isTightMeasureSet h_π_tight
  have h_seq : IsSeqCompact (closure (Set.range π)) := isCompact_iff_isSeqCompact.mp h_compact
  have hfreq : ∃ᶠ n in atTop, π n ∈ closure (Set.range π) :=
    Filter.Eventually.frequently
      (Filter.Eventually.of_forall (fun n => subset_closure (Set.mem_range_self n)))
  obtain ⟨π₀, -, φ₁, hφ₁, h_tendsto_π⟩ := h_seq.subseq_of_frequently_in hfreq
  let m : ℕ → ℝ := fun k => ((ν (φ₁ k)).mass : ℝ)
  have h_m_mem : ∀ k, m k ∈ Set.Icc 1 (max C 0 + 1) := by
    intro k
    exact ⟨by exact_mod_cast (h_mass_ge_one (φ₁ k)), by simpa [m] using h_mass_le (φ₁ k)⟩
  have hfreq_m : ∃ᶠ k in atTop, m k ∈ Set.Icc 1 (max C 0 + 1) :=
    Filter.Eventually.frequently (Filter.Eventually.of_forall h_m_mem)
  obtain ⟨M, hM_mem, φ₂, hφ₂, hm_tendsto⟩ :=
    isCompact_Icc.isSeqCompact.subseq_of_frequently_in hfreq_m
  let Φ : ℕ → ℕ := φ₁ ∘ φ₂
  have hΦ : StrictMono Φ := StrictMono.comp hφ₁ hφ₂
  have h_tendsto_π_Φ : Tendsto (fun k => π (Φ k)) atTop (nhds π₀) := by
    simpa [Φ, Function.comp_def] using h_tendsto_π.comp (StrictMono.tendsto_atTop hφ₂)
  have hm_tendsto_Φ : Tendsto (fun k => ((ν (Φ k)).mass : ℝ)) atTop (nhds M) := by
    simpa [m, Φ, Function.comp_def] using hm_tendsto
  have hM_nonneg : 0 ≤ M := le_trans zero_le_one hM_mem.1
  let Mnn : NNReal := ⟨M, hM_nonneg⟩
  let ν₀ : FiniteMeasure ℝ := Mnn • π₀.toFiniteMeasure
  let ν₀m : Measure ℝ := (ν₀ : FiniteMeasure ℝ)
  have h_int_bcf : ∀ (g : BoundedContinuousFunction ℝ ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ],
      Integrable g μ := by
    intro g μ _
    apply MeasureTheory.Integrable.mono' (integrable_const ‖g‖)
    · exact g.continuous.aestronglyMeasurable
    · filter_upwards with x; exact g.norm_coe_le_norm x
  have h_int_lim : ∀ (g : BoundedContinuousFunction ℝ ℝ),
      Tendsto (fun k => ∫ p, g p ∂((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ)) atTop
        (nhds (∫ p, g p ∂ν₀m)) := by
    intro g
    have h_π_lim :
        Tendsto (fun k => ∫ p, g p ∂((π (Φ k) : ProbabilityMeasure ℝ) : Measure ℝ)) atTop
          (nhds (∫ p, g p ∂((π₀ : ProbabilityMeasure ℝ) : Measure ℝ))) :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h_tendsto_π_Φ) g
    have h_prod := Tendsto.mul hm_tendsto_Φ h_π_lim
    have h_eq : ∀ k, ((ν (Φ k)).mass : ℝ) *
            ∫ p, g p ∂((π (Φ k) : ProbabilityMeasure ℝ) : Measure ℝ) =
            ∫ p, g p ∂((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) := by
      intro k
      have hν_nonzero_mass : (ν (Φ k)).mass ≠ 0 :=
        ne_of_gt (lt_of_lt_of_le zero_lt_one (h_mass_ge_one (Φ k)))
      have hν_nonzero : ν (Φ k) ≠ 0 :=
        (FiniteMeasure.mass_nonzero_iff (ν (Φ k))).mp hν_nonzero_mass
      have h1 : ∫ p, g p ∂((π (Φ k) : ProbabilityMeasure ℝ) : Measure ℝ) =
            ((ν (Φ k)).mass : ℝ)⁻¹ *
              ∫ p, g p ∂((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) := by
        rw [show π (Φ k) = (ν (Φ k)).normalize from rfl]
        rw [(ν (Φ k)).toMeasure_normalize_eq_of_nonzero hν_nonzero]
        change ∫ p, g p ∂((((ν (Φ k)).mass⁻¹ : NNReal) : ENNReal) •
            ((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ)) = _
        rw [MeasureTheory.integral_smul_measure g ((((ν (Φ k)).mass⁻¹ : NNReal) : ENNReal))]
        simp [smul_eq_mul]
      rw [h1]
      have hmass_ne : ((ν (Φ k)).mass : ℝ) ≠ 0 := by exact_mod_cast hν_nonzero_mass
      field_simp [hmass_ne]
    simp_rw [h_eq] at h_prod
    have hν₀_eq : (M : ℝ) * ∫ p, g p ∂((π₀ : ProbabilityMeasure ℝ) : Measure ℝ) =
          ∫ p, g p ∂ν₀m := by
      change (Mnn : ℝ) * ∫ p, g p ∂((π₀ : ProbabilityMeasure ℝ) : Measure ℝ) =
        ∫ p, g p ∂((ν₀ : FiniteMeasure ℝ) : Measure ℝ)
      change (Mnn : ℝ) * ∫ p, g p ∂((π₀ : ProbabilityMeasure ℝ) : Measure ℝ) =
        ∫ p, g p ∂(((Mnn : ENNReal)) • ((π₀ : ProbabilityMeasure ℝ) : Measure ℝ))
      rw [MeasureTheory.integral_smul_measure g ((Mnn : ENNReal))]
      simp [smul_eq_mul]
    exact hν₀_eq ▸ h_prod
  let χ : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun x => max 0 (min 1 (x + 1)), by fun_prop⟩ 1
      (by
        intro x y
        set fx : ℝ := max 0 (min 1 (x + 1))
        set fy : ℝ := max 0 (min 1 (y + 1))
        have hx0 : 0 ≤ fx := by simp [fx]
        have hy0 : 0 ≤ fy := by simp [fy]
        have hx1 : fx ≤ 1 := by simp [fx, zero_le_one]
        have hy1 : fy ≤ 1 := by simp [fy, zero_le_one]
        change |fx - fy| ≤ 1
        rw [abs_le]; constructor <;> linarith)
  let f_cut : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun x => max 0 (min (x + 1) (-x)), by fun_prop⟩ 1
      (by
        intro x y
        set fx : ℝ := max 0 (min (x + 1) (-x))
        set fy : ℝ := max 0 (min (y + 1) (-y))
        have hx0 : 0 ≤ fx := by simp [fx]
        have hy0 : 0 ≤ fy := by simp [fy]
        have hx1 : fx ≤ 1 := by
          have hmin : min (x + 1) (-x) ≤ 1 := by
            by_cases hx : x ≤ 0
            · exact le_trans (min_le_left _ _) (by linarith)
            · exact le_trans (min_le_right _ _) (by linarith)
          simp [fx, hmin, zero_le_one]
        have hy1 : fy ≤ 1 := by
          have hmin : min (y + 1) (-y) ≤ 1 := by
            by_cases hy : y ≤ 0
            · exact le_trans (min_le_left _ _) (by linarith)
            · exact le_trans (min_le_right _ _) (by linarith)
          simp [fy, hmin, zero_le_one]
        change |fx - fy| ≤ 1
        rw [abs_le]; constructor <;> linarith)
  let h_cut : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun x => max 0 (min 1 (-x - 1)), by fun_prop⟩ 1
      (by
        intro x y
        set fx : ℝ := max 0 (min 1 (-x - 1))
        set fy : ℝ := max 0 (min 1 (-y - 1))
        have hx0 : 0 ≤ fx := by simp [fx]
        have hy0 : 0 ≤ fy := by simp [fy]
        have hx1 : fx ≤ 1 := by simp [fx, zero_le_one]
        have hy1 : fy ≤ 1 := by simp [fy, zero_le_one]
        change |fx - fy| ≤ 1
        rw [abs_le]; constructor <;> linarith)
  have hχ_nonneg : ∀ x, 0 ≤ χ x := fun x => le_max_left _ _
  have hχ_eq_one : ∀ x, 0 ≤ x → χ x = 1 := by
    intro x hx
    change max 0 (min 1 (x + 1)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  have hχ_neg1 : χ (-1) = 0 := by
    change max 0 (min 1 ((-1 : ℝ) + 1)) = 0
    norm_num
  have hf_cut_zero_of_nonneg : ∀ x, 0 ≤ x → f_cut x = 0 := by
    intro x hx
    change max 0 (min (x + 1) (-x)) = 0
    exact max_eq_left (le_trans (min_le_right _ _) (by linarith))
  have hh_cut_zero_of_nonneg : ∀ x, 0 ≤ x → h_cut x = 0 := by
    intro x hx
    change max 0 (min 1 (-x - 1)) = 0
    exact max_eq_left (le_trans (min_le_right _ _) (by linarith))
  have hν_f_zero : ∀ k, ∫ p, f_cut p ∂((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) = 0 := by
    intro k
    rw [show ((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) = σ (Φ k) + Measure.dirac (-1) from rfl]
    rw [MeasureTheory.integral_add_measure (h_int_bcf f_cut (σ (Φ k)))
      (h_int_bcf f_cut (Measure.dirac (-1)))]
    have hσ : ∫ p, f_cut p ∂(σ (Φ k)) = 0 := by
      apply MeasureTheory.integral_eq_zero_of_ae
      refine ae_iff.mpr (measure_mono_null ?_ (hsupp (Φ k)))
      intro p hp
      simp only [Set.mem_setOf_eq, Set.mem_Iio] at hp ⊢
      by_contra hpneg
      exact hp (hf_cut_zero_of_nonneg p (le_of_not_gt hpneg))
    have hδ : ∫ p, f_cut p ∂(Measure.dirac (-1)) = 0 := by
      rw [MeasureTheory.integral_dirac]
      change max 0 (min (((-1 : ℝ) + 1)) (-(-1 : ℝ))) = 0
      norm_num
    simp [hσ, hδ]
  have hν_h_zero : ∀ k, ∫ p, h_cut p ∂((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) = 0 := by
    intro k
    rw [show ((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) = σ (Φ k) + Measure.dirac (-1) from rfl]
    rw [MeasureTheory.integral_add_measure (h_int_bcf h_cut (σ (Φ k)))
      (h_int_bcf h_cut (Measure.dirac (-1)))]
    have hσ : ∫ p, h_cut p ∂(σ (Φ k)) = 0 := by
      apply MeasureTheory.integral_eq_zero_of_ae
      refine ae_iff.mpr (measure_mono_null ?_ (hsupp (Φ k)))
      intro p hp
      simp only [Set.mem_setOf_eq, Set.mem_Iio] at hp ⊢
      by_contra hpneg
      exact hp (hh_cut_zero_of_nonneg p (le_of_not_gt hpneg))
    have hδ : ∫ p, h_cut p ∂(Measure.dirac (-1)) = 0 := by
      rw [MeasureTheory.integral_dirac]
      change max 0 (min 1 (-(-1 : ℝ) - 1)) = 0
      norm_num
    simp [hσ, hδ]
  have hν₀_ae_zero_f : f_cut =ᵐ[ν₀m] 0 := by
    have hlim := h_int_lim f_cut
    simp_rw [hν_f_zero] at hlim
    have hint0 : ∫ p, f_cut p ∂ν₀m = 0 := tendsto_nhds_unique hlim tendsto_const_nhds
    exact (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun p => by
      change 0 ≤ max 0 (min (p + 1) (-p)); exact le_max_left _ _))
      (h_int_bcf f_cut ν₀m)).mp hint0
  have hν₀_ae_zero_h : h_cut =ᵐ[ν₀m] 0 := by
    have hlim := h_int_lim h_cut
    simp_rw [hν_h_zero] at hlim
    have hint0 : ∫ p, h_cut p ∂ν₀m = 0 := tendsto_nhds_unique hlim tendsto_const_nhds
    exact (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun p => by
      change 0 ≤ max 0 (min 1 (-p - 1)); exact le_max_left _ _))
      (h_int_bcf h_cut ν₀m)).mp hint0
  let μ₀ : Measure ℝ := ν₀m.restrict (Ici 0)
  haveI hν₀m_fin : IsFiniteMeasure ν₀m := by
    dsimp [ν₀m, ν₀]
    exact Measure.smul_finite (π₀ : Measure ℝ) (by simp)
  haveI hμ₀_fin : IsFiniteMeasure μ₀ :=
    (MeasureTheory.isFiniteMeasure_restrict).2 (measure_ne_top ν₀m (Ici 0))
  have hχ_neg_ae : χ =ᵐ[ν₀m.restrict (Iio 0)] 0 := by
    change ∀ᵐ p ∂(ν₀m.restrict (Iio 0)), χ p = 0
    rw [ae_restrict_iff' measurableSet_Iio]
    filter_upwards [hν₀_ae_zero_f, hν₀_ae_zero_h] with p hp_f hp_h hp_neg
    by_cases hp_eq : p = -1
    · rw [hp_eq]; exact hχ_neg1
    · by_cases hp_gt : -1 < p
      · exfalso
        have hpos : 0 < f_cut p := by
          change 0 < max 0 (min (p + 1) (-p))
          have hmin : 0 < min (p + 1) (-p) := by
            refine lt_min ?_ ?_
            · linarith
            · simpa [Set.mem_Iio] using hp_neg
          exact lt_max_of_lt_right hmin
        have hp_f0 : f_cut p = 0 := by simpa using hp_f
        simp [hp_f0] at hpos
      · exfalso
        have hp_le : p ≤ -1 := le_of_not_gt hp_gt
        have hp_lt : p < -1 := lt_of_le_of_ne hp_le hp_eq
        have hpos : 0 < h_cut p := by
          change 0 < max 0 (min 1 (-p - 1))
          have hmin : 0 < min 1 (-p - 1) := by
            apply lt_min
            · norm_num
            · linarith [hp_lt]
          exact lt_max_of_lt_right hmin
        have hp_h0 : h_cut p = 0 := by simpa using hp_h
        simp [hp_h0] at hpos
  refine ⟨μ₀, Φ, hμ₀_fin, hΦ, ?_, ?_, ?_⟩
  · rw [show μ₀ = ν₀m.restrict (Ici 0) from rfl, Measure.restrict_apply measurableSet_Iio]
    have : Iio 0 ∩ Ici 0 = (∅ : Set ℝ) := by ext x; simp
    rw [this, measure_empty]
  · have hχ_seq : Tendsto (fun k => ∫ p, χ p ∂((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ)) atTop
          (nhds (∫ p, χ p ∂ν₀m)) := h_int_lim χ
    have hχ_sigma : ∀ k, ∫ p, χ p ∂((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) =
        ((σ (Φ k)) univ).toReal := by
      intro k
      rw [show ((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) = σ (Φ k) + Measure.dirac (-1) from rfl]
      rw [MeasureTheory.integral_add_measure (h_int_bcf χ (σ (Φ k)))
        (h_int_bcf χ (Measure.dirac (-1)))]
      have hσ : ∫ p, χ p ∂(σ (Φ k)) = ((σ (Φ k)) univ).toReal := by
        have hEq : χ =ᵐ[σ (Φ k)] fun _ => (1 : ℝ) := by
          refine ae_iff.mpr (measure_mono_null ?_ (hsupp (Φ k)))
          intro p hp
          simp only [Set.mem_setOf_eq, Set.mem_Iio] at hp ⊢
          by_contra hpneg
          exact hp (hχ_eq_one p (le_of_not_gt hpneg))
        rw [MeasureTheory.integral_congr_ae hEq, MeasureTheory.integral_const]
        simp [Measure.real]
      have hδ : ∫ p, χ p ∂(Measure.dirac (-1)) = 0 := by
        rw [MeasureTheory.integral_dirac]; exact hχ_neg1
      simp [hσ, hδ]
    simp_rw [hχ_sigma] at hχ_seq
    have hχ_ν₀ : ∫ p, χ p ∂ν₀m = (μ₀ univ).toReal := by
      have hsplit := MeasureTheory.setIntegral_union (Set.disjoint_left.mpr (by
        intro x hx1 hx2; exact (not_lt_of_ge hx1) (by simpa [Set.mem_Iio] using hx2)))
        measurableSet_Iio
        (h_int_bcf χ (ν₀m.restrict (Ici 0))) (h_int_bcf χ (ν₀m.restrict (Iio 0)))
      have hunion : Ici (0 : ℝ) ∪ Iio 0 = univ := by ext x; simp
      have hsplit' : ∫ p, χ p ∂ν₀m =
          ∫ p in Ici 0, χ p ∂ν₀m + ∫ p in Iio 0, χ p ∂ν₀m := by
        calc ∫ p, χ p ∂ν₀m = ∫ p in univ, χ p ∂ν₀m := (MeasureTheory.setIntegral_univ).symm
          _ = ∫ p in Ici 0 ∪ Iio 0, χ p ∂ν₀m := by rw [hunion]
          _ = ∫ p in Ici 0, χ p ∂ν₀m + ∫ p in Iio 0, χ p ∂ν₀m := hsplit
      have hIio : ∫ p in Iio 0, χ p ∂ν₀m = 0 := by
        simpa using MeasureTheory.integral_eq_zero_of_ae hχ_neg_ae
      have hIci : ∫ p in Ici 0, χ p ∂ν₀m = (μ₀ univ).toReal := by
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun p hp => hχ_eq_one p hp)]
        change ∫ p, (1 : ℝ) ∂μ₀ = _
        rw [MeasureTheory.integral_const]; simp [Measure.real]
      rw [hIio, add_zero] at hsplit'
      exact hsplit'.trans hIci
    rw [hχ_ν₀] at hχ_seq
    have hle_real : ∀ k, ((σ (Φ k)) univ).toReal ≤ max C 0 := fun k =>
      ENNReal.toReal_le_of_le_ofReal (by positivity)
        (le_trans (hmass (Φ k)) (ENNReal.ofReal_le_ofReal (le_max_left C 0)))
    have hlimit : (μ₀ univ).toReal ≤ max C 0 :=
      le_of_tendsto hχ_seq (Filter.Eventually.of_forall hle_real)
    have htop : μ₀ univ ≠ (⊤ : ENNReal) := measure_ne_top μ₀ univ
    rw [← ENNReal.ofReal_toReal htop]
    refine le_trans (ENNReal.ofReal_le_ofReal hlimit) ?_
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero]
    exact max_le_iff.mpr ⟨le_rfl, zero_le⟩
  · intro g
    let gχ : BoundedContinuousFunction ℝ ℝ := g * χ
    have hσ_eq : ∀ k, ∫ p, g p ∂(σ (Φ k)) =
          ∫ p, gχ p ∂((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) := by
      intro k
      rw [show ((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) = σ (Φ k) + Measure.dirac (-1) from rfl]
      rw [MeasureTheory.integral_add_measure (h_int_bcf gχ (σ (Φ k)))
        (h_int_bcf gχ (Measure.dirac (-1)))]
      have hσ : ∫ p, gχ p ∂(σ (Φ k)) = ∫ p, g p ∂(σ (Φ k)) := by
        apply MeasureTheory.integral_congr_ae
        refine ae_iff.mpr (measure_mono_null ?_ (hsupp (Φ k)))
        intro p hp
        simp only [Set.mem_setOf_eq, Set.mem_Iio] at hp ⊢
        by_contra hpneg
        apply hp
        change g p * χ p = g p
        rw [hχ_eq_one p (le_of_not_gt hpneg), mul_one]
      have hδ : ∫ p, gχ p ∂(Measure.dirac (-1)) = 0 := by
        rw [MeasureTheory.integral_dirac]
        change g (-1) * χ (-1) = 0
        rw [hχ_neg1, mul_zero]
      rw [hσ, hδ]; simp
    have hlim := h_int_lim gχ
    simp_rw [← hσ_eq] at hlim
    have hν₀_eq : ∫ p, gχ p ∂ν₀m = ∫ p, g p ∂μ₀ := by
      have hsplit := MeasureTheory.setIntegral_union (Set.disjoint_left.mpr (by
        intro x hx1 hx2; exact (not_lt_of_ge hx1) (by simpa [Set.mem_Iio] using hx2)))
        measurableSet_Iio
        (h_int_bcf gχ (ν₀m.restrict (Ici 0))) (h_int_bcf gχ (ν₀m.restrict (Iio 0)))
      have hunion : Ici (0 : ℝ) ∪ Iio 0 = univ := by ext x; simp
      have hsplit' : ∫ p, gχ p ∂ν₀m =
          ∫ p in Ici 0, gχ p ∂ν₀m + ∫ p in Iio 0, gχ p ∂ν₀m := by
        calc ∫ p, gχ p ∂ν₀m = ∫ p in univ, gχ p ∂ν₀m := (MeasureTheory.setIntegral_univ).symm
          _ = ∫ p in Ici 0 ∪ Iio 0, gχ p ∂ν₀m := by rw [hunion]
          _ = ∫ p in Ici 0, gχ p ∂ν₀m + ∫ p in Iio 0, gχ p ∂ν₀m := hsplit
      have hIio : ∫ p in Iio 0, gχ p ∂ν₀m = 0 := by
        have hEq : gχ =ᵐ[ν₀m.restrict (Iio 0)] 0 := by
          filter_upwards [hχ_neg_ae] with p hp
          change g p * χ p = 0
          rw [show χ p = 0 from by simpa using hp, mul_zero]
        simpa using MeasureTheory.integral_eq_zero_of_ae hEq
      have hIci : ∫ p in Ici 0, gχ p ∂ν₀m = ∫ p, g p ∂μ₀ := by
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ici (by
          intro p hp; change g p * χ p = g p; rw [hχ_eq_one p hp, mul_one])]
      rw [hIio, add_zero] at hsplit'
      exact hsplit'.trans hIci
    rw [hν₀_eq] at hlim
    exact hlim

/-- Weak convergence of `∫ e^{-xp}` along the subsequence, via the bounded-continuous surrogate
`exp_bcf`, for measures supported on `[0,∞)`. -/
lemma tendsto_exp_integral
    (σ : ℕ → Measure ℝ) (φ : ℕ → ℕ) (μ₀ : Measure ℝ)
    (hweak : ∀ (g : BoundedContinuousFunction ℝ ℝ),
      Tendsto (fun k => ∫ p, g p ∂(σ (φ k))) atTop (nhds (∫ p, g p ∂μ₀)))
    (hsupp_σ : ∀ n, (σ n) (Iio 0) = 0) (hsupp_μ : μ₀ (Iio 0) = 0)
    (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun k => ∫ p, Real.exp (-(x * p)) ∂(σ (φ k))) atTop
      (nhds (∫ p, Real.exp (-(x * p)) ∂μ₀)) := by
  have h1 : ∀ k, ∫ p, Real.exp (-(x * p)) ∂(σ (φ k)) = ∫ p, exp_bcf x hx p ∂(σ (φ k)) :=
    fun k => (integral_exp_bcf_eq (hsupp_σ (φ k)) x hx).symm
  have h2 : ∫ p, Real.exp (-(x * p)) ∂μ₀ = ∫ p, exp_bcf x hx p ∂μ₀ :=
    (integral_exp_bcf_eq hsupp_μ x hx).symm
  rw [h2]; exact (hweak (exp_bcf x hx)).congr (fun k => (h1 k).symm)

end TauCeti
