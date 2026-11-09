/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.BetaGas.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.PairwiseProd
import TauCeti.Analysis.SpecialFunctions.Gaussian.Integrable

import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Normalizability of the finite beta gas

For continuous potentials with sufficiently strong logarithmic growth, the finite beta-gas weight
has a finite, strictly positive integral. This normalizes the general beta-gas density and measure.
The Gaussian results are recovered as a specialization.
-/

public section
noncomputable section

open MeasureTheory Real Set

namespace TauCeti.Probability

private lemma betaGasVandermonde_le_coord_prod (n : ℕ) {β : ℝ} (hβ : 0 ≤ β)
    (x : Fin n → ℝ) :
    (∏ z ∈ betaGasPairs n, |x z.1 - x z.2| ^ β) ≤
      ∏ i : Fin n, (1 + |x i|) ^ (β * ((n - 1 : ℕ) : ℝ)) := by
  classical
  let f : Fin n → ℝ := fun i => 1 + |x i|
  have hdiff (i j : Fin n) : |x i - x j| ≤ f i * f j := by
    dsimp [f]
    have h := abs_sub_le (x i) 0 (x j)
    simp only [sub_zero, zero_sub, abs_neg] at h
    nlinarith [abs_nonneg (x i), abs_nonneg (x j)]
  have hfst :
      (∏ z ∈ betaGasPairs n, f z.1 ^ β) =
        ∏ i : Fin n, f i ^ (β * ((n - 1 - i.val : ℕ) : ℝ)) := by
    rw [show betaGasPairs n = Finset.univ.filter (fun z : Fin n × Fin n => z.1 < z.2) by
      ext z
      simp [mem_betaGasPairs]]
    rw [Finset.prod_finset_product (Finset.univ.filter _) Finset.univ
      (fun i => Finset.Ioi i) (by
        intro z
        simp)]
    simp only [Finset.prod_const, Fin.card_Ioi, f]
    apply Finset.prod_congr rfl
    intro i hi
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have hsnd :
      (∏ z ∈ betaGasPairs n, f z.2 ^ β) =
        ∏ i : Fin n, f i ^ (β * (i.val : ℝ)) := by
    rw [show betaGasPairs n = Finset.univ.filter (fun z : Fin n × Fin n => z.1 < z.2) by
      ext z
      simp [mem_betaGasPairs]]
    rw [Finset.prod_finset_product_right (Finset.univ.filter _) Finset.univ
      (fun i => Finset.Iio i) (by
        intro z
        simp)]
    simp only [Finset.prod_const, Fin.card_Iio, f]
    apply Finset.prod_congr rfl
    intro i hi
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  calc
    _ ≤ ∏ z ∈ betaGasPairs n, (f z.1 ^ β * f z.2 ^ β) := by
      apply Finset.prod_le_prod₀
      · intro z hz
        positivity
      intro z hz
      calc
        |x z.1 - x z.2| ^ β ≤ (f z.1 * f z.2) ^ β :=
          Real.rpow_le_rpow (abs_nonneg _) (hdiff z.1 z.2) hβ
        _ = f z.1 ^ β * f z.2 ^ β :=
          Real.mul_rpow (by positivity) (by positivity)
    _ = (∏ z ∈ betaGasPairs n, f z.1 ^ β) *
        (∏ z ∈ betaGasPairs n, f z.2 ^ β) := Finset.prod_mul_distrib
    _ = ∏ i : Fin n, (f i ^ (β * ((n - 1 - i.val : ℕ) : ℝ)) *
        f i ^ (β * (i.val : ℝ))) := by rw [hfst, hsnd, Finset.prod_mul_distrib]
    _ = ∏ i : Fin n, f i ^ (β * ((n - 1 : ℕ) : ℝ)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [← Real.rpow_add (by positivity)]
      have hpow : n - 1 - i.val + i.val = n - 1 := by omega
      have hpowR : ((n - 1 - i.val : ℕ) : ℝ) + (i.val : ℝ) =
          ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hpow
      rw [← mul_add, hpowR]

private lemma integrable_betaGas_oneDim_of_log_growth {p a c : ℝ} {V : ℝ → ℝ}
    (hp : 0 ≤ p) (ha : 0 < a) (hq : p - a * c < -1)
    (hV : Continuous V)
    (hGrowth : ∀ᶠ x in Filter.comap abs Filter.atTop, c * log |x| ≤ V x) :
    Integrable (fun x : ℝ => (1 + |x|) ^ p * exp (-a * V x)) volume := by
  let q : ℝ := p - a * c
  have hq' : q < -1 := hq
  have hTail : ∀ᶠ x in Filter.comap abs Filter.atTop, c * log |x| ≤ V x := hGrowth
  rw [Filter.eventually_comap] at hTail
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 hTail
  let R' : ℝ := max R 1
  have hR' : 1 ≤ R' := le_max_right _ _
  have hRbound (x : ℝ) (hx : R' ≤ |x|) : c * log |x| ≤ V x := by
    exact hR _ (le_trans (le_max_left _ _) hx) x rfl
  have hpoint (x : ℝ) (hx : 1 ≤ |x|) (hVx : c * log |x| ≤ V x) :
      (1 + |x|) ^ p * exp (-a * V x) ≤ 2 ^ p * |x| ^ q := by
    have hxabs : 0 < |x| := lt_of_lt_of_le zero_lt_one hx
    have hpoly : (1 + |x|) ^ p ≤ (2 * |x|) ^ p :=
      Real.rpow_le_rpow (by positivity) (by nlinarith) hp
    have hexp : exp (-a * V x) ≤ |x| ^ (-a * c) := by
      rw [Real.rpow_def_of_pos hxabs]
      apply exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonpos_left hVx (by linarith : -a ≤ 0)
      nlinarith [hmul]
    calc
      _ ≤ (2 * |x|) ^ p * |x| ^ (-a * c) :=
        mul_le_mul hpoly hexp (by positivity) (by positivity)
      _ = 2 ^ p * |x| ^ q := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        rw [mul_assoc, ← Real.rpow_add hxabs]
        congr 2
        dsimp [q]
        ring
  have hpowPos : IntegrableOn (fun x : ℝ => x ^ q) (Ioi R') volume :=
    integrableOn_Ioi_rpow_of_lt hq' (lt_of_lt_of_le zero_lt_one hR')
  have hpowNeg : IntegrableOn (fun x : ℝ => (-x) ^ q) (Iio (-R')) volume := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simp only [Function.comp_def, neg_preimage, neg_Iio, neg_neg]
    exact hpowPos
  have hg : Continuous (fun x : ℝ => (1 + |x|) ^ p * exp (-a * V x)) := by
    have hbase : Continuous (fun x : ℝ => 1 + |x|) := by fun_prop
    have hexp : Continuous (fun x : ℝ => exp (-a * V x)) := by fun_prop
    exact (hbase.rpow_const (fun x => Or.inl (by positivity))).mul hexp
  have hcenter : IntegrableOn (fun x : ℝ => (1 + |x|) ^ p * exp (-a * V x))
      (Icc (-R') R') volume := hg.integrableOn_Icc
  have hpos : IntegrableOn (fun x : ℝ => (1 + |x|) ^ p * exp (-a * V x))
      (Ioi R') volume := by
    apply Integrable.mono' (hpowPos.const_mul (2 ^ p)) hg.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change R' < x at hx
    have hxge1 : 1 ≤ x := le_of_lt (lt_of_le_of_lt hR' hx)
    have habs : |x| = x := abs_of_nonneg (le_trans zero_le_one hxge1)
    have hnonneg : 0 ≤ (1 + |x|) ^ p * exp (-a * V x) :=
      mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (by positivity) _))
        (le_of_lt (Real.exp_pos _))
    calc
      ‖(1 + |x|) ^ p * exp (-a * V x)‖ =
          (1 + |x|) ^ p * exp (-a * V x) := norm_of_nonneg hnonneg
      _ ≤ 2 ^ p * x ^ q := by
        simpa [habs] using hpoint x (by rw [habs]; exact hxge1)
          (hRbound x (by rw [habs]; exact le_of_lt hx))
  have hneg : IntegrableOn (fun x : ℝ => (1 + |x|) ^ p * exp (-a * V x))
      (Iio (-R')) volume := by
    apply Integrable.mono' (hpowNeg.const_mul (2 ^ p)) hg.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    change x < -R' at hx
    have hnegx : R' < -x := by linarith
    have habs : |x| = -x := abs_of_nonpos (by linarith)
    have hnonneg : 0 ≤ (1 + |x|) ^ p * exp (-a * V x) :=
      mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (by positivity) _))
        (le_of_lt (Real.exp_pos _))
    calc
      ‖(1 + |x|) ^ p * exp (-a * V x)‖ =
          (1 + |x|) ^ p * exp (-a * V x) := norm_of_nonneg hnonneg
      _ ≤ 2 ^ p * (-x) ^ q := by
        simpa [habs] using hpoint x (by rw [habs]; linarith [hnegx, hR'])
          (hRbound x (by rw [habs]; exact le_of_lt hnegx))
  have hcover : (Set.univ : Set ℝ) = Iio (-R') ∪ Icc (-R') R' ∪ Ioi R' := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Ioi]
    constructor
    · intro _
      by_cases hleft : x < -R'
      · exact Or.inl (Or.inl hleft)
      · by_cases hright : x ≤ R'
        · exact Or.inl (Or.inr ⟨le_of_not_gt hleft, hright⟩)
        · exact Or.inr (lt_of_not_ge hright)
    · intro _
      trivial
  rw [← integrableOn_univ, hcover, integrableOn_union, integrableOn_union]
  exact ⟨⟨hneg, hcenter⟩, hpos⟩

private lemma betaGasWeight_le_coord_prod (n : ℕ) {β : ℝ} (hβ : 0 ≤ β)
    (V : ℝ → ℝ)
    (x : Fin n → ℝ) :
    betaGasWeight n β V x ≤
      ∏ i : Fin n, ((1 + |x i|) ^ (β * ((n - 1 : ℕ) : ℝ)) *
        exp (-(β * (n : ℝ) / 2) * V (x i))) := by
  classical
  let pairs := betaGasPairs n
  let a : ℝ := β * (n : ℝ) / 2
  let p : ℝ := β * ((n - 1 : ℕ) : ℝ)
  have hvander : (∏ z ∈ pairs, |x z.1 - x z.2| ^ β) ≤
      ∏ i : Fin n, (1 + |x i|) ^ p :=
    betaGasVandermonde_le_coord_prod n hβ x
  have hexp : exp (-(β * (n : ℝ) / 2) * ∑ i : Fin n, V (x i)) =
      ∏ i : Fin n, exp (-a * V (x i)) := by
    have hdistrib : -(β * (n : ℝ) / 2) * ∑ i : Fin n, V (x i) =
        ∑ i : Fin n, (-a * V (x i)) := by simp [a, Finset.mul_sum]
    rw [hdistrib]
    exact Real.exp_sum _ _
  have hpoint : betaGasWeight n β V x ≤
      ∏ i : Fin n, ((1 + |x i|) ^ p * exp (-a * V (x i))) := by
    rw [betaGasWeight_def]
    rw [hexp]
    calc
      _ ≤ (∏ i : Fin n, exp (-a * V (x i))) *
          (∏ i : Fin n, (1 + |x i|) ^ p) := by
        exact mul_le_mul_of_nonneg_left hvander (by positivity)
      _ = ∏ i : Fin n, ((1 + |x i|) ^ p * exp (-a * V (x i))) := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i hi
        ring
  exact hpoint

private lemma eventually_quadratic_log_ratio (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x in Filter.comap (fun x : ℝ => |x|) Filter.atTop,
      c < (x ^ 2 / 2) / log |x| := by
  rw [Filter.eventually_comap]
  apply Filter.eventually_atTop.2
  refine ⟨max (2 * c + 1) 2, ?_⟩
  intro t ht x hxt
  have htA : 2 * c + 1 ≤ t := le_trans (le_max_left _ _) ht
  have htB : 2 ≤ t := le_trans (le_max_right _ _) ht
  have htpos : 0 < t := by linarith
  have htgt : 1 < t := by linarith
  have hlogpos : 0 < log t := Real.log_pos htgt
  have hlogle : log t ≤ t :=
    (Real.log_le_sub_one_of_pos htpos).trans (by linarith)
  have hmargin : 0 < t / 2 - c := by linarith
  have hquad : c * t < t ^ 2 / 2 := by
    have := mul_pos htpos hmargin
    nlinarith
  rw [← sq_abs, hxt, lt_div_iff₀ hlogpos]
  exact (mul_le_mul_of_nonneg_left hlogle hc.le).trans_lt hquad

/-- A continuous potential with supercritical logarithmic growth gives an integrable beta-gas
weight. The liminf is taken in the extended reals along `|x| → ∞`. -/
theorem integrable_betaGasWeight_of_eventual_log_growth (n : ℕ) {β β' : ℝ}
    (hβ : 0 < β)
    (hβ' : 1 < β') (hββ' : β ≤ β') {V : ℝ → ℝ} (hV : Continuous V)
    (hRatio : ∀ᶠ x in Filter.comap (fun x : ℝ => |x|) Filter.atTop,
      2 * β' / β < V x / log |x|) :
    Integrable (betaGasWeight n β V)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  · have hnle : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    let a : ℝ := β * (n : ℝ) / 2
    let p : ℝ := β * ((n - 1 : ℕ) : ℝ)
    let c : ℝ := 2 * β' / β
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have hq : p - a * c < -1 := by
      have hncast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (Nat.sub_add_cancel hnle).symm
      have hformula : p - a * c =
          -β' + ((n - 1 : ℕ) : ℝ) * (β - β') := by
        dsimp [p, a, c]
        rw [hncast]
        field_simp [hβ.ne']
        ring
      rw [hformula]
      have hdiff : β - β' ≤ 0 := sub_nonpos.mpr hββ'
      have hmul : ((n - 1 : ℕ) : ℝ) * (β - β') ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hdiff
      linarith
    have hlarge : ∀ᶠ x in Filter.comap (fun x : ℝ => |x|) Filter.atTop, 1 < |x| := by
      rw [Filter.eventually_comap]
      exact Filter.eventually_atTop.2 ⟨(2 : ℝ), fun b hb x hxb => by
        rw [hxb]
        linarith⟩
    have hGrowth :
        ∀ᶠ x in Filter.comap (fun x : ℝ => |x|) Filter.atTop, c * log |x| ≤ V x := by
      filter_upwards [hRatio, hlarge] with x hratio hx
      have hlog : 0 < log |x| := Real.log_pos hx
      exact le_of_lt ((lt_div_iff₀ hlog).mp hratio)
    have hmajor : Integrable
        (fun x : Fin n → ℝ =>
          ∏ i, ((1 + |x i|) ^ p * exp (-a * V (x i))))
        (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) :=
      Integrable.fintype_prod fun _ =>
        integrable_betaGas_oneDim_of_log_growth (by positivity) ha hq hV hGrowth
    apply Integrable.mono' hmajor
      ((continuous_betaGasWeight n hβ.le hV).aestronglyMeasurable)
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (betaGasWeight_nonneg n β V x),
      abs_of_nonneg (by positivity :
        0 ≤ ∏ i : Fin n, ((1 + |x i|) ^ p * exp (-a * V (x i))))] using
      betaGasWeight_le_coord_prod n hβ.le V x

/-- A continuous potential with supercritical logarithmic growth gives an integrable beta-gas
weight. The liminf is taken in the extended reals along `|x| → ∞`. -/
theorem integrable_betaGasWeight_of_log_growth (n : ℕ) {β β' : ℝ} (hβ : 0 < β)
    (hβ' : 1 < β') (hββ' : β ≤ β') {V : ℝ → ℝ} (hV : Continuous V)
    (hliminf :
      ((2 * β' / β : ℝ) : EReal) <
        Filter.liminf (fun x : ℝ => ((V x / log |x| : ℝ) : EReal))
          (Filter.comap (fun x : ℝ => |x|) Filter.atTop)) :
    Integrable (betaGasWeight n β V)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) := by
  have hratioE : ∀ᶠ x in Filter.comap (fun x : ℝ => |x|) Filter.atTop,
      ((2 * β' / β : ℝ) : EReal) < ((V x / log |x| : ℝ) : EReal) :=
    Filter.eventually_lt_of_lt_liminf hliminf
  have hRatio : ∀ᶠ x in Filter.comap (fun x : ℝ => |x|) Filter.atTop,
      2 * β' / β < V x / log |x| := by
    filter_upwards [hratioE] with x hx
    exact EReal.coe_lt_coe_iff.mp hx
  exact integrable_betaGasWeight_of_eventual_log_growth n hβ hβ' hββ' hV hRatio

/-- Under the same logarithmic-growth condition, the beta-gas partition function is finite and
strictly positive. -/
theorem betaGasPartitionFunction_pos_of_log_growth (n : ℕ) {β β' : ℝ} (hβ : 0 < β)
    (hβ' : 1 < β') (hββ' : β ≤ β') {V : ℝ → ℝ} (hV : Continuous V)
    (hliminf :
      ((2 * β' / β : ℝ) : EReal) <
        Filter.liminf (fun x : ℝ => ((V x / log |x| : ℝ) : EReal))
          (Filter.comap (fun x : ℝ => |x|) Filter.atTop)) :
    0 < betaGasPartitionFunction n β V := by
  let x₀ : Fin n → ℝ := fun i => (i : ℝ)
  have hx₀ : 0 < betaGasWeight n β V x₀ := by
    apply betaGasWeight_pos
    intro i j hij
    dsimp [x₀] at hij
    exact Fin.ext (by exact_mod_cast hij)
  rw [betaGasPartitionFunction_def]
  exact integral_pos_of_integrable_nonneg_ne_zero
    (continuous_betaGasWeight n hβ.le hV)
    (integrable_betaGasWeight_of_log_growth n hβ hβ' hββ' hV hliminf)
    (betaGasWeight_nonneg n β V) hx₀.ne'

/-- The beta-gas density is integrable under the logarithmic-growth condition. -/
theorem integrable_betaGasDensity_of_log_growth (n : ℕ) {β β' : ℝ} (hβ : 0 < β)
    (hβ' : 1 < β') (hββ' : β ≤ β') {V : ℝ → ℝ} (hV : Continuous V)
    (hliminf :
      ((2 * β' / β : ℝ) : EReal) <
        Filter.liminf (fun x : ℝ => ((V x / log |x| : ℝ) : EReal))
          (Filter.comap (fun x : ℝ => |x|) Filter.atTop)) :
    Integrable (betaGasDensity n β V)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) :=
  integrable_betaGasDensity n β V
    (integrable_betaGasWeight_of_log_growth n hβ hβ' hββ' hV hliminf)

/-- The general-potential beta-gas measure is a probability under the logarithmic-growth
condition. -/
theorem isProbabilityMeasure_betaGasMeasure_of_log_growth (n : ℕ) {β β' : ℝ} (hβ : 0 < β)
    (hβ' : 1 < β') (hββ' : β ≤ β') {V : ℝ → ℝ} (hV : Continuous V)
    (hliminf :
      ((2 * β' / β : ℝ) : EReal) <
        Filter.liminf (fun x : ℝ => ((V x / log |x| : ℝ) : EReal))
          (Filter.comap (fun x : ℝ => |x|) Filter.atTop)) :
    IsProbabilityMeasure (betaGasMeasure n β V) :=
  isProbabilityMeasure_betaGasMeasure n β V
    (integrable_betaGasWeight_of_log_growth n hβ hβ' hββ' hV hliminf)
    (betaGasPartitionFunction_pos_of_log_growth n hβ hβ' hββ' hV hliminf)

private lemma gaussianBetaGasWeight_le_prod (n : ℕ) {β : ℝ} (hβ : 0 < β)
    (x : Fin n → ℝ) :
    gaussianBetaGasWeight n β x ≤
      ∏ i : Fin n, ((1 + |x i|) ^ (β * ((n - 1 : ℕ) : ℝ)) *
        exp (-(β * (n : ℝ) / 4) * x i ^ 2)) := by
  rw [gaussianBetaGasWeight_eq_betaGasWeight]
  convert (betaGasWeight_le_coord_prod n hβ.le (fun t => t ^ 2 / 2) x) using 1
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  ring_nf

/-- The Gaussian beta-gas weight is integrable for every positive inverse temperature. -/
theorem integrable_gaussianBetaGasWeight (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    Integrable (gaussianBetaGasWeight n β)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) := by
  let β' : ℝ := max β 2
  have hβ' : 1 < β' := by
    dsimp [β']
    exact lt_of_lt_of_le one_lt_two (le_max_right _ _)
  have hββ' : β ≤ β' := le_max_left _ _
  have hc : 0 < 2 * β' / β := by positivity
  have hRatio := eventually_quadratic_log_ratio (2 * β' / β) hc
  rw [gaussianBetaGasWeight_eq_betaGasWeight]
  exact integrable_betaGasWeight_of_eventual_log_growth n hβ hβ' hββ' (by fun_prop) (by
    simpa [β'] using hRatio)

/-- The Gaussian beta-gas partition function is strictly positive. -/
theorem gaussianBetaGasPartitionFunction_pos (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    0 < gaussianBetaGasPartitionFunction n β := by
  let β' : ℝ := max β 2
  have hβ' : 1 < β' := by
    dsimp [β']
    exact lt_of_lt_of_le one_lt_two (le_max_right _ _)
  have hββ' : β ≤ β' := le_max_left _ _
  have hc : 0 < 2 * β' / β := by positivity
  have hRatio := eventually_quadratic_log_ratio (2 * β' / β) hc
  let V : ℝ → ℝ := fun t => t ^ 2 / 2
  have hV : Continuous V := by fun_prop
  let x₀ : Fin n → ℝ := fun i => (i : ℝ)
  have hx₀ : 0 < betaGasWeight n β V x₀ := by
    apply betaGasWeight_pos
    intro i j hij
    dsimp [x₀] at hij
    exact Fin.ext (by exact_mod_cast hij)
  rw [gaussianBetaGasPartitionFunction_eq_betaGasPartitionFunction]
  rw [betaGasPartitionFunction_def]
  exact integral_pos_of_integrable_nonneg_ne_zero
    (continuous_betaGasWeight n hβ.le hV)
    (integrable_betaGasWeight_of_eventual_log_growth n hβ hβ' hββ' hV (by
      simpa [V, β'] using hRatio))
    (betaGasWeight_nonneg n β V) hx₀.ne'

/-- The Gaussian beta-gas density is integrable for positive inverse temperature. -/
theorem integrable_gaussianBetaGasDensity (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    Integrable (gaussianBetaGasDensity n β)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) := by
  rw [gaussianBetaGasDensity_eq_betaGasDensity]
  apply integrable_betaGasDensity
  rw [← gaussianBetaGasWeight_eq_betaGasWeight]
  exact integrable_gaussianBetaGasWeight n hβ

/-- The Gaussian beta-gas density integrates to one for positive inverse temperature. -/
@[simp]
theorem integral_gaussianBetaGasDensity (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    (∫ x, gaussianBetaGasDensity n β x
      ∂Measure.pi fun _ : Fin n => (volume : Measure ℝ)) = 1 := by
  rw [gaussianBetaGasDensity_eq_betaGasDensity]
  apply integral_betaGasDensity
  rw [← gaussianBetaGasPartitionFunction_eq_betaGasPartitionFunction]
  exact gaussianBetaGasPartitionFunction_pos n hβ

/-- The normalized Gaussian beta-gas measure has total mass one. -/
theorem isProbabilityMeasure_gaussianBetaGasMeasure (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    IsProbabilityMeasure (gaussianBetaGasMeasure n β) := by
  rw [gaussianBetaGasMeasure_eq_betaGasMeasure]
  apply isProbabilityMeasure_betaGasMeasure
  · rw [← gaussianBetaGasWeight_eq_betaGasWeight]
    exact integrable_gaussianBetaGasWeight n hβ
  · rw [← gaussianBetaGasPartitionFunction_eq_betaGasPartitionFunction]
    exact gaussianBetaGasPartitionFunction_pos n hβ

/-- Evaluate the Gaussian beta-gas measure on a measurable set. -/
theorem gaussianBetaGasMeasure_apply (n : ℕ) {β : ℝ} (hβ : 0 < β)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    gaussianBetaGasMeasure n β s =
      ENNReal.ofReal (∫ x in s, gaussianBetaGasDensity n β x
        ∂Measure.pi fun _ : Fin n => (volume : Measure ℝ)) := by
  rw [gaussianBetaGasMeasure_eq_betaGasMeasure, gaussianBetaGasDensity_eq_betaGasDensity]
  apply betaGasMeasure_apply n β _ hs
  rw [← gaussianBetaGasWeight_eq_betaGasWeight]
  exact integrable_gaussianBetaGasWeight n hβ

/-- Integrate a function against the Gaussian beta-gas measure. -/
theorem integral_gaussianBetaGasMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (β : ℝ) (f : (Fin n → ℝ) → E) :
    ∫ x, f x ∂gaussianBetaGasMeasure n β =
      ∫ x, gaussianBetaGasDensity n β x • f x
        ∂Measure.pi fun _ : Fin n => (volume : Measure ℝ) := by
  rw [gaussianBetaGasMeasure_eq_betaGasMeasure, gaussianBetaGasDensity_eq_betaGasDensity]
  apply integral_betaGasMeasure
  exact (measurable_betaGasDensity n β (by fun_prop)).aemeasurable

end TauCeti.Probability
