/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import TauCeti.InformationTheory.Hellinger.Basic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.RadonNikodym

/-!
# Data processing inequality and invariance for Hellinger affinity and distance

Pushing two finite measures forward along a measurable map or through a Markov kernel cannot
decrease their Hellinger affinity, and therefore contracts the squared Hellinger distance of
probability measures (Samworth and Shah, Lemma 8.10, p. 233).

For measurable maps, we prove `TauCeti.hellingerAffinity_le_map` directly via the variational
AM–GM bound $2\sqrt{ab} \le \sqrt{v/u}\,a + \sqrt{u/v}\,b$ on Radon–Nikodym derivatives, avoiding
any countability or standard-Borel assumptions on the measurable spaces. For a Markov kernel `κ`,
composition-product invariance `TauCeti.hellingerAffinity_compProd_left` shows
`hellingerAffinity (P ⊗ₘ κ) (Q ⊗ₘ κ) = hellingerAffinity P Q`, and projecting onto the second
coordinate yields the kernel data processing inequality `TauCeti.hellingerAffinity_le_comp`.

When `f` is a measurable embedding (in particular, a measurable equivalence), the Hellinger
affinity and squared Hellinger distance are preserved with equality
(`MeasurableEmbedding.hellingerAffinity_map`, `MeasurableEquiv.hellingerAffinity_map`).

## Main results

* `TauCeti.hellingerAffinity_le_map` and `TauCeti.hellingerAffinity_le_map_of_aemeasurable`:
  data processing inequality for Hellinger affinity under measurable and a.e.-measurable maps.
* `TauCeti.sqHellinger_map_le` and `TauCeti.sqHellinger_map_le_of_aemeasurable`:
  contraction of squared Hellinger distance under pushforwards.
* `TauCeti.hellingerAffinity_le_trim` and `TauCeti.sqHellinger_trim_le`:
  data processing under restriction to a sub-σ-algebra.
* `TauCeti.hellingerAffinity_compProd_left`: invariance under forming a composition product with a
  Markov kernel.
* `TauCeti.hellingerAffinity_le_comp` and `TauCeti.sqHellinger_comp_le`:
  data processing inequality under composition with a Markov kernel.
* `MeasurableEmbedding.hellingerAffinity_map`, `MeasurableEmbedding.sqHellinger_map`,
  `MeasurableEquiv.hellingerAffinity_map`, `MeasurableEquiv.sqHellinger_map`:
  invariance under measurable embeddings and measurable equivalences.

## References

* R. J. Samworth and R. D. Shah, *Modern Statistical Methods and Theory*, Cambridge University
  Press, 2026, Lemma 8.10, p. 233.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

section Map

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

private lemma two_mul_sqrt_mul_le {a b u v : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : 0 < u) (hv : 0 < v) :
    2 * √(a * b) ≤ √(v / u) * a + √(u / v) * b := by
  have hsq : 0 ≤ (√(v * a) - √(u * b)) ^ 2 := sq_nonneg _
  rw [sub_sq, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at hsq
  have hprod : √(v * a) * √(u * b) = √(u * v) * √(a * b) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1; ring
  have hv_eq : v / u * (u * v) = v ^ 2 := by field_simp
  have hu_eq : u / v * (u * v) = u ^ 2 := by field_simp
  have h1 : √(v / u) * √(u * v) = v := by
    rw [← Real.sqrt_mul (by positivity), hv_eq, Real.sqrt_sq hv.le]
  have h2 : √(u / v) * √(u * v) = u := by
    rw [← Real.sqrt_mul (by positivity), hu_eq, Real.sqrt_sq hu.le]
  have hpos : 0 < √(u * v) := Real.sqrt_pos.mpr (mul_pos hu hv)
  nlinarith

private lemma rnDeriv_map_eq_zero_imp {P ν : Measure α} [IsFiniteMeasure P] [IsFiniteMeasure ν]
    (hPν : P ≪ ν) {f : α → β} (hf : Measurable f) :
    ∀ᵐ x ∂ν, (P.map f).rnDeriv (ν.map f) (f x) = 0 → P.rnDeriv ν x = 0 := by
  set S : Set β := {y | (P.map f).rnDeriv (ν.map f) y = 0}
  have hS : MeasurableSet S :=
    ((P.map f).measurable_rnDeriv (ν.map f)) (measurableSet_singleton 0)
  have hSP : P.map f S = 0 := by
    rw [← Measure.setLIntegral_rnDeriv (hPν.map hf)]
    exact setLIntegral_eq_zero hS fun _ hy => hy
  have hPre : ∫⁻ x in f ⁻¹' S, P.rnDeriv ν x ∂ν = 0 := by
    rw [Measure.setLIntegral_rnDeriv hPν, ← Measure.map_apply hf hS, hSP]
  exact (setLIntegral_eq_zero_iff' (hf hS) (P.measurable_rnDeriv ν).aemeasurable).mp hPre

private lemma measurable_ratioWeight (P Q ν : Measure α) (f : α → β) :
    let p' := (P.map f).rnDeriv (ν.map f)
    let q' := (Q.map f).rnDeriv (ν.map f)
    let A : Set β := p' ⁻¹' Set.Ioo 0 ∞ ∩ q' ⁻¹' Set.Ioo 0 ∞
    Measurable (A.indicator fun y => ENNReal.ofReal (√((q' y).toReal / (p' y).toReal))) := by
  intro p' q' A
  have hA : MeasurableSet A :=
    ((P.map f).measurable_rnDeriv (ν.map f) measurableSet_Ioo).inter
      ((Q.map f).measurable_rnDeriv (ν.map f) measurableSet_Ioo)
  refine Measurable.indicator ?_ hA
  exact ((((Q.map f).measurable_rnDeriv (ν.map f)).ennreal_toReal.div
    ((P.map f).measurable_rnDeriv (ν.map f)).ennreal_toReal).sqrt).ennreal_ofReal

private lemma lintegral_rnDeriv_mul_ratio_le {P Q ν : Measure α}
    [IsFiniteMeasure P] [IsFiniteMeasure ν]
    (hPν : P ≪ ν) {f : α → β} (hf : Measurable f) :
    let p' := (P.map f).rnDeriv (ν.map f)
    let q' := (Q.map f).rnDeriv (ν.map f)
    let A : Set β := p' ⁻¹' Set.Ioo 0 ∞ ∩ q' ⁻¹' Set.Ioo 0 ∞
    let r : β → ℝ≥0∞ := A.indicator fun y => ENNReal.ofReal (√((q' y).toReal / (p' y).toReal))
    ∫⁻ x, r (f x) * P.rnDeriv ν x ∂ν ≤
      ∫⁻ y, ENNReal.ofReal (√((p' y).toReal * (q' y).toReal)) ∂(ν.map f) := by
  intro p' q' A r
  have hr : Measurable r := measurable_ratioWeight P Q ν f
  calc
    ∫⁻ x, r (f x) * P.rnDeriv ν x ∂ν
      = ∫⁻ x, P.rnDeriv ν x * r (f x) ∂ν := by simp_rw [mul_comm]
    _ = ∫⁻ x, r (f x) ∂P := lintegral_rnDeriv_mul hPν (hr.comp hf).aemeasurable
    _ = ∫⁻ y, r y ∂(P.map f) := (lintegral_map hr hf).symm
    _ = ∫⁻ y, p' y * r y ∂(ν.map f) :=
      (lintegral_rnDeriv_mul (hPν.map hf) hr.aemeasurable).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (√((p' y).toReal * (q' y).toReal)) ∂(ν.map f) := by
      refine lintegral_mono fun y => ?_
      by_cases hy : y ∈ A
      · have hp0 : 0 < p' y := hy.1.1
        have hpt : p' y < ∞ := hy.1.2
        have hu : 0 < (p' y).toReal := ENNReal.toReal_pos hp0.ne' hpt.ne
        simp only [r, Set.indicator_of_mem hy]
        nth_rw 1 [← ENNReal.ofReal_toReal hpt.ne]
        rw [← ENNReal.ofReal_mul hu.le]
        refine le_of_eq (congrArg ENNReal.ofReal ?_)
        calc
          (p' y).toReal * √((q' y).toReal / (p' y).toReal)
            = √((p' y).toReal ^ 2) * √((q' y).toReal / (p' y).toReal) := by
              rw [Real.sqrt_sq hu.le]
          _ = √((p' y).toReal ^ 2 * ((q' y).toReal / (p' y).toReal)) :=
              (Real.sqrt_mul (sq_nonneg _) _).symm
          _ = √((p' y).toReal * (q' y).toReal) := by congr 1; field_simp
      · simp [r, Set.indicator_of_notMem hy]

private lemma ae_two_mul_sqrt_rnDeriv_le (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] {f : α → β} (hf : Measurable f) :
    let ν := P + Q
    let p' := (P.map f).rnDeriv (ν.map f)
    let q' := (Q.map f).rnDeriv (ν.map f)
    let A : Set β := p' ⁻¹' Set.Ioo 0 ∞ ∩ q' ⁻¹' Set.Ioo 0 ∞
    let r₁ : β → ℝ≥0∞ := A.indicator fun y => ENNReal.ofReal (√((q' y).toReal / (p' y).toReal))
    let r₂ : β → ℝ≥0∞ := A.indicator fun y => ENNReal.ofReal (√((p' y).toReal / (q' y).toReal))
    ∀ᵐ x ∂ν,
      2 * ENNReal.ofReal (√((P.rnDeriv ν x).toReal * (Q.rnDeriv ν x).toReal)) ≤
        r₁ (f x) * P.rnDeriv ν x + r₂ (f x) * Q.rnDeriv ν x := by
  intro ν p' q' A r₁ r₂
  have hPν : P ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQν : Q ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right' P
  filter_upwards [P.rnDeriv_lt_top ν, Q.rnDeriv_lt_top ν,
    ae_of_ae_map hf.aemeasurable ((P.map f).rnDeriv_lt_top (ν.map f)),
    ae_of_ae_map hf.aemeasurable ((Q.map f).rnDeriv_lt_top (ν.map f)),
    rnDeriv_map_eq_zero_imp hPν hf, rnDeriv_map_eq_zero_imp hQν hf]
    with x hPt hQt hP't hQ't hP0 hQ0
  by_cases hp'0 : p' (f x) = 0
  · simp [hP0 hp'0]
  · by_cases hq'0 : q' (f x) = 0
    · simp [hQ0 hq'0]
    · have hfxA : f x ∈ A :=
        ⟨⟨pos_iff_ne_zero.mpr hp'0, hP't⟩, ⟨pos_iff_ne_zero.mpr hq'0, hQ't⟩⟩
      have hu : 0 < (p' (f x)).toReal := ENNReal.toReal_pos hp'0 hP't.ne
      have hv : 0 < (q' (f x)).toReal := ENNReal.toReal_pos hq'0 hQ't.ne
      have hp_eq : ENNReal.ofReal (P.rnDeriv ν x).toReal = P.rnDeriv ν x :=
        ENNReal.ofReal_toReal hPt.ne
      have hq_eq : ENNReal.ofReal (Q.rnDeriv ν x).toReal = Q.rnDeriv ν x :=
        ENNReal.ofReal_toReal hQt.ne
      simp only [r₁, r₂, Set.indicator_of_mem hfxA]
      nth_rw 2 [← hp_eq]
      nth_rw 2 [← hq_eq]
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal
        (two_mul_sqrt_mul_le ENNReal.toReal_nonneg ENNReal.toReal_nonneg hu hv)

/-- **Data processing inequality for Hellinger affinity** under a measurable map. -/
theorem hellingerAffinity_le_map (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {f : α → β} (hf : Measurable f) :
    hellingerAffinity P Q ≤ hellingerAffinity (P.map f) (Q.map f) := by
  let ν := P + Q
  have hPν : P ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQν : Q ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right' P
  have hmap : ν.map f = P.map f + Q.map f := Measure.map_add P Q hf
  let p := P.rnDeriv ν
  let q := Q.rnDeriv ν
  let p' := (P.map f).rnDeriv (ν.map f)
  let q' := (Q.map f).rnDeriv (ν.map f)
  let A : Set β := p' ⁻¹' Set.Ioo 0 ∞ ∩ q' ⁻¹' Set.Ioo 0 ∞
  let r₁ : β → ℝ≥0∞ := A.indicator fun y => ENNReal.ofReal (√((q' y).toReal / (p' y).toReal))
  let r₂ : β → ℝ≥0∞ := A.indicator fun y => ENNReal.ofReal (√((p' y).toReal / (q' y).toReal))
  have h1 : ∫⁻ x, r₁ (f x) * p x ∂ν ≤
      ∫⁻ y, ENNReal.ofReal (√((p' y).toReal * (q' y).toReal)) ∂(ν.map f) :=
    lintegral_rnDeriv_mul_ratio_le hPν hf
  have h2 : ∫⁻ x, r₂ (f x) * q x ∂ν ≤
      ∫⁻ y, ENNReal.ofReal (√((p' y).toReal * (q' y).toReal)) ∂(ν.map f) := by
    have h2' := lintegral_rnDeriv_mul_ratio_le (P := Q) (Q := P) (ν := ν) hQν hf
    dsimp only at h2'
    convert h2' using 1
    · simp only [r₂, A, p', q', q, Set.inter_comm]
    · simp_rw [mul_comm (p' _).toReal]; rfl
  have hlint : 2 * ∫⁻ x, ENNReal.ofReal (√((p x).toReal * (q x).toReal)) ∂ν ≤
      2 * ∫⁻ y, ENNReal.ofReal (√((p' y).toReal * (q' y).toReal)) ∂(ν.map f) := by
    calc
      2 * ∫⁻ x, ENNReal.ofReal (√((p x).toReal * (q x).toReal)) ∂ν
        = ∫⁻ x, 2 * ENNReal.ofReal (√((p x).toReal * (q x).toReal)) ∂ν :=
          (lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top).symm
      _ ≤ ∫⁻ x, (r₁ (f x) * p x + r₂ (f x) * q x) ∂ν :=
          lintegral_mono_ae (ae_two_mul_sqrt_rnDeriv_le P Q hf)
      _ = (∫⁻ x, r₁ (f x) * p x ∂ν) + ∫⁻ x, r₂ (f x) * q x ∂ν :=
          lintegral_add_left
            (((measurable_ratioWeight P Q ν f).comp hf).mul (P.measurable_rnDeriv ν)) _
      _ ≤ (∫⁻ y, ENNReal.ofReal (√((p' y).toReal * (q' y).toReal)) ∂(ν.map f)) +
            ∫⁻ y, ENNReal.ofReal (√((p' y).toReal * (q' y).toReal)) ∂(ν.map f) :=
          add_le_add h1 h2
      _ = 2 * ∫⁻ y, ENNReal.ofReal (√((p' y).toReal * (q' y).toReal)) ∂(ν.map f) := by
          rw [two_mul]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_sqrt_rnDeriv_mul P Q ν)
      (ae_of_all _ fun _ => Real.sqrt_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal
      (integrable_sqrt_rnDeriv_mul (P.map f) (Q.map f) (ν.map f))
      (ae_of_all _ fun _ => Real.sqrt_nonneg _),
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num)
      (integral_nonneg fun _ => Real.sqrt_nonneg _))] at hlint
  rw [hellingerAffinity_def, hellingerAffinity_def, ← hmap]
  linarith

/-- **Data processing inequality for Hellinger affinity** under an almost-everywhere measurable
map. -/
theorem hellingerAffinity_le_map_of_aemeasurable {P Q : Measure α}
    [IsFiniteMeasure P] [IsFiniteMeasure Q] {f : α → β}
    (hfP : AEMeasurable f P) (hfQ : AEMeasurable f Q) :
    hellingerAffinity P Q ≤ hellingerAffinity (P.map f) (Q.map f) := by
  have hf : AEMeasurable f (P + Q) := hfP.add_measure hfQ
  obtain ⟨hPg, hQg⟩ := ae_add_measure_iff.mp hf.ae_eq_mk
  rw [Measure.map_congr hPg, Measure.map_congr hQg]
  exact hellingerAffinity_le_map P Q hf.measurable_mk

/-- **Data processing inequality for squared Hellinger distance** under a measurable map. -/
theorem sqHellinger_map_le (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {f : α → β} (hf : Measurable f) :
    sqHellinger (P.map f) (Q.map f) ≤ sqHellinger P Q := by
  rw [sqHellinger_def, sqHellinger_def]
  linarith [hellingerAffinity_le_map P Q hf]

/-- **Data processing inequality for squared Hellinger distance** under an almost-everywhere
measurable map. -/
theorem sqHellinger_map_le_of_aemeasurable {P Q : Measure α}
    [IsFiniteMeasure P] [IsFiniteMeasure Q] {f : α → β}
    (hfP : AEMeasurable f P) (hfQ : AEMeasurable f Q) :
    sqHellinger (P.map f) (Q.map f) ≤ sqHellinger P Q := by
  rw [sqHellinger_def, sqHellinger_def]
  linarith [hellingerAffinity_le_map_of_aemeasurable hfP hfQ]

end Map

section Trim

variable {α : Type*} {m m₀ : MeasurableSpace α}

/-- Restricting two finite measures to a sub-σ-algebra cannot decrease their Hellinger affinity. -/
theorem hellingerAffinity_le_trim (P Q : Measure[m₀] α) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hm : m ≤ m₀) :
    hellingerAffinity P Q ≤ hellingerAffinity (P.trim hm) (Q.trim hm) := by
  simp_rw [trim_eq_map]
  exact @hellingerAffinity_le_map α α m₀ m P Q _ _ id (measurable_id'' hm)

/-- Restricting two finite measures to a sub-σ-algebra contracts their squared Hellinger
distance. -/
theorem sqHellinger_trim_le (P Q : Measure[m₀] α) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hm : m ≤ m₀) :
    sqHellinger (P.trim hm) (Q.trim hm) ≤ sqHellinger P Q := by
  rw [sqHellinger_def, sqHellinger_def]
  linarith [hellingerAffinity_le_trim P Q hm]

end Trim

section Kernel

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- Forming a composition product with a common Markov kernel preserves the Hellinger affinity of
two finite measures. -/
theorem hellingerAffinity_compProd_left (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    hellingerAffinity (P ⊗ₘ κ) (Q ⊗ₘ κ) = hellingerAffinity P Q := by
  rw [hellingerAffinity_def, hellingerAffinity_def, ← Measure.compProd_add_left]
  have hae : (fun z : α × β =>
        √(((P ⊗ₘ κ).rnDeriv ((P + Q) ⊗ₘ κ) z).toReal *
          ((Q ⊗ₘ κ).rnDeriv ((P + Q) ⊗ₘ κ) z).toReal)) =ᵐ[(P + Q) ⊗ₘ κ]
      fun z => √((P.rnDeriv (P + Q) z.1).toReal * (Q.rnDeriv (P + Q) z.1).toReal) := by
    filter_upwards [rnDeriv_measure_compProd_left P (P + Q) κ,
      rnDeriv_measure_compProd_left Q (P + Q) κ] with z hPz hQz
    rw [hPz, hQz]
  have hint : Integrable
      (fun z : α × β => √((P.rnDeriv (P + Q) z.1).toReal * (Q.rnDeriv (P + Q) z.1).toReal))
      ((P + Q) ⊗ₘ κ) :=
    (integrable_sqrt_rnDeriv_mul (P ⊗ₘ κ) (Q ⊗ₘ κ) ((P + Q) ⊗ₘ κ)).congr hae
  rw [integral_congr_ae hae, Measure.integral_compProd hint]
  simp [integral_const]

/-- **Data processing inequality for Hellinger affinity** under composition with a Markov kernel.
-/
theorem hellingerAffinity_le_comp (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    hellingerAffinity P Q ≤ hellingerAffinity (κ ∘ₘ P) (κ ∘ₘ Q) := by
  rw [← hellingerAffinity_compProd_left P Q κ, ← Measure.snd_compProd P κ,
    ← Measure.snd_compProd Q κ]
  exact hellingerAffinity_le_map (P ⊗ₘ κ) (Q ⊗ₘ κ) measurable_snd

/-- **Data processing inequality for squared Hellinger distance** under composition with a Markov
kernel. -/
theorem sqHellinger_comp_le (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    sqHellinger (κ ∘ₘ P) (κ ∘ₘ Q) ≤ sqHellinger P Q := by
  rw [sqHellinger_def, sqHellinger_def]
  linarith [hellingerAffinity_le_comp P Q κ]

end Kernel

end TauCeti

namespace MeasurableEmbedding

open MeasureTheory TauCeti

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β}

/-- Pushing two finite measures forward along a measurable embedding preserves their Hellinger
affinity. -/
theorem hellingerAffinity_map (hf : MeasurableEmbedding f) (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    hellingerAffinity (P.map f) (Q.map f) = hellingerAffinity P Q := by
  rw [hellingerAffinity_def, hellingerAffinity_def, ← Measure.map_add P Q hf.measurable,
    hf.integral_map]
  refine integral_congr_ae ?_
  filter_upwards [hf.rnDeriv_map P (P + Q), hf.rnDeriv_map Q (P + Q)] with x hPx hQx
  rw [hPx, hQx]

/-- Pushing two finite measures forward along a measurable embedding preserves their squared
Hellinger distance. -/
theorem sqHellinger_map (hf : MeasurableEmbedding f) (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    sqHellinger (P.map f) (Q.map f) = sqHellinger P Q := by
  rw [sqHellinger_def, sqHellinger_def, hf.hellingerAffinity_map]

end MeasurableEmbedding

namespace MeasurableEquiv

open MeasureTheory TauCeti

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- Pushing two finite measures forward along a measurable equivalence preserves their Hellinger
affinity. -/
@[simp]
theorem hellingerAffinity_map (e : α ≃ᵐ β) (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    hellingerAffinity (P.map e) (Q.map e) = hellingerAffinity P Q :=
  e.measurableEmbedding.hellingerAffinity_map P Q

/-- Pushing two finite measures forward along a measurable equivalence preserves their squared
Hellinger distance. -/
@[simp]
theorem sqHellinger_map (e : α ≃ᵐ β) (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    sqHellinger (P.map e) (Q.map e) = sqHellinger P Q :=
  e.measurableEmbedding.sqHellinger_map P Q

end MeasurableEquiv
