/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Entropic.Basic

import TauCeti.InformationTheory.KullbackLeibler.Basic
import TauCeti.MeasureTheory.Integral.Bochner.WithDensity
import TauCeti.MeasureTheory.Measure.Decomposition.Prod
import TauCeti.MeasureTheory.Measure.Prod

/-!
# Four-point cyclic perturbations of Schrödinger minimizers

Let `μ` and `ν` be finite measures on measurable spaces `X` and `Y`, and let `R` be a finite
reference measure on `X × Y` mutually absolutely continuous with respect to `μ.prod ν`. Given a
coupling `γ` of `μ` and `ν` with `klDiv γ R ≠ ∞` that minimizes `klDiv · R`, bounded four-point
cyclic perturbations move mass from `(x₁, y₂)` and `(x₂, y₁)` to `(x₁, y₁)` and `(x₂, y₂)` without
changing either marginal. Truncating onto integer annuli where `dR / d(μ ⊗ ν)` and `dγ / dR` lie in
`[(n + 1)⁻¹, n + 1]` expands `klDiv · R` without any uniform bound on `llr R (μ.prod ν)`:

* shifting mass onto `{dγ / dR = 0}` from positive-density cross-points would give an `O(t log t)`
  entropy drop dominating the `O(t)` cost on positive-density points, forcing `R ≪ γ`;
* signed first variations on positive-density annuli force the four-point cross-difference of
  `llr γ R` to vanish `(μ ⊗ ν) ⊗ (μ ⊗ ν)`-almost everywhere.

These two results feed `TauCeti/MeasureTheory/OptimalTransport/Entropic/Potentials.lean`.

## Main statements

* `TauCeti.IsCoupling.absolutelyContinuous_of_forall_klDiv_le`: for finite `μ` and `R` with
  `R ∼ μ ⊗ ν`, any finite-entropy coupling `γ` minimizing `klDiv · R` satisfies `R ≪ γ`.
* `TauCeti.IsCoupling.ae_llr_add_llr_eq_of_forall_klDiv_le`: under the same hypotheses,
  `llr γ R q.1 + llr γ R q.2 = llr γ R (q.1.1, q.2.2) + llr γ R (q.2.1, q.1.2)` for
  `(μ.prod ν).prod (μ.prod ν)`-almost every `q`.

## References

* M. Nutz, *Introduction to Entropic Optimal Transport*, lecture notes, Columbia University, 2021,
  Theorem 2.1.
* L. Rüschendorf and W. Thomsen, *Note on the Schrödinger equation and I-projections*, Statist.
  Probab. Lett. 17 (1993), 369–375.
* I. Csiszár, *I-divergence geometry of probability distributions and minimization problems*, Ann.
  Probab. 3 (1975), 146–158.
-/

public section

noncomputable section

open MeasureTheory InformationTheory Set
open Real (exp log exp_pos log_exp log_zero log_le_log log_inv log_nonneg)
open scoped ENNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} {R γ : Measure (X × Y)}

/-! ### Four-point cyclic perturbations of densities -/

section FourPoint

private def fourPointDelta (μ : Measure X) (ν : Measure Y)
    (W : (X × Y) × (X × Y) → ℝ) (z : X × Y) : ℝ :=
  (∫ w, W (z, w) ∂μ.prod ν + ∫ w, W (w, z) ∂μ.prod ν) -
    (∫ w, W (prodProdSndComm (z, w)) ∂μ.prod ν + ∫ w, W (prodProdSndComm (w, z)) ∂μ.prod ν)

private theorem measurable_fourPointDelta [SFinite μ] [SFinite ν]
    {W : (X × Y) × (X × Y) → ℝ} (hW : Measurable W) :
    Measurable (fourPointDelta μ ν W) :=
  (hW.stronglyMeasurable.integral_prod_right'.measurable.add
    (hW.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable).sub
    ((hW.comp prodProdSndComm.measurable).stronglyMeasurable.integral_prod_right'.measurable.add
      (hW.comp (prodProdSndComm.measurable.comp
        measurable_swap)).stronglyMeasurable.integral_prod_right'.measurable)

private theorem abs_integral_le_measureReal_univ [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : X × Y → ℝ} (hf : ∀ w, |f w| ≤ 1) :
    |∫ w, f w ∂μ.prod ν| ≤ (μ.prod ν).real univ := by
  rw [← Real.norm_eq_abs]
  exact (norm_integral_le_of_norm_le_const
    (ae_of_all _ fun w ↦ by simpa [Real.norm_eq_abs] using hf w)).trans_eq (one_mul _)

private theorem abs_fourPointDelta_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {W : (X × Y) × (X × Y) → ℝ} (hWB : ∀ q, |W q| ≤ 1) (z : X × Y) :
    |fourPointDelta μ ν W z| ≤ 4 * (μ.prod ν).real univ := by
  have h1 := abs_integral_le_measureReal_univ (μ := μ) (ν := ν) fun w ↦ hWB (z, w)
  have h2 := abs_integral_le_measureReal_univ (μ := μ) (ν := ν) fun w ↦ hWB (w, z)
  have h3 := abs_integral_le_measureReal_univ (μ := μ) (ν := ν) fun w ↦
    hWB (prodProdSndComm (z, w))
  have h4 := abs_integral_le_measureReal_univ (μ := μ) (ν := ν) fun w ↦
    hWB (prodProdSndComm (w, z))
  unfold fourPointDelta
  linarith [abs_sub ((∫ w, W (z, w) ∂μ.prod ν) + ∫ w, W (w, z) ∂μ.prod ν)
      ((∫ w, W (prodProdSndComm (z, w)) ∂μ.prod ν) + ∫ w, W (prodProdSndComm (w, z)) ∂μ.prod ν),
    abs_add_le (∫ w, W (z, w) ∂μ.prod ν) (∫ w, W (w, z) ∂μ.prod ν),
    abs_add_le (∫ w, W (prodProdSndComm (z, w)) ∂μ.prod ν)
      (∫ w, W (prodProdSndComm (w, z)) ∂μ.prod ν)]

private theorem integrable_fourPointDelta [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {W : (X × Y) × (X × Y) → ℝ} (hW : Measurable W) (hWB : ∀ q, |W q| ≤ 1) :
    Integrable (fourPointDelta μ ν W) (μ.prod ν) :=
  .of_bound (measurable_fourPointDelta hW).aestronglyMeasurable (4 * (μ.prod ν).real univ)
    (ae_of_all _ fun z ↦ by simpa [Real.norm_eq_abs] using abs_fourPointDelta_le hWB z)

private theorem fourPointDelta_eq_zero_of_notMem {S : Set (X × Y)}
    {W : (X × Y) × (X × Y) → ℝ}
    (hWS : ∀ q, q.1 ∉ S ∨ q.2 ∉ S ∨ (prodProdSndComm q).1 ∉ S ∨ (prodProdSndComm q).2 ∉ S →
      W q = 0) {z : X × Y} (hz : z ∉ S) :
    fourPointDelta μ ν W z = 0 := by
  have h1 (w : X × Y) : W (z, w) = 0 := hWS (z, w) (.inl hz)
  have h2 (w : X × Y) : W (w, z) = 0 := hWS (w, z) (.inr (.inl hz))
  have h3 (w : X × Y) : W (prodProdSndComm (z, w)) = 0 :=
    hWS (prodProdSndComm (z, w)) (.inr (.inr (.inl (by simpa using hz))))
  have h4 (w : X × Y) : W (prodProdSndComm (w, z)) = 0 :=
    hWS (prodProdSndComm (w, z)) (.inr (.inr (.inr (by simpa using hz))))
  simp [fourPointDelta, -prodProdSndComm_apply, h1, h2, h3, h4]

private theorem abs_indicator_one_le {α : Type*} (M : Set α) (q : α) :
    |M.indicator (1 : α → ℝ) q| ≤ 1 := by
  by_cases hq : q ∈ M <;> simp [hq]

private theorem indicator_one_eq_zero_of_notMem_quad {K : Set (X × Y)}
    (M : Set ((X × Y) × (X × Y)))
    (hMK : ∀ q ∈ M, q.1 ∈ K ∧ q.2 ∈ K ∧ (prodProdSndComm q).1 ∈ K ∧ (prodProdSndComm q).2 ∈ K)
    (q : (X × Y) × (X × Y))
    (hq : q.1 ∉ K ∨ q.2 ∉ K ∨ (prodProdSndComm q).1 ∉ K ∨ (prodProdSndComm q).2 ∉ K) :
    M.indicator (1 : (X × Y) × (X × Y) → ℝ) q = 0 :=
  indicator_of_notMem (fun hm ↦ by
    obtain ⟨h1, h2, h3, h4⟩ := hMK q hm
    exact hq.elim (· h1) (·.elim (· h2) (·.elim (· h3) (· h4)))) _

private theorem integral_mul_integral_add_integral_swap [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {V : (X × Y) × (X × Y) → ℝ} (hV : Measurable V) (hVB : ∀ q, |V q| ≤ 1)
    {g : X × Y → ℝ} (hg : Measurable g) {M : ℝ} (hgM : ∀ z, |g z| ≤ M) :
    Integrable (fun z ↦ g z * ((∫ w, V (z, w) ∂μ.prod ν) + ∫ w, V (w, z) ∂μ.prod ν)) (μ.prod ν) ∧
      Integrable (fun q ↦ (g q.1 + g q.2) * V q) ((μ.prod ν).prod (μ.prod ν)) ∧
      ∫ z, g z * ((∫ w, V (z, w) ∂μ.prod ν) + ∫ w, V (w, z) ∂μ.prod ν) ∂μ.prod ν =
        ∫ q, (g q.1 + g q.2) * V q ∂((μ.prod ν).prod (μ.prod ν)) := by
  set P := μ.prod ν
  set Q := P.prod P
  set C := max M 0
  have hC0 : 0 ≤ C := le_max_right M 0
  have hgC (z : X × Y) : |g z| ≤ C := (hgM z).trans (le_max_left M 0)
  have hintQ {h : (X × Y) × (X × Y) → X × Y} (hh : Measurable h) :
      Integrable (fun q ↦ g (h q) * V q) Q :=
    .of_bound (by fun_prop) C <| ae_of_all _ fun q ↦ by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (hgC (h q)) (hVB q) (abs_nonneg _) hC0).trans_eq (mul_one _)
  have hbP (u : X × Y → ℝ) (hu : Measurable u) (huB : ∀ z, |u z| ≤ P.real univ) :
      Integrable (fun z ↦ g z * u z) P :=
    .of_bound (by fun_prop) (C * P.real univ) <| ae_of_all _ fun z ↦ by
      rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul (hgC z) (huB z) (abs_nonneg _) hC0
  have hi1 : Integrable (fun q : (X × Y) × (X × Y) ↦ g q.1 * V q) Q := hintQ measurable_fst
  have hi2 : Integrable (fun q : (X × Y) × (X × Y) ↦ g q.2 * V q) Q := hintQ measurable_snd
  have hp1 := hbP (fun z ↦ ∫ w, V (z, w) ∂P) hV.stronglyMeasurable.integral_prod_right'.measurable
    fun z ↦ abs_integral_le_measureReal_univ fun w ↦ hVB (z, w)
  have hp2 := hbP (fun z ↦ ∫ w, V (w, z) ∂P)
    (hV.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable
    fun z ↦ abs_integral_le_measureReal_univ fun w ↦ hVB (w, z)
  have ht1 : ∫ z, g z * (∫ w, V (z, w) ∂P) ∂P = ∫ q, g q.1 * V q ∂Q := by
    simp_rw [← integral_const_mul]; exact (integral_prod (fun q ↦ g q.1 * V q) hi1).symm
  have ht2 : ∫ z, g z * (∫ w, V (w, z) ∂P) ∂P = ∫ q, g q.2 * V q ∂Q := by
    simp_rw [← integral_const_mul]; exact (integral_prod_symm (fun q ↦ g q.2 * V q) hi2).symm
  refine ⟨by simpa [Pi.add_def, mul_add] using hp1.add hp2,
    by simpa [Pi.add_def, add_mul] using hi1.add hi2, ?_⟩
  simp_rw [mul_add, add_mul]
  rw [integral_add hp1 hp2, ht1, ht2, integral_add hi1 hi2]

/-- Integrating `g * fourPointDelta μ ν W` against `μ ⊗ ν` integrates `W` against the four-point
cross-difference of `g`. -/
private theorem integral_mul_fourPointDelta [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {W : (X × Y) × (X × Y) → ℝ} (hW : Measurable W) (hWB : ∀ q, |W q| ≤ 1)
    {g : X × Y → ℝ} (hg : Measurable g) {M : ℝ} (hgM : ∀ z, |g z| ≤ M) :
    ∫ z, g z * fourPointDelta μ ν W z ∂μ.prod ν =
      ∫ q, (g q.1 + g q.2 - g (prodProdSndComm q).1 - g (prodProdSndComm q).2) * W q
        ∂((μ.prod ν).prod (μ.prod ν)) := by
  obtain ⟨hp12, hi12, ht12⟩ :=
    integral_mul_integral_add_integral_swap (μ := μ) (ν := ν) hW hWB hg hgM
  obtain ⟨hp34, hi34', ht34⟩ := integral_mul_integral_add_integral_swap (μ := μ) (ν := ν)
    (V := fun q ↦ W (prodProdSndComm q)) (by fun_prop) (fun q ↦ hWB (prodProdSndComm q)) hg hgM
  have hinv (q : (X × Y) × (X × Y)) : prodProdSndComm (prodProdSndComm q) = q := by
    simp [prodProdSndComm_apply]
  have hi34 : Integrable (fun q ↦ (g (prodProdSndComm q).1 + g (prodProdSndComm q).2) * W q)
      ((μ.prod ν).prod (μ.prod ν)) :=
    ((measurePreserving_prodProdSndComm (μ := μ) (ν := ν) (μ' := μ) (ν' := ν)).integrable_comp_emb
      prodProdSndComm.measurableEmbedding).1 (by simpa only [Function.comp_def, hinv] using hi34')
  have ht34' : ∫ q, (g q.1 + g q.2) * W (prodProdSndComm q) ∂((μ.prod ν).prod (μ.prod ν)) =
      ∫ q, (g (prodProdSndComm q).1 + g (prodProdSndComm q).2) * W q
        ∂((μ.prod ν).prod (μ.prod ν)) := by
    simpa only [Function.comp_def, hinv] using
      (measurePreserving_prodProdSndComm (μ := μ) (ν := ν) (μ' := μ) (ν' := ν)).integral_comp'
        (fun r ↦ (g (prodProdSndComm r).1 + g (prodProdSndComm r).2) * W r)
  simp_rw [fourPointDelta, mul_sub]
  rw [integral_sub hp12 hp34, ht12, ht34, ht34', ← integral_sub hi12 hi34]
  exact integral_congr_ae (ae_of_all _ fun _ ↦ by ring)

private theorem setIntegral_fourPointDelta_eq_zero [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {W : (X × Y) × (X × Y) → ℝ} (hW : Measurable W) (hWB : ∀ q, |W q| ≤ 1)
    {T : Set (X × Y)} (hT : MeasurableSet T)
    (hcross : ∀ q : (X × Y) × (X × Y),
      T.indicator (1 : X × Y → ℝ) q.1 + T.indicator 1 q.2 -
        T.indicator 1 (prodProdSndComm q).1 - T.indicator 1 (prodProdSndComm q).2 = 0) :
    ∫ z in T, fourPointDelta μ ν W z ∂μ.prod ν = 0 := by
  have hind : ∫ z in T, fourPointDelta μ ν W z ∂μ.prod ν =
      ∫ z, T.indicator (1 : X × Y → ℝ) z * fourPointDelta μ ν W z ∂μ.prod ν := by
    rw [← integral_indicator hT]
    exact integral_congr_ae (ae_of_all _ fun z ↦ by by_cases hz : z ∈ T <;> simp [hz])
  rw [hind, integral_mul_fourPointDelta hW hWB (measurable_one.indicator hT)
    (abs_indicator_one_le T)]
  simp [-prodProdSndComm_apply, hcross]

private theorem setIntegral_fourPointDelta_prod_univ [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {W : (X × Y) × (X × Y) → ℝ} (hW : Measurable W) (hWB : ∀ q, |W q| ≤ 1)
    {s : Set X} (hs : MeasurableSet s) :
    ∫ z in s ×ˢ (univ : Set Y), fourPointDelta μ ν W z ∂μ.prod ν = 0 := by
  refine setIntegral_fourPointDelta_eq_zero hW hWB (hs.prod .univ) fun q ↦ ?_
  have hmem (z : X × Y) : (s ×ˢ (univ : Set Y)).indicator (1 : X × Y → ℝ) z =
      s.indicator 1 z.1 := by by_cases hzs : z.1 ∈ s <;> simp [hzs]
  simp only [hmem, prodProdSndComm_apply]; ring

private theorem setIntegral_fourPointDelta_univ_prod [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {W : (X × Y) × (X × Y) → ℝ} (hW : Measurable W) (hWB : ∀ q, |W q| ≤ 1)
    {u : Set Y} (hu : MeasurableSet u) :
    ∫ z in (univ : Set X) ×ˢ u, fourPointDelta μ ν W z ∂μ.prod ν = 0 := by
  refine setIntegral_fourPointDelta_eq_zero hW hWB (MeasurableSet.univ.prod hu) fun q ↦ ?_
  have hmem (z : X × Y) : ((univ : Set X) ×ˢ u).indicator (1 : X × Y → ℝ) z =
      u.indicator 1 z.2 := by by_cases hzu : z.2 ∈ u <;> simp [hzu]
  simp only [hmem, prodProdSndComm_apply]; ring

private theorem withDensity_add_mul_eq_withDensity_fourPointDelta
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure R]
    (hRμν : R ≪ μ.prod ν) {W : (X × Y) × (X × Y) → ℝ}
    {Z δZ : X × Y → ℝ} (hZ : Measurable Z) (hδZ : Measurable δZ)
    (hδZr : ∀ z, δZ z * (R.rnDeriv (μ.prod ν) z).toReal = fourPointDelta μ ν W z) (t : ℝ) :
    (R.withDensity fun z ↦ ENNReal.ofReal (Z z + t * δZ z)) =
      (μ.prod ν).withDensity fun z ↦
        ENNReal.ofReal (Z z * (R.rnDeriv (μ.prod ν) z).toReal + t * fourPointDelta μ ν W z) := by
  set P := μ.prod ν
  conv_lhs => rw [← Measure.withDensity_ofReal_toReal_rnDeriv_eq R P hRμν]
  rw [← withDensity_mul _ (by fun_prop) (by fun_prop)]
  congr 1; funext z
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  congr 1; rw [← hδZr z]; ring

private theorem integral_mul_eq_integral_mul_fourPointDelta
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure R]
    (hRμν : R ≪ μ.prod ν) {W : (X × Y) × (X × Y) → ℝ} {δZ : X × Y → ℝ}
    (hδZr : ∀ z, δZ z * (R.rnDeriv (μ.prod ν) z).toReal = fourPointDelta μ ν W z) (g : X × Y → ℝ) :
    ∫ z, g z * δZ z ∂R = ∫ z, g z * fourPointDelta μ ν W z ∂μ.prod ν := by
  set P := μ.prod ν
  rw [← Measure.withDensity_rnDeriv_eq R P hRμν,
    integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv R P)
      (Measure.rnDeriv_lt_top R P)]
  exact integral_congr_ae <| ae_of_all _ fun z ↦ by simp only [smul_eq_mul, ← hδZr z]; ring

private theorem isCoupling_withDensity_add_mul_fourPointDelta
    [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hRμν : R ≪ μ.prod ν) (hγ : IsCoupling γ μ ν) (hγR : γ ≪ R)
    {W : (X × Y) × (X × Y) → ℝ} (hW : Measurable W) (hWB : ∀ q, |W q| ≤ 1)
    {δZ : X × Y → ℝ} (hδZ : Measurable δZ)
    (hδZr : ∀ z, δZ z * (R.rnDeriv (μ.prod ν) z).toReal = fourPointDelta μ ν W z)
    {t : ℝ} (hpos : ∀ z, 0 ≤ (γ.rnDeriv R z).toReal + t * δZ z) :
    IsCoupling (R.withDensity fun z ↦ ENNReal.ofReal ((γ.rnDeriv R z).toReal + t * δZ z)) μ ν := by
  have := hγ.isFiniteMeasure
  have := hγ.isFiniteMeasure_right
  set P := μ.prod ν
  set p : X × Y → ℝ := fun z ↦ (γ.rnDeriv R z).toReal * (R.rnDeriv P z).toReal
  -- Express `γ` and its perturbation as integrable nonnegative densities against `P = μ ⊗ ν`.
  have hγ_P : P.withDensity (fun z ↦ ENNReal.ofReal (p z)) = γ := by
    have hmul : (fun z ↦ ENNReal.ofReal (p z)) = (fun z ↦ ENNReal.ofReal (R.rnDeriv P z).toReal) *
        (fun z ↦ ENNReal.ofReal (γ.rnDeriv R z).toReal) := funext fun z ↦ by
      rw [Pi.mul_apply, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, mul_comm]
    rw [hmul, withDensity_mul _ (by fun_prop) (by fun_prop),
      Measure.withDensity_ofReal_toReal_rnDeriv_eq R P hRμν,
      Measure.withDensity_ofReal_toReal_rnDeriv_eq γ R hγR]
  have hp_int : Integrable p P := MeasureTheory.integrable_of_eq_withDensity hγ_P.symm
    (by fun_prop) (ae_of_all _ fun _ ↦ mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  have hΔ_int : Integrable (fourPointDelta μ ν W) P := integrable_fourPointDelta hW hWB
  have hpt_int : Integrable (fun z ↦ p z + t * fourPointDelta μ ν W z) P :=
    hp_int.add (hΔ_int.const_mul t)
  have hpt_nn (z : X × Y) : 0 ≤ p z + t * fourPointDelta μ ν W z := by
    have hmul : p z + t * fourPointDelta μ ν W z =
        ((γ.rnDeriv R z).toReal + t * δZ z) * (R.rnDeriv P z).toReal := by
      dsimp only [p]; rw [← hδZr z]; ring
    exact hmul ▸ mul_nonneg (hpos z) ENNReal.toReal_nonneg
  -- Any measurable set on which `fourPointDelta` has zero integral keeps its `γ`-mass.
  have hrect {T : Set (X × Y)} (hT : MeasurableSet T)
      (hvanish : ∫ z in T, fourPointDelta μ ν W z ∂P = 0) :
      (P.withDensity fun z ↦ ENNReal.ofReal (p z + t * fourPointDelta μ ν W z)) T = γ T := by
    rw [withDensity_apply _ hT, ← ofReal_integral_eq_lintegral_ofReal hpt_int.integrableOn
        (ae_of_all _ hpt_nn),
      integral_add hp_int.integrableOn (hΔ_int.const_mul t).integrableOn, integral_const_mul,
      hvanish, mul_zero, add_zero, ofReal_integral_eq_lintegral_ofReal hp_int.integrableOn
        (ae_of_all _ fun _ ↦ mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
      ← withDensity_apply _ hT, hγ_P]
  rw [withDensity_add_mul_eq_withDensity_fourPointDelta hRμν
    (Measure.measurable_rnDeriv γ R).ennreal_toReal hδZ hδZr t]
  exact isCoupling_of_measure_prod_univ_of_measure_univ_prod
    (fun s hs ↦ (hrect (hs.prod .univ) (setIntegral_fourPointDelta_prod_univ hW hWB hs)).trans
      (hγ.measure_prod_univ hs))
    (fun u hu ↦ (hrect (MeasurableSet.univ.prod hu)
      (setIntegral_fourPointDelta_univ_prod hW hWB hu)).trans (hγ.measure_univ_prod hu))

private def scaledFourPointDelta (μ : Measure X) (ν : Measure Y) (R : Measure (X × Y))
    (S : Set (X × Y)) (W : (X × Y) × (X × Y) → ℝ) : X × Y → ℝ :=
  S.indicator fun z ↦ fourPointDelta μ ν W z / (R.rnDeriv (μ.prod ν) z).toReal

private theorem measurable_scaledFourPointDelta [SFinite μ] [SFinite ν]
    {S : Set (X × Y)} (hS : MeasurableSet S) {W : (X × Y) × (X × Y) → ℝ} (hW : Measurable W) :
    Measurable (scaledFourPointDelta μ ν R S W) :=
  ((measurable_fourPointDelta hW).div
    (Measure.measurable_rnDeriv R (μ.prod ν)).ennreal_toReal).indicator hS

private theorem scaledFourPointDelta_mul_rnDeriv
    {S : Set (X × Y)} {W : (X × Y) × (X × Y) → ℝ}
    (hrS : ∀ z ∈ S, 0 < (R.rnDeriv (μ.prod ν) z).toReal)
    (hWS : ∀ q, q.1 ∉ S ∨ q.2 ∉ S ∨ (prodProdSndComm q).1 ∉ S ∨ (prodProdSndComm q).2 ∉ S →
      W q = 0) (z : X × Y) :
    scaledFourPointDelta μ ν R S W z * (R.rnDeriv (μ.prod ν) z).toReal =
      fourPointDelta μ ν W z := by
  by_cases hz : z ∈ S
  · simp [scaledFourPointDelta, indicator_of_mem hz, div_mul_cancel₀ _ (hrS z hz).ne']
  · simp [scaledFourPointDelta, indicator_of_notMem hz, fourPointDelta_eq_zero_of_notMem hWS hz]

private theorem abs_scaledFourPointDelta_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Set (X × Y)} {W : (X × Y) × (X × Y) → ℝ} (hWB : ∀ q, |W q| ≤ 1)
    {c : ℝ} (hc : 0 < c) (hrS : ∀ z ∈ S, c⁻¹ ≤ (R.rnDeriv (μ.prod ν) z).toReal) (z : X × Y) :
    |scaledFourPointDelta μ ν R S W z| ≤ 4 * c * (μ.prod ν).real univ := by
  by_cases hz : z ∈ S
  · have hrpos : 0 < (R.rnDeriv (μ.prod ν) z).toReal := (inv_pos.2 hc).trans_le (hrS z hz)
    simp only [scaledFourPointDelta, indicator_of_mem hz]
    rw [abs_div, abs_of_pos hrpos, div_le_iff₀ hrpos]
    calc |fourPointDelta μ ν W z| ≤ 4 * (μ.prod ν).real univ := abs_fourPointDelta_le hWB z
      _ = 4 * (μ.prod ν).real univ * (c⁻¹ * c) := by rw [inv_mul_cancel₀ hc.ne', mul_one]
      _ ≤ 4 * (μ.prod ν).real univ * ((R.rnDeriv (μ.prod ν) z).toReal * c) := by
          gcongr; exact hrS z hz
      _ = 4 * c * (μ.prod ν).real univ * (R.rnDeriv (μ.prod ν) z).toReal := by ring
  · simp only [scaledFourPointDelta, indicator_of_notMem hz, abs_zero]; positivity

private theorem integrable_and_integral_klFun_scaledFourPointDelta_nonneg
    [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hRμν : R ≪ μ.prod ν) (hγ : IsCoupling γ μ ν) (hKL : klDiv γ R ≠ ∞)
    (hmin : ∀ γ', IsCoupling γ' μ ν → klDiv γ R ≤ klDiv γ' R)
    {K : Set (X × Y)} (hK : MeasurableSet K) {M : Set ((X × Y) × (X × Y))} (hM : MeasurableSet M)
    (hMK : ∀ q ∈ M, q.1 ∈ K ∧ q.2 ∈ K ∧ (prodProdSndComm q).1 ∈ K ∧ (prodProdSndComm q).2 ∈ K)
    {c M₀ : ℝ} (hc : 0 < c) (hrK : ∀ z ∈ K, c⁻¹ ≤ (R.rnDeriv (μ.prod ν) z).toReal)
    (hZK : ∀ z ∈ K, (γ.rnDeriv R z).toReal ≤ M₀) {s : ℝ}
    (hpos : ∀ z, 0 ≤ (γ.rnDeriv R z).toReal + s * scaledFourPointDelta μ ν R K (M.indicator 1) z) :
    Integrable (fun z ↦
        klFun ((γ.rnDeriv R z).toReal + s * scaledFourPointDelta μ ν R K (M.indicator 1) z) -
          klFun (γ.rnDeriv R z).toReal) R ∧
      0 ≤ ∫ z, (klFun ((γ.rnDeriv R z).toReal +
          s * scaledFourPointDelta μ ν R K (M.indicator 1) z) -
        klFun (γ.rnDeriv R z).toReal) ∂R := by
  have := hγ.isFiniteMeasure
  have := hγ.isFiniteMeasure_right
  obtain ⟨hγR, hllr⟩ := klDiv_ne_top_iff.1 hKL
  set W : (X × Y) × (X × Y) → ℝ := M.indicator 1
  set δZ : X × Y → ℝ := scaledFourPointDelta μ ν R K W
  set Zs : X × Y → ℝ := fun z ↦ (γ.rnDeriv R z).toReal + s * δZ z
  have hδZ_meas : Measurable δZ := measurable_scaledFourPointDelta hK (measurable_one.indicator hM)
  have hZs_meas : Measurable Zs :=
    (Measure.measurable_rnDeriv γ R).ennreal_toReal.add (hδZ_meas.const_mul s)
  have hδZr (z : X × Y) : δZ z * (R.rnDeriv (μ.prod ν) z).toReal = fourPointDelta μ ν W z :=
    scaledFourPointDelta_mul_rnDeriv (fun w hw ↦ (inv_pos.2 hc).trans_le (hrK w hw))
      (indicator_one_eq_zero_of_notMem_quad M hMK) z
  have hγs : IsCoupling (R.withDensity fun z ↦ ENNReal.ofReal (Zs z)) μ ν :=
    isCoupling_withDensity_add_mul_fourPointDelta hRμν hγ hγR (measurable_one.indicator hM)
      (abs_indicator_one_le M) hδZ_meas hδZr hpos
  have hklZ : Integrable (fun z ↦ klFun (γ.rnDeriv R z).toReal) R :=
    (integrable_klFun_rnDeriv_iff hγR).2 hllr
  have hklZs : Integrable (fun z ↦ klFun (Zs z)) R := by
    refine integrable_klFun_of_ae_eq_or_le (M := M₀ + |s| * (4 * c * (μ.prod ν).real univ))
      hZs_meas.aemeasurable (ae_of_all _ hpos) hklZ (ae_of_all _ fun z ↦ ?_)
    by_cases hz : z ∈ K
    · have hsB := (le_abs_self (s * δZ z)).trans <| (abs_mul s (δZ z)).trans_le <|
        mul_le_mul_of_nonneg_left (abs_scaledFourPointDelta_le (abs_indicator_one_le M) hc hrK z)
          (abs_nonneg s)
      exact .inr (by linarith [hZK z hz])
    · exact .inl (by simp [Zs, δZ, scaledFourPointDelta, indicator_of_notMem hz])
  have hKL_eq := klDiv_withDensity_ofReal_eq hZs_meas.aemeasurable (ae_of_all _ hpos) hklZs
  refine ⟨hklZs.sub hklZ, ?_⟩
  rw [integral_sub hklZs hklZ, ← toReal_klDiv_eq_integral_klFun hγR, sub_nonneg]
  exact (ENNReal.le_ofReal_iff_toReal_le hKL
    (integral_nonneg fun z ↦ klFun_nonneg (hpos z))).1 (hKL_eq ▸ hmin _ hγs)

private def rnAnnulus (μ : Measure X) (ν : Measure Y) (R : Measure (X × Y)) (n : ℕ) : Set (X × Y) :=
  {z | ((n : ℝ) + 1)⁻¹ ≤ (R.rnDeriv (μ.prod ν) z).toReal ∧
    (R.rnDeriv (μ.prod ν) z).toReal ≤ (n : ℝ) + 1}

private def jointAnnulus (μ : Measure X) (ν : Measure Y) (R γ : Measure (X × Y)) (n : ℕ) :
    Set (X × Y) :=
  rnAnnulus μ ν R n ∩
    {z | ((n : ℝ) + 1)⁻¹ ≤ (γ.rnDeriv R z).toReal ∧ (γ.rnDeriv R z).toReal ≤ (n : ℝ) + 1}

private def rnZeroSet (μ : Measure X) (ν : Measure Y) (R γ : Measure (X × Y)) (n : ℕ) :
    Set (X × Y) :=
  rnAnnulus μ ν R n ∩ {z | (γ.rnDeriv R z).toReal = 0}

private theorem measurableSet_rnAnnulus (n : ℕ) : MeasurableSet (rnAnnulus μ ν R n) :=
  (measurableSet_le measurable_const (Measure.measurable_rnDeriv R _).ennreal_toReal).inter
    (measurableSet_le (Measure.measurable_rnDeriv R _).ennreal_toReal measurable_const)

private theorem measurableSet_jointAnnulus (n : ℕ) : MeasurableSet (jointAnnulus μ ν R γ n) :=
  (measurableSet_rnAnnulus n).inter <|
    (measurableSet_le measurable_const (Measure.measurable_rnDeriv γ R).ennreal_toReal).inter
      (measurableSet_le (Measure.measurable_rnDeriv γ R).ennreal_toReal measurable_const)

private theorem measurableSet_rnZeroSet (n : ℕ) : MeasurableSet (rnZeroSet μ ν R γ n) :=
  (measurableSet_rnAnnulus n).inter
    (measurableSet_eq_fun (Measure.measurable_rnDeriv γ R).ennreal_toReal measurable_const)

private theorem rnDeriv_pos_of_mem_rnAnnulus {n : ℕ} {z : X × Y}
    (hz : z ∈ rnAnnulus μ ν R n) : 0 < (R.rnDeriv (μ.prod ν) z).toReal :=
  (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹).trans_le hz.1

private theorem rnDeriv_pos_of_mem_jointAnnulus {n : ℕ} {z : X × Y}
    (hz : z ∈ jointAnnulus μ ν R γ n) : 0 < (γ.rnDeriv R z).toReal :=
  (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹).trans_le hz.2.1

private theorem monotone_rnAnnulus : Monotone (rnAnnulus μ ν R) := fun m n hmn _ hz ↦ by
  have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
  exact ⟨(inv_anti₀ (by positivity) hmn').trans hz.1, hz.2.trans hmn'⟩

private theorem monotone_jointAnnulus : Monotone (jointAnnulus μ ν R γ) := fun m n hmn _ hz ↦ by
  have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
  exact ⟨monotone_rnAnnulus hmn hz.1, (inv_anti₀ (by positivity) hmn').trans hz.2.1,
    hz.2.2.trans hmn'⟩

private theorem exists_mem_rnAnnulus {z : X × Y} (hr : 0 < (R.rnDeriv (μ.prod ν) z).toReal) :
    ∃ n, z ∈ rnAnnulus μ ν R n := by
  obtain ⟨n, hn⟩ := exists_nat_ge
    (max ((R.rnDeriv (μ.prod ν) z).toReal)⁻¹ (R.rnDeriv (μ.prod ν) z).toReal)
  have hn1 := hn.trans (le_add_of_nonneg_right zero_le_one)
  exact ⟨n, (inv_le_comm₀ (by positivity) hr).2 ((le_max_left _ _).trans hn1),
    (le_max_right _ _).trans hn1⟩

private theorem exists_mem_jointAnnulus {z : X × Y}
    (hr : 0 < (R.rnDeriv (μ.prod ν) z).toReal) (hZ : 0 < (γ.rnDeriv R z).toReal) :
    ∃ n, z ∈ jointAnnulus μ ν R γ n := by
  obtain ⟨n₁, hn₁⟩ := exists_mem_rnAnnulus hr
  obtain ⟨n₂, hn₂⟩ := exists_nat_ge (max ((γ.rnDeriv R z).toReal)⁻¹ (γ.rnDeriv R z).toReal)
  have hn2 : max ((γ.rnDeriv R z).toReal)⁻¹ (γ.rnDeriv R z).toReal ≤ ((max n₁ n₂ : ℕ) : ℝ) + 1 :=
    (hn₂.trans (le_add_of_nonneg_right zero_le_one)).trans
      (by exact_mod_cast Nat.add_le_add_right (le_max_right n₁ n₂) 1)
  exact ⟨max n₁ n₂, monotone_rnAnnulus (le_max_left n₁ n₂) hn₁,
    (inv_le_comm₀ (by positivity) hZ).2 ((le_max_left _ _).trans hn2),
    (le_max_right _ _).trans hn2⟩

private theorem add_mul_nonneg_of_mem_jointAnnulus {n : ℕ} {z : X × Y}
    (hz : z ∈ jointAnnulus μ ν R γ n) {s u B : ℝ} (hB0 : 0 ≤ B) (hu : |u| ≤ B)
    (hs : |s| ≤ (((n : ℝ) + 1) * (B + 1))⁻¹) : 0 ≤ (γ.rnDeriv R z).toReal + s * u := by
  have hstep : |s| * |u| ≤ ((n : ℝ) + 1)⁻¹ :=
    (mul_le_mul hs (hu.trans (le_add_of_nonneg_right zero_le_one)) (abs_nonneg _)
      (inv_nonneg.2 (by positivity))).trans_eq
      (by rw [mul_inv, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one])
  linarith [hz.2.1, neg_abs_le (s * u), abs_mul s u, hstep]

private theorem abs_indicator_llr_jointAnnulus_le (n : ℕ) (z : X × Y) :
    |(jointAnnulus μ ν R γ n).indicator (llr γ R) z| ≤ log ((n : ℝ) + 1) := by
  by_cases hz : z ∈ jointAnnulus μ ν R γ n
  · simp only [indicator_of_mem hz, llr_def]
    exact abs_le.2 ⟨by rw [← log_inv]; exact log_le_log (by positivity) hz.2.1,
      log_le_log (rnDeriv_pos_of_mem_jointAnnulus hz) hz.2.2⟩
  · simp only [indicator_of_notMem hz, abs_zero]
    exact log_nonneg (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1)

private theorem klFun_add_mul_sub_klFun_le_of_jointAnnulus {n : ℕ} {z : X × Y}
    {s u B : ℝ} (hB0 : 0 ≤ B) (hu : |u| ≤ B) (huH : z ∉ jointAnnulus μ ν R γ n → u = 0)
    (hZs : 0 ≤ (γ.rnDeriv R z).toReal + s * u) :
    klFun ((γ.rnDeriv R z).toReal + s * u) - klFun (γ.rnDeriv R z).toReal ≤
      s * ((jointAnnulus μ ν R γ n).indicator (llr γ R) z * u) +
        s ^ 2 * (((n : ℝ) + 1) * B ^ 2) := by
  by_cases hz : z ∈ jointAnnulus μ ν R γ n
  · have hquad := klFun_sub_klFun_sub_le_sq_div (rnDeriv_pos_of_mem_jointAnnulus hz) hZs
    rw [add_sub_cancel_left] at hquad
    have h1 := div_le_div_of_nonneg_left (sq_nonneg (s * u)) (by positivity) hz.2.1
    have h2 : (s * u) ^ 2 / ((n : ℝ) + 1)⁻¹ = s ^ 2 * ((n : ℝ) + 1) * u ^ 2 := by
      rw [div_inv_eq_mul]; ring
    have hu2 : u ^ 2 ≤ B ^ 2 := sq_le_sq.2 (hu.trans_eq (abs_of_nonneg hB0).symm)
    have hsq : (s * u) ^ 2 / (γ.rnDeriv R z).toReal ≤ s ^ 2 * (((n : ℝ) + 1) * B ^ 2) := by
      linarith [mul_le_mul_of_nonneg_left hu2 (by positivity : 0 ≤ s ^ 2 * ((n : ℝ) + 1))]
    simp only [indicator_of_mem hz, llr_def]; linarith
  · simp only [huH hz, mul_zero, add_zero, sub_self]; positivity

end FourPoint

/-! ### Mutual absolute continuity of the Schrödinger minimizer -/

section Positivity

private def posDensitySet (μ : Measure X) (ν : Measure Y) (R γ : Measure (X × Y)) : Set (X × Y) :=
  {z | 0 < (R.rnDeriv (μ.prod ν) z).toReal ∧ 0 < (γ.rnDeriv R z).toReal}

private def fourPointZeroConfig (μ : Measure X) (ν : Measure Y) (R γ : Measure (X × Y)) (n : ℕ) :
    Set ((X × Y) × (X × Y)) :=
  {q | q.1 ∈ rnZeroSet μ ν R γ n ∧ q.2 ∈ rnZeroSet μ ν R γ n ∪ jointAnnulus μ ν R γ n ∧
    (prodProdSndComm q).1 ∈ jointAnnulus μ ν R γ n ∧
    (prodProdSndComm q).2 ∈ jointAnnulus μ ν R γ n}

private theorem measurableSet_fourPointZeroConfig (n : ℕ) :
    MeasurableSet (fourPointZeroConfig μ ν R γ n) :=
  (measurable_fst (measurableSet_rnZeroSet n)).inter <|
    (measurable_snd ((measurableSet_rnZeroSet n).union (measurableSet_jointAnnulus n))).inter <|
      ((measurable_fst.comp prodProdSndComm.measurable) (measurableSet_jointAnnulus n)).inter
        ((measurable_snd.comp prodProdSndComm.measurable) (measurableSet_jointAnnulus n))

private theorem fourPointZeroConfig_subset_quad (n : ℕ) :
    ∀ q ∈ fourPointZeroConfig μ ν R γ n,
      q.1 ∈ rnZeroSet μ ν R γ n ∪ jointAnnulus μ ν R γ n ∧
        q.2 ∈ rnZeroSet μ ν R γ n ∪ jointAnnulus μ ν R γ n ∧
        (prodProdSndComm q).1 ∈ rnZeroSet μ ν R γ n ∪ jointAnnulus μ ν R γ n ∧
        (prodProdSndComm q).2 ∈ rnZeroSet μ ν R γ n ∪ jointAnnulus μ ν R γ n :=
  fun _ hq ↦ ⟨.inl hq.1, hq.2.1, .inr hq.2.2.1, .inr hq.2.2.2⟩

private theorem IsCoupling.ae_section_pos_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hγ : IsCoupling γ μ ν) (hRμν : R ≪ μ.prod ν) (hμνR : μ.prod ν ≪ R) (hγR : γ ≪ R) :
    (∀ᵐ x ∂μ, ν (Prod.mk x ⁻¹' posDensitySet μ ν R γ) ≠ 0) ∧
      (∀ᵐ y ∂ν, μ {x | (x, y) ∈ posDensitySet μ ν R γ} ≠ 0) := by
  have := hγ.isFiniteMeasure
  have := hγ.isFiniteMeasure_right
  set P := μ.prod ν
  have hγP : γ ≪ P := hγR.trans hRμν
  have hrn_zero : ∀ᵐ z ∂P, z ∉ posDensitySet μ ν R γ → γ.rnDeriv P z = 0 := by
    filter_upwards [(Measure.rnDeriv_mul_rnDeriv hγR).symm,
      hμνR.ae_le (Measure.rnDeriv_lt_top γ R), Measure.rnDeriv_lt_top R P] with z hch hZlt hrlt hz
    rw [hch, Pi.mul_apply]
    by_cases hr0 : (R.rnDeriv P z).toReal ≤ 0
    · rw [((ENNReal.toReal_eq_zero_iff _).1 (le_antisymm hr0 ENNReal.toReal_nonneg)).resolve_right
        hrlt.ne, mul_zero]
    · have h0 := le_antisymm (not_lt.1 fun hZp ↦ hz ⟨not_le.1 hr0, hZp⟩) ENNReal.toReal_nonneg
      rw [((ENNReal.toReal_eq_zero_iff _).1 h0).resolve_right hZlt.ne, zero_mul]
  refine ⟨?_, ?_⟩
  · filter_upwards [Measure.ae_lintegral_rnDeriv_prod_right_eq_one hγ.fst_eq hγP,
      Measure.ae_ae_of_ae_prod hrn_zero] with x h1 hx h0
    have hzero : ∀ᵐ y ∂ν, γ.rnDeriv P (x, y) = 0 := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0, hx] with y hy hxy using hxy hy
    rw [lintegral_congr_ae hzero, lintegral_zero] at h1; exact zero_ne_one h1
  · filter_upwards [Measure.ae_lintegral_rnDeriv_prod_left_eq_one hγ.snd_eq hγP,
      Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae
        hrn_zero)] with y h1 hy h0
    have hzero : ∀ᵐ x ∂μ, γ.rnDeriv P (x, y) = 0 := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0, hy] with x hx hyx using hyx hx
    rw [lintegral_congr_ae hzero, lintegral_zero] at h1; exact zero_ne_one h1

private theorem measure_untruncatedFourPointZeroSet_ne_zero [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hRμν : R ≪ μ.prod ν) (hμνR : μ.prod ν ≪ R) (hγ : IsCoupling γ μ ν) (hγR : γ ≪ R)
    (hN : μ.prod ν {z | (γ.rnDeriv R z).toReal = 0} ≠ 0) :
    ((μ.prod ν).prod (μ.prod ν))
      {q | (0 < (R.rnDeriv (μ.prod ν) q.1).toReal ∧ (γ.rnDeriv R q.1).toReal = 0) ∧
        0 < (R.rnDeriv (μ.prod ν) q.2).toReal ∧
        (prodProdSndComm q).1 ∈ posDensitySet μ ν R γ ∧
        (prodProdSndComm q).2 ∈ posDensitySet μ ν R γ} ≠ 0 := by
  intro hQU
  have := hγ.isFiniteMeasure_right
  set P := μ.prod ν
  set r : X × Y → ℝ := fun z ↦ (R.rnDeriv P z).toReal
  set Z : X × Y → ℝ := fun z ↦ (γ.rnDeriv R z).toReal
  set S := posDensitySet μ ν R γ
  -- Almost every row and column meets `S = posDensitySet`, and `r = dR/dP > 0` `P`-a.e.
  obtain ⟨hS_row, hS_col⟩ := hγ.ae_section_pos_of_ac hRμν hμνR hγR
  have hr_pos : ∀ᵐ z ∂P, 0 < r z := by
    filter_upwards [Measure.rnDeriv_pos' hμνR, Measure.rnDeriv_lt_top R P]
      with _ hpos hlt using ENNReal.toReal_pos hpos.ne' hlt.ne
  have hr_meas : Measurable r := by fun_prop
  have hZ_meas : Measurable Z := by fun_prop
  have hS_meas : MeasurableSet S :=
    (measurableSet_lt measurable_const hr_meas).inter (measurableSet_lt measurable_const hZ_meas)
  -- By Tonelli on `P ⊗ P`, `(P ⊗ P) U = 0` means `P`-a.e. `z₁`-slice of `U` is `P`-null.
  set U : Set ((X × Y) × (X × Y)) :=
    {q | (0 < r q.1 ∧ Z q.1 = 0) ∧ 0 < r q.2 ∧
      (prodProdSndComm q).1 ∈ S ∧ (prodProdSndComm q).2 ∈ S}
  have hU_meas : MeasurableSet U :=
    ((measurableSet_lt measurable_const (hr_meas.comp measurable_fst)).inter
      (measurable_fst (measurableSet_eq_fun hZ_meas measurable_const))).inter <|
      (measurableSet_lt measurable_const (hr_meas.comp measurable_snd)).inter <|
        ((measurable_fst.comp prodProdSndComm.measurable) hS_meas).inter
          ((measurable_snd.comp prodProdSndComm.measurable) hS_meas)
  rw [Measure.prod_apply hU_meas, lintegral_eq_zero_iff (measurable_measure_prodMk_left hU_meas)]
    at hQU
  -- For `z₁` with `0 < r z₁` and `Z z₁ = 0`, the cross-section rectangle in `S` is covered by
  -- the null `z₁`-slice of `U` together with `{r ≤ 0}`, contradicting `hS_row` and `hS_col`.
  have hae : ∀ᵐ z₁ ∂P, z₁ ∉ {z | 0 < r z ∧ Z z = 0} := by
    filter_upwards [hQU, ae_of_ae_fst hS_row, ae_of_ae_snd hS_col] with z₁ hz₁ hrow hcol hmem
    have hrect : P ({x₂ | (x₂, z₁.2) ∈ S} ×ˢ (Prod.mk z₁.1 ⁻¹' S)) = 0 := by
      refine nonpos_iff_eq_zero.1 <| (measure_mono fun z₂ hz₂ ↦ ?_).trans <|
        (measure_union_le (Prod.mk z₁ ⁻¹' U) {z₂ | ¬ 0 < r z₂}).trans_eq <| by
          rw [hz₁, Pi.zero_apply, ae_iff.1 hr_pos, add_zero]
      exact if hrz₂ : 0 < r z₂ then
        .inl ⟨hmem, hrz₂, by simpa using hz₂.2, by simpa using hz₂.1⟩ else .inr hrz₂
    rw [Measure.prod_prod, mul_eq_zero] at hrect; exact hrect.elim hcol hrow
  -- Combining `hae` with `P {r ≤ 0} = 0` forces `P {Z = 0} = 0`, contradicting `hN`.
  exact hN <| measure_mono_null (fun z hz ↦ if hrz : 0 < r z then Or.inl ⟨hrz, hz⟩ else Or.inr hrz)
    (measure_union_null (measure_eq_zero_iff_ae_notMem.2 hae) (ae_iff.1 hr_pos))

private theorem exists_measure_pos_fourPointZeroConfig [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hRμν : R ≪ μ.prod ν) (hμνR : μ.prod ν ≪ R) (hγ : IsCoupling γ μ ν) (hγR : γ ≪ R)
    (hN : μ.prod ν {z | (γ.rnDeriv R z).toReal = 0} ≠ 0) :
    ∃ n : ℕ, ((μ.prod ν).prod (μ.prod ν)) (fourPointZeroConfig μ ν R γ n) ≠ 0 := by
  by_contra! hall
  refine measure_untruncatedFourPointZeroSet_ne_zero hRμν hμνR hγ hγR hN ?_
  refine measure_mono_null (fun q ⟨⟨hr1, hN1⟩, hr2, hS1, hS2⟩ ↦ ?_) (measure_iUnion_null hall)
  obtain ⟨n₁, hn₁⟩ := exists_mem_rnAnnulus hr1
  obtain ⟨n₂, hn₂⟩ := exists_mem_rnAnnulus hr2
  obtain ⟨n₃, hn₃⟩ := exists_mem_jointAnnulus hS1.1 hS1.2
  obtain ⟨n₄, hn₄⟩ := exists_mem_jointAnnulus hS2.1 hS2.2
  rcases (ENNReal.toReal_nonneg : 0 ≤ (γ.rnDeriv R q.2).toReal).eq_or_lt with hZq2 | hZq2
  · exact mem_iUnion.2 ⟨max (max n₁ n₂) (max n₃ n₄), ⟨monotone_rnAnnulus (by omega) hn₁, hN1⟩,
      .inl ⟨monotone_rnAnnulus (by omega) hn₂, hZq2.symm⟩,
      monotone_jointAnnulus (by omega) hn₃, monotone_jointAnnulus (by omega) hn₄⟩
  · obtain ⟨n₅, hn₅⟩ := exists_mem_jointAnnulus hr2 hZq2
    exact mem_iUnion.2 ⟨max n₅ (max (max n₁ n₂) (max n₃ n₄)),
      ⟨monotone_rnAnnulus (by omega) hn₁, hN1⟩, .inr (monotone_jointAnnulus (by omega) hn₅),
      monotone_jointAnnulus (by omega) hn₃, monotone_jointAnnulus (by omega) hn₄⟩

private theorem disjoint_rnZeroSet_jointAnnulus (n : ℕ) :
    Disjoint (rnZeroSet μ ν R γ n) (jointAnnulus μ ν R γ n) :=
  Set.disjoint_left.2 fun _ hzGN hzH ↦ (rnDeriv_pos_of_mem_jointAnnulus hzH).ne' hzGN.2

private theorem nonneg_and_pos_setIntegral_scaledFourPointDelta_rnZeroSet
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure R] (hRμν : R ≪ μ.prod ν) {n : ℕ}
    (hQM : ((μ.prod ν).prod (μ.prod ν)) (fourPointZeroConfig μ ν R γ n) ≠ 0) :
    (∀ z ∈ rnZeroSet μ ν R γ n, 0 ≤ scaledFourPointDelta μ ν R
      (rnZeroSet μ ν R γ n ∪ jointAnnulus μ ν R γ n)
      ((fourPointZeroConfig μ ν R γ n).indicator 1) z) ∧
    0 < ∫ z in rnZeroSet μ ν R γ n, scaledFourPointDelta μ ν R
      (rnZeroSet μ ν R γ n ∪ jointAnnulus μ ν R γ n)
      ((fourPointZeroConfig μ ν R γ n).indicator 1) z ∂R := by
  set P := μ.prod ν; set GN := rnZeroSet μ ν R γ n; set H := jointAnnulus μ ν R γ n
  set M := fourPointZeroConfig μ ν R γ n; set W : (X × Y) × (X × Y) → ℝ := M.indicator 1
  set δZ := scaledFourPointDelta μ ν R (GN ∪ H) W
  have hGN_meas : MeasurableSet GN := measurableSet_rnZeroSet n
  have hW_meas : Measurable W := measurable_one.indicator (measurableSet_fourPointZeroConfig n)
  -- Pointwise lower bound on `GN`: disjoint from `H`, so cross-terms vanish and `∫ W(w, z) ≥ 0`.
  have hGN_le {z : X × Y} (hz : z ∈ GN) : ∫ w, W (z, w) ∂P ≤ fourPointDelta μ ν W z := by
    have hzH : z ∉ H := Set.disjoint_left.1 (disjoint_rnZeroSet_jointAnnulus n) hz
    have h3 (w : X × Y) : W (prodProdSndComm (z, w)) = 0 :=
      indicator_of_notMem (fun hm : prodProdSndComm (z, w) ∈ M ↦ hzH (by simpa using hm.2.2.1)) _
    have h4 (w : X × Y) : W (prodProdSndComm (w, z)) = 0 :=
      indicator_of_notMem (fun hm : prodProdSndComm (w, z) ∈ M ↦ hzH (by simpa using hm.2.2.2)) _
    have h2 : 0 ≤ ∫ w, W (w, z) ∂P :=
      integral_nonneg fun _ ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) _
    simp only [fourPointDelta, h3, h4, integral_zero, add_zero, sub_zero]; linarith
  -- Nonnegativity of `δZ` on `GN` follows immediately from `hGN_le`.
  have hδZ_nn (z : X × Y) (hz : z ∈ GN) : 0 ≤ δZ z := by
    dsimp only [δZ, scaledFourPointDelta]; rw [indicator_of_mem (mem_union_left H hz)]
    exact div_nonneg ((integral_nonneg fun _ ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) _).trans
      (hGN_le hz)) ENNReal.toReal_nonneg
  -- Change of measure from `R` to `P = μ ⊗ ν` using `δZ * dR/dP = fourPointDelta`.
  have hδZr (z : X × Y) : δZ z * (R.rnDeriv P z).toReal = fourPointDelta μ ν W z :=
    scaledFourPointDelta_mul_rnDeriv
      (fun _ (hw : _ ∈ GN ∪ H) ↦ rnDeriv_pos_of_mem_rnAnnulus (hw.elim And.left And.left))
      (indicator_one_eq_zero_of_notMem_quad M (fourPointZeroConfig_subset_quad n)) z
  have hα_eq : ∫ z in GN, δZ z ∂R = ∫ z in GN, fourPointDelta μ ν W z ∂P := by
    have hmul (f : X × Y → ℝ) : GN.indicator f = fun z ↦ GN.indicator 1 z * f z :=
      funext fun z ↦ by by_cases hz : z ∈ GN <;> simp [hz]
    rw [← integral_indicator hGN_meas, ← integral_indicator hGN_meas, hmul δZ,
      hmul (fourPointDelta μ ν W), integral_mul_eq_integral_mul_fourPointDelta hRμν hδZr]
  -- Fubini on `P ⊗ P`: `W(z, w) = 0` for `z ∉ GN`, so the outer integral restricts to `GN`.
  have hW_int : Integrable W (P.prod P) := Integrable.of_bound hW_meas.aestronglyMeasurable 1
    (ae_of_all _ fun q ↦ by simpa [Real.norm_eq_abs] using abs_indicator_one_le M q)
  have hQ_eq : (P.prod P).real M = ∫ z in GN, (∫ w, W (z, w) ∂P) ∂P := by
    have htot : ∫ q, W q ∂(P.prod P) = (P.prod P).real M :=
      integral_indicator_one (measurableSet_fourPointZeroConfig n)
    rw [← htot, integral_prod W hW_int, ← integral_indicator hGN_meas]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    by_cases hz : z ∈ GN
    · simp [hz]
    · have hw (w : X × Y) : W (z, w) = 0 := indicator_of_notMem (fun hm : (z, w) ∈ M ↦ hz hm.1) _
      simp [hz, hw]
  -- Combine `0 < (P ⊗ P).real M`, `hQ_eq`, `hα_eq`, and `hGN_le`.
  refine ⟨hδZ_nn, (ENNReal.toReal_pos hQM (measure_ne_top (P.prod P) M)).trans_le ?_⟩
  rw [← measureReal_def, hQ_eq, hα_eq]
  exact setIntegral_mono_on hW_int.integral_prod_left.integrableOn
    (integrable_fourPointDelta hW_meas (abs_indicator_one_le M)).integrableOn hGN_meas
    fun _ hz ↦ hGN_le hz

private theorem klFun_add_mul_sub_klFun_le_on_annulus {n : ℕ} {z : X × Y}
    (hz : z ∈ jointAnnulus μ ν R γ n) {u t B : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hB0 : 0 ≤ B) (hu : |u| ≤ B) (hZt0 : 0 ≤ (γ.rnDeriv R z).toReal + t * u) :
    klFun ((γ.rnDeriv R z).toReal + t * u) - klFun (γ.rnDeriv R z).toReal ≤
      t * (B * log ((n : ℝ) + 1) + ((n : ℝ) + 1) * B ^ 2) := by
  have hbase := klFun_add_mul_sub_klFun_le_of_jointAnnulus hB0 hu (fun h ↦ (h hz).elim) hZt0
  have hlin : t * ((jointAnnulus μ ν R γ n).indicator (llr γ R) z * u) ≤
      t * (B * log ((n : ℝ) + 1)) := by
    refine mul_le_mul_of_nonneg_left ((le_abs_self _).trans ?_) ht0.le
    rw [abs_mul, mul_comm]
    exact mul_le_mul hu (abs_indicator_llr_jointAnnulus_le n z) (abs_nonneg _) hB0
  have hsq : t ^ 2 * (((n : ℝ) + 1) * B ^ 2) ≤ t * (((n : ℝ) + 1) * B ^ 2) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  linarith

private theorem setIntegral_klFun_rnZeroSet_le {n : ℕ} {δZ : X × Y → ℝ}
    {t B : ℝ} (ht0 : 0 < t) (hδZ_int : Integrable δZ R)
    (hdiff_int : Integrable (fun z ↦
      klFun ((γ.rnDeriv R z).toReal + t * δZ z) - klFun (γ.rnDeriv R z).toReal) R)
    (hδZ_nn : ∀ z ∈ rnZeroSet μ ν R γ n, 0 ≤ δZ z) (hδZ_abs : ∀ z, |δZ z| ≤ B) :
    ∫ z in rnZeroSet μ ν R γ n,
        (klFun ((γ.rnDeriv R z).toReal + t * δZ z) - klFun (γ.rnDeriv R z).toReal) ∂R ≤
      t * (∫ z in rnZeroSet μ ν R γ n, δZ z ∂R) * (log (t * (B + 1)) - 1) := by
  refine (setIntegral_mono_on hdiff_int.integrableOn
    (hδZ_int.const_mul (t * (log (t * (B + 1)) - 1))).integrableOn
    (measurableSet_rnZeroSet n) fun z hz ↦ ?_).trans_eq (by rw [integral_const_mul]; ring)
  have hZ0 : (γ.rnDeriv R z).toReal = 0 := hz.2
  have hu0 : 0 ≤ δZ z := hδZ_nn z hz
  have huB : δZ z ≤ B + 1 := (le_abs_self _).trans ((hδZ_abs z).trans (by linarith))
  have hkl0 : klFun ((γ.rnDeriv R z).toReal + t * δZ z) - klFun (γ.rnDeriv R z).toReal =
      t * δZ z * log (t * δZ z) - t * δZ z := by
    simp only [hZ0, klFun, log_zero, zero_add]; ring
  rw [hkl0]
  rcases hu0.eq_or_lt with h0 | hup
  · simp [← h0]
  · nlinarith [mul_le_mul_of_nonneg_left
      (log_le_log (mul_pos ht0 hup) (mul_le_mul_of_nonneg_left huB ht0.le))
      (mul_nonneg ht0.le hu0)]

private theorem integral_klFun_rnZeroSet_union_le [IsFiniteMeasure R] {n : ℕ}
    {δZ : X × Y → ℝ} {t B : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hB0 : 0 ≤ B)
    (hδZ_int : Integrable δZ R)
    (hdiff_int : Integrable (fun z ↦
      klFun ((γ.rnDeriv R z).toReal + t * δZ z) - klFun (γ.rnDeriv R z).toReal) R)
    (hδZ_supp : ∀ z ∉ rnZeroSet μ ν R γ n ∪ jointAnnulus μ ν R γ n, δZ z = 0)
    (hδZ_nn : ∀ z ∈ rnZeroSet μ ν R γ n, 0 ≤ δZ z) (hδZ_abs : ∀ z, |δZ z| ≤ B)
    (hZt0 : ∀ z, 0 ≤ (γ.rnDeriv R z).toReal + t * δZ z) :
    ∫ z, (klFun ((γ.rnDeriv R z).toReal + t * δZ z) - klFun (γ.rnDeriv R z).toReal) ∂R ≤
      t * (∫ z in rnZeroSet μ ν R γ n, δZ z ∂R) * (log (t * (B + 1)) - 1) +
        t * ((B * log ((n : ℝ) + 1) + ((n : ℝ) + 1) * B ^ 2) * R.real univ) := by
  set f : X × Y → ℝ := fun z ↦
    klFun ((γ.rnDeriv R z).toReal + t * δZ z) - klFun (γ.rnDeriv R z).toReal
  have htot : ∫ z, f z ∂R =
      (∫ z in rnZeroSet μ ν R γ n, f z ∂R) + ∫ z in jointAnnulus μ ν R γ n, f z ∂R := by
    rw [← setIntegral_union (disjoint_rnZeroSet_jointAnnulus n) (measurableSet_jointAnnulus n)
      hdiff_int.integrableOn hdiff_int.integrableOn, ← integral_indicator
      ((measurableSet_rnZeroSet n).union (measurableSet_jointAnnulus n))]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    by_cases hz : z ∈ rnZeroSet μ ν R γ n ∪ jointAnnulus μ ν R γ n
    · simp [hz]
    · simp [f, hz, hδZ_supp z hz]
  have hbH : ∫ z in jointAnnulus μ ν R γ n, f z ∂R ≤
      t * ((B * log ((n : ℝ) + 1) + ((n : ℝ) + 1) * B ^ 2) * R.real univ) := by
    refine (setIntegral_mono_on hdiff_int.integrableOn (integrable_const _).integrableOn
      (measurableSet_jointAnnulus n) fun z hz ↦ klFun_add_mul_sub_klFun_le_on_annulus hz ht0
        ht1 hB0 (hδZ_abs z) (hZt0 z)).trans ?_
    rw [setIntegral_const, smul_eq_mul, measureReal_def]
    exact (mul_le_mul_of_nonneg_right
      (ENNReal.toReal_mono (measure_ne_top R univ) (measure_mono (subset_univ _)))
      (mul_nonneg ht0.le (add_nonneg (mul_nonneg hB0
        (log_nonneg (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1)))
        (by positivity)))).trans_eq (by rw [measureReal_def]; ring)
  linarith [setIntegral_klFun_rnZeroSet_le ht0 hδZ_int hdiff_int hδZ_nn hδZ_abs]

/-- **Mutual absolute continuity of the Schrödinger minimizer.** When `R ∼ μ ⊗ ν` and `γ` minimizes
`klDiv · R` among couplings of `μ` and `ν` with `klDiv γ R ≠ ∞`, the reference measure `R` is
absolutely continuous with respect to `γ` (so `γ` and `R` are mutually absolutely continuous). -/
theorem IsCoupling.absolutelyContinuous_of_forall_klDiv_le
    [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hγ : IsCoupling γ μ ν) (hRμν : R ≪ μ.prod ν) (hμνR : μ.prod ν ≪ R)
    (hKL : klDiv γ R ≠ ∞)
    (hmin : ∀ γ', IsCoupling γ' μ ν → klDiv γ R ≤ klDiv γ' R) :
    R ≪ γ := by
  have := hγ.isFiniteMeasure
  have := hγ.isFiniteMeasure_right
  obtain ⟨hγR, _⟩ := klDiv_ne_top_iff.1 hKL
  -- Reduce `R ≪ γ` to showing the zero-density set `{z | (dγ/dR z).toReal = 0}` is `μ ⊗ ν`-null.
  suffices hPN : μ.prod ν {z | (γ.rnDeriv R z).toReal = 0} = 0 by
    rw [← Measure.withDensity_rnDeriv_eq γ R hγR]
    refine withDensity_absolutelyContinuous' (Measure.measurable_rnDeriv γ R).aemeasurable ?_
    filter_upwards [hRμν.ae_le (measure_eq_zero_iff_ae_notMem.1 hPN)] with z hz h0
    exact hz (by simp [h0])
  -- By contradiction, pick a positive-measure config and build `δZ` on `rnZeroSet ∪ jointAnnulus`.
  by_contra hPN
  obtain ⟨n, hQM⟩ := exists_measure_pos_fourPointZeroConfig hRμν hμνR hγ hγR hPN
  obtain ⟨hδZ_GN_nn, hα_pos⟩ := nonneg_and_pos_setIntegral_scaledFourPointDelta_rnZeroSet hRμν hQM
  set K := rnZeroSet μ ν R γ n ∪ jointAnnulus μ ν R γ n
  set δZ : X × Y → ℝ := scaledFourPointDelta μ ν R K ((fourPointZeroConfig μ ν R γ n).indicator 1)
  set α := ∫ z in rnZeroSet μ ν R γ n, δZ z ∂R
  have hK_meas : MeasurableSet K := (measurableSet_rnZeroSet n).union (measurableSet_jointAnnulus n)
  set B := 4 * ((n : ℝ) + 1) * (μ.prod ν).real univ
  have hB0 : 0 ≤ B := by positivity
  have hrK (z : X × Y) (hz : z ∈ K) : ((n : ℝ) + 1)⁻¹ ≤ (R.rnDeriv (μ.prod ν) z).toReal :=
    (hz.elim And.left And.left).1
  have hδZ_abs (z : X × Y) : |δZ z| ≤ B :=
    abs_scaledFourPointDelta_le (abs_indicator_one_le _) (by positivity) hrK z
  have hδZ_int : Integrable δZ R := Integrable.of_bound (measurable_scaledFourPointDelta hK_meas
    (measurable_one.indicator (measurableSet_fourPointZeroConfig n))).aestronglyMeasurable B
    (ae_of_all _ fun z ↦ by simpa [Real.norm_eq_abs] using hδZ_abs z)
  -- Pick `t ∈ (0, 1]` keeping `dγ/dR + t * δZ ≥ 0` so the `O(t log t)` gain beats `t * C`.
  set C := (B * log ((n : ℝ) + 1) + ((n : ℝ) + 1) * B ^ 2) * R.real univ
  set t := min 1 (min (((n : ℝ) + 1) * (B + 1))⁻¹ (exp (-(C / α)) / (B + 1)))
  have ht0 : 0 < t := lt_min zero_lt_one
    (lt_min (inv_pos.2 (by positivity)) (div_pos (exp_pos _) (by positivity)))
  have hZt0 (z : X × Y) : 0 ≤ (γ.rnDeriv R z).toReal + t * δZ z := by
    by_cases hz : z ∈ K
    · exact hz.elim (fun h ↦ by rw [h.2, zero_add]; exact mul_nonneg ht0.le (hδZ_GN_nn z h))
        fun h ↦ add_mul_nonneg_of_mem_jointAnnulus h hB0 (hδZ_abs z)
          ((abs_of_pos ht0).trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    · simp [δZ, scaledFourPointDelta, indicator_of_notMem hz]
  -- Optimality of `γ` gives a nonnegative entropy change, contradicting the upper bound at `t`.
  obtain ⟨hdiff_int, hge⟩ := integrable_and_integral_klFun_scaledFourPointDelta_nonneg
    hRμν hγ hKL hmin hK_meas (measurableSet_fourPointZeroConfig n)
    (fourPointZeroConfig_subset_quad n) (by positivity) hrK
    (M₀ := (n : ℝ) + 1) (fun _ hz ↦ hz.elim (fun h ↦ by rw [h.2]; positivity) fun h ↦ h.2.2) hZt0
  have hlog_t : log (t * (B + 1)) ≤ -(C / α) := (log_le_log (mul_pos ht0 (by positivity))
    ((le_div_iff₀ (by positivity)).1 ((min_le_right _ _).trans (min_le_right _ _)))).trans_eq
    (log_exp _)
  have hcancel : α * -(C / α) = -C := by rw [mul_neg, mul_div_cancel₀ C hα_pos.ne']
  have hmul : t * α * (log (t * (B + 1)) - 1) ≤ t * (-C - α) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog_t hα_pos.le]
  linarith [mul_pos ht0 hα_pos, hge, integral_klFun_rnZeroSet_union_le ht0 (min_le_left _ _) hB0
    hδZ_int hdiff_int (fun _ hz ↦ indicator_of_notMem hz _) hδZ_GN_nn hδZ_abs hZt0]

end Positivity

/-! ### Four-point cyclic additivity of the log-likelihood ratio -/

section CyclicAdditivity

private def llrCrossDiff (γ R : Measure (X × Y)) (q : (X × Y) × (X × Y)) : ℝ :=
  llr γ R q.1 + llr γ R q.2 - llr γ R (prodProdSndComm q).1 - llr γ R (prodProdSndComm q).2

private def posDefectConfig (μ : Measure X) (ν : Measure Y) (R γ : Measure (X × Y))
    (n : ℕ) : Set ((X × Y) × (X × Y)) :=
  {q | 0 < llrCrossDiff γ R q ∧ q.1 ∈ jointAnnulus μ ν R γ n ∧
    q.2 ∈ jointAnnulus μ ν R γ n ∧ (prodProdSndComm q).1 ∈ jointAnnulus μ ν R γ n ∧
    (prodProdSndComm q).2 ∈ jointAnnulus μ ν R γ n}

private theorem measurable_llrCrossDiff : Measurable (llrCrossDiff γ R) := by
  unfold llrCrossDiff; fun_prop

private theorem measurableSet_posDefectConfig (n : ℕ) :
    MeasurableSet (posDefectConfig μ ν R γ n) :=
  (measurableSet_lt measurable_const measurable_llrCrossDiff).inter <|
    (measurable_fst (measurableSet_jointAnnulus n)).inter <|
      (measurable_snd (measurableSet_jointAnnulus n)).inter <|
        ((measurable_fst.comp prodProdSndComm.measurable) (measurableSet_jointAnnulus n)).inter
          ((measurable_snd.comp prodProdSndComm.measurable) (measurableSet_jointAnnulus n))

private theorem integral_indicator_llr_mul_scaledFourPointDelta_eq
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure R]
    (hRμν : R ≪ μ.prod ν) (n : ℕ) :
    ∫ z, (jointAnnulus μ ν R γ n).indicator (llr γ R) z *
        scaledFourPointDelta μ ν R (jointAnnulus μ ν R γ n)
          ((posDefectConfig μ ν R γ n).indicator (1 : (X × Y) × (X × Y) → ℝ)) z ∂R =
      ∫ q in posDefectConfig μ ν R γ n, llrCrossDiff γ R q ∂((μ.prod ν).prod (μ.prod ν)) := by
  have hδZr (z : X × Y) := scaledFourPointDelta_mul_rnDeriv (R := R)
    (fun _ (hw : _ ∈ jointAnnulus μ ν R γ n) ↦ rnDeriv_pos_of_mem_rnAnnulus hw.1)
    (indicator_one_eq_zero_of_notMem_quad (posDefectConfig μ ν R γ n) fun _ hm ↦ hm.2) z
  rw [integral_mul_eq_integral_mul_fourPointDelta hRμν hδZr,
    integral_mul_fourPointDelta (measurable_one.indicator (measurableSet_posDefectConfig n))
      (abs_indicator_one_le _) ((measurable_llr γ R).indicator (measurableSet_jointAnnulus n))
      (abs_indicator_llr_jointAnnulus_le n),
    ← integral_indicator (measurableSet_posDefectConfig n)]
  refine integral_congr_ae (ae_of_all _ fun q ↦ ?_)
  by_cases hq : q ∈ posDefectConfig μ ν R γ n
  · simp [llrCrossDiff, -prodProdSndComm_apply, indicator_of_mem hq, indicator_of_mem hq.2.1,
      indicator_of_mem hq.2.2.1, indicator_of_mem hq.2.2.2.1, indicator_of_mem hq.2.2.2.2]
  · simp [indicator_of_notMem hq]

private theorem zero_le_mul_setIntegral_posDefectConfig_add_sq
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure R]
    (hRμν : R ≪ μ.prod ν) (hγ : IsCoupling γ μ ν) (hKL : klDiv γ R ≠ ∞)
    (hmin : ∀ γ', IsCoupling γ' μ ν → klDiv γ R ≤ klDiv γ' R) (n : ℕ) {s : ℝ}
    (hs : |s| ≤ (((n : ℝ) + 1) * (4 * ((n : ℝ) + 1) * (μ.prod ν).real univ + 1))⁻¹) :
    0 ≤ s * ∫ q in posDefectConfig μ ν R γ n, llrCrossDiff γ R q ∂((μ.prod ν).prod (μ.prod ν)) +
      s ^ 2 * (((n : ℝ) + 1) * (4 * ((n : ℝ) + 1) * (μ.prod ν).real univ) ^ 2 * R.real univ) := by
  set H := jointAnnulus μ ν R γ n
  set A := posDefectConfig μ ν R γ n
  set δZ : X × Y → ℝ := scaledFourPointDelta μ ν R H (A.indicator (1 : (X × Y) × (X × Y) → ℝ))
  set g : X × Y → ℝ := H.indicator (llr γ R)
  set B := 4 * ((n : ℝ) + 1) * (μ.prod ν).real univ
  have hB0 : 0 ≤ B := by positivity
  have hδZ_abs (z : X × Y) : |δZ z| ≤ B :=
    abs_scaledFourPointDelta_le (abs_indicator_one_le A) (by positivity)
      (fun _ (hw : _ ∈ H) ↦ hw.1.1) z
  have hZs0 (z : X × Y) : 0 ≤ (γ.rnDeriv R z).toReal + s * δZ z := by
    by_cases hz : z ∈ H
    · exact add_mul_nonneg_of_mem_jointAnnulus hz hB0 (hδZ_abs z) hs
    · simp [δZ, scaledFourPointDelta, indicator_of_notMem hz]
  obtain ⟨hdiff_int, hge⟩ := integrable_and_integral_klFun_scaledFourPointDelta_nonneg
    hRμν hγ hKL hmin (measurableSet_jointAnnulus n) (measurableSet_posDefectConfig n)
    (fun _ hm ↦ hm.2) (by positivity) (fun _ (hw : _ ∈ H) ↦ hw.1.1)
    (fun _ (hw : _ ∈ H) ↦ hw.2.2) hZs0
  have hgδ_int : Integrable (fun z ↦ g z * δZ z) R :=
    Integrable.of_bound (((measurable_llr γ R).indicator (measurableSet_jointAnnulus n)).mul
        (measurable_scaledFourPointDelta (measurableSet_jointAnnulus n)
          (measurable_one.indicator (measurableSet_posDefectConfig n)))).aestronglyMeasurable
      (log ((n : ℝ) + 1) * B) <| ae_of_all _ fun z ↦ by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (abs_indicator_llr_jointAnnulus_le n z) (hδZ_abs z) (abs_nonneg _)
          (log_nonneg (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1))
  refine hge.trans <| (integral_mono hdiff_int ((hgδ_int.const_mul s).add (integrable_const _))
    fun z ↦ klFun_add_mul_sub_klFun_le_of_jointAnnulus hB0 (hδZ_abs z)
      (fun hz ↦ indicator_of_notMem hz _) (hZs0 z)).trans_eq ?_
  dsimp only [Pi.add_apply]
  rw [integral_add (hgδ_int.const_mul s) (integrable_const _), integral_const_mul,
    integral_const, smul_eq_mul, integral_indicator_llr_mul_scaledFourPointDelta_eq hRμν n]
  ring

private theorem setIntegral_llrCrossDiff_posDefectConfig_nonpos
    [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hRμν : R ≪ μ.prod ν) (hγ : IsCoupling γ μ ν) (hKL : klDiv γ R ≠ ∞)
    (hmin : ∀ γ', IsCoupling γ' μ ν → klDiv γ R ≤ klDiv γ' R) (n : ℕ) :
    ∫ q in posDefectConfig μ ν R γ n, llrCrossDiff γ R q ∂((μ.prod ν).prod (μ.prod ν)) ≤ 0 := by
  have := hγ.isFiniteMeasure_right
  by_contra! hpos_int
  set B := 4 * ((n : ℝ) + 1) * (μ.prod ν).real univ
  set I := ∫ q in posDefectConfig μ ν R γ n, llrCrossDiff γ R q ∂((μ.prod ν).prod (μ.prod ν))
  set Kquad := ((n : ℝ) + 1) * B ^ 2 * R.real univ
  set t := min (((n : ℝ) + 1) * (B + 1))⁻¹ (I / (2 * (Kquad + 1)))
  have ht0 : 0 < t := lt_min (inv_pos.2 (by positivity)) (div_pos hpos_int (by positivity))
  have hquad := zero_le_mul_setIntegral_posDefectConfig_add_sq hRμν hγ hKL hmin n (s := -t)
    (by rw [abs_neg, abs_of_pos ht0]; exact min_le_left _ _)
  have htK : t * Kquad ≤ I / 2 := by
    have h1 := (le_div_iff₀ (by positivity : 0 < 2 * (Kquad + 1))).1 (min_le_right _ _ : t ≤ _)
    nlinarith [ht0]
  nlinarith [hquad, mul_pos ht0 hpos_int, mul_le_mul_of_nonneg_left htK ht0.le]

private theorem measure_posDefectConfig_eq_zero [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hRμν : R ≪ μ.prod ν) (hγ : IsCoupling γ μ ν) (hKL : klDiv γ R ≠ ∞)
    (hmin : ∀ γ', IsCoupling γ' μ ν → klDiv γ R ≤ klDiv γ' R) (n : ℕ) :
    ((μ.prod ν).prod (μ.prod ν)) (posDefectConfig μ ν R γ n) = 0 := by
  have := hγ.isFiniteMeasure_right
  set Q := (μ.prod ν).prod (μ.prod ν)
  set A := posDefectConfig μ ν R γ n
  set g : X × Y → ℝ := (jointAnnulus μ ν R γ n).indicator (llr γ R)
  have hA_meas : MeasurableSet A := measurableSet_posDefectConfig n
  have hD_intOn : IntegrableOn (llrCrossDiff γ R) A Q := by
    rw [← integrable_indicator_iff hA_meas]
    refine .of_bound (measurable_llrCrossDiff.indicator hA_meas).aestronglyMeasurable
      (4 * log ((n : ℝ) + 1)) (ae_of_all _ fun q ↦ ?_)
    by_cases hq : q ∈ A
    · have heq : llrCrossDiff γ R q =
          g q.1 + g q.2 - g (prodProdSndComm q).1 - g (prodProdSndComm q).2 := by
        simp [llrCrossDiff, g, -prodProdSndComm_apply, indicator_of_mem hq.2.1,
          indicator_of_mem hq.2.2.1, indicator_of_mem hq.2.2.2.1, indicator_of_mem hq.2.2.2.2]
      have hb := abs_indicator_llr_jointAnnulus_le (μ := μ) (ν := ν) (R := R) (γ := γ) n
      rw [indicator_of_mem hq, Real.norm_eq_abs, heq]
      linarith [abs_sub (g q.1 + g q.2 - g (prodProdSndComm q).1) (g (prodProdSndComm q).2),
        abs_sub (g q.1 + g q.2) (g (prodProdSndComm q).1), abs_add_le (g q.1) (g q.2),
        hb q.1, hb q.2, hb (prodProdSndComm q).1, hb (prodProdSndComm q).2]
    · simp only [indicator_of_notMem hq, Real.norm_eq_abs, abs_zero]
      exact mul_nonneg (by positivity) (log_nonneg (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1))
  have hae_zero : ∀ᵐ q ∂Q.restrict A, llrCrossDiff γ R q = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae ((ae_restrict_mem hA_meas).mono fun _ hq ↦ hq.1.le)
      hD_intOn).1 <| le_antisymm
      (setIntegral_llrCrossDiff_posDefectConfig_nonpos hRμν hγ hKL hmin n)
      (setIntegral_nonneg hA_meas fun _ hq ↦ hq.1.le)
  rw [← Measure.restrict_apply_univ]
  refine measure_eq_zero_iff_ae_notMem.2 ?_
  filter_upwards [hae_zero, ae_restrict_mem hA_meas] with _ h0 hq _ using hq.1.ne' h0

private theorem ae_llrCrossDiff_nonpos_of_forall_klDiv_le [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hγ : IsCoupling γ μ ν) (hRμν : R ≪ μ.prod ν) (hμνR : μ.prod ν ≪ R) (hKL : klDiv γ R ≠ ∞)
    (hmin : ∀ γ', IsCoupling γ' μ ν → klDiv γ R ≤ klDiv γ' R) :
    ∀ᵐ q ∂(μ.prod ν).prod (μ.prod ν), llrCrossDiff γ R q ≤ 0 := by
  have := hγ.isFiniteMeasure
  have := hγ.isFiniteMeasure_right
  set P := μ.prod ν
  have hRγ : R ≪ γ := hγ.absolutelyContinuous_of_forall_klDiv_le hRμν hμνR hKL hmin
  have hex_H : ∀ᵐ z ∂P, ∃ n, z ∈ jointAnnulus μ ν R γ n := by
    filter_upwards [Measure.rnDeriv_pos' hμνR, Measure.rnDeriv_lt_top R P,
      hμνR.ae_le (Measure.rnDeriv_pos' hRγ), hμνR.ae_le (Measure.rnDeriv_lt_top γ R)]
      with _ hrp hrlt hZp hZlt using exists_mem_jointAnnulus
        (ENNReal.toReal_pos hrp.ne' hrlt.ne) (ENNReal.toReal_pos hZp.ne' hZlt.ne)
  have h12 := (ae_of_ae_fst hex_H).and (ae_of_ae_snd hex_H)
  have hQ_union : ∀ᵐ q ∂P.prod P, q ∉ ⋃ n, posDefectConfig μ ν R γ n :=
    measure_eq_zero_iff_ae_notMem.1
      (measure_iUnion_null (measure_posDefectConfig_eq_zero hRμν hγ hKL hmin))
  have hswap := measurePreserving_prodProdSndComm (μ := μ) (ν := ν) (μ' := μ) (ν' := ν)
  filter_upwards [h12, hswap.quasiMeasurePreserving.ae h12, hQ_union] with _
    ⟨⟨n₁, h₁⟩, ⟨n₂, h₂⟩⟩ ⟨⟨n₃, h₃⟩, ⟨n₄, h₄⟩⟩ hnot
  exact not_lt.1 fun hpos ↦ hnot (mem_iUnion.2 ⟨max (max n₁ n₂) (max n₃ n₄), hpos,
    monotone_jointAnnulus (by omega) h₁, monotone_jointAnnulus (by omega) h₂,
    monotone_jointAnnulus (by omega) h₃, monotone_jointAnnulus (by omega) h₄⟩)

/-- **Four-point cyclic additivity of the Schrödinger minimizer's log-likelihood ratio.** When
`R ∼ μ ⊗ ν` and `γ` minimizes `klDiv · R` among couplings of `μ` and `ν` with `klDiv γ R ≠ ∞`,
its log-likelihood ratio `llr γ R` satisfies
`llr γ R q.1 + llr γ R q.2 = llr γ R (q.1.1, q.2.2) + llr γ R (q.2.1, q.1.2)` for
`(μ.prod ν) ⊗ (μ.prod ν)`-almost every `q`. -/
theorem IsCoupling.ae_llr_add_llr_eq_of_forall_klDiv_le [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hγ : IsCoupling γ μ ν) (hRμν : R ≪ μ.prod ν) (hμνR : μ.prod ν ≪ R) (hKL : klDiv γ R ≠ ∞)
    (hmin : ∀ γ', IsCoupling γ' μ ν → klDiv γ R ≤ klDiv γ' R) :
    ∀ᵐ q ∂(μ.prod ν).prod (μ.prod ν),
      llr γ R q.1 + llr γ R q.2 = llr γ R (q.1.1, q.2.2) + llr γ R (q.2.1, q.1.2) := by
  have := hγ.isFiniteMeasure_right
  have hle := ae_llrCrossDiff_nonpos_of_forall_klDiv_le hγ hRμν hμνR hKL hmin
  have hswap := measurePreserving_prodProdSndComm (μ := μ) (ν := ν) (μ' := μ) (ν' := ν)
  filter_upwards [hle, hswap.quasiMeasurePreserving.ae hle] with q h1 h2
  simp only [llrCrossDiff, prodProdSndComm_apply] at h1 h2; linarith

end CyclicAdditivity

end TauCeti
