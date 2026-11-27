/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.HasLaw
public import TauCeti.Probability.Quantile.Median
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.InnerProductSpace.PiL2
import TauCeti.MeasureTheory.Measure.Tail

/-!
# Talagrand concentration for quasiconvex functions

For independent real coordinates supported in intervals of length at most one, the exponential
moment of the squared Euclidean distance to a convex set is bounded by the reciprocal of its
positive outer probability. Comparing a slice with the coordinate projection gives the
dimension induction. Applying the distance bound to sublevel sets controls deviations of
quasiconvex Lipschitz observables about a median and about the mean.

## References

* M. Talagrand, *Concentration of measure and isoperimetric inequalities in product spaces*,
  Publ. Math. IHÉS 81 (1995), §4.1.
* M. Ledoux, *Concentration of measure and logarithmic Sobolev inequalities*,
  Séminaire de Probabilités XXXIII (1999), §3.2.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped NNReal

namespace TauCeti.Probability

noncomputable section

private abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

open EuclideanSpace (consEquivL consEquivL_apply consEquivL_apply_zero consEquivL_apply_succ
  consEquivL_symm_apply_fst consEquivL_symm_apply_snd dist_consEquivL_sq)

private theorem exp_one_div_four_le_four_div_three : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
  convert Real.exp_bound_div_one_sub_of_interval (x := 1 / 4) (by norm_num) (by norm_num)
    using 1
  norm_num

private theorem exp_sq_div_four_le_two_sub {r : ℝ} (hr₁ : r ≤ 1) :
    ∃ b ∈ Icc (0 : ℝ) 1,
      Real.exp (b ^ 2 / 4 + (1 - b) * Real.log r⁻¹) ≤ 2 - r := by
  by_cases h : r ≤ 1 / 2
  · refine ⟨1, right_mem_Icc.2 zero_le_one, ?_⟩
    simp only [one_pow, sub_self, zero_mul, add_zero]
    linarith [exp_one_div_four_le_four_div_three]
  have hr : 0 < r := by linarith [lt_of_not_ge h]
  let b := 2 * (1 - r)
  have hb₀ : 0 ≤ b := by dsimp [b]; linarith
  have hb₁ : b ≤ 1 := by dsimp [b]; linarith
  refine ⟨b, ⟨hb₀, hb₁⟩, ?_⟩
  have he := convexOn_exp.2 (mem_univ (Real.log r⁻¹)) (mem_univ (0 : ℝ))
    (sub_nonneg.2 hb₁) hb₀ (sub_add_cancel 1 b)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one,
    Real.exp_log (inv_pos.2 hr)] at he
  have h₀ : 0 ≤ b ^ 2 / 4 := by positivity
  have h₁ : b ^ 2 / 4 < 1 := by nlinarith [mul_nonneg hb₀ (sub_nonneg.2 hb₁)]
  rw [Real.exp_add]
  calc
    _ ≤ (1 - b ^ 2 / 4)⁻¹ * ((1 - b) * r⁻¹ + b) :=
      mul_le_mul (by simpa only [one_div] using Real.exp_bound_div_one_sub_of_interval h₀ h₁) he
        (Real.exp_nonneg _) (by positivity)
    _ ≤ 2 - r := by
      rw [mul_comm, ← div_eq_mul_inv, div_le_iff₀ (sub_pos.2 h₁)]
      calc
        (1 - b) * r⁻¹ + b = ((1 - b) + b * r) / r := by field_simp
        _ ≤ _ := by
          rw [div_le_iff₀ hr]
          dsimp [b]
          nlinarith [pow_nonneg (sub_nonneg.2 hr₁) 4]

private def tailProj (n : ℕ) : Euclidean (n + 1) →L[ℝ] Euclidean n :=
  (ContinuousLinearMap.snd ℝ ℝ (Euclidean n)).comp (consEquivL ℝ n).symm.toContinuousLinearMap

private def slice {n : ℕ} (A : Set (Euclidean (n + 1))) (t : ℝ) : Set (Euclidean n) :=
  (fun x ↦ consEquivL ℝ n (t, x)) ⁻¹' A

private theorem slice_subset_image_tail {n : ℕ} (A : Set (Euclidean (n + 1))) (t : ℝ) :
    slice A t ⊆ tailProj n '' A :=
  fun y hy ↦ ⟨consEquivL ℝ n (t, y), hy, by simp [tailProj]⟩

private theorem isCompact_slice {n : ℕ} {A : Set (Euclidean (n + 1))}
    (hA : IsCompact A) (t : ℝ) : IsCompact (slice A t) := by
  have heq : slice A t = tailProj n '' (A ∩ {z | z 0 = t}) := by
    ext y
    constructor
    · intro hy
      exact ⟨consEquivL ℝ n (t, y), ⟨hy, consEquivL_apply_zero (t, y)⟩, by simp [tailProj]⟩
    · rintro ⟨z, ⟨hz, hzt⟩, rfl⟩
      rw [mem_ofPred_eq] at hzt
      rw [slice, mem_preimage, ← hzt, tailProj, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_snd', ContinuousLinearEquiv.coe_coe, ← consEquivL_symm_apply_fst,
        Prod.mk.eta, ContinuousLinearEquiv.apply_symm_apply]
      exact hz
  rw [heq]
  exact (hA.inter_right (isClosed_eq (PiLp.continuous_apply 2 _ 0) continuous_const)).image
    (tailProj n).continuous

private theorem convex_slice {n : ℕ} {A : Set (Euclidean (n + 1))}
    (hA : Convex ℝ A) (t : ℝ) : Convex ℝ (slice A t) := by
  intro x hx y hy a b ha hb hab
  have ht : a * t + b * t = t := by rw [← add_mul, hab, one_mul]
  have hx' : consEquivL ℝ n (t, x) ∈ A := hx
  have hy' : consEquivL ℝ n (t, y) ∈ A := hy
  have h := hA hx' hy' ha hb hab
  rw [← map_smul, ← map_smul, ← map_add] at h
  simpa only [slice, mem_preimage, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, ht] using h

private theorem sq_sub_le_one_of_dist_le_one {x y : ℝ} (h : dist x y ≤ 1) :
    (x - y) ^ 2 ≤ 1 := by
  rwa [sq_le_one_iff_abs_le_one, ← Real.dist_eq]

private theorem infDist_cons_sq_le_of_mem {n : ℕ}
    {A : Set (Euclidean (n + 1))} (hAc : Convex ℝ A)
    {t : ℝ} {x y : Euclidean n} {z : Euclidean (n + 1)}
    (hy : y ∈ slice A t) (hz : z ∈ A) (htz : dist t (z 0) ≤ 1)
    {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    infDist (consEquivL ℝ n (t, x)) A ^ 2 ≤ (1 - b) * dist x y ^ 2 +
      b * dist x (tailProj n z) ^ 2 + b ^ 2 := by
  let zTail := tailProj n z
  let c := (1 - b) * t + b * z 0
  let w := (1 - b) • y + b • zTail
  have hw : consEquivL ℝ n (c, w) ∈ A := by
    have hy' : consEquivL ℝ n (t, y) ∈ A := hy
    have h := hAc hy' hz (sub_nonneg.2 hb.2) hb.1 (sub_add_cancel 1 b)
    rw [← (consEquivL ℝ n).apply_symm_apply z, ← map_smul, ← map_smul, ← map_add] at h
    have heq : (1 - b) • (t, y) + b • (consEquivL ℝ n).symm z = (c, w) := by
      apply Prod.ext <;> simp [c, w, zTail, tailProj, smul_eq_mul]
    rwa [heq] at h
  have hc : (t - c) ^ 2 ≤ b ^ 2 := by
    dsimp [c]
    nlinarith [mul_le_mul_of_nonneg_left (sq_sub_le_one_of_dist_le_one htz) (sq_nonneg b)]
  have hd : dist x w ^ 2 ≤ (1 - b) * dist x y ^ 2 + b * dist x zTail ^ 2 := by
    have h₁ := sub_nonneg.2 hb.2
    have hsum := sub_add_cancel 1 b
    have hdist : dist w x ≤ (1 - b) * dist y x + b * dist zTail x :=
      (convexOn_univ_dist x).2 (mem_univ y) (mem_univ zTail) h₁ hb.1 hsum
    rw [dist_comm w x, dist_comm y x, dist_comm zTail x] at hdist
    have hweighted : 0 ≤ (1 - b) * dist x y + b * dist x zTail :=
      add_nonneg (mul_nonneg h₁ dist_nonneg) (mul_nonneg hb.1 dist_nonneg)
    exact ((sq_le_sq₀ dist_nonneg hweighted).2 hdist).trans
      ((convexOn_pow 2).2 (mem_Ici.2 dist_nonneg) (mem_Ici.2 dist_nonneg) h₁ hb.1 hsum)
  calc
    _ ≤ dist (consEquivL ℝ n (t, x)) (consEquivL ℝ n (c, w)) ^ 2 :=
      (sq_le_sq₀ infDist_nonneg dist_nonneg).2 (infDist_le_dist_of_mem hw)
    _ ≤ _ := by rw [dist_consEquivL_sq, Real.dist_eq, sq_abs]; linarith

private theorem infDist_cons_sq_le {n : ℕ}
    {A : Set (Euclidean (n + 1))} (hAc : Convex ℝ A)
    {t : ℝ} (hline : ∀ z ∈ A, dist t (z 0) ≤ 1) {x : Euclidean n}
    {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (hne : (slice A t).Nonempty) :
    infDist (consEquivL ℝ n (t, x)) A ^ 2 ≤ (1 - b) * infDist x (slice A t) ^ 2 +
      b * infDist x (tailProj n '' A) ^ 2 + b ^ 2 := by
  obtain ⟨y, hy, hyd⟩ := exists_mem_closure_infDist_eq_dist hne x
  obtain ⟨z, hz, hzd⟩ :=
    exists_mem_closure_infDist_eq_dist (hne.mono (slice_subset_image_tail A t)) x
  rw [hyd, hzd]
  -- Extend the inequality to the closures of the slice and projection to use nearest points.
  have hS : IsClosed {u : Euclidean n | infDist (consEquivL ℝ n (t, x)) A ^ 2 ≤
      (1 - b) * dist x u ^ 2 + b * dist x z ^ 2 + b ^ 2} :=
    isClosed_le continuous_const (by fun_prop)
  apply closure_minimal ?_ hS hy
  intro u hu
  have hT : IsClosed {v : Euclidean n | infDist (consEquivL ℝ n (t, x)) A ^ 2 ≤
      (1 - b) * dist x u ^ 2 + b * dist x v ^ 2 + b ^ 2} :=
    isClosed_le continuous_const (by fun_prop)
  apply closure_minimal ?_ hT hz
  rintro _ ⟨v, hv, rfl⟩
  exact infDist_cons_sq_le_of_mem hAc hu hv (hline v hv) hb

private theorem infDist_cons_sq_le_of_projection {n : ℕ}
    {A : Set (Euclidean (n + 1))} {t : ℝ} (hline : ∀ z ∈ A, dist t (z 0) ≤ 1)
    (x : Euclidean n) :
    infDist (consEquivL ℝ n (t, x)) A ^ 2 ≤
      infDist x (tailProj n '' A) ^ 2 + 1 := by
  obtain rfl | hne := A.eq_empty_or_nonempty
  · simp
  obtain ⟨y, hy, hyd⟩ :=
    exists_mem_closure_infDist_eq_dist (hne.image (tailProj n)) x
  rw [hyd]
  have hT : IsClosed {v : Euclidean n | infDist (consEquivL ℝ n (t, x)) A ^ 2 ≤ dist x v ^ 2 + 1} :=
    isClosed_le continuous_const (by fun_prop)
  apply closure_minimal ?_ hT hy
  rintro _ ⟨z, hz, rfl⟩
  have hsq := sq_sub_le_one_of_dist_le_one (hline z hz)
  calc
    _ ≤ dist (consEquivL ℝ n (t, x)) z ^ 2 :=
      (sq_le_sq₀ infDist_nonneg dist_nonneg).2 (infDist_le_dist_of_mem hz)
    _ = (t - z 0) ^ 2 + dist x (tailProj n z) ^ 2 := by
      simpa [tailProj, Real.dist_eq] using dist_consEquivL_sq (t, x) ((consEquivL ℝ n).symm z)
    _ ≤ _ := by linarith only [hsq]

private def expSqInfDist {ι : Type*} [Fintype ι] (A : Set (EuclideanSpace ℝ ι))
    (x : EuclideanSpace ℝ ι) : ℝ :=
  Real.exp (infDist x A ^ 2 / 4)

private theorem continuous_expSqInfDist {ι : Type*} [Fintype ι]
    (A : Set (EuclideanSpace ℝ ι)) : Continuous (expSqInfDist A) :=
  Real.continuous_exp.comp ((continuous_infDist_pt A).pow 2 |>.div_const 4)

private theorem integrable_expSqInfDist_toLp {ι : Type*} [Fintype ι] {μ : ι → Measure ℝ}
    [∀ i, IsFiniteMeasure (μ i)] {a b : ι → ℝ}
    (hμ : ∀ i, ∀ᵐ x ∂μ i, x ∈ Icc (a i) (b i)) (A : Set (EuclideanSpace ℝ ι)) :
    Integrable (fun x ↦ expSqInfDist A (WithLp.toLp 2 x)) (Measure.pi μ) := by
  rw [← Measure.restrict_eq_self_of_ae_mem (s := univ.pi fun i ↦ Icc (a i) (b i))
    (Measure.ae_pi_le_pi (Filter.pi_mem_pi finite_univ fun i _ ↦ hμ i))]
  exact ContinuousOn.integrableOn_compact (isCompact_univ_pi fun _ ↦ isCompact_Icc)
    ((continuous_expSqInfDist A).comp (PiLp.continuous_toLp _ _)).continuousOn

private theorem integrable_expSqInfDist_cons_toLp {n : ℕ} {μ : Fin n → Measure ℝ}
    [∀ i, IsFiniteMeasure (μ i)] {a b : Fin n → ℝ}
    (hμ : ∀ i, ∀ᵐ x ∂μ i, x ∈ Icc (a i) (b i)) (A : Set (Euclidean (n + 1))) (t : ℝ) :
    Integrable (fun x ↦ expSqInfDist A (consEquivL ℝ n (t, WithLp.toLp 2 x))) (Measure.pi μ) := by
  rw [← Measure.restrict_eq_self_of_ae_mem (s := univ.pi fun i ↦ Icc (a i) (b i))
    (Measure.ae_pi_le_pi (Filter.pi_mem_pi finite_univ fun i _ ↦ hμ i))]
  exact ContinuousOn.integrableOn_compact (isCompact_univ_pi fun _ ↦ isCompact_Icc)
    (((continuous_expSqInfDist A).comp ((consEquivL ℝ n).continuous.comp
      (continuous_const.prodMk (PiLp.continuous_toLp _ _)))).continuousOn)

-- Normalize the two exponential moments before applying convexity of the exponential.
private theorem exp_le_weighted {u v w c p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hc : c ∈ Icc (0 : ℝ) 1) (hu : u ≤ (1 - c) * v + c * w + c ^ 2 / 4) :
    Real.exp u ≤ Real.exp (c ^ 2 / 4 + (1 - c) * Real.log (q / p)⁻¹) / p *
      ((1 - c) * (q * Real.exp v) + c * (p * Real.exp w)) := by
  have hconv := convexOn_exp.2 (mem_univ (v + Real.log q)) (mem_univ (w + Real.log p))
    (sub_nonneg.2 hc.2) hc.1 (sub_add_cancel 1 c)
  simp only [smul_eq_mul] at hconv
  rw [Real.exp_add v, Real.exp_add w, Real.exp_log hq, Real.exp_log hp] at hconv
  have heq : Real.exp (c ^ 2 / 4 + (1 - c) * Real.log (q / p)⁻¹) / p =
      Real.exp (c ^ 2 / 4 - ((1 - c) * Real.log q + c * Real.log p)) := by
    calc
      _ = Real.exp ((c ^ 2 / 4 + (1 - c) * Real.log (q / p)⁻¹) - Real.log p) := by
        rw [Real.exp_sub, Real.exp_log hp]
      _ = _ := by
        rw [inv_div, Real.log_div hp.ne' hq.ne']
        congr 1
        ring
  rw [heq, mul_comm q, mul_comm p]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hconv (Real.exp_nonneg _))
  rw [← Real.exp_add, Real.exp_le_exp]
  linarith only [hu]

private theorem integral_expSqInfDist_cons_le_of_projection {n : ℕ} {μ : Fin n → Measure ℝ}
    [∀ i, IsFiniteMeasure (μ i)] {a b : Fin n → ℝ}
    (hμ : ∀ i, ∀ᵐ x ∂μ i, x ∈ Icc (a i) (b i))
    {A : Set (Euclidean (n + 1))} {t : ℝ} (hline : ∀ z ∈ A, dist t (z 0) ≤ 1)
    (hp : 0 < (Measure.pi μ).real ((WithLp.toLp 2) ⁻¹' (tailProj n '' A)))
    (hproj : (Measure.pi μ).real ((WithLp.toLp 2) ⁻¹' (tailProj n '' A)) *
      (∫ x, expSqInfDist (tailProj n '' A) (WithLp.toLp 2 x)
        ∂Measure.pi μ) ≤ 1) :
    (∫ x, expSqInfDist A (consEquivL ℝ n (t, WithLp.toLp 2 x)) ∂Measure.pi μ) ≤
      2 / (Measure.pi μ).real ((WithLp.toLp 2) ⁻¹' (tailProj n '' A)) := by
  let p := (Measure.pi μ).real ((WithLp.toLp 2) ⁻¹' (tailProj n '' A))
  let G := fun x : Fin n → ℝ ↦
    expSqInfDist (tailProj n '' A) (WithLp.toLp 2 x)
  let H := fun x : Fin n → ℝ ↦ expSqInfDist A (consEquivL ℝ n (t, WithLp.toLp 2 x))
  have hG : Integrable G (Measure.pi μ) :=
    integrable_expSqInfDist_toLp hμ _
  have hH : Integrable H (Measure.pi μ) :=
    integrable_expSqInfDist_cons_toLp hμ A t
  have hle (x : Fin n → ℝ) : H x ≤ Real.exp (1 / 4) * G x := by
    dsimp [H, G, expSqInfDist]
    rw [← Real.exp_add, ← add_div]
    apply Real.exp_le_exp.mpr
    have hx := infDist_cons_sq_le_of_projection hline (WithLp.toLp 2 x)
    exact div_le_div_of_nonneg_right (by linarith only [hx]) (by norm_num)
  have he : Real.exp (1 / 4 : ℝ) ≤ 2 :=
    exp_one_div_four_le_four_div_three.trans (by norm_num)
  calc
    (∫ x, H x ∂Measure.pi μ) ≤ ∫ x, Real.exp (1 / 4) * G x ∂Measure.pi μ :=
      integral_mono hH (hG.const_mul _) hle
    _ ≤ 2 / p := by
      rw [integral_const_mul, le_div_iff₀ hp]
      calc
        _ = Real.exp (1 / 4) * (p * ∫ x, G x ∂Measure.pi μ) := by ring
        _ ≤ Real.exp (1 / 4) := by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hproj (Real.exp_nonneg _)
        _ ≤ 2 := he

private theorem integral_expSqInfDist_cons_le {n : ℕ} {μ : Fin n → Measure ℝ}
    [∀ i, IsFiniteMeasure (μ i)] {a b : Fin n → ℝ}
    (hμ : ∀ i, ∀ᵐ x ∂μ i, x ∈ Icc (a i) (b i))
    {A : Set (Euclidean (n + 1))} (hAc : Convex ℝ A)
    {t : ℝ} (hline : ∀ z ∈ A, dist t (z 0) ≤ 1)
    (hp : 0 < (Measure.pi μ).real ((WithLp.toLp 2) ⁻¹' (tailProj n '' A)))
    (hproj : (Measure.pi μ).real ((WithLp.toLp 2) ⁻¹' (tailProj n '' A)) *
      (∫ x, expSqInfDist (tailProj n '' A) (WithLp.toLp 2 x)
        ∂Measure.pi μ) ≤ 1)
    (hslice : (Measure.pi μ).real ((WithLp.toLp 2) ⁻¹' slice A t) *
      (∫ x, expSqInfDist (slice A t) (WithLp.toLp 2 x) ∂Measure.pi μ) ≤ 1) :
    (∫ x, expSqInfDist A (consEquivL ℝ n (t, WithLp.toLp 2 x)) ∂Measure.pi μ) ≤
      (2 - (Measure.pi μ).real ((WithLp.toLp 2) ⁻¹' slice A t) /
        (Measure.pi μ).real ((WithLp.toLp 2) ⁻¹' (tailProj n '' A))) /
        (Measure.pi μ).real ((WithLp.toLp 2) ⁻¹' (tailProj n '' A)) := by
  let p := (Measure.pi μ).real ((WithLp.toLp 2) ⁻¹' (tailProj n '' A))
  let q := (Measure.pi μ).real ((WithLp.toLp 2) ⁻¹' slice A t)
  let F := fun x : Fin n → ℝ ↦ expSqInfDist (slice A t) (WithLp.toLp 2 x)
  let G := fun x : Fin n → ℝ ↦
    expSqInfDist (tailProj n '' A) (WithLp.toLp 2 x)
  let H := fun x : Fin n → ℝ ↦ expSqInfDist A (consEquivL ℝ n (t, WithLp.toLp 2 x))
  have hF : Integrable F (Measure.pi μ) :=
    integrable_expSqInfDist_toLp hμ _
  have hG : Integrable G (Measure.pi μ) :=
    integrable_expSqInfDist_toLp hμ _
  have hH : Integrable H (Measure.pi μ) :=
    integrable_expSqInfDist_cons_toLp hμ A t
  by_cases hq : q = 0
  · calc
      _ ≤ 2 / p := integral_expSqInfDist_cons_le_of_projection hμ hline hp hproj
      _ = (2 - q / p) / p := by rw [hq, zero_div, sub_zero]
  have hqpos : 0 < q := lt_of_le_of_ne measureReal_nonneg (Ne.symm hq)
  have hqp : q ≤ p := measureReal_mono (preimage_mono (slice_subset_image_tail A t))
  obtain ⟨c, hc, hexp⟩ := exp_sq_div_four_le_two_sub ((div_le_one hp).2 hqp)
  let C := Real.exp (c ^ 2 / 4 + (1 - c) * Real.log (q / p)⁻¹) / p
  have hne : (slice A t).Nonempty := by
    contrapose! hqpos
    simp [q, hqpos]
  have hle (x : Fin n → ℝ) : H x ≤ C * ((1 - c) * (q * F x) + c * (p * G x)) := by
    apply exp_le_weighted hp hqpos hc
    linarith only [infDist_cons_sq_le hAc hline hc hne (x := WithLp.toLp 2 x)]
  have hC₀ : 0 ≤ C := div_nonneg (Real.exp_nonneg _) hp.le
  have hweighted := (hF.const_mul q |>.const_mul (1 - c)).add (hG.const_mul p |>.const_mul c)
  calc
    (∫ x, H x ∂Measure.pi μ) ≤ ∫ x, C * ((1 - c) * (q * F x) + c * (p * G x)) ∂Measure.pi μ :=
      integral_mono hH (hweighted.const_mul C) hle
    _ ≤ C := by
      rw [integral_const_mul, integral_add (hF.const_mul q |>.const_mul (1 - c))
        (hG.const_mul p |>.const_mul c)]
      simp only [integral_const_mul]
      nth_rw 2 [← mul_one C]
      refine mul_le_mul_of_nonneg_left ?_ hC₀
      have hf := mul_le_mul_of_nonneg_left hslice (sub_nonneg.2 hc.2)
      have hg := mul_le_mul_of_nonneg_left hproj hc.1
      linarith only [hf, hg]
    _ ≤ _ := div_le_div_of_nonneg_right hexp hp.le

private abbrev finConsEquiv (n : ℕ) : (ℝ × (Fin n → ℝ)) ≃ᵐ (Fin (n + 1) → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm

private theorem finConsEquiv_apply {n : ℕ} (z : ℝ × (Fin n → ℝ)) :
    finConsEquiv n z = Fin.cons z.1 z.2 := by
  simp [finConsEquiv, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

private theorem measurePreserving_finConsEquiv {n : ℕ} (μ : Fin (n + 1) → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] :
    MeasurePreserving (finConsEquiv n) ((μ 0).prod (Measure.pi fun i : Fin n ↦ μ i.succ))
      (Measure.pi μ) := by
  simpa only [finConsEquiv, Fin.zero_succAbove] using (measurePreserving_piFinSuccAbove μ 0).symm

private theorem preimage_slice_eq {n : ℕ} (A : Set (Euclidean (n + 1))) (t : ℝ) :
    WithLp.toLp 2 ⁻¹' slice A t =
      Prod.mk t ⁻¹' (finConsEquiv n ⁻¹' (WithLp.toLp 2 ⁻¹' A)) := by
  ext x
  simp only [slice, mem_preimage, finConsEquiv_apply, consEquivL_apply]

private theorem measureReal_pi_eq_integral_slice {n : ℕ} (μ : Fin (n + 1) → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] {A : Set (Euclidean (n + 1))} (hA : MeasurableSet A) :
    (Measure.pi μ).real (WithLp.toLp 2 ⁻¹' A) =
      ∫ t, (Measure.pi fun i : Fin n ↦ μ i.succ).real (WithLp.toLp 2 ⁻¹' slice A t) ∂μ 0 := by
  have hC : MeasurableSet (WithLp.toLp 2 ⁻¹' A) :=
    WithLp.measurable_toLp 2 (Fin (n + 1) → ℝ) hA
  have hC' := (finConsEquiv n).measurable hC
  rw [← (measurePreserving_finConsEquiv μ).measureReal_preimage hC.nullMeasurableSet,
    measureReal_def, Measure.prod_apply hC']
  simp_rw [preimage_slice_eq, measureReal_def]
  exact (integral_toReal (measurable_measure_prodMk_left hC').aemeasurable
    (ae_of_all _ fun _ ↦ (measure_ne_top _ _).lt_top)).symm

private theorem integrable_slice_measureReal {n : ℕ} (μ : Fin (n + 1) → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] {A : Set (Euclidean (n + 1))} (hA : MeasurableSet A) :
    Integrable (fun t ↦ (Measure.pi fun i : Fin n ↦ μ i.succ).real
      (WithLp.toLp 2 ⁻¹' slice A t)) (μ 0) := by
  let ν := Measure.pi (fun i : Fin n ↦ μ i.succ)
  refine .of_bound ?_ (ν.real univ) (ae_of_all _ fun t ↦ ?_)
  · simp_rw [preimage_slice_eq, measureReal_def]
    exact (measurable_measure_prodMk_left ((finConsEquiv n).measurable
      (WithLp.measurable_toLp 2 (Fin (n + 1) → ℝ) hA))).ennreal_toReal.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_mono (subset_univ _)

private theorem integrable_expSqInfDist_cons {n : ℕ} {μ : Fin (n + 1) → Measure ℝ}
    [∀ i, IsFiniteMeasure (μ i)] {a b : Fin (n + 1) → ℝ}
    (hμ : ∀ i, ∀ᵐ x ∂μ i, x ∈ Icc (a i) (b i)) (A : Set (Euclidean (n + 1))) :
    Integrable (fun z : ℝ × (Fin n → ℝ) ↦ expSqInfDist A (consEquivL ℝ n (z.1, WithLp.toLp 2 z.2)))
      ((μ 0).prod (Measure.pi fun i : Fin n ↦ μ i.succ)) := by
  simpa only [Function.comp_def, finConsEquiv_apply, consEquivL_apply, WithLp.ofLp_toLp] using
    (measurePreserving_finConsEquiv μ).integrable_comp_of_integrable
      (integrable_expSqInfDist_toLp hμ A)

private theorem measureReal_mul_integral_expSqInfDist_le_succ {n : ℕ}
    (μ : Fin (n + 1) → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {a b : Fin (n + 1) → ℝ} (hwidth : b 0 - a 0 ≤ 1)
    (hμ : ∀ i, ∀ᵐ x ∂μ i, x ∈ Icc (a i) (b i))
    {A : Set (Euclidean (n + 1))} (hA : MeasurableSet A) (hAc : Convex ℝ A)
    (hAbox : ∀ x ∈ A, x 0 ∈ Icc (a 0) (b 0))
    (hproj : (Measure.pi fun i : Fin n ↦ μ i.succ).real
      (WithLp.toLp 2 ⁻¹' (tailProj n '' A)) *
      (∫ x, expSqInfDist (tailProj n '' A) (WithLp.toLp 2 x)
        ∂Measure.pi fun i : Fin n ↦ μ i.succ) ≤ 1)
    (hslice : ∀ t, (Measure.pi fun i : Fin n ↦ μ i.succ).real (WithLp.toLp 2 ⁻¹' slice A t) *
      (∫ x, expSqInfDist (slice A t) (WithLp.toLp 2 x) ∂Measure.pi fun i : Fin n ↦ μ i.succ) ≤ 1) :
    (Measure.pi μ).real (WithLp.toLp 2 ⁻¹' A) *
      (∫ x, expSqInfDist A (WithLp.toLp 2 x) ∂Measure.pi μ) ≤ 1 := by
  by_cases hzero : (Measure.pi μ).real ((WithLp.toLp 2) ⁻¹' A) = 0
  · simp [hzero]
  let ν := Measure.pi (fun i : Fin n ↦ μ i.succ)
  let f := fun x : Fin (n + 1) → ℝ ↦ expSqInfDist A (WithLp.toLp 2 x)
  let C := (WithLp.toLp 2) ⁻¹' A
  let m := (Measure.pi μ).real C
  let p := ν.real ((WithLp.toLp 2) ⁻¹' (tailProj n '' A))
  let q := fun t ↦ ν.real ((WithLp.toLp 2) ⁻¹' slice A t)
  have hm : m = ∫ t, q t ∂μ 0 := measureReal_pi_eq_integral_slice μ hA
  have hqle (t : ℝ) : q t ≤ p :=
    measureReal_mono (preimage_mono (slice_subset_image_tail A t))
  have hqi : Integrable q (μ 0) := integrable_slice_measureReal μ hA
  have hmp : m ≤ p := by
    rw [hm]
    simpa only [integral_const, probReal_univ, one_smul] using
      integral_mono hqi (integrable_const (μ := μ 0) p) hqle
  have hmpos : 0 < m := lt_of_le_of_ne measureReal_nonneg (Ne.symm hzero)
  have hp : 0 < p := hmpos.trans_le hmp
  have hI := integrable_expSqInfDist_cons hμ A
  have hIeq : (∫ x, f x ∂Measure.pi μ) =
      ∫ t, ∫ x, expSqInfDist A (consEquivL ℝ n (t, WithLp.toLp 2 x)) ∂ν ∂μ 0 := by
    rw [← (measurePreserving_finConsEquiv μ).integral_comp' f]
    simpa only [Function.comp_apply, finConsEquiv_apply, consEquivL_apply, WithLp.ofLp_toLp] using
      integral_prod _ hI
  have hi : (∫ x, f x ∂Measure.pi μ) ≤ (2 - m / p) / p := by
    rw [hIeq, hm]
    calc
      _ ≤ ∫ t, (2 - q t / p) / p ∂μ 0 := by
        refine integral_mono_ae hI.integral_prod_left
          (((integrable_const 2).sub (hqi.div_const p)).div_const p) ?_
        filter_upwards [hμ 0] with t ht
        exact integral_expSqInfDist_cons_le (fun i ↦ hμ i.succ) hAc
          (fun z hz ↦ (Real.dist_le_of_mem_Icc ht (hAbox z hz)).trans hwidth) hp hproj (hslice t)
      _ = _ := by
        rw [integral_div, integral_sub (integrable_const _) (hqi.div_const p), integral_div]
        simp
  calc
    _ ≤ m * ((2 - m / p) / p) := mul_le_mul_of_nonneg_left hi hmpos.le
    _ ≤ 1 := by
      have : 0 ≤ (1 - m / p) ^ 2 := sq_nonneg _
      calc
        _ = (m / p) * (2 - m / p) := by ring
        _ ≤ 1 := by nlinarith only [this]

private theorem measureReal_mul_integral_expSqInfDist_le_box (n : ℕ)
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (a b : Fin n → ℝ) (hwidth : ∀ i, b i - a i ≤ 1)
    (hμ : ∀ i, ∀ᵐ x ∂μ i, x ∈ Icc (a i) (b i))
    {A : Set (Euclidean n)} (hA : IsCompact A) (hAc : Convex ℝ A)
    (hAbox : ∀ x ∈ A, ∀ i, x i ∈ Icc (a i) (b i)) :
    (Measure.pi μ).real ((WithLp.toLp 2) ⁻¹' A) *
      (∫ x, expSqInfDist A (WithLp.toLp 2 x) ∂Measure.pi μ) ≤ 1 := by
  induction n with
  | zero =>
      by_cases hne : A.Nonempty
      swap
      · simp [Set.not_nonempty_iff_eq_empty.mp hne]
      obtain ⟨z, hz⟩ := hne
      have hdist (x : Fin 0 → ℝ) : infDist (WithLp.toLp 2 x) A = 0 := by
        have hx : WithLp.toLp 2 x = z := Subsingleton.elim _ _
        exact hx ▸ infDist_zero_of_mem hz
      simp only [expSqInfDist, hdist, zero_pow (by decide : 2 ≠ 0), zero_div, Real.exp_zero,
        integral_const, probReal_univ, smul_eq_mul, mul_one]
      exact measureReal_le_one
  | succ n ih =>
      have hproj := ih (fun i ↦ μ i.succ) (fun i ↦ a i.succ) (fun i ↦ b i.succ)
        (fun i ↦ hwidth i.succ) (fun i ↦ hμ i.succ)
        (hA.image (tailProj n).continuous) (hAc.linear_image (tailProj n).toLinearMap)
        (by
          rintro _ ⟨z, hz, rfl⟩ i
          simpa [tailProj] using hAbox z hz i.succ)
      have hslice (t : ℝ) := ih (fun i ↦ μ i.succ) (fun i ↦ a i.succ) (fun i ↦ b i.succ)
        (fun i ↦ hwidth i.succ) (fun i ↦ hμ i.succ) (isCompact_slice hA t) (convex_slice hAc t)
        (fun z hz i ↦ by
          simpa only [consEquivL_apply_succ] using hAbox (consEquivL ℝ n (t, z)) hz i.succ)
      exact measureReal_mul_integral_expSqInfDist_le_succ μ (hwidth 0) hμ
        hA.isClosed.measurableSet hAc (fun z hz ↦ hAbox z hz 0) hproj hslice

section Fin

variable {n : ℕ} {μ : Fin n → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)]
    {a b : Fin n → ℝ}

private theorem measureReal_mul_integral_exp_infDist_sq_div_four_le_fin
    (hwidth : ∀ i, b i - a i ≤ 1) (hμ : ∀ i, ∀ᵐ x ∂μ i, x ∈ Icc (a i) (b i))
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsClosed A) (hAc : Convex ℝ A) :
    (Measure.pi μ).real (WithLp.toLp 2 ⁻¹' A) *
      (∫ x, Real.exp (infDist (WithLp.toLp 2 x) A ^ 2 / 4) ∂Measure.pi μ) ≤ 1 := by
  let B := WithLp.toLp 2 '' (univ.pi fun i ↦ Icc (a i) (b i))
  have hBc : IsCompact B := (isCompact_univ_pi fun _ ↦ isCompact_Icc).image
    (PiLp.continuous_toLp _ _)
  have hbox : Convex ℝ (univ.pi fun i ↦ Icc (a i) (b i)) :=
    convex_pi fun {i} _ ↦ convex_Icc (a i) (b i)
  have hconv : Convex ℝ B :=
    hbox.linear_image (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap
  have hB (z : Euclidean n) (hz : z ∈ B) (i : Fin n) : z i ∈ Icc (a i) (b i) := by
    obtain ⟨x, hx, rfl⟩ := hz
    exact hx i (mem_univ i)
  have hbox_mem : ∀ᵐ x ∂Measure.pi μ, x ∈ univ.pi (fun i ↦ Icc (a i) (b i)) :=
    Measure.ae_pi_le_pi (Filter.pi_mem_pi finite_univ fun i _ ↦ hμ i)
  have hmem : ∀ᵐ x ∂Measure.pi μ, WithLp.toLp 2 x ∈ B :=
    hbox_mem.mono fun x hx ↦ mem_image_of_mem _ hx
  have hm : (Measure.pi μ).real (WithLp.toLp 2 ⁻¹' (A ∩ B)) =
      (Measure.pi μ).real (WithLp.toLp 2 ⁻¹' A) := by
    apply measureReal_congr
    filter_upwards [hmem] with x hx
    simp [hx]
  rw [← hm]
  by_cases hne : (A ∩ B).Nonempty
  swap
  · simp [Set.not_nonempty_iff_eq_empty.mp hne]
  have hbound := measureReal_mul_integral_expSqInfDist_le_box n μ a b hwidth hμ
    (hBc.inter_left hA) (hAc.inter hconv) (fun z hz ↦ hB z hz.2)
  refine le_trans (mul_le_mul_of_nonneg_left ?_ measureReal_nonneg) hbound
  refine integral_mono (integrable_expSqInfDist_toLp hμ A)
    (integrable_expSqInfDist_toLp hμ (A ∩ B)) fun x ↦ ?_
  exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
    ((sq_le_sq₀ infDist_nonneg infDist_nonneg).2
      (infDist_le_infDist_of_subset inter_subset_left hne)) (by norm_num))

end Fin

section Fintype

variable {ι : Type*} [Fintype ι] {μ : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)]
    {a b : ι → ℝ}

/-- **Talagrand's distance bound** for a product of probability measures supported in intervals
of length at most one. The expectation of `exp (dist(x, A)² / 4)`, multiplied by the outer
probability of the convex set `A`, is at most one. -/
theorem measureReal_mul_integral_exp_infDist_sq_div_four_le
    (hwidth : ∀ i, b i - a i ≤ 1) (hμ : ∀ i, ∀ᵐ x ∂μ i, x ∈ Icc (a i) (b i))
    {A : Set (EuclideanSpace ℝ ι)} (hAc : Convex ℝ A) :
    (Measure.pi μ).real (WithLp.toLp 2 ⁻¹' A) *
      (∫ x, Real.exp (infDist (WithLp.toLp 2 x) A ^ 2 / 4) ∂Measure.pi μ) ≤ 1 := by
  let e := (Fintype.equivFin ι).symm
  let E := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  let g := MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℝ) e
  let S := E ⁻¹' closure A
  have hg : MeasurePreserving g (Measure.pi fun i ↦ μ (e i)) (Measure.pi μ) :=
    measurePreserving_piCongrLeft μ e
  have hcoord (x : Fin (Fintype.card ι) → ℝ) : WithLp.toLp 2 (g x) = E (WithLp.toLp 2 x) := by
    ext i
    obtain ⟨j, rfl⟩ := e.surjective i
    rw [LinearIsometryEquiv.piLpCongrLeft_apply]
    simpa only [Equiv.piCongrLeft'_apply, Equiv.symm_apply_apply] using
      MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι ↦ ℝ) e x j
  have hS : IsClosed S := isClosed_closure.preimage E.continuous
  have hSc : Convex ℝ S := hAc.closure.linear_preimage E.toLinearMap
  have hSmap : E '' S = closure A := E.surjective.image_preimage _
  have h := measureReal_mul_integral_exp_infDist_sq_div_four_le_fin
    (fun i ↦ hwidth (e i)) (fun i ↦ hμ (e i)) hS hSc
  have hmass : (Measure.pi fun i ↦ μ (e i)).real (WithLp.toLp 2 ⁻¹' S) =
      (Measure.pi μ).real (WithLp.toLp 2 ⁻¹' closure A) := by
    rw [← hg.measureReal_preimage (WithLp.measurable_toLp 2 (ι → ℝ)
      isClosed_closure.measurableSet).nullMeasurableSet]
    apply congrArg (Measure.pi fun i ↦ μ (e i)).real
    ext x
    simp only [mem_preimage, hcoord, S]
  have hI : (∫ x, Real.exp (infDist (WithLp.toLp 2 x) S ^ 2 / 4) ∂Measure.pi fun i ↦ μ (e i)) =
      ∫ x, Real.exp (infDist (WithLp.toLp 2 x) A ^ 2 / 4) ∂Measure.pi μ := by
    rw [← hg.integral_comp']
    simp only [hcoord, ← infDist_closure (s := A), ← hSmap, infDist_image E.isometry]
  rw [hmass, hI] at h
  exact (mul_le_mul_of_nonneg_right (measureReal_mono (preimage_mono subset_closure))
    (integral_nonneg fun _ ↦ Real.exp_nonneg _)).trans h

/-- For a quasiconvex `L`-Lipschitz observable of a bounded product, the product of the
probabilities of being at most `s` and at least `s + t` is bounded by `exp (−(t / L)² / 4)`. -/
theorem measureReal_mul_measureReal_le_of_quasiconvexOn_lipschitzWith
    (hwidth : ∀ i, b i - a i ≤ 1) (hμ : ∀ i, ∀ᵐ x ∂μ i, x ∈ Icc (a i) (b i))
    {L : ℝ≥0} {f : EuclideanSpace ℝ ι → ℝ}
    (hconv : QuasiconvexOn ℝ univ f) (hL : LipschitzWith L f)
    (s : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi μ).real {x | f (WithLp.toLp 2 x) ≤ s} *
      (Measure.pi μ).real {x | s + t ≤ f (WithLp.toLp 2 x)} ≤
      Real.exp (-(t / (L : ℝ)) ^ 2 / 4) := by
  by_cases hL₀ : (L : ℝ) = 0
  · simpa [hL₀] using
      (mul_le_mul (α := ℝ) (measureReal_le_one (μ := Measure.pi μ)
        (s := {x | f (WithLp.toLp 2 x) ≤ s})) (measureReal_le_one (μ := Measure.pi μ)
        (s := {x | s + t ≤ f (WithLp.toLp 2 x)})) measureReal_nonneg zero_le_one)
  have hLpos : 0 < (L : ℝ) := lt_of_le_of_ne L.coe_nonneg (Ne.symm hL₀)
  let A := {x | f x ≤ s}
  let B := {x : ι → ℝ | s + t ≤ f (WithLp.toLp 2 x)}
  let p := (Measure.pi μ).real (WithLp.toLp 2 ⁻¹' A)
  let c := Real.exp ((t / (L : ℝ)) ^ 2 / 4)
  have hp₀ : 0 ≤ p := measureReal_nonneg
  by_cases hp : p = 0
  · have hz : (Measure.pi μ).real {x | f (WithLp.toLp 2 x) ≤ s} = 0 := by
      simpa only [p, A, preimage_ofPred_eq] using hp
    simp [hz, Real.exp_nonneg]
  have hAne : A.Nonempty := by
    contrapose! hp
    simp [p, hp]
  have hAc : Convex ℝ A := by
    simpa only [mem_univ, true_and] using hconv s
  have hb := measureReal_mul_integral_exp_infDist_sq_div_four_le hwidth hμ hAc
  have hE : c * (Measure.pi μ).real B ≤ ∫ x, expSqInfDist A (WithLp.toLp 2 x) ∂Measure.pi μ := by
    refine le_trans (mul_le_mul_of_nonneg_left (measureReal_mono ?_ (measure_ne_top _ _))
      (Real.exp_nonneg _)) (mul_meas_ge_le_integral_of_nonneg
      (ae_of_all _ fun _ ↦ Real.exp_nonneg _)
      (integrable_expSqInfDist_toLp hμ A) c)
    intro x hx
    have hd : t / (L : ℝ) ≤ infDist (WithLp.toLp 2 x) A := by
      refine (le_infDist hAne).2 fun y hy ↦ (div_le_iff₀ hLpos).2 ?_
      have hLip := hL.dist_le_mul (WithLp.toLp 2 x) y
      rw [Real.dist_eq] at hLip
      have hx' : s + t ≤ f (WithLp.toLp 2 x) := hx
      have hy' : f y ≤ s := hy
      calc
        t ≤ f (WithLp.toLp 2 x) - f y := by linarith
        _ ≤ |f (WithLp.toLp 2 x) - f y| := le_abs_self _
        _ ≤ _ := by simpa only [mul_comm] using hLip
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      ((sq_le_sq₀ (div_nonneg ht hLpos.le) infDist_nonneg).2 hd) (by norm_num))
  have hpB : (p * (Measure.pi μ).real B) * c ≤ 1 := by
    calc
      _ = p * (c * (Measure.pi μ).real B) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hE hp₀).trans hb
  exact (le_div_iff₀ (Real.exp_pos _)).2 hpB |>.trans_eq (by rw [one_div, ← Real.exp_neg]; ring_nf)

/-- **Talagrand's quasiconvex Lipschitz inequality** about any median. The bound is dimension-free,
and the individual coordinate laws can differ. -/
theorem measureReal_abs_sub_median_ge_le_of_quasiconvexOn_lipschitzWith
    (hwidth : ∀ i, b i - a i ≤ 1) (hμ : ∀ i, ∀ᵐ x ∂μ i, x ∈ Icc (a i) (b i))
    {L : ℝ≥0} {f : EuclideanSpace ℝ ι → ℝ}
    (hconv : QuasiconvexOn ℝ univ f) (hL : LipschitzWith L f)
    {m t : ℝ} (hm : ((Measure.pi μ).map (fun x ↦ f (WithLp.toLp 2 x))).IsMedian m)
    (ht : 0 ≤ t) :
    (Measure.pi μ).real {x | t ≤ |f (WithLp.toLp 2 x) - m|} ≤
      4 * Real.exp (-(t / (L : ℝ)) ^ 2 / 4) := by
  have hf : Measurable (fun x : ι → ℝ ↦ f (WithLp.toLp 2 x)) :=
    hL.continuous.measurable.comp (WithLp.measurable_toLp 2 _)
  obtain ⟨hm₁, hm₂⟩ := Measure.isMedian_iff.1 hm
  simp only [map_measureReal_apply hf measurableSet_Iic, preimage, mem_Iic] at hm₁
  simp only [map_measureReal_apply hf measurableSet_Ici, preimage, mem_Ici] at hm₂
  let U := {x : ι → ℝ | m + t ≤ f (WithLp.toLp 2 x)}
  let D := {x : ι → ℝ | f (WithLp.toLp 2 x) ≤ m - t}
  have hu := measureReal_mul_measureReal_le_of_quasiconvexOn_lipschitzWith hwidth hμ hconv hL m ht
  have hd := measureReal_mul_measureReal_le_of_quasiconvexOn_lipschitzWith
    hwidth hμ hconv hL (m - t) ht
  rw [sub_add_cancel] at hd
  have hu' : (Measure.pi μ).real U ≤ 2 * Real.exp (-(t / (L : ℝ)) ^ 2 / 4) := by
    have h := mul_le_mul_of_nonneg_right hm₁ (measureReal_nonneg (μ := Measure.pi μ) (s := U))
    linarith only [h, hu]
  have hd' : (Measure.pi μ).real D ≤ 2 * Real.exp (-(t / (L : ℝ)) ^ 2 / 4) := by
    have h := mul_le_mul_of_nonneg_left hm₂ (measureReal_nonneg (μ := Measure.pi μ) (s := D))
    linarith only [h, hd]
  calc
    _ ≤ (Measure.pi μ).real U + (Measure.pi μ).real D := by
      simpa only [U, D, neg_sub, le_sub_iff_add_le', add_comm] using
        (TauCeti.measureReal_le_abs_le_add (μ := Measure.pi μ)
          (f := fun x ↦ f (WithLp.toLp 2 x) - m) (ε := t))
    _ ≤ _ := by linarith only [hu', hd']

private theorem abs_integral_sub_median_le_of_quasiconvexOn_lipschitzWith
    (hwidth : ∀ i, b i - a i ≤ 1) (hμ : ∀ i, ∀ᵐ x ∂μ i, x ∈ Icc (a i) (b i))
    {L : ℝ≥0} {f : EuclideanSpace ℝ ι → ℝ}
    (hconv : QuasiconvexOn ℝ univ f) (hL : LipschitzWith L f)
    {m : ℝ} (hm : ((Measure.pi μ).map (fun x ↦ f (WithLp.toLp 2 x))).IsMedian m) :
    |(∫ x, f (WithLp.toLp 2 x) ∂Measure.pi μ) - m| ≤ 8 * (L : ℝ) := by
  by_cases hzero : L = 0
  · have hf : Measurable (fun x : ι → ℝ ↦ f (WithLp.toLp 2 x)) :=
      hL.continuous.measurable.comp (WithLp.measurable_toLp 2 _)
    rw [Measure.isMedian_iff, map_measureReal_apply hf measurableSet_Iic,
      map_measureReal_apply hf measurableSet_Ici] at hm
    obtain ⟨hm₁, hm₂⟩ := hm
    have hconst (x : ι → ℝ) : f (WithLp.toLp 2 x) = f 0 :=
      (LipschitzWith.zero_iff f).1 (hzero ▸ hL) _ _
    have hfm : f 0 = m := le_antisymm
      (le_of_not_gt fun h ↦ by norm_num [preimage, mem_Iic, hconst, not_le.2 h] at hm₁)
      (le_of_not_gt fun h ↦ by norm_num [preimage, mem_Ici, hconst, not_le.2 h] at hm₂)
    simp [hzero, hconst, hfm]
  let F := fun x : ι → ℝ ↦ f (WithLp.toLp 2 x)
  let P := Measure.pi μ
  let q := fun t : ℝ ↦ P.real {x | t < |F x - m|}
  let c := (4 * (L : ℝ) ^ 2)⁻¹
  have hF : Integrable F P := by
    rw [← Measure.restrict_eq_self_of_ae_mem (μ := P) (s := univ.pi fun i ↦ Icc (a i) (b i))
      (Measure.ae_pi_le_pi (Filter.pi_mem_pi finite_univ fun i _ ↦ hμ i))]
    exact ContinuousOn.integrableOn_compact (isCompact_univ_pi fun _ ↦ isCompact_Icc)
      (hL.continuous.comp (PiLp.continuous_toLp _ _)).continuousOn
  have hq : ∀ t > 0, q t ≤ 4 * Real.exp (-c * t ^ 2) := by
    intro t ht
    have heq : -(t / (L : ℝ)) ^ 2 / 4 = -c * t ^ 2 := by dsimp [c]; ring
    have hmed := measureReal_abs_sub_median_ge_le_of_quasiconvexOn_lipschitzWith
      hwidth hμ hconv hL hm ht.le
    exact heq ▸ (measureReal_mono (ofPred_subset_ofPred.2 fun _ hx ↦ hx.le)).trans hmed
  have hg : IntegrableOn (fun t : ℝ ↦ 4 * Real.exp (-c * t ^ 2)) (Ioi 0) :=
    ((integrable_exp_neg_mul_sq (by positivity : 0 < c)).const_mul 4).integrableOn
  have hqm : Antitone q := fun _ _ htu ↦ measureReal_mono (preimage_mono (Ioi_subset_Ioi htu))
  have hqi : IntegrableOn q (Ioi 0) := hg.mono' hqm.measurable.aestronglyMeasurable (by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact hq t ht)
  have hr : Real.pi / c = (2 * (L : ℝ)) ^ 2 * Real.pi := by rw [div_inv_eq_mul]; ring
  calc
    _ ≤ ∫ x, |F x - m| ∂P := by
      simpa [Real.norm_eq_abs, integral_sub hF (integrable_const m)] using
        norm_integral_le_integral_norm (μ := P) (fun x ↦ F x - m)
    _ = ∫ t in Ioi (0 : ℝ), q t := (hF.sub (integrable_const m)).abs.integral_eq_integral_meas_lt
      (ae_of_all _ fun x ↦ abs_nonneg (F x - m))
    _ ≤ ∫ t in Ioi (0 : ℝ), 4 * Real.exp (-c * t ^ 2) :=
      setIntegral_mono_on hqi hg measurableSet_Ioi hq
    _ = 4 * (L : ℝ) * √Real.pi := by
      rw [integral_const_mul, integral_gaussian_Ioi, hr, Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq (by positivity : 0 ≤ 2 * (L : ℝ))]
      ring
    _ ≤ 8 * (L : ℝ) := by
      have hs : √Real.pi ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by linarith [Real.pi_le_four]⟩
      nlinarith only [mul_nonneg L.coe_nonneg (sub_nonneg.2 hs)]

/-- **Talagrand's quasiconvex Lipschitz inequality** about the expectation, with an absolute
constant in the exponent. -/
theorem measureReal_abs_sub_integral_ge_le_of_quasiconvexOn_lipschitzWith
    (hwidth : ∀ i, b i - a i ≤ 1) (hμ : ∀ i, ∀ᵐ x ∂μ i, x ∈ Icc (a i) (b i))
    {L : ℝ≥0} {f : EuclideanSpace ℝ ι → ℝ}
    (hconv : QuasiconvexOn ℝ univ f) (hL : LipschitzWith L f) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi μ).real {x | t ≤ |f (WithLp.toLp 2 x) -
      ∫ y, f (WithLp.toLp 2 y) ∂Measure.pi μ|} ≤ 4 * Real.exp (-(t / (L : ℝ)) ^ 2 / 256) := by
  by_cases hL₀ : (L : ℝ) = 0
  · simpa [hL₀] using measureReal_le_one.trans (by norm_num : (1 : ℝ) ≤ 4)
  have hLpos : 0 < (L : ℝ) := lt_of_le_of_ne L.coe_nonneg (Ne.symm hL₀)
  by_cases htlarge : 16 * (L : ℝ) ≤ t
  swap
  · have ht' : t / (L : ℝ) ≤ 16 := (div_le_iff₀ hLpos).2 (by linarith)
    have hsq := (sq_le_sq₀ (div_nonneg ht hLpos.le) (by norm_num)).2 ht'
    have he : Real.exp (-1) ≤ Real.exp (-(t / (L : ℝ)) ^ 2 / 256) :=
      Real.exp_le_exp.mpr (by linarith only [hsq])
    exact measureReal_le_one.trans (by linarith [Real.exp_neg_one_gt_d9])
  let F := fun x : ι → ℝ ↦ f (WithLp.toLp 2 x)
  let P := Measure.pi μ
  let m := (P.map F).quantile 2⁻¹
  have hm := Measure.isMedian_quantile_half (P.map F)
  have hbound := abs_integral_sub_median_le_of_quasiconvexOn_lipschitzWith hwidth hμ hconv hL hm
  have hmed := measureReal_abs_sub_median_ge_le_of_quasiconvexOn_lipschitzWith hwidth hμ hconv hL
    hm (t := t / 2) (by positivity)
  calc
    _ ≤ P.real {x | t / 2 ≤ |F x - m|} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro x (hx : t ≤ |F x - ∫ y, F y ∂P|)
      have htriangle := abs_sub_le (F x) m (∫ y, F y ∂P)
      rw [abs_sub_comm m] at htriangle
      have hshift : |(∫ y, F y ∂P) - m| ≤ 8 * (L : ℝ) := hbound
      simp only [mem_ofPred_eq]
      linarith only [hx, htriangle, hshift, htlarge]
    _ ≤ _ := by
      refine hmed.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
      rw [div_right_comm t 2 (L : ℝ)]
      nlinarith only [sq_nonneg (t / (L : ℝ))]

end Fintype

end

end TauCeti.Probability

namespace ProbabilityTheory.iIndepFun

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
  {X : ι → Ω → ℝ} {a b : ι → ℝ} {L : ℝ≥0} {f : EuclideanSpace ℝ ι → ℝ}

private theorem hasLaw_pi_and_ae_mem_Icc (hi : iIndepFun X P)
    (hX : ∀ i, AEMeasurable (X i) P) (hbox : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc (a i) (b i)) :
    HasLaw (fun ω i ↦ X i ω) (Measure.pi fun i ↦ P.map (X i)) P ∧
      ∀ i, ∀ᵐ x ∂P.map (X i), x ∈ Icc (a i) (b i) :=
  ⟨hi.hasLaw_pi (fun i ↦ hasLaw_map (hX i)),
    fun i ↦ (ae_map_iff (hX i) measurableSet_Icc).2 (hbox i)⟩

/-- Talagrand's two-sided median bound for a quasiconvex Lipschitz function of independent real
coordinates, each almost surely in an interval of length at most one. -/
theorem measureReal_abs_sub_median_ge_le_of_quasiconvexOn_lipschitzWith (hi : iIndepFun X P)
    (hX : ∀ i, AEMeasurable (X i) P) (hwidth : ∀ i, b i - a i ≤ 1)
    (hbox : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc (a i) (b i))
    (hconv : QuasiconvexOn ℝ univ f) (hL : LipschitzWith L f) {m t : ℝ}
    (hm : (P.map (fun ω ↦ f (WithLp.toLp 2 (fun i ↦ X i ω)))).IsMedian m)
    (ht : 0 ≤ t) :
    P.real {ω | t ≤ |f (WithLp.toLp 2 (fun i ↦ X i ω)) - m|} ≤
      4 * Real.exp (-(t / (L : ℝ)) ^ 2 / 4) := by
  have := hi.isProbabilityMeasure
  obtain ⟨h, hμ⟩ := hasLaw_pi_and_ae_mem_Icc hi hX hbox
  have hf : Measurable (fun x : ι → ℝ ↦ f (WithLp.toLp 2 x)) :=
    hL.continuous.measurable.comp (WithLp.measurable_toLp 2 _)
  have hmap := hf.aemeasurable.map_map_of_aemeasurable h.aemeasurable
  rw [h.map_eq, Function.comp_def] at hmap
  rw [← hmap] at hm
  have hg : Measurable (fun x : ι → ℝ ↦ |f (WithLp.toLp 2 x) - m|) :=
    continuous_abs.measurable.comp (hf.sub_const m)
  rw [h.measureReal_eq (measurableSet_le measurable_const hg)]
  exact TauCeti.Probability.measureReal_abs_sub_median_ge_le_of_quasiconvexOn_lipschitzWith
    hwidth hμ hconv hL hm ht

/-- Talagrand's two-sided mean bound for a quasiconvex Lipschitz function of independent real
coordinates, each almost surely in an interval of length at most one. -/
theorem measureReal_abs_sub_integral_ge_le_of_quasiconvexOn_lipschitzWith (hi : iIndepFun X P)
    (hX : ∀ i, AEMeasurable (X i) P) (hwidth : ∀ i, b i - a i ≤ 1)
    (hbox : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc (a i) (b i))
    (hconv : QuasiconvexOn ℝ univ f) (hL : LipschitzWith L f) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t ≤ |f (WithLp.toLp 2 (fun i ↦ X i ω)) -
      ∫ ω', f (WithLp.toLp 2 (fun i ↦ X i ω')) ∂P|} ≤ 4 * Real.exp (-(t / (L : ℝ)) ^ 2 / 256) := by
  have := hi.isProbabilityMeasure
  obtain ⟨h, hμ⟩ := hasLaw_pi_and_ae_mem_Icc hi hX hbox
  have hf : Measurable (fun x : ι → ℝ ↦ f (WithLp.toLp 2 x)) :=
    hL.continuous.measurable.comp (WithLp.measurable_toLp 2 _)
  let m := ∫ x, f (WithLp.toLp 2 x) ∂Measure.pi (fun i ↦ P.map (X i))
  have heq : (∫ ω, f (WithLp.toLp 2 (fun i ↦ X i ω)) ∂P) = m :=
    h.integral_comp hf.aestronglyMeasurable
  have hg : Measurable (fun x : ι → ℝ ↦ |f (WithLp.toLp 2 x) - m|) :=
    continuous_abs.measurable.comp (hf.sub_const m)
  rw [heq, h.measureReal_eq (measurableSet_le measurable_const hg)]
  exact TauCeti.Probability.measureReal_abs_sub_integral_ge_le_of_quasiconvexOn_lipschitzWith
    hwidth hμ hconv hL ht

end ProbabilityTheory.iIndepFun
