/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Probability.BrownianMotion.Integral.Square
public import TauCeti.Probability.Martingale.QuadraticVariation.Covariation
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Independence.Integration
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Process.Progressive
import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# Quadratic variation and covariation of filtered Brownian motion

Connects `IsFilteredPreBrownianReal` and `Finance.simpleGains` to `IsQuadraticVariation` and
`IsCovariation`: `[B]_t = t`, elementary Brownian integrals, independent Brownian coordinates,
finite linear combinations, and orthonormal-basis inner-product projections.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §1.5, §3.2.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., 1999, Ch. IV, §1.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace NNReal Topology

namespace TauCeti.Probability

namespace IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {B B₁ B₂ W : ℝ≥0 → Ω → ℝ}

/-- A real pre-Brownian motion relative to `ℱ` has quadratic variation `t ↦ t`. -/
theorem isQuadraticVariation (hB : IsFilteredPreBrownianReal ℱ B P) :
    IsQuadraticVariation ℱ P B (fun t _ ↦ (t : ℝ)) :=
  IsQuadraticVariation.mk (NNReal.continuous_coe.stronglyMeasurable.isStronglyProgressive ℱ)
    (ae_of_all P fun _ ↦ NNReal.continuous_coe) (ae_of_all P fun _ ↦ NNReal.coe_mono)
    (ae_of_all P fun _ ↦ NNReal.coe_zero)
    (Locally.of_prop (p := fun Y ↦ Martingale Y ℱ P) hB.martingale_sq_sub_sq_zero_sub)

/-- Any quadratic variation of an a.s. continuous filtered Brownian motion is indistinguishable
from `t ↦ t`. -/
theorem indist_of_isQuadraticVariation (hB : IsFilteredPreBrownianReal ℱ B P)
    (hcB : ∀ᵐ ω ∂P, Continuous (B · ω)) {A : ℝ≥0 → Ω → ℝ} (hA : IsQuadraticVariation ℱ P B A) :
    A ≡ᵐ[P] fun t _ ↦ (t : ℝ) := by
  have := hB.isGaussianProcess.isProbabilityMeasure; exact hA.indist hB.isQuadraticVariation hcB

/-- **Quadratic variation of an elementary Brownian integral** with `L²` adapted heights. -/
theorem isQuadraticVariation_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ} (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i)) (ha₂ : ∀ i < n, MemLp (a i) 2 P) :
    IsQuadraticVariation ℱ P (Finance.simpleGains τ n a W)
      (fun t ω ↦ ∑ i ∈ Finset.range n, a i ω ^ 2 * (↑(min (τ (i + 1)) t) - ↑(min (τ i) t))) := by
  have hadp := Finance.stronglyAdapted_simpleGains hτ ha fun u ↦ (hW.adapted u).stronglyMeasurable
  have htime : IsStronglyProgressive ℱ (fun t (_ : Ω) ↦ (t : ℝ)) :=
    NNReal.continuous_coe.stronglyMeasurable.isStronglyProgressive ℱ
  have hprog := Finance.isStronglyProgressive_simpleGains hτ (fun i hi ↦ (ha i hi).pow 2) htime
  convert IsQuadraticVariation.mk hprog
    (ae_of_all P fun _ ↦ Finance.continuous_simpleGains NNReal.continuous_coe)
    (ae_of_all P fun _ ↦ Finance.monotone_simpleGains hτ (fun _ _ ↦ sq_nonneg _) NNReal.coe_mono)
    (ae_of_all P fun _ ↦ by simp [Finance.simpleGains_def])
    (Locally.of_prop (p := fun Y ↦ Martingale Y ℱ P)
      ((hW.martingale_sq_simpleGains_sub hτ ha ha₂).congr
        (fun t ↦ (((hadp t).pow 2).sub (((hadp 0).pow 2).mono (ℱ.mono bot_le))).sub
          (hprog.stronglyAdapted t))
        fun _ ↦ .of_forall fun _ ↦ by simp [Finance.simpleGains_def])) using 1
  ext t ω; exact (Finance.simpleGains_def τ n (fun i ω ↦ a i ω ^ 2) (fun u _ ↦ (u : ℝ)) t ω).symm

/-- **Covariation of two elementary Brownian integrals** on a common monotone grid. -/
theorem isCovariation_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a b : ℕ → Ω → ℝ} (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (hb : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (b i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) (hb₂ : ∀ i < n, MemLp (b i) 2 P) :
    IsCovariation ℱ P (Finance.simpleGains τ n a W) (Finance.simpleGains τ n b W)
      (fun t ω ↦ ∑ i ∈ Finset.range n,
        a i ω * b i ω * (↑(min (τ (i + 1)) t) - ↑(min (τ i) t))) := by
  let C := Finance.simpleGains τ n (a * b) (fun t _ ↦ (t : ℝ))
  have htime : IsStronglyProgressive ℱ (fun t (_ : Ω) ↦ (t : ℝ)) :=
    NNReal.continuous_coe.stronglyMeasurable.isStronglyProgressive ℱ
  have hC : (fun t ω ↦ ∑ i ∈ Finset.range n,
      a i ω * b i ω * (↑(min (τ (i + 1)) t) - ↑(min (τ i) t))) = C :=
    funext₂ fun t ω ↦ (Finance.simpleGains_def τ n (a * b) (fun u _ ↦ (u : ℝ)) t ω).symm
  rw [hC]; refine IsCovariation.mk
    (Finance.isStronglyProgressive_simpleGains hτ (fun i hi ↦ (ha i hi).mul (hb i hi)) htime)
    (ae_of_all P fun _ ↦ Finance.continuous_simpleGains NNReal.continuous_coe)
    (ae_of_all P fun _ ↦ Finance.locallyBoundedVariationOn_simpleGains
      (NNReal.coe_mono.monotoneOn Set.univ).locallyBoundedVariationOn)
    (ae_of_all P fun _ ↦ by simp [C, Finance.simpleGains_def]) ?_
  convert Locally.of_prop (p := fun Y ↦ Martingale Y ℱ P)
    (hW.martingale_mul_simpleGains_sub hτ ha hb ha₂ hb₂) using 1
  ext t ω; simp [C, Finance.simpleGains_def]

private theorem condExp_mul_sub_eq_zero (hB₁ : IsFilteredPreBrownianReal ℱ B₁ P)
    (hB₂ : IsFilteredPreBrownianReal ℱ B₂ P) {s t : ℝ≥0}
    (hindep_past : Indep (.comap (fun ω ↦ (B₁ t ω - B₁ s ω, B₂ t ω - B₂ s ω)) inferInstance)
      (ℱ s) P) (hindep_inc : IndepFun (B₁ t - B₁ s) (B₂ t - B₂ s) P) :
    P[(B₁ t - B₁ s) * (B₂ t - B₂ s) | ℱ s] =ᵐ[P] 0 := by
  have := hB₁.isGaussianProcess.isProbabilityMeasure
  let pair (ω : Ω) : ℝ × ℝ := (B₁ t ω - B₁ s ω, B₂ t ω - B₂ s ω)
  have hcond : P[(B₁ t - B₁ s) * (B₂ t - B₂ s) | ℱ s] =ᵐ[P]
      fun _ ↦ ∫ ω, (B₁ t ω - B₁ s ω) * (B₂ t ω - B₂ s ω) ∂P :=
    condExp_indep_eq ((hB₁.adapted.measurable.sub hB₁.adapted.measurable).prodMk
      (hB₂.adapted.measurable.sub hB₂.adapted.measurable)).comap_le (ℱ.le s)
      (((continuous_fst.mul continuous_snd).stronglyMeasurable).comp_measurable
        (comap_measurable pair)) hindep_past
  have hm₁ : ∫ ω, B₁ t ω - B₁ s ω ∂P = 0 := by
    rw [integral_sub (hB₁.integrable_eval t) (hB₁.integrable_eval s),
      hB₁.integral_eval, hB₁.integral_eval, sub_self]
  have hint_zero : ∫ ω, (B₁ t ω - B₁ s ω) * (B₂ t ω - B₂ s ω) ∂P = 0 := by
    simpa only [Pi.sub_apply, hm₁, zero_mul] using hindep_inc.integral_fun_mul_eq_mul_integral
      (hB₁.adapted.measurable.sub hB₁.adapted.measurable).aestronglyMeasurable
      (hB₂.adapted.measurable.sub hB₂.adapted.measurable).aestronglyMeasurable
  simpa only [hint_zero, Pi.zero_def] using hcond

/-- **Product martingale of independent filtered Brownian motions** with past-independent and
mutually independent increments. -/
theorem martingale_mul_of_indep_sub (hB₁ : IsFilteredPreBrownianReal ℱ B₁ P)
    (hB₂ : IsFilteredPreBrownianReal ℱ B₂ P)
    (hindep_past : ∀ ⦃s t⦄, s ≤ t →
      Indep (.comap (fun ω ↦ (B₁ t ω - B₁ s ω, B₂ t ω - B₂ s ω)) inferInstance) (ℱ s) P)
    (hindep_inc : ∀ ⦃s t⦄, s ≤ t → IndepFun (B₁ t - B₁ s) (B₂ t - B₂ s) P) :
    Martingale (B₁ * B₂) ℱ P := by
  have := hB₁.isGaussianProcess.isProbabilityMeasure
  refine ⟨fun t ↦ ((hB₁.adapted t).mul (hB₂.adapted t)).stronglyMeasurable, fun s t hst ↦ ?_⟩
  let Δ₁ := B₁ t - B₁ s; let Δ₂ := B₂ t - B₂ s
  have hL₁ (u : ℝ≥0) : MemLp (B₁ u) 2 P := hB₁.memLp_eval u (by simp)
  have hL₂ (u : ℝ≥0) : MemLp (B₂ u) 2 P := hB₂.memLp_eval u (by simp)
  have hi₀ : Integrable (B₁ s * B₂ s) P := (hL₁ s).integrable_mul (hL₂ s)
  have hi₁ : Integrable (Δ₁ * Δ₂) P := ((hL₁ t).sub (hL₁ s)).integrable_mul ((hL₂ t).sub (hL₂ s))
  have hi₂ : Integrable (B₁ s * Δ₂) P := (hL₁ s).integrable_mul ((hL₂ t).sub (hL₂ s))
  have hi₃ : Integrable (B₂ s * Δ₁) P := (hL₂ s).integrable_mul ((hL₁ t).sub (hL₁ s))
  have hcross {U V : ℝ≥0 → Ω → ℝ} (hU : IsFilteredPreBrownianReal ℱ U P)
      (hV : IsFilteredPreBrownianReal ℱ V P) : P[U s * (V t - V s) | ℱ s] =ᵐ[P] 0 := by
    simpa only [min_self, min_eq_left hst, min_eq_right hst, sub_self, mul_zero,
      Pi.mul_def, Pi.sub_def, Pi.zero_def] using (hV.martingale_mul_sub_min hst
        (hU.adapted s).stronglyMeasurable (hU.integrable_eval s)).condExp_ae_eq hst
  have hsplit : (B₁ * B₂) t = B₁ s * B₂ s + (Δ₁ * Δ₂ + (B₁ s * Δ₂ + B₂ s * Δ₁)) := by
    ext; simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Δ₁, Δ₂]; ring
  rw [hsplit]
  have hbase := condExp_of_stronglyMeasurable (ℱ.le s)
    ((hB₁.adapted s).mul (hB₂.adapted s)).stronglyMeasurable hi₀
  filter_upwards [condExp_add hi₀ (hi₁.add (hi₂.add hi₃)) (ℱ s),
    condExp_add hi₁ (hi₂.add hi₃) (ℱ s), condExp_add hi₂ hi₃ (ℱ s),
    condExp_mul_sub_eq_zero hB₁ hB₂ (hindep_past hst) (hindep_inc hst),
    hcross hB₁ hB₂, hcross hB₂ hB₁] with ω h1 h2 h3 z1 z2 z3
  dsimp only [Δ₁, Δ₂] at h1 h2 h3 ⊢
  simp only [Pi.add_apply, Pi.zero_apply] at h1 h2 h3 z1 z2 z3 ⊢
  rw [h1, hbase, h2, h3, z1, z2, z3]; simp

private theorem martingale_mul_sub_zero (hB₁ : IsFilteredPreBrownianReal ℱ B₁ P)
    (hB₂ : IsFilteredPreBrownianReal ℱ B₂ P) (hmul : Martingale (B₁ * B₂) ℱ P) :
    Martingale (fun t ω ↦ B₁ t ω * B₂ t ω - B₁ 0 ω * B₂ 0 ω) ℱ P :=
  hmul.congr (fun t ↦ ((hB₁.adapted t).stronglyMeasurable.mul
      (hB₂.adapted t).stronglyMeasurable).sub (((hB₁.adapted 0).stronglyMeasurable.mul
      (hB₂.adapted 0).stronglyMeasurable).mono (ℱ.mono bot_le)))
    fun _ ↦ hB₁.eval_zero_ae_eq_zero.mono fun _ h0 ↦ by simp [h0]

/-- Filtered pre-Brownian motions whose product `B₁ * B₂` is a martingale have zero covariation. -/
theorem isCovariation_zero_of_martingale_mul (hB₁ : IsFilteredPreBrownianReal ℱ B₁ P)
    (hB₂ : IsFilteredPreBrownianReal ℱ B₂ P) (hmul : Martingale (B₁ * B₂) ℱ P) :
    IsCovariation ℱ P B₁ B₂ 0 := by
  refine IsCovariation.mk (isStronglyProgressive_const ℱ 0) (ae_of_all P fun _ ↦ continuous_const)
    (ae_of_all P fun _ ↦ locallyBoundedVariationOn_const 0 Set.univ) .rfl ?_
  simpa only [Pi.zero_apply, sub_zero] using Locally.of_prop (p := fun Y ↦ Martingale Y ℱ P)
    (hB₁.martingale_mul_sub_zero hB₂ hmul)

/-- Independent filtered Brownian motions have zero covariation. -/
theorem isCovariation_zero_of_indep_sub (hB₁ : IsFilteredPreBrownianReal ℱ B₁ P)
    (hB₂ : IsFilteredPreBrownianReal ℱ B₂ P)
    (hindep_past : ∀ ⦃s t⦄, s ≤ t →
      Indep (.comap (fun ω ↦ (B₁ t ω - B₁ s ω, B₂ t ω - B₂ s ω)) inferInstance) (ℱ s) P)
    (hindep_inc : ∀ ⦃s t⦄, s ≤ t → IndepFun (B₁ t - B₁ s) (B₂ t - B₂ s) P) :
    IsCovariation ℱ P B₁ B₂ 0 :=
  hB₁.isCovariation_zero_of_martingale_mul hB₂
    (hB₁.martingale_mul_of_indep_sub hB₂ hindep_past hindep_inc)

end IsFilteredPreBrownianReal

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}

open scoped Classical in
private theorem martingale_mul_sub_mul_zero_sub_ite {B : ι → ℝ≥0 → Ω → ℝ} {i j : ι}
    (hBi : IsFilteredPreBrownianReal ℱ (B i) P) (hBj : IsFilteredPreBrownianReal ℱ (B j) P)
    (horth : i ≠ j → Martingale (B i * B j) ℱ P) :
    Martingale (fun t ω ↦
      B i t ω * B j t ω - B i 0 ω * B j 0 ω - if i = j then (t : ℝ) else 0) ℱ P := by
  by_cases hij : i = j
  · subst hij; simpa only [↓reduceIte, sq] using hBi.martingale_sq_sub_sq_zero_sub
  · simpa only [hij, ↓reduceIte, sub_zero] using hBi.martingale_mul_sub_zero hBj (horth hij)

/-- **Covariation of linear combinations of pairwise-orthogonal filtered Brownian motions.** -/
theorem isCovariation_sum_mul_of_martingale_mul (s : Finset ι) (u v : ι → ℝ)
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i ∈ s, IsFilteredPreBrownianReal ℱ (B i) P)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Martingale (B i * B j) ℱ P) :
    IsCovariation ℱ P (fun t ω ↦ ∑ i ∈ s, u i * B i t ω) (fun t ω ↦ ∑ j ∈ s, v j * B j t ω)
      (fun t _ ↦ (∑ i ∈ s, u i * v i) * (t : ℝ)) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · convert isCovariation_zero_left (ℱ := ℱ) (P := P) (0 : ℝ≥0 → Ω → ℝ) using 1 <;> (ext; simp)
  have := (hB i₀ hi₀).isGaussianProcess.isProbabilityMeasure
  let c := ∑ i ∈ s, u i * v i
  refine IsCovariation.mk
    ((continuous_const.mul NNReal.continuous_coe).stronglyMeasurable.isStronglyProgressive ℱ)
    (ae_of_all P fun _ ↦ continuous_const.mul NNReal.continuous_coe)
    (ae_of_all P fun _ ↦ ((lipschitzWith_smul c).comp_locallyBoundedVariationOn
      (NNReal.coe_mono.monotoneOn Set.univ).locallyBoundedVariationOn).congr fun _ _ ↦ rfl)
    (ae_of_all P fun _ ↦ by simp) ?_
  let K (p : ι × ι) (t : ℝ≥0) (ω : Ω) : ℝ :=
    B p.1 t ω * B p.2 t ω - B p.1 0 ω * B p.2 0 ω - if p.1 = p.2 then (t : ℝ) else 0
  have hsum_mart : Martingale (∑ p ∈ s ×ˢ s, (u p.1 * v p.2) • K p) ℱ P :=
    Finset.sum_induction _ (Martingale · ℱ P) (fun _ _ ↦ Martingale.add)
      (martingale_zero _ ℱ P) fun ⟨i, j⟩ hp ↦
        (martingale_mul_sub_mul_zero_sub_ite (hB i (Finset.mem_product.1 hp).1)
          (hB j (Finset.mem_product.1 hp).2)
          (horth i (Finset.mem_product.1 hp).1 j (Finset.mem_product.1 hp).2)).smul (u i * v j)
  convert Locally.of_prop (p := fun Y ↦ Martingale Y ℱ P) hsum_mart using 1; ext t ω
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, K, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_product, Finset.sum_mul_sum]
  have hmul (r : ℝ≥0) : ∑ x ∈ s, ∑ y ∈ s, u x * v y * (B x r ω * B y r ω) =
      ∑ x ∈ s, ∑ y ∈ s, u x * B x r ω * (v y * B y r ω) :=
    Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  have hdiag : ∑ x ∈ s, ∑ y ∈ s, u x * v y * (if x = y then (t : ℝ) else 0) = c * (t : ℝ) := by
    simp only [c, Finset.sum_mul]; refine Finset.sum_congr rfl fun x hx ↦ ?_; simp [mul_ite, hx]
  rw [hmul t, hmul 0, hdiag]

/-- **Quadratic variation of a linear combination of pairwise-orthogonal Brownian motions.** -/
theorem isQuadraticVariation_sum_mul_of_martingale_mul (s : Finset ι) (u : ι → ℝ)
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i ∈ s, IsFilteredPreBrownianReal ℱ (B i) P)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Martingale (B i * B j) ℱ P) :
    IsQuadraticVariation ℱ P (fun t ω ↦ ∑ i ∈ s, u i * B i t ω)
      (fun t _ ↦ (∑ i ∈ s, u i ^ 2) * (t : ℝ)) := by
  have hcov := isCovariation_sum_mul_of_martingale_mul s u u hB horth
  simp_rw [← sq] at hcov
  exact hcov.isQuadraticVariation_of_ae_monotone <| ae_of_all P fun _ _ _ hst ↦
    mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 hst) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

end TauCeti.Probability

namespace OrthonormalBasis

open TauCeti.Probability

variable {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Covariation of inner-product projections** `[⟨u, W⟩, ⟨v, W⟩]_t = ⟨u, v⟩ t`. -/
theorem isCovariation_inner_of_martingale_mul (b : OrthonormalBasis ι ℝ E) {W : ℝ≥0 → Ω → E}
    (hW : ∀ i, IsFilteredPreBrownianReal ℱ (fun t ω ↦ ⟪b i, W t ω⟫_ℝ) P)
    (horth : ∀ i j, i ≠ j → Martingale (fun t ω ↦ ⟪b i, W t ω⟫_ℝ * ⟪b j, W t ω⟫_ℝ) ℱ P) (u v : E) :
    IsCovariation ℱ P (fun t ω ↦ ⟪u, W t ω⟫_ℝ) (fun t ω ↦ ⟪v, W t ω⟫_ℝ)
      (fun t _ ↦ ⟪u, v⟫_ℝ * (t : ℝ)) := by
  have hexp (z : E) : (fun t ω ↦ ∑ i : ι, ⟪z, b i⟫_ℝ * ⟪b i, W t ω⟫_ℝ) = fun t ω ↦ ⟪z, W t ω⟫_ℝ :=
    funext₂ fun t ω ↦ b.sum_inner_mul_inner z (W t ω)
  have hinner : ∑ i : ι, ⟪u, b i⟫_ℝ * ⟪v, b i⟫_ℝ = ⟪u, v⟫_ℝ := by
    simpa only [real_inner_comm (b _)] using b.sum_inner_mul_inner u v
  simpa only [hexp, hinner] using isCovariation_sum_mul_of_martingale_mul Finset.univ
    (fun i ↦ ⟪u, b i⟫_ℝ) (fun j ↦ ⟪v, b j⟫_ℝ) (fun i _ ↦ hW i) fun i _ j _ hij ↦ horth i j hij

/-- **Quadratic variation of an inner-product projection** `[⟨u, W⟩]_t = ‖u‖² t`. -/
theorem isQuadraticVariation_inner_of_martingale_mul (b : OrthonormalBasis ι ℝ E) {W : ℝ≥0 → Ω → E}
    (hW : ∀ i, IsFilteredPreBrownianReal ℱ (fun t ω ↦ ⟪b i, W t ω⟫_ℝ) P)
    (horth : ∀ i j, i ≠ j → Martingale (fun t ω ↦ ⟪b i, W t ω⟫_ℝ * ⟪b j, W t ω⟫_ℝ) ℱ P) (u : E) :
    IsQuadraticVariation ℱ P (fun t ω ↦ ⟪u, W t ω⟫_ℝ) (fun t _ ↦ ‖u‖ ^ 2 * (t : ℝ)) := by
  have hcov := b.isCovariation_inner_of_martingale_mul hW horth u u
  rw [real_inner_self_eq_norm_sq] at hcov
  exact hcov.isQuadraticVariation_of_ae_monotone <| ae_of_all P fun _ _ _ hst ↦
    mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 hst) (sq_nonneg _)

end OrthonormalBasis
