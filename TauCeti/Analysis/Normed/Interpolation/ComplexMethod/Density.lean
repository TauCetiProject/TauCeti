/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
import Mathlib.Analysis.Normed.Group.Submodule
import TauCeti.Analysis.Fourier.AddCircle
import TauCeti.Topology.Algebra.InfiniteSum.Real

/-!
# Bounded boundary traces and Calderón's density lemma in the complex method

This file proves the bounded-boundary equivalence and density theorems of Bergh–Löfström §4.2 for
Calderón's complex interpolation space `[X₀, X₁]_θ`:
* **Bounded-boundary formulation (Lemma 4.2.1):** relaxing the `C₀(ℝ, X_j)` boundary-decay
  condition on admissible functions to bounded continuous traces in `ℝ →ᵇ X_j`
  (`CompatibleCouple.IsBoundedStripFunction`) leaves the space `[X₀, X₁]_θ` and its quotient norm
  unchanged (`ComplexMethodSpace.exists_toSum_eq_iff_isBoundedStripFunction`,
  `ComplexMethodSpace.norm_lt_iff_exists_isBoundedStripFunction`), with no completeness hypotheses
  on `X₀` or `X₁`.
* **Calderón's density lemma (Lemma 4.2.3 & Theorem 4.2.2 (a)):** for a Banach couple `(X₀, X₁)`,
  the submodule `CompatibleCouple.elementaryStripTraces` spanned over `ℂ` by the scalar-Gaussian
  multiples `z ↦ exp (δ z² + ω z) x` (`δ > 0`, `ω : ℝ`, `x ∈ X₀ ∩ X₁`) is dense in `stripTraces`
  (`CompatibleCouple.dense_elementaryStripTraces`). Taking quotient classes at `θ` shows that the
  intersection `X₀ ∩ X₁` is dense in `[X₀, X₁]_θ` (`ComplexMethodSpace.denseRange_ofInter`). These
  density results supply the approximation step for endpoint identifications, regularization
  invariance (`[X₀°, X₁°]_θ ≃ₗᵢ[ℂ] [X₀, X₁]_θ`), and complex-interpolation duality.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190, §§3–6.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §4.2 (Lemma 4.2.1, Theorem 4.2.2 (a), Lemma 4.2.3).
-/

public noncomputable section

open Complex Complex.HadamardThreeLines TauCeti.Complex.HadamardThreeLines
open Filter MeasureTheory Set Topology AddCircle
open scoped ZeroAtInfty BoundedContinuousFunction

namespace TauCeti.CompatibleCouple

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  (C : CompatibleCouple ℂ X₀ X₁ V)

/-! ### Bounded-boundary strip functions (Bergh–Löfström, Lemma 4.2.1) -/

namespace ComplexMethodSpace

variable {C} {θ : ℝ}

/-- **Bergh–Löfström, Lemma 4.2.1.** An element of `X₀ + X₁` belongs to `[X₀, X₁]_θ` (`0 ≤ θ ≤ 1`)
iff it is `F θ` for a bounded-boundary strip function `F`. -/
theorem exists_toSum_eq_iff_isBoundedStripFunction (hθ : θ ∈ Icc 0 1) {u : C.SumSpace} :
    (∃ v : C.ComplexMethodSpace θ, toSum v = u) ↔
      ∃ F g, C.IsBoundedStripFunction F g ∧ F θ = u := by
  rw [exists_toSum_eq_iff hθ]
  refine ⟨fun ⟨F, g, hF, h⟩ => ⟨F, (g.1.toBCF, g.2.toBCF), hF.isBoundedStripFunction, h⟩, ?_⟩
  rintro ⟨F, g, hF, rfl⟩
  obtain ⟨g', hg', -⟩ := hF.exists_isStripFunction_exp_smul_and_norm_le one_pos θ
  exact ⟨_, g', hg', by simp⟩

/-- **Bergh–Löfström, Lemma 4.2.1.** For `0 ≤ θ ≤ 1`, the quotient norm on `[X₀, X₁]_θ` coincides
with the infimum over bounded-boundary strip functions. -/
theorem norm_lt_iff_exists_isBoundedStripFunction (hθ : θ ∈ Icc 0 1) {u : C.ComplexMethodSpace θ}
    {r : ℝ} : ‖u‖ < r ↔ ∃ F g, C.IsBoundedStripFunction F g ∧ toSum u = F θ ∧ ‖g‖ < r := by
  refine ⟨fun hr => ?_, fun ⟨F, g, hF, hu, hg⟩ =>
    (norm_le_of_isBoundedStripFunction hθ hF hu).trans_lt hg⟩
  obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 hr
  refine ⟨C.stripFunction g, ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1.toBCF,
    (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2.toBCF),
    (C.isStripFunction_stripFunction g).isBoundedStripFunction,
    by rw [toSum_mk, stripEval_apply], ?_⟩
  simpa [Prod.norm_def, ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using hg

end ComplexMethodSpace

/-! ### Calderón's density lemma (Bergh–Löfström, Lemma 4.2.3) -/

section ElementaryTraces

private theorem complete_sq_expGaussian {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (z : ℂ) :
    exp (-((ω : ℂ) ^ 2 / (4 * δ))) * exp ((δ : ℂ) * (z - (-ω / (2 * δ) : ℝ)) ^ 2) =
      exp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) := by
  have : (δ : ℂ) ≠ 0 := ofReal_ne_zero.2 hδ.ne'
  rw [← Complex.exp_add]
  congr 1; push_cast; field_simp; ring

/-- The continuous linear map sending `x ∈ X₀ ∩ X₁` to the admissible boundary trace of
`z ↦ exp (δ z² + ω z) x` (`δ > 0`, `ω : ℝ`). -/
def expGaussianTrace {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) : C.inter →L[ℂ] C.stripTraces :=
  exp (-((ω : ℂ) ^ 2 / (4 * δ))) • C.gaussianTrace hδ (-ω / (2 * δ))

@[simp]
theorem expGaussianTrace_apply_fst {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter) (t : ℝ) :
    (C.expGaussianTrace hδ ω x : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t =
      exp ((δ : ℂ) * (t * I) ^ 2 + (ω : ℂ) * (t * I)) • C.interFst x := by
  simpa [expGaussianTrace, smul_smul] using
    congrArg (· • C.interFst x) (complete_sq_expGaussian hδ ω (t * I))

@[simp]
theorem expGaussianTrace_apply_snd {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter) (t : ℝ) :
    (C.expGaussianTrace hδ ω x : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t =
      exp ((δ : ℂ) * (1 + t * I) ^ 2 + (ω : ℂ) * (1 + t * I)) • C.interSnd x := by
  simpa [expGaussianTrace, smul_smul] using
    congrArg (· • C.interSnd x) (complete_sq_expGaussian hδ ω (1 + t * I))

theorem stripEval_expGaussianTrace {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) : C.stripEval z (C.expGaussianTrace hδ ω x) =
      exp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) • C.fstToSum (C.interFst x) := by
  rw [expGaussianTrace, smul_apply, map_smul,
    C.stripEval_gaussianTrace hδ _ x hz, smul_smul, complete_sq_expGaussian hδ]

@[simp]
theorem ComplexMethodSpace.mk_expGaussianTrace {C : CompatibleCouple ℂ X₀ X₁ V} {δ : ℝ}
    (hδ : 0 < δ) (ω θ : ℝ) (x : C.inter) :
    ComplexMethodSpace.mk θ (C.expGaussianTrace hδ ω x) =
      exp ((δ : ℂ) * (θ : ℂ) ^ 2 + (ω : ℂ) * (θ : ℂ)) • ComplexMethodSpace.ofInter θ x := by
  by_cases hθ : θ ∈ Icc 0 1
  · ext; rw [ComplexMethodSpace.toSum_mk, C.stripEval_expGaussianTrace hδ ω x (by simpa using hθ),
      map_smul, ComplexMethodSpace.toSum_ofInter hθ]
  · simp [ComplexMethodSpace.eq_zero_of_notMem hθ]

/-- The submodule of `C.stripTraces` spanned over `ℂ` by the boundary traces
`C.expGaussianTrace hδ ω x` of `z ↦ exp (δ z² + ω z) x` (`δ > 0`, `ω : ℝ`, `x : C.inter`). -/
def elementaryStripTraces : Submodule ℂ C.stripTraces := Submodule.span ℂ
  {g | ∃ (δ : ℝ) (hδ : 0 < δ) (ω : ℝ) (x : C.inter), C.expGaussianTrace hδ ω x = g}

theorem elementaryStripTraces_def : C.elementaryStripTraces = Submodule.span ℂ
    {g | ∃ (δ : ℝ) (hδ : 0 < δ) (ω : ℝ) (x : C.inter), C.expGaussianTrace hδ ω x = g} := (rfl)
theorem expGaussianTrace_mem_elementaryStripTraces {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter) :
    C.expGaussianTrace hδ ω x ∈ C.elementaryStripTraces := Submodule.subset_span ⟨δ, hδ, ω, x, rfl⟩
theorem elementaryStripTraces_le {S : Submodule ℂ C.stripTraces}
    (h : ∀ {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter), C.expGaussianTrace hδ ω x ∈ S) :
    C.elementaryStripTraces ≤ S := Submodule.span_le.2 fun _ ⟨_, hδ, ω, x, heq⟩ => heq ▸ h hδ ω x

variable {C} in
/-- Induction principle for `C.elementaryStripTraces`. -/
@[elab_as_elim]
theorem elementaryStripTraces_induction
    {p : (g : C.stripTraces) → g ∈ C.elementaryStripTraces → Prop}
    (expGaussian : ∀ {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter),
      p (C.expGaussianTrace hδ ω x) (C.expGaussianTrace_mem_elementaryStripTraces hδ ω x))
    (zero : p 0 C.elementaryStripTraces.zero_mem)
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (C.elementaryStripTraces.add_mem hx hy))
    (smul : ∀ (c : ℂ) x hx, p x hx → p (c • x) (C.elementaryStripTraces.smul_mem c hx))
    {g : C.stripTraces} (hg : g ∈ C.elementaryStripTraces) : p g hg :=
  Submodule.span_induction (by rintro _ ⟨_, hδ, ω, x, rfl⟩; exact expGaussian hδ ω x)
    zero add smul hg

private theorem exists_gaussian_smul_approx_single {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (a : ℝ) (f : C₀(ℝ, E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ {δ : ℝ}, 0 < δ → δ < δ₀ →
      ∀ t : ℝ, ‖exp ((2 * δ : ℝ) * (a + t * I) ^ 2) • f t - f t‖ ≤ ε := by
  have hlim : Tendsto (fun t : ℝ => ‖f t‖) (cocompact ℝ) (𝓝 0) := by
    simpa using (zero_at_infty f).norm
  obtain ⟨K, hK, hKc⟩ := mem_cocompact.1 (hlim.eventually (gt_mem_nhds (by positivity : 0 < ε / 4)))
  obtain ⟨R, _, hR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨η, hηpos, hη⟩ := Metric.continuousAt_iff.1
    (Complex.continuous_exp.continuousAt (x := 0)) (ε / (‖f‖ + 1)) (div_pos hε (by positivity))
  rw [Complex.exp_zero] at hη
  let B : ℝ := (|a| + R) ^ 2 + 1
  have hBpos : 0 < B := by positivity
  refine ⟨min (Real.log 2 / (2 * (a ^ 2 + 1))) (η / (2 * B)),
    lt_min (div_pos (Real.log_pos one_lt_two) (by positivity)) (div_pos hηpos (by positivity)),
    fun {δ} hδ hδlt t => ?_⟩
  by_cases ht : |t| ≤ R
  · have hsq : ‖(a + t * I : ℂ) ^ 2‖ < B :=
      ((norm_pow _ 2).trans_le (pow_le_pow_left₀ (norm_nonneg _)
        ((norm_add_le _ _).trans (by simpa using add_le_add_right ht |a|)) 2)).trans_lt
          (lt_add_one _)
    have hw : dist (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) 0 < η := by
      rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hδ' : 2 * δ < 2 * (η / (2 * B)) := by linarith [hδlt.trans_le (min_le_right _ _)]
      exact (mul_lt_mul'' hδ' hsq (by positivity) (norm_nonneg _)).trans_eq (by field_simp)
    have hexp_lt : ‖exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) - 1‖ < ε / (‖f‖ + 1) := by
      simpa [dist_eq_norm] using hη hw
    rw [show exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) • f t - f t =
      (exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) - 1) • f t by rw [sub_smul, one_smul], norm_smul]
    exact (mul_le_mul hexp_lt.le (f.norm_coe_le_norm t) (norm_nonneg _) (by positivity)).trans <| by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; linarith
  · have hft : ‖f t‖ < ε / 4 := hKc fun hm => not_le.2 (not_le.1 ht) (by simpa using hR t hm)
    have hexp_le : ‖exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2)‖ ≤ 2 := by
      rw [Complex.norm_exp, show (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2).re =
        2 * δ * (a ^ 2 - t ^ 2) by simp [sq]]
      refine (Real.exp_le_exp.2 ?_).trans_eq (Real.exp_log zero_lt_two)
      have := (lt_div_iff₀ (by positivity : 0 < 2 * (a ^ 2 + 1))).1
        (hδlt.trans_le (min_le_left _ _))
      nlinarith [sq_nonneg t]
    exact (norm_sub_le _ _).trans <| by
      rw [norm_smul]; linarith [mul_le_mul_of_nonneg_right hexp_le (norm_nonneg (f t))]
private theorem mul_natAbs_le_sq (T : ℝ) (k : ℤ) : T ^ 2 * (k.natAbs : ℝ) ≤ (k * T : ℝ) ^ 2 := by
  have hk : (k.natAbs : ℝ) ≤ (k : ℝ) ^ 2 := by
    simpa only [Int.cast_natCast, Int.cast_pow] using
      (Int.cast_le (R := ℝ)).2 (Int.natAbs_le_self_sq k)
  exact (mul_le_mul_of_nonneg_left hk (sq_nonneg T)).trans_eq (by ring)
private theorem exp_damped_shift_le {δ T B x y : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hx : x ∈ Icc 0 1) (hy : |y| ≤ B) (k : ℤ) :
    ‖exp ((δ : ℂ) * ((x : ℂ) + (y + k * T : ℝ) * I) ^ 2)‖ ≤
      Real.exp (δ * (1 + B ^ 2)) * (Real.exp (-(δ * T ^ 2 / 2))) ^ k.natAbs := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul, mul_comm (k.natAbs : ℝ), ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  rw [show ((δ : ℂ) * ((x : ℂ) + (y + k * T : ℝ) * I) ^ 2).re =
    δ * (x ^ 2 - (y + k * T) ^ 2) by simp [sq]]
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  have hy2 : y ^ 2 ≤ B ^ 2 := by rwa [sq_le_sq, abs_of_nonneg hB]
  nlinarith [mul_natAbs_le_sq T k, sq_nonneg (2 * y + k * T)]
private theorem norm_damped_shift_le {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)}
    (hF : C.IsStripFunction F g) {δ T B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (k : ℤ) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) (him : |z.im| ≤ B) :
    ‖exp ((δ : ℂ) * (z + k * T * I) ^ 2) • F (z + k * T * I)‖ ≤
      Real.exp (δ * (1 + B ^ 2)) * ‖g‖ * (Real.exp (-(δ * T ^ 2 / 2))) ^ k.natAbs := by
  rw [norm_smul, mul_right_comm (Real.exp (δ * (1 + B ^ 2))) ‖g‖]
  refine mul_le_mul ?_ (hF.norm_le (by simpa using hz)) (norm_nonneg _) (by positivity)
  rw [show z + k * T * I = (z.re : ℂ) + (z.im + k * T : ℝ) * I by
    nth_rw 1 [← re_add_im z]; push_cast; ring]
  exact exp_damped_shift_le hδ hB hz him k
private theorem norm_double_damped_shift_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : C₀(ℝ, E)) {a δ T : ℝ} (ha : a ∈ Icc 0 1) (hδ : 0 < δ) (k : ℤ) (t : ℝ) :
    ‖exp ((δ : ℂ) * (a + t * I) ^ 2) •
        (exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) • f (t + k * T))‖ ≤
      Real.exp (2 * δ) * ‖f‖ * (Real.exp (-(δ * T ^ 2 / 2))) ^ k.natAbs := by
  rw [norm_smul, norm_smul, Complex.norm_exp, Complex.norm_exp, ← mul_assoc, ← Real.exp_add,
    mul_right_comm, ← Real.exp_nat_mul, mul_comm (k.natAbs : ℝ), ← Real.exp_add]
  refine mul_le_mul (Real.exp_le_exp.2 ?_) (f.norm_coe_le_norm _) (norm_nonneg _) (by positivity)
  rw [show ((δ : ℂ) * (a + t * I) ^ 2).re = δ * (a ^ 2 - t ^ 2) by simp [sq],
    show ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2).re =
      δ * (a ^ 2 - (t + k * T) ^ 2) by simp [sq]]
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [ha.1, ha.2]
  nlinarith [mul_natAbs_le_sq T k, sq_nonneg (2 * t + k * T)]
private theorem tsum_sub_one_shift {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    (φ : ℤ → G) : (∑' k : ℤ, φ (k - 1)) = ∑' k : ℤ, φ k :=
  (Equiv.subRight (1 : ℤ)).tsum_eq φ

private def periodizeTrace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a δ T : ℝ) (f : C₀(ℝ, E)) (t : ℝ) : E :=
  ∑' k : ℤ, exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) • f (t + k * T)

private theorem norm_periodizeTrace_term_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : C₀(ℝ, E)) {a δ T B : ℝ} (ha : a ∈ Icc 0 1) (hδ : 0 < δ) (hB : 0 ≤ B)
    (k : ℤ) {t : ℝ} (ht : |t| ≤ B) :
    ‖exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) • f (t + k * T)‖ ≤
      Real.exp (δ * (1 + B ^ 2)) * ‖f‖ * (Real.exp (-(δ * T ^ 2 / 2))) ^ k.natAbs := by
  rw [norm_smul, mul_right_comm]
  exact mul_le_mul (exp_damped_shift_le hδ hB ha ht k) (f.norm_coe_le_norm _)
    (norm_nonneg _) (by positivity)

private theorem summable_periodizeTrace_term {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : C₀(ℝ, E)) {a δ T : ℝ} (ha : a ∈ Icc 0 1)
    (hδ : 0 < δ) (hT : 0 < T) (t : ℝ) :
    Summable fun k : ℤ => exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) • f (t + k * T) :=
  .of_norm_bounded ((summable_pow_natAbs (Real.exp_pos _).le
      (Real.exp_lt_one_iff.2 (neg_lt_zero.2 (by positivity)))).mul_left _) fun k =>
    norm_periodizeTrace_term_le f ha hδ (abs_nonneg t) k le_rfl

private theorem continuous_periodizeTrace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : C₀(ℝ, E)) {a δ T : ℝ} (ha : a ∈ Icc 0 1)
    (hδ : 0 < δ) (hT : 0 < T) : Continuous (periodizeTrace a δ T f) :=
  continuous_iff_continuousAt.2 fun t₀ => by
    set B := |t₀| + 1
    exact (continuousOn_tsum (fun k => by fun_prop)
      ((summable_pow_natAbs (Real.exp_pos _).le
        (Real.exp_lt_one_iff.2 (neg_lt_zero.2 (by positivity)))).mul_left
          (Real.exp (δ * (1 + B ^ 2)) * ‖f‖))
      fun k _ ht => norm_periodizeTrace_term_le f ha hδ (by positivity) k
        (le_of_lt ht)).continuousAt
      ((isOpen_lt (by fun_prop) continuous_const).mem_nhds (lt_add_one |t₀|))

private theorem periodic_periodizeTrace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a δ T : ℝ) (f : C₀(ℝ, E)) : Function.Periodic (periodizeTrace a δ T f) T := fun t => by
  rw [periodizeTrace, periodizeTrace, ← tsum_sub_one_shift]
  congr 1 with k
  rw [show t + T + ((k - 1 : ℤ) : ℝ) * T = t + (k : ℝ) * T by push_cast; ring]

private def periodizeStrip (δ T : ℝ) (F : ℂ → C.SumSpace) (z : ℂ) : C.SumSpace :=
  ∑' k : ℤ, exp ((δ : ℂ) * (z + k * T * I) ^ 2) • F (z + k * T * I)

private theorem differentiableOn_periodizeStrip [CompleteSpace X₀] [CompleteSpace X₁]
    {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g)
    {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) :
    DifferentiableOn ℂ (C.periodizeStrip δ T F) (verticalStrip 0 1) := fun z₀ hz₀ => by
  set B := |z₀.im| + 1
  let U : Set ℂ := verticalStrip 0 1 ∩ {z : ℂ | |z.im| < B}
  have hUopen : IsOpen U := (isOpen_verticalStrip 0 1).inter
    (isOpen_lt (continuous_abs.comp continuous_im) continuous_const)
  have hr₁ : Real.exp (-(δ * T ^ 2 / 2)) < 1 :=
    Real.exp_lt_one_iff.2 (neg_lt_zero.2 (by positivity))
  exact ((differentiableOn_tsum_of_summable_norm
    ((summable_pow_natAbs (Real.exp_pos _).le hr₁).mul_left
      (Real.exp (δ * (1 + B ^ 2)) * ‖g‖))
    (fun k => (by fun_prop : Differentiable ℂ fun z : ℂ =>
        exp ((δ : ℂ) * (z + k * T * I) ^ 2)).differentiableOn.smul
      (hF.diffContOnCl.differentiableOn.comp
        (by fun_prop : Differentiable ℂ fun z : ℂ => z + k * T * I).differentiableOn
        fun _ hz => by simpa using hz.1))
    hUopen fun k _ hz => norm_damped_shift_le C hF hδ (by positivity) k
      (verticalStrip_subset_verticalClosedStrip 0 1 hz.1) (le_of_lt hz.2)).differentiableAt
    (hUopen.mem_nhds ⟨hz₀, show |z₀.im| < B from lt_add_one _⟩)).differentiableWithinAt

private theorem continuousOn_periodizeStrip [CompleteSpace X₀] [CompleteSpace X₁]
    {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g)
    {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) :
    ContinuousOn (C.periodizeStrip δ T F) (closure (verticalStrip 0 1)) := by
  rw [closure_verticalStrip zero_ne_one]
  intro z₀ hz₀
  set B := |z₀.im| + 1
  have hFc : ContinuousOn F (verticalClosedStrip 0 1) := by
    simpa using hF.diffContOnCl.continuousOn
  have hr₁ : Real.exp (-(δ * T ^ 2 / 2)) < 1 :=
    Real.exp_lt_one_iff.2 (neg_lt_zero.2 (by positivity))
  exact (continuousOn_tsum (s := verticalClosedStrip 0 1 ∩ {z : ℂ | |z.im| < B})
    (fun (k : ℤ) => (by fun_prop : Continuous fun z : ℂ =>
        exp ((δ : ℂ) * (z + k * T * I) ^ 2)).continuousOn.smul
      (hFc.comp (by fun_prop : Continuous fun z : ℂ => z + k * T * I).continuousOn
        fun _ hz => by simpa using hz.1))
    ((summable_pow_natAbs (Real.exp_pos _).le hr₁).mul_left
      (Real.exp (δ * (1 + B ^ 2)) * ‖g‖))
    (fun k _ hz => norm_damped_shift_le C hF hδ (by positivity) k hz.1 (le_of_lt hz.2)) z₀
    ⟨hz₀, show |z₀.im| < B from lt_add_one _⟩).mono_of_mem_nhdsWithin <|
    inter_mem_nhdsWithin _ <| (isOpen_lt (continuous_abs.comp continuous_im)
      continuous_const).mem_nhds (show |z₀.im| < B from lt_add_one _)

private theorem diffContOnCl_periodizeStrip [CompleteSpace X₀] [CompleteSpace X₁]
    {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g)
    {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) :
    DiffContOnCl ℂ (C.periodizeStrip δ T F) (verticalStrip 0 1) :=
  ⟨differentiableOn_periodizeStrip C hF hδ hT, continuousOn_periodizeStrip C hF hδ hT⟩

omit [T1Space V] in
private theorem periodizeStrip_add_mul_I (δ T : ℝ) (F : ℂ → C.SumSpace) (z : ℂ) :
    C.periodizeStrip δ T F (z + T * I) = C.periodizeStrip δ T F z := by
  rw [periodizeStrip, periodizeStrip, ← tsum_sub_one_shift]
  congr 1 with k
  rw [show z + T * I + ((k - 1 : ℤ) : ℂ) * T * I = z + (k : ℂ) * T * I by push_cast; ring]

private theorem periodizeStrip_mul_I [CompleteSpace X₀]
    {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g)
    {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) (t : ℝ) :
    C.periodizeStrip δ T F (t * I) = C.fstToSum (periodizeTrace 0 δ T g.1 t) := by
  rw [periodizeTrace,
    C.fstToSum.map_tsum (summable_periodizeTrace_term g.1 ⟨le_rfl, zero_le_one⟩ hδ hT t),
    periodizeStrip]
  congr 1 with k
  rw [ofReal_zero, zero_add,
    show (t : ℂ) * I + k * T * I = ((t + k * T : ℝ) : ℂ) * I by push_cast; ring,
    hF.apply_mul_I, map_smul]

private theorem periodizeStrip_one_add_mul_I [CompleteSpace X₁]
    {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g)
    {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) (t : ℝ) :
    C.periodizeStrip δ T F (1 + t * I) = C.sndToSum (periodizeTrace 1 δ T g.2 t) := by
  rw [periodizeTrace,
    C.sndToSum.map_tsum (summable_periodizeTrace_term g.2 ⟨zero_le_one, le_rfl⟩ hδ hT t),
    periodizeStrip]
  congr 1 with k
  rw [ofReal_one,
    show (1 : ℂ) + t * I + k * T * I = 1 + ((t + k * T : ℝ) : ℂ) * I by push_cast; ring,
    hF.apply_one_add_mul_I, map_smul]

private theorem intervalIntegrable_fourier_smul_lift {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {T : ℝ} {p : ℝ → E} (hp_cont : Continuous p) (hp_per : Function.Periodic p T)
    (m : ℤ) : IntervalIntegrable (fun y : ℝ => @fourier T (-m) y • hp_per.lift y) volume 0 T := by
  have hl : Continuous hp_per.lift := continuous_coinduced_dom.2 hp_cont
  exact (((@fourier T (-m)).continuous.comp continuous_quotient_mk').smul
    (hl.comp continuous_quotient_mk')).intervalIntegrable 0 T

private theorem fourierCoeff_periodic_mem_inter [CompleteSpace X₀] [CompleteSpace X₁]
    {T : ℝ} [Fact (0 < T)] {P : ℂ → C.SumSpace} (hP : DiffContOnCl ℂ P (verticalStrip 0 1))
    (hper : ∀ z : ℂ, P (z + T * I) = P z) {p₀ : ℝ → X₀} {p₁ : ℝ → X₁}
    (hp₀_cont : Continuous p₀) (hp₁_cont : Continuous p₁)
    (hp₀_per : Function.Periodic p₀ T) (hp₁_per : Function.Periodic p₁ T)
    (hP₀ : ∀ t : ℝ, P (t * I) = C.fstToSum (p₀ t))
    (hP₁ : ∀ t : ℝ, P (1 + t * I) = C.sndToSum (p₁ t)) (m : ℤ) :
    (fourierCoeff hp₀_per.lift m,
      exp (-(2 * Real.pi * m / T : ℂ)) • fourierCoeff hp₁_per.lift m) ∈ C.inter := by
  rw [C.mem_inter_iff, ← C.sumSpaceEmbed_fstToSum, ← C.sumSpaceEmbed_sndToSum]; congr 1
  rw [fourierCoeff_eq_intervalIntegral _ m 0, fourierCoeff_eq_intervalIntegral _ m 0, zero_add,
    C.fstToSum.map_smul_of_tower, map_smul, C.sndToSum.map_smul_of_tower,
    smul_comm (exp _) (1 / T : ℝ)]; congr 1
  rw [← C.fstToSum.intervalIntegral_comp_comm
      (intervalIntegrable_fourier_smul_lift hp₀_cont hp₀_per m),
    ← C.sndToSum.intervalIntegral_comp_comm
      (intervalIntegrable_fourier_smul_lift hp₁_cont hp₁_per m),
    ← intervalIntegral.integral_smul]
  refine (intervalIntegral.integral_congr fun y _ => ?_).trans
    ((hP.intervalIntegral_exp_smul_add_mul_I_eq zero_le_one T (fun _ _ => hper _) m).trans
      (intervalIntegral.integral_congr fun y _ => ?_))
  · rw [ofReal_zero, zero_add, Function.Periodic.lift_coe, map_smul, ← hP₀ y, fourier_coe_apply]
    congr 2; push_cast; ring
  · rw [ofReal_one, Function.Periodic.lift_coe, map_smul, ← hP₁ y, smul_smul, fourier_coe_apply,
      ← Complex.exp_add]; congr 2; push_cast; ring

private theorem exists_elementary_of_mem_span_fourier {T δ : ℝ} [hT : Fact (0 < T)] (hδ : 0 < δ)
    {f₀ : AddCircle T → X₀} {f₁ : AddCircle T → X₁} (hf₀ : Continuous f₀) (hf₁ : Continuous f₁)
    (hmem : ∀ m : ℤ,
      (fourierCoeff f₀ m, exp (-(2 * Real.pi * m / T : ℂ)) • fourierCoeff f₁ m) ∈ C.inter)
    {Q : C(AddCircle T, ℂ)} (hQ : Q ∈ Submodule.span ℂ (Set.range (@fourier T))) :
    ∃ h ∈ C.elementaryStripTraces,
      (∀ t : ℝ, (h : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t = exp ((δ : ℂ) * (t * I) ^ 2) •
          ∫ u, Q u • f₀ ((t : AddCircle T) - u) ∂haarAddCircle) ∧
      (∀ t : ℝ, (h : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t = exp ((δ : ℂ) * (1 + t * I) ^ 2) •
          ∫ u, Q u • f₁ ((t : AddCircle T) - u) ∂haarAddCircle) := by
  have hT0 : (T : ℂ) ≠ 0 := ofReal_ne_zero.2 hT.out.ne'
  refine Submodule.span_induction ?_
    ⟨0, C.elementaryStripTraces.zero_mem, fun _ => by simp, fun _ => by simp⟩ ?_ ?_ hQ
  · rintro _ ⟨m, rfl⟩
    let xm : C.inter :=
      ⟨(fourierCoeff f₀ m, exp (-(2 * Real.pi * m / T : ℂ)) • fourierCoeff f₁ m), hmem m⟩
    refine ⟨C.expGaussianTrace hδ (2 * Real.pi * m / T) xm,
      C.expGaussianTrace_mem_elementaryStripTraces hδ _ xm, fun t => ?_, fun t => ?_⟩
    · rw [expGaussianTrace_apply_fst, C.interFst_apply, integral_fourier_smul_sub_eq,
        fourier_coe_apply, smul_smul, ← Complex.exp_add]; dsimp [xm]; congr 2; push_cast; ring
    · rw [expGaussianTrace_apply_snd, C.interSnd_apply, integral_fourier_smul_sub_eq,
        fourier_coe_apply]
      dsimp [xm]; rw [smul_smul, smul_smul, ← Complex.exp_add, ← Complex.exp_add]
      congr 2; push_cast; field_simp; ring
  · rintro Q₁ Q₂ - - ⟨h₁, hh₁, h₁₀, h₁₁⟩ ⟨h₂, hh₂, h₂₀, h₂₁⟩
    refine ⟨h₁ + h₂, C.elementaryStripTraces.add_mem hh₁ hh₂, fun t => ?_, fun t => ?_⟩
    · simp only [Submodule.coe_add, Prod.fst_add, FunLike.coe_add, Pi.add_apply]
      rw [h₁₀ t, h₂₀ t, ← smul_add,
        ← integral_add (Q₁.integrable_smul_sub_haarAddCircle hf₀ t)
          (Q₂.integrable_smul_sub_haarAddCircle hf₀ t)]
      simp_rw [ContinuousMap.add_apply, add_smul]
    · simp only [Submodule.coe_add, Prod.snd_add, FunLike.coe_add, Pi.add_apply]
      rw [h₁₁ t, h₂₁ t, ← smul_add,
        ← integral_add (Q₁.integrable_smul_sub_haarAddCircle hf₁ t)
          (Q₂.integrable_smul_sub_haarAddCircle hf₁ t)]
      simp_rw [ContinuousMap.add_apply, add_smul]
  · rintro c Q₁ - ⟨h₁, hh₁, h₁₀, h₁₁⟩
    refine ⟨c • h₁, C.elementaryStripTraces.smul_mem c hh₁, fun t => ?_, fun t => ?_⟩
    · simp only [SetLike.val_smul, Prod.smul_fst, FunLike.coe_smul, Pi.smul_apply]
      rw [h₁₀ t, smul_comm c]; simp_rw [ContinuousMap.smul_apply, smul_assoc, integral_smul]
    · simp only [SetLike.val_smul, Prod.smul_snd, FunLike.coe_smul, Pi.smul_apply]
      rw [h₁₁ t, smul_comm c]; simp_rw [ContinuousMap.smul_apply, smul_assoc, integral_smul]

private theorem exists_period_tail_lt {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (M : ℝ) :
    ∃ T > 0, let r := Real.exp (-(δ * T ^ 2 / 2))
      Real.exp (2 * δ) * M * (2 * (r * (1 - r)⁻¹)) < ε := by
  have hr : Tendsto (fun T : ℝ => Real.exp (-(δ * T ^ 2 / 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp <| (tendsto_neg_atTop_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop (half_pos hδ))).congr fun _ => by
        dsimp; ring
  have hlim : Tendsto (fun T : ℝ => Real.exp (2 * δ) * M *
      (2 * (Real.exp (-(δ * T ^ 2 / 2)) * (1 - Real.exp (-(δ * T ^ 2 / 2)))⁻¹))) atTop (𝓝 0) := by
    simpa using (((hr.mul ((tendsto_const_nhds.sub hr).inv₀ (by norm_num))).const_mul 2).const_mul
      (Real.exp (2 * δ) * M))
  exact ((eventually_gt_atTop (0 : ℝ)).and (hlim.eventually (gt_mem_nhds hε))).exists

private theorem norm_damped_periodizeTrace_sub_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {a δ T M η : ℝ} (ha : a ∈ Icc 0 1) (hδ : 0 < δ) (hT : 0 < T)
    (f : C₀(ℝ, E)) (hfM : ‖f‖ ≤ M)
    (hsum : Summable fun k : ℤ => exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) • f (t + k * T))
    (htail : Real.exp (2 * δ) * M *
      (2 * (Real.exp (-(δ * T ^ 2 / 2)) * (1 - Real.exp (-(δ * T ^ 2 / 2)))⁻¹)) < η) :
    ‖exp ((δ : ℂ) * (a + t * I) ^ 2) • periodizeTrace a δ T f t -
        exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) • f t‖ ≤ η := by
  set r := Real.exp (-(δ * T ^ 2 / 2))
  have hr₀ : 0 ≤ r := (Real.exp_pos _).le
  have hr₁ : r < 1 := Real.exp_lt_one_iff.2 (neg_lt_zero.2 (by positivity))
  have : 0 ≤ M := (norm_nonneg f).trans hfM
  let hcL : E →L[ℂ] E := ContinuousLinearMap.lsmul ℂ ℂ (exp ((δ : ℂ) * (a + t * I) ^ 2))
  have hsmul_sum : Summable fun k : ℤ => exp ((δ : ℂ) * (a + t * I) ^ 2) •
      (exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) • f (t + k * T)) := by
    simpa only [Function.comp_def, hcL, ContinuousLinearMap.lsmul_apply] using hsum.mapL hcL
  have hk0 : exp ((δ : ℂ) * (a + t * I) ^ 2) •
      (exp ((δ : ℂ) * (a + (t + (0 : ℤ) * T : ℝ) * I) ^ 2) • f (t + (0 : ℤ) * T)) =
      exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) • f t := by
    simp [smul_smul, ← Complex.exp_add, two_mul, add_mul]
  rw [show exp ((δ : ℂ) * (a + t * I) ^ 2) • periodizeTrace a δ T f t = _ from
      by simpa only [periodizeTrace, hcL, ContinuousLinearMap.lsmul_apply] using hcL.map_tsum hsum,
    hsmul_sum.tsum_eq_add_tsum_ite 0, hk0, add_sub_cancel_left]
  have hite_bound (k : ℤ) : ‖if k = 0 then (0 : E) else exp ((δ : ℂ) * (a + t * I) ^ 2) •
      (exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) • f (t + k * T))‖ ≤
      Real.exp (2 * δ) * M * (if k = 0 then 0 else r ^ k.natAbs) := by
    split_ifs
    · simp
    · exact (norm_double_damped_shift_le f ha hδ k t).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfM (by positivity)) (by positivity))
  have hsum_ite : Summable fun k : ℤ =>
      Real.exp (2 * δ) * M * (if k = 0 then (0 : ℝ) else r ^ k.natAbs) :=
    (Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity)
      (fun _ => by split_ifs <;> [positivity; exact le_rfl])
      (summable_pow_natAbs hr₀ hr₁)).mul_left _
  have hsum_norm := hsum_ite.of_nonneg_of_le (fun _ => norm_nonneg _) hite_bound
  refine (norm_tsum_le_tsum_norm hsum_norm).trans
    ((Summable.tsum_le_tsum hite_bound hsum_norm hsum_ite).trans ?_)
  rw [tsum_mul_left, tsum_ite_eq_zero_pow_natAbs hr₀ hr₁]
  exact htail.le

private theorem norm_damped_conv_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {T : ℝ} [hT : Fact (0 < T)] {a δ M ε : ℝ} (ha : a ∈ Icc 0 1) (hδ : 0 < δ)
    (f : C₀(ℝ, E)) (hfM : ‖f‖ ≤ M)
    (hsum : ∀ t : ℝ, Summable fun k : ℤ =>
      exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) • f (t + k * T))
    (Q : C(AddCircle T, ℂ)) (hQ : ∀ x : AddCircle T,
      ‖(∫ u, Q u • (periodic_periodizeTrace a δ T f).lift (x - u) ∂haarAddCircle) -
        (periodic_periodizeTrace a δ T f).lift x‖ < (ε / 3) / Real.exp δ)
    (htail : Real.exp (2 * δ) * M *
      (2 * (Real.exp (-(δ * T ^ 2 / 2)) * (1 - Real.exp (-(δ * T ^ 2 / 2)))⁻¹)) < ε / 3)
    {t : ℝ} (hdamp : ‖exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) • f t - f t‖ ≤ ε / 4) :
    ‖exp ((δ : ℂ) * (a + t * I) ^ 2) •
        (∫ u, Q u • (periodic_periodizeTrace a δ T f).lift ((t : AddCircle T) - u) ∂haarAddCircle) -
      f t‖ ≤ ε / 3 + ε / 3 + ε / 4 := by
  let d : E := exp ((δ : ℂ) * (a + t * I) ^ 2) • periodizeTrace a δ T f t
  let m : E := exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) • f t
  have hconv_err : ‖exp ((δ : ℂ) * (a + t * I) ^ 2) •
      (∫ u, Q u • (periodic_periodizeTrace a δ T f).lift ((t : AddCircle T) - u) ∂haarAddCircle) -
      d‖ ≤ ε / 3 := by
    dsimp [d]
    rw [← (periodic_periodizeTrace a δ T f).lift_coe, ← smul_sub, norm_smul, Complex.norm_exp]
    have hexp_le : Real.exp (((δ : ℂ) * (a + t * I) ^ 2).re) ≤ Real.exp δ := by
      refine Real.exp_le_exp.2 ?_
      rw [show ((δ : ℂ) * (a + t * I) ^ 2).re = δ * (a ^ 2 - t ^ 2) by simp [sq]]
      have : a ^ 2 ≤ 1 := by nlinarith [ha.1, ha.2]
      nlinarith [sq_nonneg t]
    exact (mul_le_mul hexp_le (hQ t).le (norm_nonneg _) (Real.exp_pos δ).le).trans_eq
      (mul_div_cancel₀ _ (Real.exp_pos δ).ne')
  have htail_err : ‖d - m‖ ≤ ε / 3 :=
    norm_damped_periodizeTrace_sub_le ha hδ hT.out f hfM (hsum t) htail
  linarith [norm_sub_le_norm_sub_add_norm_sub (exp ((δ : ℂ) * (a + t * I) ^ 2) •
    (∫ u, Q u • (periodic_periodizeTrace a δ T f).lift ((t : AddCircle T) - u) ∂haarAddCircle))
    d (f t), norm_sub_le_norm_sub_add_norm_sub d m (f t)]

private theorem norm_integral_smul_sub_comp_lt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {T : ℝ} [Fact (0 < T)] (L : E →L[ℂ] F) (hL : ∀ e, ‖L e‖ ≤ ‖e‖) {f : AddCircle T → E}
    (hf : Continuous f)
    {Q : C(AddCircle T, ℂ)} {η : ℝ}
    (hQ : ∀ x : AddCircle T, ‖(∫ u, Q u • f (x - u) ∂haarAddCircle) - f x‖ < η)
    (x : AddCircle T) :
    ‖(∫ u, Q u • L (f (x - u)) ∂haarAddCircle) - L (f x)‖ < η := by
  have hcomm : (∫ u, Q u • L (f (x - u)) ∂haarAddCircle) =
      L (∫ u, Q u • f (x - u) ∂haarAddCircle) := by
    simpa [Function.comp_def] using
      L.integral_comp_comm (Q.integrable_smul_sub_haarAddCircle hf x)
  rw [hcomm, ← map_sub]
  exact (hL _).trans_lt (hQ x)

/-- **Calderón's density lemma (Bergh–Löfström, Lemma 4.2.3).** When `X₀` and `X₁` are Banach
spaces, `C.elementaryStripTraces` is dense in `C.stripTraces`. -/
theorem dense_elementaryStripTraces [CompleteSpace X₀] [CompleteSpace X₁] :
    Dense (C.elementaryStripTraces : Set C.stripTraces) := by
  refine Metric.dense_iff.2 fun g ε hε => ?_
  set g₀ : C₀(ℝ, X₀) := (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1
  set g₁ : C₀(ℝ, X₁) := (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2
  -- Step 1: choose Gaussian damping `δ > 0` and period `T > 0` with small tail error.
  obtain ⟨δ₀, hδ₀, hdamp₀⟩ := exists_gaussian_smul_approx_single 0 g₀ (by positivity : 0 < ε / 4)
  obtain ⟨δ₁, hδ₁, hdamp₁⟩ := exists_gaussian_smul_approx_single 1 g₁ (by positivity : 0 < ε / 4)
  set δ := min δ₀ δ₁ / 2
  have hδ : 0 < δ := half_pos (lt_min hδ₀ hδ₁)
  obtain ⟨T, hTpos, htail⟩ := exists_period_tail_lt hδ (by positivity : 0 < ε / 3) ‖g‖
  have : Fact (0 < T) := ⟨hTpos⟩
  -- Step 2: periodize the damped strip function and approximate its boundary traces by a
  -- scalar trigonometric polynomial `Q` on `AddCircle T`.
  have hp₀_cont := continuous_periodizeTrace g₀ ⟨le_rfl, zero_le_one⟩ hδ hTpos
  have hp₁_cont := continuous_periodizeTrace g₁ ⟨zero_le_one, le_rfl⟩ hδ hTpos
  have hf₀ : Continuous (periodic_periodizeTrace 0 δ T g₀).lift :=
    continuous_coinduced_dom.2 hp₀_cont
  have hf₁ : Continuous (periodic_periodizeTrace 1 δ T g₁).lift :=
    continuous_coinduced_dom.2 hp₁_cont
  obtain ⟨Q, hQspan, hQ⟩ := (hf₀.prodMk hf₁).exists_mem_span_fourier_integral_smul_sub_lt
    (div_pos (by positivity : 0 < ε / 3) (Real.exp_pos δ))
  have hQ₀ := norm_integral_smul_sub_comp_lt (.fst ℂ X₀ X₁) norm_fst_le (hf₀.prodMk hf₁) hQ
  have hQ₁ := norm_integral_smul_sub_comp_lt (.snd ℂ X₀ X₁) norm_snd_le (hf₀.prodMk hf₁) hQ
  -- Step 3: realize the damped trigonometric convolution inside `elementaryStripTraces` and
  -- combine the convolution, periodization-tail, and damping bounds.
  have hStrip := C.isStripFunction_stripFunction g
  obtain ⟨h, hhmem, hh₀, hh₁⟩ := exists_elementary_of_mem_span_fourier C hδ hf₀ hf₁
    (fourierCoeff_periodic_mem_inter C (diffContOnCl_periodizeStrip C hStrip hδ hTpos)
      (periodizeStrip_add_mul_I C δ T _) hp₀_cont hp₁_cont
      (periodic_periodizeTrace 0 δ T g₀) (periodic_periodizeTrace 1 δ T g₁)
      (periodizeStrip_mul_I C hStrip hδ hTpos) (periodizeStrip_one_add_mul_I C hStrip hδ hTpos))
    hQspan
  refine ⟨h, ?_, hhmem⟩
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev, ← Submodule.norm_coe, Submodule.coe_sub]
  refine lt_of_le_of_lt (norm_prod_le_iff.2 ⟨?_, ?_⟩) (by linarith : ε / 3 + ε / 3 + ε / 4 < ε)
  · refine (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_
    simp only [Prod.fst_sub, FunLike.coe_sub, Pi.sub_apply]; rw [norm_sub_rev, hh₀ t]
    simpa [zero_add, Submodule.norm_coe] using norm_damped_conv_sub_le ⟨le_rfl, zero_le_one⟩ hδ g₀
      ((norm_fst_le (g : C₀(ℝ, X₀) × C₀(ℝ, X₁))).trans_eq (Submodule.norm_coe g))
      (summable_periodizeTrace_term g₀ ⟨le_rfl, zero_le_one⟩ hδ hTpos) Q hQ₀ htail
      (hdamp₀ hδ ((half_lt_self (lt_min hδ₀ hδ₁)).trans_le (min_le_left _ _)) t)
  · refine (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_
    simp only [Prod.snd_sub, FunLike.coe_sub, Pi.sub_apply]; rw [norm_sub_rev, hh₁ t]
    simpa [Submodule.norm_coe] using norm_damped_conv_sub_le ⟨zero_le_one, le_rfl⟩ hδ g₁
      ((norm_snd_le (g : C₀(ℝ, X₀) × C₀(ℝ, X₁))).trans_eq (Submodule.norm_coe g))
      (summable_periodizeTrace_term g₁ ⟨zero_le_one, le_rfl⟩ hδ hTpos) Q hQ₁ htail
      (hdamp₁ hδ ((half_lt_self (lt_min hδ₀ hδ₁)).trans_le (min_le_right _ _)) t)

end ElementaryTraces

namespace ComplexMethodSpace

variable {C}

/-- **Density of the intersection (Bergh–Löfström, Theorem 4.2.2 (a)).** When `X₀` and `X₁` are
Banach spaces, `X₀ ∩ X₁` is dense in `[X₀, X₁]_θ` for every `θ : ℝ`. -/
theorem denseRange_ofInter [CompleteSpace X₀] [CompleteSpace X₁] (θ : ℝ) :
    DenseRange (ofInter (C := C) θ) := by
  have hle := C.elementaryStripTraces_le
    (S := (LinearMap.range (ofInter (C := C) θ).toLinearMap).comap (mk (C := C) θ).toLinearMap)
    fun {δ} hδ ω x => by
      rw [Submodule.mem_comap, LinearMap.mem_range]
      exact ⟨exp ((δ : ℂ) * (θ : ℂ) ^ 2 + (ω : ℂ) * (θ : ℂ)) • x,
        by simp [ContinuousLinearMap.coe_coe]⟩
  refine (mk_surjective.denseRange.dense_image (mk (C := C) θ).continuous
    C.dense_elementaryStripTraces).mono ?_
  rintro _ ⟨g, hg, rfl⟩
  exact Set.mem_range.2 (by
    simpa only [Submodule.mem_comap, LinearMap.mem_range, ContinuousLinearMap.coe_coe] using hle hg)

end ComplexMethodSpace

end TauCeti.CompatibleCouple
