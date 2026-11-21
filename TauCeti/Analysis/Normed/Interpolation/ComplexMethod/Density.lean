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
import TauCeti.Analysis.SpecialFunctions.Gaussian.Basic
import TauCeti.Topology.Algebra.InfiniteSum.Real

/-!
# Bounded boundary traces and Calderón's density lemma in the complex method

This file proves Bergh–Löfström §4.2 (Lemmas 4.2.1 and 4.2.3, Theorem 4.2.2 (a)) for `[X₀, X₁]_θ`:
* **Bounded-boundary formulation:** relaxing `C₀(ℝ, X_j)` boundary decay to `ℝ →ᵇ X_j`
  (`CompatibleCouple.IsBoundedStripFunction`) leaves `[X₀, X₁]_θ` and its quotient norm unchanged.
* **Calderón's density lemma:** for a Banach couple `(X₀, X₁)`, `elementaryStripTraces` (the span
  of `z ↦ exp (δ z² + ω z) x`, `δ > 0`, `ω : ℝ`, `x ∈ X₀ ∩ X₁`) is dense in `stripTraces`, so
  `X₀ ∩ X₁` is dense in `[X₀, X₁]_θ`, feeding endpoint identifications and regularization.
* **Maps from elementary traces:** a continuous linear map `L` of the ambient spaces restricts to
  a map `[X₀, X₁]_θ → [Y₀, Y₁]_θ` of norm at most `K` as soon as every elementary admissible
  function `G` is matched by a bounded-boundary strip function with value `L (G θ)` at `θ` and
  traces of norm at most `K ‖G‖`
  (`TauCeti.CompatibleCouple.ComplexMethodSpace.exists_map_of_forall_elementaryStripTraces`). This
  is Stein's interpolation theorem for analytic families defined on `X₀ ∩ X₁`.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190, §§3–6.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Springer, 1976, §4.2.
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
  obtain ⟨g', hg', -⟩ := hF.exists_isStripFunction_stripGaussian_smul_and_norm_le one_pos θ
  exact ⟨_, g', hg', by simp⟩

/-- **Bergh–Löfström, Lemma 4.2.1.** For `0 ≤ θ ≤ 1`, the quotient norm on `[X₀, X₁]_θ` coincides
with the infimum over bounded-boundary strip functions. -/
theorem norm_lt_iff_exists_isBoundedStripFunction (hθ : θ ∈ Icc 0 1) {u : C.ComplexMethodSpace θ}
    {r : ℝ} : ‖u‖ < r ↔ ∃ F g, C.IsBoundedStripFunction F g ∧ toSum u = F θ ∧ ‖g‖ < r := by
  refine ⟨fun hr => ?_, fun ⟨_, _, hF, hu, hg⟩ =>
    (norm_le_of_isBoundedStripFunction hθ hF hu).trans_lt hg⟩
  obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 hr
  exact ⟨C.stripFunction g, ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1.toBCF,
      (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2.toBCF),
    (C.isStripFunction_stripFunction g).isBoundedStripFunction, by rw [toSum_mk, stripEval_apply],
    by simpa [Prod.norm_def, ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using hg⟩
end ComplexMethodSpace

/-! ### Calderón's density lemma (Bergh–Löfström, Lemma 4.2.3) -/

section ElementaryTraces
/-- The continuous linear map sending `x ∈ X₀ ∩ X₁` to the admissible boundary trace of
`z ↦ exp (δ z² + ω z) x` (`δ > 0`, `ω : ℝ`). -/
def expGaussianTrace {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) : C.inter →L[ℂ] C.stripTraces :=
  exp (-((ω : ℂ) ^ 2 / (4 * δ))) • C.gaussianTrace hδ (-ω / (2 * δ))

@[simp] theorem expGaussianTrace_apply_fst {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter) (t : ℝ) :
    (C.expGaussianTrace hδ ω x : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t =
      exp ((δ : ℂ) * (t * I) ^ 2 + (ω : ℂ) * (t * I)) • C.interFst x := by
  simp [expGaussianTrace, smul_smul, exp_mul_sq_add_mul (ofReal_ne_zero.2 hδ.ne'),
    neg_div, sub_neg_eq_add]
@[simp] theorem expGaussianTrace_apply_snd {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter) (t : ℝ) :
    (C.expGaussianTrace hδ ω x : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t =
      exp ((δ : ℂ) * (1 + t * I) ^ 2 + (ω : ℂ) * (1 + t * I)) • C.interSnd x := by
  simp [expGaussianTrace, smul_smul, exp_mul_sq_add_mul (ofReal_ne_zero.2 hδ.ne'),
    neg_div, sub_neg_eq_add]

/-- Sharp boundary-trace norm bound on `C.expGaussianTrace hδ ω x`. -/
theorem norm_expGaussianTrace_le {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter) :
    ‖C.expGaussianTrace hδ ω x‖ ≤ max ‖C.interFst x‖ (Real.exp (δ + ω) * ‖C.interSnd x‖) := by
  rw [← Submodule.norm_coe]
  refine norm_prod_le_iff.2
    ⟨((ZeroAtInftyContinuousMap.norm_le (norm_nonneg _)).2 fun t => ?_).trans (le_max_left _ _),
      ((ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_).trans (le_max_right _ _)⟩
  · rw [expGaussianTrace_apply_fst, norm_smul, Complex.norm_exp]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (Real.exp_le_one_iff.2 (by simp [sq]; nlinarith [sq_nonneg t]))
  · rw [expGaussianTrace_apply_snd, norm_smul, Complex.norm_exp]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.2 (by simp [sq]; nlinarith [sq_nonneg t])) (norm_nonneg _)
theorem stripEval_expGaussianTrace {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) : C.stripEval z (C.expGaussianTrace hδ ω x) =
      exp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) • C.fstToSum (C.interFst x) := by
  rw [expGaussianTrace, smul_apply, map_smul, C.stripEval_gaussianTrace hδ _ x hz, smul_smul,
    exp_mul_sq_add_mul (ofReal_ne_zero.2 hδ.ne')]
  simp [neg_div, sub_neg_eq_add]
@[simp] theorem ComplexMethodSpace.mk_expGaussianTrace {C : CompatibleCouple ℂ X₀ X₁ V} {δ : ℝ}
    (hδ : 0 < δ) (ω θ : ℝ) (x : C.inter) :
    ComplexMethodSpace.mk θ (C.expGaussianTrace hδ ω x) =
      exp ((δ : ℂ) * (θ : ℂ) ^ 2 + (ω : ℂ) * (θ : ℂ)) • ComplexMethodSpace.ofInter θ x := by
  by_cases hθ : θ ∈ Icc 0 1
  · ext; rw [ComplexMethodSpace.toSum_mk, C.stripEval_expGaussianTrace hδ ω x (by simpa using hθ),
      map_smul, ComplexMethodSpace.toSum_ofInter hθ]
  · simp [ComplexMethodSpace.eq_zero_of_notMem hθ]

/-- The submodule of `C.stripTraces` spanned over `ℂ` by `C.expGaussianTrace hδ ω x`
(`δ > 0`, `ω : ℝ`, `x : C.inter`). -/
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
@[elab_as_elim] theorem elementaryStripTraces_induction
    {p : (g : C.stripTraces) → g ∈ C.elementaryStripTraces → Prop}
    (expGaussian : ∀ {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter),
      p (C.expGaussianTrace hδ ω x) (C.expGaussianTrace_mem_elementaryStripTraces hδ ω x))
    (zero : p 0 C.elementaryStripTraces.zero_mem)
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (C.elementaryStripTraces.add_mem hx hy))
    (smul : ∀ (c : ℂ) x hx, p x hx → p (c • x) (C.elementaryStripTraces.smul_mem c hx))
    {g : C.stripTraces} (hg : g ∈ C.elementaryStripTraces) : p g hg :=
  Submodule.span_induction (by rintro _ ⟨_, hδ, ω, x, rfl⟩; exact expGaussian hδ ω x)
    zero add smul hg

-- Private Calderón-proof constructions: periodized boundary traces, strip, and damped convolution.
private def periodizeTrace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a δ T : ℝ) (f : C₀(ℝ, E)) (t : ℝ) : E :=
  ∑' k : ℤ, exp ((δ : ℂ) * ((a : ℂ) + t * I + k * T * I) ^ 2) • f (t + k * T)
private theorem summable_periodizeTrace_term {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : C₀(ℝ, E)) (a : ℝ) {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 < T) (t : ℝ) :
    Summable fun k : ℤ => exp ((δ : ℂ) * ((a : ℂ) + t * I + k * T * I) ^ 2) • f (t + k * T) :=
  .of_norm_bounded ((summable_pow_natAbs (Real.exp_pos _).le (Real.exp_lt_one_iff.2
    (neg_lt_zero.2 (by positivity : 0 < δ * T ^ 2 / 2)))).mul_left
    (Real.exp (δ * (a ^ 2 + t ^ 2)) * ‖f‖)) fun k => by
    rw [norm_smul, mul_right_comm (Real.exp _) ‖f‖]
    exact mul_le_mul (by simpa using (norm_exp_ofReal_mul_add_intCast_mul_I_sq_le hδ.le T k
      ((a : ℂ) + t * I))) (f.norm_coe_le_norm _) (norm_nonneg _) (by positivity)
private theorem continuous_periodizeTrace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : C₀(ℝ, E)) (a : ℝ) {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 < T) : Continuous (periodizeTrace a δ T f) :=
  continuous_iff_continuousAt.2 fun t₀ => (continuousOn_tsum (s := {t | |t| < |t₀| + 1})
    (fun _ => by fun_prop) ((summable_pow_natAbs (Real.exp_pos _).le (Real.exp_lt_one_iff.2
      (neg_lt_zero.2 (by positivity : 0 < δ * T ^ 2 / 2)))).mul_left
      (Real.exp (δ * (a ^ 2 + (|t₀| + 1) ^ 2)) * ‖f‖)) fun k t ht => by
      have ht2 : t ^ 2 ≤ (|t₀| + 1) ^ 2 := by rw [← sq_abs t]; gcongr; exact ht.le
      rw [norm_smul, mul_right_comm (Real.exp _) ‖f‖]
      exact mul_le_mul ((norm_exp_ofReal_mul_add_intCast_mul_I_sq_le hδ.le T k
        ((a : ℂ) + t * I)).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2
        (by simp; nlinarith [ht2])) (by positivity))) (f.norm_coe_le_norm _) (norm_nonneg _)
        (by positivity)).continuousAt
    ((isOpen_lt (by fun_prop) continuous_const).mem_nhds (lt_add_one |t₀|))
private theorem periodic_periodizeTrace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a δ T : ℝ) (f : C₀(ℝ, E)) : Function.Periodic (periodizeTrace a δ T f) T := fun t => by
  rw [periodizeTrace, periodizeTrace, ← (Equiv.subRight (1 : ℤ)).tsum_eq]; congr 1 with k
  rw [Equiv.subRight_apply]; congr 1
  · congr 3; push_cast; ring
  · congr 1; push_cast; ring
private def periodizeStrip (δ T : ℝ) (F : ℂ → C.SumSpace) (z : ℂ) : C.SumSpace :=
  ∑' k : ℤ, exp ((δ : ℂ) * (z + k * T * I) ^ 2) • F (z + k * T * I)
private theorem diffContOnCl_periodizeStrip [CompleteSpace X₀] [CompleteSpace X₁]
    {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g)
    {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) :
    DiffContOnCl ℂ (C.periodizeStrip δ T F) (verticalStrip 0 1) := by
  have hsum (B : ℝ) : Summable fun k : ℤ =>
      Real.exp (δ * (1 + B ^ 2)) * ‖g‖ * Real.exp (-(δ * T ^ 2 / 2)) ^ k.natAbs :=
    (summable_pow_natAbs (Real.exp_pos _).le
      (Real.exp_lt_one_iff.2 (neg_lt_zero.2 (by positivity : 0 < δ * T ^ 2 / 2)))).mul_left _
  have hbd (B : ℝ) (k : ℤ) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) (him : |z.im| ≤ B) :
      ‖exp ((δ : ℂ) * (z + k * T * I) ^ 2) • F (z + k * T * I)‖ ≤
        Real.exp (δ * (1 + B ^ 2)) * ‖g‖ * Real.exp (-(δ * T ^ 2 / 2)) ^ k.natAbs := by
    rw [norm_smul, mul_right_comm (Real.exp _) ‖g‖]
    refine mul_le_mul ((norm_exp_ofReal_mul_add_intCast_mul_I_sq_le hδ.le T k z).trans ?_)
      (hF.norm_le (z := z + k * T * I) (by simpa using hz)) (norm_nonneg _) (by positivity)
    have : z.re ^ 2 ≤ 1 := by nlinarith [hz.1, hz.2]
    have : z.im ^ 2 ≤ B ^ 2 := by rw [← sq_abs z.im]; gcongr
    gcongr
  have hopen (B : ℝ) : IsOpen {z : ℂ | |z.im| < B} :=
    isOpen_lt (continuous_abs.comp continuous_im) continuous_const
  have hdiff (k : ℤ) : Differentiable ℂ fun z : ℂ => exp ((δ : ℂ) * (z + k * T * I) ^ 2) := by
    fun_prop
  have hshift (k : ℤ) : Differentiable ℂ fun z : ℂ => z + k * T * I := by fun_prop
  refine ⟨fun z₀ hz₀ => ?_, ?_⟩
  · set B := |z₀.im| + 1; have hU := (isOpen_verticalStrip 0 1).inter (hopen B)
    exact ((differentiableOn_tsum_of_summable_norm (hsum B)
      (fun k => (hdiff k).differentiableOn.fun_smul (hF.diffContOnCl.differentiableOn.comp
        (hshift k).differentiableOn fun _ hz => by simpa using hz.1))
      hU fun k z hz => hbd B k (verticalStrip_subset_verticalClosedStrip 0 1 hz.1)
        hz.2.le).differentiableAt (hU.mem_nhds ⟨hz₀, lt_add_one |z₀.im|⟩)).differentiableWithinAt
  · have hFc := hF.diffContOnCl.continuousOn
    rw [closure_verticalStrip zero_lt_one] at hFc ⊢; intro z₀ hz₀; set B := |z₀.im| + 1
    exact (continuousOn_tsum (s := verticalClosedStrip 0 1 ∩ {z : ℂ | |z.im| < B})
      (fun k => (hdiff k).continuous.continuousOn.fun_smul
        (hFc.comp (hshift k).continuous.continuousOn fun _ hz => by simpa using hz.1))
      (hsum B) (fun k z hz => hbd B k hz.1 hz.2.le) z₀
      ⟨hz₀, lt_add_one |z₀.im|⟩).mono_of_mem_nhdsWithin <|
      inter_mem_nhdsWithin _ ((hopen B).mem_nhds (lt_add_one |z₀.im|))
omit [T1Space V] in
private theorem periodizeStrip_add_mul_I (δ T : ℝ) (F : ℂ → C.SumSpace) (z : ℂ) :
    C.periodizeStrip δ T F (z + T * I) = C.periodizeStrip δ T F z := by
  rw [periodizeStrip, periodizeStrip, ← (Equiv.subRight (1 : ℤ)).tsum_eq]; congr 1 with k
  rw [Equiv.subRight_apply]; congr 1 <;> [congr 3; congr 1] <;> (push_cast; ring)
private theorem periodizeStrip_mul_I [CompleteSpace X₀]
    {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g)
    {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) (t : ℝ) :
    C.periodizeStrip δ T F (t * I) = C.fstToSum (periodizeTrace 0 δ T g.1 t) := by
  rw [periodizeTrace, C.fstToSum.map_tsum (summable_periodizeTrace_term g.1 0 hδ hT t),
    periodizeStrip]
  congr 1 with k; rw [ofReal_zero, zero_add, map_smul, ← hF.apply_mul_I]; congr 2; push_cast; ring
private theorem periodizeStrip_one_add_mul_I [CompleteSpace X₁]
    {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g)
    {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) (t : ℝ) :
    C.periodizeStrip δ T F (1 + t * I) = C.sndToSum (periodizeTrace 1 δ T g.2 t) := by
  rw [periodizeTrace, C.sndToSum.map_tsum (summable_periodizeTrace_term g.2 1 hδ hT t),
    periodizeStrip]
  congr 1 with k; rw [ofReal_one, map_smul, ← hF.apply_one_add_mul_I]; congr 2; push_cast; ring
private theorem fourierCoeff_periodic_mem_inter [CompleteSpace X₀] [CompleteSpace X₁]
    {T : ℝ} [Fact (0 < T)] {P : ℂ → C.SumSpace} (hP : DiffContOnCl ℂ P (verticalStrip 0 1))
    (hper : ∀ z : ℂ, P (z + T * I) = P z) {p₀ : ℝ → X₀} {p₁ : ℝ → X₁}
    (hc₀ : Continuous p₀) (hc₁ : Continuous p₁)
    (h₀ : Function.Periodic p₀ T) (h₁ : Function.Periodic p₁ T)
    (hP₀ : ∀ t : ℝ, P (t * I) = C.fstToSum (p₀ t))
    (hP₁ : ∀ t : ℝ, P (1 + t * I) = C.sndToSum (p₁ t)) (m : ℤ) :
    (fourierCoeff h₀.lift m,
      exp (-(2 * Real.pi * m / T : ℂ)) • fourierCoeff h₁.lift m) ∈ C.inter := by
  rw [C.mem_inter_iff, ← C.sumSpaceEmbed_fstToSum, ← C.sumSpaceEmbed_sndToSum]; congr 1
  rw [fourierCoeff_eq_intervalIntegral _ m 0, fourierCoeff_eq_intervalIntegral _ m 0, zero_add,
    C.fstToSum.map_smul_of_tower, map_smul, C.sndToSum.map_smul_of_tower,
    smul_comm (exp _) (1 / T : ℝ)]; congr 1
  rw [← C.fstToSum.intervalIntegral_comp_comm
      (h₀.intervalIntegrable_fourier_smul_lift hc₀ (-m) 0 T),
    ← C.sndToSum.intervalIntegral_comp_comm
      (h₁.intervalIntegrable_fourier_smul_lift hc₁ (-m) 0 T), ← intervalIntegral.integral_smul]
  refine (intervalIntegral.integral_congr fun y _ => ?_).trans
    ((hP.intervalIntegral_exp_smul_add_mul_I_eq zero_le_one T (fun _ _ => hper _) m).trans
      (intervalIntegral.integral_congr fun y _ => ?_))
  · rw [ofReal_zero, zero_add, Function.Periodic.lift_coe, map_smul, ← hP₀ y, fourier_coe_apply]
    congr 2; push_cast; ring
  · rw [ofReal_one, Function.Periodic.lift_coe, map_smul, ← hP₁ y, smul_smul, fourier_coe_apply,
      ← Complex.exp_add]; congr 2; push_cast; ring
private def dampedConv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {T : ℝ} [Fact (0 < T)]
    (a δ : ℝ) (Q : C(AddCircle T, ℂ)) (f : AddCircle T → E) (t : ℝ) : E :=
  exp ((δ : ℂ) * (a + t * I) ^ 2) • ∫ u, Q u • f ((t : AddCircle T) - u) ∂haarAddCircle
private theorem exists_elementary_of_mem_span_fourier {T δ : ℝ} [hT : Fact (0 < T)] (hδ : 0 < δ)
    {f₀ : AddCircle T → X₀} {f₁ : AddCircle T → X₁} (hf₀ : Continuous f₀) (hf₁ : Continuous f₁)
    (hmem : ∀ m : ℤ,
      (fourierCoeff f₀ m, exp (-(2 * Real.pi * m / T : ℂ)) • fourierCoeff f₁ m) ∈ C.inter)
    {Q : C(AddCircle T, ℂ)} (hQ : Q ∈ Submodule.span ℂ (Set.range (@fourier T))) :
    ∃ h ∈ C.elementaryStripTraces,
      (∀ t, (h : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t = dampedConv 0 δ Q f₀ t) ∧
      (∀ t, (h : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t = dampedConv 1 δ Q f₁ t) := by
  have : (T : ℂ) ≠ 0 := ofReal_ne_zero.2 hT.out.ne'
  refine Submodule.span_induction ?_ ⟨0, C.elementaryStripTraces.zero_mem,
    fun _ => by simp [dampedConv], fun _ => by simp [dampedConv]⟩ ?_ ?_ hQ
  · rintro _ ⟨m, rfl⟩
    let xm : C.inter :=
      ⟨(fourierCoeff f₀ m, exp (-(2 * Real.pi * m / T : ℂ)) • fourierCoeff f₁ m), hmem m⟩
    refine ⟨C.expGaussianTrace hδ (2 * Real.pi * m / T) xm,
      C.expGaussianTrace_mem_elementaryStripTraces hδ _ xm, fun t => ?_, fun t => ?_⟩
    · rw [expGaussianTrace_apply_fst, C.interFst_apply, dampedConv, ofReal_zero, zero_add,
        integral_fourier_smul_sub_eq, fourier_coe_apply, smul_smul, ← Complex.exp_add]
      dsimp [xm]; congr 2; push_cast; ring
    · rw [expGaussianTrace_apply_snd, C.interSnd_apply, dampedConv, ofReal_one,
        integral_fourier_smul_sub_eq, fourier_coe_apply]
      dsimp [xm]; rw [smul_smul, smul_smul, ← Complex.exp_add, ← Complex.exp_add]
      congr 2; push_cast; field_simp; ring
  · rintro Q₁ Q₂ - - ⟨h₁, hh₁, h₁₀, h₁₁⟩ ⟨h₂, hh₂, h₂₀, h₂₁⟩
    exact ⟨h₁ + h₂, C.elementaryStripTraces.add_mem hh₁ hh₂,
      fun t => by simp [h₁₀ t, h₂₀ t, dampedConv, add_smul, ← smul_add, integral_add
        (Q₁.continuous.integrable_smul_sub_haarAddCircle hf₀ t)
        (Q₂.continuous.integrable_smul_sub_haarAddCircle hf₀ t)],
      fun t => by simp [h₁₁ t, h₂₁ t, dampedConv, add_smul, ← smul_add, integral_add
        (Q₁.continuous.integrable_smul_sub_haarAddCircle hf₁ t)
        (Q₂.continuous.integrable_smul_sub_haarAddCircle hf₁ t)]⟩
  · rintro c _ - ⟨h₁, hh₁, h₁₀, h₁₁⟩
    exact ⟨c • h₁, C.elementaryStripTraces.smul_mem c hh₁,
      fun t => by rw [SetLike.val_smul, Prod.smul_fst, FunLike.coe_smul, Pi.smul_apply, h₁₀ t,
        dampedConv, dampedConv, smul_comm]; simp [mul_smul, integral_smul],
      fun t => by rw [SetLike.val_smul, Prod.smul_snd, FunLike.coe_smul, Pi.smul_apply, h₁₁ t,
        dampedConv, dampedConv, smul_comm]; simp [mul_smul, integral_smul]⟩
private theorem norm_damped_periodizeTrace_sub_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {a δ T M η : ℝ} (ha : a ∈ Icc 0 1) (hδ : 0 < δ)
    (hT : 0 < T) (f : C₀(ℝ, E)) (hfM : ‖f‖ ≤ M) (t : ℝ) (htail : Real.exp (2 * δ) * M *
      (∑' k : ℤ, if k = 0 then (0 : ℝ) else Real.exp (-(δ * T ^ 2 / 2)) ^ k.natAbs) < η) :
    ‖exp ((δ : ℂ) * (a + t * I) ^ 2) • periodizeTrace a δ T f t -
        exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) • f t‖ ≤ η := by
  set r := Real.exp (-(δ * T ^ 2 / 2)); let c : ℂ := exp ((δ : ℂ) * (a + t * I) ^ 2)
  have : 0 ≤ M := (norm_nonneg f).trans hfM
  have hsum := summable_periodizeTrace_term f a hδ hT t
  have h0 : c • (exp ((δ : ℂ) * ((a : ℂ) + t * I + (0 : ℤ) * T * I) ^ 2) • f (t + (0 : ℤ) * T)) =
      exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) • f t := by
    simp [c, smul_smul, ← Complex.exp_add, two_mul, add_mul]
  rw [periodizeTrace, ← hsum.tsum_const_smul c, (hsum.const_smul c).tsum_eq_add_tsum_ite 0,
    h0, add_sub_cancel_left]
  have hite (k : ℤ) : ‖if k = 0 then (0 : E) else
      c • (exp ((δ : ℂ) * ((a : ℂ) + t * I + k * T * I) ^ 2) • f (t + k * T))‖ ≤
      Real.exp (2 * δ) * M * (if k = 0 then 0 else r ^ k.natAbs) := by
    split_ifs
    · simp
    · have hc : (a : ℂ) + t * I + k * T * I = ((a : ℂ) + t * I) + ((k * T : ℝ) : ℂ) * I := by
        push_cast; ring
      have he : -(δ * (k * T) ^ 2 / 2) = -(δ * T ^ 2 / 2) * (k : ℝ) ^ 2 := by ring
      have ha2 : a ^ 2 ≤ 1 := by nlinarith [ha.1, ha.2]
      rw [smul_smul, hc, norm_smul, mul_right_comm (Real.exp (2 * δ)) M]
      refine mul_le_mul ((norm_exp_ofReal_mul_sq_mul_add_mul_I_sq_le hδ.le _ _).trans
        (mul_le_mul (Real.exp_le_exp.2 (by simp; nlinarith))
          (he ▸ exp_neg_mul_intCast_sq_le (by positivity) k) (by positivity) (by positivity)))
        ((f.norm_coe_le_norm _).trans hfM) (norm_nonneg _) (by positivity)
  have hsum_ite : Summable fun k : ℤ =>
      Real.exp (2 * δ) * M * (if k = 0 then (0 : ℝ) else r ^ k.natAbs) :=
    ((summable_pow_natAbs (r := r) (by positivity) (Real.exp_lt_one_iff.2
      (neg_lt_zero.2 (by positivity)))).of_nonneg_of_le (fun _ => by split_ifs <;> positivity)
      fun _ => by split_ifs <;> [positivity; exact le_rfl]).mul_left _
  have hsum_norm := hsum_ite.of_nonneg_of_le (fun _ => norm_nonneg _) hite
  exact (norm_tsum_le_tsum_norm hsum_norm).trans
    ((Summable.tsum_le_tsum hite hsum_norm hsum_ite).trans (by rw [tsum_mul_left]; exact htail.le))
private theorem norm_damped_conv_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {T : ℝ} [hT : Fact (0 < T)] {a δ M ε : ℝ} (ha : a ∈ Icc 0 1) (hδ : 0 < δ)
    (f : C₀(ℝ, E)) (hfM : ‖f‖ ≤ M) (Q : C(AddCircle T, ℂ)) (hQ : ∀ x : AddCircle T,
      ‖(∫ u, Q u • (periodic_periodizeTrace a δ T f).lift (x - u) ∂haarAddCircle) -
        (periodic_periodizeTrace a δ T f).lift x‖ < (ε / 3) / Real.exp δ)
    (htail : Real.exp (2 * δ) * M *
      (∑' k : ℤ, if k = 0 then (0 : ℝ) else Real.exp (-(δ * T ^ 2 / 2)) ^ k.natAbs) < ε / 3)
    {t : ℝ} (hdamp : ‖exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) • f t - f t‖ ≤ ε / 4) :
    ‖dampedConv a δ Q (periodic_periodizeTrace a δ T f).lift t - f t‖ ≤ ε / 3 + ε / 3 + ε / 4 := by
  let d : E := exp ((δ : ℂ) * (a + t * I) ^ 2) • periodizeTrace a δ T f t
  have hconv_err : ‖dampedConv a δ Q (periodic_periodizeTrace a δ T f).lift t - d‖ ≤ ε / 3 := by
    dsimp [dampedConv, d]; rw [← (periodic_periodizeTrace a δ T f).lift_coe, ← smul_sub, norm_smul]
    exact (mul_le_mul (by simpa [stripGaussian_apply] using (norm_stripGaussian_le hδ.le 0
      (z := a + t * I) (by simpa using ha))) (hQ t).le (norm_nonneg _) (Real.exp_pos δ).le).trans_eq
      (mul_div_cancel₀ _ (Real.exp_pos δ).ne')
  linarith [norm_damped_periodizeTrace_sub_le ha hδ hT.out f hfM t htail,
    norm_sub_le_norm_sub_add_norm_sub
      (dampedConv a δ Q (periodic_periodizeTrace a δ T f).lift t) d (f t),
    norm_sub_le_norm_sub_add_norm_sub d (exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) • f t) (f t)]

/-- **Calderón's density lemma (Bergh–Löfström, Lemma 4.2.3).** When `X₀` and `X₁` are Banach
spaces, `C.elementaryStripTraces` is dense in `C.stripTraces`. -/
theorem dense_elementaryStripTraces [CompleteSpace X₀] [CompleteSpace X₁] :
    Dense (C.elementaryStripTraces : Set C.stripTraces) := by
  refine Metric.dense_iff.2 fun g ε hε => ?_
  set g₀ := (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1; set g₁ := (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2
  have hbd₀ := Metric.tendstoUniformly_iff.1 (tendstoUniformly_exp_ofReal_mul_add_mul_I_sq_smul
    (f := g₀) 0 (isBounded_iff_forall_norm_le.2 ⟨‖g₀‖, fun _ ⟨t, ht⟩ =>
      ht ▸ g₀.norm_coe_le_norm t⟩) (zero_at_infty g₀)) (ε / 4) (by positivity)
  have hbd₁ := Metric.tendstoUniformly_iff.1 (tendstoUniformly_exp_ofReal_mul_add_mul_I_sq_smul
    (f := g₁) 1 (isBounded_iff_forall_norm_le.2 ⟨‖g₁‖, fun _ ⟨t, ht⟩ =>
      ht ▸ g₁.norm_coe_le_norm t⟩) (zero_at_infty g₁)) (ε / 4) (by positivity)
  obtain ⟨u, ⟨hdamp₀, hdamp₁⟩, hu0⟩ := (((hbd₀.and hbd₁).filter_mono
    (nhdsWithin_mono 0 Ioi_subset_Ici_self)).and self_mem_nhdsWithin).exists
  set δ := u / 2; have hδ : 0 < δ := half_pos hu0
  have h2δ : 2 * δ = u := mul_div_cancel₀ u two_ne_zero
  have hr : Tendsto (fun T : ℝ => Real.exp (-(δ * T ^ 2 / 2))) atTop (𝓝[≥] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((tendsto_exp_sub_mul_sq_cocompact (half_pos hδ) 0).mono_left atTop_le_cocompact).congr
        fun _ => by congr 1; ring) (Eventually.of_forall fun _ => (Real.exp_pos _).le)
  have hlim := (tendsto_tsum_ite_eq_zero_pow_natAbs.comp hr).const_mul (Real.exp (2 * δ) * ‖g‖)
  rw [mul_zero] at hlim
  obtain ⟨T, hTpos, htail⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hlim.eventually (gt_mem_nhds (by positivity : 0 < ε / 3)))).exists
  have : Fact (0 < T) := ⟨hTpos⟩
  have hp₀ := continuous_periodizeTrace g₀ 0 hδ hTpos
  have hp₁ := continuous_periodizeTrace g₁ 1 hδ hTpos
  have hf₀ : Continuous (periodic_periodizeTrace 0 δ T g₀).lift := continuous_coinduced_dom.2 hp₀
  have hf₁ : Continuous (periodic_periodizeTrace 1 δ T g₁).lift := continuous_coinduced_dom.2 hp₁
  obtain ⟨Q, hQspan, hQ⟩ := (hf₀.prodMk hf₁).exists_mem_span_fourier_integral_smul_sub_lt
    (div_pos (by positivity : 0 < ε / 3) (Real.exp_pos δ))
  have hStrip := C.isStripFunction_stripFunction g
  obtain ⟨h, hhmem, hh₀, hh₁⟩ := exists_elementary_of_mem_span_fourier C hδ hf₀ hf₁
    (fourierCoeff_periodic_mem_inter C (diffContOnCl_periodizeStrip C hStrip hδ hTpos)
      (periodizeStrip_add_mul_I C δ T _) hp₀ hp₁
      (periodic_periodizeTrace 0 δ T g₀) (periodic_periodizeTrace 1 δ T g₁)
      (periodizeStrip_mul_I C hStrip hδ hTpos) (periodizeStrip_one_add_mul_I C hStrip hδ hTpos))
    hQspan
  refine ⟨h, ?_, hhmem⟩
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev, ← Submodule.norm_coe, Submodule.coe_sub]
  refine lt_of_le_of_lt (norm_prod_le_iff.2 ⟨?_, ?_⟩) (by linarith : ε / 3 + ε / 3 + ε / 4 < ε)
  · refine (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_
    simp only [Prod.fst_sub, FunLike.coe_sub, Pi.sub_apply]; rw [norm_sub_rev, hh₀ t]
    refine norm_damped_conv_sub_le ⟨le_rfl, zero_le_one⟩ hδ g₀
      ((norm_fst_le (g : C₀(ℝ, X₀) × C₀(ℝ, X₁))).trans_eq (Submodule.norm_coe g)) Q (fun x => ?_)
      htail (by rw [h2δ, norm_sub_rev]; simpa [dist_eq_norm] using (hdamp₀ t).le)
    have hc := (ContinuousLinearMap.fst ℂ X₀ X₁).integral_smul_sub_haarAddCircle_comp
      Q.continuous (hf₀.prodMk hf₁) x
    simp only [ContinuousLinearMap.coe_fst'] at hc
    simpa only [Prod.fst_sub, ← hc] using (norm_fst_le _).trans_lt (hQ x)
  · refine (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_
    simp only [Prod.snd_sub, FunLike.coe_sub, Pi.sub_apply]; rw [norm_sub_rev, hh₁ t]
    refine norm_damped_conv_sub_le ⟨zero_le_one, le_rfl⟩ hδ g₁
      ((norm_snd_le (g : C₀(ℝ, X₀) × C₀(ℝ, X₁))).trans_eq (Submodule.norm_coe g)) Q (fun x => ?_)
      htail (by rw [h2δ, norm_sub_rev]; simpa [dist_eq_norm] using (hdamp₁ t).le)
    have hc := (ContinuousLinearMap.snd ℂ X₀ X₁).integral_smul_sub_haarAddCircle_comp
      Q.continuous (hf₀.prodMk hf₁) x
    simp only [ContinuousLinearMap.coe_snd'] at hc
    simpa only [Prod.snd_sub, ← hc] using (norm_snd_le _).trans_lt (hQ x)

end ElementaryTraces

namespace ComplexMethodSpace
variable {C}

/-- **Density of the intersection (Bergh–Löfström, Theorem 4.2.2 (a)).** When `X₀` and `X₁` are
Banach spaces, `X₀ ∩ X₁` is dense in `[X₀, X₁]_θ` for every `θ : ℝ`. -/
theorem denseRange_ofInter [CompleteSpace X₀] [CompleteSpace X₁] (θ : ℝ) :
    DenseRange (ofInter (C := C) θ) := by
  have hle := C.elementaryStripTraces_le
    (S := (LinearMap.range (ofInter (C := C) θ).toLinearMap).comap (mk (C := C) θ).toLinearMap)
    fun {δ} hδ ω x => ⟨exp ((δ : ℂ) * (θ : ℂ) ^ 2 + (ω : ℂ) * (θ : ℂ)) • x,
      by simp [ContinuousLinearMap.coe_coe]⟩
  refine (mk_surjective.denseRange.dense_image (mk (C := C) θ).continuous
    C.dense_elementaryStripTraces).mono ?_
  rintro _ ⟨g, hg, rfl⟩
  exact Set.mem_range.2 (by simpa [ContinuousLinearMap.coe_coe] using hle hg)

/-! ### Maps of interpolation spaces from elementary traces -/

section ElementaryMap

variable {Y₀ Y₁ W : Type*} [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀] [NormedAddCommGroup Y₁]
  [NormedSpace ℂ Y₁] [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [ContinuousAdd W]
  [T2Space W] {D : CompatibleCouple ℂ Y₀ Y₁ W}

/-- **Maps of complex interpolation spaces defined by elementary traces.** Let `(X₀, X₁)` and
`(Y₀, Y₁)` be Banach couples in Hausdorff ambient spaces `V` and `W`, let `L : V →L[ℂ] W` and
`0 ≤ θ ≤ 1`. Suppose that every elementary admissible function `G` of `(X₀, X₁)`
(`CompatibleCouple.elementaryStripTraces`) is matched by a bounded-boundary strip function `Ψ` of
`(Y₀, Y₁)` with `Ψ θ = L (G θ)` in `W`, whose boundary traces have norm at most `K` times those of
`G`. Then `L` restricts to a map `[X₀, X₁]_θ → [Y₀, Y₁]_θ` of norm at most `K`.

This is the form of Stein's interpolation theorem in which the analytic family `z ↦ T z` is only
applied to functions with values in `X₀ ∩ X₁`: the strip function `Ψ` is typically
`z ↦ T z (G z)`, and Calderón's density lemma (`CompatibleCouple.dense_elementaryStripTraces`)
extends the estimate to all admissible functions. -/
theorem exists_map_of_forall_elementaryStripTraces [CompleteSpace X₀]
    [CompleteSpace X₁] [CompleteSpace Y₀] [CompleteSpace Y₁] {θ : ℝ} (hθ : θ ∈ Icc 0 1)
    (L : V →L[ℂ] W) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ G ∈ C.elementaryStripTraces, ∃ (Ψ : ℂ → D.SumSpace) (g : (ℝ →ᵇ Y₀) × (ℝ →ᵇ Y₁)),
      D.IsBoundedStripFunction Ψ g ∧ D.sumSpaceEmbed (Ψ θ) = L (C.sumSpaceEmbed (C.stripEval θ G)) ∧
        ‖g‖ ≤ K * ‖G‖) :
    ∃ T : C.ComplexMethodSpace θ →L[ℂ] D.ComplexMethodSpace θ, ‖T‖ ≤ K ∧
      ∀ u, D.sumSpaceEmbed (toSum (T u)) = L (C.sumSpaceEmbed (toSum u)) := by
  set S := C.elementaryStripTraces
  -- `J` embeds `[Y₀, Y₁]_θ` injectively into `W`.
  set J : D.ComplexMethodSpace θ →L[ℂ] W := D.sumSpaceEmbed ∘L toSum
  have hJ : Function.Injective J := D.sumSpaceEmbed_injective.comp toSum_injective
  have hex : ∀ G : S, ∃ v : D.ComplexMethodSpace θ,
      J v = L (C.sumSpaceEmbed (C.stripEval θ G)) ∧ ‖v‖ ≤ K * ‖G‖ := by
    rintro ⟨G, hG⟩
    obtain ⟨Ψ, g, hΨ, hΨθ, hg⟩ := h G hG
    obtain ⟨v, hv⟩ := (exists_toSum_eq_iff_isBoundedStripFunction hθ).2 ⟨Ψ, g, hΨ, rfl⟩
    exact ⟨v, by simpa [J, hv] using hΨθ,
      (norm_le_of_isBoundedStripFunction hθ hΨ hv).trans hg⟩
  choose φ hφ hφn using hex
  -- `φ` is linear since `J` is injective; extend it from the dense subspace `S` by continuity.
  have hdense : DenseRange (Subtype.val : S → C.stripTraces) := by
    simpa [DenseRange] using C.dense_elementaryStripTraces
  set Φ := LinearMap.extendOfNorm (𝕜 := ℂ) (σ₁₂ := RingHom.id ℂ) (E := S)
    (Eₗ := C.stripTraces) (F := D.ComplexMethodSpace θ)
    ⟨⟨φ, fun G H ↦ hJ <| by simp [hφ]⟩, fun c G ↦ hJ <| by simp [hφ]⟩
    ⟨⟨Subtype.val, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩
  have hΦ : ∀ G : S, Φ G = φ G := fun G ↦
    LinearMap.extendOfNorm_eq hdense ⟨K, fun G ↦ hφn G⟩ G
  have hΦn : ∀ g, ‖Φ g‖ ≤ K * ‖g‖ :=
    LinearMap.norm_extendOfNorm_apply_le hdense K fun G ↦ hφn G
  have hΦJ : ∀ g, J (Φ g) = L (C.sumSpaceEmbed (C.stripEval θ g)) := fun g ↦
    hdense.induction_on g (isClosed_eq (by fun_prop) (by fun_prop)) fun G ↦ by
      simpa [hΦ] using hφ G
  refine ⟨ComplexMethodSpace.lift Φ fun g hg ↦ hJ (by simp [hΦJ, hg]),
    opNorm_le_of_norm_apply_mk_le hK fun g ↦ by simpa using hΦn g, fun u ↦ ?_⟩
  obtain ⟨g, rfl⟩ := mk_surjective u
  simpa [J] using hΦJ g

end ElementaryMap

end ComplexMethodSpace

end TauCeti.CompatibleCouple
