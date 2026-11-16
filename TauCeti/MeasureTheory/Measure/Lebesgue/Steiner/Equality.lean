/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.BoundedVariation.Coarea
import TauCeti.Analysis.BoundedVariation.Convolution
import TauCeti.Analysis.BoundedVariation.Slicing.Excess
import TauCeti.Analysis.BoundedVariation.Slicing.Measurability
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Convolution.Basic
import TauCeti.Analysis.Distribution.TestFunction.Convolution
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence
import TauCeti.Analysis.SpecialFunctions.Sqrt
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz
import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Perimeter

/-!
# Equality in Steiner's perimeter inequality

Let `s` be a Lebesgue-measurable set of finite volume in a finite-dimensional real inner product
space `E`, and let `e` be a unit vector with orthogonal hyperplane `H = (ℝ ∙ e)ᗮ`. Write
`D = {y ∈ H | 0 < |s_y|}` for the transverse projection of positive-length line sections
`s_y = {t ∈ ℝ | y + t • e ∈ s}`, and `v(y) = |s_y|` for the real section length. For any
null-measurable family `A ⊆ H` of noninterval sections (sections that do not agree almost
everywhere with any interval), the perimeter deficit between `s` and its Steiner symmetral `S s`
controls `|A|²`:

`(2 |D| + |Dv|) P(S s) + 4 |A|² ≤ (2 |D| + |Dv|) P(s)`

(`TauCeti.mul_perimeter_steinerSymmetrization_add_four_mul_sq_le`), and in the coordinate-free
form using `2 |D| + |Dv| ≤ 2 P(s)`,

`P(s) P(S s) + 2 |A|² ≤ P(s)²`

(`TauCeti.perimeter_mul_perimeter_steinerSymmetrization_add_two_mul_sq_le`). Both inequalities hold
for finite or infinite ambient perimeter and in every positive dimension. Consequently, if `s` has
finite perimeter and `P(S s) = P(s)`, then almost every line section of `s` along `e` agrees almost
everywhere with an interval
(`TauCeti.ae_exists_ordConnected_lineSection_of_perimeter_steinerSymmetrization_eq`). Finite
ambient perimeter is necessary for the equality conclusion: a set of infinite perimeter whose
noninterval sections still give a symmetral of infinite perimeter satisfies `P(S s) = P(s)`.

## Strategy

For a shrinking family of radial smooth mollifiers `κ_j` on `H`, put `w_j = κ_j ⋆ v`,
`d_j = κ_j ⋆ (2 · 1_D)`, and `a_j = κ_j ⋆ 1_A`. Testing the localized joint slicing inequality
(`TauCeti.two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter`) against
mollifications of the smoothed gradient vector field `-η (∇w_j) / √(d_j² + ‖∇w_j‖² + δ²)` on `H`,
applying Cauchy–Schwarz to the localized noninterval excess, and letting `η ↑ 1` and `δ → 0⁺`
yields

`M ∫ √(d_j² + ‖∇w_j‖²) + 2 (∫ a_j √d_j)² ≤ M P(s)`,

where `M = 2 |D| + |Dv|`. On the other hand, applying the coarea formula
(`LocallyLipschitzOn.lintegral_perimeter_eq_setLIntegral_enorm_fderiv`) to a clamped defining
function of the truncated symmetric subgraph `{|⟪e, x⟫| < (w_j(y) - ε) / 2}` bounds its perimeter
above by `∫_{w_j > ε} √(4 + ‖∇w_j‖²)`, which compares with `∫ √(d_j² + ‖∇w_j‖²)` up to the `L¹`
error `∫ |2 · 1_{w_j > ε} - d_j|`. Passing first to `j → ∞` for `ε > 0` with `|{v = ε}| = 0` and
then to `ε → 0⁺`, lower semicontinuity of the perimeter concludes.

## References

* F. Cagnetti, M. Colombo, G. De Philippis, F. Maggi, *Rigidity of equality cases in Steiner's
  perimeter inequality*, Anal. PDE **7** (2014), §1.2 and Theorem 1.1.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, Chapter 14.
-/

public section

noncomputable section

open ContinuousLinearMap Filter InnerProductSpace MeasureTheory Metric Set TestFunction
  TopologicalSpace
open scoped Convolution Distributions ENNReal Pointwise RealInnerProductSpace Topology symmDiff

namespace TauCeti

section Helpers

/-- Triangle-inequality comparison `√(a² + c²) ≤ √(b² + c²) + |a - b|` for `b ≥ 0`. -/
private theorem sqrt_sq_add_sq_le_add_abs {a b c : ℝ} (hb : 0 ≤ b) :
    √(a ^ 2 + c ^ 2) ≤ √(b ^ 2 + c ^ 2) + |a - b| := by
  rw [Real.sqrt_le_left (by positivity)]
  have hsq : √(b ^ 2 + c ^ 2) ^ 2 = b ^ 2 + c ^ 2 := Real.sq_sqrt (by positivity)
  have hble : b ≤ √(b ^ 2 + c ^ 2) :=
    Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg c))
  have hcross : b * (a - b) ≤ |a - b| * √(b ^ 2 + c ^ 2) :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hb).trans <|
      (mul_comm b _).le.trans (mul_le_mul_of_nonneg_left hble (abs_nonneg _))
  nlinarith [hsq, (sq_abs (a - b)).symm, hcross]

/-- Pointwise bound `(a² + c²) / √(a² + c² + δ²) ≤ a + c` for `a, c ≥ 0` and `δ > 0`. -/
private theorem div_sqrt_add_sq_le {a c δ : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hδ : 0 < δ) :
    (a ^ 2 + c ^ 2) / √(a ^ 2 + c ^ 2 + δ ^ 2) ≤ a + c := by
  have h1 : (a ^ 2 + c ^ 2) / √(a ^ 2 + c ^ 2 + δ ^ 2) ≤ √(a ^ 2 + c ^ 2) := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 (by positivity))]
    calc a ^ 2 + c ^ 2 = √(a ^ 2 + c ^ 2) * √(a ^ 2 + c ^ 2) :=
          (Real.mul_self_sqrt (by positivity)).symm
      _ ≤ √(a ^ 2 + c ^ 2) * √(a ^ 2 + c ^ 2 + δ ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [sq_nonneg δ]))
            (Real.sqrt_nonneg _)
  exact h1.trans (Real.sqrt_le_left (add_nonneg ha hc) |>.2 (by nlinarith [mul_nonneg ha hc]))

/-- The square root of a nonnegative integrable function belongs to `L²`. -/
private theorem memLp_two_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : Integrable f μ) (h0 : ∀ x, 0 ≤ f x) : MemLp (fun x ↦ √(f x)) 2 μ := by
  rw [memLp_two_iff_integrable_sq
    (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable)]
  exact hf.congr (.of_forall fun x ↦ (Real.sq_sqrt (h0 x)).symm)

/-- Passing a linear `ℝ≥0∞` inequality to the limit along `liminf` lower bounds. -/
private theorem mul_add_le_of_le_liminf {m p c l : ℝ≥0∞} {u v r : ℕ → ℝ≥0∞}
    (hp : p ≤ liminf u atTop) (hc : c ≤ liminf v atTop)
    (hle : ∀ k, m * u k + v k ≤ r k) (hr : Tendsto r atTop (𝓝 l)) : m * p + c ≤ l := by
  calc m * p + c ≤ m * liminf u atTop + c := by gcongr
    _ ≤ liminf (fun k ↦ m * u k) atTop + liminf v atTop := by
        refine add_le_add ?_ hc
        simpa only [liminf_const, Pi.mul_def] using
          ENNReal.le_liminf_mul (u := fun _ : ℕ ↦ m) (v := u) (f := atTop)
    _ ≤ liminf (fun k ↦ m * u k + v k) atTop := ENNReal.le_liminf_add _ _
    _ ≤ liminf r atTop := liminf_le_liminf (.of_forall hle)
    _ = l := hr.liminf_eq

/-- The symmetric difference of centered real `eball`s of lengths `a, b ≥ 0` has Lebesgue measure at
most `|a - b|`. -/
private theorem volume_eball_ofReal_symmDiff_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    volume (Metric.eball (0 : ℝ) (ENNReal.ofReal a / 2) ∆
        Metric.eball (0 : ℝ) (ENNReal.ofReal b / 2)) ≤ ENNReal.ofReal |a - b| := by
  have hvol (r : ℝ) : volume (Metric.eball (0 : ℝ) (ENNReal.ofReal r / 2)) = ENNReal.ofReal r := by
    rw [Real.volume_eball, ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
  have hle {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
      volume (Metric.eball (0 : ℝ) (ENNReal.ofReal x / 2) ∆
          Metric.eball (0 : ℝ) (ENNReal.ofReal y / 2)) ≤ ENNReal.ofReal |x - y| := by
    have hsub : Metric.eball (0 : ℝ) (ENNReal.ofReal x / 2) ⊆
        Metric.eball (0 : ℝ) (ENNReal.ofReal y / 2) :=
      Metric.eball_subset_eball (ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hxy) 2)
    rw [symmDiff_def, Set.sdiff_eq_empty.2 hsub, empty_union,
      measure_sdiff hsub Metric.isOpen_eball.measurableSet.nullMeasurableSet
        (by rw [hvol]; exact ENNReal.ofReal_ne_top),
      hvol, hvol, ← ENNReal.ofReal_sub _ hx, abs_of_nonpos (sub_nonpos.2 hxy), neg_sub]
  rcases le_total a b with hab | hba
  · exact hle ha hab
  · rw [symmDiff_comm, abs_sub_comm]; exact hle hb hba

/-- If `{0 < f}` has finite measure, then `{0 < f ∧ f ≤ 1 / (k + 1)}` has measure tending to `0`. -/
private theorem tendsto_measure_setOf_pos_le_one_div {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : AEMeasurable f μ) (hfin : μ {x | 0 < f x} ≠ ∞) :
    Tendsto (fun k : ℕ ↦ μ {x | 0 < f x ∧ f x ≤ 1 / ((k : ℝ) + 1)}) atTop (𝓝 0) := by
  let G : ℕ → Set α := fun k ↦ {x | 0 < f x ∧ f x ≤ 1 / ((k : ℝ) + 1)}
  have hGm (k : ℕ) : NullMeasurableSet (G k) μ :=
    (nullMeasurableSet_lt aemeasurable_const hf).inter (nullMeasurableSet_le hf aemeasurable_const)
  have hGanti : Antitone G := fun m n hmn _ hx ↦
    ⟨hx.1, hx.2.trans (one_div_le_one_div_of_le (by positivity) (by gcongr))⟩
  have hGfin : μ (G 0) ≠ ∞ := ne_top_of_le_ne_top hfin (measure_mono fun _ (hx : _ ∈ G 0) ↦ hx.1)
  have hGinter : (⋂ k, G k) = ∅ := eq_empty_of_forall_notMem fun x hx ↦ by
    simp only [mem_iInter, mem_ofPred_eq, G] at hx
    exact (hx 0).1.not_ge (ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat fun k ↦ (hx k).2)
  simpa only [Function.comp_def, hGinter, measure_empty] using
    tendsto_measure_iInter_atTop hGm hGanti ⟨0, hGfin⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

/-- Lower semicontinuity of whole-space perimeter along global `L¹` convergence of sets. -/
private theorem perimeter_le_liminf_of_tendsto_symmDiff {s : ℕ → Set H} {t : Set H}
    (hs : ∀ k, NullMeasurableSet (s k) volume) (ht : NullMeasurableSet t volume)
    (hlim : Tendsto (fun k ↦ volume (s k ∆ t)) atTop (𝓝 0)) :
    perimeter volume ⊤ t ≤ liminf (fun k ↦ perimeter volume ⊤ (s k)) atTop :=
  perimeter_le_liminf (.of_forall hs) ht fun _ _ _ ↦
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ zero_le)
      fun _ ↦ measure_mono inter_subset_left

/-- The gradient norm of a radial bump mollification of a `BV ∩ L¹` function is integrable. -/
private theorem integrable_norm_fderiv_normed_convolution (ρ : ContDiffBump (0 : H))
    {v : H → ℝ} (hv : Integrable v volume) (htv : totalVariationOn volume ⊤ v ≠ ∞) :
    Integrable (fun y : H ↦ ‖fderiv ℝ (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] v) y‖) volume := by
  let w : H → ℝ := ρ.normed volume ⋆[lsmul ℝ ℝ, volume] v
  have hw : ContDiff ℝ 1 w := ρ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    (ρ.contDiff_normed (n := 1)) hv.locallyIntegrable
  refine ⟨(hw.continuous_fderiv one_ne_zero).norm.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral,
    show (fun y : H ↦ ‖‖fderiv ℝ w y‖‖ₑ) = fun y : H ↦ ‖fderiv ℝ w y‖ₑ from
      funext fun _ ↦ by rw [Real.eNorm_of_nonneg (opNorm_nonneg _), ofReal_norm],
    show ∫⁻ y : H, ‖fderiv ℝ w y‖ₑ = totalVariationOn volume ⊤ w by
      rw [hw.locallyLipschitz.locallyLipschitzOn.totalVariationOn_eq_setLIntegral_enorm_fderiv,
        Opens.coe_top, Measure.restrict_univ]]
  exact (ρ.totalVariationOn_normed_convolution_le
    (hv.locallyIntegrable.locallyIntegrableOn _) fun _ _ ↦ subset_univ _).trans_lt htv.lt_top

/-- **Self-adjointness of radial bump mollification.** For a normalized bump `ρ` centred at `0`, an
integrable function `f` and an essentially bounded measurable function `h`,
`∫ f * (ρ ⋆ h) = ∫ (ρ ⋆ f) * h`. -/
private theorem integral_mul_normed_convolution_eq_of_bdd (ρ : ContDiffBump (0 : H))
    {f h : H → ℝ} (hf : Integrable f volume) (hh : AEStronglyMeasurable h volume)
    {C : ℝ} (hC : ∀ x, ‖h x‖ ≤ C) :
    ∫ y, f y * (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] h) y =
      ∫ x, (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x * h x := by
  set κ : H → ℝ := ρ.normed volume
  have hprod : Integrable (fun p : H × H ↦ f p.1 * (κ p.2 * h (p.1 - p.2))) (volume.prod volume) :=
    ((hf.mul_prod ρ.integrable_normed).bdd_mul
      (hh.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant volume volume))
      (.of_forall fun p ↦ hC (p.1 - p.2))).congr
      (.of_forall fun p ↦ by dsimp only [Function.comp_apply, κ]; ring)
  have hprod' : Integrable (fun p : H × H ↦ (κ p.1 * f (p.2 - p.1)) * h p.2) (volume.prod volume) :=
    ((by simpa only [lsmul_apply, smul_eq_mul] using
      ρ.integrable_normed.convolution_integrand (lsmul ℝ ℝ) hf :
        Integrable (fun p : H × H ↦ κ p.2 * f (p.1 - p.2)) (volume.prod volume)).swap).mul_bdd
      hh.comp_snd (.of_forall fun p ↦ hC p.2)
  calc ∫ y, f y * (κ ⋆[lsmul ℝ ℝ, volume] h) y
      = ∫ y, ∫ t, f y * (κ t * h (y - t)) := integral_congr_ae (.of_forall fun _ ↦ by
          simp only [convolution_lsmul, smul_eq_mul, ← integral_const_mul])
    _ = ∫ t, ∫ y, f y * (κ t * h (y - t)) := integral_integral_swap hprod
    _ = ∫ t, ∫ x, f (x + t) * (κ t * h x) := integral_congr_ae (.of_forall fun t ↦ by
          dsimp only
          rw [← integral_add_right_eq_self (fun x ↦ f x * (κ t * h (x - t))) t]
          exact integral_congr_ae (.of_forall fun _ ↦ by simp only [add_sub_cancel_right]))
    _ = ∫ t, ∫ x, (κ t * f (x - t)) * h x := by
          rw [← integral_neg_eq_self (fun t ↦ ∫ x, f (x + t) * (κ t * h x))]
          refine integral_congr_ae (.of_forall fun t ↦ integral_congr_ae (.of_forall fun x ↦ ?_))
          dsimp only
          rw [show κ (-t) = κ t from ρ.normed_neg t, ← sub_eq_add_neg]; ring
    _ = ∫ x, ∫ t, (κ t * f (x - t)) * h x := integral_integral_swap hprod'
    _ = ∫ x, (κ ⋆[lsmul ℝ ℝ, volume] f) x * h x := integral_congr_ae (.of_forall fun _ ↦ by
          dsimp only; simp only [convolution_lsmul, smul_eq_mul, ← integral_mul_const])

/-- The divergence of a mollified test vector field is the mollification of its divergence. -/
private theorem divergenceCLM_mollify (φ₀ : 𝓓(⊤, H)) (ρ : ContDiffBump (0 : H))
    (h : closedBall (0 : H) ρ.rOut + tsupport φ₀ ⊆ ((⊤ : Opens H) : Set H)) (x : H) :
    divergenceCLM (TestFunction.mollify φ₀ volume ρ h) x =
      (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] (divergenceCLM φ₀ : H → ℝ)) x := by
  let b := stdOrthonormalBasis ℝ H
  have hφ₀_diff : ContDiff ℝ 1 (φ₀ : H → H) := φ₀.contDiff.of_le (by simp)
  have hκ_loc : LocallyIntegrable (ρ.normed volume) volume := ρ.continuous_normed.locallyIntegrable
  have hcont (i) : Continuous (fun y : H ↦ fderiv ℝ (φ₀ : H → H) y (b i)) :=
    (hφ₀_diff.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hstep (i) :
      ⟪b i, fderiv ℝ (TestFunction.mollify φ₀ volume ρ h : H → H) x (b i)⟫_ℝ =
        (ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
          fun y ↦ ⟪b i, fderiv ℝ (φ₀ : H → H) y (b i)⟫_ℝ) x := by
    rw [TestFunction.coe_mollify,
      φ₀.hasCompactSupport.fderiv_convolution_right_apply (lsmul ℝ ℝ) hκ_loc hφ₀_diff x (b i)]
    have hex := ρ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right (lsmul ℝ ℝ)
      hκ_loc (hcont i) x
    simpa only [innerSL_apply_apply] using ((innerSL ℝ (b i)).convolution_lsmul_comp_comm hex).symm
  have hterm (i) : Integrable (fun t : H ↦
      ρ.normed volume t * ⟪b i, fderiv ℝ (φ₀ : H → H) (x - t) (b i)⟫_ℝ) volume := by
    simpa only [lsmul_apply, smul_eq_mul, Function.comp_apply, innerSL_apply_apply] using
      (ρ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right (lsmul ℝ ℝ) hκ_loc
        ((innerSL ℝ (b i)).continuous.comp (hcont i)) x).integrable
  rw [divergenceCLM_apply, LinearMap.trace_eq_sum_inner _ b]
  simp_rw [ContinuousLinearMap.coe_coe, hstep, convolution_def, lsmul_apply, smul_eq_mul]
  rw [← integral_finsetSum _ fun i _ ↦ hterm i]
  refine integral_congr_ae (.of_forall fun _ ↦ ?_)
  dsimp only
  rw [← Finset.mul_sum, divergenceCLM_apply, LinearMap.trace_eq_sum_inner _ b]
  simp only [ContinuousLinearMap.coe_coe]

/-- If `h : H → ℝ` and `φ₀ : H → H` are continuous and satisfy `h² + ‖φ₀‖² ≤ 1` pointwise, then
their normalized-bump mollifications satisfy `(ρ ⋆ h) y ≤ √(1 - ‖(ρ ⋆ φ₀) y‖²)`. -/
private theorem normed_convolution_le_sqrt_one_sub_sq (ρ : ContDiffBump (0 : H))
    {h : H → ℝ} {φ₀ : H → H} (hh : Continuous h) (hφ₀ : Continuous φ₀)
    (hle : ∀ z, h z ^ 2 + ‖φ₀ z‖ ^ 2 ≤ 1) (y : H) :
    (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] h) y ≤
      √(1 - ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] φ₀) y‖ ^ 2) := by
  let F : H → WithLp 2 (ℝ × H) := fun z ↦ WithLp.toLp 2 (h z, φ₀ z)
  have hF1 (z : H) : ‖F z‖ ≤ 1 := by
    have hsq : ‖F z‖ ^ 2 ≤ 1 ^ 2 := by rw [WithLp.prod_norm_sq_eq_of_L2]; simpa [F] using hle z
    nlinarith [norm_nonneg (F z)]
  have hconv1 : ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] F) y‖ ≤ 1 :=
    ρ.norm_normed_convolution_le hF1 y
  have hex : ConvolutionExistsAt (ρ.normed volume) F y (lsmul ℝ ℝ) volume :=
    ρ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right (lsmul ℝ ℝ)
      ρ.continuous_normed.locallyIntegrable
      ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ H).symm.continuous.comp (hh.prodMk hφ₀)) y
  let E2 := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ H).toContinuousLinearMap
  have h1 : ((ρ.normed volume ⋆[lsmul ℝ ℝ, volume] F) y).fst =
      (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] h) y := by
    simpa [E2, F] using
      (((ContinuousLinearMap.fst ℝ ℝ H).comp E2).convolution_lsmul_comp_comm hex).symm
  have h2 : ((ρ.normed volume ⋆[lsmul ℝ ℝ, volume] F) y).snd =
      (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] φ₀) y := by
    simpa [E2, F] using
      (((ContinuousLinearMap.snd ℝ ℝ H).comp E2).convolution_lsmul_comp_comm hex).symm
  have hnorm := WithLp.prod_norm_sq_eq_of_L2 ((ρ.normed volume ⋆[lsmul ℝ ℝ, volume] F) y)
  rw [h1, h2, Real.norm_eq_abs, sq_abs] at hnorm
  exact Real.le_sqrt_of_sq_le
    (by nlinarith [norm_nonneg ((ρ.normed volume ⋆[lsmul ℝ ℝ, volume] F) y)])

/-- Shrinking normalized-bump mollifications of an integrable function converge in real `L¹`. -/
private theorem tendsto_integral_abs_normed_convolution_sub
    {ρ : ℕ → ContDiffBump (0 : H)} (hρ : Tendsto (fun j ↦ (ρ j).rOut) atTop (𝓝 0))
    {f : H → ℝ} (hf : Integrable f volume) :
    Tendsto (fun j ↦ ∫ y : H, |((ρ j).normed volume ⋆[lsmul ℝ ℝ, volume] f) y - f y|)
      atTop (𝓝 0) := by
  have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_lintegral_enorm_normed_convolution_sub hρ hf)
  rw [ENNReal.toReal_zero] at h1
  refine h1.congr fun j ↦ ?_
  have hdiff : Integrable (fun y : H ↦
      |((ρ j).normed volume ⋆[lsmul ℝ ℝ, volume] f) y - f y|) volume :=
    (((ρ j).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hf).sub hf).abs
  have hof := ofReal_integral_eq_lintegral_ofReal hdiff (.of_forall fun _ ↦ abs_nonneg _)
  simp_rw [← Real.eNorm_eq_ofReal_abs] at hof
  rw [Function.comp_apply, ← hof, ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ abs_nonneg _)]

/-- If functions `w j` converge in `L¹` to an integrable function `v`, and `{v = ε}` for `ε > 0`
is null, then the superlevel sets `{ε < w j}` converge in measure to `{ε < v}`. -/
private theorem tendsto_measure_setOf_lt_symmDiff {v : H → ℝ} (hv : Integrable v volume)
    {w : ℕ → H → ℝ} (hw : ∀ j, AEStronglyMeasurable (w j) volume)
    (hlim : Tendsto (fun j ↦ ∫⁻ y, ‖w j y - v y‖ₑ) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (hlevel : volume {y : H | v y = ε} = 0) :
    Tendsto (fun j ↦ volume ({y : H | ε < w j y} ∆ {y : H | ε < v y})) atTop (𝓝 0) := by
  let B : ℕ → Set H := fun m ↦ {y : H | |v y - ε| ≤ ε / (2 * (m + 2))}
  have hBm (m : ℕ) : NullMeasurableSet (B m) volume :=
    nullMeasurableSet_le (hv.aestronglyMeasurable.sub aestronglyMeasurable_const).norm.aemeasurable
      aemeasurable_const
  have hBanti : Antitone B := fun _ _ hmn _ hy ↦
    le_trans hy (div_le_div_of_nonneg_left hε.le (by positivity) (by gcongr))
  have hBfin : volume (B 0) ≠ ∞ :=
    ne_top_of_le_ne_top (hv.measure_ge_lt_top (half_pos hε)).ne <|
      measure_mono fun y (hy : y ∈ B 0) ↦ by
        have h1 : |v y - ε| ≤ ε / 4 := by
          have : |v y - ε| ≤ ε / (2 * ((0 : ℕ) + 2)) := hy; linarith
        change ε / 2 ≤ v y
        linarith [(abs_le.1 h1).1]
  have hBinter : (⋂ m, B m) = {y : H | v y = ε} := by
    ext y; simp only [mem_iInter, mem_ofPred_eq, B]
    refine ⟨fun h ↦ sub_eq_zero.1 (abs_eq_zero.1 (le_antisymm ?_ (abs_nonneg _))),
      fun hy _ ↦ by rw [hy, sub_self, abs_zero]; positivity⟩
    exact ge_of_tendsto' (tendsto_const_nhds.div_atTop
      ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop zero_lt_two)) h
  have hBlim : Tendsto (fun m ↦ volume (B m)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hBinter, hlevel] using
      tendsto_measure_iInter_atTop hBm hBanti ⟨0, hBfin⟩
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  obtain ⟨m, hm⟩ := ENNReal.tendsto_atTop_zero.1 hBlim (δ / 2) (ENNReal.half_pos hδ.ne')
  set η : ℝ := ε / (2 * ((m : ℝ) + 2))
  have hη : 0 < η := by positivity
  have hmark_lim : Tendsto (fun j ↦ volume {y : H | ENNReal.ofReal η ≤ ‖w j y - v y‖ₑ})
      atTop (𝓝 0) := by
    have hdiv : Tendsto (fun j ↦ (∫⁻ y, ‖w j y - v y‖ₑ) / ENNReal.ofReal η) atTop (𝓝 0) := by
      simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const hlim (b := ENNReal.ofReal η)
        (Or.inr (ENNReal.ofReal_pos.2 hη).ne')
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv (fun _ ↦ zero_le)
      fun j ↦ ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hη).ne')
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact mul_meas_ge_le_lintegral₀ ((hw j).sub hv.aestronglyMeasurable).eNorm (ENNReal.ofReal η)
  obtain ⟨J, hJ⟩ := ENNReal.tendsto_atTop_zero.1 hmark_lim (δ / 2) (ENNReal.half_pos hδ.ne')
  refine ⟨J, fun j hj ↦ ?_⟩
  have hsub : {y : H | ε < w j y} ∆ {y : H | ε < v y} ⊆
      B m ∪ {y : H | ENNReal.ofReal η ≤ ‖w j y - v y‖ₑ} := fun y hy ↦ by
    by_cases hyB : y ∈ B m
    · exact Or.inl hyB
    · refine Or.inr ?_
      have hgt : η < |v y - ε| := lt_of_not_ge hyB
      change ENNReal.ofReal η ≤ ‖w j y - v y‖ₑ
      rw [Real.eNorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      rcases hy with ⟨hwj, hvj⟩ | ⟨hvj, hwj⟩
      · simp only [mem_ofPred_eq, not_lt] at hwj hvj
        rw [abs_of_nonpos (sub_nonpos.2 hvj)] at hgt
        exact (by linarith : η ≤ w j y - v y).trans (le_abs_self _)
      · simp only [mem_ofPred_eq, not_lt] at hvj hwj
        rw [abs_of_pos (sub_pos.2 hvj)] at hgt
        exact (by linarith : η ≤ -(w j y - v y)).trans (neg_le_abs _)
  calc volume ({y : H | ε < w j y} ∆ {y : H | ε < v y})
      ≤ volume (B m) + volume {y : H | ENNReal.ofReal η ≤ ‖w j y - v y‖ₑ} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ δ / 2 + δ / 2 := add_le_add (hm m le_rfl) (hJ j hj)
    _ = δ := ENNReal.add_halves δ

/-- For shrinking mollifiers `ρ j` and finite-measure null-measurable sets `A, D` with `A ⊆ᵐ D`,
the mollifications `a j = ρ j ⋆ 1_A` and `d j = ρ j ⋆ (2 · 1_D)` satisfy
`∫ a j √(d j) → √2 |A|`. -/
private theorem tendsto_integral_mul_sqrt_normed_convolution
    {ρ : ℕ → ContDiffBump (0 : H)} (hρ : Tendsto (fun j ↦ (ρ j).rOut) atTop (𝓝 0))
    {A D : Set H} (hA : NullMeasurableSet A volume) (hD : NullMeasurableSet D volume)
    (hAfin : volume A ≠ ∞) (hDfin : volume D ≠ ∞) (hAD : ∀ᵐ y : H ∂volume, y ∈ A → y ∈ D) :
    Tendsto (fun j ↦ ∫ y : H,
        ((ρ j).normed volume ⋆[lsmul ℝ ℝ, volume] A.indicator (fun _ ↦ (1 : ℝ))) y *
          √(((ρ j).normed volume ⋆[lsmul ℝ ℝ, volume] D.indicator (fun _ ↦ (2 : ℝ))) y))
      atTop (𝓝 (√2 * volume.real A)) := by
  let fA : H → ℝ := A.indicator (fun _ ↦ 1)
  let fD : H → ℝ := D.indicator (fun _ ↦ 2)
  let a : ℕ → H → ℝ := fun j ↦ (ρ j).normed volume ⋆[lsmul ℝ ℝ, volume] fA
  let d : ℕ → H → ℝ := fun j ↦ (ρ j).normed volume ⋆[lsmul ℝ ℝ, volume] fD
  have hA_int : Integrable fA volume := (integrableOn_const hAfin).integrable_indicator₀ hA
  have hD_int : Integrable fD volume := (integrableOn_const hDfin).integrable_indicator₀ hD
  have ha_int (j) : Integrable (a j) volume :=
    (ρ j).integrable_normed.integrable_convolution _ hA_int
  have hd_int (j) : Integrable (d j) volume :=
    (ρ j).integrable_normed.integrable_convolution _ hD_int
  have hd_mem (j : ℕ) (y : H) : d j y ∈ Icc (0 : ℝ) 2 :=
    (ρ j).normed_convolution_mem_Icc hD_int.locallyIntegrable
      (fun z ↦ by by_cases hz : z ∈ D <;> simp [fD, hz]) y
  have htarget : ∫ y : H, fA y * √(fD y) = √2 * volume.real A := by
    rw [integral_congr_ae (hAD.mono fun y hy ↦ by by_cases hyA : y ∈ A <;> simp [fA, fD, hyA, hy] :
        (fun y : H ↦ fA y * √(fD y)) =ᵐ[volume] A.indicator (fun _ ↦ √2)),
      integral_indicator₀ hA, setIntegral_const, smul_eq_mul, mul_comm]
  have hbound : Tendsto (fun j ↦ √2 * (∫ y : H, |a j y - fA y|) +
      √(volume.real A * ∫ y : H, |d j y - fD y|)) atTop (𝓝 0) := by
    have h1 := (tendsto_integral_abs_normed_convolution_sub hρ hA_int).const_mul √2
    have h2 := (Real.continuous_sqrt.tendsto 0).comp
      (by simpa only [mul_zero] using
        (tendsto_integral_abs_normed_convolution_sub hρ hD_int).const_mul (volume.real A))
    simpa only [Function.comp_def, mul_zero, Real.sqrt_zero, add_zero] using h1.add h2
  have hM1 : MemLp fA 2 volume := by
    rw [memLp_two_iff_integrable_sq hA_int.aestronglyMeasurable]
    exact hA_int.congr (.of_forall fun y ↦ by by_cases hy : y ∈ A <;> simp [fA, hy])
  have hint2 : Integrable (fun y : H ↦ fA y * √(fD y)) volume :=
    hA_int.mul_bdd (c := √2)
      (Real.continuous_sqrt.comp_aestronglyMeasurable hD_int.aestronglyMeasurable)
      (.of_forall fun y ↦ by
        rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt (by by_cases hy : y ∈ D <;> simp [fD, hy]))
  rw [← htarget, Metric.tendsto_nhds]
  intro r hr
  filter_upwards [hbound.eventually (gt_mem_nhds hr)] with j hj
  rw [Real.dist_eq]
  have hint1 : Integrable (fun y : H ↦ a j y * √(d j y)) volume :=
    (ha_int j).mul_bdd (c := √2)
      (Real.continuous_sqrt.comp_aestronglyMeasurable (hd_int j).aestronglyMeasurable)
      (.of_forall fun y ↦ by
        rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]; exact Real.sqrt_le_sqrt (hd_mem j y).2)
  have hM2 : MemLp (fun y : H ↦ √|d j y - fD y|) 2 volume :=
    memLp_two_sqrt ((hd_int j).sub hD_int).abs fun _ ↦ abs_nonneg _
  have hcs_sqrt : ∫ y : H, fA y * √|d j y - fD y| ≤
      √(volume.real A * ∫ y : H, |d j y - fD y|) := by
    have hcs := sq_integral_mul_le_integral_sq_mul_integral_sq hM1 hM2
    rw [show ∫ y : H, fA y ^ 2 = volume.real A by
        rw [show (fun y : H ↦ fA y ^ 2) = fA from funext fun y ↦ by by_cases hy : y ∈ A <;>
            simp [fA, hy], integral_indicator₀ hA, setIntegral_const, smul_eq_mul, mul_one],
      show ∫ y : H, √|d j y - fD y| ^ 2 = ∫ y : H, |d j y - fD y| from
        integral_congr_ae (.of_forall fun _ ↦ Real.sq_sqrt (abs_nonneg _))] at hcs
    exact Real.le_sqrt_of_sq_le hcs
  have hterm1 : Integrable (fun y : H ↦ √2 * |a j y - fA y|) volume :=
    ((ha_int j).sub hA_int).abs.const_mul √2
  have hterm2 : Integrable (fun y : H ↦ fA y * √|d j y - fD y|) volume := hM1.integrable_mul hM2
  refine lt_of_le_of_lt ?_ hj
  rw [← integral_sub hint1 hint2]
  calc |∫ y : H, (a j y * √(d j y) - fA y * √(fD y))|
      ≤ ∫ y : H, |a j y * √(d j y) - fA y * √(fD y)| := abs_integral_le_integral_abs
    _ ≤ ∫ y : H, (√2 * |a j y - fA y| + fA y * √|d j y - fD y|) :=
        integral_mono (hint1.sub hint2).abs (hterm1.add hterm2) fun y ↦ by
          rw [show a j y * √(d j y) - fA y * √(fD y) =
              (a j y - fA y) * √(d j y) + fA y * (√(d j y) - √(fD y)) by ring]
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_comm]
            exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hd_mem j y).2) (abs_nonneg _)
          · have hA0 : 0 ≤ fA y := by by_cases hy : y ∈ A <;> simp [fA, hy]
            rw [abs_mul, abs_of_nonneg hA0]
            exact mul_le_mul_of_nonneg_left (Real.abs_sqrt_sub_sqrt_le _ _) hA0
    _ = √2 * (∫ y : H, |a j y - fA y|) + ∫ y : H, fA y * √|d j y - fD y| := by
        rw [integral_add hterm1 hterm2, integral_const_mul]
    _ ≤ _ := add_le_add le_rfl hcs_sqrt

end Helpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Line sections of a truncated symmetric subgraph are centered open intervals (`eball`s). -/
private theorem lineSection_symmetricSubgraph_eq (e : E) (he : ‖e‖ = 1)
    (f : (ℝ ∙ e)ᗮ → ℝ) (ε : ℝ) (y : (ℝ ∙ e)ᗮ) :
    {t : ℝ | (y : E) + t • e ∈
        {x : E | |⟪e, x⟫_ℝ| < (f ((orthogonalLineEquiv e he).symm x).1 - ε) / 2}} =
      Metric.eball (0 : ℝ) (ENNReal.ofReal (max (f y - ε) 0) / 2) := by
  ext t
  have hqyt : ((orthogonalLineEquiv e he).symm ((y : E) + t • e)).1 = y := by
    rw [← orthogonalLineEquiv_apply e he y t, (orthogonalLineEquiv e he).symm_apply_apply]
  simp only [mem_ofPred_eq, inner_add_smul e he, hqyt, Metric.mem_eball, edist_zero_right,
    Real.eNorm_eq_ofReal_abs]
  rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_div_of_pos zero_lt_two]
  rcases le_or_gt (f y - ε) 0 with hle | hgt
  · rw [max_eq_right hle, zero_div, ENNReal.ofReal_zero]
    exact ⟨fun h ↦ by linarith [abs_nonneg t], fun h ↦ absurd h (not_lt_of_ge zero_le)⟩
  · rw [max_eq_left hgt.le, ENNReal.ofReal_lt_ofReal_iff (div_pos hgt zero_lt_two)]

section SymmetricSubgraph

/-- **Perimeter upper bound for a truncated symmetric subgraph.** Let `w : (ℝ ∙ e)ᗮ → ℝ` be `C¹`,
nonnegative and integrable, and let `ε > 0`. The symmetric open subgraph
`S = {x : E | |⟪e, x⟫| < (w y - ε) / 2}` (where `y` is the transverse coordinate of `x`) has
perimeter at most `∫_{w > ε} √(4 + ‖Dw‖²)`. -/
private theorem perimeter_symmetricSubgraph_le (e : E) (he : ‖e‖ = 1)
    {w : (ℝ ∙ e)ᗮ → ℝ} (hw : ContDiff ℝ 1 w) (hw0 : ∀ y, 0 ≤ w y) (hwi : Integrable w volume)
    {ε : ℝ} (hε : 0 < ε) :
    perimeter volume ⊤
        {x : E | |⟪e, x⟫_ℝ| < (w ((orthogonalLineEquiv e he).symm x).1 - ε) / 2} ≤
      ∫⁻ y in {y : (ℝ ∙ e)ᗮ | ε < w y}, ENNReal.ofReal √(4 + ‖fderiv ℝ w y‖ ^ 2) := by
  let H := (ℝ ∙ e)ᗮ
  let q : E →L[ℝ] H :=
    (ContinuousLinearMap.fst ℝ H ℝ).comp (orthogonalLineEquiv e he).symm.toContinuousLinearMap
  have hqyt (y : H) (t : ℝ) : q ((y : E) + t • e) = y := by
    rw [← orthogonalLineEquiv_apply e he y t]
    exact congrArg Prod.fst ((orthogonalLineEquiv e he).symm_apply_apply (y, t))
  let h : E → ℝ := fun x ↦ (w (q x) - ε) / 2 - |⟪e, x⟫_ℝ|
  have hhyt (y : H) (t : ℝ) : h ((y : E) + t • e) = (w y - ε) / 2 - |t| := by
    simp [h, hqyt, inner_add_smul e he]
  have hS_eq : {x : E | |⟪e, x⟫_ℝ| < (w ((orthogonalLineEquiv e he).symm x).1 - ε) / 2} =
      {x : E | 0 < h x} := by ext x; simp [h, q, sub_pos]
  rw [hS_eq]
  have hcont_h : Continuous h :=
    (((hw.continuous.comp q.continuous).sub continuous_const).div_const 2).sub
      (continuous_const.inner continuous_id).abs
  have hlip_h : LocallyLipschitz h := by
    refine ((((hw.comp q.contDiff).sub contDiff_const).div_const 2).locallyLipschitz).sub
      (LipschitzWith.of_dist_le_mul (K := 1) fun x₁ x₂ ↦ ?_).locallyLipschitz
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    calc |(|⟪e, x₁⟫_ℝ| - |⟪e, x₂⟫_ℝ|)| ≤ |⟪e, x₁ - x₂⟫_ℝ| := by
          rw [inner_sub_right]; exact abs_abs_sub_abs_le _ _
      _ ≤ ‖e‖ * ‖x₁ - x₂‖ := abs_real_inner_le_norm e (x₁ - x₂)
      _ = ‖x₁ - x₂‖ := by rw [he, one_mul]
  -- Key coarea estimate on `{0 < h < δ}` for every `δ > 0`.
  have hcoarea {δ : ℝ} (hδ : 0 < δ) :
      ∫⁻ r in Ioo 0 δ, perimeter volume ⊤ {x : E | r < h x} ≤
        ENNReal.ofReal δ *
          ∫⁻ y in {y : H | ε < w y}, ENNReal.ofReal √(4 + ‖fderiv ℝ w y‖ ^ 2) := by
    let u : E → ℝ := fun x ↦ min (max (h x) 0) δ
    have hulip : LocallyLipschitzOn (⊤ : Opens E) u :=
      ((hlip_h.max_const 0).min_const δ).locallyLipschitzOn
    have hsuper : ∀ r ∈ Ioo 0 δ, {x : E | r < u x} = {x : E | r < h x} := fun r hr ↦ by
      ext x; simp only [u, mem_ofPred_eq, lt_min_iff, lt_max_iff]
      exact ⟨fun ⟨h1, _⟩ ↦ h1.resolve_right (not_lt.2 hr.1.le), fun hx ↦ ⟨Or.inl hx, hr.2⟩⟩
    let Z : Set E := {x : E | h x = 0 ∨ h x = δ ∨ ⟪e, x⟫_ℝ = 0}
    have hZ_closed : IsClosed Z :=
      (isClosed_eq hcont_h continuous_const).union
        ((isClosed_eq hcont_h continuous_const).union
          (isClosed_eq (continuous_const.inner continuous_id) continuous_const))
    have hZ_null : volume Z = 0 := by
      rw [volume_eq_lintegral_volume_lineSection e he hZ_closed.measurableSet.nullMeasurableSet]
      refine (lintegral_eq_zero_iff'
        (aemeasurable_volume_lineSection e he hZ_closed.measurableSet.nullMeasurableSet)).2
        (.of_forall fun y ↦ ?_)
      set R : ℝ := (w y - ε) / 2
      have hsub : {t : ℝ | (y : E) + t • e ∈ Z} ⊆ {0, R, -R, R - δ, -(R - δ)} := fun t ht ↦ by
        simp only [Z, mem_ofPred_eq, hhyt, inner_add_smul e he] at ht
        rcases ht with h1 | h2 | h3
        · have habs : |t| = R := by dsimp only [R]; linarith
          rcases (abs_eq (habs ▸ abs_nonneg t)).1 habs with rfl | rfl <;> simp
        · have habs : |t| = R - δ := by dsimp only [R]; linarith
          rcases (abs_eq (habs ▸ abs_nonneg t)).1 habs with rfl | rfl <;> simp
        · exact Or.inl h3
      exact measure_mono_null hsub (Set.Finite.measure_zero (by simp) volume)
    have hgrad_ae : ∀ᵐ x : E ∂volume,
        ‖fderiv ℝ u x‖ₑ =
          {x : E | 0 < h x ∧ h x < δ}.indicator
            (fun x ↦ ENNReal.ofReal ((1 / 2) * √(4 + ‖fderiv ℝ w (q x)‖ ^ 2))) x := by
      filter_upwards [ae_iff.2 (by simpa using hZ_null : volume {x : E | ¬x ∉ Z} = 0)] with x hxZ
      simp only [Z, mem_ofPred_eq, not_or] at hxZ
      obtain ⟨hx0, hxδ, hxt⟩ := hxZ
      rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · have hev : u =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
          filter_upwards [(isOpen_lt hcont_h continuous_const).mem_nhds hneg] with z hz
          simp [u, max_eq_right (le_of_lt hz), min_eq_left hδ.le]
        rw [hev.fderiv_eq, fderiv_const_apply,
          indicator_of_notMem (fun (hx : 0 < h x ∧ h x < δ) ↦ hneg.not_gt hx.1)]
        exact (eNorm_eq_zero (a := (0 : E →L[ℝ] ℝ))).2 rfl
      · rcases lt_or_gt_of_ne hxδ with hlt | hgt
        · rw [indicator_of_mem (show x ∈ {x : E | 0 < h x ∧ h x < δ} from ⟨hpos, hlt⟩)]
          have hev_u : u =ᶠ[𝓝 x] h := by
            filter_upwards [((isOpen_lt continuous_const hcont_h).inter
                (isOpen_lt hcont_h continuous_const)).mem_nhds ⟨hpos, hlt⟩] with z hz
            simp [u, max_eq_left hz.1.le, min_eq_left hz.2.le]
          rw [hev_u.fderiv_eq]
          have hd1 : HasFDerivAt (fun z : E ↦ (w (q z) - ε) / 2)
              (((1 / 2 : ℝ) • fderiv ℝ w (q x)).comp q) x := by
            simpa [div_eq_inv_mul, smul_eq_mul, ContinuousLinearMap.smul_comp] using
              ((((hw.differentiable one_ne_zero (q x)).hasFDerivAt).comp x
                q.hasFDerivAt).sub_const ε).const_mul (1 / 2 : ℝ)
          let σ : ℝ := if 0 < ⟪e, x⟫_ℝ then -1 else 1
          have hσsq : σ ^ 2 = 1 := by dsimp [σ]; split_ifs <;> norm_num
          have hd2 : HasFDerivAt (fun z : E ↦ -|⟪e, z⟫_ℝ|) (σ • innerSL ℝ e) x := by
            rcases lt_or_gt_of_ne hxt with ht_neg | ht_pos
            · have hev : (fun z : E ↦ -|⟪e, z⟫_ℝ|) =ᶠ[𝓝 x] fun z ↦ ⟪e, z⟫_ℝ := by
                filter_upwards [(isOpen_lt (continuous_const.inner continuous_id)
                  continuous_const).mem_nhds ht_neg] with z hz
                dsimp only [id_eq] at hz; rw [abs_of_neg hz, neg_neg]
              rw [show σ = 1 from ite_eq_right (not_lt.2 ht_neg.le), one_smul]
              exact (innerSL ℝ e).hasFDerivAt.congr_of_eventuallyEq hev
            · have hev : (fun z : E ↦ -|⟪e, z⟫_ℝ|) =ᶠ[𝓝 x] fun z ↦ -⟪e, z⟫_ℝ := by
                filter_upwards [(isOpen_lt continuous_const
                  (continuous_const.inner continuous_id)).mem_nhds ht_pos] with z hz
                dsimp only [id_eq] at hz; rw [abs_of_pos hz]
              rw [show σ = -1 from ite_eq_left ht_pos, neg_one_smul]
              exact (innerSL ℝ e).hasFDerivAt.neg.congr_of_eventuallyEq hev
          have hdh : HasFDerivAt h
              ((((1 / 2 : ℝ) • fderiv ℝ w (q x)).comp q) + σ • innerSL ℝ e) x :=
            (hd1.add hd2).congr_of_eventuallyEq (.of_forall fun _ ↦ (sub_eq_add_neg _ _).symm)
          let v : H := (InnerProductSpace.toDual ℝ H).symm ((1 / 2 : ℝ) • fderiv ℝ w (q x))
          have hv_norm : ‖v‖ = (1 / 2) * ‖fderiv ℝ w (q x)‖ := by
            rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_of_nonneg (by positivity)]
          have hdual : (((1 / 2 : ℝ) • fderiv ℝ w (q x)).comp q) + σ • innerSL ℝ e =
              InnerProductSpace.toDual ℝ E ((v : E) + σ • e) := by
            ext z
            obtain ⟨⟨y_z, t_z⟩, rfl⟩ := (orthogonalLineEquiv e he).surjective z
            have hv_apply : ⟪(v : E), (y_z : E)⟫_ℝ = ((1 / 2 : ℝ) • fderiv ℝ w (q x)) y_z := by
              simpa [v] using InnerProductSpace.toDual_symm_apply
                (y := (1 / 2 : ℝ) • fderiv ℝ w (q x)) (x := y_z)
            simp only [add_apply, ContinuousLinearMap.comp_apply, smul_apply, innerSL_apply_apply,
              orthogonalLineEquiv_apply, hqyt, InnerProductSpace.toDual_apply_apply, inner_add_left,
              inner_add_right, inner_smul_left, inner_smul_right,
              Submodule.mem_orthogonal_singleton_iff_inner_left.mp v.2,
              Submodule.mem_orthogonal_singleton_iff_inner_right.mp y_z.2,
              real_inner_self_eq_norm_sq, he, smul_eq_mul, starRingEnd_apply, star_trivial,
              mul_zero, add_zero, zero_add, one_pow, mul_one, hv_apply]
            ring
          rw [← ofReal_norm, hdh.fderiv, hdual, LinearIsometryEquiv.norm_map]
          congr 1
          have hsq : ‖(v : E) + σ • e‖ ^ 2 = ((1 / 2) * √(4 + ‖fderiv ℝ w (q x)‖ ^ 2)) ^ 2 := by
            rw [norm_add_smul_sq e he, hv_norm, hσsq, mul_pow, mul_pow,
              Real.sq_sqrt (add_nonneg (by norm_num) (sq_nonneg _))]
            ring
          nlinarith [norm_nonneg ((v : E) + σ • e), Real.sqrt_nonneg (4 + ‖fderiv ℝ w (q x)‖ ^ 2)]
        · have hev : u =ᶠ[𝓝 x] fun _ ↦ δ := by
            filter_upwards [(isOpen_lt continuous_const hcont_h).mem_nhds hgt] with z hz
            simp [u, max_eq_left (hδ.trans hz).le, min_eq_right hz.le]
          rw [hev.fderiv_eq, fderiv_const_apply,
            indicator_of_notMem (fun (hx : 0 < h x ∧ h x < δ) ↦ hgt.not_gt hx.2)]
          exact (eNorm_eq_zero (a := (0 : E →L[ℝ] ℝ))).2 rfl
    have hgrad_meas : AEMeasurable
        ({x : E | 0 < h x ∧ h x < δ}.indicator
          (fun x ↦ ENNReal.ofReal ((1 / 2) * √(4 + ‖fderiv ℝ w (q x)‖ ^ 2)))) volume :=
      ((ENNReal.continuous_ofReal.comp (continuous_const.mul (Real.continuous_sqrt.comp
        (continuous_const.add (((hw.continuous_fderiv one_ne_zero).comp q.continuous).norm.pow
          2))))).measurable.indicator ((measurableSet_lt measurable_const hcont_h.measurable).inter
            (measurableSet_lt hcont_h.measurable measurable_const))).aemeasurable
    calc ∫⁻ r in Ioo 0 δ, perimeter volume ⊤ {x : E | r < h x}
        = ∫⁻ r in Ioo 0 δ, perimeter volume ⊤ {x : E | r < u x} :=
          setLIntegral_congr_fun measurableSet_Ioo fun r hr ↦ by rw [hsuper r hr]
      _ ≤ ∫⁻ r, perimeter volume ⊤ {x : E | r < u x} := setLIntegral_le_lintegral _ _
      _ = ∫⁻ x, ‖fderiv ℝ u x‖ₑ := by
          rw [hulip.lintegral_perimeter_eq_setLIntegral_enorm_fderiv, Opens.coe_top,
            Measure.restrict_univ]
      _ = ∫⁻ x, {x : E | 0 < h x ∧ h x < δ}.indicator
            (fun x ↦ ENNReal.ofReal ((1 / 2) * √(4 + ‖fderiv ℝ w (q x)‖ ^ 2))) x :=
          lintegral_congr_ae hgrad_ae
      _ = ∫⁻ y : H, ∫⁻ t : ℝ, {x : E | 0 < h x ∧ h x < δ}.indicator
            (fun x ↦ ENNReal.ofReal ((1 / 2) * √(4 + ‖fderiv ℝ w (q x)‖ ^ 2)))
            ((y : E) + t • e) :=
          lintegral_eq_lintegral_lintegral_line e he hgrad_meas
      _ ≤ ∫⁻ y : H, {y : H | ε < w y}.indicator
            (fun y ↦ ENNReal.ofReal δ * ENNReal.ofReal √(4 + ‖fderiv ℝ w y‖ ^ 2)) y := by
          refine lintegral_mono fun y ↦ ?_
          set c : ℝ≥0∞ := ENNReal.ofReal ((1 / 2) * √(4 + ‖fderiv ℝ w y‖ ^ 2))
          set T : Set ℝ := {t : ℝ | 0 < (w y - ε) / 2 - |t| ∧ (w y - ε) / 2 - |t| < δ}
          have hTm : MeasurableSet T :=
            (measurableSet_lt measurable_const
              (measurable_const.sub continuous_abs.measurable)).inter
              (measurableSet_lt (measurable_const.sub continuous_abs.measurable) measurable_const)
          rw [show (fun t : ℝ ↦ {x : E | 0 < h x ∧ h x < δ}.indicator
              (fun x ↦ ENNReal.ofReal ((1 / 2) * √(4 + ‖fderiv ℝ w (q x)‖ ^ 2)))
              ((y : E) + t • e)) = T.indicator (fun _ ↦ c) from funext fun t ↦ by
                by_cases ht : t ∈ T
                · rw [indicator_of_mem ht, indicator_of_mem (by simpa [T, hhyt] using ht), hqyt]
                · rw [indicator_of_notMem ht, indicator_of_notMem (by simpa [T, hhyt] using ht)],
            lintegral_indicator_const hTm]
          by_cases hy : ε < w y
          · rw [indicator_of_mem hy]
            set R : ℝ := (w y - ε) / 2
            have hTvol : volume T ≤ ENNReal.ofReal (2 * δ) := by
              have hTsub : T ⊆ Ioo (R - δ) R ∪ Ioo (-R) (-(R - δ)) := fun t ⟨h1, h2⟩ ↦ by
                change 0 < R - |t| at h1; change R - |t| < δ at h2
                rcases le_or_gt 0 t with ht | ht
                · rw [abs_of_nonneg ht] at h1 h2; exact Or.inl ⟨by linarith, by linarith⟩
                · rw [abs_of_neg ht] at h1 h2; exact Or.inr ⟨by linarith, by linarith⟩
              refine ((measure_mono hTsub).trans (measure_union_le _ _)).trans_eq ?_
              rw [Real.volume_Ioo, Real.volume_Ioo, show R - (R - δ) = δ by ring,
                show -(R - δ) - -R = δ by ring, ← ENNReal.ofReal_add hδ.le hδ.le, two_mul]
            refine (mul_le_mul_right hTvol c).trans_eq ?_
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hδ.le]
            congr 1; ring
          · rw [indicator_of_notMem hy,
              eq_empty_of_forall_notMem (s := T) fun t ⟨h1, _⟩ ↦ by linarith [abs_nonneg t]]
            simp
      _ = ENNReal.ofReal δ *
            ∫⁻ y in {y : H | ε < w y}, ENNReal.ofReal √(4 + ‖fderiv ℝ w y‖ ^ 2) := by
          rw [lintegral_indicator (measurableSet_lt measurable_const hw.continuous.measurable),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  set B : ℝ≥0∞ := ∫⁻ y in {y : H | ε < w y}, ENNReal.ofReal √(4 + ‖fderiv ℝ w y‖ ^ 2)
  rcases eq_or_ne B ∞ with hBtop | hBfin
  · simp [hBtop]
  have hexists (k : ℕ) : ∃ r ∈ Ioo (0 : ℝ) (1 / ((k : ℝ) + 1)),
      perimeter volume ⊤ {x : E | r < h x} ≤ B + ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    set δ : ℝ := 1 / ((k : ℝ) + 1)
    have hδ : 0 < δ := by positivity
    by_contra! hgt
    have hle : ENNReal.ofReal δ * B + ENNReal.ofReal δ * ENNReal.ofReal δ ≤
        ENNReal.ofReal δ * B := by
      have h1 : ENNReal.ofReal δ * (B + ENNReal.ofReal δ) =
          ∫⁻ _ in Ioo 0 δ, (B + ENNReal.ofReal δ) := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero, mul_comm]
      rw [← mul_add, h1]
      exact (setLIntegral_mono' measurableSet_Ioo fun r hr ↦ (hgt r hr).le).trans (hcoarea hδ)
    have h0 : ENNReal.ofReal δ * ENNReal.ofReal δ = 0 := nonpos_iff_eq_zero.1 <|
      WithTop.le_of_add_le_add_left (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin)
        (hle.trans_eq (add_zero _).symm)
    exact mul_ne_zero (by positivity) (by positivity) h0
  choose r hr_mem hr_per using hexists
  have hS_fin : volume {x : E | 0 < h x} ≠ ∞ := by
    rw [volume_eq_lintegral_volume_lineSection e he
      (measurableSet_lt measurable_const hcont_h.measurable).nullMeasurableSet]
    refine ne_top_of_le_ne_top hwi.2.ne (lintegral_mono fun y ↦ ?_)
    rw [← hS_eq, lineSection_symmetricSubgraph_eq e he w ε y, Real.volume_eball,
      ENNReal.mul_div_cancel (by norm_num) (by norm_num), Real.eNorm_of_nonneg (hw0 y)]
    exact ENNReal.ofReal_le_ofReal (max_le (by linarith) (hw0 y))
  have hL1 : Tendsto (fun k ↦ volume ({x : E | r k < h x} ∆ {x : E | 0 < h x})) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_measure_setOf_pos_le_one_div hcont_h.measurable.aemeasurable hS_fin)
      (fun _ ↦ zero_le) fun k ↦ measure_mono fun x hx ↦ ?_
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd ((hr_mem k).1.trans h1) h2
    · exact ⟨h1, (not_lt.1 h2).trans (hr_mem k).2.le⟩
  calc perimeter volume ⊤ {x : E | 0 < h x}
      ≤ liminf (fun k : ℕ ↦ perimeter volume ⊤ {x : E | r k < h x}) atTop :=
        perimeter_le_liminf_of_tendsto_symmDiff
          (fun _ ↦ (measurableSet_lt measurable_const hcont_h.measurable).nullMeasurableSet)
          (measurableSet_lt measurable_const hcont_h.measurable).nullMeasurableSet hL1
    _ ≤ liminf (fun k : ℕ ↦ B + ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop :=
        liminf_le_liminf (.of_forall hr_per)
    _ = B := Tendsto.liminf_eq <| by
        simpa only [ENNReal.ofReal_zero, add_zero] using
          (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat).const_add B

end SymmetricSubgraph

section MollifiedExcess

/-- **One-mollifier slicing excess bound.** For any fixed normalized radial bump `ρ` on
`H = (ℝ ∙ e)ᗮ`, writing `d = ρ ⋆ (2 · 1_D)`, `w = ρ ⋆ v`, `a = ρ ⋆ 1_A` and
`M = 2 |D| + |Dv|`, the localized joint slicing inequality yields
`M ∫ √(d² + ‖Dw‖²) + 2 (∫ a √d)² ≤ M P(s)`. -/
private theorem mollified_slicing_excess_le {s : Set E} (hs : NullMeasurableSet s volume)
    (hfin : volume s ≠ ∞) (hP : perimeter volume ⊤ s ≠ ∞) (e : E) (he : ‖e‖ = 1)
    {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    (hDfin : volume {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} ≠ ∞)
    (hAfin : volume A ≠ ∞)
    (hv_int : Integrable (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s}) volume)
    (hv_tv_fin : totalVariationOn volume ⊤
      (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s}) ≠ ∞)
    (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ)) :
    let H := (ℝ ∙ e)ᗮ
    let D : Set H := {y : H | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
    let v : H → ℝ := fun y ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s}
    let κ : H → ℝ := ρ.normed volume
    let d : H → ℝ := κ ⋆[lsmul ℝ ℝ, volume] D.indicator (fun _ ↦ (2 : ℝ))
    let w : H → ℝ := κ ⋆[lsmul ℝ ℝ, volume] v
    let a : H → ℝ := κ ⋆[lsmul ℝ ℝ, volume] A.indicator (fun _ ↦ (1 : ℝ))
    let M : ℝ := 2 * volume.real D + (totalVariationOn volume ⊤ v).toReal
    M * (∫ y : H, √(d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2)) + 2 * (∫ y : H, a y * √(d y)) ^ 2 ≤
      M * (perimeter volume ⊤ s).toReal := by
  intro H D v κ d w a M
  have hD : NullMeasurableSet D volume :=
    nullMeasurableSet_lt aemeasurable_const (aemeasurable_volume_lineSection e he hs)
  have hD_ind_int : Integrable (D.indicator (fun _ ↦ (2 : ℝ))) volume :=
    (integrableOn_const hDfin).integrable_indicator₀ hD
  have hA_ind_int : Integrable (A.indicator (fun _ ↦ (1 : ℝ))) volume :=
    (integrableOn_const hAfin).integrable_indicator₀ hA
  have hcsmooth {f : H → ℝ} (hf : Integrable f volume) :
      ContDiff ℝ (⊤ : ℕ∞) (κ ⋆[lsmul ℝ ℝ, volume] f) :=
    ρ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) ρ.contDiff_normed
      hf.locallyIntegrable
  have hd_smooth : ContDiff ℝ (⊤ : ℕ∞) d := hcsmooth hD_ind_int
  have hw_smooth : ContDiff ℝ (⊤ : ℕ∞) w := hcsmooth hv_int
  have ha_smooth : ContDiff ℝ (⊤ : ℕ∞) a := hcsmooth hA_ind_int
  have hd_int : Integrable d volume := ρ.integrable_normed.integrable_convolution _ hD_ind_int
  have ha_int : Integrable a volume := ρ.integrable_normed.integrable_convolution _ hA_ind_int
  have hd_mem (y : H) : d y ∈ Icc (0 : ℝ) 2 :=
    ρ.normed_convolution_mem_Icc hD_ind_int.locallyIntegrable
      (fun z ↦ by by_cases hz : z ∈ D <;> simp [hz]) y
  have ha_mem (y : H) : a y ∈ Icc (0 : ℝ) 1 :=
    ρ.normed_convolution_mem_Icc hA_ind_int.locallyIntegrable
      (fun z ↦ by by_cases hz : z ∈ A <;> simp [hz]) y
  have hd_int_eq : ∫ y : H, d y = 2 * volume.real D := by
    rw [integral_convolution (lsmul ℝ ℝ) ρ.integrable_normed hD_ind_int, lsmul_apply,
      ρ.integral_normed, one_smul, integral_indicator₀ hD, setIntegral_const, smul_eq_mul, mul_comm]
  have ha_int_eq : ∫ y : H, a y = volume.real A := by
    rw [integral_convolution (lsmul ℝ ℝ) ρ.integrable_normed hA_ind_int, lsmul_apply,
      ρ.integral_normed, one_smul, integral_indicator₀ hA, setIntegral_const, smul_eq_mul, mul_one]
  let gradW : H → H := fun y ↦ (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ w y)
  have hgradW_smooth : ContDiff ℝ (⊤ : ℕ∞) gradW :=
    (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearMap.contDiff.comp
      (hw_smooth.fderiv_right (by simp))
  have hgradW_norm (y : H) : ‖gradW y‖ = ‖fderiv ℝ w y‖ := LinearIsometryEquiv.norm_map _ _
  have hw1 : ContDiff ℝ 1 w := hw_smooth.of_le (by simp)
  have hgradW_cont : Continuous (fun y : H ↦ ‖fderiv ℝ w y‖) :=
    (hw1.continuous_fderiv one_ne_zero).norm
  have hgradW_int : Integrable (fun y : H ↦ ‖fderiv ℝ w y‖) volume :=
    integrable_norm_fderiv_normed_convolution ρ hv_int hv_tv_fin
  have hgradW_int_le : ∫ y : H, ‖fderiv ℝ w y‖ ≤ (totalVariationOn volume ⊤ v).toReal := by
    have h1 : ENNReal.ofReal (∫ y : H, ‖fderiv ℝ w y‖) = totalVariationOn volume ⊤ w := by
      rw [ofReal_integral_eq_lintegral_ofReal hgradW_int (.of_forall fun _ ↦ opNorm_nonneg _),
        hw1.locallyLipschitz.locallyLipschitzOn.totalVariationOn_eq_setLIntegral_enorm_fderiv,
        Opens.coe_top, Measure.restrict_univ]
      exact lintegral_congr fun y ↦ ofReal_norm (fderiv ℝ w y)
    exact (ENNReal.ofReal_le_iff_le_toReal hv_tv_fin).1 <| h1.symm ▸
      ρ.totalVariationOn_normed_convolution_le (hv_int.locallyIntegrable.locallyIntegrableOn _)
        fun _ _ ↦ subset_univ _
  -- For any fixed `δ > 0`, prove the regularized estimate before letting `δ → 0⁺`.
  have hdelta {δ : ℝ} (hδ : 0 < δ) :
      let g : H → ℝ := fun y ↦ √(d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2 + δ ^ 2)
      let Mδ : ℝ := M + δ * volume.real A
      Mδ * (∫ y : H, (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y) + 2 * (∫ y : H, a y * √(d y)) ^ 2 ≤
        Mδ * (perimeter volume ⊤ s).toReal := by
    intro g Mδ
    have hg_pos (y : H) : 0 < g y := Real.sqrt_pos.2 (by positivity)
    have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
      have hinner : ContDiff ℝ (⊤ : ℕ∞) fun y : H ↦ d y ^ 2 + ⟪gradW y, gradW y⟫_ℝ + δ ^ 2 :=
        ((hd_smooth.pow 2).add (hgradW_smooth.inner ℝ hgradW_smooth)).add contDiff_const
      have hrad : (fun y : H ↦ d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2 + δ ^ 2) =
          fun y : H ↦ d y ^ 2 + ⟪gradW y, gradW y⟫_ℝ + δ ^ 2 :=
        funext fun y ↦ by rw [real_inner_self_eq_norm_sq, hgradW_norm]
      rw [contDiff_iff_contDiffAt]
      exact fun y ↦ (Real.contDiffAt_sqrt (by positivity)).comp y (hrad ▸ hinner.contDiffAt)
    have hdg_mem (y : H) : d y / g y ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (hd_mem y).1 (hg_pos y).le, (div_le_one (hg_pos y)).2
        (Real.le_sqrt_of_sq_le (by linarith [sq_nonneg ‖fderiv ℝ w y‖, sq_nonneg δ]))⟩
    -- Test the localized slicing bound against compactly supported cutoffs `η`.
    have heta (η : ContDiffBump (0 : H)) :
        (∫ y : H, η y * (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y) +
          2 * (∫ y : H, a y * (d y / g y)) ≤ (perimeter volume ⊤ s).toReal := by
      let ψ₀ : H → ℝ := fun y ↦ η y * d y / g y
      let φ₀_fun : H → H := fun y ↦ (-(η y * (g y)⁻¹)) • gradW y
      let φ₀ : 𝓓(⊤, H) := ⟨φ₀_fun,
        ((η.contDiff.mul (hg_smooth.inv fun y ↦ (hg_pos y).ne')).neg).smul hgradW_smooth,
        (η.hasCompactSupport.mul_right.neg).smul_right, subset_univ _⟩
      let φ : 𝓓(⊤, H) := TestFunction.mollify φ₀ volume ρ (subset_univ _)
      let ψ : H → ℝ := κ ⋆[lsmul ℝ ℝ, volume] ψ₀
      let α : H → ℝ := κ ⋆[lsmul ℝ ℝ, volume] (fun y ↦ d y / g y)
      have hψ₀_cont : Continuous ψ₀ :=
        (η.continuous.mul hd_smooth.continuous).div hg_smooth.continuous fun y ↦ (hg_pos y).ne'
      have hdg_cont : Continuous (fun y : H ↦ d y / g y) :=
        hd_smooth.continuous.div hg_smooth.continuous fun y ↦ (hg_pos y).ne'
      have hψ₀_mem (y : H) : ψ₀ y ∈ Icc (0 : ℝ) 1 := by
        refine ⟨div_nonneg (mul_nonneg η.nonneg (hd_mem y).1) (hg_pos y).le, ?_⟩
        rw [show ψ₀ y = η y * (d y / g y) from mul_div_assoc _ _ _]
        exact (mul_le_mul η.le_one (hdg_mem y).2 (hdg_mem y).1 zero_le_one).trans_eq (one_mul 1)
      have hsq_α (y : H) : (d y / g y) ^ 2 + ‖φ₀ y‖ ^ 2 ≤ 1 := by
        have hnorm : ‖φ₀ y‖ = η y * ‖fderiv ℝ w y‖ / g y := by
          change ‖(-(η y * (g y)⁻¹)) • gradW y‖ = _
          rw [norm_smul, norm_neg,
            Real.norm_of_nonneg (mul_nonneg η.nonneg (inv_nonneg.2 (hg_pos y).le)), hgradW_norm,
            div_eq_mul_inv]
          ring
        rw [hnorm, div_pow, div_pow, mul_pow, ← add_div, div_le_one (sq_pos_of_pos (hg_pos y)),
          Real.sq_sqrt (by positivity)]
        have hη1 : η y ^ 2 ≤ 1 := by nlinarith [η.nonneg (x := y), η.le_one (x := y)]
        nlinarith [sq_nonneg ‖fderiv ℝ w y‖, sq_nonneg δ]
      have hsq_ψ (y : H) : ψ₀ y ^ 2 + ‖φ₀ y‖ ^ 2 ≤ 1 := by
        have hψle : ψ₀ y ^ 2 ≤ (d y / g y) ^ 2 := by
          rw [show ψ₀ y = η y * (d y / g y) from mul_div_assoc _ _ _, mul_pow]
          exact mul_le_of_le_one_left (sq_nonneg _)
            (by nlinarith [η.nonneg (x := y), η.le_one (x := y)])
        exact (add_le_add hψle le_rfl).trans (hsq_α y)
      have hφ_le (y : H) : ‖φ y‖ ≤ 1 := by
        rw [TestFunction.mollify_apply]
        exact ρ.norm_normed_convolution_le (fun z ↦ by
          nlinarith [hsq_α z, sq_nonneg (d z / g z), norm_nonneg (φ₀ z)]) y
      have hpair_D : ∫ y : H, D.indicator (fun _ ↦ (2 : ℝ)) y * ψ y =
          ∫ y : H, η y * d y ^ 2 / g y := by
        rw [integral_mul_normed_convolution_eq_of_bdd ρ hD_ind_int hψ₀_cont.aestronglyMeasurable
          (C := 1) fun y ↦ by rw [Real.norm_of_nonneg (hψ₀_mem y).1]; exact (hψ₀_mem y).2]
        exact integral_congr_ae (.of_forall fun y ↦ by dsimp [ψ₀]; ring)
      have hpair_A : ∫ y : H, A.indicator (fun _ ↦ (1 : ℝ)) y * α y =
          ∫ y : H, a y * (d y / g y) :=
        integral_mul_normed_convolution_eq_of_bdd ρ hA_ind_int hdg_cont.aestronglyMeasurable
          (C := 1) fun y ↦ by rw [Real.norm_of_nonneg (hdg_mem y).1]; exact (hdg_mem y).2
      have hpair_div : ∫ y : H, divergenceCLM φ y * v y =
          ∫ y : H, η y * ‖fderiv ℝ w y‖ ^ 2 / g y := by
        obtain ⟨C, hC⟩ := (divergenceCLM φ₀).continuous.bounded_above_of_compact_support
          (divergenceCLM φ₀).hasCompactSupport
        have h1 : ∫ y : H, divergenceCLM φ y * v y =
            ∫ y : H, v y * (κ ⋆[lsmul ℝ ℝ, volume] (divergenceCLM φ₀ : H → ℝ)) y :=
          integral_congr_ae (.of_forall fun y ↦ by dsimp only; rw [mul_comm, divergenceCLM_mollify])
        rw [h1, integral_mul_normed_convolution_eq_of_bdd ρ hv_int
          (divergenceCLM φ₀).continuous.aestronglyMeasurable hC,
          integral_congr_ae (.of_forall fun y ↦ by rw [mul_comm, ← smul_eq_mul]),
          ((hw_smooth.of_le (by simp)).contDiffOn.hasWeakFDerivOn_fderiv
            (μ := volume) (Ω := ⊤)).integral_divergenceCLM_smul_eq_neg_integral φ₀,
          ← integral_neg]
        refine integral_congr_ae (.of_forall fun y ↦ ?_)
        dsimp only
        rw [(InnerProductSpace.toDual_symm_apply (y := fderiv ℝ w y) (x := φ₀ y)).symm]
        change -⟪gradW y, (-(η y * (g y)⁻¹)) • gradW y⟫_ℝ = _
        rw [inner_smul_right, real_inner_self_eq_norm_sq, hgradW_norm, div_eq_mul_inv]
        ring
      have hterm_le {S : Set H} (hS : NullMeasurableSet S volume) {c : ℝ} (hc : 0 ≤ c)
          (hS_int : Integrable (S.indicator (fun _ ↦ c)) volume) {h₀ : H → ℝ} (hh₀ : Continuous h₀)
          (hmem : ∀ y, h₀ y ∈ Icc (0 : ℝ) 1) (hsq : ∀ y, h₀ y ^ 2 + ‖φ₀ y‖ ^ 2 ≤ 1) :
          ENNReal.ofReal (∫ y : H, S.indicator (fun _ ↦ c) y * (κ ⋆[lsmul ℝ ℝ, volume] h₀) y) ≤
            ENNReal.ofReal c * ∫⁻ y in S, ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) := by
        have hm (y : H) := ρ.normed_convolution_mem_Icc (μ := volume) hh₀.locallyIntegrable hmem y
        have hcont : Continuous (κ ⋆[lsmul ℝ ℝ, volume] h₀) :=
          ρ.hasCompactSupport_normed.continuous_convolution_left
            (lsmul ℝ ℝ) ρ.continuous_normed hh₀.locallyIntegrable
        rw [ofReal_integral_eq_lintegral_ofReal (hS_int.mul_bdd (c := 1)
              hcont.aestronglyMeasurable (.of_forall fun y ↦ by
                rw [Real.norm_of_nonneg (hm y).1]; exact (hm y).2))
            (.of_forall fun y ↦ mul_nonneg (by by_cases hy : y ∈ S <;> simp [hy, hc]) (hm y).1),
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator₀ hS]
        refine lintegral_mono fun y ↦ ?_
        by_cases hy : y ∈ S
        · rw [indicator_of_mem hy, indicator_of_mem hy, ENNReal.ofReal_mul hc,
            TestFunction.mollify_apply]
          exact mul_le_mul_right (ENNReal.ofReal_le_ofReal
            (normed_convolution_le_sqrt_one_sub_sq ρ hh₀ φ₀.continuous hsq y)) _
        · simp [hy]
      have htermD : ENNReal.ofReal (∫ y : H, D.indicator (fun _ ↦ (2 : ℝ)) y * ψ y) ≤
          2 * ∫⁻ y in D, ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) := by
        simpa only [ENNReal.ofReal_ofNat] using
          hterm_le hD zero_le_two hD_ind_int hψ₀_cont hψ₀_mem hsq_ψ
      have htermA : ENNReal.ofReal (2 * ∫ y : H, A.indicator (fun _ ↦ (1 : ℝ)) y * α y) ≤
          2 * ∫⁻ y in A, ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) := by
        rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
        refine mul_le_mul_right ?_ 2
        simpa only [ENNReal.ofReal_one, one_mul] using
          hterm_le hA zero_le_one hA_ind_int hdg_cont hdg_mem hsq_α
      have hI1 : Integrable (fun y : H ↦ η y * d y ^ 2 / g y) volume :=
        hd_int.mono' (((η.continuous.mul (hd_smooth.continuous.pow 2)).div
          hg_smooth.continuous fun y ↦ (hg_pos y).ne').aestronglyMeasurable) (.of_forall fun y ↦ by
            rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg η.nonneg (sq_nonneg _)) (hg_pos y).le),
              show η y * d y ^ 2 / g y = ψ₀ y * d y by dsimp [ψ₀]; ring]
            exact mul_le_of_le_one_left (hd_mem y).1 (hψ₀_mem y).2)
      have hI2 : Integrable (fun y : H ↦ η y * ‖fderiv ℝ w y‖ ^ 2 / g y) volume :=
        hgradW_int.mono' (((η.continuous.mul (hgradW_cont.pow 2)).div
          hg_smooth.continuous fun y ↦ (hg_pos y).ne').aestronglyMeasurable) (.of_forall fun y ↦ by
            rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg η.nonneg (sq_nonneg _)) (hg_pos y).le),
              show η y * ‖fderiv ℝ w y‖ ^ 2 / g y = (η y * (‖fderiv ℝ w y‖ / g y)) *
                ‖fderiv ℝ w y‖ by ring]
            have hle1 : ‖fderiv ℝ w y‖ / g y ≤ 1 := (div_le_one (hg_pos y)).2
              (Real.le_sqrt_of_sq_le (by linarith [sq_nonneg (d y), sq_nonneg δ]))
            exact mul_le_of_le_one_left (opNorm_nonneg _)
              ((mul_le_mul η.le_one hle1 (div_nonneg (opNorm_nonneg _) (hg_pos y).le)
                zero_le_one).trans_eq (one_mul 1)))
      rw [show (∫ y : H, η y * (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y) =
            (∫ y : H, η y * d y ^ 2 / g y) + ∫ y : H, η y * ‖fderiv ℝ w y‖ ^ 2 / g y by
          rw [← integral_add hI1 hI2]; exact integral_congr_ae (.of_forall fun _ ↦ by ring)]
      refine (ENNReal.ofReal_le_iff_le_toReal hP).1 ?_
      rw [add_right_comm]
      exact (ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)).trans <| by
        rw [← hpair_D, ← hpair_A, ← hpair_div]
        exact (add_le_add (add_le_add htermD htermA) le_rfl).trans
          (two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter
            hs hfin e he hA hbad φ hφ_le)
    -- Exhaust `H` with bumps `ηseq m ↑ 1` by dominated convergence.
    let ηseq : ℕ → ContDiffBump (0 : H) := fun m ↦
      ⟨(m : ℝ) + 1, (m : ℝ) + 2, by positivity, by linarith⟩
    have hη_lim : Tendsto (fun m ↦ ∫ y : H, ηseq m y * (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y)
        atTop (𝓝 (∫ y : H, (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y)) := by
      refine tendsto_integral_of_dominated_convergence (fun y ↦ d y + ‖fderiv ℝ w y‖)
        (fun m ↦ (((ηseq m).continuous.mul ((hd_smooth.continuous.pow 2).add
          (hgradW_cont.pow 2))).div hg_smooth.continuous
          fun y ↦ (hg_pos y).ne').aestronglyMeasurable)
        (hd_int.add hgradW_int) (fun m ↦ .of_forall fun y ↦ ?_) (.of_forall fun y ↦ ?_)
      · have hq0 : 0 ≤ (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y :=
          div_nonneg (by positivity) (hg_pos y).le
        rw [mul_div_assoc, Real.norm_of_nonneg (mul_nonneg (ηseq m).nonneg hq0)]
        exact (mul_le_of_le_one_left hq0 (ηseq m).le_one).trans
          (div_sqrt_add_sq_le (hd_mem y).1 (opNorm_nonneg _) hδ)
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop (Nat.ceil ‖y‖)] with m hm
        have hball : y ∈ closedBall (0 : H) (ηseq m).rIn := by
          rw [mem_closedBall_zero_iff]
          have h1 : ‖y‖ ≤ (m : ℝ) := (Nat.le_ceil ‖y‖).trans (Nat.cast_le.2 hm)
          change ‖y‖ ≤ (m : ℝ) + 1; linarith
        rw [(ηseq m).one_of_mem_closedBall hball, one_mul]
    have hfull : (∫ y : H, (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y) +
        2 * (∫ y : H, a y * (d y / g y)) ≤ (perimeter volume ⊤ s).toReal :=
      le_of_tendsto (hη_lim.add tendsto_const_nhds) (.of_forall fun m ↦ heta (ηseq m))
    -- Apply Cauchy–Schwarz to bound `(∫ a √d)²` by `(∫ a d / g) (∫ a g)`.
    have hag_pt (y : H) : a y * g y ≤ d y + ‖fderiv ℝ w y‖ + δ * a y := by
      have hg_le : g y ≤ d y + ‖fderiv ℝ w y‖ + δ := by
        rw [Real.sqrt_le_left (by linarith [(hd_mem y).1, opNorm_nonneg (fderiv ℝ w y), hδ])]
        nlinarith [(hd_mem y).1, opNorm_nonneg (fderiv ℝ w y), hδ]
      nlinarith [mul_le_mul_of_nonneg_left hg_le (ha_mem y).1, (ha_mem y).2, (hd_mem y).1,
        opNorm_nonneg (fderiv ℝ w y)]
    have hf1_int : Integrable (fun y : H ↦ a y * (d y / g y)) volume :=
      ha_int.mul_bdd (c := 1) (hd_smooth.continuous.div hg_smooth.continuous
        fun y ↦ (hg_pos y).ne').aestronglyMeasurable
        (.of_forall fun y ↦ by rw [Real.norm_of_nonneg (hdg_mem y).1]; exact (hdg_mem y).2)
    have hdg_int : Integrable (fun y : H ↦ d y + ‖fderiv ℝ w y‖) volume := hd_int.add hgradW_int
    have hf2_int : Integrable (fun y : H ↦ a y * g y) volume :=
      (hdg_int.add (ha_int.const_mul δ)).mono'
        (ha_smooth.continuous.mul hg_smooth.continuous).aestronglyMeasurable
        (.of_forall fun y ↦ by
          rw [Real.norm_of_nonneg (mul_nonneg (ha_mem y).1 (hg_pos y).le)]; exact hag_pt y)
    have hcs := sq_integral_mul_le_integral_sq_mul_integral_sq
      (memLp_two_sqrt hf1_int fun y ↦ mul_nonneg (ha_mem y).1 (hdg_mem y).1)
      (memLp_two_sqrt hf2_int fun y ↦ mul_nonneg (ha_mem y).1 (hg_pos y).le)
    rw [show (fun y : H ↦ √(a y * (d y / g y)) * √(a y * g y)) = fun y ↦ a y * √(d y) from
          funext fun y ↦ by
            rw [← Real.sqrt_mul (mul_nonneg (ha_mem y).1 (hdg_mem y).1),
              show a y * (d y / g y) * (a y * g y) = a y ^ 2 * d y by field_simp [(hg_pos y).ne'],
              Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (ha_mem y).1],
      show (fun y : H ↦ √(a y * (d y / g y)) ^ 2) = fun y ↦ a y * (d y / g y) from
        funext fun y ↦ Real.sq_sqrt (mul_nonneg (ha_mem y).1 (hdg_mem y).1),
      show (fun y : H ↦ √(a y * g y) ^ 2) = fun y ↦ a y * g y from
        funext fun y ↦ Real.sq_sqrt (mul_nonneg (ha_mem y).1 (hg_pos y).le)] at hcs
    have hag_le : ∫ y : H, a y * g y ≤ Mδ := by
      calc ∫ y : H, a y * g y
          ≤ ∫ y : H, (d y + ‖fderiv ℝ w y‖ + δ * a y) :=
            integral_mono hf2_int (hdg_int.add (ha_int.const_mul δ)) hag_pt
        _ = (∫ y : H, d y) + (∫ y : H, ‖fderiv ℝ w y‖) + δ * ∫ y : H, a y := by
            rw [integral_add hdg_int (ha_int.const_mul δ), integral_add hd_int hgradW_int,
              integral_const_mul]
        _ ≤ Mδ := by rw [hd_int_eq, ha_int_eq]; dsimp [Mδ, M]; linarith
    have hcs' : (∫ y : H, a y * √(d y)) ^ 2 ≤ (∫ y : H, a y * (d y / g y)) * Mδ :=
      hcs.trans (mul_le_mul_of_nonneg_left hag_le
        (integral_nonneg fun y ↦ mul_nonneg (ha_mem y).1 (hdg_mem y).1))
    nlinarith [mul_le_mul_of_nonneg_left hfull (show 0 ≤ Mδ by dsimp [Mδ, M]; positivity)]
  -- Pass to `δ = 1 / (k + 1) → 0⁺` by dominated convergence.
  let δseq : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hδpos (k : ℕ) : 0 < δseq k := by positivity
  have hδlim : Tendsto δseq atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hM_lim : Tendsto (fun k ↦ M + δseq k * volume.real A) atTop (𝓝 M) := by
    simpa only [zero_mul, add_zero] using (hδlim.mul_const (volume.real A)).const_add M
  have hint_lim : Tendsto
      (fun k ↦ ∫ y : H, (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) /
        √(d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2 + δseq k ^ 2))
      atTop (𝓝 (∫ y : H, √(d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2))) := by
    refine tendsto_integral_of_dominated_convergence (fun y ↦ d y + ‖fderiv ℝ w y‖)
      (fun k ↦ (((hd_smooth.continuous.pow 2).add (hgradW_cont.pow 2)).div
        (Real.continuous_sqrt.comp (((hd_smooth.continuous.pow 2).add (hgradW_cont.pow 2)).add
          continuous_const)) fun y ↦ (Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos
            (add_nonneg (sq_nonneg _) (sq_nonneg _))
            (sq_pos_of_pos (hδpos k)))).ne').aestronglyMeasurable)
      (hd_int.add hgradW_int)
      (fun k ↦ .of_forall fun y ↦ by
        rw [Real.norm_of_nonneg (by positivity)]
        exact div_sqrt_add_sq_le (hd_mem y).1 (opNorm_nonneg _) (hδpos k))
      (.of_forall fun y ↦ ?_)
    set x : ℝ := d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2
    rcases eq_or_lt_of_le (show 0 ≤ x by positivity) with hx0 | hxpos
    · simp [← hx0]
    · have hden : Tendsto (fun k ↦ √(x + δseq k ^ 2)) atTop (𝓝 √x) :=
        (Real.continuous_sqrt.tendsto x).comp <| by
          simpa only [zero_pow two_ne_zero, add_zero] using (hδlim.pow 2).const_add x
      have hq := (tendsto_const_nhds (x := x)).div hden (Real.sqrt_pos.2 hxpos).ne'
      rwa [show x / √x = √x by rw [div_eq_iff (Real.sqrt_pos.2 hxpos).ne',
        Real.mul_self_sqrt hxpos.le]] at hq
  exact le_of_tendsto_of_tendsto ((hM_lim.mul hint_lim).add tendsto_const_nhds)
    (hM_lim.mul_const (perimeter volume ⊤ s).toReal) (.of_forall fun k ↦ hdelta (hδpos k))

end MollifiedExcess

section Main

/-- **Quantitative Steiner perimeter excess inequality.** Let `s` be a Lebesgue-measurable set of
finite volume, `e` a unit vector with orthogonal hyperplane `H = (ℝ ∙ e)ᗮ`, and `A ⊆ H` a
null-measurable family of noninterval line sections of `s`. Writing
`D = {y ∈ H | 0 < |s_y|}` and `v(y) = |s_y|`, we have

`(2 |D| + |Dv|) P(S_e s) + 4 |A|² ≤ (2 |D| + |Dv|) P(s)`,

whether the ambient perimeter `P(s)` is finite or infinite. -/
theorem mul_perimeter_steinerSymmetrization_add_four_mul_sq_le
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (e : E) (he : ‖e‖ = 1) {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) :
    (2 * volume {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} +
        totalVariationOn volume ⊤
          (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s})) *
        perimeter volume ⊤ (steinerSymmetrization e he s) + 4 * volume A ^ 2 ≤
      (2 * volume {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} +
        totalVariationOn volume ⊤
          (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s})) *
        perimeter volume ⊤ s := by
  let H := (ℝ ∙ e)ᗮ
  let D : Set H := {y : H | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  let v : H → ℝ := fun y ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s}
  let fD : H → ℝ := D.indicator (fun _ ↦ 2)
  let fA : H → ℝ := A.indicator (fun _ ↦ 1)
  -- Handle infinite ambient perimeter: then `volume s ≠ 0`, so `volume D ≠ 0` and RHS = ∞.
  by_cases hP : perimeter volume ⊤ s = ∞
  · have hD0 : volume D ≠ 0 := fun hD0 ↦ by
      have hs0 : volume s = 0 := by
        rw [volume_eq_lintegral_volume_lineSection e he hs,
          lintegral_eq_zero_iff' (aemeasurable_volume_lineSection e he hs)]
        have hD0' : ∀ᵐ y : H ∂volume, ¬0 < volume {t : ℝ | (y : E) + t • e ∈ s} :=
          ae_iff.2 (by simpa only [not_not] using hD0)
        filter_upwards [hD0'] with y hy
        exact nonpos_iff_eq_zero.1 (not_lt.1 hy)
      rw [perimeter_congr_ae (ae_restrict_of_ae (ae_eq_empty.2 hs0)), perimeter_empty] at hP
      exact ENNReal.zero_ne_top hP
    rw [hP, ENNReal.mul_top fun h0 ↦
      hD0 ((mul_eq_zero.1 (add_eq_zero.1 h0).1).resolve_left (by norm_num))]
    exact le_top
  -- Finite ambient perimeter: set up `D`, `A`, `v`, and shrinking mollifiers `ρ j`.
  have hD : NullMeasurableSet D volume :=
    nullMeasurableSet_lt aemeasurable_const (aemeasurable_volume_lineSection e he hs)
  have hDA_le := two_mul_volume_add_two_mul_volume_le_perimeter_of_noninterval_lineSection
    hs hfin e he hA hbad
  have hDfin : volume D ≠ ∞ := ne_top_of_le_ne_top hP <|
    (le_self_add.trans_eq (two_mul _).symm).trans (le_self_add.trans hDA_le)
  have hAfin : volume A ≠ ∞ := ne_top_of_le_ne_top hP <|
    (le_self_add.trans_eq (two_mul _).symm).trans (le_add_self.trans hDA_le)
  have hv_tv_fin : totalVariationOn volume ⊤ v ≠ ∞ :=
    ne_top_of_le_ne_top hP (totalVariationOn_measureReal_lineSection_le hs hfin e he)
  have hv_int : Integrable v volume :=
    ⟨(aemeasurable_volume_lineSection e he hs).ennreal_toReal.aestronglyMeasurable,
      (lintegral_mono fun y ↦ by
        rw [Real.eNorm_of_nonneg measureReal_nonneg, measureReal_def]
        exact ENNReal.ofReal_toReal_le).trans_lt
        ((volume_eq_lintegral_volume_lineSection e he hs).symm ▸ hfin.lt_top)⟩
  have hD_ind_int : Integrable fD volume := (integrableOn_const hDfin).integrable_indicator₀ hD
  have hAD : ∀ᵐ y : H ∂volume, y ∈ A → y ∈ D := by
    filter_upwards [hbad] with y hy hyA
    by_contra hyD
    exact hy hyA ∅ ordConnected_empty (ae_eq_empty.2 (nonpos_iff_eq_zero.1 (not_lt.1 hyD)))
  let M : ℝ := 2 * volume.real D + (totalVariationOn volume ⊤ v).toReal
  have hM_nonneg : 0 ≤ M := by positivity
  have hM_ofReal : ENNReal.ofReal M = 2 * volume D + totalVariationOn volume ⊤ v := by
    rw [ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg, ENNReal.ofReal_mul zero_le_two,
      ENNReal.ofReal_ofNat, ofReal_measureReal hDfin, ENNReal.ofReal_toReal hv_tv_fin]
  have hA_ofReal : ENNReal.ofReal (4 * volume.real A ^ 2) = 4 * volume A ^ 2 := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_pow measureReal_nonneg, ofReal_measureReal hAfin]
  have hq_qmp : QuasiMeasurePreserving
      (fun x : E ↦ ((orthogonalLineEquiv e he).symm x).1) volume volume :=
    Measure.quasiMeasurePreserving_fst.comp
      (MeasurePreserving.symm (orthogonalLineEquiv e he).toHomeomorph.toMeasurableEquiv
        (measurePreserving_orthogonalLineEquiv e he)).quasiMeasurePreserving
  let S_trunc : ℝ → Set E := fun ε ↦
    {x : E | |⟪e, x⟫_ℝ| < (v ((orthogonalLineEquiv e he).symm x).1 - ε) / 2}
  have hS_trunc_nm (ε : ℝ) : NullMeasurableSet (S_trunc ε) volume :=
    nullMeasurableSet_lt (continuous_const.inner continuous_id).abs.measurable.aemeasurable
      (((hv_int.aestronglyMeasurable.aemeasurable.comp_quasiMeasurePreserving hq_qmp).sub
        aemeasurable_const).div_const 2)
  let ρ : ℕ → ContDiffBump (0 : H) := ContDiffBump.shrinking one_pos
  have hρ_lim : Tendsto (fun j ↦ (ρ j).rOut) atTop (𝓝 0) :=
    ContDiffBump.tendsto_rOut_shrinking one_pos
  -- Step 1: For any `ε > 0` with `volume {v = ε} = 0`, pass to `j → ∞`.
  have hstep_eps {ε : ℝ} (hε : 0 < ε) (hlevel : volume {y : H | v y = ε} = 0) :
      ENNReal.ofReal M * perimeter volume ⊤ (S_trunc ε) + 4 * volume A ^ 2 ≤
        ENNReal.ofReal M * perimeter volume ⊤ s +
          ENNReal.ofReal (M * (2 * volume.real (D \ {y : H | ε < v y}))) := by
    let d : ℕ → H → ℝ := fun j ↦ (ρ j).normed volume ⋆[lsmul ℝ ℝ, volume] fD
    let w : ℕ → H → ℝ := fun j ↦ (ρ j).normed volume ⋆[lsmul ℝ ℝ, volume] v
    let a : ℕ → H → ℝ := fun j ↦ (ρ j).normed volume ⋆[lsmul ℝ ℝ, volume] fA
    let Sj : ℕ → Set E := fun j ↦
      {x : E | |⟪e, x⟫_ℝ| < (w j ((orthogonalLineEquiv e he).symm x).1 - ε) / 2}
    let Ej : ℕ → Set H := fun j ↦ {y : H | ε < w j y}
    let Eε : Set H := {y : H | ε < v y}
    let fEj : ℕ → H → ℝ := fun j ↦ (Ej j).indicator (fun _ ↦ 2)
    let fEε : H → ℝ := Eε.indicator (fun _ ↦ 2)
    have hw_smooth (j : ℕ) : ContDiff ℝ 1 (w j) :=
      (ρ j).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
        ((ρ j).contDiff_normed (n := 1)) hv_int.locallyIntegrable
    have hw0 (j : ℕ) (y : H) : 0 ≤ w j y :=
      le_convolution_lsmul_of_forall_le (ρ j).support_normed_eq.subset (ρ j).nonneg_normed
        (ρ j).integral_normed
        ((ρ j).hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
          (ρ j).continuous_normed hv_int.locallyIntegrable y)
        (fun _ _ ↦ measureReal_nonneg)
    have hw_int (j : ℕ) : Integrable (w j) volume :=
      (ρ j).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hv_int
    have hd_int (j : ℕ) : Integrable (d j) volume :=
      (ρ j).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hD_ind_int
    have hd_mem (j : ℕ) (y : H) : d j y ∈ Icc (0 : ℝ) 2 :=
      (ρ j).normed_convolution_mem_Icc hD_ind_int.locallyIntegrable
        (fun z ↦ by by_cases hz : z ∈ D <;> simp [fD, hz]) y
    have hEj_m (j : ℕ) : MeasurableSet (Ej j) :=
      measurableSet_lt measurable_const (hw_smooth j).continuous.measurable
    have hEε_nm : NullMeasurableSet Eε volume :=
      nullMeasurableSet_lt aemeasurable_const hv_int.aestronglyMeasurable.aemeasurable
    have hEj_fin (j : ℕ) : volume (Ej j) ≠ ∞ :=
      ne_top_of_le_ne_top ((hw_int j).measure_ge_lt_top hε).ne <|
        measure_mono fun _ (hy : ε < w j _) ↦ hy.le
    have hSj_nm (j : ℕ) : NullMeasurableSet (Sj j) volume :=
      (measurableSet_lt (continuous_const.inner continuous_id).abs.measurable
        ((((hw_smooth j).continuous.comp (continuous_fst.comp
          (orthogonalLineEquiv e he).symm.continuous)).sub continuous_const).div_const
          2).measurable).nullMeasurableSet
    -- Combine `perimeter_symmetricSubgraph_le` and `mollified_slicing_excess_le` for each `j`.
    have hper_j (j : ℕ) :
        ENNReal.ofReal M * perimeter volume ⊤ (Sj j) +
            ENNReal.ofReal (2 * (∫ y : H, a j y * √(d j y)) ^ 2) ≤
          ENNReal.ofReal M * perimeter volume ⊤ s +
            ENNReal.ofReal (M * ∫ y : H, |fEj j y - d j y|) := by
      have hgrad_int : Integrable (fun y : H ↦ ‖fderiv ℝ (w j) y‖) volume :=
        integrable_norm_fderiv_normed_convolution (ρ j) hv_int hv_tv_fin
      have hsqrt_int : Integrable (fun y : H ↦ √(d j y ^ 2 + ‖fderiv ℝ (w j) y‖ ^ 2)) volume := by
        refine ((hd_int j).add hgrad_int).mono'
          (Real.continuous_sqrt.comp ((((ρ j).hasCompactSupport_normed.continuous_convolution_left
            (lsmul ℝ ℝ) (ρ j).continuous_normed hD_ind_int.locallyIntegrable).pow 2).add
              (((hw_smooth j).continuous_fderiv one_ne_zero).norm.pow 2))).aestronglyMeasurable
          (.of_forall fun y ↦ ?_)
        rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        exact (Real.sqrt_le_left (add_nonneg (hd_mem j y).1 (opNorm_nonneg _))).2
          (by nlinarith [mul_nonneg (hd_mem j y).1 (opNorm_nonneg (fderiv ℝ (w j) y))])
      have hdiff_int : Integrable (fun y : H ↦ |fEj j y - d j y|) volume :=
        (((integrableOn_const (hEj_fin j)).integrable_indicator (hEj_m j)).sub (hd_int j)).abs
      have hsum_int : Integrable (fun y : H ↦ √(d j y ^ 2 + ‖fderiv ℝ (w j) y‖ ^ 2) +
          |fEj j y - d j y|) volume := hsqrt_int.add hdiff_int
      set I_sq := ∫ y : H, √(d j y ^ 2 + ‖fderiv ℝ (w j) y‖ ^ 2)
      set I_err := ∫ y : H, |fEj j y - d j y|
      have hper_upper : perimeter volume ⊤ (Sj j) ≤ ENNReal.ofReal (I_sq + I_err) := by
        calc perimeter volume ⊤ (Sj j)
            ≤ ∫⁻ y in Ej j, ENNReal.ofReal √(4 + ‖fderiv ℝ (w j) y‖ ^ 2) :=
              perimeter_symmetricSubgraph_le e he (hw_smooth j) (hw0 j) (hw_int j) hε
          _ ≤ ∫⁻ y : H, ENNReal.ofReal
                (√(d j y ^ 2 + ‖fderiv ℝ (w j) y‖ ^ 2) + |fEj j y - d j y|) := by
              rw [← lintegral_indicator (hEj_m j)]
              refine lintegral_mono fun y ↦ ?_
              by_cases hy : y ∈ Ej j
              · rw [indicator_of_mem hy]
                refine ENNReal.ofReal_le_ofReal ?_
                simpa only [fEj, indicator_of_mem hy, show (2 : ℝ) ^ 2 = 4 by norm_num] using
                  sqrt_sq_add_sq_le_add_abs (a := 2) (b := d j y)
                    (c := ‖fderiv ℝ (w j) y‖) (hd_mem j y).1
              · rw [indicator_of_notMem hy]; exact zero_le
          _ = ENNReal.ofReal (I_sq + I_err) := by
              rw [← integral_add hsqrt_int hdiff_int, ofReal_integral_eq_lintegral_ofReal hsum_int
                (.of_forall fun _ ↦ add_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))]
      have hmoll := mollified_slicing_excess_le hs hfin hP e he hA hbad hDfin hAfin hv_int
        hv_tv_fin (ρ j)
      calc ENNReal.ofReal M * perimeter volume ⊤ (Sj j) +
              ENNReal.ofReal (2 * (∫ y : H, a j y * √(d j y)) ^ 2)
          ≤ ENNReal.ofReal M * ENNReal.ofReal (I_sq + I_err) +
              ENNReal.ofReal (2 * (∫ y : H, a j y * √(d j y)) ^ 2) := by gcongr
        _ = ENNReal.ofReal (M * I_sq + 2 * (∫ y : H, a j y * √(d j y)) ^ 2 + M * I_err) := by
            rw [← ENNReal.ofReal_mul hM_nonneg, ← ENNReal.ofReal_add
              (mul_nonneg hM_nonneg (add_nonneg (integral_nonneg fun _ ↦ Real.sqrt_nonneg _)
                (integral_nonneg fun _ ↦ abs_nonneg _))) (by positivity)]
            congr 1; ring
        _ ≤ ENNReal.ofReal (M * (perimeter volume ⊤ s).toReal + M * I_err) :=
            ENNReal.ofReal_le_ofReal (by linarith)
        _ = ENNReal.ofReal M * perimeter volume ⊤ s + ENNReal.ofReal (M * I_err) := by
            rw [ENNReal.ofReal_add (mul_nonneg hM_nonneg ENNReal.toReal_nonneg)
                (mul_nonneg hM_nonneg (integral_nonneg fun _ ↦ abs_nonneg _)),
              ENNReal.ofReal_mul hM_nonneg, ENNReal.ofReal_toReal hP]
    -- Limit 1: `Sj j → S_trunc ε` in `L¹`, so `P(S_trunc ε) ≤ liminf P(Sj j)`.
    have hSj_lim : Tendsto (fun j ↦ volume (Sj j ∆ S_trunc ε)) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (tendsto_lintegral_enorm_normed_convolution_sub hρ_lim hv_int) (fun _ ↦ zero_le) fun j ↦ ?_
      rw [volume_eq_lintegral_volume_lineSection e he ((hSj_nm j).symmDiff (hS_trunc_nm ε))]
      refine lintegral_mono fun y ↦ ?_
      have hsymm_sec : {t : ℝ | (y : E) + t • e ∈ Sj j ∆ S_trunc ε} =
          Metric.eball (0 : ℝ) (ENNReal.ofReal (max (w j y - ε) 0) / 2) ∆
            Metric.eball (0 : ℝ) (ENNReal.ofReal (max (v y - ε) 0) / 2) := by
        rw [← lineSection_symmetricSubgraph_eq e he (w j) ε y,
          ← lineSection_symmetricSubgraph_eq e he v ε y]
        ext t; simp only [Set.mem_symmDiff, mem_ofPred_eq, Sj, S_trunc]
      rw [hsymm_sec]
      refine (volume_eball_ofReal_symmDiff_le (le_max_right _ _) (le_max_right _ _)).trans ?_
      rw [Real.eNorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal <|
        (abs_max_sub_max_le_abs (w j y - ε) (v y - ε) 0).trans_eq (by rw [sub_sub_sub_cancel_right])
    -- Limit 2: `2 (∫ a j √(d j))² → 4 |A|²`.
    have ha_sq_lim : Tendsto (fun j ↦ ENNReal.ofReal (2 * (∫ y : H, a j y * √(d j y)) ^ 2))
        atTop (𝓝 (4 * volume A ^ 2)) := by
      have hreal : Tendsto (fun j ↦ 2 * (∫ y : H, a j y * √(d j y)) ^ 2) atTop
          (𝓝 (4 * volume.real A ^ 2)) := by
        have := ((tendsto_integral_mul_sqrt_normed_convolution hρ_lim hA hD hAfin hDfin hAD).pow
          2).const_mul 2
        rwa [show 2 * (√2 * volume.real A) ^ 2 = 4 * volume.real A ^ 2 by
          rw [mul_pow, Real.sq_sqrt zero_le_two]; ring] at this
      simpa only [hA_ofReal] using ENNReal.tendsto_ofReal hreal
    -- Limit 3: `limsup ∫ |2 · 1_{Ej j} - d j| ≤ 2 |D \ Eε|`.
    have hEε_sub_D : Eε ⊆ D := fun y (hy : ε < v y) ↦ by
      change 0 < volume {t : ℝ | (y : E) + t • e ∈ s}
      exact pos_iff_ne_zero.2 fun h0 ↦ (hε.trans hy).ne' (by simp [v, measureReal_def, h0])
    have herr_upper (j : ℕ) :
        ∫ y : H, |fEj j y - d j y| ≤
          2 * volume.real (Ej j ∆ Eε) + 2 * volume.real (D \ Eε) + ∫ y : H, |fD y - d j y| := by
      have hfEj_int : Integrable (fEj j) volume :=
        (integrableOn_const (hEj_fin j)).integrable_indicator (hEj_m j)
      have hfEε_int : Integrable fEε volume :=
        (integrableOn_const (ne_top_of_le_ne_top hDfin
          (measure_mono hEε_sub_D))).integrable_indicator₀ hEε_nm
      have hi1 : Integrable (fun y : H ↦ |fEj j y - fEε y|) volume := (hfEj_int.sub hfEε_int).abs
      have hi2 : Integrable (fun y : H ↦ |fEε y - fD y|) volume := (hfEε_int.sub hD_ind_int).abs
      have hi12 : Integrable (fun y : H ↦ |fEj j y - fEε y| + |fEε y - fD y|) volume := hi1.add hi2
      have hi3 : Integrable (fun y : H ↦ |fD y - d j y|) volume := (hD_ind_int.sub (hd_int j)).abs
      have hI1 : ∫ y : H, |fEj j y - fEε y| = 2 * volume.real (Ej j ∆ Eε) := by
        rw [show (fun y : H ↦ |fEj j y - fEε y|) = (Ej j ∆ Eε).indicator (fun _ ↦ (2 : ℝ)) from
            funext fun y ↦ by by_cases h1 : y ∈ Ej j <;> by_cases h2 : y ∈ Eε <;>
              simp [fEj, fEε, Set.mem_symmDiff, h1, h2],
          integral_indicator₀ ((hEj_m j).nullMeasurableSet.symmDiff hEε_nm),
          setIntegral_const, smul_eq_mul, mul_comm]
      have hI2 : ∫ y : H, |fEε y - fD y| = 2 * volume.real (D \ Eε) := by
        rw [show (fun y : H ↦ |fEε y - fD y|) = (D \ Eε).indicator (fun _ ↦ (2 : ℝ)) from
            funext fun y ↦ by by_cases h1 : y ∈ Eε <;> by_cases h2 : y ∈ D <;>
              first | exact absurd (hEε_sub_D h1) h2 | simp [fEε, fD, h1, h2],
          integral_indicator₀ (hD.diff hEε_nm), setIntegral_const, smul_eq_mul, mul_comm]
      calc ∫ y : H, |fEj j y - d j y|
          ≤ ∫ y : H, (|fEj j y - fEε y| + |fEε y - fD y| + |fD y - d j y|) :=
            integral_mono (hfEj_int.sub (hd_int j)).abs (hi12.add hi3) fun y ↦ by
              linarith [abs_sub_le (fEj j y) (fEε y) (d j y), abs_sub_le (fEε y) (fD y) (d j y)]
        _ = _ := by rw [integral_add hi12 hi3, integral_add hi1 hi2, hI1, hI2]
    have herr_lim : Tendsto (fun j ↦ ENNReal.ofReal (M * (2 * volume.real (Ej j ∆ Eε) +
        2 * volume.real (D \ Eε) + ∫ y : H, |fD y - d j y|)))
        atTop (𝓝 (ENNReal.ofReal (M * (2 * volume.real (D \ Eε))))) := by
      have hsymm_real : Tendsto (fun j ↦ volume.real (Ej j ∆ Eε)) atTop (𝓝 0) := by
        simpa only [Function.comp_def, measureReal_def, ENNReal.toReal_zero] using
          (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
            (tendsto_measure_setOf_lt_symmDiff hv_int (fun j ↦ (hw_int j).aestronglyMeasurable)
              (tendsto_lintegral_enorm_normed_convolution_sub hρ_lim hv_int) hε hlevel)
      have hd_L1 : Tendsto (fun j ↦ ∫ y : H, |fD y - d j y|) atTop (𝓝 0) :=
        (tendsto_integral_abs_normed_convolution_sub hρ_lim hD_ind_int).congr
          fun j ↦ integral_congr_ae (.of_forall fun _ ↦ abs_sub_comm _ _)
      refine ENNReal.tendsto_ofReal (Tendsto.const_mul M ?_)
      simpa only [mul_zero, zero_add, add_zero] using
        ((hsymm_real.const_mul 2).add tendsto_const_nhds).add hd_L1
    exact mul_add_le_of_le_liminf
      (perimeter_le_liminf_of_tendsto_symmDiff hSj_nm (hS_trunc_nm ε) hSj_lim)
      ha_sq_lim.liminf_eq.ge
      (fun j ↦ (hper_j j).trans (by gcongr; exact herr_upper j)) (herr_lim.const_add _)
  -- Step 2: Choose `ε k ∈ (0, 1 / (k + 1))` with `volume {v = ε k} = 0` and let `k → ∞`.
  have hcount : {t : ℝ | 0 < volume {y : H | v y = t}}.Countable :=
    Measure.countable_meas_level_set_pos₀ hv_int.aestronglyMeasurable.aemeasurable.nullMeasurable
  have hex_eps (k : ℕ) : ∃ ε ∈ Ioo (0 : ℝ) (1 / ((k : ℝ) + 1)), volume {y : H | v y = ε} = 0 := by
    obtain ⟨ε, hεI, hε0⟩ :
        (Ioo (0 : ℝ) (1 / ((k : ℝ) + 1)) \ {t : ℝ | 0 < volume {y : H | v y = t}}).Nonempty :=
      Set.nonempty_iff_ne_empty.2 fun hempty ↦ by
        have h0 := measure_mono_null (Set.sdiff_eq_empty.1 hempty) (hcount.measure_zero volume)
        rw [Real.volume_Ioo, sub_zero] at h0
        exact (ENNReal.ofReal_pos.2 (by positivity)).ne' h0
    exact ⟨ε, hεI, nonpos_iff_eq_zero.1 (not_lt.1 hε0)⟩
  choose ε hε_mem hε_level using hex_eps
  have hε_lim : Tendsto ε atTop (𝓝 0) :=
    squeeze_zero (fun k ↦ (hε_mem k).1.le) (fun k ↦ (hε_mem k).2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hS_lim : Tendsto (fun k ↦ volume (S_trunc (ε k) ∆ steinerSymmetrization e he s))
      atTop (𝓝 0) := by
    have hdom : Tendsto (fun k ↦ ∫⁻ y : H, ENNReal.ofReal (min (v y) (ε k))) atTop (𝓝 0) := by
      rw [← lintegral_zero (μ := (volume : Measure H))]
      refine tendsto_lintegral_of_dominated_convergence' (fun y ↦ ENNReal.ofReal (v y))
        (fun k ↦ (hv_int.aestronglyMeasurable.aemeasurable.min aemeasurable_const).ennreal_ofReal)
        (fun k ↦ .of_forall fun y ↦ ENNReal.ofReal_le_ofReal (min_le_left _ _))
        (ne_top_of_le_ne_top hv_int.2.ne (lintegral_mono fun y ↦ by
          rw [Real.eNorm_of_nonneg measureReal_nonneg]))
        (.of_forall fun y ↦ by
          simpa only [ENNReal.ofReal_zero,
            min_eq_right (show (0 : ℝ) ≤ v y from measureReal_nonneg)] using
            ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := v y)).min hε_lim))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdom (fun _ ↦ zero_le)
      fun k ↦ ?_
    rw [volume_eq_lintegral_volume_lineSection e he
      ((hS_trunc_nm (ε k)).symmDiff (nullMeasurableSet_steinerSymmetrization e he hs))]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_volume_lineSection_lt_top e he hs hfin] with y hyfin
    have hsymm_sec : {t : ℝ | (y : E) + t • e ∈ S_trunc (ε k) ∆ steinerSymmetrization e he s} =
        Metric.eball (0 : ℝ) (ENNReal.ofReal (max (v y - ε k) 0) / 2) ∆
          Metric.eball (0 : ℝ) (ENNReal.ofReal (v y) / 2) := by
      rw [← lineSection_symmetricSubgraph_eq e he v (ε k) y,
        show ENNReal.ofReal (v y) = volume {t : ℝ | (y : E) + t • e ∈ s} from
          ofReal_measureReal hyfin.ne, ← lineSection_steinerSymmetrization e he]
      ext t; simp only [Set.mem_symmDiff, mem_ofPred_eq, S_trunc]
    rw [hsymm_sec]
    refine (volume_eball_ofReal_symmDiff_le (le_max_right _ _) measureReal_nonneg).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rcases le_total (v y) (ε k) with hle | hge
    · rw [max_eq_right (sub_nonpos.2 hle), zero_sub, abs_neg, abs_of_nonneg measureReal_nonneg,
        min_eq_left hle]
    · rw [max_eq_left (sub_nonneg.2 hge), sub_sub_cancel_left, abs_neg,
        abs_of_pos (hε_mem k).1, min_eq_right hge]
  have hDdiff_lim : Tendsto (fun k ↦ volume (D \ {y : H | ε k < v y})) atTop (𝓝 0) := by
    have hvpos_fin : volume {y : H | 0 < v y} ≠ ∞ :=
      ne_top_of_le_ne_top hDfin <| measure_mono fun y (hy : 0 < v y) ↦ by
        change 0 < volume {t : ℝ | (y : E) + t • e ∈ s}
        exact pos_iff_ne_zero.2 fun h0 ↦ hy.ne' (by simp [v, measureReal_def, h0])
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_measure_setOf_pos_le_one_div hv_int.aestronglyMeasurable.aemeasurable hvpos_fin)
      (fun _ ↦ zero_le) fun k ↦ measure_mono_ae ?_
    filter_upwards [ae_volume_lineSection_lt_top e he hs hfin] with y hyfin ⟨hyD, hnot⟩
    exact ⟨ENNReal.toReal_pos hyD.ne' hyfin.ne, (not_lt.1 hnot).trans (hε_mem k).2.le⟩
  have hDdiff_rhs : Tendsto (fun k ↦ ENNReal.ofReal M * perimeter volume ⊤ s +
      ENNReal.ofReal (M * (2 * volume.real (D \ {y : H | ε k < v y}))))
      atTop (𝓝 (ENNReal.ofReal M * perimeter volume ⊤ s)) := by
    have hreal : Tendsto (fun k ↦ volume.real (D \ {y : H | ε k < v y})) atTop (𝓝 0) := by
      simpa only [Function.comp_def, measureReal_def, ENNReal.toReal_zero] using
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hDdiff_lim
    simpa only [mul_zero, ENNReal.ofReal_zero, add_zero] using
      (ENNReal.tendsto_ofReal ((hreal.const_mul 2).const_mul M)).const_add
        (ENNReal.ofReal M * perimeter volume ⊤ s)
  rw [← hM_ofReal]
  exact mul_add_le_of_le_liminf
    (perimeter_le_liminf_of_tendsto_symmDiff (fun k ↦ hS_trunc_nm (ε k))
      (nullMeasurableSet_steinerSymmetrization e he hs) hS_lim)
    (liminf_const _).ge (fun k ↦ hstep_eps (hε_mem k).1 (hε_level k)) hDdiff_rhs

/-- **Coordinate-free quantitative Steiner perimeter excess inequality.** For a Lebesgue-measurable
set `s` of finite volume, a unit vector `e`, and a null-measurable family `A ⊆ (ℝ ∙ e)ᗮ` of
noninterval line sections of `s`,

`P(s) P(S_e s) + 2 |A|² ≤ P(s)²`.

This holds whether `P(s)` is finite or infinite, in every positive dimension. -/
theorem perimeter_mul_perimeter_steinerSymmetrization_add_two_mul_sq_le
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (e : E) (he : ‖e‖ = 1) {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) :
    perimeter volume ⊤ s * perimeter volume ⊤ (steinerSymmetrization e he s) +
        2 * volume A ^ 2 ≤
      perimeter volume ⊤ s ^ 2 := by
  by_cases hP : perimeter volume ⊤ s = ∞
  · rw [hP, ENNReal.top_pow two_ne_zero]; exact le_top
  set P := perimeter volume ⊤ s
  set PS := perimeter volume ⊤ (steinerSymmetrization e he s)
  set D : Set (ℝ ∙ e)ᗮ := {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  set v : (ℝ ∙ e)ᗮ → ℝ := fun y ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s}
  set M := 2 * volume D + totalVariationOn volume ⊤ v
  have hDA_le := two_mul_volume_add_two_mul_volume_le_perimeter_of_noninterval_lineSection
    hs hfin e he hA hbad
  have hM_le : M ≤ 2 * P := by
    rw [two_mul]
    exact add_le_add (le_self_add.trans hDA_le)
      (totalVariationOn_measureReal_lineSection_le hs hfin e he)
  have hM_fin : M ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) hP) hM_le
  have hPS_le : PS ≤ P := perimeter_steinerSymmetrization_le e he hs hfin
  have hPS_fin : PS ≠ ∞ := ne_top_of_le_ne_top hP hPS_le
  have hAfin : volume A ≠ ∞ := ne_top_of_le_ne_top hP <|
    (le_self_add.trans_eq (two_mul _).symm).trans (le_add_self.trans hDA_le)
  have hreal : M.toReal * PS.toReal + 4 * volume.real A ^ 2 ≤ M.toReal * P.toReal := by
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top hM_fin hP)
      (mul_perimeter_steinerSymmetrization_add_four_mul_sq_le hs hfin e he hA hbad)
    rwa [ENNReal.toReal_add (ENNReal.mul_ne_top hM_fin hPS_fin)
        (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hAfin)),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_pow] at h1
  have hM_le_real : M.toReal ≤ 2 * P.toReal := by
    simpa [ENNReal.toReal_mul] using ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hP) hM_le
  have hPS_le_real : PS.toReal ≤ P.toReal := ENNReal.toReal_mono hP hPS_le
  have hfinal_real : P.toReal * PS.toReal + 2 * volume.real A ^ 2 ≤ P.toReal ^ 2 := by
    nlinarith [ENNReal.toReal_nonneg (a := P), ENNReal.toReal_nonneg (a := PS),
      ENNReal.toReal_nonneg (a := M)]
  calc P * PS + 2 * volume A ^ 2
      = ENNReal.ofReal (P.toReal * PS.toReal + 2 * volume.real A ^ 2) := by
        rw [ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
            (by positivity),
          ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hP,
          ENNReal.ofReal_toReal hPS_fin, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
          ENNReal.ofReal_pow measureReal_nonneg, ofReal_measureReal hAfin]
    _ ≤ ENNReal.ofReal (P.toReal ^ 2) := ENNReal.ofReal_le_ofReal hfinal_real
    _ = P ^ 2 := by rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hP]

/-- **Equality in Steiner's perimeter inequality forces interval sections.** Let `s` be a
Lebesgue-measurable set of finite volume and finite perimeter, and let `e` be a unit vector. If
the Steiner symmetral of `s` along `e` has the same perimeter as `s`, then almost every line
section of `s` parallel to `e` agrees almost everywhere with an interval. -/
theorem ae_exists_ordConnected_lineSection_of_perimeter_steinerSymmetrization_eq
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞) (e : E) (he : ‖e‖ = 1)
    (heq : perimeter volume ⊤ (steinerSymmetrization e he s) = perimeter volume ⊤ s) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume,
      ∃ I : Set ℝ, I.OrdConnected ∧ {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I := by
  let A : Set (ℝ ∙ e)ᗮ := {y : (ℝ ∙ e)ᗮ | ∀ I : Set ℝ, I.OrdConnected →
    ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I}
  have hineq := perimeter_mul_perimeter_steinerSymmetrization_add_two_mul_sq_le
    hs hfin e he (nullMeasurableSet_noninterval_lineSection hs hfin e he) (.of_forall fun _ ↦ id)
  rw [heq, ← sq] at hineq
  have hzero : 2 * volume A ^ 2 = 0 := nonpos_iff_eq_zero.1 <|
    WithTop.le_of_add_le_add_left (ENNReal.pow_ne_top hP) (hineq.trans_eq (add_zero _).symm)
  have hA0 : volume A = 0 := by
    simpa [sq] using (mul_eq_zero.1 hzero).resolve_left (by norm_num)
  rw [ae_iff]
  simpa [A] using hA0

end Main

end TauCeti

end
