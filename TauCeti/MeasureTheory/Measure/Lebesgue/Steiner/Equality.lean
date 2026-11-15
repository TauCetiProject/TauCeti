/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Covering.EssentialBoundary
public import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Perimeter
public import TauCeti.Analysis.BoundedVariation.LebesgueDecomposition
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import TauCeti.Analysis.BoundedVariation.Real
import TauCeti.Analysis.BoundedVariation.Slicing.Excess
import TauCeti.Analysis.BoundedVariation.Slicing.Measurability
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Distribution.TestFunction.Divergence
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.Analysis.Distribution.TestFunction.Lp
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Rigidity of line sections for equality in Steiner's perimeter inequality

Let `s` be a Lebesgue-measurable set of finite volume and finite perimeter in a finite-dimensional
real inner product space `E`, and let `e` be a unit vector with orthogonal hyperplane `(ℝ ∙ e)ᗮ`.
Steiner symmetrization in direction `e` preserves the section-length profile
`ℓ(y) = |{t : ℝ | y + t • e ∈ s}|` and does not increase perimeter
(`TauCeti.perimeter_steinerSymmetrization_le`). When `perimeter volume ⊤ s ≠ ∞`, `ℓ` is an
integrable function of bounded variation on `(ℝ ∙ e)ᗮ`.

Writing `g` for the absolutely continuous derivative density of `ℓ` on `(ℝ ∙ e)ᗮ`, this file proves
a quantitative localized refinement of Steiner's perimeter inequality
(`TauCeti.perimeter_steinerSymmetrization_add_ofReal_setIntegral_le`): for every null-measurable
family `A ⊆ (ℝ ∙ e)ᗮ` of noninterval sections of `s`,

`P(S_e s) + ∫_A 4 / √(4 + ‖g(y)‖²) dy ≤ P(s)`.

In particular, if `P(S_e s) = P(s) < ∞`, then `A` must be null: for almost every `y ∈ (ℝ ∙ e)ᗮ`,
the parallel line section `{t : ℝ | y + t • e ∈ s}` agrees almost everywhere with an interval
(`TauCeti.ae_lineSection_ordConnected_of_perimeter_steinerSymmetrization_eq`), and therefore has at
most two essential boundary points
(`TauCeti.ae_encard_essentialBoundary_lineSection_le_two_of_perimeter_steinerSymmetrization_eq`,
`TauCeti.volume_setOf_two_lt_encard_essentialBoundary_lineSection_eq_zero`). Note that interval
sections in a single direction are necessary but not sufficient for `P(S_e s) = P(s)`: a sheared
parallelogram has interval sections everywhere while symmetrization strictly decreases its
perimeter by centering the section midpoints.

## Proof outline

1. **Upper bound for `P(S_e s)` via smoothed subgraphs.** Mollifying `ℓ` with normalized shrinking
   smooth bumps produces smooth nonnegative profiles `m_n → ℓ` in `L¹((ℝ ∙ e)ᗮ)` whose centered
   open subgraphs `{|⟪e, x⟫| < m_n(π x) / 2}` converge in `L¹(E)` to `S_e s`. Integration by parts
   on each smooth subgraph expresses `∫ div ψ` for a norm-at-most-one test field `ψ` as a boundary
   integral bounded pointwise using `TauCeti.norm_fderiv_convolution_lsmul_top_le`. Letting
   `n → ∞` bounds `P(S_e s)` above by a variational functional of `Dℓ`.
2. **Lower bound for `P(s)` with noninterval excess.** Testing the localized slicing inequality
   `TauCeti.two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter` against
   smooth norm-at-most-one approximations to the optimal Borel vector field aligning with
   `-g / √(4 + ‖g‖²)` on `{ℓ > 0}`, with `-g / ‖g‖` on `{ℓ = 0}`, and with the polar density on
   the singular set of `|Dℓ|` recovers the same variational functional plus
   `∫_A 4 / √(4 + ‖g(y)‖²) dy`.

## References

* M. Chlebík, A. Cianchi, N. Fusco, *The perimeter inequality under Steiner symmetrization: cases
  of equality*, Ann. of Math. (2) **162** (2005), 525–555.
* F. Cagnetti, M. Colombo, G. De Philippis, F. Maggi, *Rigidity of equality cases in Steiner's
  perimeter inequality*, Anal. PDE **7** (2014), 1677–1737, §1.2 and Theorem A.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, Chapter 14 (Theorem 14.4).
-/

public noncomputable section

open MeasureTheory Metric Filter Set TopologicalSpace TestFunction ContinuousLinearMap
open scoped ENNReal Topology Convolution Distributions LineDeriv RealInnerProductSpace symmDiff

namespace TauCeti

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Decompose a vector along a unit vector `e` and an orthonormal basis of `(ℝ ∙ e)ᗮ`. -/
private theorem eq_inner_smul_add_sum_orthogonal (e : E) (he : ‖e‖ = 1) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (ℝ ∙ e)ᗮ) (w : E) :
    w = ⟪e, w⟫ • e + ∑ i, ⟪(b i : E), w⟫ • (b i : E) := by
  set p : (ℝ ∙ e)ᗮ := ((orthogonalLineEquiv e he).symm w).1
  have hp : (p : E) = w - ⟪e, w⟫ • e := orthogonalLineEquiv_symm_fst e he w
  have hsum : ∑ i, ⟪b i, p⟫ • (b i : E) = (p : E) := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, OrthonormalBasis.repr_apply_apply]
      using congrArg (Subtype.val : (ℝ ∙ e)ᗮ → E) (b.sum_repr p)
  have hbi (i) : ⟪(b i : E), w⟫ = ⟪b i, p⟫ := by
    have h0 : ⟪(b i : E), e⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.1 (b i).2
    rw [Submodule.coe_inner, hp, inner_sub_right, inner_smul_right, h0, mul_zero, sub_zero]
  simp_rw [hbi, hsum, hp, add_sub_cancel]

/-- Expand the divergence of a test vector field along `e` and an orthonormal basis of
`(ℝ ∙ e)ᗮ`. -/
private theorem divergenceCLM_eq_lineDeriv_add_sum [FiniteDimensional ℝ E] (e : E) (he : ‖e‖ = 1)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ (ℝ ∙ e)ᗮ)) ℝ (ℝ ∙ e)ᗮ) (ψ : 𝓓(⊤, E)) (x : E) :
    divergenceCLM ψ x =
      lineDeriv ℝ (fun z => ⟪e, ψ z⟫) x e +
        ∑ i, lineDeriv ℝ (fun z => ⟪(b i : E), ψ z⟫) x (b i : E) := by
  let ψe : 𝓓(⊤, ℝ) := postcompCLM (innerSL ℝ e) ψ
  let ψi (i) : 𝓓(⊤, ℝ) := postcompCLM (innerSL ℝ (b i : E)) ψ
  let evE (z : E) : 𝓓(⊤, E) →+ E := AddMonoidHom.mk' (fun Φ => Φ z) fun _ _ => rfl
  let evR (z : E) : 𝓓(⊤, ℝ) →+ ℝ := AddMonoidHom.mk' (fun Φ => Φ z) fun _ _ => rfl
  have hψ : ψ = postcompCLM (toSpanSingleton ℝ e) ψe +
      ∑ i, postcompCLM (toSpanSingleton ℝ (b i : E)) (ψi i) := by
    ext z
    have hcoe := (map_add (evE z) (postcompCLM (toSpanSingleton ℝ e) ψe)
      (∑ i, postcompCLM (toSpanSingleton ℝ (b i : E)) (ψi i))).trans <|
      congrArg _ (map_sum (evE z) _ _)
    simp only [evE, AddMonoidHom.mk'_apply, postcompCLM_apply, Function.comp_apply,
      toSpanSingleton_apply, innerSL_apply_apply, ψe, ψi] at hcoe
    exact (eq_inner_smul_add_sum_orthogonal e he b (ψ z)).trans hcoe.symm
  have hdiv : divergenceCLM ψ = ∂_{e} ψe + ∑ i, ∂_{(b i : E)} (ψi i) := by
    rw [hψ, map_add, map_sum]
    simp only [divergenceCLM_postcompCLM_toSpanSingleton]
  have hx := (congrArg (evR x) hdiv).trans <|
    (map_add (evR x) _ _).trans <| congrArg _ (map_sum (evR x) _ _)
  simp only [evR, AddMonoidHom.mk'_apply, lineDerivOp_eq_lineDerivCLM ℝ,
    lineDerivCLM_apply_of_le le_top, ψe, ψi, postcompCLM_apply, Function.comp_def,
    innerSL_apply_apply] at hx
  exact hx

/-- Expand `L (((orthogonalLineEquiv e he).symm w).1)` in an orthonormal basis of `(ℝ ∙ e)ᗮ`. -/
private theorem sum_apply_mul_inner_eq_apply_fst (e : E) (he : ‖e‖ = 1) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (ℝ ∙ e)ᗮ) (L : (ℝ ∙ e)ᗮ →L[ℝ] ℝ) (w : E) :
    ∑ i, L (b i) * ⟪(b i : E), w⟫ = L (((orthogonalLineEquiv e he).symm w).1) := by
  set p : (ℝ ∙ e)ᗮ := ((orthogonalLineEquiv e he).symm w).1
  have hp : (p : E) = w - ⟪e, w⟫ • e := orthogonalLineEquiv_symm_fst e he w
  have hbi (i) : ⟪(b i : E), w⟫ = ⟪b i, p⟫ := by
    have h0 : ⟪(b i : E), e⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.1 (b i).2
    rw [Submodule.coe_inner, hp, inner_sub_right, inner_smul_right, h0, mul_zero, sub_zero]
  conv_rhs => rw [← b.sum_repr p]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hbi, b.repr_apply_apply, map_smul, smul_eq_mul, mul_comm]

/-- Pointwise Cauchy–Schwarz bound for the boundary flux integrand on a smooth subgraph. -/
private theorem flux_integrand_le_sqrt (e : E) (he : ‖e‖ = 1) {w₁ w₂ : E}
    (hw₁ : ‖w₁‖ ≤ 1) (hw₂ : ‖w₂‖ ≤ 1) (L : (ℝ ∙ e)ᗮ →L[ℝ] ℝ) :
    ⟪e, w₁⟫ - ⟪e, w₂⟫ - L (((orthogonalLineEquiv e he).symm ((2 : ℝ)⁻¹ • (w₁ + w₂))).1) ≤
      √(4 + ‖L‖ ^ 2) := by
  have half_bound (w : E) (hw : ‖w‖ ≤ 1) :
      2 * |⟪e, w⟫| + ‖L‖ * ‖((orthogonalLineEquiv e he).symm w).1‖ ≤ √(4 + ‖L‖ ^ 2) := by
    set p := ((orthogonalLineEquiv e he).symm w).1
    set c := ⟪e, w⟫
    have hw_eq : (p : E) + c • e = w := by rw [orthogonalLineEquiv_symm_fst, sub_add_cancel]
    have hnorm : ‖p‖ ^ 2 + c ^ 2 ≤ 1 := by
      have h1 : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
      rwa [← hw_eq, norm_add_smul_sq e he] at h1
    have hsq : (2 * |c| + ‖L‖ * ‖p‖) ^ 2 ≤ 4 + ‖L‖ ^ 2 := by
      nlinarith [sq_nonneg (‖L‖ * |c| - 2 * ‖p‖), sq_abs c, norm_nonneg L, norm_nonneg p]
    exact (Real.sqrt_sq (by positivity)).symm.trans_le (Real.sqrt_le_sqrt hsq)
  set p₁ := ((orthogonalLineEquiv e he).symm w₁).1
  set p₂ := ((orthogonalLineEquiv e he).symm w₂).1
  have hmid : ((orthogonalLineEquiv e he).symm ((2 : ℝ)⁻¹ • (w₁ + w₂))).1 =
      (2 : ℝ)⁻¹ • (p₁ + p₂) := by
    rw [map_smul, map_add, Prod.smul_fst, Prod.fst_add]
  have hL : -L (((orthogonalLineEquiv e he).symm ((2 : ℝ)⁻¹ • (w₁ + w₂))).1) ≤
      ‖L‖ * ((‖p₁‖ + ‖p₂‖) / 2) := by
    rw [hmid, map_smul, smul_eq_mul]
    calc -(2⁻¹ * L (p₁ + p₂)) ≤ |2⁻¹ * L (p₁ + p₂)| := neg_le_abs _
      _ = 2⁻¹ * |L (p₁ + p₂)| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
      _ ≤ 2⁻¹ * (‖L‖ * ‖p₁ + p₂‖) := by gcongr; exact L.le_opNorm _
      _ ≤ 2⁻¹ * (‖L‖ * (‖p₁‖ + ‖p₂‖)) := by gcongr; exact norm_add_le _ _
      _ = ‖L‖ * ((‖p₁‖ + ‖p₂‖) / 2) := by ring
  have h1 : ⟪e, w₁⟫ - ⟪e, w₂⟫ ≤ |⟪e, w₁⟫| + |⟪e, w₂⟫| := by
    linarith [le_abs_self ⟪e, w₁⟫, neg_le_abs ⟪e, w₂⟫]
  linarith [half_bound w₁ hw₁, half_bound w₂ hw₂]

/-- Subadditivity of `u ↦ √(4 + u²)` with respect to nonnegative perturbations. -/
private theorem sqrt_four_add_sq_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    √(4 + (a + b) ^ 2) ≤ √(4 + a ^ 2) + b := by
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have ha' : a ≤ √(4 + a ^ 2) :=
    (Real.sqrt_sq ha).symm.trans_le (Real.sqrt_le_sqrt (by linarith))
  have h4a : 0 ≤ 4 + a ^ 2 := by positivity
  nlinarith [Real.sq_sqrt h4a]

/-- `u ↦ √(4 + u²)` is `1`-Lipschitz on `[0, ∞)`. -/
private theorem abs_sqrt_four_add_sq_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |√(4 + a ^ 2) - √(4 + b ^ 2)| ≤ |a - b| := by
  wlog hab : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a b]
    exact this hb ha (le_of_not_ge hab)
  have h1 : √(4 + b ^ 2) ≤ √(4 + a ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have h2 : √(4 + a ^ 2) ≤ √(4 + b ^ 2) + (a - b) := by
    simpa [add_sub_cancel] using sqrt_four_add_sq_add_le hb (sub_nonneg.2 hab)
  rw [abs_of_nonneg (sub_nonneg.2 h1), abs_of_nonneg (sub_nonneg.2 hab)]
  linarith

/-- Symmetric difference of two centered open intervals on `ℝ` has measure `‖a - b‖ₑ`. -/
private theorem lintegral_enorm_indicator_Ioo_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫⁻ t : ℝ, ‖(Ioo (-a / 2) (a / 2)).indicator (1 : ℝ → ℝ) t -
      (Ioo (-b / 2) (b / 2)).indicator 1 t‖ₑ) ≤ ‖a - b‖ₑ := by
  wlog hab : a ≤ b generalizing a b
  · simp_rw [← eNorm_neg (_ - _), neg_sub]
    exact this hb ha (le_of_not_ge hab)
  have hsub : Ioo (-a / 2) (a / 2) ⊆ Ioo (-b / 2) (b / 2) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hpt (t : ℝ) : ‖(Ioo (-a / 2) (a / 2)).indicator (1 : ℝ → ℝ) t -
      (Ioo (-b / 2) (b / 2)).indicator 1 t‖ₑ =
      (Ioo (-b / 2) (b / 2) \ Ioo (-a / 2) (a / 2)).indicator 1 t := by
    by_cases hta : t ∈ Ioo (-a / 2) (a / 2)
    · simp [hta, hsub hta]
    · by_cases htb : t ∈ Ioo (-b / 2) (b / 2) <;> simp [hta, htb]
  simp_rw [hpt]
  rw [lintegral_indicator_one (measurableSet_Ioo.diff measurableSet_Ioo),
    measure_sdiff hsub measurableSet_Ioo.nullMeasurableSet
      (by simp [Real.volume_Ioo] : volume (Ioo (-a / 2) (a / 2)) ≠ ∞),
    Real.volume_Ioo, Real.volume_Ioo]
  have h1 : b / 2 - -b / 2 = b := by ring
  have h2 : a / 2 - -a / 2 = a := by ring
  rw [h1, h2, ← ENNReal.ofReal_sub _ ha, Real.eNorm_eq_ofReal_abs, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.2 hab)]

/-- For `a ≥ 0`, the centered extended-radius ball of radius `ENNReal.ofReal a / 2` in `ℝ` is the
open interval `Ioo (-a / 2) (a / 2)`. -/
private theorem eball_zero_ofReal_div_two {a : ℝ} (ha : 0 ≤ a) :
    Metric.eball (0 : ℝ) (ENNReal.ofReal a / 2) = Ioo (-a / 2) (a / 2) := by
  ext t
  rcases eq_or_lt_of_le ha with rfl | hpos
  · simp
  · rw [Metric.mem_eball, edist_zero_right, Real.eNorm_eq_ofReal_abs,
      ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_div_of_pos zero_lt_two,
      ENNReal.ofReal_lt_ofReal_iff (half_pos hpos), abs_lt, neg_div]
    rfl

/-- Outside a transverse closed ball containing `tsupport f`, `f` vanishes along every parallel
line `t ↦ y + t • e`. -/
private theorem apply_add_smul_eq_zero_of_tsupport_subset_closedBall {V : Type*}
    [AddCommMonoid V] (e : E) (he : ‖e‖ = 1) {f : E → V} {R₀ : ℝ}
    (hR₀ : tsupport f ⊆ closedBall 0 R₀) {y : (ℝ ∙ e)ᗮ}
    (hy : y ∉ closedBall (0 : (ℝ ∙ e)ᗮ) (max R₀ 0)) (t : ℝ) :
    f ((y : E) + t • e) = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  rw [mem_closedBall_zero_iff, not_le] at hy
  have hle : ‖(y : E) + t • e‖ ≤ max R₀ 0 :=
    (mem_closedBall_zero_iff.1 (hR₀ hmem)).trans (le_max_left _ _)
  have hsq : ‖(y : E) + t • e‖ ^ 2 ≤ max R₀ 0 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hgt : max R₀ 0 ^ 2 < ‖y‖ ^ 2 := pow_lt_pow_left₀ hy (le_max_right _ _) two_ne_zero
  linarith [norm_add_smul_sq e he y t, sq_nonneg t]

end Helpers

section SubgraphIBP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Centered open symmetric subgraph in direction `e` with section-length profile `m`. -/
private def symmetricSubgraph (e : E) (he : ‖e‖ = 1) (m : (ℝ ∙ e)ᗮ → ℝ) : Set E :=
  {x | ((orthogonalLineEquiv e he).symm x).2 ∈
    Ioo (-m ((orthogonalLineEquiv e he).symm x).1 / 2)
      (m ((orthogonalLineEquiv e he).symm x).1 / 2)}

omit [FiniteDimensional ℝ E] in
private theorem measurableSet_symmetricSubgraph (e : E) (he : ‖e‖ = 1) {m : (ℝ ∙ e)ᗮ → ℝ}
    (hm : Continuous m) : MeasurableSet (symmetricSubgraph e he m) :=
  (measurableSet_lt ((hm.neg.div_const 2).comp
    (orthogonalLineEquiv e he).symm.continuous.fst).measurable
    (orthogonalLineEquiv e he).symm.continuous.snd.measurable).inter
    (measurableSet_lt (orthogonalLineEquiv e he).symm.continuous.snd.measurable
      ((hm.div_const 2).comp (orthogonalLineEquiv e he).symm.continuous.fst).measurable)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem mem_symmetricSubgraph_add_smul (e : E) (he : ‖e‖ = 1) (m : (ℝ ∙ e)ᗮ → ℝ)
    (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    (y : E) + t • e ∈ symmetricSubgraph e he m ↔ t ∈ Ioo (-m y / 2) (m y / 2) := by
  rw [← orthogonalLineEquiv_apply e he y t, symmetricSubgraph, mem_ofPred_eq,
    ContinuousLinearEquiv.symm_apply_apply]

/-- Parametric line integral `(y, a) ↦ ∫ τ in 0..1, a * F (y + (a * τ) • e)`. -/
private def parametricLineIntegral (e : E) (F : E → ℝ) (p : (ℝ ∙ e)ᗮ × ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..1, p.2 * F ((p.1 : E) + (p.2 * τ) • e)

private theorem continuous_lineDeriv_add_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : V → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x d w : V) :
    Continuous (fun t : ℝ => lineDeriv ℝ F (x + t • d) w) := by
  have heq : (fun t : ℝ => lineDeriv ℝ F (x + t • d) w) = fun t => fderiv ℝ F (x + t • d) w :=
    funext fun _ => (hF.differentiable (by simp) _).lineDeriv_eq_fderiv
  rw [heq]
  exact ((hF.continuous_fderiv (by simp)).comp
    (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Differentiating the parametric integral `G(y, a) = ∫ t in 0..a, F(y + t • e)` on
`(ℝ ∙ e)ᗮ × ℝ`. -/
private theorem fderiv_parametric_line_integral_apply (e : E) {F : E → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (y v : (ℝ ∙ e)ᗮ) (a c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (parametricLineIntegral e F) ∧
      parametricLineIntegral e F (y, a) = (∫ t in (0 : ℝ)..a, F ((y : E) + t • e)) ∧
      (fderiv ℝ (parametricLineIntegral e F) (y, a)) (v, c) =
        (∫ t in (0 : ℝ)..a, lineDeriv ℝ F ((y : E) + t • e) (v : E)) +
          c * F ((y : E) + a • e) := by
  have hG : ContDiff ℝ (⊤ : ℕ∞) (parametricLineIntegral e F) :=
    (contDiff_fst.snd.mul (hF.comp (((ℝ ∙ e)ᗮ.subtypeL.contDiff.comp contDiff_fst.fst).add
      ((contDiff_fst.snd.mul contDiff_snd).smul contDiff_const)))).parametric_intervalIntegral
  have hGeq (z : (ℝ ∙ e)ᗮ) (b : ℝ) :
      parametricLineIntegral e F (z, b) = ∫ t in (0 : ℝ)..b, F ((z : E) + t • e) := by
    dsimp only [parametricLineIntegral]
    rw [intervalIntegral.integral_const_mul, ← smul_eq_mul,
      intervalIntegral.smul_integral_comp_mul_left (f := fun s => F ((z : E) + s • e)),
      mul_zero, mul_one]
  refine ⟨hG, hGeq y a, ?_⟩
  have hGd : DifferentiableAt ℝ (parametricLineIntegral e F) (y, a) :=
    hG.differentiable (by simp) (y, a)
  have hsplit : (v, c) = (v, (0 : ℝ)) + c • ((0 : (ℝ ∙ e)ᗮ), (1 : ℝ)) := by ext <;> simp
  -- Differentiate with respect to the transverse variable `y` under the integral sign.
  have hp1 : (fderiv ℝ (parametricLineIntegral e F) (y, a)) (v, 0) =
      ∫ t in (0 : ℝ)..a, lineDeriv ℝ F ((y : E) + t • e) (v : E) := by
    have hγ : HasDerivAt (fun s : ℝ => (y + s • v, a)) (v, 0) 0 := by
      simpa using ((((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const v).const_add y).prodMk
        (hasFDerivAt_const (𝕜 := ℝ) a (0 : ℝ))).hasDerivAt
    have hGd0 : HasFDerivAt (parametricLineIntegral e F)
        (fderiv ℝ (parametricLineIntegral e F) (y, a)) (y + (0 : ℝ) • v, a) := by
      simpa using hGd.hasFDerivAt
    have hcomp : HasDerivAt (fun s : ℝ => parametricLineIntegral e F (y + s • v, a))
        ((fderiv ℝ (parametricLineIntegral e F) (y, a)) (v, 0)) 0 := by
      simpa [Function.comp_def] using hGd0.comp_hasDerivAt 0 hγ
    have hpar : HasDerivAt
        (fun s : ℝ => ∫ t in (0 : ℝ)..a, F ((y : E) + s • (v : E) + t • e))
        ((∫ t in (0 : ℝ)..a,
          fderiv ℝ (fun s : ℝ => F ((y : E) + s • (v : E) + t • e)) 0) 1) 0 :=
      (intervalIntegral.hasFDerivAt_integral_of_contDiffOn (μ := volume) Filter.univ_mem
        ((hF.comp ((contDiff_const.add (contDiff_fst.smul contDiff_const)).add
          (contDiff_snd.smul contDiff_const))).contDiffOn.of_le (by simp))).hasDerivAt
    have hd_t (t : ℝ) :
        fderiv ℝ (fun s : ℝ => F ((y : E) + s • (v : E) + t • e)) 0 =
          ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)
            (lineDeriv ℝ F ((y : E) + t • e) (v : E)) := by
      have hid : HasDerivAt (fun s : ℝ => s • (v : E)) (v : E) 0 := by
        simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const (v : E)
      have hin : HasDerivAt (fun s : ℝ => (y : E) + s • (v : E) + t • e) (v : E) 0 :=
        (hid.const_add (y : E)).add_const (t • e)
      have hF0 : HasFDerivAt F (fderiv ℝ F ((y : E) + t • e))
          ((y : E) + (0 : ℝ) • (v : E) + t • e) := by
        simpa using (hF.differentiable (by simp) ((y : E) + t • e)).hasFDerivAt
      have hdt : HasDerivAt (fun s : ℝ => F ((y : E) + s • (v : E) + t • e))
          (fderiv ℝ F ((y : E) + t • e) (v : E)) 0 := by
        simpa [Function.comp_def] using hF0.comp_hasDerivAt 0 hin
      rw [hdt.hasFDerivAt.fderiv,
        (hF.differentiable (by simp) ((y : E) + t • e)).lineDeriv_eq_fderiv]
      ext; simp
    have hcont : Continuous (fun t : ℝ => lineDeriv ℝ F ((y : E) + t • e) (v : E)) :=
      continuous_lineDeriv_add_smul hF (y : E) e (v : E)
    have hint_eq : (∫ t in (0 : ℝ)..a,
          fderiv ℝ (fun s : ℝ => F ((y : E) + s • (v : E) + t • e)) 0) 1 =
        ∫ t in (0 : ℝ)..a, lineDeriv ℝ F ((y : E) + t • e) (v : E) := by
      simp_rw [hd_t]
      rw [← ContinuousLinearMap.apply_apply (1 : ℝ) (∫ t in (0 : ℝ)..a, _)]
      simpa [Function.comp_def] using
        ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).intervalIntegral_comp_comm
          (((ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous.comp hcont)
            |>.intervalIntegrable 0 a)).symm
    rw [hint_eq] at hpar
    have hfun : (fun s : ℝ => parametricLineIntegral e F (y + s • v, a)) =
        fun s => ∫ t in (0 : ℝ)..a, F ((y : E) + s • (v : E) + t • e) := by
      ext s; simp [hGeq]
    rw [hfun] at hcomp
    exact hcomp.unique hpar
  -- Differentiate with respect to the upper endpoint `a` by the fundamental theorem of calculus.
  have hp2 : (fderiv ℝ (parametricLineIntegral e F) (y, a)) (0, 1) = F ((y : E) + a • e) := by
    have hcomp : HasDerivAt (fun b : ℝ => parametricLineIntegral e F (y, b))
        ((fderiv ℝ (parametricLineIntegral e F) (y, a)) (0, 1)) a := by
      simpa [Function.comp_def] using (hGd.hasFDerivAt.comp a
        ((hasFDerivAt_const (𝕜 := ℝ) y a).prodMk (hasFDerivAt_id (𝕜 := ℝ) a))).hasDerivAt
    have hftc : HasDerivAt (fun b : ℝ => ∫ t in (0 : ℝ)..b, F ((y : E) + t • e))
        (F ((y : E) + a • e)) a :=
      ((hF.continuous.comp (continuous_const.add
        (continuous_id.smul continuous_const))).integral_hasStrictDerivAt 0 a).hasDerivAt
    exact hcomp.unique (by simpa only [← hGeq] using hftc)
  rw [hsplit, map_add, map_smul, smul_eq_mul, hp1, hp2]

/-- Transverse integration by parts for an interval integral with smooth symmetric endpoints. -/
private theorem integrable_and_integral_intervalIntegral_lineDeriv_eq_neg (e : E) (he : ‖e‖ = 1)
    {F : E → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) {r : (ℝ ∙ e)ᗮ → ℝ}
    (hr : ContDiff ℝ (⊤ : ℕ∞) r) (v : (ℝ ∙ e)ᗮ) :
    Integrable (fun y : (ℝ ∙ e)ᗮ =>
        ∫ t in (-r y)..(r y), lineDeriv ℝ F ((y : E) + t • e) (v : E)) volume ∧
      Integrable (fun y : (ℝ ∙ e)ᗮ =>
        fderiv ℝ r y v * (F ((y : E) + r y • e) + F ((y : E) + (-r y) • e))) volume ∧
      (∫ y : (ℝ ∙ e)ᗮ, ∫ t in (-r y)..(r y), lineDeriv ℝ F ((y : E) + t • e) (v : E)) =
        -∫ y : (ℝ ∙ e)ᗮ, fderiv ℝ r y v * (F ((y : E) + r y • e) + F ((y : E) + (-r y) • e)) := by
  -- Package `y ↦ ∫_{-r(y)}^{r(y)} F(y + t • e) dt` as a compactly supported smooth function `QT`.
  have hGsmooth : ContDiff ℝ (⊤ : ℕ∞) (parametricLineIntegral e F) :=
    (fderiv_parametric_line_integral_apply e hF 0 0 0 0).1
  let Q : (ℝ ∙ e)ᗮ → ℝ := fun y =>
    parametricLineIntegral e F (y, r y) - parametricLineIntegral e F (y, -r y)
  have hQsmooth : ContDiff ℝ (⊤ : ℕ∞) Q :=
    (hGsmooth.comp (contDiff_id.prodMk hr)).sub (hGsmooth.comp (contDiff_id.prodMk hr.neg))
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E)).1 hFc.isCompact.isBounded
  have hQc : HasCompactSupport Q := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : (ℝ ∙ e)ᗮ) (max R₀ 0)) fun y hy => ?_
    dsimp only [Q]
    rw [(fderiv_parametric_line_integral_apply e hF y 0 (r y) 0).2.1,
      (fderiv_parametric_line_integral_apply e hF y 0 (-r y) 0).2.1]
    simp [apply_add_smul_eq_zero_of_tsupport_subset_closedBall e he hR₀ hy]
  let QT : 𝓓(⊤, ℝ) := ⟨Q, hQsmooth, hQc, by intro x _; exact Opens.mem_top x⟩
  have hzero : ∫ y : (ℝ ∙ e)ᗮ, lineDeriv ℝ Q y v = 0 :=
    TestFunction.integral_lineDeriv_eq_zero (μ := volume) QT v
  -- Compute `lineDeriv ℝ Q y v` by the chain rule and Leibniz's rule at the moving endpoints.
  have hline (y : (ℝ ∙ e)ᗮ) : lineDeriv ℝ Q y v =
      (∫ t in (-r y)..(r y), lineDeriv ℝ F ((y : E) + t • e) (v : E)) +
        fderiv ℝ r y v * (F ((y : E) + r y • e) + F ((y : E) + (-r y) • e)) := by
    have hrd : DifferentiableAt ℝ r y := hr.differentiable (by simp) y
    have hG1 := fderiv_parametric_line_integral_apply e hF y v (r y) (fderiv ℝ r y v)
    have hG2 := fderiv_parametric_line_integral_apply e hF y v (-r y) (-fderiv ℝ r y v)
    have hd1 : HasFDerivAt (fun z => parametricLineIntegral e F (z, r z))
        ((fderiv ℝ (parametricLineIntegral e F) (y, r y)).comp
          ((ContinuousLinearMap.id ℝ _).prod (fderiv ℝ r y))) y :=
      (hGsmooth.differentiable (by simp) _).hasFDerivAt.comp y
        ((hasFDerivAt_id (𝕜 := ℝ) y).prodMk hrd.hasFDerivAt)
    have hd2 : HasFDerivAt (fun z => parametricLineIntegral e F (z, -r z))
        ((fderiv ℝ (parametricLineIntegral e F) (y, -r y)).comp
          ((ContinuousLinearMap.id ℝ _).prod (fderiv ℝ (-r) y))) y :=
      (hGsmooth.differentiable (by simp) _).hasFDerivAt.comp y
        ((hasFDerivAt_id (𝕜 := ℝ) y).prodMk hrd.neg.hasFDerivAt)
    have hQd : HasFDerivAt Q _ y := hd1.sub hd2
    rw [(hQsmooth.differentiable (by simp) y).lineDeriv_eq_fderiv, hQd.fderiv]
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply]
    rw [fderiv_neg, neg_apply, hG1.2.2, hG2.2.2]
    have hcont : Continuous (fun t : ℝ => lineDeriv ℝ F ((y : E) + t • e) (v : E)) :=
      continuous_lineDeriv_add_smul hF (y : E) e (v : E)
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (μ := volume) (-r y) 0)
      (hcont.intervalIntegrable (μ := volume) 0 (r y))
    rw [intervalIntegral.integral_symm 0 (-r y)] at hadj
    linarith
  have hint2 : Integrable (fun y : (ℝ ∙ e)ᗮ =>
      fderiv ℝ r y v * (F ((y : E) + r y • e) + F ((y : E) + (-r y) • e))) volume := by
    refine Continuous.integrable_of_hasCompactSupport ?_
      (HasCompactSupport.intro (isCompact_closedBall (0 : (ℝ ∙ e)ᗮ) (max R₀ 0)) fun y hy => ?_)
    · exact ((hr.continuous_fderiv (by simp)).clm_apply continuous_const).mul
        ((hF.continuous.comp ((ℝ ∙ e)ᗮ.subtypeL.continuous.add
          (hr.continuous.smul continuous_const))).add
          (hF.continuous.comp ((ℝ ∙ e)ᗮ.subtypeL.continuous.add
            (hr.neg.continuous.smul continuous_const))))
    · rw [apply_add_smul_eq_zero_of_tsupport_subset_closedBall e he hR₀ hy,
        apply_add_smul_eq_zero_of_tsupport_subset_closedBall e he hR₀ hy, add_zero, mul_zero]
  have hintQ : Integrable (fun y : (ℝ ∙ e)ᗮ => lineDeriv ℝ Q y v) volume := by
    let dQT : 𝓓(⊤, ℝ) := lineDerivCLM ℝ v QT
    have hcoe : (fun y : (ℝ ∙ e)ᗮ => lineDeriv ℝ Q y v) = fun y => dQT y := by
      ext y
      simp only [dQT, lineDerivCLM_apply_of_le le_top]
      rfl
    rw [hcoe]
    exact dQT.continuous.integrable_of_hasCompactSupport dQT.hasCompactSupport
  have hint1 : Integrable (fun y : (ℝ ∙ e)ᗮ =>
      ∫ t in (-r y)..(r y), lineDeriv ℝ F ((y : E) + t • e) (v : E)) volume :=
    (hintQ.sub hint2).congr (.of_forall fun y => by simp [hline y])
  simp_rw [hline] at hzero
  rw [integral_add hint1 hint2] at hzero
  exact ⟨hint1, hint2, by linarith⟩

/-- Fubini's theorem for `divergenceCLM ψ` on `symmetricSubgraph e he m`. -/
private theorem integral_divergenceCLM_mul_indicator_subgraph_eq_iterated (e : E) (he : ‖e‖ = 1)
    {m : (ℝ ∙ e)ᗮ → ℝ} (hm : Continuous m) (hm0 : ∀ y, 0 ≤ m y) (ψ : 𝓓(⊤, E)) :
    ∫ x : E, divergenceCLM ψ x * (symmetricSubgraph e he m).indicator 1 x =
      ∫ y : (ℝ ∙ e)ᗮ, ∫ t in (-m y / 2)..(m y / 2), divergenceCLM ψ ((y : E) + t • e) := by
  have hUm : MeasurableSet (symmetricSubgraph e he m) := measurableSet_symmetricSubgraph e he hm
  have hintE : Integrable
      (fun x : E => divergenceCLM ψ x * (symmetricSubgraph e he m).indicator 1 x) volume := by
    refine (((divergenceCLM ψ).continuous.integrable_of_hasCompactSupport
      (divergenceCLM ψ).hasCompactSupport).indicator hUm).congr (.of_forall fun x => ?_)
    by_cases hx : x ∈ symmetricSubgraph e he m <;> simp [hx]
  have hL := measurePreserving_orthogonalLineEquiv e he
  rw [← hL.integral_comp (orthogonalLineEquiv e he).toHomeomorph.measurableEmbedding
    (fun x => divergenceCLM ψ x * (symmetricSubgraph e he m).indicator 1 x)]
  rw [integral_prod
    (fun p : (ℝ ∙ e)ᗮ × ℝ => divergenceCLM ψ (orthogonalLineEquiv e he p) *
      (symmetricSubgraph e he m).indicator 1 (orthogonalLineEquiv e he p))
    (hL.integrable_comp_of_integrable hintE)]
  refine integral_congr_ae (.of_forall fun y => ?_)
  have hsec (t : ℝ) : divergenceCLM ψ (orthogonalLineEquiv e he (y, t)) *
      (symmetricSubgraph e he m).indicator 1 (orthogonalLineEquiv e he (y, t)) =
      (Ioo (-m y / 2) (m y / 2)).indicator (fun t => divergenceCLM ψ ((y : E) + t • e)) t := by
    rw [orthogonalLineEquiv_apply]
    have hmem := mem_symmetricSubgraph_add_smul e he m y t
    by_cases ht : t ∈ Ioo (-m y / 2) (m y / 2) <;> simp [hmem, ht]
  simp_rw [hsec]
  rw [integral_indicator measurableSet_Ioo, Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [hm0 y])]

/-- Gauss–Green formula for a test vector field `ψ` on `symmetricSubgraph e he m` for a smooth
nonnegative profile `m : (ℝ ∙ e)ᗮ → ℝ`. -/
private theorem integral_divergenceCLM_mul_indicator_subgraph_eq (e : E) (he : ‖e‖ = 1)
    {m : (ℝ ∙ e)ᗮ → ℝ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hm0 : ∀ y, 0 ≤ m y) (ψ : 𝓓(⊤, E)) :
    Integrable (fun y : (ℝ ∙ e)ᗮ =>
        ⟪e, ψ ((y : E) + (m y / 2) • e)⟫ - ⟪e, ψ ((y : E) + (-m y / 2) • e)⟫ -
          fderiv ℝ m y (((orthogonalLineEquiv e he).symm
            ((2 : ℝ)⁻¹ • (ψ ((y : E) + (m y / 2) • e) + ψ ((y : E) + (-m y / 2) • e)))).1))
        volume ∧
      ∫ x : E, divergenceCLM ψ x * (symmetricSubgraph e he m).indicator 1 x =
        ∫ y : (ℝ ∙ e)ᗮ,
          (⟪e, ψ ((y : E) + (m y / 2) • e)⟫ - ⟪e, ψ ((y : E) + (-m y / 2) • e)⟫ -
            fderiv ℝ m y (((orthogonalLineEquiv e he).symm
              ((2 : ℝ)⁻¹ • (ψ ((y : E) + (m y / 2) • e) + ψ ((y : E) + (-m y / 2) • e)))).1)) := by
  let b := stdOrthonormalBasis ℝ (ℝ ∙ e)ᗮ
  let r : (ℝ ∙ e)ᗮ → ℝ := fun y => m y / 2
  have hr : ContDiff ℝ (⊤ : ℕ∞) r := hm.div_const 2
  have hFi (v : E) : ContDiff ℝ (⊤ : ℕ∞) (fun z : E => ⟪v, ψ z⟫) :=
    (innerSL ℝ v).contDiff.comp ψ.contDiff
  have hFic (v : E) : HasCompactSupport (fun z : E => ⟪v, ψ z⟫) :=
    ψ.hasCompactSupport.comp_left (inner_zero_right v)
  have htrans (i) := integrable_and_integral_intervalIntegral_lineDeriv_eq_neg e he
    (hFi (b i : E)) (hFic (b i : E)) hr (b i)
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E)).1
    ψ.hasCompactSupport.isCompact.isBounded
  have hint_long : Integrable (fun y : (ℝ ∙ e)ᗮ =>
      ⟪e, ψ ((y : E) + r y • e)⟫ - ⟪e, ψ ((y : E) + (-r y) • e)⟫) volume := by
    refine Continuous.integrable_of_hasCompactSupport ?_
      (HasCompactSupport.intro (isCompact_closedBall (0 : (ℝ ∙ e)ᗮ) (max R₀ 0)) fun y hy => ?_)
    · exact ((hFi e).continuous.comp ((ℝ ∙ e)ᗮ.subtypeL.continuous.add
        (hr.continuous.smul continuous_const))).sub
        ((hFi e).continuous.comp ((ℝ ∙ e)ᗮ.subtypeL.continuous.add
          (hr.neg.continuous.smul continuous_const)))
    · rw [apply_add_smul_eq_zero_of_tsupport_subset_closedBall e he hR₀ hy,
        apply_add_smul_eq_zero_of_tsupport_subset_closedBall e he hR₀ hy, inner_zero_right,
        sub_self]
  -- Split `div ψ` into the `e`-derivative (integrated along the fiber) and transverse derivatives.
  have hline_split (y : (ℝ ∙ e)ᗮ) :
      (∫ t in (-r y)..(r y), divergenceCLM ψ ((y : E) + t • e)) =
        (⟪e, ψ ((y : E) + r y • e)⟫ - ⟪e, ψ ((y : E) + (-r y) • e)⟫) +
          ∑ i, ∫ t in (-r y)..(r y),
            lineDeriv ℝ (fun z => ⟪(b i : E), ψ z⟫) ((y : E) + t • e) (b i : E) := by
    simp_rw [divergenceCLM_eq_lineDeriv_add_sum e he b ψ]
    have hcont_i (v : E) :
        Continuous (fun t : ℝ => lineDeriv ℝ (fun z => ⟪v, ψ z⟫) ((y : E) + t • e) v) :=
      continuous_lineDeriv_add_smul (hFi v) (y : E) e v
    have hci (v : E) : IntervalIntegrable
        (fun t : ℝ => lineDeriv ℝ (fun z => ⟪v, ψ z⟫) ((y : E) + t • e) v) volume (-r y) (r y) :=
      (hcont_i v).intervalIntegrable _ _
    have hcsum : IntervalIntegrable
        (fun t : ℝ => ∑ i, lineDeriv ℝ (fun z => ⟪(b i : E), ψ z⟫) ((y : E) + t • e) (b i : E))
        volume (-r y) (r y) :=
      (continuous_finsetSum Finset.univ fun i _ => hcont_i (b i : E)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add (hci e) hcsum,
      intervalIntegral.integral_finsetSum fun i _ => hci (b i : E)]
    congr 1
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => ⟪e, ψ ((y : E) + t • e)⟫) (fun t _ => ?_) (hci e)
    have hid : HasDerivAt (fun s : ℝ => s • e) e t := by
      simpa only [one_smul, id_eq] using (hasDerivAt_id t).smul_const e
    have hin : HasDerivAt (fun s : ℝ => (y : E) + s • e) e t := hid.const_add (y : E)
    have hd : HasDerivAt (fun t : ℝ => ⟪e, ψ ((y : E) + t • e)⟫)
        (fderiv ℝ (fun z => ⟪e, ψ z⟫) ((y : E) + t • e) e) t := by
      simpa [Function.comp_def] using
        ((hFi e).differentiable (by simp) ((y : E) + t • e)).hasFDerivAt.comp_hasDerivAt t hin
    rwa [← ((hFi e).differentiable (by simp) _).lineDeriv_eq_fderiv] at hd
  -- Reassemble the orthonormal-basis boundary terms into `fderiv ℝ m y` applied to the average.
  have hsum_eq (y : (ℝ ∙ e)ᗮ) :
      ∑ i, fderiv ℝ r y (b i) *
        (⟪(b i : E), ψ ((y : E) + r y • e)⟫ + ⟪(b i : E), ψ ((y : E) + (-r y) • e)⟫) =
      fderiv ℝ m y (((orthogonalLineEquiv e he).symm
        ((2 : ℝ)⁻¹ • (ψ ((y : E) + r y • e) + ψ ((y : E) + (-r y) • e)))).1) := by
    have hfr : fderiv ℝ r y = (2 : ℝ)⁻¹ • fderiv ℝ m y := by
      have hre : r = (2 : ℝ)⁻¹ • m := by ext z; simp [r, div_eq_inv_mul]
      rw [hre, fderiv_const_smul (hm.differentiable (by simp) y)]
    rw [← sum_apply_mul_inner_eq_apply_fst e he b (fderiv ℝ m y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfr, smul_apply, smul_eq_mul, inner_smul_right, inner_add_right]
    ring
  have hint_sum := integrable_finsetSum Finset.univ fun i _ => (htrans i).2.1
  have hint_sum' : Integrable (fun y : (ℝ ∙ e)ᗮ =>
      fderiv ℝ m y (((orthogonalLineEquiv e he).symm
        ((2 : ℝ)⁻¹ • (ψ ((y : E) + r y • e) + ψ ((y : E) + (-r y) • e)))).1)) volume :=
    hint_sum.congr (.of_forall hsum_eq)
  have hint_rhs : Integrable (fun y : (ℝ ∙ e)ᗮ =>
      ⟪e, ψ ((y : E) + r y • e)⟫ - ⟪e, ψ ((y : E) + (-r y) • e)⟫ -
        fderiv ℝ m y (((orthogonalLineEquiv e he).symm
          ((2 : ℝ)⁻¹ • (ψ ((y : E) + r y • e) + ψ ((y : E) + (-r y) • e)))).1)) volume :=
    hint_long.sub hint_sum'
  refine ⟨by simpa only [r, neg_div] using hint_rhs, ?_⟩
  rw [integral_divergenceCLM_mul_indicator_subgraph_eq_iterated e he hm.continuous hm0 ψ]
  have hr_neg (y) : -m y / 2 = -r y := by simp [r, neg_div]
  have hr_pos (y) : m y / 2 = r y := rfl
  simp_rw [hr_neg, hr_pos, hline_split]
  rw [integral_add hint_long (integrable_finsetSum Finset.univ fun i _ => (htrans i).1),
    integral_finsetSum _ fun i _ => (htrans i).1]
  simp_rw [(htrans _).2.2]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ => (htrans i).2.1]
  simp_rw [hsum_eq]
  rw [← sub_eq_add_neg, ← integral_sub hint_long hint_sum']

end SubgraphIBP

section VariationalComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Canonical measurable equivalence `H ≃ᵐ (⊤ : Opens H)`. -/
private def topOpensEquiv (H : Type*) [TopologicalSpace H] [MeasurableSpace H] :
    H ≃ᵐ (⊤ : Opens H) where
  toFun y := ⟨y, Opens.mem_top y⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_id.subtype_mk
  measurable_invFun := measurable_subtype_coe

/-- Standard measure-theoretic properties of `volume.comap Subtype.val` and the BV decomposition on
`(⊤ : Opens H)`. -/
private theorem topOpens_bv_facts {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] {ℓ : H → ℝ}
    (hℓ : Integrable ℓ volume) (hTV : totalVariationOn volume ⊤ ℓ ≠ ∞) :
    let ν : Measure (⊤ : Opens H) := volume.comap Subtype.val
    SigmaFinite ν ∧ MeasurePreserving (Subtype.val : (⊤ : Opens H) → H) ν volume ∧
      Integrable (fun y : H => acDerivativeDensity volume ⊤ ℓ ν ⟨y, Opens.mem_top y⟩) volume ∧
      IsFiniteMeasure ((variationMeasure volume ⊤ ℓ).singularPart ν) := by
  intro ν
  let e_top := topOpensEquiv H
  have hν : ν = volume.map e_top := MeasurableEquiv.comap_symm e_top
  have : SigmaFinite ν := hν ▸ e_top.sigmaFinite_map
  have hm : MeasurableEmbedding (Subtype.val : (⊤ : Opens H) → H) := e_top.symm.measurableEmbedding
  have hmp : MeasurePreserving (Subtype.val : (⊤ : Opens H) → H) ν volume :=
    ⟨measurable_subtype_coe,
      by rw [hm.map_comap, Subtype.range_coe, Opens.coe_top, Measure.restrict_univ]⟩
  have hfin_top : ∀ K : Set H, IsCompact K → K ⊆ (⊤ : Opens H) →
      ∃ V : Opens H, K ⊆ (V : Set H) ∧ totalVariationOn volume V ℓ ≠ ∞ :=
    fun _ _ hK => ⟨⊤, hK, hTV⟩
  refine ⟨inferInstance, hmp, (hmp.integrable_comp_emb hm).1
    (integrable_acDerivativeDensity (hℓ.locallyIntegrable.locallyIntegrableOn ⊤) ν hTV),
    ⟨(Measure.singularPart_le _ _ univ).trans_lt ?_⟩⟩
  rw [variationMeasure_univ (hℓ.locallyIntegrable.locallyIntegrableOn ⊤) hfin_top]
  exact hTV.lt_top

/-- The real section-length profile of a finite-volume null-measurable set is integrable on
`(ℝ ∙ e)ᗮ`. -/
private theorem integrable_measureReal_lineSection (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞) :
    Integrable (fun y : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (y : E) + t • e ∈ s}) volume := by
  refine ⟨(aemeasurable_volume_lineSection e he hs).ennreal_toReal.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_eNorm]
  have hae : (fun y : (ℝ ∙ e)ᗮ => ‖volume.real {t : ℝ | (y : E) + t • e ∈ s}‖ₑ) =ᵐ[volume]
      fun y => volume {t : ℝ | (y : E) + t • e ∈ s} := by
    filter_upwards [ae_volume_lineSection_lt_top e he hs hfin] with y hy
    rw [Real.eNorm_of_nonneg measureReal_nonneg, measureReal_def, ENNReal.ofReal_toReal hy.ne]
  rw [lintegral_congr_ae hae, ← volume_eq_lintegral_volume_lineSection e he hs]
  exact hfin.lt_top

/-- Convolving a normalized smooth bump against a finite measure on `(⊤ : Opens H)` gives an
integrable function on `H` with integral `ω.real univ`. -/
private theorem integrable_and_integral_normed_singular {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (φ : ContDiffBump (0 : H)) (ω : Measure (⊤ : Opens H)) [IsFiniteMeasure ω] :
    Integrable (fun y : H => ∫ x : (⊤ : Opens H), φ.normed volume (y - x) ∂ω) volume ∧
      (∫ y : H, ∫ x : (⊤ : Opens H), φ.normed volume (y - x) ∂ω) = ω.real univ := by
  set S : H → ℝ := fun y => ∫ x : (⊤ : Opens H), φ.normed volume (y - x) ∂ω
  have hmeas : Measurable (fun p : H × (⊤ : Opens H) => φ.normed volume (p.1 - p.2)) :=
    φ.continuous_normed.measurable.comp
      (measurable_fst.sub (measurable_subtype_coe.comp measurable_snd))
  have hS0 (y : H) : 0 ≤ S y := integral_nonneg fun _ => φ.nonneg_normed _
  have hS_lint (y : H) : ENNReal.ofReal (S y) =
      ∫⁻ x : (⊤ : Opens H), ENNReal.ofReal (φ.normed volume (y - x)) ∂ω := by
    refine ofReal_integral_eq_lintegral_ofReal ?_ (.of_forall fun _ => φ.nonneg_normed _)
    obtain ⟨M, hM⟩ := φ.continuous_normed.bounded_above_of_compact_support
      (φ.hasCompactSupport_normed (μ := volume))
    exact Integrable.of_bound
      (φ.continuous_normed.comp (continuous_const.sub continuous_subtype_val)).aestronglyMeasurable
      M (.of_forall fun x => hM _)
  have hton : ∫⁻ y : H, ENNReal.ofReal (S y) = ω univ := by
    simp_rw [hS_lint]
    rw [lintegral_lintegral_swap hmeas.ennreal_ofReal.aemeasurable]
    have hx (x : (⊤ : Opens H)) :
        ∫⁻ y : H, ENNReal.ofReal (φ.normed volume (y - x)) = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        (φ.integrable_normed.comp_sub_right (x : H))
        (.of_forall fun _ => φ.nonneg_normed _),
        integral_sub_right_eq_self _ (x : H), φ.integral_normed, ENNReal.ofReal_one]
    simp_rw [hx]
    simp
  have hSm : AEStronglyMeasurable S volume := by
    have h1 : Measurable (fun y : H => ENNReal.ofReal (S y)) := by
      simp_rw [hS_lint]
      exact hmeas.ennreal_ofReal.lintegral_prod_right'
    exact h1.ennreal_toReal.aestronglyMeasurable.congr
      (.of_forall fun y => ENNReal.toReal_ofReal (hS0 y))
  have hint : Integrable S volume := by
    refine ⟨hSm, ?_⟩
    rw [hasFiniteIntegral_iff_eNorm]
    simp_rw [Real.eNorm_of_nonneg (hS0 _)]
    exact hton ▸ measure_lt_top ω univ
  refine ⟨hint, ?_⟩
  rw [← ENNReal.toReal_ofReal (integral_nonneg hS0),
    ofReal_integral_eq_lintegral_ofReal hint (.of_forall hS0), hton, measureReal_def]

/-- Pairings of a test vector field `ψ` with the subgraphs of the mollified section lengths
converge to the pairing with the Steiner symmetral. -/
private theorem tendsto_integral_divergenceCLM_subgraph_mollified (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞) (ψ : 𝓓(⊤, E)) :
    let ℓ : (ℝ ∙ e)ᗮ → ℝ := fun y => volume.real {t : ℝ | (y : E) + t • e ∈ s}
    let φ (k : ℕ) : ContDiffBump (0 : (ℝ ∙ e)ᗮ) := ContDiffBump.shrinking one_pos k
    let m (k : ℕ) : (ℝ ∙ e)ᗮ → ℝ := (φ k).normed volume ⋆[lsmul ℝ ℝ, volume] ℓ
    Tendsto (fun k => ∫ x : E, divergenceCLM ψ x * (symmetricSubgraph e he (m k)).indicator 1 x)
      atTop (𝓝 (∫ x : E, divergenceCLM ψ x * (steinerSymmetrization e he s).indicator 1 x)) := by
  intro ℓ φ m
  have hℓ : Integrable ℓ volume := integrable_measureReal_lineSection e he hs hfin
  have hm0 (k : ℕ) (y : (ℝ ∙ e)ᗮ) : 0 ≤ m k y := by
    dsimp only [m]; rw [convolution_def]
    exact integral_nonneg fun _ => mul_nonneg ((φ k).nonneg_normed _) measureReal_nonneg
  have hm_smooth (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (m k) :=
    (φ k).hasCompactSupport_normed.contDiff_convolution_left _ (φ k).contDiff_normed
      hℓ.locallyIntegrable
  have hUm (k : ℕ) : MeasurableSet (symmetricSubgraph e he (m k)) :=
    measurableSet_symmetricSubgraph e he (hm_smooth k).continuous
  have hSm : NullMeasurableSet (steinerSymmetrization e he s) volume :=
    nullMeasurableSet_steinerSymmetrization e he hs
  -- Bound the `L¹(E)` indicator difference slicewise by `‖m k - ℓ‖_{L¹((ℝ ∙ e)ᗮ)}`.
  have hL1 : Tendsto (fun k => ∫⁻ x : E,
      ‖(symmetricSubgraph e he (m k)).indicator (1 : E → ℝ) x -
        (steinerSymmetrization e he s).indicator 1 x‖ₑ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds (x := (0 : ℝ≥0∞)))
      (tendsto_lintegral_enorm_normed_convolution_sub
        (ContDiffBump.tendsto_rOut_shrinking one_pos) hℓ)
      (fun _ => zero_le) fun k => ?_
    have haemeas : AEMeasurable (fun x : E =>
        ‖(symmetricSubgraph e he (m k)).indicator (1 : E → ℝ) x -
          (steinerSymmetrization e he s).indicator 1 x‖ₑ) volume :=
      ((aestronglyMeasurable_const.indicator (hUm k)).sub
        (aestronglyMeasurable_const.indicator₀ hSm)).eNorm
    rw [lintegral_eq_lintegral_lintegral_line e he haemeas]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_volume_lineSection_lt_top e he hs hfin] with y hy
    have hvol_y : volume {t : ℝ | (y : E) + t • e ∈ s} = ENNReal.ofReal (ℓ y) := by
      simp [ℓ, measureReal_def, ENNReal.ofReal_toReal hy.ne]
    have hsecS : {t : ℝ | (y : E) + t • e ∈ steinerSymmetrization e he s} =
        Ioo (-ℓ y / 2) (ℓ y / 2) := by
      rw [lineSection_steinerSymmetrization, hvol_y, eball_zero_ofReal_div_two measureReal_nonneg]
    have hsecU (t : ℝ) : (symmetricSubgraph e he (m k)).indicator (1 : E → ℝ) ((y : E) + t • e) -
        (steinerSymmetrization e he s).indicator 1 ((y : E) + t • e) =
        (Ioo (-m k y / 2) (m k y / 2)).indicator 1 t -
          (Ioo (-ℓ y / 2) (ℓ y / 2)).indicator 1 t := by
      have hmU := mem_symmetricSubgraph_add_smul e he (m k) y t
      have hmS : (y : E) + t • e ∈ steinerSymmetrization e he s ↔ t ∈ Ioo (-ℓ y / 2) (ℓ y / 2) := by
        simpa using Set.ext_iff.1 hsecS t
      by_cases h1 : t ∈ Ioo (-m k y / 2) (m k y / 2) <;>
        by_cases h2 : t ∈ Ioo (-ℓ y / 2) (ℓ y / 2) <;> simp [hmU, hmS, h1, h2]
    simp_rw [hsecU]
    exact lintegral_enorm_indicator_Ioo_sub_le (hm0 k y) measureReal_nonneg
  -- Multiply by the bounded compactly supported function `div ψ` to deduce `L¹(E)` convergence.
  obtain ⟨C, hC⟩ := (divergenceCLM ψ).continuous.bounded_above_of_compact_support
    (divergenceCLM ψ).hasCompactSupport
  have hdiv : Integrable (fun x : E => divergenceCLM ψ x) volume :=
    (divergenceCLM ψ).continuous.integrable_of_hasCompactSupport (divergenceCLM ψ).hasCompactSupport
  refine tendsto_integral_of_L1
    (fun x => divergenceCLM ψ x * (steinerSymmetrization e he s).indicator 1 x)
    ((divergenceCLM ψ).continuous.aestronglyMeasurable.mul
      (aestronglyMeasurable_const.indicator₀ hSm))
    (.of_forall fun k => hdiv.mono (hdiv.1.mul (aestronglyMeasurable_const.indicator (hUm k)))
      (.of_forall fun x => by by_cases hx : x ∈ symmetricSubgraph e he (m k) <;> simp [hx])) ?_
  have hmul : Tendsto (fun k => ENNReal.ofReal (max C 0) * ∫⁻ x : E,
      ‖(symmetricSubgraph e he (m k)).indicator (1 : E → ℝ) x -
        (steinerSymmetrization e he s).indicator 1 x‖ₑ) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hL1
      (Or.inr (ENNReal.ofReal_ne_top (r := max C 0)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds (x := (0 : ℝ≥0∞))) hmul
    (fun _ => zero_le) fun k => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  rw [← mul_sub, eNorm_mul, ← ofReal_norm]
  exact mul_le_mul_of_nonneg_right
    (ENNReal.ofReal_le_ofReal ((hC x).trans (le_max_left _ _))) zero_le

/-- Variational functional of the section-length BV derivative matching the Steiner symmetral
perimeter from above and the sliced perimeter (minus noninterval excess) from below. -/
private def steinerFunctional (e : E) (s : Set E) : ℝ :=
  let ℓ : (ℝ ∙ e)ᗮ → ℝ := fun y => volume.real {t : ℝ | (y : E) + t • e ∈ s}
  let D : Set (ℝ ∙ e)ᗮ := {y | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  let ν : Measure (⊤ : Opens (ℝ ∙ e)ᗮ) := volume.comap Subtype.val
  let g : (ℝ ∙ e)ᗮ → (ℝ ∙ e)ᗮ :=
    fun y => acDerivativeDensity volume ⊤ ℓ ν ⟨y, Opens.mem_top y⟩
  let ω : Measure (⊤ : Opens (ℝ ∙ e)ᗮ) := (variationMeasure volume ⊤ ℓ).singularPart ν
  (∫ y in D, √(4 + ‖g y‖ ^ 2)) + (∫ y in Dᶜ, ‖g y‖) + ω.real univ

private theorem integrableOn_sqrt_four_add_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {D : Set α} (hDfin : μ D ≠ ∞) {u : α → ℝ} (hu : Integrable u μ) (hu0 : ∀ y, 0 ≤ u y) :
    IntegrableOn (fun y => √(4 + (u y) ^ 2)) D μ :=
  ((integrableOn_const (C := (2 : ℝ)) hDfin).add hu.integrableOn).mono'
    (((Real.continuous_sqrt.comp (continuous_const.add (continuous_pow 2)))
      |>.comp_aestronglyMeasurable hu.1).restrict)
    (.of_forall fun y => by
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      have h4 : √(4 : ℝ) = 2 := Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num) |>.2 (by ring)
      simpa [h4] using sqrt_four_add_sq_add_le (le_refl (0 : ℝ)) (hu0 y))

/-- Single-step bound on `∫ div ψ * 1_{symmetricSubgraph e he m}` in terms of gradient bounds
`Gn + Sn` on `D` and `Dᶜ`. -/
private theorem integral_divergenceCLM_subgraph_le_split (e : E) (he : ‖e‖ = 1)
    {D : Set (ℝ ∙ e)ᗮ} (hDm : NullMeasurableSet D volume) (hDfin : volume D ≠ ∞)
    {m Gn Sn : (ℝ ∙ e)ᗮ → ℝ} (hm_sm : ContDiff ℝ (⊤ : ℕ∞) m) (hm_int : Integrable m volume)
    (hm0 : ∀ y, 0 ≤ m y) (hGn_int : Integrable Gn volume) (hGn0 : ∀ y, 0 ≤ Gn y)
    (hSn_int : Integrable Sn volume) (hSn0 : ∀ y, 0 ≤ Sn y)
    (hgrad : ∀ y, ‖fderiv ℝ m y‖ ≤ Gn y + Sn y)
    {ψ : 𝓓(⊤, E)} (hψ : ∀ x, ‖ψ x‖ ≤ 1) {Mψ : ℝ} (hMψ : ∀ x, ‖fderiv ℝ (ψ : E → E) x‖ ≤ Mψ) :
    ∫ x : E, divergenceCLM ψ x * (symmetricSubgraph e he m).indicator 1 x ≤
      (∫ y in D, √(4 + (Gn y) ^ 2)) +
        ((∫ y in Dᶜ, Mψ * m y) + (∫ y in Dᶜ, Gn y)) + ∫ y : (ℝ ∙ e)ᗮ, Sn y := by
  obtain ⟨hJ_int, hJ_eq⟩ := integral_divergenceCLM_mul_indicator_subgraph_eq e he hm_sm hm0 ψ
  rw [hJ_eq, ← integral_add_compl₀ hDm hJ_int, ← integral_add_compl₀ hDm hSn_int]
  -- On `D`, use the pointwise Cauchy–Schwarz bound `√(4 + ‖Dm‖²)` and subadditivity in `Gn + Sn`.
  have hsq_int := integrableOn_sqrt_four_add_sq hDfin hGn_int hGn0
  have hbD : (∫ y in D,
      (⟪e, ψ ((y : E) + (m y / 2) • e)⟫ - ⟪e, ψ ((y : E) + (-m y / 2) • e)⟫ -
        fderiv ℝ m y (((orthogonalLineEquiv e he).symm
          ((2 : ℝ)⁻¹ • (ψ ((y : E) + (m y / 2) • e) + ψ ((y : E) + (-m y / 2) • e)))).1))) ≤
      (∫ y in D, √(4 + (Gn y) ^ 2)) + ∫ y in D, Sn y := by
    rw [← integral_add hsq_int hSn_int.integrableOn]
    refine integral_mono_ae hJ_int.integrableOn (hsq_int.add hSn_int.integrableOn)
      (.of_forall fun y => (flux_integrand_le_sqrt e he (hψ _) (hψ _) _).trans ?_)
    refine (Real.sqrt_le_sqrt ?_).trans (sqrt_four_add_sq_add_le (hGn0 y) (hSn0 y))
    nlinarith [hgrad y, norm_nonneg (fderiv ℝ m y)]
  -- On `Dᶜ`, bound the vertical jump by `Mψ * m y` via the mean value theorem (`m_k → 0` on `Dᶜ`).
  have hbDc : (∫ y in Dᶜ,
      (⟪e, ψ ((y : E) + (m y / 2) • e)⟫ - ⟪e, ψ ((y : E) + (-m y / 2) • e)⟫ -
        fderiv ℝ m y (((orthogonalLineEquiv e he).symm
          ((2 : ℝ)⁻¹ • (ψ ((y : E) + (m y / 2) • e) + ψ ((y : E) + (-m y / 2) • e)))).1))) ≤
      ((∫ y in Dᶜ, Mψ * m y) + ∫ y in Dᶜ, Gn y) + ∫ y in Dᶜ, Sn y := by
    have hi1 : IntegrableOn (fun y => Mψ * m y) Dᶜ volume := (hm_int.const_mul Mψ).integrableOn
    have hi12 : IntegrableOn (fun y => Mψ * m y + Gn y) Dᶜ volume := hi1.add hGn_int.integrableOn
    have hi123 : IntegrableOn (fun y => (Mψ * m y + Gn y) + Sn y) Dᶜ volume :=
      hi12.add hSn_int.integrableOn
    rw [← integral_add hi1 hGn_int.integrableOn, ← integral_add hi12 hSn_int.integrableOn]
    refine integral_mono_ae hJ_int.integrableOn hi123 (.of_forall fun y => ?_)
    dsimp only
    set x₁ : E := (y : E) + (m y / 2) • e
    set x₂ : E := (y : E) + (-m y / 2) • e
    have hmvt : ‖ψ x₁ - ψ x₂‖ ≤ Mψ * ‖x₁ - x₂‖ :=
      convex_univ.norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => ψ.contDiff.differentiable (by simp) z)
        (fun z _ => hMψ z) (mem_univ _) (mem_univ _)
    have hx_norm : ‖x₁ - x₂‖ = m y := by
      have hsub : x₁ - x₂ = (m y) • e := by simp only [x₁, x₂, neg_div]; module
      rw [hsub, norm_smul, he, mul_one, Real.norm_of_nonneg (hm0 y)]
    have he_diff : ⟪e, ψ x₁⟫ - ⟪e, ψ x₂⟫ ≤ Mψ * m y := by
      rw [← inner_sub_right]
      exact (le_abs_self _).trans <| (abs_real_inner_le_norm _ _).trans <| by
        rw [he, one_mul, ← hx_norm]; exact hmvt
    set u : E := (2 : ℝ)⁻¹ • (ψ x₁ + ψ x₂)
    have hu : ‖u‖ ≤ 1 := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      linarith [(norm_add_le (ψ x₁) (ψ x₂)).trans (add_le_add (hψ x₁) (hψ x₂))]
    have hp : ‖((orthogonalLineEquiv e he).symm u).1‖ ≤ 1 := by
      have h1 : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
      have h2 : ((((orthogonalLineEquiv e he).symm u).1 : E) + ⟪e, u⟫ • e) = u := by
        rw [orthogonalLineEquiv_symm_fst, sub_add_cancel]
      rw [← h2, norm_add_smul_sq e he] at h1
      nlinarith [sq_nonneg ⟪e, u⟫, norm_nonneg (((orthogonalLineEquiv e he).symm u).1)]
    have hmid_le : -fderiv ℝ m y (((orthogonalLineEquiv e he).symm u).1) ≤ Gn y + Sn y :=
      (neg_le_abs _).trans <| ((fderiv ℝ m y).le_opNorm_of_le hp).trans
        (by rw [mul_one]; exact hgrad y)
    linarith
  linarith

/-- **Upper bound for `perimeter volume ⊤ (steinerSymmetrization e he s)`.** -/
private theorem perimeter_steinerSymmetrization_le_ofReal_functional (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hDfin : volume {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} ≠ ∞)
    (hTV : totalVariationOn volume ⊤
      (fun y : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (y : E) + t • e ∈ s}) ≠ ∞) :
    perimeter volume ⊤ (steinerSymmetrization e he s) ≤
      ENNReal.ofReal (steinerFunctional e s) := by
  let ℓ : (ℝ ∙ e)ᗮ → ℝ := fun y => volume.real {t : ℝ | (y : E) + t • e ∈ s}
  let D : Set (ℝ ∙ e)ᗮ := {y | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  let ν : Measure (⊤ : Opens (ℝ ∙ e)ᗮ) := volume.comap Subtype.val
  let g : (ℝ ∙ e)ᗮ → (ℝ ∙ e)ᗮ :=
    fun y => acDerivativeDensity volume ⊤ ℓ ν ⟨y, Opens.mem_top y⟩
  let ω : Measure (⊤ : Opens (ℝ ∙ e)ᗮ) := (variationMeasure volume ⊤ ℓ).singularPart ν
  have hℓ : Integrable ℓ volume := integrable_measureReal_lineSection e he hs hfin
  obtain ⟨_, _, hg_int, hω_fin⟩ := topOpens_bv_facts hℓ hTV
  have hDm : NullMeasurableSet D volume :=
    nullMeasurableSet_lt aemeasurable_const (aemeasurable_volume_lineSection e he hs)
  rw [perimeter_def]
  refine totalVariationOn_le_iff.mpr fun ψ hψ => ENNReal.ofReal_le_ofReal ?_
  -- Mollify `ℓ` and bound `‖Dm_k‖` by `Gn_k + Sn_k` via the BV Lebesgue decomposition.
  let φ (k : ℕ) : ContDiffBump (0 : (ℝ ∙ e)ᗮ) := ContDiffBump.shrinking one_pos k
  let m (k : ℕ) : (ℝ ∙ e)ᗮ → ℝ := (φ k).normed volume ⋆[lsmul ℝ ℝ, volume] ℓ
  let Gn (k : ℕ) : (ℝ ∙ e)ᗮ → ℝ := (φ k).normed volume ⋆[lsmul ℝ ℝ, volume] fun z => ‖g z‖
  have hm0 (k : ℕ) (y : (ℝ ∙ e)ᗮ) : 0 ≤ m k y := by
    dsimp only [m]; rw [convolution_def]
    exact integral_nonneg fun _ => mul_nonneg ((φ k).nonneg_normed _) measureReal_nonneg
  have hGn0 (k : ℕ) (y : (ℝ ∙ e)ᗮ) : 0 ≤ Gn k y := by
    dsimp only [Gn]; rw [convolution_def]
    exact integral_nonneg fun _ => mul_nonneg ((φ k).nonneg_normed _) (norm_nonneg _)
  have hSn (k : ℕ) := integrable_and_integral_normed_singular (φ k) ω
  have hGn_int (k : ℕ) : Integrable (Gn k) volume :=
    (φ k).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hg_int.norm
  have hm_int (k : ℕ) : Integrable (m k) volume :=
    (φ k).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hℓ
  obtain ⟨Mψ, hMψ⟩ := (ψ.contDiff.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (ψ.hasCompactSupport.fderiv ℝ)
  have hstep (k : ℕ) :
      ∫ x : E, divergenceCLM ψ x * (symmetricSubgraph e he (m k)).indicator 1 x ≤
        (∫ y in D, √(4 + (Gn k y) ^ 2)) +
          ((∫ y in Dᶜ, Mψ * m k y) + (∫ y in Dᶜ, Gn k y)) + ω.real univ := by
    rw [← (hSn k).2]
    exact integral_divergenceCLM_subgraph_le_split e he hDm hDfin
      ((φ k).hasCompactSupport_normed.contDiff_convolution_left _ (φ k).contDiff_normed
        hℓ.locallyIntegrable)
      (hm_int k) (hm0 k) (hGn_int k) (hGn0 k) (hSn k).1
      (fun _ => integral_nonneg fun _ => (φ k).nonneg_normed _)
      (fun y => norm_fderiv_convolution_lsmul_top_le hℓ.locallyIntegrable
        (fun _ _ hK => ⟨⊤, hK, hTV⟩) ((φ k).contDiff_normed (n := 1))
        (φ k).hasCompactSupport_normed (φ k).nonneg_normed y) hψ hMψ
  -- Pass to the `k → ∞` limit using `L¹` convergence `m_k → ℓ` and `Gn_k → ‖g‖`.
  have hG_L1 := tendsto_lintegral_enorm_normed_convolution_sub
    (ContDiffBump.tendsto_rOut_shrinking one_pos) hg_int.norm
  have hm_L1 := tendsto_lintegral_enorm_normed_convolution_sub
    (ContDiffBump.tendsto_rOut_shrinking one_pos) hℓ
  have hsq_g_int := integrableOn_sqrt_four_add_sq hDfin hg_int.norm fun y => norm_nonneg (g y)
  have hlim1 : Tendsto (fun k => ∫ y in D, √(4 + (Gn k y) ^ 2)) atTop
      (𝓝 (∫ y in D, √(4 + ‖g y‖ ^ 2))) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 <|
      squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
        (by simpa using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hG_L1)
    have hsq_k := integrableOn_sqrt_four_add_sq hDfin (hGn_int k) (hGn0 k)
    rw [← integral_sub hsq_k hsq_g_int]
    refine (norm_integral_le_integral_norm _).trans <|
      (integral_mono_ae (hsq_k.sub hsq_g_int).norm
        ((hGn_int k).sub hg_int.norm).norm.integrableOn (.of_forall fun y => ?_)).trans <|
        (setIntegral_le_integral ((hGn_int k).sub hg_int.norm).norm
          (.of_forall fun _ => norm_nonneg _)).trans_eq
          (integral_norm_eq_lintegral_eNorm ((hGn_int k).sub hg_int.norm).aestronglyMeasurable)
    simpa [Real.norm_eq_abs] using abs_sqrt_four_add_sq_sub_le (hGn0 k y) (norm_nonneg _)
  have hlim2 : Tendsto (fun k => ∫ y in Dᶜ, Mψ * m k y) atTop (𝓝 0) := by
    have hℓ_Dc : ∫ y in Dᶜ, ℓ y = 0 := setIntegral_eq_zero_of_forall_eq_zero fun y hy => by
      have h0 : volume {t : ℝ | (y : E) + t • e ∈ s} = 0 := nonpos_iff_eq_zero.1 (not_lt.1 hy)
      simp [ℓ, measureReal_def, h0]
    have hm_Dc : Tendsto (fun k => ∫ y in Dᶜ, m k y) atTop (𝓝 0) := by
      rw [← hℓ_Dc]
      refine tendsto_iff_norm_sub_tendsto_zero.2 <|
        squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
          (by simpa using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hm_L1)
      rw [← integral_sub (hm_int k).integrableOn hℓ.integrableOn]
      exact (norm_integral_le_integral_norm _).trans <|
        (setIntegral_le_integral ((hm_int k).sub hℓ).norm
          (.of_forall fun _ => norm_nonneg _)).trans_eq
          (integral_norm_eq_lintegral_eNorm ((hm_int k).sub hℓ).aestronglyMeasurable)
    simpa [integral_const_mul, mul_zero] using hm_Dc.const_mul Mψ
  have hlim3 : Tendsto (fun k => ∫ y in Dᶜ, Gn k y) atTop (𝓝 (∫ y in Dᶜ, ‖g y‖)) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 <|
      squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
        (by simpa using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hG_L1)
    rw [← integral_sub (hGn_int k).integrableOn hg_int.norm.integrableOn]
    exact (norm_integral_le_integral_norm _).trans <|
      (setIntegral_le_integral ((hGn_int k).sub hg_int.norm).norm
        (.of_forall fun _ => norm_nonneg _)).trans_eq
        (integral_norm_eq_lintegral_eNorm ((hGn_int k).sub hg_int.norm).aestronglyMeasurable)
  exact le_of_tendsto_of_tendsto
    (tendsto_integral_divergenceCLM_subgraph_mollified e he hs hfin ψ)
    (by simpa only [zero_add, steinerFunctional] using
      (hlim1.add (hlim2.add hlim3)).add_const (ω.real univ))
    (.of_forall hstep)

/-- Construct the optimal Borel vector field `Φ` on `H` for the localized slicing lower bound and
evaluate its integrals against `D₀`, `A₀`, `g`, and the singular variation `ω`. -/
private theorem exists_optimal_transverse_field {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {ℓ : H → ℝ} (hℓ : Integrable ℓ volume) (hTV : totalVariationOn volume ⊤ ℓ ≠ ∞)
    {D₀ A₀ : Set H} (hD₀m : MeasurableSet D₀) (hA₀m : MeasurableSet A₀) (hAD : A₀ ⊆ D₀)
    (hD₀fin : volume D₀ ≠ ∞) :
    let ν : Measure (⊤ : Opens H) := volume.comap Subtype.val
    let g : H → H := fun y => acDerivativeDensity volume ⊤ ℓ ν ⟨y, Opens.mem_top y⟩
    let σ : (⊤ : Opens H) → H := polarDensity volume ⊤ ℓ
    let ω : Measure (⊤ : Opens H) := (variationMeasure volume ⊤ ℓ).singularPart ν
    ∃ Φ : H → H, Measurable Φ ∧ (∀ y, ‖Φ y‖ ≤ 1) ∧
      (2 * ∫ y in D₀, √(1 - ‖Φ y‖ ^ 2)) - (∫ y : H, ⟪Φ y, g y⟫) =
        (∫ y in D₀, √(4 + ‖g y‖ ^ 2)) + (∫ y in D₀ᶜ, ‖g y‖) ∧
      2 * (∫ y in A₀, √(1 - ‖Φ y‖ ^ 2)) = (∫ y in A₀, 4 / √(4 + ‖g y‖ ^ 2)) ∧
      -(∫ x : (⊤ : Opens H), ⟪Φ x, σ x⟫ ∂ω) = ω.real univ := by
  intro ν g σ ω
  classical
  let e_top := topOpensEquiv H
  obtain ⟨_, _, hg_int, _⟩ := topOpens_bv_facts hℓ hTV
  have hg_meas : Measurable g := (measurable_acDerivativeDensity ν).comp e_top.measurable
  have hσ_meas : Measurable (fun y : H => σ (e_top y)) :=
    measurable_polarDensity.comp e_top.measurable
  -- Separate the singular support `S` (Lebesgue-null, carrying `ω`) from the Lebesgue part.
  have hms := Measure.mutuallySingular_singularPart (variationMeasure volume ⊤ ℓ) ν
  set S : Set H := e_top ⁻¹' hms.nullSetᶜ
  have hSm : MeasurableSet S := hms.measurableSet_nullSet.compl.preimage e_top.measurable
  have hS_vol : volume S = 0 := by
    have h0 : (volume.map e_top) hms.nullSetᶜ = 0 :=
      (congrArg (fun μ : Measure (⊤ : Opens H) => μ hms.nullSetᶜ)
        (MeasurableEquiv.comap_symm e_top)).symm.trans hms.measure_compl_nullSet
    rwa [Measure.map_apply e_top.measurable hms.measurableSet_nullSet.compl] at h0
  have hS_ω : ω {x : (⊤ : Opens H) | (x : H) ∉ S} = 0 := by
    convert hms.measure_nullSet using 2
    ext ⟨y, _⟩; simp [S, e_top, topOpensEquiv]
  -- Define `Φ` piecewise on `S`, `D₀ \ S`, and `(S ∪ D₀)ᶜ`.
  set Φ : H → H := S.piecewise (fun y => -(max 1 ‖σ (e_top y)‖)⁻¹ • σ (e_top y))
    (D₀.piecewise (fun y => -(√(4 + ‖g y‖ ^ 2))⁻¹ • g y) (fun y => -‖g y‖⁻¹ • g y))
  have hΦm : Measurable Φ :=
    Measurable.piecewise hSm
      ((((measurable_const (a := (1 : ℝ))).max hσ_meas.norm).inv.neg).smul hσ_meas)
      (Measurable.piecewise hD₀m
        (((Real.continuous_sqrt.measurable.comp
          ((measurable_const (a := (4 : ℝ))).add (hg_meas.norm.pow_const 2))).inv.neg).smul hg_meas)
        (hg_meas.norm.inv.neg.smul hg_meas))
  have hΦ1 (y : H) : ‖Φ y‖ ≤ 1 := by
    by_cases hyS : y ∈ S
    · simp only [Φ, piecewise_eq_of_mem _ _ _ hyS, norm_neg, norm_smul, norm_inv,
        Real.norm_of_nonneg (zero_le_one.trans (le_max_left _ _))]
      exact inv_mul_le_one_of_le₀ (le_max_right _ _) (zero_le_one.trans (le_max_left _ _))
    · simp only [Φ, piecewise_eq_of_notMem _ _ _ hyS]
      by_cases hyD : y ∈ D₀
      · simp only [piecewise_eq_of_mem _ _ _ hyD, norm_neg, norm_smul, norm_inv,
          Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        exact inv_mul_le_one_of_le₀
          ((Real.sqrt_sq (norm_nonneg _)).symm.trans_le (Real.sqrt_le_sqrt (by linarith)))
          (Real.sqrt_nonneg _)
      · simp only [piecewise_eq_of_notMem _ _ _ hyD, norm_neg, norm_smul, norm_inv, norm_norm]
        rcases eq_or_ne ‖g y‖ 0 with h0 | h0 <;> simp [h0]
  -- Evaluate the Lebesgue and singular integrals of `Φ`.
  have hS_ae : ∀ᵐ y : H ∂volume, y ∉ S := compl_mem_ae_iff.2 hS_vol
  have hsqrt_D (y : H) (hyS : y ∉ S) (hyD : y ∈ D₀) :
      √(1 - ‖Φ y‖ ^ 2) = 2 / √(4 + ‖g y‖ ^ 2) := by
    have hpos : 0 < 4 + ‖g y‖ ^ 2 := by positivity
    simp only [Φ, piecewise_eq_of_notMem _ _ _ hyS, piecewise_eq_of_mem _ _ _ hyD, norm_neg,
      norm_smul, norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow,
      Real.sq_sqrt hpos.le]
    have h1 : 1 - (4 + ‖g y‖ ^ 2)⁻¹ * ‖g y‖ ^ 2 = 4 / (4 + ‖g y‖ ^ 2) := by field_simp; ring
    rw [h1, Real.sqrt_div (by norm_num),
      Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num) |>.2 (by norm_num : (4 : ℝ) = 2 ^ 2)]
  have hA_eq : 2 * (∫ y in A₀, √(1 - ‖Φ y‖ ^ 2)) = ∫ y in A₀, 4 / √(4 + ‖g y‖ ^ 2) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_ae hA₀m (hS_ae.mono fun y hyS hyA => by
      rw [hsqrt_D y hyS (hAD hyA)]; ring)
  have hD_int_sq : IntegrableOn (fun y => √(1 - ‖Φ y‖ ^ 2)) D₀ volume :=
    (integrableOn_const (C := (1 : ℝ)) hD₀fin).mono'
      ((Real.continuous_sqrt.measurable.comp
        (measurable_const.sub (hΦm.norm.pow_const 2))).aestronglyMeasurable.restrict)
      (.of_forall fun y => by
        rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_one.2 (by nlinarith [norm_nonneg (Φ y)]))
  have hinner_int : Integrable (fun y : H => ⟪Φ y, g y⟫) volume :=
    hg_int.norm.mono' (hΦm.aestronglyMeasurable.inner hg_meas.aestronglyMeasurable)
      (.of_forall fun y => (norm_inner_le_norm _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) (hΦ1 y)))
  have hcomb : (2 * ∫ y in D₀, √(1 - ‖Φ y‖ ^ 2)) - (∫ y : H, ⟪Φ y, g y⟫) =
      (∫ y in D₀, √(4 + ‖g y‖ ^ 2)) + ∫ y in D₀ᶜ, ‖g y‖ := by
    rw [← integral_const_mul, ← integral_add_compl hD₀m hinner_int]
    have h1 : (∫ y in D₀, 2 * √(1 - ‖Φ y‖ ^ 2)) - (∫ y in D₀, ⟪Φ y, g y⟫) =
        ∫ y in D₀, √(4 + ‖g y‖ ^ 2) := by
      rw [← integral_sub (hD_int_sq.const_mul 2) hinner_int.integrableOn]
      refine setIntegral_congr_ae hD₀m (hS_ae.mono fun y hyS hyD => ?_)
      rw [hsqrt_D y hyS hyD]
      simp only [Φ, piecewise_eq_of_notMem _ _ _ hyS, piecewise_eq_of_mem _ _ _ hyD,
        real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
      have h4g : 0 ≤ 4 + ‖g y‖ ^ 2 := by positivity
      linarith [Real.sq_sqrt h4g]
    have h2 : -(∫ y in D₀ᶜ, ⟪Φ y, g y⟫) = ∫ y in D₀ᶜ, ‖g y‖ := by
      rw [← integral_neg]
      refine setIntegral_congr_ae hD₀m.compl (hS_ae.mono fun y hyS hyDc => ?_)
      simp only [Φ, piecewise_eq_of_notMem _ _ _ hyS, piecewise_eq_of_notMem _ _ _ hyDc,
        real_inner_smul_left, real_inner_self_eq_norm_sq]
      rcases eq_or_ne ‖g y‖ 0 with h0 | h0
      · simp [h0]
      · field_simp
    linarith
  have hsing : -(∫ x : (⊤ : Opens H), ⟪Φ x, σ x⟫ ∂ω) = ω.real univ := by
    rw [← integral_neg]
    have hae_ω : ∀ᵐ x : (⊤ : Opens H) ∂ω, -⟪Φ x, σ x⟫ = 1 := by
      filter_upwards [ae_iff.2 hS_ω, ae_mono (Measure.singularPart_le _ _)
        (ae_norm_polarDensity_eq_one (hℓ.locallyIntegrable.locallyIntegrableOn ⊤)
          fun _ _ hK => ⟨⊤, hK, hTV⟩)] with x hxS hx1
      have hΦx : Φ x = -(max 1 ‖σ (e_top x)‖)⁻¹ • σ (e_top x) := piecewise_eq_of_mem _ _ _ hxS
      have hxe : e_top x = x := by ext; rfl
      dsimp only [σ] at hΦx ⊢
      rw [hΦx, hxe, hx1, max_self, inv_one, neg_smul, one_smul,
        inner_neg_left, neg_neg, real_inner_self_eq_norm_sq, hx1, one_pow]
    rw [integral_congr_ae hae_ω, integral_const, smul_eq_mul, mul_one]
  exact ⟨Φ, hΦm, hΦ1, hcomb, hA_eq, hsing⟩

/-- Convergence in `L¹(volume.withDensity (‖g ·‖ₑ))` of norm-at-most-one continuous vector fields
to `Φ` implies convergence of the linear pairings `∫ ⟪ψ j y, g y⟫`. -/
private theorem tendsto_integral_inner_of_tendsto_lintegral_withDensity {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    {g Φ : H → H} (hg_int : Integrable g volume) (hg_meas : Measurable g)
    (hΦm : Measurable Φ) (hΦ1 : ∀ y, ‖Φ y‖ ≤ 1)
    {ψ : ℕ → H → H} (hψc : ∀ j, Continuous (ψ j)) (hψ1 : ∀ j y, ‖ψ j y‖ ≤ 1)
    (hL1 : Tendsto (fun j => ∫⁻ y, ‖Φ y - ψ j y‖ₑ ∂volume.withDensity (fun y => ‖g y‖ₑ))
      atTop (𝓝 0)) :
    Tendsto (fun j => ∫ y : H, ⟪ψ j y, g y⟫) atTop (𝓝 (∫ y : H, ⟪Φ y, g y⟫)) := by
  refine tendsto_iff_norm_sub_tendsto_zero.2 <|
    squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_)
      (by simpa using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL1)
  have hi_ψ : Integrable (fun y => ⟪ψ j y, g y⟫) volume :=
    hg_int.norm.mono' ((hψc j).aestronglyMeasurable.inner hg_int.1)
      (.of_forall fun y => (norm_inner_le_norm _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) (hψ1 j y)))
  have hi_Φ : Integrable (fun y => ⟪Φ y, g y⟫) volume :=
    hg_int.norm.mono' (hΦm.aestronglyMeasurable.inner hg_int.1)
      (.of_forall fun y => (norm_inner_le_norm _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) (hΦ1 y)))
  have hmul_int : Integrable (fun y => ‖Φ y - ψ j y‖ * ‖g y‖) volume :=
    (hg_int.norm.const_mul 2).mono'
      ((hΦm.sub (hψc j).measurable).norm.aestronglyMeasurable.mul hg_int.norm.1)
      (.of_forall fun y => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right
          ((norm_sub_le _ _).trans (by linarith [hΦ1 y, hψ1 j y])) (norm_nonneg _))
  rw [← integral_sub hi_ψ hi_Φ]
  refine (norm_integral_le_integral_norm _).trans <|
    (integral_mono (hi_ψ.sub hi_Φ).norm hmul_int fun y => ?_).trans_eq ?_
  · simp only [Pi.sub_apply, ← inner_sub_left]
    exact (norm_inner_le_norm _ _).trans_eq (by rw [norm_sub_rev])
  · dsimp only [Function.comp_apply]
    rw [← ENNReal.toReal_ofReal (integral_nonneg fun _ => by positivity),
      ofReal_integral_eq_lintegral_ofReal hmul_int (.of_forall fun _ => by positivity),
      lintegral_withDensity_eq_lintegral_mul₀ hg_meas.eNorm.aemeasurable
        (g := fun y => ‖Φ y - ψ j y‖ₑ) (hΦm.sub (hψc j).measurable).eNorm.aemeasurable]
    congr 1; refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm, mul_comm]

/-- Convergence in `L¹(ω.map Subtype.val)` of norm-at-most-one test fields to `Φ` implies
convergence of their pairings against `polarDensity` on the singular variation measure `ω`. -/
private theorem tendsto_integral_inner_polarDensity_of_tendsto_lintegral_map {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H] {ℓ : H → ℝ} (hℓ : Integrable ℓ volume)
    (hTV : totalVariationOn volume ⊤ ℓ ≠ ∞) {Φ : H → H} (hΦm : Measurable Φ)
    (hΦ1 : ∀ y, ‖Φ y‖ ≤ 1) {ψ : ℕ → 𝓓(⊤, H)} (hψ1 : ∀ j y, ‖ψ j y‖ ≤ 1)
    (hL1 : Tendsto (fun j => ∫⁻ y, ‖Φ y - ψ j y‖ₑ
      ∂((variationMeasure volume ⊤ ℓ).singularPart (volume.comap Subtype.val)).map Subtype.val)
      atTop (𝓝 0)) :
    let ω := (variationMeasure volume ⊤ ℓ).singularPart (volume.comap Subtype.val)
    Tendsto (fun j => ∫ x : (⊤ : Opens H), ⟪ψ j x, polarDensity volume ⊤ ℓ x⟫ ∂ω) atTop
      (𝓝 (∫ x : (⊤ : Opens H), ⟪Φ x, polarDensity volume ⊤ ℓ x⟫ ∂ω)) := by
  intro ω
  obtain ⟨_, _, _, hω_fin⟩ := topOpens_bv_facts hℓ hTV
  refine tendsto_iff_norm_sub_tendsto_zero.2 <|
    squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_)
      (by simpa using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL1)
  have hfin_top : ∀ K : Set H, IsCompact K → K ⊆ (⊤ : Opens H) →
      ∃ V : Opens H, K ⊆ (V : Set H) ∧ totalVariationOn volume V ℓ ≠ ∞ :=
    fun _ _ hK => ⟨⊤, hK, hTV⟩
  have hi_ψ : Integrable (fun x : (⊤ : Opens H) => ⟪ψ j x, polarDensity volume ⊤ ℓ x⟫) ω :=
    (ψ j).integrable_inner_subtype
      ((locallyIntegrable_polarDensity (μ := volume) (Ω := ⊤) (u := ℓ)).mono_measure
        (Measure.singularPart_le _ _))
  have hi_Φ : Integrable (fun x : (⊤ : Opens H) => ⟪Φ x, polarDensity volume ⊤ ℓ x⟫) ω :=
    Integrable.of_bound ((hΦm.comp measurable_subtype_coe).aestronglyMeasurable.inner
      measurable_polarDensity.aestronglyMeasurable) 1
      (Filter.Eventually.mono (ae_mono (Measure.singularPart_le _ _)
        (ae_norm_polarDensity_eq_one (hℓ.locallyIntegrable.locallyIntegrableOn ⊤)
          hfin_top)) fun x hx => (norm_inner_le_norm _ _).trans
            (by rw [hx, mul_one]; exact hΦ1 _))
  have hb_ω : Integrable (fun x : (⊤ : Opens H) => ‖Φ x - ψ j x‖) ω :=
    Integrable.of_bound (((hΦm.sub (ψ j).continuous.measurable).comp
      measurable_subtype_coe).norm.aestronglyMeasurable) 2
      (.of_forall fun x => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact (norm_sub_le _ _).trans (by linarith [hΦ1 x, hψ1 j x]))
  rw [← integral_sub hi_ψ hi_Φ]
  refine (norm_integral_le_integral_norm _).trans <|
    (integral_mono_ae (hi_ψ.sub hi_Φ).norm hb_ω ?_).trans_eq ?_
  · filter_upwards [ae_mono (Measure.singularPart_le _ _)
      (ae_norm_polarDensity_eq_one (hℓ.locallyIntegrable.locallyIntegrableOn ⊤) hfin_top)]
      with x hx
    simp only [Pi.sub_apply, ← inner_sub_left]
    exact (norm_inner_le_norm _ _).trans (by rw [hx, mul_one, norm_sub_rev])
  · dsimp only [Function.comp_apply]
    rw [← ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _),
      ofReal_integral_eq_lintegral_ofReal hb_ω (.of_forall fun _ => norm_nonneg _),
      lintegral_map (f := fun y => ‖Φ y - ψ j y‖ₑ)
        (hΦm.sub (ψ j).continuous.measurable).eNorm measurable_subtype_coe]
    simp_rw [ofReal_norm]; rfl

/-- Approximate a bounded Borel field `Φ` on `H` by norm-at-most-one test vector fields whose
nonlinear and linear pairings on `D₀`, `A₀`, `g`, and `ω` converge to those of `Φ`. -/
private theorem exists_testFunction_seq_tendsto_pairings {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {ℓ : H → ℝ} (hℓ : Integrable ℓ volume) (hTV : totalVariationOn volume ⊤ ℓ ≠ ∞)
    {D₀ A₀ : Set H} (hAD : A₀ ⊆ D₀) (hD₀fin : volume D₀ ≠ ∞) (hA₀fin : volume A₀ ≠ ∞)
    {Φ : H → H} (hΦm : Measurable Φ) (hΦ1 : ∀ y, ‖Φ y‖ ≤ 1) :
    let ν : Measure (⊤ : Opens H) := volume.comap Subtype.val
    let g : H → H := fun y => acDerivativeDensity volume ⊤ ℓ ν ⟨y, Opens.mem_top y⟩
    let ω : Measure (⊤ : Opens H) := (variationMeasure volume ⊤ ℓ).singularPart ν
    ∃ ψ : ℕ → 𝓓(⊤, H), (∀ j y, ‖ψ j y‖ ≤ 1) ∧
      Tendsto (fun j => ∫ y in D₀, √(1 - ‖ψ j y‖ ^ 2)) atTop
        (𝓝 (∫ y in D₀, √(1 - ‖Φ y‖ ^ 2))) ∧
      Tendsto (fun j => ∫ y in A₀, √(1 - ‖ψ j y‖ ^ 2)) atTop
        (𝓝 (∫ y in A₀, √(1 - ‖Φ y‖ ^ 2))) ∧
      Tendsto (fun j => ∫ y : H, ⟪ψ j y, g y⟫) atTop (𝓝 (∫ y : H, ⟪Φ y, g y⟫)) ∧
      Tendsto (fun j => ∫ x : (⊤ : Opens H), ⟪ψ j x, polarDensity volume ⊤ ℓ x⟫ ∂ω) atTop
        (𝓝 (∫ x : (⊤ : Opens H), ⟪Φ x, polarDensity volume ⊤ ℓ x⟫ ∂ω)) := by
  intro ν g ω
  obtain ⟨_, _, hg_int, hω_fin⟩ := topOpens_bv_facts hℓ hTV
  have hg_meas : Measurable g :=
    (measurable_acDerivativeDensity ν).comp (topOpensEquiv H).measurable
  -- Approximate `Φ` in `L¹(Θ)` where `Θ` simultaneously controls `D₀`, `‖g‖ dy`, and `ω`.
  have : IsFiniteMeasure (ω.map Subtype.val) := Measure.isFiniteMeasure_map ω Subtype.val
  have : IsFiniteMeasure (volume.restrict D₀) :=
    ⟨by rwa [Measure.restrict_apply_univ, lt_top_iff_ne_top]⟩
  have : IsFiniteMeasure (volume.withDensity fun y => ‖g y‖ₑ) :=
    isFiniteMeasure_withDensity (hasFiniteIntegral_iff_eNorm.1 hg_int.2).ne
  let Θ : Measure H := volume.restrict D₀ + volume.withDensity (fun y => ‖g y‖ₑ) + ω.map Subtype.val
  have hΦ_Θ : Integrable Φ Θ := Integrable.of_bound hΦm.aestronglyMeasurable 1 (.of_forall hΦ1)
  have hεk (k : ℕ) : ENNReal.ofReal (1 / (k + 1 : ℝ)) ≠ 0 := by positivity
  choose φ hφ1 hφ_err using fun k : ℕ =>
    hΦ_Θ.exists_testFunction_top_lintegral_sub_le_and_norm_le (n := ⊤) zero_le_one
      (.of_forall hΦ1) (hεk k)
  have hΘ_lim : Tendsto (fun k => ∫⁻ y, ‖Φ y - φ k y‖ₑ ∂Θ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds (x := (0 : ℝ≥0∞)))
      (by simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
      (fun _ => zero_le) hφ_err
  -- Extract a subsequence converging almost everywhere on `D₀` for dominated convergence.
  have hD₀_L1 : Tendsto (fun k => ∫⁻ y in D₀, ‖Φ y - φ k y‖ₑ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds (x := (0 : ℝ≥0∞))) hΘ_lim
      (fun _ => zero_le) fun k => lintegral_mono'
        ((Measure.le_add_right le_rfl).trans (Measure.le_add_right le_rfl)) le_rfl
  obtain ⟨κ, hκ, hae_D₀⟩ := exists_strictMono_ae_tendsto_zero_of_tendsto_lintegral
    (fun k => (hΦm.sub (φ k).continuous.measurable).eNorm.aemeasurable) hD₀_L1
  have hpt_D₀ : ∀ᵐ y ∂volume.restrict D₀,
      Tendsto (fun j => √(1 - ‖φ (κ j) y‖ ^ 2)) atTop (𝓝 √(1 - ‖Φ y‖ ^ 2)) := by
    filter_upwards [hae_D₀] with y hy
    have hnorm : Tendsto (fun j => dist (φ (κ j) y) (Φ y)) atTop (𝓝 0) := by
      have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hy
      simpa only [Function.comp_def, Pi.sub_apply, ← ofReal_norm, norm_nonneg,
        ENNReal.toReal_ofReal, ENNReal.toReal_zero, dist_eq_norm, norm_sub_rev] using h1
    exact (Real.continuous_sqrt.comp (continuous_const.sub (continuous_norm.pow 2)))
      |>.continuousAt.tendsto.comp (tendsto_iff_dist_tendsto_zero.2 hnorm)
  have hDCT {S : Set H} (hSfin : volume S ≠ ∞)
      (hpt : ∀ᵐ y ∂volume.restrict S,
        Tendsto (fun j => √(1 - ‖φ (κ j) y‖ ^ 2)) atTop (𝓝 √(1 - ‖Φ y‖ ^ 2))) :
      Tendsto (fun j => ∫ y in S, √(1 - ‖φ (κ j) y‖ ^ 2)) atTop
        (𝓝 (∫ y in S, √(1 - ‖Φ y‖ ^ 2))) :=
    tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun j => (Real.continuous_sqrt.comp (continuous_const.sub
        ((φ (κ j)).continuous.norm.pow 2))).aestronglyMeasurable)
      (integrableOn_const (C := (1 : ℝ)) hSfin)
      (fun j => .of_forall fun y => by
        rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_one.2 (by nlinarith [norm_nonneg (φ (κ j) y)])) hpt
  refine ⟨fun j => φ (κ j), fun j => hφ1 (κ j), hDCT hD₀fin hpt_D₀,
    hDCT hA₀fin (ae_mono (Measure.restrict_mono hAD le_rfl) hpt_D₀), ?_, ?_⟩
  · exact tendsto_integral_inner_of_tendsto_lintegral_withDensity hg_int hg_meas hΦm hΦ1
      (fun j => (φ (κ j)).continuous) (fun j => hφ1 (κ j))
      (tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds (x := (0 : ℝ≥0∞)))
        (hΘ_lim.comp hκ.tendsto_atTop) (fun _ => zero_le) fun j => lintegral_mono'
          ((Measure.le_add_left le_rfl).trans (Measure.le_add_right le_rfl)) le_rfl)
  · exact tendsto_integral_inner_polarDensity_of_tendsto_lintegral_map hℓ hTV hΦm hΦ1
      (fun j => hφ1 (κ j))
      (tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds (x := (0 : ℝ≥0∞)))
        (hΘ_lim.comp hκ.tendsto_atTop) (fun _ => zero_le) fun j => lintegral_mono'
          (Measure.le_add_left le_rfl) le_rfl)

/-- **Lower bound for `perimeter volume ⊤ s` with noninterval excess.** -/
private theorem ofReal_functional_add_setIntegral_le_perimeter (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞) {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) :
    ENNReal.ofReal (steinerFunctional e s +
      ∫ y in A, 4 / √(4 + ‖acDerivativeDensity volume ⊤
        (fun z : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (z : E) + t • e ∈ s})
        (volume.comap Subtype.val) ⟨y, Opens.mem_top y⟩‖ ^ 2)) ≤ perimeter volume ⊤ s := by
  let ℓ : (ℝ ∙ e)ᗮ → ℝ := fun y => volume.real {t : ℝ | (y : E) + t • e ∈ s}
  let D : Set (ℝ ∙ e)ᗮ := {y | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  let ν : Measure (⊤ : Opens (ℝ ∙ e)ᗮ) := volume.comap Subtype.val
  let g : (ℝ ∙ e)ᗮ → (ℝ ∙ e)ᗮ :=
    fun y => acDerivativeDensity volume ⊤ ℓ ν ⟨y, Opens.mem_top y⟩
  let ω : Measure (⊤ : Opens (ℝ ∙ e)ᗮ) := (variationMeasure volume ⊤ ℓ).singularPart ν
  have hℓ : Integrable ℓ volume := integrable_measureReal_lineSection e he hs hfin
  have hTV : totalVariationOn volume ⊤ ℓ ≠ ∞ :=
    ne_top_of_le_ne_top hP (totalVariationOn_measureReal_lineSection_le hs hfin e he)
  obtain ⟨_, hmp, _, _⟩ := topOpens_bv_facts hℓ hTV
  -- Replace `D` and `A` with Borel subsets `A₀ ⊆ D₀` of finite measure agreeing a.e.
  have hDm : NullMeasurableSet D volume :=
    nullMeasurableSet_lt aemeasurable_const (aemeasurable_volume_lineSection e he hs)
  have hDA_vol := two_mul_volume_add_two_mul_volume_le_perimeter_of_noninterval_lineSection
    hs hfin e he hA hbad
  have hDfin : volume D ≠ ∞ := fun htop => by simp [D, htop, hP] at hDA_vol
  obtain ⟨D₀, _, hD₀m, hD₀_ae⟩ := hDm.exists_measurable_subset_ae_eq
  have hAD_ae : (A ∩ D₀ : Set (ℝ ∙ e)ᗮ) =ᵐ[volume] A := by
    filter_upwards [hbad, hD₀_ae] with y hy hyD₀
    simp only [mem_inter_iff]
    refine ⟨And.left, fun hyA => ⟨hyA, ?_⟩⟩
    rw [hyD₀]
    by_contra hyD
    exact hy hyA ∅ ordConnected_empty (ae_eq_empty.2 (nonpos_iff_eq_zero.1 (not_lt.1 hyD)))
  obtain ⟨A₀, hA₀_sub, hA₀m, hA₀_ae⟩ :=
    (hA.inter hD₀m.nullMeasurableSet).exists_measurable_subset_ae_eq
  have hA₀_aeA : A₀ =ᵐ[volume] A := hA₀_ae.trans hAD_ae
  have hD₀fin : volume D₀ ≠ ∞ := (measure_congr hD₀_ae).trans_ne hDfin
  have hA₀fin : volume A₀ ≠ ∞ := ne_top_of_le_ne_top hD₀fin
    (measure_mono (hA₀_sub.trans inter_subset_right))
  -- Construct the optimal Borel field `Φ` and test the localized slicing bound along `ψ_j → Φ`.
  obtain ⟨Φ, hΦm, hΦ1, hcomb, hA_eq, hsing⟩ := exists_optimal_transverse_field hℓ hTV hD₀m hA₀m
    (hA₀_sub.trans inter_subset_right) hD₀fin
  obtain ⟨ψ, hψ1, hDCT_D, hDCT_A, hg_lim, hω_lim⟩ := exists_testFunction_seq_tendsto_pairings
    hℓ hTV (hA₀_sub.trans inter_subset_right) hD₀fin hA₀fin hΦm hΦ1
  have hj_le (j : ℕ) : ENNReal.ofReal
      (((2 * ∫ y in D₀, √(1 - ‖ψ j y‖ ^ 2)) - (∫ y : (ℝ ∙ e)ᗮ, ⟪ψ j y, g y⟫) -
          ∫ x : (⊤ : Opens (ℝ ∙ e)ᗮ), ⟪ψ j x, polarDensity volume ⊤ ℓ x⟫ ∂ω) +
        (2 * ∫ y in A₀, √(1 - ‖ψ j y‖ ^ 2))) ≤ perimeter volume ⊤ s := by
    have hslic := two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter
      hs hfin e he hA₀m.nullMeasurableSet
      (hbad.mono fun y hy hy' => hy (hA₀_sub hy').1)
      (ψ j) (hψ1 j)
    have hdiv_eq : ∫ y : (ℝ ∙ e)ᗮ, divergenceCLM (ψ j) y * ℓ y =
        -(∫ y : (ℝ ∙ e)ᗮ, ⟪ψ j y, g y⟫) -
          ∫ x : (⊤ : Opens (ℝ ∙ e)ᗮ), ⟪ψ j x, polarDensity volume ⊤ ℓ x⟫ ∂ω := by
      have h1 :=
        integral_divergenceCLM_mul_eq_neg_integral_inner_acDerivativeDensity_sub_singularPart
          (hℓ.locallyIntegrable.locallyIntegrableOn ⊤) (fun _ _ hK => ⟨⊤, hK, hTV⟩) ν (ψ j)
      rwa [hmp.integral_comp (topOpensEquiv (ℝ ∙ e)ᗮ).symm.measurableEmbedding
        fun y => ⟪ψ j y, g y⟫] at h1
    have hcont_sq : Continuous fun y : (ℝ ∙ e)ᗮ => √(1 - ‖ψ j y‖ ^ 2) :=
      Real.continuous_sqrt.comp (continuous_const.sub ((ψ j).continuous.norm.pow 2))
    have hL_eq {S : Set (ℝ ∙ e)ᗮ} (hSfin : volume S ≠ ∞) :
        2 * (∫⁻ y in S, ENNReal.ofReal √(1 - ‖ψ j y‖ ^ 2)) =
          ENNReal.ofReal (2 * ∫ y in S, √(1 - ‖ψ j y‖ ^ 2)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal
          ((integrableOn_const (C := (1 : ℝ)) hSfin).mono' hcont_sq.aestronglyMeasurable.restrict
            (.of_forall fun y => by
              rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
              exact Real.sqrt_le_one.2 (by nlinarith [norm_nonneg (ψ j y)])))
          (.of_forall fun _ => Real.sqrt_nonneg _),
        ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
    rw [setLIntegral_congr hD₀_ae.symm, hL_eq hD₀fin, hL_eq hA₀fin, hdiv_eq] at hslic
    have hrew : ((2 * ∫ y in D₀, √(1 - ‖ψ j y‖ ^ 2)) - (∫ y : (ℝ ∙ e)ᗮ, ⟪ψ j y, g y⟫) -
        (∫ x : (⊤ : Opens (ℝ ∙ e)ᗮ), ⟪ψ j x, polarDensity volume ⊤ ℓ x⟫ ∂ω)) +
        (2 * ∫ y in A₀, √(1 - ‖ψ j y‖ ^ 2)) =
        ((2 * ∫ y in D₀, √(1 - ‖ψ j y‖ ^ 2)) + (2 * ∫ y in A₀, √(1 - ‖ψ j y‖ ^ 2))) +
          (-(∫ y : (ℝ ∙ e)ᗮ, ⟪ψ j y, g y⟫) -
            ∫ x : (⊤ : Opens (ℝ ∙ e)ᗮ), ⟪ψ j x, polarDensity volume ⊤ ℓ x⟫ ∂ω) := by ring
    rw [hrew]
    exact ENNReal.ofReal_add_le.trans <| (add_le_add ENNReal.ofReal_add_le le_rfl).trans hslic
  have htarget : (((2 * ∫ y in D₀, √(1 - ‖Φ y‖ ^ 2)) - (∫ y : (ℝ ∙ e)ᗮ, ⟪Φ y, g y⟫) -
      ∫ x : (⊤ : Opens (ℝ ∙ e)ᗮ), ⟪Φ x, polarDensity volume ⊤ ℓ x⟫ ∂ω) +
      (2 * ∫ y in A₀, √(1 - ‖Φ y‖ ^ 2))) =
      steinerFunctional e s + ∫ y in A, 4 / √(4 + ‖g y‖ ^ 2) := by
    have hD_c : ∫ y in D₀, √(4 + ‖g y‖ ^ 2) = ∫ y in D, √(4 + ‖g y‖ ^ 2) :=
      setIntegral_congr_set hD₀_ae
    have hDc_c : ∫ y in D₀ᶜ, ‖g y‖ = ∫ y in Dᶜ, ‖g y‖ := setIntegral_congr_set hD₀_ae.compl
    have hA_c : ∫ y in A₀, 4 / √(4 + ‖g y‖ ^ 2) = ∫ y in A, 4 / √(4 + ‖g y‖ ^ 2) :=
      setIntegral_congr_set hA₀_aeA
    dsimp only [steinerFunctional, g, D, ω, ν, ℓ] at hcomb hA_eq hsing hD_c hDc_c hA_c ⊢
    linarith [hcomb, hA_eq, hsing, hD_c, hDc_c, hA_c]
  have hlim : Tendsto
      (fun j => ((2 * ∫ y in D₀, √(1 - ‖ψ j y‖ ^ 2)) - (∫ y : (ℝ ∙ e)ᗮ, ⟪ψ j y, g y⟫) -
          ∫ x : (⊤ : Opens (ℝ ∙ e)ᗮ), ⟪ψ j x, polarDensity volume ⊤ ℓ x⟫ ∂ω) +
        (2 * ∫ y in A₀, √(1 - ‖ψ j y‖ ^ 2)))
      atTop (𝓝 (steinerFunctional e s + ∫ y in A, 4 / √(4 + ‖g y‖ ^ 2))) :=
    htarget ▸ (((hDCT_D.const_mul 2).sub hg_lim).sub hω_lim).add (hDCT_A.const_mul 2)
  exact le_of_tendsto' (ENNReal.tendsto_ofReal hlim) hj_le

/-- **Quantitative localized Steiner perimeter inequality.** For a null-measurable set `s` of
finite volume and finite perimeter, a unit direction `e`, and any null-measurable family
`A ⊆ (ℝ ∙ e)ᗮ` of noninterval parallel sections, the perimeter of the Steiner symmetral plus
`∫_A 4 / √(4 + ‖g(y)‖²) dy` is at most the perimeter of `s`, where `g` is the absolutely
continuous derivative density of the section-length function. -/
theorem perimeter_steinerSymmetrization_add_ofReal_setIntegral_le (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞) {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) :
    perimeter volume ⊤ (steinerSymmetrization e he s) +
        ENNReal.ofReal (∫ y in A, 4 / √(4 + ‖acDerivativeDensity volume ⊤
          (fun z : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (z : E) + t • e ∈ s})
          (volume.comap Subtype.val) ⟨y, Opens.mem_top y⟩‖ ^ 2)) ≤
      perimeter volume ⊤ s := by
  have hDA := two_mul_volume_add_two_mul_volume_le_perimeter_of_noninterval_lineSection
    hs hfin e he hA hbad
  have hDfin : volume {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} ≠ ∞ :=
    fun htop => by simp [htop, hP] at hDA
  have hTV : totalVariationOn volume ⊤
      (fun y : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (y : E) + t • e ∈ s}) ≠ ∞ :=
    ne_top_of_le_ne_top hP (totalVariationOn_measureReal_lineSection_le hs hfin e he)
  have hup := perimeter_steinerSymmetrization_le_ofReal_functional e he hs hfin hDfin hTV
  have hlow := ofReal_functional_add_setIntegral_le_perimeter e he hs hfin hP hA hbad
  have hJ0 : 0 ≤ steinerFunctional e s :=
    add_nonneg (add_nonneg (integral_nonneg fun _ => Real.sqrt_nonneg _)
      (integral_nonneg fun _ => norm_nonneg _)) measureReal_nonneg
  have hA0 : 0 ≤ ∫ y in A, 4 / √(4 + ‖acDerivativeDensity volume ⊤
      (fun z : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (z : E) + t • e ∈ s})
      (volume.comap Subtype.val) ⟨y, Opens.mem_top y⟩‖ ^ 2) :=
    integral_nonneg fun _ => div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  rw [ENNReal.ofReal_add hJ0 hA0] at hlow
  exact (add_le_add hup le_rfl).trans hlow

/-- **Steiner perimeter equality forces interval line sections.** Let `s` be a null-measurable set
of finite volume and finite perimeter, and let `e` be a unit vector. If Steiner symmetrization in
direction `e` preserves the perimeter of `s`, then almost every parallel line section of `s`
agrees almost everywhere with an interval (possibly empty). -/
theorem ae_lineSection_ordConnected_of_perimeter_steinerSymmetrization_eq (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞)
    (heq : perimeter volume ⊤ (steinerSymmetrization e he s) = perimeter volume ⊤ s) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume,
      ∃ I : Set ℝ, I.OrdConnected ∧ {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I := by
  set A : Set (ℝ ∙ e)ᗮ :=
    {y | ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I}
  have hAm : NullMeasurableSet A volume := nullMeasurableSet_noninterval_lineSection hs hfin e he
  have hAfin : volume A ≠ ∞ := fun htop => by
    have h := two_mul_volume_add_two_mul_volume_le_perimeter_of_noninterval_lineSection
      hs hfin e he hAm (.of_forall fun _ => id)
    simp [htop, hP] at h
  have hineq := perimeter_steinerSymmetrization_add_ofReal_setIntegral_le e he hs hfin hP hAm
    (.of_forall fun _ => id)
  rw [heq] at hineq
  let ℓ : (ℝ ∙ e)ᗮ → ℝ := fun y => volume.real {t : ℝ | (y : E) + t • e ∈ s}
  let g : (ℝ ∙ e)ᗮ → (ℝ ∙ e)ᗮ := fun y =>
    acDerivativeDensity volume ⊤ ℓ (volume.comap Subtype.val) ⟨y, Opens.mem_top y⟩
  have hg_meas : Measurable g :=
    (measurable_acDerivativeDensity _).comp measurable_id.subtype_mk
  set w : (ℝ ∙ e)ᗮ → ℝ := fun y => 4 / √(4 + ‖g y‖ ^ 2)
  have hw0 (y) : 0 ≤ w y := div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hw_pos (y) : 0 < w y := div_pos (by norm_num) (Real.sqrt_pos.2 (by positivity))
  have hw_le (y) : w y ≤ 2 := by
    have h2 : (2 : ℝ) ≤ √(4 + ‖g y‖ ^ 2) :=
      Real.le_sqrt_of_sq_le (by linarith [sq_nonneg ‖g y‖] : (2 : ℝ) ^ 2 ≤ 4 + ‖g y‖ ^ 2)
    exact (div_le_div_of_nonneg_left (by norm_num) zero_lt_two h2).trans_eq (by norm_num)
  have hw_int : IntegrableOn w A volume :=
    (integrableOn_const (C := (2 : ℝ)) hAfin).mono'
      (((measurable_const.div (Real.continuous_sqrt.measurable.comp
        (measurable_const.add (hg_meas.norm.pow_const 2)))).aestronglyMeasurable).restrict)
      (.of_forall fun y => by rw [Real.norm_of_nonneg (hw0 y)]; exact hw_le y)
  have h0_ofReal : ENNReal.ofReal (∫ y in A, w y) = 0 :=
    nonpos_iff_eq_zero.1 ((add_le_add_iff_right_of_ne_top hP).1 (by simpa [w] using hineq))
  have hint0 : ∫ y in A, w y = 0 :=
    le_antisymm (ENNReal.ofReal_eq_zero.1 h0_ofReal) (integral_nonneg hw0)
  have hae0 : w =ᵐ[volume.restrict A] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (.of_forall hw0) hw_int).1 hint0
  have hAnull : volume A = 0 := by
    have hfalse : ∀ᵐ _ ∂volume.restrict A, False := hae0.mono fun y hy => (hw_pos y).ne' hy
    rw [ae_iff] at hfalse
    simpa [Measure.restrict_apply_univ] using hfalse
  filter_upwards [compl_mem_ae_iff.2 hAnull] with _ hy
  simpa [A, not_forall, not_not] using hy

/-- **Steiner perimeter equality bounds essential boundary points of parallel sections.** If
`P(S_e s) = P(s) < ∞`, then almost every parallel line section of `s` in direction `e` has at most
two essential boundary points. -/
theorem ae_encard_essentialBoundary_lineSection_le_two_of_perimeter_steinerSymmetrization_eq
    (e : E) (he : ‖e‖ = 1) {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞)
    (heq : perimeter volume ⊤ (steinerSymmetrization e he s) = perimeter volume ⊤ s) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume,
      (essentialBoundary volume {t : ℝ | (y : E) + t • e ∈ s}).encard ≤ 2 := by
  filter_upwards [ae_volume_lineSection_lt_top e he hs hfin,
    ae_lineSection_ordConnected_of_perimeter_steinerSymmetrization_eq e he hs hfin hP heq]
    with _ hyfin hyI
  exact Real.encard_essentialBoundary_le_two_of_ae_eq_ordConnected hyfin.ne hyI

/-- **Steiner perimeter equality makes sections with more than two essential boundary points
transverse-null.** -/
theorem volume_setOf_two_lt_encard_essentialBoundary_lineSection_eq_zero
    (e : E) (he : ‖e‖ = 1) {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞)
    (heq : perimeter volume ⊤ (steinerSymmetrization e he s) = perimeter volume ⊤ s) :
    volume {y : (ℝ ∙ e)ᗮ |
      2 < (essentialBoundary volume {t : ℝ | (y : E) + t • e ∈ s}).encard} = 0 := by
  have hae : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume,
      ¬2 < (essentialBoundary volume {t : ℝ | (y : E) + t • e ∈ s}).encard := by
    filter_upwards
      [ae_encard_essentialBoundary_lineSection_le_two_of_perimeter_steinerSymmetrization_eq
        e he hs hfin hP heq] with _ hy
    exact not_lt.2 hy
  simpa only [ae_iff, Classical.not_not] using hae

end VariationalComparison

end TauCeti
