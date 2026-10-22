/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Estimate
public import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.MeasureTheory.Function.Lp.Norm
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Flat traces in `W^{1,p}`

For `1 ≤ p < ∞`, restriction to the hyperplane `{a} × E` extends uniquely to a bounded linear map
`TauCeti.W1p.hyperplaneTrace hp a` from the weak Sobolev space `W^{1,p}(ℝ × E)` to `Lᵖ(E)`. The
ambient product has its Euclidean norm, represented by `WithLp 2`. The trace agrees with
restriction on test functions, has operator norm at most `p ^ (1 / p)`, and sends Sobolev
convergence to convergence of boundary values. The construction uses the whole-space
test-function density theorem and Mathlib's `LinearMap.extendOfNorm`.

The estimate behind it is the `Lʳ` trace inequality for compactly supported `C¹` functions,
`∫ |u(a, y)|ʳ dy ≤ ∫_{x₁ > a} ((r - 1) |u|ʳ + ‖Du‖ʳ)` for `1 ≤ r`
(`TauCeti.integral_hyperplane_abs_rpow_le_integral_halfSpace`), obtained by integrating the
one-dimensional estimate `TauCeti.abs_rpow_le_integral_Ioi` over the normal lines. For `r = 2`
its right side is the `H¹` energy on the half-space, and for `r = 1` it is the `L¹` norm of the
gradient there.

This flat trace is the local model for boundary conditions on strips and on smooth domains.
No pointwise representative of an arbitrary Sobolev function is evaluated: agreement with
classical restriction is first proved on the dense space of test functions.

The proof follows L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.5.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace Topology
open scoped Distributions Gradient ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

private theorem hyperplane_memLp (p : ℝ≥0∞) (a : ℝ)
    (φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ)) :
    MemLp (fun y ↦ φ (WithLp.toLp 2 (a, y))) p volume := by
  have he : IsClosedEmbedding (fun y : E ↦ WithLp.toLp 2 (a, y)) :=
    (WithLp.homeomorphProd 2 ℝ E).symm.isClosedEmbedding.comp
      (.of_isEmbedding_isClosedMap (isEmbedding_prodMkRight a) (isClosedMap_prodMk_left a))
  exact (φ.continuous.comp he.continuous).memLp_of_hasCompactSupport
    (φ.hasCompactSupport.comp_isClosedEmbedding he)

private def hyperplaneTestFunctionₗ (p : ℝ≥0∞) (a : ℝ) :
    𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ) →ₗ[ℝ] Lp ℝ p (volume : Measure E) where
  toFun φ := (hyperplane_memLp p a φ).toLp (fun y ↦ φ (WithLp.toLp 2 (a, y)))
  map_add' φ ψ := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun y ↦ by simp
  map_smul' c φ := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun y ↦ by simp

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The `Lʳ` energy density `(r - 1) |u|ʳ + ‖Du‖ʳ` of a compactly supported `C¹` function is
continuous with compact support. -/
private theorem continuous_rpow_energy {u : WithLp 2 (ℝ × E) → ℝ} (hu : ContDiff ℝ 1 u)
    {r : ℝ} (hr : 1 ≤ r) :
    Continuous fun x ↦ (r - 1) * |u x| ^ r + ‖fderiv ℝ u x‖ ^ r :=
  (continuous_const.mul (hu.continuous.abs.rpow_const fun _ ↦ Or.inr (zero_le_one.trans hr))).add
    ((hu.continuous_fderiv one_ne_zero).norm.rpow_const fun _ ↦ Or.inr (zero_le_one.trans hr))

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem hasCompactSupport_rpow_energy {u : WithLp 2 (ℝ × E) → ℝ}
    (hsupp : HasCompactSupport u) {r : ℝ} (hr : 1 ≤ r) :
    HasCompactSupport fun x ↦ (r - 1) * |u x| ^ r + ‖fderiv ℝ u x‖ ^ r := by
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  exact (hsupp.mono fun x hx hz ↦ hx (by simp [hz, hr0])).add
    ((hsupp.fderiv ℝ).mono fun x hx hz ↦ hx (by
      simp only [hz, norm_zero (E := WithLp 2 (ℝ × E) →L[ℝ] ℝ), Real.zero_rpow hr0]))

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem rpow_energy_nonneg (u : WithLp 2 (ℝ × E) → ℝ) {r : ℝ} (hr : 1 ≤ r)
    (x : WithLp 2 (ℝ × E)) : 0 ≤ (r - 1) * |u x| ^ r + ‖fderiv ℝ u x‖ ^ r :=
  add_nonneg (mul_nonneg (sub_nonneg.2 hr) (Real.rpow_nonneg (abs_nonneg _) _))
    (Real.rpow_nonneg (norm_nonneg (fderiv ℝ u x)) _)

/-- **The one-sided flat `Lʳ` trace inequality.** For `1 ≤ r` and a compactly supported `C¹`
function `u` on `ℝ × E`, the integral of `|u|ʳ` over the hyperplane `{a} × E` is bounded by the
integral of `(r - 1) |u|ʳ + ‖Du‖ʳ` over the half-space `{x | a < x.fst}`. -/
theorem integral_hyperplane_abs_rpow_le_integral_halfSpace
    {u : WithLp 2 (ℝ × E) → ℝ} (hu : ContDiff ℝ 1 u) (hsupp : HasCompactSupport u)
    (a : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    (∫ y : E, |u (WithLp.toLp 2 (a, y))| ^ r) ≤
      ∫ x : WithLp 2 (ℝ × E) in {x | a < (WithLp.ofLp x).1},
        (r - 1) * |u x| ^ r + ‖fderiv ℝ u x‖ ^ r := by
  set F : WithLp 2 (ℝ × E) → ℝ := fun x ↦ (r - 1) * |u x| ^ r + ‖fderiv ℝ u x‖ ^ r with hF
  have hFc : Continuous F := continuous_rpow_energy hu hr
  have hs : HasCompactSupport F := hasCompactSupport_rpow_energy hsupp hr
  have hint : Integrable F volume := hFc.integrable_of_hasCompactSupport hs
  have hprod : Integrable (fun z : ℝ × E ↦ F (WithLp.toLp 2 z)) (volume.prod volume) :=
    (WithLp.volume_preserving_toLp ℝ E).integrable_comp hint.aestronglyMeasurable |>.mpr hint
  have hprodR : Integrable (fun z : ℝ × E ↦ F (WithLp.toLp 2 z))
      ((volume.restrict (Ioi a)).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact hprod.integrableOn
  -- Apply the one-dimensional estimate on each normal line.
  have hline (y : E) : |u (WithLp.toLp 2 (a, y))| ^ r ≤
      ∫ t : ℝ in Ioi a, F (WithLp.toLp 2 (t, y)) := by
    have he : IsClosedEmbedding (fun t : ℝ ↦ WithLp.toLp 2 (t, y)) :=
      (WithLp.homeomorphProd 2 ℝ E).symm.isClosedEmbedding.comp
        (.of_isEmbedding_isClosedMap (isEmbedding_prodMkLeft y) (isClosedMap_prodMk_right y))
    have hpath : ContDiff ℝ 1 (fun t : ℝ ↦ WithLp.toLp 2 (t, y)) :=
      ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.contDiff).comp
        (contDiff_id.prodMk contDiff_const)
    have hg := hu.comp hpath
    have hgs := hsupp.comp_isClosedEmbedding he
    have hd (t : ℝ) : deriv (u ∘ fun s : ℝ ↦ WithLp.toLp 2 (s, y)) t =
        fderiv ℝ u (WithLp.toLp 2 (t, y)) (WithLp.toLp 2 (1, (0 : E))) := by
      have hp : HasDerivAt (fun s : ℝ ↦ WithLp.toLp 2 (s, y))
          (WithLp.toLp 2 (1, (0 : E))) t :=
        ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.hasFDerivAt).comp_hasDerivAt t
          ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
      exact ((hu.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t hp).deriv
    refine (abs_rpow_le_integral_Ioi hg hgs a hr).trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t ↦ add_nonneg
        (mul_nonneg (sub_nonneg.2 hr) (Real.rpow_nonneg (abs_nonneg _) _))
        (Real.rpow_nonneg (abs_nonneg _) _))
      ((hFc.comp he.continuous).integrable_of_hasCompactSupport
        (hs.comp_isClosedEmbedding he)).integrableOn
      (Filter.Eventually.of_forall fun t ↦ ?_))
    have hb := (fderiv ℝ u (WithLp.toLp 2 (t, y))).le_opNorm (WithLp.toLp 2 (1, (0 : E)))
    simp only [WithLp.norm_toLp_fst, norm_one, mul_one, Real.norm_eq_abs] at hb
    simp only [hF, Function.comp_apply, hd t]
    gcongr
  -- Integrate the slice estimates and use the volume-preserving product coordinates.
  calc
    _ ≤ ∫ y : E, ∫ t : ℝ in Ioi a, F (WithLp.toLp 2 (t, y)) :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun y ↦ Real.rpow_nonneg (abs_nonneg _) _)
        hprodR.integral_prod_right (Filter.Eventually.of_forall hline)
    _ = _ := by
      rw [← integral_prod_symm _ hprodR]
      rw [Measure.restrict_prod_eq_prod_univ, Set.prod_univ]
      simpa only [Measure.volume_eq_prod, Set.preimage_ofPred_eq, WithLp.ofLp_toLp,
        Set.Ioi] using
        (WithLp.volume_preserving_toLp ℝ E).setIntegral_preimage_emb
          (MeasurableEquiv.toLp 2 (ℝ × E)).measurableEmbedding F
          {x | a < (WithLp.ofLp x).1}

/-- **The flat `Lʳ` trace inequality.** For `1 ≤ r` and a compactly supported `C¹` function `u`
on `ℝ × E`, the integral of `|u|ʳ` over the hyperplane `{a} × E` is bounded by the integral of
`(r - 1) |u|ʳ + ‖Du‖ʳ` over the whole space. -/
theorem integral_hyperplane_abs_rpow_le_integral
    {u : WithLp 2 (ℝ × E) → ℝ} (hu : ContDiff ℝ 1 u) (hsupp : HasCompactSupport u)
    (a : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    (∫ y : E, |u (WithLp.toLp 2 (a, y))| ^ r) ≤
      ∫ x : WithLp 2 (ℝ × E), (r - 1) * |u x| ^ r + ‖fderiv ℝ u x‖ ^ r :=
  (integral_hyperplane_abs_rpow_le_integral_halfSpace hu hsupp a hr).trans
    (setIntegral_le_integral ((continuous_rpow_energy hu hr).integrable_of_hasCompactSupport
      (hasCompactSupport_rpow_energy hsupp hr))
      (Filter.Eventually.of_forall (rpow_energy_nonneg u hr)))

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On test functions, the `Lᵖ` norm of the restriction to `{a} × E` is at most `p ^ (1 / p)`
times the `W^{1,p}` norm. -/
private theorem norm_hyperplaneTestFunction_le (hp : p ≠ ∞) (a : ℝ)
    (φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ)) :
    ‖hyperplaneTestFunctionₗ p a φ‖ ≤
      p.toReal ^ p.toReal⁻¹ * ‖W1p.ofTestFunctionₗ volume ⊤ p φ‖ := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  set r := p.toReal with hr_def
  have hr : 1 ≤ r := by simpa using ENNReal.toReal_mono hp hp1
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  set w := W1p.ofTestFunctionₗ volume ⊤ p φ
  have hu : ContDiff ℝ 1 (φ : WithLp 2 (ℝ × E) → ℝ) := φ.contDiff.of_le (by simp)
  have hvalue := testFunctionLp_apply_ae (mu := volume) p φ
  have hgrad := gradientTestFunctionLp_apply_ae (mu := volume) p φ
  simp only [Opens.coe_top, Measure.restrict_univ] at hvalue hgrad
  -- The three integrals in the trace inequality, as powers of `Lᵖ` norms.
  have htr : ‖hyperplaneTestFunctionₗ p a φ‖ ^ r = ∫ y : E, |φ (WithLp.toLp 2 (a, y))| ^ r := by
    rw [← Lp.integral_norm_rpow_eq_norm_rpow hp0 hp]
    apply integral_congr_ae
    filter_upwards [(hyperplane_memLp p a φ).coeFn_toLp] with y hy
    simp only [hyperplaneTestFunctionₗ, LinearMap.coe_mk, AddHom.coe_mk, hy, Real.norm_eq_abs,
      hr_def]
  have hv : ∫ x : WithLp 2 (ℝ × E), |φ x| ^ r = ‖W1p.value w‖ ^ r := by
    rw [← Lp.integral_norm_rpow_eq_norm_rpow hp0 hp, W1p.value_ofTestFunctionₗ]
    simp only [Opens.coe_top, Measure.restrict_univ]
    apply integral_congr_ae
    filter_upwards [hvalue] with x hx
    rw [hx, Real.norm_eq_abs]
  have hg : ∫ x : WithLp 2 (ℝ × E), ‖fderiv ℝ φ x‖ ^ r = ‖W1p.gradient w‖ ^ r := by
    rw [← Lp.integral_norm_rpow_eq_norm_rpow hp0 hp, W1p.gradient_ofTestFunctionₗ]
    simp only [Opens.coe_top, Measure.restrict_univ]
    apply integral_congr_ae
    filter_upwards [hgrad] with x hx
    rw [hx, norm_gradient_eq_norm_fderiv]
  have hiv : Integrable (fun x : WithLp 2 (ℝ × E) ↦ |φ x| ^ r) volume :=
    (φ.continuous.abs.rpow_const fun _ ↦ Or.inr hr0.le).integrable_of_hasCompactSupport
      (φ.hasCompactSupport.mono fun x hx hz ↦ hx (by simp [hz, hr0.ne']))
  have hig : Integrable (fun x : WithLp 2 (ℝ × E) ↦ ‖fderiv ℝ φ x‖ ^ r) volume :=
    ((hu.continuous_fderiv one_ne_zero).norm.rpow_const fun _ ↦ Or.inr hr0.le)
      |>.integrable_of_hasCompactSupport ((φ.hasCompactSupport.fderiv ℝ).mono fun x hx hz ↦
        hx (by simp only [hz, norm_zero (E := WithLp 2 (ℝ × E) →L[ℝ] ℝ),
          Real.zero_rpow hr0.ne']))
  have key := integral_hyperplane_abs_rpow_le_integral hu φ.hasCompactSupport a hr
  rw [integral_add (hiv.const_mul _) hig, integral_const_mul, hv, hg, ← htr] at key
  -- Both norms on the right are at most the Sobolev norm.
  have hbound : ‖hyperplaneTestFunctionₗ p a φ‖ ^ r ≤ r * ‖w‖ ^ r := by
    have h1 : ‖W1p.value w‖ ^ r ≤ ‖w‖ ^ r :=
      Real.rpow_le_rpow (norm_nonneg _) (W1p.norm_value_le w) hr0.le
    have h2 : ‖W1p.gradient w‖ ^ r ≤ ‖w‖ ^ r :=
      Real.rpow_le_rpow (norm_nonneg _) (W1p.norm_gradient_le w) hr0.le
    nlinarith [sub_nonneg.2 hr]
  rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (by positivity) hr0,
    Real.mul_rpow (by positivity) (norm_nonneg _), ← Real.rpow_mul hr0.le,
    inv_mul_cancel₀ hr0.ne', Real.rpow_one]
  exact hbound

/-- The `Lᵖ` trace on the hyperplane `{a} × E` of a whole-space `W^{1,p}` function, defined as the
unique continuous extension of restriction of test functions. It is characterized by
`TauCeti.W1p.hyperplaneTrace_ofTestFunction_apply_ae` and `TauCeti.W1p.hyperplaneTrace_unique`.
The exponent is finite because test functions are dense in `W^{1,p}` only for `p < ∞`. -/
def W1p.hyperplaneTrace (_hp : p ≠ ∞) (a : ℝ) :
    W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p →L[ℝ] Lp ℝ p (volume : Measure E) :=
  (hyperplaneTestFunctionₗ p a).extendOfNorm (W1p.ofTestFunctionₗ volume ⊤ p)

/-- On test functions, the hyperplane trace agrees almost everywhere with classical restriction. -/
theorem W1p.hyperplaneTrace_ofTestFunction_apply_ae (hp : p ≠ ∞) (a : ℝ)
    (φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ)) :
    ∀ᵐ y ∂(volume : Measure E),
      W1p.hyperplaneTrace hp a (W1p.ofTestFunctionₗ volume ⊤ p φ) y =
        φ (WithLp.toLp 2 (a, y)) := by
  rw [W1p.hyperplaneTrace, LinearMap.extendOfNorm_eq
    (W1p.denseRange_ofTestFunctionₗ_top (mu := (volume : Measure (WithLp 2 (ℝ × E)))) (p := p) hp)
    ⟨p.toReal ^ p.toReal⁻¹, norm_hyperplaneTestFunction_le hp a⟩]
  exact (hyperplane_memLp p a φ).coeFn_toLp

/-- The flat trace has norm at most `p ^ (1 / p)` times the whole-space `W^{1,p}` norm. -/
theorem W1p.norm_hyperplaneTrace_le (hp : p ≠ ∞) (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p) :
    ‖W1p.hyperplaneTrace hp a u‖ ≤ p.toReal ^ p.toReal⁻¹ * ‖u‖ :=
  (hyperplaneTestFunctionₗ p a).norm_extendOfNorm_apply_le
    (W1p.denseRange_ofTestFunctionₗ_top (mu := (volume : Measure (WithLp 2 (ℝ × E)))) (p := p) hp) _
    (norm_hyperplaneTestFunction_le hp a) u

/-- The operator norm of the hyperplane trace is at most `p ^ (1 / p)`. -/
theorem W1p.opNorm_hyperplaneTrace_le (hp : p ≠ ∞) (a : ℝ) :
    ‖W1p.hyperplaneTrace (E := E) (p := p) hp a‖ ≤ p.toReal ^ p.toReal⁻¹ :=
  LinearMap.opNorm_extendOfNorm_le (f := hyperplaneTestFunctionₗ p a)
    (W1p.denseRange_ofTestFunctionₗ_top (mu := (volume : Measure (WithLp 2 (ℝ × E)))) (p := p) hp)
    (by positivity) (norm_hyperplaneTestFunction_le hp a)

/-- A continuous linear boundary operator agreeing with restriction on every test function is
the hyperplane trace. -/
theorem W1p.hyperplaneTrace_unique (hp : p ≠ ∞) (a : ℝ)
    (T : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p →L[ℝ] Lp ℝ p (volume : Measure E))
    (hT : ∀ φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ),
      ∀ᵐ y ∂(volume : Measure E), T (W1p.ofTestFunctionₗ volume ⊤ p φ) y =
        φ (WithLp.toLp 2 (a, y))) : T = W1p.hyperplaneTrace hp a := by
  apply Eq.symm
  unfold W1p.hyperplaneTrace
  refine LinearMap.extendOfNorm_unique
    (W1p.denseRange_ofTestFunctionₗ_top (mu := (volume : Measure (WithLp 2 (ℝ × E)))) (p := p) hp) _
    (norm_hyperplaneTestFunction_le hp a) T ?_
  ext φ
  filter_upwards [hT φ, (hyperplane_memLp p a φ).coeFn_toLp] with y ht hf
  exact ht.trans hf.symm

end TauCeti
