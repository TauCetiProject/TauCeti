/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Poisson
import Mathlib.Analysis.MeanInequalities
import TauCeti.Analysis.Normed.Lp.PiLp
import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.MeasureTheory.Integral.Bochner.PiLp

/-!
# Complex interpolation of finite vector-valued `ℓ^q` products

For a finite family `i ↦ (X₀ i, X₁ i)` of compatible couples of complex normed spaces and
`1 ≤ q₀, q₁ ≤ ∞`, `TauCeti.CompatibleCouple.piLp q₀ q₁ C` embeds `(PiLp q₀ X₀, PiLp q₁ X₁)` into
`∀ i, V i`. For `0 < θ < 1` and `1 / q = (1 - θ) / q₀ + θ / q₁` (including `∞`), we construct
`[PiLp q₀ X₀, PiLp q₁ X₁]_θ ≃ₗᵢ[ℂ] PiLp q (fun i ↦ [X₀ i, X₁ i]_θ)` without completeness, density
of intersections, or duality (Calderón §13.6; Bergh–Löfström, Theorem 5.1.2).

## Main definitions and results

* `TauCeti.CompatibleCouple.piLp`, `piLp_proj_compat`, `piLpCoord`, `piLpCoord_mk`,
  `piLpCoord_injective`, `piLpComplexMethodEquiv`, and `piLpReflComplexMethodEquiv`.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. **24**
  (1964), 113–190, §13.6; J. Bergh and J. Löfström, *Interpolation Spaces*, Springer, 1976, 5.1.2.
-/

public noncomputable section

open Complex Complex.HadamardThreeLines TauCeti.Complex.HadamardThreeLines
open Filter MeasureTheory Metric Real Set WithLp
open scoped ENNReal Topology ZeroAtInfty

namespace TauCeti.CompatibleCouple

/-! ### Analytic weight rescaling on a single compatible couple -/

private def expWeight (c₀ c₁ γ : ℝ) (z : ℂ) : ℂ :=
  exp (((1 - z) * c₀ + z * c₁ - 1) * γ)

private theorem norm_expWeight (c₀ c₁ γ : ℝ) (z : ℂ) :
    ‖expWeight c₀ c₁ γ z‖ = Real.exp (((1 - z.re) * c₀ + z.re * c₁ - 1) * γ) := by
  have hre : (((1 - z) * c₀ + z * c₁ - 1) * γ).re = ((1 - z.re) * c₀ + z.re * c₁ - 1) * γ := by
    simp
  rw [expWeight, Complex.norm_exp, hre]

private theorem norm_exp_weight_le {c₀ c₁ γ : ℝ} {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    ‖expWeight c₀ c₁ γ z‖ ≤ Real.exp ((|c₀| + |c₁| + 1) * |γ|) := by
  have ⟨h0, h1⟩ := mem_verticalClosedStrip_iff.1 hz
  rw [norm_expWeight]
  refine Real.exp_le_exp.2 <| (le_abs_self _).trans <| (abs_mul _ _).trans_le <|
    mul_le_mul_of_nonneg_right ?_ (abs_nonneg γ)
  have h₀ : |1 - z.re| * |c₀| ≤ |c₀| :=
    mul_le_of_le_one_left (abs_nonneg _) (by rw [abs_of_nonneg (sub_nonneg.2 h1)]; linarith)
  have h₁ : |z.re| * |c₁| ≤ |c₁| :=
    mul_le_of_le_one_left (abs_nonneg _) (by rwa [abs_of_nonneg h0])
  linarith [abs_sub ((1 - z.re) * c₀ + z.re * c₁) 1, abs_add_le ((1 - z.re) * c₀) (z.re * c₁),
    abs_mul (1 - z.re) c₀, abs_mul z.re c₁, abs_one (α := ℝ)]

private theorem exists_weighted_trace {Y₀ Y₁ W : Type*}
    [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀] [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [ContinuousAdd W] [T1Space W]
    (D : CompatibleCouple ℂ Y₀ Y₁ W) {θ c₀ c₁ bi B : ℝ} (hθ : θ ∈ Icc 0 1)
    (hc : (1 - θ) * c₀ + θ * c₁ = 1) (hbi : 0 < bi) (hB : 0 < B)
    {u : D.ComplexMethodSpace θ} (hu : ‖u‖ < bi) :
    ∃ g' : D.stripTraces, ComplexMethodSpace.mk θ g' = u ∧
      (∀ t, ‖g'.val.1 t‖ ≤ B * (bi / B) ^ c₀) ∧
      (∀ t, ‖g'.val.2 t‖ ≤ B * (bi / B) ^ c₁) := by
  obtain ⟨g, rfl, hgb⟩ := ComplexMethodSpace.norm_lt_iff.1 hu
  set γ := Real.log (bi / B)
  have hw_diff : Differentiable ℂ (expWeight c₀ c₁ γ) := by unfold expWeight; fun_prop
  obtain ⟨g', hsmul, hg'₀, hg'₁⟩ := (D.isStripFunction_stripFunction g).exists_smul_of_diffContOnCl
    hw_diff.diffContOnCl fun _ hz ↦ norm_exp_weight_le hz
  have hwθ : expWeight c₀ c₁ γ θ = 1 := by
    have h0 : ((1 - (θ : ℂ)) * c₀ + (θ : ℂ) * c₁ - 1) * γ = 0 := by
      exact_mod_cast (by rw [hc, sub_self, zero_mul] : ((1 - θ) * c₀ + θ * c₁ - 1) * γ = 0)
    simp [expWeight, h0]
  have hbd {c m : ℝ} (hm : m ≤ bi) : Real.exp ((c - 1) * γ) * m ≤ B * (bi / B) ^ c := by
    rw [mul_comm (c - 1), ← Real.rpow_def_of_pos (div_pos hbi hB)]
    exact (mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (div_nonneg hbi.le hB.le) _)).trans_eq
      (by rw [Real.rpow_sub (div_pos hbi hB), Real.rpow_one, div_div_eq_mul_div,
        div_mul_cancel₀ _ hbi.ne', mul_comm])
  refine ⟨⟨g', mem_stripTraces_iff.2 ⟨_, hsmul⟩⟩, ComplexMethodSpace.ext ?_, fun t ↦ ?_, fun t ↦ ?_⟩
  · rw [ComplexMethodSpace.toSum_mk, ComplexMethodSpace.toSum_mk, stripEval_apply, stripEval_apply,
      stripFunction_eq hsmul (by simpa [mem_verticalClosedStrip_iff] using hθ)]
    simp [hwθ]
  · have hre : (t * I : ℂ).re = 0 := by simp
    rw [hg'₀, norm_smul, norm_expWeight, hre, sub_zero, one_mul, zero_mul, add_zero]
    exact hbd ((g.val.1.norm_coe_le_norm t).trans ((norm_fst_le g.val).trans hgb.le))
  · have hre : (1 + t * I : ℂ).re = 1 := by simp
    rw [hg'₁, norm_smul, norm_expWeight, hre, sub_self, zero_mul, zero_add, one_mul]
    exact hbd ((g.val.2.norm_coe_le_norm t).trans ((norm_snd_le g.val).trans hgb.le))

/-! ### The `PiLp` compatible couple -/

section Defs

variable {𝕜 ι : Type*} [Semiring 𝕜] {X₀ X₁ V : ι → Type*}
  [∀ i, NormedAddCommGroup (X₀ i)] [∀ i, Module 𝕜 (X₀ i)]
  [∀ i, NormedAddCommGroup (X₁ i)] [∀ i, Module 𝕜 (X₁ i)]
  [∀ i, AddCommMonoid (V i)] [∀ i, Module 𝕜 (V i)] [∀ i, TopologicalSpace (V i)]

/-- Coordinatewise compatible couple `(PiLp q₀ X₀, PiLp q₁ X₁)` in the product `∀ i, V i`. -/
def piLp (q₀ q₁ : ℝ≥0∞) (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) :
    CompatibleCouple 𝕜 (PiLp q₀ X₀) (PiLp q₁ X₁) (∀ i, V i) where
  embed₀ := ContinuousLinearMap.pi fun i ↦ (C i).embed₀.comp (PiLp.proj q₀ X₀ i)
  embed₁ := ContinuousLinearMap.pi fun i ↦ (C i).embed₁.comp (PiLp.proj q₁ X₁ i)
  embed₀_injective _ _ h := PiLp.ext fun i ↦
    (C i).embed₀_injective (by simpa [PiLp.proj_apply] using congr_fun h i)
  embed₁_injective _ _ h := PiLp.ext fun i ↦
    (C i).embed₁_injective (by simpa [PiLp.proj_apply] using congr_fun h i)

/-- `embed₀` of `CompatibleCouple.piLp` acts coordinatewise. -/
@[simp]
theorem piLp_embed₀_apply (q₀ q₁ : ℝ≥0∞) (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i))
    (x : PiLp q₀ X₀) (i : ι) :
    (piLp q₀ q₁ C).embed₀ x i = (C i).embed₀ (x i) := (rfl)

/-- `embed₁` of `CompatibleCouple.piLp` acts coordinatewise. -/
@[simp]
theorem piLp_embed₁_apply (q₀ q₁ : ℝ≥0∞) (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i))
    (x : PiLp q₁ X₁) (i : ι) :
    (piLp q₀ q₁ C).embed₁ x i = (C i).embed₁ (x i) := (rfl)

end Defs

/-! ### Coordinate projections and inclusions on `[PiLp q₀ X₀, PiLp q₁ X₁]_θ` -/

section ComplexPiLp

variable {ι : Type*} [Fintype ι] {X₀ X₁ V : ι → Type*}
  [∀ i, NormedAddCommGroup (X₀ i)] [∀ i, NormedSpace ℂ (X₀ i)]
  [∀ i, NormedAddCommGroup (X₁ i)] [∀ i, NormedSpace ℂ (X₁ i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, TopologicalSpace (V i)]
  [∀ i, ContinuousAdd (V i)] [∀ i, T1Space (V i)]
  {q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]

omit [∀ i, T1Space (V i)] in
/-- Compatibility of the `i`-th coordinate projections on the intersection space of `piLp`. -/
theorem piLp_proj_compat (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (i : ι)
    (x : (piLp q₀ q₁ C).inter) :
    (C i).fstToSum (PiLp.proj (𝕜 := ℂ) q₀ X₀ i ((piLp q₀ q₁ C).interFst x)) =
      (C i).sndToSum (PiLp.proj (𝕜 := ℂ) q₁ X₁ i ((piLp q₀ q₁ C).interSnd x)) :=
  (C i).sumSpace_ext
    (by simpa [PiLp.proj_apply] using congr_fun ((piLp q₀ q₁ C).embed₀_interFst x) i)

/-- The `i`-th coordinate projection `[PiLp q₀ X₀, PiLp q₁ X₁]_θ →L[ℂ] [X₀ i, X₁ i]_θ`. -/
def piLpCoord (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (i : ι) :
    (piLp q₀ q₁ C).ComplexMethodSpace θ →L[ℂ] (C i).ComplexMethodSpace θ :=
  ComplexMethodSpace.map θ (PiLp.proj (𝕜 := ℂ) q₀ X₀ i) (PiLp.proj (𝕜 := ℂ) q₁ X₁ i)
    (piLp_proj_compat C i)

/-- Applying `piLpCoord` to `mk θ g` projects both boundary traces to coordinate `i`. -/
@[simp]
theorem piLpCoord_mk (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (i : ι) (g : (piLp q₀ q₁ C).stripTraces) :
    piLpCoord θ C i (ComplexMethodSpace.mk θ g) =
      ComplexMethodSpace.mk θ
        (stripTracesMap (PiLp.proj (𝕜 := ℂ) q₀ X₀ i) (PiLp.proj (𝕜 := ℂ) q₁ X₁ i)
          (piLp_proj_compat C i) g) :=
  ComplexMethodSpace.map_mk (PiLp.proj (𝕜 := ℂ) q₀ X₀ i) (PiLp.proj (𝕜 := ℂ) q₁ X₁ i)
    (piLp_proj_compat C i) g

/-- Each coordinate projection `piLpCoord θ C i` has norm at most `1`. -/
theorem norm_piLpCoord_le (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (i : ι)
    (u : (piLp q₀ q₁ C).ComplexMethodSpace θ) :
    ‖piLpCoord θ C i u‖ ≤ ‖u‖ :=
  ComplexMethodSpace.norm_map_le_of_norm_le _ _ _
    (fun x ↦ PiLp.norm_apply_le x i) (fun x ↦ PiLp.norm_apply_le x i) u

/-- In `V i`, `piLpCoord θ C i u` evaluates `(piLp q₀ q₁ C).sumSpaceEmbed` at `i`. -/
@[simp]
theorem sumSpaceEmbed_toSum_piLpCoord (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (i : ι) (u : (piLp q₀ q₁ C).ComplexMethodSpace θ) :
    (C i).sumSpaceEmbed (ComplexMethodSpace.toSum (piLpCoord θ C i u)) =
      (piLp q₀ q₁ C).sumSpaceEmbed (ComplexMethodSpace.toSum u) i := by
  obtain ⟨x₀, x₁, hx⟩ := (piLp q₀ q₁ C).exists_fstToSum_add_sndToSum_eq (ComplexMethodSpace.toSum u)
  rw [piLpCoord, ComplexMethodSpace.toSum_map_of_eq_add _ _ _ hx, ← hx]
  simp [PiLp.proj_apply]

/-- Elements of `[PiLp q₀ X₀, PiLp q₁ X₁]_θ` are determined by their coordinate projections. -/
theorem piLpCoord_injective (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    {u u' : (piLp q₀ q₁ C).ComplexMethodSpace θ}
    (h : ∀ i, piLpCoord θ C i u = piLpCoord θ C i u') : u = u' :=
  ComplexMethodSpace.ext <| (piLp q₀ q₁ C).sumSpaceEmbed_injective <| funext fun i ↦ by
    rw [← sumSpaceEmbed_toSum_piLpCoord, ← sumSpaceEmbed_toSum_piLpCoord, h i]

omit [∀ i, T1Space (V i)] in
private theorem piLp_single_compat [DecidableEq ι]
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (i : ι) (x : (C i).inter) :
    (piLp q₀ q₁ C).fstToSum (PiLp.singleCLM q₀ ℂ X₀ i ((C i).interFst x)) =
      (piLp q₀ q₁ C).sndToSum (PiLp.singleCLM q₁ ℂ X₁ i ((C i).interSnd x)) := by
  refine (piLp q₀ q₁ C).sumSpace_ext <| funext fun j ↦ ?_
  by_cases hij : j = i
  · subst hij; simpa using (C j).embed₀_interFst x
  · simp [hij]

private def piLpSingle [DecidableEq ι] (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (i : ι) : (C i).ComplexMethodSpace θ →L[ℂ] (piLp q₀ q₁ C).ComplexMethodSpace θ :=
  ComplexMethodSpace.map θ (PiLp.singleCLM q₀ ℂ X₀ i) (PiLp.singleCLM q₁ ℂ X₁ i)
    (piLp_single_compat C i)

private theorem sumSpaceEmbed_toSum_piLpSingle [DecidableEq ι] (θ : ℝ)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (i j : ι)
    (u : (C i).ComplexMethodSpace θ) :
    (piLp q₀ q₁ C).sumSpaceEmbed
        (ComplexMethodSpace.toSum (piLpSingle (q₀ := q₀) (q₁ := q₁) θ C i u)) j =
      Pi.single i ((C i).sumSpaceEmbed (ComplexMethodSpace.toSum u)) j := by
  obtain ⟨x₀, x₁, hx⟩ := (C i).exists_fstToSum_add_sndToSum_eq (ComplexMethodSpace.toSum u)
  rw [piLpSingle, ComplexMethodSpace.toSum_map_of_eq_add _ _ _ hx, ← hx]
  by_cases hij : j = i
  · subst hij; simp
  · simp [hij]

private def piLpFromCoord (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (θ : ℝ)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (v : ∀ i, (C i).ComplexMethodSpace θ) : (piLp q₀ q₁ C).ComplexMethodSpace θ :=
  letI := Classical.decEq ι; ∑ i, piLpSingle θ C i (v i)

private theorem piLpCoord_piLpFromCoord (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (v : ∀ i, (C i).ComplexMethodSpace θ) (j : ι) :
    piLpCoord θ C j (piLpFromCoord q₀ q₁ θ C v) = v j := by
  classical
  apply ComplexMethodSpace.ext; apply (C j).sumSpaceEmbed_injective
  rw [sumSpaceEmbed_toSum_piLpCoord, piLpFromCoord, map_sum, map_sum, Finset.sum_apply]
  simp [sumSpaceEmbed_toSum_piLpSingle]

private theorem piLpFromCoord_piLpCoord (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (u : (piLp q₀ q₁ C).ComplexMethodSpace θ) :
    piLpFromCoord q₀ q₁ θ C (fun i ↦ piLpCoord θ C i u) = u :=
  piLpCoord_injective θ C (piLpCoord_piLpFromCoord θ C _)

/-! ### Lower bound via strip Poisson integrals and weighted AM–GM -/

private theorem norm_mk_le_stripPoissonMeasure {Y₀ Y₁ W : Type*}
    [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀] [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [ContinuousAdd W] [T1Space W]
    {D : CompatibleCouple ℂ Y₀ Y₁ W} {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    {gi : D.stripTraces} (hgi₀ : ‖gi.val.1‖ ≤ 1) (hgi₁ : ‖gi.val.2‖ ≤ 1) :
    ‖ComplexMethodSpace.mk θ gi‖ ≤
      (∫ t, ‖gi.val.1 t‖ ^ q₀.toReal ∂stripPoissonMeasure₀ θ) ^ ((1 - θ) * (q₀⁻¹).toReal) *
      (∫ t, ‖gi.val.2 t‖ ^ q₁.toReal ∂stripPoissonMeasure₁ θ) ^ (θ * (q₁⁻¹).toReal) := by
  have hu : ComplexMethodSpace.toSum (ComplexMethodSpace.mk θ gi) = D.stripFunction gi θ :=
    (ComplexMethodSpace.toSum_mk gi).trans (D.stripEval_apply θ gi)
  have hF := D.isStripFunction_stripFunction gi
  by_cases hq₀ : q₀ = ∞ <;> by_cases hq₁ : q₁ = ∞ <;>
    simp only [hq₀, hq₁, ENNReal.inv_top, ENNReal.toReal_zero, mul_zero, Real.rpow_zero,
      one_mul, mul_one, ENNReal.toReal_inv, ← div_eq_mul_inv]
  · exact (ComplexMethodSpace.norm_mk_le gi).trans
      (Submodule.norm_coe gi ▸ norm_prod_le_iff.2 ⟨hgi₀, hgi₁⟩)
  · exact (ComplexMethodSpace.norm_le_norm_fst_rpow_mul_rpow_integral_stripPoissonMeasure hθ
      (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq₁) hF hu).trans
        (mul_le_of_le_one_left (Real.rpow_nonneg (integral_nonneg fun _ ↦ by positivity) _)
          (Real.rpow_le_one (norm_nonneg _) hgi₀ (sub_nonneg.2 hθ.2.le)))
  · exact (ComplexMethodSpace.norm_le_rpow_integral_stripPoissonMeasure_mul_norm_snd_rpow hθ
      (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq₀) hF hu).trans
        (mul_le_of_le_one_right (Real.rpow_nonneg (integral_nonneg fun _ ↦ by positivity) _)
          (Real.rpow_le_one (norm_nonneg _) hgi₁ hθ.1.le))
  · exact ComplexMethodSpace.norm_le_rpow_integral_stripPoissonMeasure hθ
      (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq₀)
      (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq₁) hF hu

private theorem coord_le_poisson {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    {g : (piLp q₀ q₁ C).stripTraces} (hg : ‖g‖ ≤ 1) (i : ι) :
    ‖piLpCoord θ C i (ComplexMethodSpace.mk θ g)‖ ≤
      (∫ t, ‖(g.val.1 t) i‖ ^ q₀.toReal ∂stripPoissonMeasure₀ θ) ^ ((1 - θ) * (q₀⁻¹).toReal) *
      (∫ t, ‖(g.val.2 t) i‖ ^ q₁.toReal ∂stripPoissonMeasure₁ θ) ^ (θ * (q₁⁻¹).toReal) := by
  set gi := stripTracesMap (PiLp.proj (𝕜 := ℂ) q₀ X₀ i) (PiLp.proj (𝕜 := ℂ) q₁ X₁ i)
    (piLp_proj_compat C i) g
  have hgi1 (t : ℝ) : gi.val.1 t = (g.val.1 t) i := by
    rw [stripTracesMap_apply_fst, PiLp.proj_apply]
  have hgi2 (t : ℝ) : gi.val.2 t = (g.val.2 t) i := by
    rw [stripTracesMap_apply_snd, PiLp.proj_apply]
  rw [piLpCoord_mk]; simp_rw [← hgi1, ← hgi2]
  have h1 := (norm_fst_le g.val).trans hg; have h2 := (norm_snd_le g.val).trans hg
  exact norm_mk_le_stripPoissonMeasure (q₀ := q₀) (q₁ := q₁) hθ
    ((ZeroAtInftyContinuousMap.norm_le zero_le_one).2 fun t ↦
      hgi1 t ▸ (PiLp.norm_apply_le _ i).trans ((g.val.1.norm_coe_le_norm t).trans h1))
    ((ZeroAtInftyContinuousMap.norm_le zero_le_one).2 fun t ↦
      hgi2 t ▸ (PiLp.norm_apply_le _ i).trans ((g.val.2.norm_coe_le_norm t).trans h2))

private theorem norm_toLp_piLpCoord_mk_le_one [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    {g : (piLp q₀ q₁ C).stripTraces} (hg : ‖g‖ ≤ 1) :
    ‖toLp q (fun i ↦ piLpCoord θ C i (ComplexMethodSpace.mk θ g))‖ ≤ 1 := by
  by_cases hq_top : q = ∞
  · subst hq_top; rw [PiLp.norm_toLp]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦
      (norm_piLpCoord_le θ C i _).trans ((ComplexMethodSpace.norm_mk_le g).trans hg)
  have := isProbabilityMeasure_stripPoissonMeasure₀ hθ
  have := isProbabilityMeasure_stripPoissonMeasure₁ hθ
  have hq_pos : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq_top
  rw [PiLp.norm_eq_sum hq_pos]
  refine Real.rpow_le_one (Finset.sum_nonneg fun _ _ ↦ by positivity) ?_ (by positivity)
  set α₀ := (1 - θ) * (q₀⁻¹).toReal * q.toReal
  set α₁ := θ * (q₁⁻¹).toReal * q.toReal
  have hα₀ : 0 ≤ α₀ := by have := sub_nonneg.2 hθ.2.le; positivity
  have hα₁ : 0 ≤ α₁ :=
    mul_nonneg (mul_nonneg hθ.1.le ENNReal.toReal_nonneg) hq_pos.le
  have hα : α₀ + α₁ = 1 := by
    linear_combination TauCeti.toReal_mul_inv_add
      (zero_lt_one.trans_le (Fact.out : 1 ≤ q₀)).ne'
      (zero_lt_one.trans_le (Fact.out : 1 ≤ q₁)).ne' hq_top ⟨hθ.1.le, hθ.2.le⟩ hq
  let S₀ : ι → ℝ := fun i ↦ ∫ t, ‖(g.val.1 t) i‖ ^ q₀.toReal ∂stripPoissonMeasure₀ θ
  let S₁ : ι → ℝ := fun i ↦ ∫ t, ‖(g.val.2 t) i‖ ^ q₁.toReal ∂stripPoissonMeasure₁ θ
  have hpt (i : ι) : ‖piLpCoord θ C i (ComplexMethodSpace.mk θ g)‖ ^ q.toReal ≤
      α₀ * S₀ i + α₁ * S₁ i := by
    have hS₀ : 0 ≤ S₀ i := integral_nonneg fun _ ↦ by positivity
    have hS₁ : 0 ≤ S₁ i := integral_nonneg fun _ ↦ by positivity
    refine (Real.rpow_le_rpow (norm_nonneg _) (coord_le_poisson hθ C hg i) hq_pos.le).trans ?_
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hS₀, ← Real.rpow_mul hS₁]
    exact Real.geom_mean_le_arith_mean2_weighted hα₀ hα₁ hS₀ hS₁ hα
  have hsum₀ : α₀ * ∑ i, S₀ i ≤ α₀ := if hq₀ : q₀ = ∞ then by simp [α₀, hq₀] else
    mul_le_of_le_one_right hα₀ <| (sum_integral_norm_rpow_le_rpow (μ := stripPoissonMeasure₀ θ)
      (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq₀)
      (.of_forall fun t ↦ (g.val.1.norm_coe_le_norm t).trans
        ((norm_fst_le g.val).trans hg))).trans_eq (Real.one_rpow _)
  have hsum₁ : α₁ * ∑ i, S₁ i ≤ α₁ := if hq₁ : q₁ = ∞ then by simp [α₁, hq₁] else
    mul_le_of_le_one_right hα₁ <| (sum_integral_norm_rpow_le_rpow (μ := stripPoissonMeasure₁ θ)
      (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq₁)
      (.of_forall fun t ↦ (g.val.2.norm_coe_le_norm t).trans
        ((norm_snd_le g.val).trans hg))).trans_eq (Real.one_rpow _)
  refine (Finset.sum_le_sum fun i _ ↦ hpt i).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; linarith

private theorem norm_toLp_piLpCoord_le [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (u : (piLp q₀ q₁ C).ComplexMethodSpace θ) :
    ‖toLp q (fun i ↦ piLpCoord θ C i u)‖ ≤ ‖u‖ := by
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  set r := ‖u‖ + δ; have hr : 0 < r := add_pos_of_nonneg_of_pos (norm_nonneg u) hδ
  obtain ⟨g, rfl, hgr⟩ := ComplexMethodSpace.norm_lt_iff.1 (lt_add_of_pos_right ‖u‖ hδ)
  let g' : (piLp q₀ q₁ C).stripTraces := (r : ℂ)⁻¹ • g
  have hg'1 : ‖g'‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Complex.norm_of_nonneg hr.le, inv_mul_le_iff₀ hr, mul_one]
    exact hgr.le
  have hsmul : toLp q (fun i ↦ piLpCoord θ C i (ComplexMethodSpace.mk θ g)) =
      (r : ℂ) • toLp q (fun i ↦ piLpCoord θ C i (ComplexMethodSpace.mk θ g')) :=
    PiLp.ext fun i ↦ by simp only [g', ofLp_smul, Pi.smul_apply, map_smul, smul_smul,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hr.ne'), one_smul]
  rw [hsmul, norm_smul, Complex.norm_of_nonneg hr.le]
  exact mul_le_of_le_one_right hr.le (norm_toLp_piLpCoord_mk_le_one hθ hq C hg'1)

/-! ### Upper bound via analytic coordinate weights -/

private theorem norm_piLpFromCoord_le_of_traces {θ B : ℝ}
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (v : ∀ i, (C i).ComplexMethodSpace θ) (g : ∀ i, (C i).stripTraces)
    (hmk : ∀ i, ComplexMethodSpace.mk θ (g i) = v i)
    (h₀ : ∀ t, ‖toLp q₀ (fun j ↦ (g j).val.1 t)‖ ≤ B)
    (h₁ : ∀ t, ‖toLp q₁ (fun j ↦ (g j).val.2 t)‖ ≤ B) :
    ‖piLpFromCoord q₀ q₁ θ C v‖ ≤ B := by
  classical
  have hB : 0 ≤ B := (norm_nonneg _).trans (h₀ 0)
  let G : (piLp q₀ q₁ C).stripTraces :=
    ∑ i, stripTracesMap (PiLp.singleCLM q₀ ℂ X₀ i) (PiLp.singleCLM q₁ ℂ X₁ i)
      (piLp_single_compat C i) (g i)
  have hG_mk : ComplexMethodSpace.mk θ G = piLpFromCoord q₀ q₁ θ C v := by
    rw [piLpFromCoord, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [piLpSingle, ← hmk i, ComplexMethodSpace.map_mk]
  have hG₀ (t : ℝ) : G.val.1 t = toLp q₀ (fun j ↦ (g j).val.1 t) := by
    dsimp only [G]
    rw [Submodule.coe_sum, Prod.fst_sum, ZeroAtInftyContinuousMap.coe_sum, Finset.sum_apply]
    simp_rw [stripTracesMap_apply_fst, PiLp.singleCLM_apply]
    exact PiLp.univ_sum_single (toLp q₀ (fun j ↦ (g j).val.1 t))
  have hG₁ (t : ℝ) : G.val.2 t = toLp q₁ (fun j ↦ (g j).val.2 t) := by
    dsimp only [G]
    rw [Submodule.coe_sum, Prod.snd_sum, ZeroAtInftyContinuousMap.coe_sum, Finset.sum_apply]
    simp_rw [stripTracesMap_apply_snd, PiLp.singleCLM_apply]
    exact PiLp.univ_sum_single (toLp q₁ (fun j ↦ (g j).val.2 t))
  rw [← hG_mk]
  exact (ComplexMethodSpace.norm_mk_le G).trans (Submodule.norm_coe G ▸ norm_prod_le_iff.2
    ⟨(ZeroAtInftyContinuousMap.norm_le hB).2 fun t ↦ (hG₀ t).symm ▸ h₀ t,
      (ZeroAtInftyContinuousMap.norm_le hB).2 fun t ↦ (hG₁ t).symm ▸ h₁ t⟩)

private theorem norm_piLpFromCoord_le_top {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : (∞ : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (v : PiLp ∞ (fun i ↦ (C i).ComplexMethodSpace θ)) :
    ‖piLpFromCoord q₀ q₁ θ C v.ofLp‖ ≤ ‖v‖ := by
  obtain ⟨rfl, rfl⟩ := (eq_top_iff_of_inv_eq hθ hq).1 rfl
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  choose g hg_mk hg_norm using fun i ↦
    ComplexMethodSpace.norm_lt_iff.1 ((PiLp.norm_apply_le v i).trans_lt (lt_add_of_pos_right _ hδ))
  have hb : 0 ≤ ‖v‖ + δ := add_nonneg (norm_nonneg v) hδ.le
  exact norm_piLpFromCoord_le_of_traces C v.ofLp g hg_mk
    (fun t ↦ (PiLp.norm_toLp _).trans_le ((pi_norm_le_iff_of_nonneg hb).2 fun j ↦
      ((g j).val.1.norm_coe_le_norm t).trans ((norm_fst_le (g j).val).trans (hg_norm j).le)))
    (fun t ↦ (PiLp.norm_toLp _).trans_le ((pi_norm_le_iff_of_nonneg hb).2 fun j ↦
      ((g j).val.2.norm_coe_le_norm t).trans ((norm_snd_le (g j).val).trans (hg_norm j).le)))

private theorem norm_piLpFromCoord_le [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (v : PiLp q (fun i ↦ (C i).ComplexMethodSpace θ)) :
    ‖piLpFromCoord q₀ q₁ θ C v.ofLp‖ ≤ ‖v‖ := by
  by_cases hq_top : q = ∞
  · subst hq_top; exact norm_piLpFromCoord_le_top hθ hq C v
  rcases isEmpty_or_nonempty ι with _ | _
  · simp [piLpFromCoord]
  have hq_pos : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq_top
  have hc : (1 - θ) * (q.toReal * (q₀⁻¹).toReal) + θ * (q.toReal * (q₁⁻¹).toReal) = 1 := by
    linear_combination TauCeti.toReal_mul_inv_add
      (zero_lt_one.trans_le (Fact.out : 1 ≤ q₀)).ne'
      (zero_lt_one.trans_le (Fact.out : 1 ≤ q₁)).ne' hq_top ⟨hθ.1.le, hθ.2.le⟩ hq
  have hcont : Continuous fun δ : ℝ ↦ (∑ i, (‖v i‖ + δ) ^ q.toReal) ^ q.toReal⁻¹ :=
    (continuous_finsetSum _ fun _ _ ↦ (continuous_const.add continuous_id).rpow_const fun _ ↦
      Or.inr hq_pos.le).rpow_const fun _ ↦ Or.inr (by positivity)
  refine ge_of_tendsto (by rw [PiLp.norm_eq_sum hq_pos v, one_div]; simpa using
    (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0)))
    (eventually_nhdsWithin_of_forall fun δ hδ ↦ ?_)
  let b : ι → ℝ := fun i ↦ ‖v i‖ + δ
  have hb (i : ι) : 0 < b i := add_pos_of_nonneg_of_pos (norm_nonneg _) hδ
  set B := (∑ i, b i ^ q.toReal) ^ q.toReal⁻¹
  have hB : 0 < B := Real.rpow_pos_of_pos
    (Finset.sum_pos (fun i _ ↦ Real.rpow_pos_of_pos (hb i) _) Finset.univ_nonempty) _
  have hBq : B ^ q.toReal = ∑ i, b i ^ q.toReal :=
    Real.rpow_inv_rpow (Finset.sum_nonneg fun i _ ↦ (Real.rpow_pos_of_pos (hb i) _).le) hq_pos.ne'
  choose g' hg'_mk hg'₀ hg'₁ using fun i ↦
    exists_weighted_trace (C i) ⟨hθ.1.le, hθ.2.le⟩ hc (hb i) hB (lt_add_of_pos_right ‖v i‖ hδ)
  let w : ι → ℝ := fun i ↦ (b i / B) ^ q.toReal
  have hw (i : ι) : 0 ≤ w i := Real.rpow_nonneg (div_nonneg (hb i).le hB.le) _
  have hw_sum : ∑ i, w i = 1 := by
    simp_rw [w, Real.div_rpow (hb _).le hB.le]
    rw [← Finset.sum_div, ← hBq, div_self (Real.rpow_pos_of_pos hB _).ne']
  have hw_eq (j : ι) (a : ℝ) : (b j / B) ^ (q.toReal * a) = w j ^ a :=
    Real.rpow_mul (div_nonneg (hb j).le hB.le) _ _
  exact norm_piLpFromCoord_le_of_traces C v.ofLp g' hg'_mk
    (fun t ↦ (PiLp.norm_le_mul_sum_rpow_inv (zero_lt_one.trans_le (Fact.out : 1 ≤ q₀)).ne' hw hB.le
      (x := toLp q₀ fun j ↦ (g' j).val.1 t)
      fun j ↦ (hg'₀ j t).trans_eq (congrArg (B * ·) (hw_eq j _))).trans_eq (by simp [hw_sum]))
    (fun t ↦ (PiLp.norm_le_mul_sum_rpow_inv (zero_lt_one.trans_le (Fact.out : 1 ≤ q₁)).ne' hw hB.le
      (x := toLp q₁ fun j ↦ (g' j).val.2 t)
      fun j ↦ (hg'₁ j t).trans_eq (congrArg (B * ·) (hw_eq j _))).trans_eq (by simp [hw_sum]))

/-! ### Main linear isometry equivalences -/

/-- **Complex interpolation of finite vector-valued `ℓ^q` products** (Bergh–Löfström, 5.1.2).
For `0 < θ < 1`, `1 ≤ q₀, q₁, q ≤ ∞`, and `1 / q = (1 - θ) / q₀ + θ / q₁`, the coordinate
projections assemble into `[PiLp q₀ X₀, PiLp q₁ X₁]_θ ≃ₗᵢ[ℂ] PiLp q (fun i ↦ [X₀ i, X₁ i]_θ)`. -/
def piLpComplexMethodEquiv [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) :
    (piLp q₀ q₁ C).ComplexMethodSpace θ ≃ₗᵢ[ℂ] PiLp q (fun i ↦ (C i).ComplexMethodSpace θ) :=
  LinearIsometryEquiv.ofBounds
    { toFun u := toLp q (fun i ↦ piLpCoord θ C i u)
      invFun v := piLpFromCoord q₀ q₁ θ C v.ofLp
      left_inv := piLpFromCoord_piLpCoord (q₀ := q₀) (q₁ := q₁) θ C
      right_inv v := PiLp.ext (piLpCoord_piLpFromCoord (q₀ := q₀) (q₁ := q₁) θ C v.ofLp)
      map_add' u u' := PiLp.ext fun i ↦ map_add (piLpCoord θ C i) u u'
      map_smul' c u := PiLp.ext fun i ↦ map_smul (piLpCoord θ C i) c u }
    (norm_toLp_piLpCoord_le hθ hq C) (norm_piLpFromCoord_le hθ hq C)

/-- `piLpComplexMethodEquiv` acts by `piLpCoord` on each coordinate. -/
@[simp]
theorem piLpComplexMethodEquiv_apply [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (u : (piLp q₀ q₁ C).ComplexMethodSpace θ) (i : ι) :
    piLpComplexMethodEquiv hθ hq C u i = piLpCoord θ C i u := (rfl)

/-- Applying `piLpCoord` to `(piLpComplexMethodEquiv hθ hq C).symm v` recovers `v i`. -/
@[simp]
theorem piLpCoord_piLpComplexMethodEquiv_symm [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (v : PiLp q (fun i ↦ (C i).ComplexMethodSpace θ)) (i : ι) :
    piLpCoord θ C i ((piLpComplexMethodEquiv hθ hq C).symm v) = v i :=
  piLpCoord_piLpFromCoord (q₀ := q₀) (q₁ := q₁) θ C v.ofLp i

/-- For `0 ≤ θ ≤ 1`, `[X, X]_θ ≃ₗᵢ[ℂ] X` via evaluation in the ambient space. -/
def ComplexMethodSpace.reflEquiv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {θ : ℝ}
    (hθ : θ ∈ Icc 0 1) : (refl ℂ X).ComplexMethodSpace θ ≃ₗᵢ[ℂ] X where
  toFun u := (refl ℂ X).sumSpaceEmbed (ComplexMethodSpace.toSum u)
  invFun x := ComplexMethodSpace.ofInter θ ⟨(x, x), by simp⟩
  left_inv u := by ext; simp [ComplexMethodSpace.toSum_ofInter hθ]
  right_inv x := by simp [ComplexMethodSpace.toSum_ofInter hθ]
  map_add' u v := by simp
  map_smul' c u := by simp
  norm_map' u := (norm_refl_sumSpaceEmbed (ComplexMethodSpace.toSum u)).trans
    (ComplexMethodSpace.norm_refl u).symm

/-- Applying `reflEquiv` evaluates `toSum u` in `X`. -/
@[simp]
theorem ComplexMethodSpace.reflEquiv_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {θ : ℝ} (hθ : θ ∈ Icc 0 1) (u : (refl ℂ X).ComplexMethodSpace θ) :
    ComplexMethodSpace.reflEquiv hθ u = (refl ℂ X).sumSpaceEmbed (ComplexMethodSpace.toSum u) :=
  (rfl)

/-- The inverse of `reflEquiv` sends `x : X` to the class of `(x, x) ∈ (refl ℂ X).inter`. -/
@[simp]
theorem ComplexMethodSpace.reflEquiv_symm_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {θ : ℝ} (hθ : θ ∈ Icc 0 1) (x : X) :
    (ComplexMethodSpace.reflEquiv hθ).symm x = ComplexMethodSpace.ofInter θ ⟨(x, x), by simp⟩ :=
  (rfl)

/-- In `(refl ℂ X).SumSpace`, `(reflEquiv hθ).symm x` lies over `fstToSum x`. -/
theorem ComplexMethodSpace.toSum_reflEquiv_symm {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] {θ : ℝ} (hθ : θ ∈ Icc 0 1) (x : X) :
    ComplexMethodSpace.toSum ((ComplexMethodSpace.reflEquiv hθ).symm x) =
      (refl ℂ X).fstToSum x := by
  simp [ComplexMethodSpace.reflEquiv_symm_apply, ComplexMethodSpace.toSum_ofInter hθ]

/-- **Constant-fiber complex interpolation of finite `ℓ^q` spaces** (`0 < θ < 1`,
`1 / q = (1 - θ) / q₀ + θ / q₁`). -/
def piLpReflComplexMethodEquiv (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
    [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) :
    (piLp q₀ q₁ fun _ : ι ↦ refl ℂ X).ComplexMethodSpace θ ≃ₗᵢ[ℂ] PiLp q (fun _ : ι ↦ X) :=
  (piLpComplexMethodEquiv hθ hq fun _ : ι ↦ refl ℂ X).trans
    (LinearIsometryEquiv.piLpCongrRight q fun _ ↦ ComplexMethodSpace.reflEquiv ⟨hθ.1.le, hθ.2.le⟩)

/-- `piLpReflComplexMethodEquiv` evaluates each coordinate in `X`. -/
@[simp]
theorem piLpReflComplexMethodEquiv_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (u : (piLp q₀ q₁ fun _ : ι ↦ refl ℂ X).ComplexMethodSpace θ) (i : ι) :
    piLpReflComplexMethodEquiv X hθ hq u i =
      (piLp q₀ q₁ fun _ : ι ↦ refl ℂ X).sumSpaceEmbed (ComplexMethodSpace.toSum u) i := by
  rw [piLpReflComplexMethodEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrRight_apply]
  exact (ComplexMethodSpace.reflEquiv_apply _ _).trans
    (sumSpaceEmbed_toSum_piLpCoord θ (fun _ : ι ↦ refl ℂ X) i u)

/-- The inverse of `piLpReflComplexMethodEquiv` embeds into `ι → X` by coordinate evaluation. -/
@[simp]
theorem sumSpaceEmbed_toSum_piLpReflComplexMethodEquiv_symm {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (v : PiLp q (fun _ : ι ↦ X)) (i : ι) :
    (piLp q₀ q₁ fun _ : ι ↦ refl ℂ X).sumSpaceEmbed
        (ComplexMethodSpace.toSum ((piLpReflComplexMethodEquiv X hθ hq).symm v)) i = v i := by
  rw [← piLpReflComplexMethodEquiv_apply hθ hq, LinearIsometryEquiv.apply_symm_apply]

end ComplexPiLp

end TauCeti.CompatibleCouple

end
