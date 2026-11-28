/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Poisson
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Refl
public import TauCeti.Analysis.Normed.Interpolation.PiLp
public import TauCeti.Analysis.Normed.Lp.PiLp.Basic
import Mathlib.Analysis.MeanInequalities
import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Density
import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.MeasureTheory.Integral.Bochner.PiLp

/-!
# Complex interpolation of finite vector-valued `ℓ^q` products

For a finite family `i ↦ (X₀ i, X₁ i)` of compatible couples of complex normed spaces and
`1 ≤ q₀, q₁ ≤ ∞`, `TauCeti.CompatibleCouple.piLpFamily q₀ q₁ C` embeds `(PiLp q₀ X₀, PiLp q₁ X₁)`
into `∀ i, V i`. For `0 < θ < 1` and `1 / q = (1 - θ) / q₀ + θ / q₁` (including `∞`), we construct
`[PiLp q₀ X₀, PiLp q₁ X₁]_θ ≃ₗᵢ[ℂ] PiLp q (fun i ↦ [X₀ i, X₁ i]_θ)` without completeness, density
of intersections, or duality (Calderón §13.6; Bergh–Löfström, Theorem 5.1.2).

For a single couple `(X₀, X₁)` (`TauCeti.CompatibleCouple.piLp C ι q₀ q₁`) and all `0 ≤ θ ≤ 1`
(including the endpoints `θ = 0, 1`), we also record the contractive inclusion
`TauCeti.CompatibleCouple.ComplexMethodSpace.ofPiLp : ℓ^q([X₀, X₁]_θ) → [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ`
and the left-inverse coordinate projections
`TauCeti.CompatibleCouple.ComplexMethodSpace.piLpProj`.

## Main definitions and results

* `TauCeti.CompatibleCouple.piLpFamily`, `piLpFamily_proj_compat`, `piLpCoord`, `piLpCoord_mk`,
  `piLpCoord_injective`, `piLpFamily_single_compat`, `piLpSingle`, `norm_piLpSingle`,
  `piLpCoord_piLpSingle_same`, `piLpCoord_piLpSingle_of_ne`, `piLpFromCoord`,
  `piLpCoord_piLpFromCoord`, `piLpFromCoord_piLpCoord`, `piLpComplexMethodEquiv`, and
  `piLpReflComplexMethodEquiv`.
* `TauCeti.CompatibleCouple.ComplexMethodSpace.ofPiLp` and
  `TauCeti.CompatibleCouple.ComplexMethodSpace.piLpProj`: the `0 ≤ θ ≤ 1` inclusion and
  coordinate projections for `C.piLp ι q₀ q₁`.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. **24**
  (1964), 113–190, §13.6; J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*,
  Springer, 1976, §5.1 (Theorem 5.1.2).
-/

public noncomputable section

section Family

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
def piLpFamily (q₀ q₁ : ℝ≥0∞) (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) :
    CompatibleCouple 𝕜 (PiLp q₀ X₀) (PiLp q₁ X₁) (∀ i, V i) where
  embed₀ := ContinuousLinearMap.pi fun i ↦ (C i).embed₀.comp (PiLp.proj q₀ X₀ i)
  embed₁ := ContinuousLinearMap.pi fun i ↦ (C i).embed₁.comp (PiLp.proj q₁ X₁ i)
  embed₀_injective _ _ h := PiLp.ext fun i ↦
    (C i).embed₀_injective (by simpa [PiLp.proj_apply] using congr_fun h i)
  embed₁_injective _ _ h := PiLp.ext fun i ↦
    (C i).embed₁_injective (by simpa [PiLp.proj_apply] using congr_fun h i)

/-- `embed₀` of `CompatibleCouple.piLpFamily` acts coordinatewise. -/
@[simp]
theorem piLpFamily_embed₀_apply (q₀ q₁ : ℝ≥0∞)
    (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (x : PiLp q₀ X₀) (i : ι) :
    (piLpFamily q₀ q₁ C).embed₀ x i = (C i).embed₀ (x i) := (rfl)

/-- `embed₁` of `CompatibleCouple.piLpFamily` acts coordinatewise. -/
@[simp]
theorem piLpFamily_embed₁_apply (q₀ q₁ : ℝ≥0∞)
    (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (x : PiLp q₁ X₁) (i : ι) :
    (piLpFamily q₀ q₁ C).embed₁ x i = (C i).embed₁ (x i) := (rfl)

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
/-- Compatibility of the `i`-th coordinate projections on the intersection space of `piLpFamily`. -/
theorem piLpFamily_proj_compat (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (i : ι)
    (x : (piLpFamily q₀ q₁ C).inter) :
    (C i).fstToSum (PiLp.proj (𝕜 := ℂ) q₀ X₀ i ((piLpFamily q₀ q₁ C).interFst x)) =
      (C i).sndToSum (PiLp.proj (𝕜 := ℂ) q₁ X₁ i ((piLpFamily q₀ q₁ C).interSnd x)) :=
  (C i).sumSpace_ext
    (by simpa [PiLp.proj_apply] using congr_fun ((piLpFamily q₀ q₁ C).embed₀_interFst x) i)

/-- The `i`-th coordinate projection `[PiLp q₀ X₀, PiLp q₁ X₁]_θ →L[ℂ] [X₀ i, X₁ i]_θ`. -/
def piLpCoord (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (i : ι) :
    (piLpFamily q₀ q₁ C).ComplexMethodSpace θ →L[ℂ] (C i).ComplexMethodSpace θ :=
  ComplexMethodSpace.map θ (PiLp.proj (𝕜 := ℂ) q₀ X₀ i) (PiLp.proj (𝕜 := ℂ) q₁ X₁ i)
    (piLpFamily_proj_compat C i)

/-- Applying `piLpCoord` to `mk θ g` projects both boundary traces to coordinate `i`. -/
@[simp]
theorem piLpCoord_mk (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (i : ι) (g : (piLpFamily q₀ q₁ C).stripTraces) :
    piLpCoord θ C i (ComplexMethodSpace.mk θ g) =
      ComplexMethodSpace.mk θ
        (stripTracesMap (PiLp.proj (𝕜 := ℂ) q₀ X₀ i) (PiLp.proj (𝕜 := ℂ) q₁ X₁ i)
          (piLpFamily_proj_compat C i) g) :=
  ComplexMethodSpace.map_mk (PiLp.proj (𝕜 := ℂ) q₀ X₀ i) (PiLp.proj (𝕜 := ℂ) q₁ X₁ i)
    (piLpFamily_proj_compat C i) g

/-- Each coordinate projection `piLpCoord θ C i` has norm at most `1`. -/
theorem norm_piLpCoord_le (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (i : ι)
    (u : (piLpFamily q₀ q₁ C).ComplexMethodSpace θ) :
    ‖piLpCoord θ C i u‖ ≤ ‖u‖ :=
  ComplexMethodSpace.norm_map_le_of_norm_le _ _ _
    (fun x ↦ PiLp.norm_apply_le x i) (fun x ↦ PiLp.norm_apply_le x i) u

/-- In `V i`, `piLpCoord θ C i u` evaluates `(piLpFamily q₀ q₁ C).sumSpaceEmbed` at `i`. -/
@[simp]
theorem sumSpaceEmbed_toSum_piLpCoord (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (i : ι) (u : (piLpFamily q₀ q₁ C).ComplexMethodSpace θ) :
    (C i).sumSpaceEmbed (ComplexMethodSpace.toSum (piLpCoord θ C i u)) =
      (piLpFamily q₀ q₁ C).sumSpaceEmbed (ComplexMethodSpace.toSum u) i := by
  obtain ⟨x₀, x₁, hx⟩ :=
    (piLpFamily q₀ q₁ C).exists_fstToSum_add_sndToSum_eq (ComplexMethodSpace.toSum u)
  rw [piLpCoord, ComplexMethodSpace.toSum_map_of_eq_add _ _ _ hx, ← hx]
  simp [PiLp.proj_apply]

/-- Elements of `[PiLp q₀ X₀, PiLp q₁ X₁]_θ` are determined by their coordinate projections. -/
theorem piLpCoord_injective (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    {u u' : (piLpFamily q₀ q₁ C).ComplexMethodSpace θ}
    (h : ∀ i, piLpCoord θ C i u = piLpCoord θ C i u') : u = u' :=
  ComplexMethodSpace.ext <| (piLpFamily q₀ q₁ C).sumSpaceEmbed_injective <| funext fun i ↦ by
    rw [← sumSpaceEmbed_toSum_piLpCoord, ← sumSpaceEmbed_toSum_piLpCoord, h i]

omit [∀ i, T1Space (V i)] in
/-- Compatibility of the `i`-th coordinate inclusions on the intersection space of `piLpFamily`. -/
theorem piLpFamily_single_compat [DecidableEq ι]
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (i : ι) (x : (C i).inter) :
    (piLpFamily q₀ q₁ C).fstToSum (PiLp.singleCLM q₀ ℂ X₀ i ((C i).interFst x)) =
      (piLpFamily q₀ q₁ C).sndToSum (PiLp.singleCLM q₁ ℂ X₁ i ((C i).interSnd x)) := by
  refine (piLpFamily q₀ q₁ C).sumSpace_ext <| funext fun j ↦ ?_
  by_cases hij : j = i
  · subst hij; simpa using (C j).embed₀_interFst x
  · simp [hij]

/-- The `i`-th coordinate inclusion `[X₀ i, X₁ i]_θ →L[ℂ] [PiLp q₀ X₀, PiLp q₁ X₁]_θ`. -/
def piLpSingle [DecidableEq ι] (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (i : ι) : (C i).ComplexMethodSpace θ →L[ℂ] (piLpFamily q₀ q₁ C).ComplexMethodSpace θ :=
  ComplexMethodSpace.map θ (PiLp.singleCLM q₀ ℂ X₀ i) (PiLp.singleCLM q₁ ℂ X₁ i)
    (piLpFamily_single_compat C i)

/-- Applying `piLpSingle` to `mk θ g` places both boundary traces in coordinate `i`. -/
@[simp]
theorem piLpSingle_mk [DecidableEq ι] (θ : ℝ)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (i : ι) (g : (C i).stripTraces) :
    piLpSingle (q₀ := q₀) (q₁ := q₁) θ C i (ComplexMethodSpace.mk θ g) =
      ComplexMethodSpace.mk θ
        (stripTracesMap (PiLp.singleCLM q₀ ℂ X₀ i) (PiLp.singleCLM q₁ ℂ X₁ i)
          (piLpFamily_single_compat C i) g) :=
  ComplexMethodSpace.map_mk (PiLp.singleCLM q₀ ℂ X₀ i) (PiLp.singleCLM q₁ ℂ X₁ i)
    (piLpFamily_single_compat C i) g

/-- In `∀ j, V j`, `piLpSingle θ C i u` embeds as `Pi.single i` of `u`. -/
@[simp]
theorem sumSpaceEmbed_toSum_piLpSingle [DecidableEq ι] (θ : ℝ)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (i j : ι)
    (u : (C i).ComplexMethodSpace θ) :
    (piLpFamily q₀ q₁ C).sumSpaceEmbed
        (ComplexMethodSpace.toSum (piLpSingle (q₀ := q₀) (q₁ := q₁) θ C i u)) j =
      Pi.single i ((C i).sumSpaceEmbed (ComplexMethodSpace.toSum u)) j := by
  obtain ⟨x₀, x₁, hx⟩ := (C i).exists_fstToSum_add_sndToSum_eq (ComplexMethodSpace.toSum u)
  rw [piLpSingle, ComplexMethodSpace.toSum_map_of_eq_add _ _ _ hx, ← hx]
  by_cases hij : j = i
  · subst hij; simp
  · simp [hij]

/-- Projecting `piLpSingle θ C i u` onto coordinate `i` recovers `u`. -/
@[simp]
theorem piLpCoord_piLpSingle_same [DecidableEq ι] (θ : ℝ)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (i : ι)
    (u : (C i).ComplexMethodSpace θ) :
    piLpCoord (q₀ := q₀) (q₁ := q₁) θ C i (piLpSingle θ C i u) = u := by
  refine ComplexMethodSpace.ext ((C i).sumSpaceEmbed_injective ?_)
  simp

/-- Projecting `piLpSingle θ C i u` onto a distinct coordinate `j ≠ i` gives `0`. -/
@[simp]
theorem piLpCoord_piLpSingle_of_ne [DecidableEq ι] (θ : ℝ)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) {i j : ι} (h : j ≠ i)
    (u : (C i).ComplexMethodSpace θ) :
    piLpCoord (q₀ := q₀) (q₁ := q₁) θ C j (piLpSingle θ C i u) = 0 := by
  refine ComplexMethodSpace.ext ((C j).sumSpaceEmbed_injective ?_)
  simp [h]

/-- Each coordinate inclusion `piLpSingle θ C i` preserves norms. -/
@[simp]
theorem norm_piLpSingle [DecidableEq ι] (θ : ℝ)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (i : ι)
    (u : (C i).ComplexMethodSpace θ) :
    ‖piLpSingle (q₀ := q₀) (q₁ := q₁) θ C i u‖ = ‖u‖ :=
  le_antisymm
    (ComplexMethodSpace.norm_map_le_of_norm_le _ _ _
      (fun x ↦ by simp) (fun x ↦ by simp) u)
    (by simpa using norm_piLpCoord_le θ C i (piLpSingle (q₀ := q₀) (q₁ := q₁) θ C i u))

/-- Reassemble a family of interpolated coordinates `(i : ι) → [X₀ i, X₁ i]_θ` into
`[PiLp q₀ X₀, PiLp q₁ X₁]_θ`. -/
def piLpFromCoord (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (θ : ℝ)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (v : ∀ i, (C i).ComplexMethodSpace θ) : (piLpFamily q₀ q₁ C).ComplexMethodSpace θ :=
  letI := Classical.decEq ι; ∑ i, piLpSingle θ C i (v i)

/-- Projecting `piLpFromCoord q₀ q₁ θ C v` onto coordinate `j` recovers `v j`. -/
@[simp]
theorem piLpCoord_piLpFromCoord (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (v : ∀ i, (C i).ComplexMethodSpace θ) (j : ι) :
    piLpCoord θ C j (piLpFromCoord q₀ q₁ θ C v) = v j := by
  classical
  apply ComplexMethodSpace.ext; apply (C j).sumSpaceEmbed_injective
  rw [sumSpaceEmbed_toSum_piLpCoord, piLpFromCoord, map_sum, map_sum, Finset.sum_apply]
  simp [sumSpaceEmbed_toSum_piLpSingle]

/-- Reassembling the coordinate projections `fun i ↦ piLpCoord θ C i u` recovers `u`. -/
@[simp]
theorem piLpFromCoord_piLpCoord (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (u : (piLpFamily q₀ q₁ C).ComplexMethodSpace θ) :
    piLpFromCoord q₀ q₁ θ C (fun i ↦ piLpCoord θ C i u) = u :=
  piLpCoord_injective θ C (piLpCoord_piLpFromCoord θ C _)

/-! ### Lower bound via strip Poisson integrals and weighted AM–GM -/

private theorem ne_zero_of_fact {p : ℝ≥0∞} [Fact (1 ≤ p)] : p ≠ 0 :=
  (zero_lt_one.trans_le Fact.out).ne'

private theorem toReal_pos_of_fact {p : ℝ≥0∞} [Fact (1 ≤ p)] (h : p ≠ ∞) : 0 < p.toReal :=
  ENNReal.toReal_pos ne_zero_of_fact h

private theorem interp_exponent_normalize {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) (hq_top : q ≠ ∞) :
    (1 - θ) * (q₀⁻¹).toReal * q.toReal + θ * (q₁⁻¹).toReal * q.toReal = 1 := by
  linear_combination TauCeti.toReal_mul_inv_add
    (ne_zero_of_fact (p := q₀)) (ne_zero_of_fact (p := q₁)) hq_top ⟨hθ.1.le, hθ.2.le⟩ hq

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
      (toReal_pos_of_fact hq₁) hF hu).trans
        (mul_le_of_le_one_left (Real.rpow_nonneg (integral_nonneg fun _ ↦ by positivity) _)
          (Real.rpow_le_one (norm_nonneg _) hgi₀ (sub_nonneg.2 hθ.2.le)))
  · exact (ComplexMethodSpace.norm_le_rpow_integral_stripPoissonMeasure_mul_norm_snd_rpow hθ
      (toReal_pos_of_fact hq₀) hF hu).trans
        (mul_le_of_le_one_right (Real.rpow_nonneg (integral_nonneg fun _ ↦ by positivity) _)
          (Real.rpow_le_one (norm_nonneg _) hgi₁ hθ.1.le))
  · exact ComplexMethodSpace.norm_le_rpow_integral_stripPoissonMeasure hθ
      (toReal_pos_of_fact hq₀) (toReal_pos_of_fact hq₁) hF hu

private theorem coord_le_poisson {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    {g : (piLpFamily q₀ q₁ C).stripTraces} (hg : ‖g‖ ≤ 1) (i : ι) :
    ‖piLpCoord θ C i (ComplexMethodSpace.mk θ g)‖ ≤
      (∫ t, ‖(g.val.1 t) i‖ ^ q₀.toReal ∂stripPoissonMeasure₀ θ) ^ ((1 - θ) * (q₀⁻¹).toReal) *
      (∫ t, ‖(g.val.2 t) i‖ ^ q₁.toReal ∂stripPoissonMeasure₁ θ) ^ (θ * (q₁⁻¹).toReal) := by
  set gi := stripTracesMap (PiLp.proj (𝕜 := ℂ) q₀ X₀ i) (PiLp.proj (𝕜 := ℂ) q₁ X₁ i)
    (piLpFamily_proj_compat C i) g
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
    {g : (piLpFamily q₀ q₁ C).stripTraces} (hg : ‖g‖ ≤ 1) :
    ‖toLp q (fun i ↦ piLpCoord θ C i (ComplexMethodSpace.mk θ g))‖ ≤ 1 := by
  by_cases hq_top : q = ∞
  · subst hq_top; rw [PiLp.norm_toLp]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦
      (norm_piLpCoord_le θ C i _).trans ((ComplexMethodSpace.norm_mk_le g).trans hg)
  have := isProbabilityMeasure_stripPoissonMeasure₀ hθ
  have := isProbabilityMeasure_stripPoissonMeasure₁ hθ
  have hq_pos : 0 < q.toReal := toReal_pos_of_fact hq_top
  rw [PiLp.norm_eq_sum hq_pos]
  refine Real.rpow_le_one (Finset.sum_nonneg fun _ _ ↦ by positivity) ?_ (by positivity)
  set α₀ := (1 - θ) * (q₀⁻¹).toReal * q.toReal
  set α₁ := θ * (q₁⁻¹).toReal * q.toReal
  have hα₀ : 0 ≤ α₀ := by have := sub_nonneg.2 hθ.2.le; positivity
  have hα₁ : 0 ≤ α₁ :=
    mul_nonneg (mul_nonneg hθ.1.le ENNReal.toReal_nonneg) hq_pos.le
  have hα : α₀ + α₁ = 1 := interp_exponent_normalize hθ hq hq_top
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
      (toReal_pos_of_fact hq₀)
      (.of_forall fun t ↦ (g.val.1.norm_coe_le_norm t).trans
        ((norm_fst_le g.val).trans hg))).trans_eq (Real.one_rpow _)
  have hsum₁ : α₁ * ∑ i, S₁ i ≤ α₁ := if hq₁ : q₁ = ∞ then by simp [α₁, hq₁] else
    mul_le_of_le_one_right hα₁ <| (sum_integral_norm_rpow_le_rpow (μ := stripPoissonMeasure₁ θ)
      (toReal_pos_of_fact hq₁)
      (.of_forall fun t ↦ (g.val.2.norm_coe_le_norm t).trans
        ((norm_snd_le g.val).trans hg))).trans_eq (Real.one_rpow _)
  refine (Finset.sum_le_sum fun i _ ↦ hpt i).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; linarith

private theorem norm_toLp_piLpCoord_le [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (u : (piLpFamily q₀ q₁ C).ComplexMethodSpace θ) :
    ‖toLp q (fun i ↦ piLpCoord θ C i u)‖ ≤ ‖u‖ := by
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  set r := ‖u‖ + δ; have hr : 0 < r := add_pos_of_nonneg_of_pos (norm_nonneg u) hδ
  obtain ⟨g, rfl, hgr⟩ := ComplexMethodSpace.norm_lt_iff.1 (lt_add_of_pos_right ‖u‖ hδ)
  let g' : (piLpFamily q₀ q₁ C).stripTraces := (r : ℂ)⁻¹ • g
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
  let G : (piLpFamily q₀ q₁ C).stripTraces :=
    ∑ i, stripTracesMap (PiLp.singleCLM q₀ ℂ X₀ i) (PiLp.singleCLM q₁ ℂ X₁ i)
      (piLpFamily_single_compat C i) (g i)
  have hG_mk : ComplexMethodSpace.mk θ G = piLpFromCoord q₀ q₁ θ C v := by
    rw [piLpFromCoord, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [piLpSingle, ← hmk i, ComplexMethodSpace.map_mk]
  have hG₀ (t : ℝ) : G.val.1 t = toLp q₀ (fun j ↦ (g j).val.1 t) := by
    dsimp only [G]
    rw [Submodule.coe_sum, Prod.fst_sum, FunLike.coe_sum, Finset.sum_apply]
    simp_rw [stripTracesMap_apply_fst, PiLp.singleCLM_apply]
    exact PiLp.univ_sum_single (toLp q₀ (fun j ↦ (g j).val.1 t))
  have hG₁ (t : ℝ) : G.val.2 t = toLp q₁ (fun j ↦ (g j).val.2 t) := by
    dsimp only [G]
    rw [Submodule.coe_sum, Prod.snd_sum, FunLike.coe_sum, Finset.sum_apply]
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
  have hq_pos : 0 < q.toReal := toReal_pos_of_fact hq_top
  have hc : (1 - θ) * (q.toReal * (q₀⁻¹).toReal) + θ * (q.toReal * (q₁⁻¹).toReal) = 1 := by
    linear_combination interp_exponent_normalize hθ hq hq_top
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
    (fun t ↦ (PiLp.norm_le_mul_sum_rpow_inv (ne_zero_of_fact (p := q₀)) hw hB.le
      (x := toLp q₀ fun j ↦ (g' j).val.1 t)
      fun j ↦ (hg'₀ j t).trans_eq (congrArg (B * ·) (hw_eq j _))).trans_eq (by simp [hw_sum]))
    (fun t ↦ (PiLp.norm_le_mul_sum_rpow_inv (ne_zero_of_fact (p := q₁)) hw hB.le
      (x := toLp q₁ fun j ↦ (g' j).val.2 t)
      fun j ↦ (hg'₁ j t).trans_eq (congrArg (B * ·) (hw_eq j _))).trans_eq (by simp [hw_sum]))

/-! ### Main linear isometry equivalences -/

/-- **Complex interpolation of finite vector-valued `ℓ^q` products** (Bergh–Löfström, 5.1.2).
For `0 < θ < 1`, `1 ≤ q₀, q₁, q ≤ ∞`, and `1 / q = (1 - θ) / q₀ + θ / q₁`, the coordinate
projections assemble into `[PiLp q₀ X₀, PiLp q₁ X₁]_θ ≃ₗᵢ[ℂ] PiLp q (fun i ↦ [X₀ i, X₁ i]_θ)`. -/
def piLpComplexMethodEquiv [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) :
    (piLpFamily q₀ q₁ C).ComplexMethodSpace θ ≃ₗᵢ[ℂ]
      PiLp q (fun i ↦ (C i).ComplexMethodSpace θ) :=
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
    (u : (piLpFamily q₀ q₁ C).ComplexMethodSpace θ) (i : ι) :
    piLpComplexMethodEquiv hθ hq C u i = piLpCoord θ C i u := (rfl)

/-- Applying `piLpCoord` to `(piLpComplexMethodEquiv hθ hq C).symm v` recovers `v i`. -/
@[simp]
theorem piLpCoord_piLpComplexMethodEquiv_symm [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (v : PiLp q (fun i ↦ (C i).ComplexMethodSpace θ)) (i : ι) :
    piLpCoord θ C i ((piLpComplexMethodEquiv hθ hq C).symm v) = v i :=
  piLpCoord_piLpFromCoord (q₀ := q₀) (q₁ := q₁) θ C v.ofLp i

/-- **Constant-fiber complex interpolation of finite `ℓ^q` spaces** (`0 < θ < 1`,
`1 / q = (1 - θ) / q₀ + θ / q₁`). -/
def piLpReflComplexMethodEquiv (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
    [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) :
    (piLpFamily q₀ q₁ fun _ : ι ↦ refl ℂ X).ComplexMethodSpace θ ≃ₗᵢ[ℂ]
      PiLp q (fun _ : ι ↦ X) :=
  (piLpComplexMethodEquiv hθ hq fun _ : ι ↦ refl ℂ X).trans
    (LinearIsometryEquiv.piLpCongrRight q fun _ ↦ ComplexMethodSpace.reflEquiv ⟨hθ.1.le, hθ.2.le⟩)

/-- `piLpReflComplexMethodEquiv` evaluates each coordinate in `X`. -/
@[simp]
theorem piLpReflComplexMethodEquiv_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (u : (piLpFamily q₀ q₁ fun _ : ι ↦ refl ℂ X).ComplexMethodSpace θ) (i : ι) :
    piLpReflComplexMethodEquiv X hθ hq u i =
      (piLpFamily q₀ q₁ fun _ : ι ↦ refl ℂ X).sumSpaceEmbed (ComplexMethodSpace.toSum u) i := by
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
    (piLpFamily q₀ q₁ fun _ : ι ↦ refl ℂ X).sumSpaceEmbed
        (ComplexMethodSpace.toSum ((piLpReflComplexMethodEquiv X hθ hq).symm v)) i = v i := by
  rw [← piLpReflComplexMethodEquiv_apply hθ hq, LinearIsometryEquiv.apply_symm_apply]

end ComplexPiLp

end TauCeti.CompatibleCouple

end Family

open Complex Complex.HadamardThreeLines Set
open scoped ENNReal

namespace TauCeti.CompatibleCouple

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  {C : CompatibleCouple ℂ X₀ X₁ V} {ι : Type*} [Fintype ι]
  {q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] {θ : ℝ}

/-! ### The scalar multipliers `b ^ ((z - θ) s)` -/

section Coefficient

/-- On a boundary line `re w = j`, the multiplier `b ^ ((w - θ) s)` turns a bound `‖x‖ ≤ c` with
`c = N b` into `‖b ^ ((w - θ) s) • x‖ ≤ N b ^ r` for the exponent `r = (j - θ) s + 1`. -/
private theorem norm_cpow_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {b N c : ℝ} (hb : 0 < b) (hc : c = N * b) {w : ℂ} {j s r : ℝ} (hw : w.re = j)
    (hr : (j - θ) * s + 1 = r) {x : E} (hx : ‖x‖ ≤ c) :
    ‖(b : ℂ) ^ ((w - θ) * (s : ℂ)) • x‖ ≤ ‖N * b ^ r‖ := by
  have hre : ((w - θ) * (s : ℂ)).re = (j - θ) * s := by
    simp only [mul_re, sub_re, ofReal_re, ofReal_im, mul_zero, sub_zero, hw]
  calc ‖(b : ℂ) ^ ((w - θ) * (s : ℂ)) • x‖ = b ^ ((j - θ) * s) * ‖x‖ := by
        rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hb, hre]
    _ ≤ b ^ ((j - θ) * s) * c := by gcongr
    _ = N * b ^ r := by rw [← hr, Real.rpow_add_one hb.ne', hc]; ring
    _ ≤ ‖N * b ^ r‖ := Real.le_norm_self _

end Coefficient

/-! ### The inclusion `ℓ^q([X₀, X₁]_θ) ⊆ [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` -/

section Inclusion

/-- Coordinatewise bounded-boundary strip functions `F k`, multiplied by entire scalars `m k`
bounded on the strip, assemble into a bounded-boundary strip function `z ↦ (m k z • F k z)_k` of
the couple `(ℓ^{q₀}(X₀), ℓ^{q₁}(X₁))`. -/
private theorem isBoundedStripFunction_sum_sumSingle_smul [DecidableEq ι]
    {F : ι → ℂ → C.SumSpace}
    {g : ι → BoundedContinuousFunction ℝ X₀ × BoundedContinuousFunction ℝ X₁}
    (hF : ∀ k, C.IsBoundedStripFunction (F k) (g k)) {m : ι → ℂ → ℂ}
    (hm : ∀ k, Differentiable ℂ (m k)) {K : ι → ℝ}
    (hK : ∀ k, ∀ z ∈ verticalClosedStrip 0 1, ‖m k z‖ ≤ K k)
    {G : BoundedContinuousFunction ℝ (PiLp q₀ fun _ : ι => X₀) ×
      BoundedContinuousFunction ℝ (PiLp q₁ fun _ : ι => X₁)}
    (hG₀ : ∀ t, G.1 t = WithLp.toLp q₀ fun k => m k (t * I) • (g k).1 t)
    (hG₁ : ∀ t, G.2 t = WithLp.toLp q₁ fun k => m k (1 + t * I) • (g k).2 t) :
    (C.piLp ι q₀ q₁).IsBoundedStripFunction
      (∑ k, fun z => C.sumSingle q₀ q₁ k (m k z • F k z)) G := by
  choose M hM using fun k => (hF k).exists_norm_le
  refine ⟨Finset.sum_induction _ (fun f => DiffContOnCl ℂ f (verticalStrip 0 1))
      (fun _ _ => DiffContOnCl.add) diffContOnCl_const fun k _ =>
        (C.sumSingle q₀ q₁ k).differentiable.comp_diffContOnCl
          ((hm k).diffContOnCl.smul (hF k).diffContOnCl),
    isBounded_iff_forall_norm_le.2 ⟨∑ k : ι, ‖C.sumSingle q₀ q₁ k‖ * (K k * M k), ?_⟩,
    fun t => ?_, fun t => ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [Finset.sum_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    refine ((C.sumSingle q₀ q₁ k).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [norm_smul]
    exact mul_le_mul (hK k z hz) (hM k z hz) (norm_nonneg _) ((norm_nonneg _).trans (hK k z hz))
  · conv_rhs => rw [← PiLp.univ_sum_single (G.1 t)]
    simp [hG₀, map_sum, (hF _).apply_mul_I]
  · conv_rhs => rw [← PiLp.univ_sum_single (G.2 t)]
    simp [hG₁, map_sum, (hF _).apply_one_add_mul_I]

/-- The core estimate: if `c k > ‖u k‖_θ` and the families `(N (c k / N) ^ r_j)_k` have
`ℓ^{q_j}` norm at most `N`, for exponents with `(1 - θ) r₀ + θ r₁ = 1`, then `u` is an element of
`[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` of norm at most `N`. -/
private theorem exists_sumSpaceEmbed_toSum_eq_and_norm_le_of_lt (hθ : θ ∈ Icc 0 1) {r₀ r₁ : ℝ}
    (hr : (1 - θ) * r₀ + θ * r₁ = 1) (u : ι → C.ComplexMethodSpace θ) {c : ι → ℝ}
    (hc : ∀ k, ‖u k‖ < c k) {N : ℝ} (hN : 0 < N)
    (h₀ : ‖WithLp.toLp q₀ fun k => N * (c k / N) ^ r₀‖ ≤ N)
    (h₁ : ‖WithLp.toLp q₁ fun k => N * (c k / N) ^ r₁‖ ≤ N) :
    ∃ v : (C.piLp ι q₀ q₁).ComplexMethodSpace θ,
      (C.piLp ι q₀ q₁).sumSpaceEmbed (ComplexMethodSpace.toSum v) =
        (fun k => C.sumSpaceEmbed (ComplexMethodSpace.toSum (u k))) ∧ ‖v‖ ≤ N := by
  classical
  choose F g hF hFθ hg using fun k =>
    (ComplexMethodSpace.norm_lt_iff_exists_isBoundedStripFunction hθ).1 (hc k)
  have hb (k : ι) : 0 < c k / N := div_pos ((norm_nonneg _).trans_lt (hc k)) hN
  have hcN (k : ι) : c k = N * (c k / N) := by field_simp
  -- the multiplier `(c k / N) ^ ((z - θ) (r₁ - r₀))` of the `k`-th coordinate
  set m : ι → ℂ → ℂ := fun k z => ((c k / N : ℝ) : ℂ) ^ ((z - θ) * ((r₁ - r₀ : ℝ) : ℂ))
  have hm (k : ι) : Differentiable ℂ (m k) :=
    ((differentiable_id.sub_const _).mul_const _).const_cpow (.inl (by exact_mod_cast (hb k).ne'))
  -- on the line `re z = j`, the `k`-th coordinate has norm at most `N (c k / N) ^ r_j`
  have hb₀ (k : ι) (t : ℝ) : ‖m k (t * I) • (g k).1 t‖ ≤ ‖N * (c k / N) ^ r₀‖ :=
    norm_cpow_smul_le (j := 0) (hb k) (hcN k) (by simp) (by linear_combination -hr)
      (((g k).1.norm_coe_le_norm t).trans ((norm_fst_le _).trans (hg k).le))
  have hb₁ (k : ι) (t : ℝ) : ‖m k (1 + t * I) • (g k).2 t‖ ≤ ‖N * (c k / N) ^ r₁‖ :=
    norm_cpow_smul_le (j := 1) (hb k) (hcN k) (by simp) (by linear_combination -hr)
      (((g k).2.norm_coe_le_norm t).trans ((norm_snd_le _).trans (hg k).le))
  -- the boundary traces of the family, of norm at most `N`
  have hG₀ (t : ℝ) : ‖WithLp.toLp q₀ fun k => m k (t * I) • (g k).1 t‖ ≤ N :=
    (PiLp.norm_mono fun k => hb₀ k t).trans h₀
  have hG₁ (t : ℝ) : ‖WithLp.toLp q₁ fun k => m k (1 + t * I) • (g k).2 t‖ ≤ N :=
    (PiLp.norm_mono fun k => hb₁ k t).trans h₁
  let G₀ : BoundedContinuousFunction ℝ (PiLp q₀ fun _ : ι => X₀) :=
    .ofNormedAddCommGroup (fun t => WithLp.toLp q₀ fun k => m k (t * I) • (g k).1 t)
      ((PiLp.continuous_toLp _ _).comp <| continuous_pi fun k =>
        (((hm k).continuous).comp (by fun_prop)).smul (g k).1.continuous)
      N hG₀
  let G₁ : BoundedContinuousFunction ℝ (PiLp q₁ fun _ : ι => X₁) :=
    .ofNormedAddCommGroup (fun t => WithLp.toLp q₁ fun k => m k (1 + t * I) • (g k).2 t)
      ((PiLp.continuous_toLp _ _).comp <| continuous_pi fun k =>
        (((hm k).continuous).comp (by fun_prop)).smul (g k).2.continuous)
      N hG₁
  have hΦ := isBoundedStripFunction_sum_sumSingle_smul (G := (G₀, G₁)) hF hm
    (fun k _ hz => Complex.HadamardThreeLines.norm_ofReal_cpow_sub_mul_le (hb k) hθ (r₁ - r₀) hz)
    (fun _ => rfl) (fun _ => rfl)
  obtain ⟨v, hv⟩ :=
    (ComplexMethodSpace.exists_toSum_eq_iff_isBoundedStripFunction hθ).2 ⟨_, _, hΦ, rfl⟩
  refine ⟨v, ?_, (ComplexMethodSpace.norm_le_of_isBoundedStripFunction hθ hΦ hv).trans ?_⟩
  · rw [hv]
    simp [m, ← hFθ, map_sum, Finset.univ_sum_single]
  · exact norm_prod_le_iff.2 ⟨BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hN.le hG₀,
      BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hN.le hG₁⟩

variable [Fact (1 ≤ q)]

/-- For every family `c` strictly dominating the coordinate norms of `u ∈ ℓ^q([X₀, X₁]_θ)`, `u` is
an element of `[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` of norm at most `‖c‖_{ℓ^q}`. -/
private theorem exists_sumSpaceEmbed_toSum_eq_and_norm_le_norm_toLp [Nonempty ι]
    (hθ : θ ∈ Icc 0 1) (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (hq_top : q = ∞ → q₀ = ∞ ∧ q₁ = ∞) (u : PiLp q fun _ : ι => C.ComplexMethodSpace θ)
    {c : ι → ℝ} (hc : ∀ k, ‖u k‖ < c k) : ∃ v : (C.piLp ι q₀ q₁).ComplexMethodSpace θ,
      (C.piLp ι q₀ q₁).sumSpaceEmbed (ComplexMethodSpace.toSum v) =
        (fun k => C.sumSpaceEmbed (ComplexMethodSpace.toSum (u k))) ∧
        ‖v‖ ≤ ‖WithLp.toLp q c‖ := by
  have hc₀ (k : ι) : 0 < c k := (norm_nonneg _).trans_lt (hc k)
  have hN : 0 < ‖WithLp.toLp q c‖ := PiLp.norm_toLp_pos (hc₀ (Classical.arbitrary ι))
  by_cases hqt : q = ∞
  · -- all exponents are infinite: take `r₀ = r₁ = 1`
    obtain ⟨rfl, rfl⟩ := hq_top hqt
    subst hqt
    have hcN : (fun k => ‖WithLp.toLp ∞ c‖ * (c k / ‖WithLp.toLp ∞ c‖) ^ (1 : ℝ)) = c := by
      ext k
      rw [Real.rpow_one]
      field_simp
    exact exists_sumSpaceEmbed_toSum_eq_and_norm_le_of_lt hθ (r₀ := 1) (r₁ := 1) (by ring) u hc
      hN (by rw [hcN]) (by rw [hcN])
  -- `q < ∞`: take `r_j = q / q_j`
  have hne (p : ℝ≥0∞) [Fact (1 ≤ p)] : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hq₀ : q.toReal ≠ 0 := ((ENNReal.toReal_pos_iff_ne_top q).2 hqt).ne'
  have hθq := inv_toReal_eq_of_inv_eq (hne q₀) (hne q₁) hθ hq
  refine exists_sumSpaceEmbed_toSum_eq_and_norm_le_of_lt hθ ?_ u hc hN
    (PiLp.norm_toLp_mul_div_rpow hqt (hne q₀) hc₀).le
    (PiLp.norm_toLp_mul_div_rpow hqt (hne q₁) hc₀).le
  calc (1 - θ) * (q.toReal / q₀.toReal) + θ * (q.toReal / q₁.toReal)
      = q.toReal * ((1 - θ) * q₀.toReal⁻¹ + θ * q₁.toReal⁻¹) := by ring
    _ = 1 := by rw [← hθq, mul_inv_cancel₀ hq₀]

/-- Every family `u ∈ ℓ^q([X₀, X₁]_θ)` is an element of `[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` of norm at
most `‖u‖`. -/
private theorem exists_sumSpaceEmbed_toSum_eq_and_norm_le (hθ : θ ∈ Icc 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (hq_top : q = ∞ → q₀ = ∞ ∧ q₁ = ∞) (u : PiLp q fun _ : ι => C.ComplexMethodSpace θ) :
    ∃ v : (C.piLp ι q₀ q₁).ComplexMethodSpace θ,
      (C.piLp ι q₀ q₁).sumSpaceEmbed (ComplexMethodSpace.toSum v) =
        (fun k => C.sumSpaceEmbed (ComplexMethodSpace.toSum (u k))) ∧ ‖v‖ ≤ ‖u‖ := by
  cases isEmpty_or_nonempty ι
  · exact ⟨0, funext isEmptyElim, by simp⟩
  obtain ⟨v, hv, -⟩ := exists_sumSpaceEmbed_toSum_eq_and_norm_le_norm_toLp hθ hq hq_top u
    (c := fun k => ‖u k‖ + 1) fun k => by linarith
  refine ⟨v, hv, le_of_forall_pos_lt_add fun δ hδ => ?_⟩
  -- `v` is determined by `u`, so it obeys the bound for `c k = ‖u k‖ + ε` with `ε > 0` small
  set K := ‖WithLp.toLp q fun _ : ι => (1 : ℝ)‖
  have hε : 0 < δ / (K + 1) := div_pos hδ (by positivity)
  obtain ⟨v', hv', hnorm⟩ := exists_sumSpaceEmbed_toSum_eq_and_norm_le_norm_toLp hθ hq hq_top u
    (c := fun k => ‖u k‖ + δ / (K + 1)) fun k => by linarith
  obtain rfl : v' = v := ComplexMethodSpace.ext (sumSpace_ext _ (hv'.trans hv.symm))
  have hsplit : (WithLp.toLp q fun k => ‖u k‖ + δ / (K + 1)) =
      WithLp.toLp q (fun k => ‖u k‖) + (δ / (K + 1)) • WithLp.toLp q fun _ : ι => (1 : ℝ) :=
    WithLp.ofLp_injective q <| funext fun k => by simp
  calc ‖v'‖ ≤ ‖WithLp.toLp q fun k => ‖u k‖ + δ / (K + 1)‖ := hnorm
    _ ≤ ‖u‖ + δ / (K + 1) * K := by
        rw [hsplit]
        refine (norm_add_le _ _).trans_eq ?_
        rw [PiLp.norm_norm, norm_smul, Real.norm_of_nonneg hε.le]
    _ < ‖u‖ + δ := by
        have : δ * K / (K + 1) < δ := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
        rw [div_mul_eq_mul_div]
        linarith

variable (hθ : θ ∈ Icc 0 1) (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
  (hq_top : q = ∞ → q₀ = ∞ ∧ q₁ = ∞)

private theorem sumSpaceEmbed_toSum_choose (u : PiLp q fun _ : ι => C.ComplexMethodSpace θ) :
    (C.piLp ι q₀ q₁).sumSpaceEmbed (ComplexMethodSpace.toSum
        (exists_sumSpaceEmbed_toSum_eq_and_norm_le hθ hq hq_top u).choose) =
      fun k => C.sumSpaceEmbed (ComplexMethodSpace.toSum (u k)) :=
  (exists_sumSpaceEmbed_toSum_eq_and_norm_le hθ hq hq_top u).choose_spec.1

namespace ComplexMethodSpace

/-- **Complex interpolation of finite `ℓ^q` sums, `ℓ^q([X₀, X₁]_θ) ⊆ [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ`.**
For `0 ≤ θ ≤ 1` and `1 / q = (1 - θ) / q₀ + θ / q₁` (with `q < ∞` unless `q₀ = q₁ = ∞`), the
inclusion of the finite families of elements of `[X₀, X₁]_θ`, normed in `ℓ^q`, into the complex
interpolation space of the couple `(ℓ^{q₀}(ι; X₀), ℓ^{q₁}(ι; X₁))`. It lies over the identity of
`ι → V` (`sumSpaceEmbed_toSum_ofPiLp`) and has norm at most one (`norm_ofPiLp_le`). -/
def ofPiLp : (PiLp q fun _ : ι => C.ComplexMethodSpace θ) →L[ℂ]
    (C.piLp ι q₀ q₁).ComplexMethodSpace θ :=
  LinearMap.mkContinuous
    { toFun u := (exists_sumSpaceEmbed_toSum_eq_and_norm_le hθ hq hq_top u).choose
      map_add' u w := ext <| sumSpace_ext _ <| by
        simp only [map_add, sumSpaceEmbed_toSum_choose hθ hq hq_top]
        ext k
        simp
      map_smul' a u := ext <| sumSpace_ext _ <| by
        simp only [map_smul, sumSpaceEmbed_toSum_choose hθ hq hq_top]
        ext k
        simp }
    1 fun u => by
      simpa using (exists_sumSpaceEmbed_toSum_eq_and_norm_le hθ hq hq_top u).choose_spec.2

/-- The inclusion `ℓ^q([X₀, X₁]_θ) → [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` lies over the identity of
`ι → V`: the element it produces has coordinates `u k`. -/
@[simp]
theorem sumSpaceEmbed_toSum_ofPiLp (u : PiLp q fun _ : ι => C.ComplexMethodSpace θ) :
    (C.piLp ι q₀ q₁).sumSpaceEmbed (toSum (ofPiLp hθ hq hq_top u)) =
      fun k => C.sumSpaceEmbed (toSum (u k)) :=
  (exists_sumSpaceEmbed_toSum_eq_and_norm_le hθ hq hq_top u).choose_spec.1

/-- The inclusion `ℓ^q([X₀, X₁]_θ) → [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` does not increase norms:
`‖u‖_{[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ} ≤ ‖(‖u k‖_θ)_k‖_{ℓ^q}`. -/
theorem norm_ofPiLp_le (u : PiLp q fun _ : ι => C.ComplexMethodSpace θ) :
    ‖ofPiLp hθ hq hq_top u‖ ≤ ‖u‖ :=
  (exists_sumSpaceEmbed_toSum_eq_and_norm_le hθ hq hq_top u).choose_spec.2

/-- The inclusion `ℓ^q([X₀, X₁]_θ) → [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` has operator norm at most one. -/
theorem opNorm_ofPiLp_le :
    ‖(ofPiLp hθ hq hq_top : (PiLp q fun _ : ι => C.ComplexMethodSpace θ) →L[ℂ]
      (C.piLp ι q₀ q₁).ComplexMethodSpace θ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa using norm_ofPiLp_le hθ hq hq_top u

variable (q₀ q₁) in
/-- The projection `[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ → [X₀, X₁]_θ` onto the `k`-th coordinate, induced
by the coordinate projections of `ℓ^{q₀}(X₀)` and `ℓ^{q₁}(X₁)`. It lies over the coordinate
projection of the sum spaces (`toSum_piLpProj`) and does not increase norms
(`norm_piLpProj_le`). -/
def piLpProj (k : ι) : (C.piLp ι q₀ q₁).ComplexMethodSpace θ →L[ℂ] C.ComplexMethodSpace θ :=
  map θ (PiLp.proj q₀ (fun _ : ι => X₀) k) (PiLp.proj q₁ (fun _ : ι => X₁) k) fun x =>
    sumSpace_ext _ <| by simpa using congrFun ((C.piLp ι q₀ q₁).embed₀_interFst x) k

/-- The coordinate projection of the complex interpolation spaces lies over the coordinate
projection of the sum spaces. -/
@[simp]
theorem toSum_piLpProj (k : ι) (v : (C.piLp ι q₀ q₁).ComplexMethodSpace θ) :
    toSum (piLpProj q₀ q₁ k v) = C.sumProj q₀ q₁ k (toSum v) := by
  rw [piLpProj, toSum_map]
  exact DFunLike.congr_fun ((C.piLp ι q₀ q₁).sumLift_unique _ _ _
    (by ext; simp) (by ext; simp)).symm (toSum v)

/-- The coordinate projection `[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ → [X₀, X₁]_θ` does not increase norms. -/
theorem norm_piLpProj_le (k : ι) (v : (C.piLp ι q₀ q₁).ComplexMethodSpace θ) :
    ‖piLpProj q₀ q₁ k v‖ ≤ ‖v‖ :=
  norm_map_le_of_norm_le _ _ _ (fun x => PiLp.norm_apply_le x k) (fun x => PiLp.norm_apply_le x k) v

/-- The coordinate projections are left inverse to the inclusion
`ℓ^q([X₀, X₁]_θ) → [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ`. -/
@[simp]
theorem piLpProj_ofPiLp (k : ι) (u : PiLp q fun _ : ι => C.ComplexMethodSpace θ) :
    piLpProj q₀ q₁ k (ofPiLp hθ hq hq_top u) = u k :=
  ext <| sumSpace_ext _ <| by simp

/-- The inclusion `ℓ^q([X₀, X₁]_θ) → [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` is injective. -/
theorem ofPiLp_injective :
    Function.Injective (ofPiLp hθ hq hq_top :
      (PiLp q fun _ : ι => C.ComplexMethodSpace θ) → (C.piLp ι q₀ q₁).ComplexMethodSpace θ) :=
  fun u w h => WithLp.ofLp_injective q <| funext fun k => by
    simpa using congrArg (piLpProj q₀ q₁ k) h

end ComplexMethodSpace

end Inclusion

end TauCeti.CompatibleCouple

end
