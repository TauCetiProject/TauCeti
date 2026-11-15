/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Poisson
import Mathlib.Analysis.MeanInequalities
import TauCeti.Data.ENNReal.InterpolatedExponent

/-!
# Complex interpolation of finite vector-valued `ℓ^q` products

For a finite family `i ↦ (X₀ i, X₁ i)` of compatible couples of complex normed spaces and
`1 ≤ q₀, q₁ ≤ ∞`, the finite vector-valued `ℓ^q` spaces `PiLp q₀ X₀` and `PiLp q₁ X₁` form a
compatible couple `TauCeti.CompatibleCouple.piLp q₀ q₁ C` inside `∀ i, V i`.

This file proves the **finite vector-valued Riesz–Thorin / Lions–Peetre product formula**
(Bergh–Löfström, Theorem 5.1.2, specialized to finite index sets): for `0 < θ < 1` and
`1 / q = (1 - θ) / q₀ + θ / q₁` (including the endpoints `q₀ = ∞`, `q₁ = ∞`, and `q = ∞`),

`[PiLp q₀ X₀, PiLp q₁ X₁]_θ ≃ₗᵢ[ℂ] PiLp q (fun i ↦ [X₀ i, X₁ i]_θ)`.

Neither completeness nor density of the intersections nor duality is needed:
* the **lower bound** `‖(u_i)_i‖_{ℓ^q} ≤ ‖u‖_θ` applies the `(L^{q₀}, L^{q₁})` and mixed
  `(L^∞, L^p)` strip Poisson bounds of `ComplexMethod.Poisson` coordinatewise, followed by the
  weighted arithmetic–geometric mean inequality and Fubini on the finite sum;
* the **upper bound** multiplies near-optimal coordinate strip functions `F_i` by the bounded
  holomorphic scalar weights `exp (((1 - z) (q / q₀) + z (q / q₁) - 1) log (b_i / B))` equal to `1`
  at `z = θ`, sums their coordinate embeddings in `(piLp q₀ q₁ C).stripTraces`, and lets the slack
  tend to `0`.

Combining with the diagonal isometric identification `[X, X]_θ ≃ₗᵢ[ℂ] X`
(`CompatibleCouple.ComplexMethodSpace.reflEquiv`) gives
`[ℓ^{q₀}_n(X), ℓ^{q₁}_n(X)]_θ ≃ₗᵢ[ℂ] ℓ^q_n(X)` (`CompatibleCouple.piLpReflComplexMethodEquiv`).

## Main definitions and results

* `TauCeti.CompatibleCouple.ComplexMethodSpace.reflEquiv`: `[X, X]_θ ≃ₗᵢ[ℂ] X` for `θ ∈ [0, 1]`.
* `TauCeti.CompatibleCouple.piLp`: the compatible couple `(PiLp q₀ X₀, PiLp q₁ X₁)` in `∀ i, V i`.
* `TauCeti.CompatibleCouple.piLpCoord`: the `i`-th coordinate map
  `(piLp q₀ q₁ C).ComplexMethodSpace θ →L[ℂ] (C i).ComplexMethodSpace θ`.
* `TauCeti.CompatibleCouple.piLpComplexMethodEquiv`: the surjective linear isometry
  `(piLp q₀ q₁ C).ComplexMethodSpace θ ≃ₗᵢ[ℂ] PiLp q (fun i ↦ (C i).ComplexMethodSpace θ)`.
* `TauCeti.CompatibleCouple.piLpReflComplexMethodEquiv`: the constant-fiber specialization
  `[PiLp q₀ (fun _ ↦ X), PiLp q₁ (fun _ ↦ X)]_θ ≃ₗᵢ[ℂ] PiLp q (fun _ ↦ X)`.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. **24**
  (1964), 113–190, §13.6.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223, Springer,
  1976, Theorem 5.1.2.
-/

public noncomputable section

open Complex Complex.HadamardThreeLines TauCeti.Complex.HadamardThreeLines
open Filter MeasureTheory Metric Real Set WithLp
open scoped ENNReal Topology ZeroAtInfty

namespace TauCeti.CompatibleCouple

/-! ### Isometric identification of the diagonal couple `[X, X]_θ ≃ₗᵢ[ℂ] X` -/

namespace ComplexMethodSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- For `0 ≤ θ ≤ 1`, the complex interpolation space `[X, X]_θ` of the diagonal couple `refl ℂ X`
is linearly isometric to `X` via evaluation in the ambient space. -/
def reflEquiv {θ : ℝ} (hθ : θ ∈ Icc 0 1) :
    (refl ℂ X).ComplexMethodSpace θ ≃ₗᵢ[ℂ] X where
  toFun u := (refl ℂ X).sumSpaceEmbed (toSum u)
  invFun x := ofInter θ ⟨(x, x), by simp⟩
  left_inv u := by ext; simp [toSum_ofInter hθ]
  right_inv x := by simp [toSum_ofInter hθ]
  map_add' u v := by simp
  map_smul' c u := by simp
  norm_map' u := (norm_refl_sumSpaceEmbed (toSum u)).trans (norm_refl u).symm

/-- Applying `reflEquiv` evaluates `toSum u` in `X`. -/
@[simp]
theorem reflEquiv_apply {θ : ℝ} (hθ : θ ∈ Icc 0 1) (u : (refl ℂ X).ComplexMethodSpace θ) :
    reflEquiv hθ u = (refl ℂ X).sumSpaceEmbed (toSum u) := by
  rfl

/-- The inverse of `reflEquiv` sends `x : X` to the class of `(x, x) ∈ (refl ℂ X).inter`. -/
@[simp]
theorem reflEquiv_symm_apply {θ : ℝ} (hθ : θ ∈ Icc 0 1) (x : X) :
    (reflEquiv hθ).symm x = ofInter θ ⟨(x, x), by simp⟩ := by
  rfl

/-- In `(refl ℂ X).SumSpace`, `(reflEquiv hθ).symm x` lies over `fstToSum x`. -/
theorem toSum_reflEquiv_symm {θ : ℝ} (hθ : θ ∈ Icc 0 1) (x : X) :
    toSum ((reflEquiv hθ).symm x) = (refl ℂ X).fstToSum x := by
  simp [reflEquiv_symm_apply, toSum_ofInter hθ]

end ComplexMethodSpace

/-! ### Analytic weight rescaling on a single compatible couple -/

private theorem norm_exp_weight_le {c₀ c₁ γ : ℝ} {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    ‖exp (((1 - z) * c₀ + z * c₁ - 1) * γ)‖ ≤ Real.exp ((|c₀| + |c₁| + 1) * |γ|) := by
  have hz' := mem_verticalClosedStrip_iff.1 hz
  have hre : (((1 - z) * c₀ + z * c₁ - 1) * γ).re = ((1 - z.re) * c₀ + z.re * c₁ - 1) * γ := by
    simp
  rw [Complex.norm_exp, hre]
  refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg γ)
  have h₀ : |(1 - z.re) * c₀| ≤ |c₀| := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.2 hz'.2)]
    exact mul_le_of_le_one_left (abs_nonneg c₀) (by linarith [hz'.1])
  have h₁ : |z.re * c₁| ≤ |c₁| := by
    rw [abs_mul, abs_of_nonneg hz'.1]
    exact mul_le_of_le_one_left (abs_nonneg c₁) hz'.2
  calc |(1 - z.re) * c₀ + z.re * c₁ - 1|
    _ ≤ |(1 - z.re) * c₀ + z.re * c₁| + |(1 : ℝ)| := abs_sub _ _
    _ ≤ (|(1 - z.re) * c₀| + |z.re * c₁|) + 1 := by
        rw [abs_one]; exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ |c₀| + |c₁| + 1 := by linarith

private theorem exp_sub_one_mul_log_mul_le {c bi B m : ℝ} (hbi : 0 < bi) (hB : 0 < B)
    (hm : m ≤ bi) :
    Real.exp ((c - 1) * Real.log (bi / B)) * m ≤ B * (bi / B) ^ c := by
  calc Real.exp ((c - 1) * Real.log (bi / B)) * m
    _ = (bi / B) ^ (c - 1) * m := by
        rw [mul_comm (c - 1), ← Real.rpow_def_of_pos (div_pos hbi hB)]
    _ ≤ (bi / B) ^ (c - 1) * bi :=
        mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (div_nonneg hbi.le hB.le) _)
    _ = B * (bi / B) ^ c := by
        rw [Real.rpow_sub (div_pos hbi hB), Real.rpow_one, div_div_eq_mul_div,
          div_mul_cancel₀ _ hbi.ne', mul_comm]

private theorem exists_weighted_trace {Y₀ Y₁ W : Type*}
    [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀] [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [ContinuousAdd W] [T1Space W]
    (D : CompatibleCouple ℂ Y₀ Y₁ W) {θ c₀ c₁ bi B : ℝ} (hθ : θ ∈ Icc 0 1)
    (hc : (1 - θ) * c₀ + θ * c₁ = 1) (hbi : 0 < bi) (hB : 0 < B)
    {u : D.ComplexMethodSpace θ} (hu : ‖u‖ < bi) :
    ∃ g' : D.stripTraces, ComplexMethodSpace.mk θ g' = u ∧
      (∀ t, ‖g'.1.1 t‖ ≤ B * (bi / B) ^ c₀) ∧
      (∀ t, ‖g'.1.2 t‖ ≤ B * (bi / B) ^ c₁) := by
  obtain ⟨g, rfl, hgb⟩ := ComplexMethodSpace.norm_lt_iff.1 hu
  set γ := Real.log (bi / B)
  let w : ℂ → ℂ := fun z ↦ exp (((1 - z) * c₀ + z * c₁ - 1) * γ)
  have hw_diff : DifferentiableOn ℂ w (verticalClosedStrip 0 1) :=
    (by unfold w; fun_prop : Differentiable ℂ w).differentiableOn
  obtain ⟨g', hsmul, hg'₀, hg'₁⟩ :=
    (D.isStripFunction_stripFunction g).exists_smul_of_differentiableOn hw_diff
      fun z hz ↦ norm_exp_weight_le hz
  have hwθ : w θ = 1 := by
    have : ((1 - (θ : ℂ)) * c₀ + (θ : ℂ) * c₁ - 1) * γ = 0 := by
      exact_mod_cast (show ((1 - θ) * c₀ + θ * c₁ - 1) * γ = 0 by rw [hc, sub_self, zero_mul])
    simp [w, this]
  refine ⟨⟨g', mem_stripTraces_iff.2 ⟨_, hsmul⟩⟩, ?_, fun t ↦ ?_, fun t ↦ ?_⟩
  · apply ComplexMethodSpace.ext
    rw [ComplexMethodSpace.toSum_mk, ComplexMethodSpace.toSum_mk, stripEval_apply, stripEval_apply,
      stripFunction_eq hsmul (by simpa [mem_verticalClosedStrip_iff] using hθ)]
    simp [hwθ]
  · change ‖g'.1 t‖ ≤ _
    rw [hg'₀, norm_smul, Complex.norm_exp, show (((1 - ↑t * I) * ↑c₀ + ↑t * I * ↑c₁ - 1) * ↑γ).re =
      (c₀ - 1) * γ by simp]
    exact exp_sub_one_mul_log_mul_le hbi hB
      ((ZeroAtInftyContinuousMap.norm_coe_le_norm _ _).trans ((norm_fst_le g.1).trans hgb.le))
  · change ‖g'.2 t‖ ≤ _
    rw [hg'₁, norm_smul, Complex.norm_exp,
      show (((1 - (1 + ↑t * I)) * ↑c₀ + (1 + ↑t * I) * ↑c₁ - 1) * ↑γ).re = (c₁ - 1) * γ by simp]
    exact exp_sub_one_mul_log_mul_le hbi hB
      ((ZeroAtInftyContinuousMap.norm_coe_le_norm _ _).trans ((norm_snd_le g.1).trans hgb.le))

/-! ### The `PiLp` compatible couple -/

section Defs

variable {𝕜 ι : Type*} [Semiring 𝕜]
  {X₀ X₁ V : ι → Type*}
  [∀ i, NormedAddCommGroup (X₀ i)] [∀ i, Module 𝕜 (X₀ i)]
  [∀ i, NormedAddCommGroup (X₁ i)] [∀ i, Module 𝕜 (X₁ i)]
  [∀ i, AddCommMonoid (V i)] [∀ i, Module 𝕜 (V i)] [∀ i, TopologicalSpace (V i)]

/-- Coordinatewise compatible couple `(PiLp q₀ X₀, PiLp q₁ X₁)` in the product `∀ i, V i`. -/
def piLp (q₀ q₁ : ℝ≥0∞) (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) :
    CompatibleCouple 𝕜 (PiLp q₀ X₀) (PiLp q₁ X₁) (∀ i, V i) where
  embed₀ := ContinuousLinearMap.pi fun i ↦ (C i).embed₀.comp (PiLp.proj q₀ X₀ i)
  embed₁ := ContinuousLinearMap.pi fun i ↦ (C i).embed₁.comp (PiLp.proj q₁ X₁ i)
  embed₀_injective x y h := PiLp.ext fun i ↦
    (C i).embed₀_injective (by simpa [PiLp.proj_apply] using congr_fun h i)
  embed₁_injective x y h := PiLp.ext fun i ↦
    (C i).embed₁_injective (by simpa [PiLp.proj_apply] using congr_fun h i)

/-- `embed₀` of `CompatibleCouple.piLp` acts coordinatewise. -/
@[simp]
theorem piLp_embed₀_apply (q₀ q₁ : ℝ≥0∞) (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i))
    (x : PiLp q₀ X₀) (i : ι) :
    (piLp q₀ q₁ C).embed₀ x i = (C i).embed₀ (x i) := by
  rfl

/-- `embed₁` of `CompatibleCouple.piLp` acts coordinatewise. -/
@[simp]
theorem piLp_embed₁_apply (q₀ q₁ : ℝ≥0∞) (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i))
    (x : PiLp q₁ X₁) (i : ι) :
    (piLp q₀ q₁ C).embed₁ x i = (C i).embed₁ (x i) := by
  rfl

end Defs

/-! ### Coordinate projections and inclusions on `[PiLp q₀ X₀, PiLp q₁ X₁]_θ` -/

section ComplexPiLp

variable {ι : Type*} [Fintype ι]
  {X₀ X₁ V : ι → Type*}
  [∀ i, NormedAddCommGroup (X₀ i)] [∀ i, NormedSpace ℂ (X₀ i)]
  [∀ i, NormedAddCommGroup (X₁ i)] [∀ i, NormedSpace ℂ (X₁ i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, TopologicalSpace (V i)]
  [∀ i, ContinuousAdd (V i)] [∀ i, T1Space (V i)]
  {q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]

omit [∀ i, T1Space (V i)] in
private theorem piLp_proj_compat (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (i : ι)
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

/-- Each coordinate projection `piLpCoord θ C i` has norm at most `1`. -/
theorem norm_piLpCoord_le (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (i : ι)
    (u : (piLp q₀ q₁ C).ComplexMethodSpace θ) :
    ‖piLpCoord θ C i u‖ ≤ ‖u‖ :=
  ComplexMethodSpace.norm_map_le_of_norm_le _ _ _
    (fun x ↦ PiLp.norm_apply_le x i) (fun x ↦ PiLp.norm_apply_le x i) u

/-- In the ambient space `V i`, `piLpCoord θ C i u` evaluates `(piLp q₀ q₁ C).sumSpaceEmbed` at
`i`. -/
@[simp]
theorem sumSpaceEmbed_toSum_piLpCoord (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (i : ι) (u : (piLp q₀ q₁ C).ComplexMethodSpace θ) :
    (C i).sumSpaceEmbed (ComplexMethodSpace.toSum (piLpCoord θ C i u)) =
      (piLp q₀ q₁ C).sumSpaceEmbed (ComplexMethodSpace.toSum u) i := by
  obtain ⟨x₀, x₁, hx⟩ := (piLp q₀ q₁ C).exists_fstToSum_add_sndToSum_eq
    (ComplexMethodSpace.toSum u)
  let T₀ := PiLp.proj (𝕜 := ℂ) q₀ X₀ i
  let T₁ := PiLp.proj (𝕜 := ℂ) q₁ X₁ i
  let f₀ := (C i).fstToSum.comp T₀
  let f₁ := (C i).sndToSum.comp T₁
  let L := (piLp q₀ q₁ C).sumLift f₀ f₁ (piLp_proj_compat C i)
  have hmap : ComplexMethodSpace.toSum (piLpCoord θ C i u) = f₀ x₀ + f₁ x₁ :=
    (ComplexMethodSpace.toSum_map T₀ T₁ (piLp_proj_compat C i) u).trans <|
      (congrArg L hx.symm).trans <| (map_add L _ _).trans <|
        congr_arg₂ (· + ·) ((piLp q₀ q₁ C).sumLift_fstToSum f₀ f₁ _ x₀)
          ((piLp q₀ q₁ C).sumLift_sndToSum f₀ f₁ _ x₁)
  rw [hmap, ← hx]
  simp [f₀, f₁, T₀, T₁, PiLp.proj_apply]

private theorem piLpCoord_injective (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    {u u' : (piLp q₀ q₁ C).ComplexMethodSpace θ}
    (h : ∀ i, piLpCoord θ C i u = piLpCoord θ C i u') : u = u' := by
  apply ComplexMethodSpace.ext
  apply (piLp q₀ q₁ C).sumSpaceEmbed_injective
  ext i
  rw [← sumSpaceEmbed_toSum_piLpCoord, ← sumSpaceEmbed_toSum_piLpCoord, h i]

private def piLpSingleCLM [DecidableEq ι] (p : ℝ≥0∞) (Y : ι → Type*)
    [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℂ (Y i)] (i : ι) :
    Y i →L[ℂ] PiLp p Y :=
  (PiLp.continuousLinearEquiv p ℂ Y).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single (R := ℂ) (φ := Y) i)

omit [∀ i, T1Space (V i)] in
private theorem piLp_single_compat [DecidableEq ι]
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (i : ι) (x : (C i).inter) :
    (piLp q₀ q₁ C).fstToSum (piLpSingleCLM q₀ X₀ i ((C i).interFst x)) =
      (piLp q₀ q₁ C).sndToSum (piLpSingleCLM q₁ X₁ i ((C i).interSnd x)) := by
  apply (piLp q₀ q₁ C).sumSpace_ext
  ext j
  simp only [sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, piLp_embed₀_apply, piLp_embed₁_apply,
    piLpSingleCLM, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    PiLp.continuousLinearEquiv_symm_apply, ContinuousLinearMap.single_apply]
  by_cases hij : j = i
  · subst hij
    simpa using (C j).embed₀_interFst x
  · simp [Pi.single_eq_of_ne hij]

private def piLpSingle [DecidableEq ι] (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (i : ι) : (C i).ComplexMethodSpace θ →L[ℂ] (piLp q₀ q₁ C).ComplexMethodSpace θ :=
  ComplexMethodSpace.map θ (piLpSingleCLM q₀ X₀ i) (piLpSingleCLM q₁ X₁ i)
    (piLp_single_compat C i)

private theorem sumSpaceEmbed_toSum_piLpSingle [DecidableEq ι] (θ : ℝ)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (i j : ι)
    (u : (C i).ComplexMethodSpace θ) :
    (piLp q₀ q₁ C).sumSpaceEmbed
        (ComplexMethodSpace.toSum (piLpSingle (q₀ := q₀) (q₁ := q₁) θ C i u)) j =
      Pi.single i ((C i).sumSpaceEmbed (ComplexMethodSpace.toSum u)) j := by
  rw [piLpSingle, ComplexMethodSpace.toSum_map]
  obtain ⟨x₀, x₁, hx⟩ := (C i).exists_fstToSum_add_sndToSum_eq (ComplexMethodSpace.toSum u)
  rw [← hx]
  simp only [map_add, sumLift_fstToSum, sumLift_sndToSum, ContinuousLinearMap.comp_apply,
    sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, Pi.add_apply, piLp_embed₀_apply,
    piLp_embed₁_apply, piLpSingleCLM, ContinuousLinearEquiv.coe_coe,
    PiLp.continuousLinearEquiv_symm_apply, ContinuousLinearMap.single_apply]
  by_cases hij : j = i
  · subst hij; simp
  · simp [Pi.single_eq_of_ne hij]

private def piLpFromCoord (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (θ : ℝ)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (v : ∀ i, (C i).ComplexMethodSpace θ) : (piLp q₀ q₁ C).ComplexMethodSpace θ :=
  letI := Classical.decEq ι
  ∑ i, piLpSingle θ C i (v i)

private theorem piLpCoord_piLpFromCoord (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (v : ∀ i, (C i).ComplexMethodSpace θ) (j : ι) :
    piLpCoord θ C j (piLpFromCoord q₀ q₁ θ C v) = v j := by
  classical
  apply ComplexMethodSpace.ext
  apply (C j).sumSpaceEmbed_injective
  rw [sumSpaceEmbed_toSum_piLpCoord, piLpFromCoord, map_sum, map_sum, Finset.sum_apply]
  simp [sumSpaceEmbed_toSum_piLpSingle]

private theorem piLpFromCoord_piLpCoord (θ : ℝ) (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (u : (piLp q₀ q₁ C).ComplexMethodSpace θ) :
    piLpFromCoord q₀ q₁ θ C (fun i ↦ piLpCoord θ C i u) = u :=
  piLpCoord_injective θ C (piLpCoord_piLpFromCoord θ C _)

/-! ### Lower bound via strip Poisson integrals and weighted AM–GM -/

private theorem norm_stripTracesMap_proj_fst_le
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (g : (piLp q₀ q₁ C).stripTraces) (i : ι) :
    ‖(stripTracesMap (PiLp.proj (𝕜 := ℂ) q₀ X₀ i) (PiLp.proj (𝕜 := ℂ) q₁ X₁ i)
      (piLp_proj_compat C i) g : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).1‖ ≤ ‖g‖ :=
  ((ZeroAtInftyContinuousMap.norm_le
    (norm_nonneg (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1)).2 fun t ↦ by
    rw [stripTracesMap_apply_fst, PiLp.proj_apply]
    exact (PiLp.norm_apply_le _ i).trans
      (ZeroAtInftyContinuousMap.norm_coe_le_norm
        (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 t)).trans
    (norm_fst_le (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)))

private theorem norm_stripTracesMap_proj_snd_le
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (g : (piLp q₀ q₁ C).stripTraces) (i : ι) :
    ‖(stripTracesMap (PiLp.proj (𝕜 := ℂ) q₀ X₀ i) (PiLp.proj (𝕜 := ℂ) q₁ X₁ i)
      (piLp_proj_compat C i) g : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).2‖ ≤ ‖g‖ :=
  ((ZeroAtInftyContinuousMap.norm_le
    (norm_nonneg (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2)).2 fun t ↦ by
    rw [stripTracesMap_apply_snd, PiLp.proj_apply]
    exact (PiLp.norm_apply_le _ i).trans
      (ZeroAtInftyContinuousMap.norm_coe_le_norm
        (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 t)).trans
    (norm_snd_le (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)))

private theorem norm_mk_rpow_le_stripPoissonMeasure {Y₀ Y₁ W : Type*}
    [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀] [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [ContinuousAdd W] [T1Space W]
    {D : CompatibleCouple ℂ Y₀ Y₁ W} {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {r : ℝ} (hr : 0 < r)
    {gi : D.stripTraces} (hgi₀ : ‖(gi : C₀(ℝ, Y₀) × C₀(ℝ, Y₁)).1‖ ≤ 1)
    (hgi₁ : ‖(gi : C₀(ℝ, Y₀) × C₀(ℝ, Y₁)).2‖ ≤ 1) :
    ‖ComplexMethodSpace.mk θ gi‖ ^ r ≤
      (if q₀ = ∞ then (1 : ℝ) else
        ∫ t, ‖(gi : C₀(ℝ, Y₀) × C₀(ℝ, Y₁)).1 t‖ ^ q₀.toReal ∂stripPoissonMeasure₀ θ) ^
          (r * ((1 - θ) * (q₀⁻¹).toReal)) *
      (if q₁ = ∞ then (1 : ℝ) else
        ∫ t, ‖(gi : C₀(ℝ, Y₀) × C₀(ℝ, Y₁)).2 t‖ ^ q₁.toReal ∂stripPoissonMeasure₁ θ) ^
          (r * (θ * (q₁⁻¹).toReal)) := by
  have hI₀ : 0 ≤ ∫ t, ‖(gi : C₀(ℝ, Y₀) × C₀(ℝ, Y₁)).1 t‖ ^ q₀.toReal ∂stripPoissonMeasure₀ θ :=
    integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _
  have hI₁ : 0 ≤ ∫ t, ‖(gi : C₀(ℝ, Y₀) × C₀(ℝ, Y₁)).2 t‖ ^ q₁.toReal ∂stripPoissonMeasure₁ θ :=
    integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _
  have hu : ComplexMethodSpace.toSum (ComplexMethodSpace.mk θ gi) = D.stripFunction gi θ :=
    (ComplexMethodSpace.toSum_mk gi).trans (D.stripEval_apply θ gi)
  by_cases hq₀ : q₀ = ∞ <;> by_cases hq₁ : q₁ = ∞
  · subst hq₀; subst hq₁
    simp only [↓reduceIte, ENNReal.inv_top, ENNReal.toReal_zero, mul_zero,
      Real.rpow_zero, mul_one]
    exact Real.rpow_le_one (norm_nonneg _)
      ((ComplexMethodSpace.norm_mk_le gi).trans
        (by rw [← Submodule.norm_coe]; exact norm_prod_le_iff.2 ⟨hgi₀, hgi₁⟩)) hr.le
  · subst hq₀
    have hp₁ : 0 < q₁.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq₁
    have hb := (ComplexMethodSpace.norm_le_norm_fst_rpow_mul_rpow_integral_stripPoissonMeasure
      hθ hp₁ (D.isStripFunction_stripFunction gi) hu).trans
      (mul_le_mul_of_nonneg_right (Real.rpow_le_one (norm_nonneg _) hgi₀ (sub_nonneg.2 hθ.2.le))
        (Real.rpow_nonneg hI₁ _))
    simp only [↓reduceIte, hq₁, ENNReal.inv_top, ENNReal.toReal_zero, mul_zero,
      Real.rpow_zero, one_mul, ENNReal.toReal_inv, ← div_eq_mul_inv] at hb ⊢
    exact (Real.rpow_le_rpow (norm_nonneg _) hb hr.le).trans_eq
      (by rw [← Real.rpow_mul hI₁, mul_comm _ r])
  · subst hq₁
    have hp₀ : 0 < q₀.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq₀
    have hb := (ComplexMethodSpace.norm_le_rpow_integral_stripPoissonMeasure_mul_norm_snd_rpow
      hθ hp₀ (D.isStripFunction_stripFunction gi) hu).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_one (norm_nonneg _) hgi₁ hθ.1.le)
        (Real.rpow_nonneg hI₀ _))
    simp only [↓reduceIte, hq₀, ENNReal.inv_top, ENNReal.toReal_zero, mul_zero,
      Real.rpow_zero, mul_one, ENNReal.toReal_inv, ← div_eq_mul_inv] at hb ⊢
    exact (Real.rpow_le_rpow (norm_nonneg _) hb hr.le).trans_eq
      (by rw [← Real.rpow_mul hI₀, mul_comm _ r])
  · have hp₀ : 0 < q₀.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq₀
    have hp₁ : 0 < q₁.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq₁
    have hb := ComplexMethodSpace.norm_le_rpow_integral_stripPoissonMeasure
      hθ hp₀ hp₁ (D.isStripFunction_stripFunction gi) hu
    simp only [hq₀, hq₁, ↓reduceIte, ENNReal.toReal_inv, ← div_eq_mul_inv]
    refine (Real.rpow_le_rpow (norm_nonneg _) hb hr.le).trans_eq ?_
    rw [Real.mul_rpow (Real.rpow_nonneg hI₀ _) (Real.rpow_nonneg hI₁ _),
      ← Real.rpow_mul hI₀, ← Real.rpow_mul hI₁, mul_comm _ r, mul_comm (θ / _) r]

private theorem coord_rpow_le_poisson {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {r : ℝ} (hr : 0 < r)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    {g : (piLp q₀ q₁ C).stripTraces} (hg : ‖g‖ ≤ 1) (i : ι) :
    let S₀ := if q₀ = ∞ then (1 : ℝ) else
      ∫ t, ‖(g.1.1 t) i‖ ^ q₀.toReal ∂stripPoissonMeasure₀ θ
    let S₁ := if q₁ = ∞ then (1 : ℝ) else
      ∫ t, ‖(g.1.2 t) i‖ ^ q₁.toReal ∂stripPoissonMeasure₁ θ
    ‖piLpCoord θ C i (ComplexMethodSpace.mk θ g)‖ ^ r ≤
      S₀ ^ (r * ((1 - θ) * (q₀⁻¹).toReal)) * S₁ ^ (r * (θ * (q₁⁻¹).toReal)) := by
  intro S₀ S₁
  let gi := stripTracesMap (PiLp.proj (𝕜 := ℂ) q₀ X₀ i) (PiLp.proj (𝕜 := ℂ) q₁ X₁ i)
    (piLp_proj_compat C i) g
  have hmk : piLpCoord θ C i (ComplexMethodSpace.mk θ g) = ComplexMethodSpace.mk θ gi :=
    ComplexMethodSpace.map_mk _ _ _ g
  have hgi1 (t : ℝ) : (gi : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).1 t = (g.1.1 t) i := by
    rw [stripTracesMap_apply_fst, PiLp.proj_apply]
  have hgi2 (t : ℝ) : (gi : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).2 t = (g.1.2 t) i := by
    rw [stripTracesMap_apply_snd, PiLp.proj_apply]
  rw [hmk]
  have h := norm_mk_rpow_le_stripPoissonMeasure (q₀ := q₀) (q₁ := q₁) (gi := gi) hθ hr
    ((norm_stripTracesMap_proj_fst_le C g i).trans hg)
    ((norm_stripTracesMap_proj_snd_le C g i).trans hg)
  dsimp only [S₀, S₁]
  simpa only [hgi1, hgi2] using h

private theorem sum_poisson_coord_le_one {p : ℝ≥0∞} [Fact (1 ≤ p)] {Y : ι → Type*}
    [∀ i, NormedAddCommGroup (Y i)] {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (f : C₀(ℝ, PiLp p Y)) (hf : ‖f‖ ≤ 1) (hp : p ≠ ∞) :
    ∑ i, (∫ t, ‖(f t) i‖ ^ p.toReal ∂μ) ≤ 1 := by
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
  have hint (i : ι) : Integrable (fun t ↦ ‖(f t) i‖ ^ p.toReal) μ := by
    have hc : Continuous fun t ↦ ‖(f t) i‖ ^ p.toReal :=
      ((continuous_norm.comp ((PiLp.continuous_apply p Y i).comp f.continuous)).rpow_const
        fun _ ↦ Or.inr hp_pos.le)
    refine Integrable.of_bound hc.aestronglyMeasurable 1 (Eventually.of_forall fun t ↦ ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_one (norm_nonneg _)
      ((PiLp.norm_apply_le _ i).trans
        ((ZeroAtInftyContinuousMap.norm_coe_le_norm f t).trans hf)) hp_pos.le
  rw [← integral_finsetSum _ fun i _ ↦ hint i]
  refine (integral_mono (integrable_finsetSum _ fun i _ ↦ hint i) (integrable_const 1)
    fun t ↦ ?_).trans_eq (by rw [integral_const, probReal_univ, one_smul])
  have hsum : ∑ i, ‖(f t) i‖ ^ p.toReal = ‖f t‖ ^ p.toReal := by
    have h := congrArg (· ^ p.toReal) (PiLp.norm_eq_sum hp_pos (f t))
    rw [one_div, Real.rpow_inv_rpow
      (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) hp_pos.ne'] at h
    exact h.symm
  exact hsum.le.trans
    (Real.rpow_le_one (norm_nonneg _)
      ((ZeroAtInftyContinuousMap.norm_coe_le_norm f t).trans hf) hp_pos.le)

private theorem toReal_mul_inv_add {θ : ℝ} (hθ : θ ∈ Icc 0 1) (hq_ne : q ≠ ∞)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) :
    q.toReal * ((1 - θ) * (q₀⁻¹).toReal) + q.toReal * (θ * (q₁⁻¹).toReal) = 1 := by
  have hq1 : 1 ≤ q := one_le_of_inv_eq Fact.out Fact.out hθ hq
  have hq_pos : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hq1).ne' hq_ne
  have hinv := congrArg ENNReal.toReal (inv_eq_ofReal_of_inv_eq
    (zero_lt_one.trans_le (Fact.out : 1 ≤ q₀)).ne'
    (zero_lt_one.trans_le (Fact.out : 1 ≤ q₁)).ne' hθ hq)
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal
    (add_nonneg (mul_nonneg (sub_nonneg.2 hθ.2) ENNReal.toReal_nonneg)
      (mul_nonneg hθ.1 ENNReal.toReal_nonneg))] at hinv
  rw [← mul_add, ← hinv, mul_inv_cancel₀ hq_pos.ne']

private theorem norm_toLp_piLpCoord_mk_le_one [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    {g : (piLp q₀ q₁ C).stripTraces} (hg : ‖g‖ ≤ 1) :
    ‖toLp q (fun i ↦ piLpCoord θ C i (ComplexMethodSpace.mk θ g))‖ ≤ 1 := by
  by_cases hq_top : q = ∞
  · subst hq_top
    rw [PiLp.norm_toLp]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦
      (norm_piLpCoord_le θ C i _).trans ((ComplexMethodSpace.norm_mk_le g).trans hg)
  have := isProbabilityMeasure_stripPoissonMeasure₀ hθ
  have := isProbabilityMeasure_stripPoissonMeasure₁ hθ
  have hq_pos : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq_top
  rw [PiLp.norm_eq_sum hq_pos]
  refine Real.rpow_le_one
    (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) ?_ (by positivity)
  set α₀ := q.toReal * ((1 - θ) * (q₀⁻¹).toReal)
  set α₁ := q.toReal * (θ * (q₁⁻¹).toReal)
  have hα₀ : 0 ≤ α₀ :=
    mul_nonneg hq_pos.le (mul_nonneg (sub_nonneg.2 hθ.2.le) ENNReal.toReal_nonneg)
  have hα₁ : 0 ≤ α₁ := mul_nonneg hq_pos.le (mul_nonneg hθ.1.le ENNReal.toReal_nonneg)
  have hα : α₀ + α₁ = 1 := toReal_mul_inv_add ⟨hθ.1.le, hθ.2.le⟩ hq_top hq
  let S₀ : ι → ℝ := fun i ↦
    if q₀ = ∞ then 1 else ∫ t, ‖(g.1.1 t) i‖ ^ q₀.toReal ∂stripPoissonMeasure₀ θ
  let S₁ : ι → ℝ := fun i ↦
    if q₁ = ∞ then 1 else ∫ t, ‖(g.1.2 t) i‖ ^ q₁.toReal ∂stripPoissonMeasure₁ θ
  have hpt (i : ι) : ‖piLpCoord θ C i (ComplexMethodSpace.mk θ g)‖ ^ q.toReal ≤
      α₀ * S₀ i + α₁ * S₁ i := by
    have hS₀_nn : 0 ≤ S₀ i := by
      dsimp only [S₀]; split_ifs
      · exact zero_le_one
      · exact integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _
    have hS₁_nn : 0 ≤ S₁ i := by
      dsimp only [S₁]; split_ifs
      · exact zero_le_one
      · exact integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _
    exact (coord_rpow_le_poisson hθ hq_pos C hg i).trans
      (Real.geom_mean_le_arith_mean2_weighted hα₀ hα₁ hS₀_nn hS₁_nn hα)
  refine (Finset.sum_le_sum fun i _ ↦ hpt i).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hb₀ : α₀ * ∑ i, S₀ i ≤ α₀ := by
    by_cases hq₀ : q₀ = ∞
    · simp [α₀, hq₀]
    · simpa [S₀, hq₀] using mul_le_of_le_one_right hα₀
        (sum_poisson_coord_le_one g.1.1 ((norm_fst_le g.1).trans hg) hq₀)
  have hb₁ : α₁ * ∑ i, S₁ i ≤ α₁ := by
    by_cases hq₁ : q₁ = ∞
    · simp [α₁, hq₁]
    · simpa [S₁, hq₁] using mul_le_of_le_one_right hα₁
        (sum_poisson_coord_le_one g.1.2 ((norm_snd_le g.1).trans hg) hq₁)
  linarith

private theorem norm_toLp_piLpCoord_le [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (u : (piLp q₀ q₁ C).ComplexMethodSpace θ) :
    ‖toLp q (fun i ↦ piLpCoord θ C i u)‖ ≤ ‖u‖ := by
  refine le_of_forall_gt fun r hr ↦ ?_
  obtain ⟨g, rfl, hgr⟩ := ComplexMethodSpace.norm_lt_iff.1 hr
  by_cases hg0 : ‖g‖ = 0
  · obtain rfl := norm_eq_zero.1 hg0
    rw [norm_zero] at hgr
    have hz : toLp q (fun i ↦ piLpCoord (q₀ := q₀) (q₁ := q₁) θ C i
        (ComplexMethodSpace.mk θ 0)) = 0 := by
      ext i; simp
    rwa [hz, norm_zero]
  have hg_pos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg g) (Ne.symm hg0)
  let g' : (piLp q₀ q₁ C).stripTraces := ((‖g‖ : ℂ)⁻¹) • g
  have hg'1 : ‖g'‖ ≤ 1 := by
    dsimp only [g']
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hg_pos.le,
      inv_mul_cancel₀ hg_pos.ne']
  have h1 := norm_toLp_piLpCoord_mk_le_one hθ hq C hg'1
  have hsmul : toLp q (fun i ↦ piLpCoord θ C i (ComplexMethodSpace.mk θ g)) =
      (‖g‖ : ℂ) • toLp q (fun i ↦ piLpCoord θ C i (ComplexMethodSpace.mk θ g')) := by
    ext i
    simp only [g', ofLp_smul, Pi.smul_apply, map_smul, smul_smul,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hg_pos.ne'), one_smul]
  rw [hsmul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hg_pos.le]
  exact (mul_le_of_le_one_right hg_pos.le h1).trans_lt hgr

/-! ### Upper bound via analytic coordinate weights -/

private theorem piLp_norm_le_of_coord_le {Y : ι → Type*} [∀ i, NormedAddCommGroup (Y i)]
    (r : ℝ≥0∞) [Fact (1 ≤ r)] {p : ℝ} {b : ι → ℝ} (hb : ∀ i, 0 < b i)
    {B : ℝ} (hB : 0 < B) (hBp : B ^ p = ∑ i, b i ^ p) (x : ∀ i, Y i)
    (hx : ∀ i, ‖x i‖ ≤ B * (b i / B) ^ (p * (r⁻¹).toReal)) :
    ‖toLp r x‖ ≤ B := by
  by_cases hr : r = ∞
  · subst hr
    rw [PiLp.norm_toLp]
    exact (pi_norm_le_iff_of_nonneg hB.le).2 fun i ↦ by simpa using hx i
  have hr_pos : 0 < r.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hr
  rw [PiLp.norm_eq_sum hr_pos]
  have hsum : ∑ i, ‖x i‖ ^ r.toReal ≤ B ^ r.toReal := by
    have hpt (i : ι) : ‖x i‖ ^ r.toReal ≤ B ^ r.toReal * (b i ^ p / B ^ p) := by
      refine (Real.rpow_le_rpow (norm_nonneg _) (hx i) hr_pos.le).trans_eq ?_
      rw [ENNReal.toReal_inv,
        Real.mul_rpow hB.le (Real.rpow_nonneg (div_nonneg (hb i).le hB.le) _),
        ← Real.rpow_mul (div_nonneg (hb i).le hB.le), mul_assoc, inv_mul_cancel₀ hr_pos.ne',
        mul_one, Real.div_rpow (hb i).le hB.le]
    refine (Finset.sum_le_sum fun i _ ↦ hpt i).trans_eq ?_
    rw [← Finset.mul_sum, ← Finset.sum_div, ← hBp,
      div_self (Real.rpow_pos_of_pos hB p).ne', mul_one]
  exact (Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
    hsum (by positivity)).trans_eq
    (by rw [one_div, ← Real.rpow_mul hB.le, mul_inv_cancel₀ hr_pos.ne', Real.rpow_one])

private theorem sum_stripTracesMap_fst_apply [DecidableEq ι]
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (g : ∀ i, (C i).stripTraces)
    (t : ℝ) (j : ι) :
    ((((∑ i, stripTracesMap (piLpSingleCLM q₀ X₀ i) (piLpSingleCLM q₁ X₁ i)
      (piLp_single_compat C i) (g i) : (piLp q₀ q₁ C).stripTraces) :
        C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 t) : ∀ i, X₀ i) j =
      (g j).1.1 t := by
  rw [Submodule.coe_sum, Prod.fst_sum, ZeroAtInftyContinuousMap.coe_sum, Finset.sum_apply]
  change PiLp.continuousLinearEquiv q₀ ℂ X₀ (∑ i, _) j = _
  rw [map_sum, Finset.sum_apply]
  simp [piLpSingleCLM]

private theorem sum_stripTracesMap_snd_apply [DecidableEq ι]
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (g : ∀ i, (C i).stripTraces)
    (t : ℝ) (j : ι) :
    ((((∑ i, stripTracesMap (piLpSingleCLM q₀ X₀ i) (piLpSingleCLM q₁ X₁ i)
      (piLp_single_compat C i) (g i) : (piLp q₀ q₁ C).stripTraces) :
        C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 t) : ∀ i, X₁ i) j =
      (g j).1.2 t := by
  rw [Submodule.coe_sum, Prod.snd_sum, ZeroAtInftyContinuousMap.coe_sum, Finset.sum_apply]
  change PiLp.continuousLinearEquiv q₁ ℂ X₁ (∑ i, _) j = _
  rw [map_sum, Finset.sum_apply]
  simp [piLpSingleCLM]

private theorem norm_piLpFromCoord_le_top {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : (∞ : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (v : PiLp ∞ (fun i ↦ (C i).ComplexMethodSpace θ)) :
    ‖piLpFromCoord q₀ q₁ θ C v.ofLp‖ ≤ ‖v‖ := by
  classical
  obtain ⟨rfl, rfl⟩ := (eq_top_iff_of_inv_eq hθ hq).1 rfl
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  have hex (i : ι) : ∃ g : (C i).stripTraces,
      ComplexMethodSpace.mk θ g = v i ∧ ‖g‖ < ‖v‖ + δ :=
    ComplexMethodSpace.norm_lt_iff.1 ((PiLp.norm_apply_le v i).trans_lt (lt_add_of_pos_right _ hδ))
  choose g hg_mk hg_norm using hex
  let G : (piLp ∞ ∞ C).stripTraces :=
    ∑ i, stripTracesMap (piLpSingleCLM ∞ X₀ i) (piLpSingleCLM ∞ X₁ i)
      (piLp_single_compat C i) (g i)
  have hmk : ComplexMethodSpace.mk θ G = piLpFromCoord ∞ ∞ θ C v.ofLp := by
    rw [piLpFromCoord, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [piLpSingle, ← hg_mk i, ComplexMethodSpace.map_mk]
  rw [← hmk]
  refine (ComplexMethodSpace.norm_mk_le G).trans ?_
  rw [← Submodule.norm_coe]
  refine norm_prod_le_iff.2 ⟨?_, ?_⟩
  · refine (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t ↦ ?_
    rw [← toLp_ofLp ∞ ((G : C₀(ℝ, PiLp ∞ X₀) × C₀(ℝ, PiLp ∞ X₁)).1 t), PiLp.norm_toLp]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j ↦ ?_
    rw [sum_stripTracesMap_fst_apply]
    exact (ZeroAtInftyContinuousMap.norm_coe_le_norm _ _).trans
      ((norm_fst_le (g j).1).trans (hg_norm j).le)
  · refine (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t ↦ ?_
    rw [← toLp_ofLp ∞ ((G : C₀(ℝ, PiLp ∞ X₀) × C₀(ℝ, PiLp ∞ X₁)).2 t), PiLp.norm_toLp]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j ↦ ?_
    rw [sum_stripTracesMap_snd_apply]
    exact (ZeroAtInftyContinuousMap.norm_coe_le_norm _ _).trans
      ((norm_snd_le (g j).1).trans (hg_norm j).le)

private theorem norm_piLpFromCoord_le [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (v : PiLp q (fun i ↦ (C i).ComplexMethodSpace θ)) :
    ‖piLpFromCoord q₀ q₁ θ C v.ofLp‖ ≤ ‖v‖ := by
  classical
  by_cases hq_top : q = ∞
  · subst hq_top; exact norm_piLpFromCoord_le_top hθ hq C v
  rcases isEmpty_or_nonempty ι with hEmpty | hne
  · simp [piLpFromCoord]
  have hq_pos : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq_top
  have hc : (1 - θ) * (q.toReal * (q₀⁻¹).toReal) + θ * (q.toReal * (q₁⁻¹).toReal) = 1 := by
    linear_combination toReal_mul_inv_add ⟨hθ.1.le, hθ.2.le⟩ hq_top hq
  have hcont : Continuous fun δ : ℝ ↦ (∑ i, (‖v i‖ + δ) ^ q.toReal) ^ (1 / q.toReal) :=
    (continuous_finsetSum _ fun i _ ↦
      (continuous_const.add continuous_id).rpow_const fun _ ↦ Or.inr hq_pos.le).rpow_const
      fun _ ↦ Or.inr (by positivity)
  have hlim : Tendsto (fun δ : ℝ ↦ (∑ i, (‖v i‖ + δ) ^ q.toReal) ^ (1 / q.toReal))
      (𝓝[>] 0) (𝓝 ‖v‖) := by
    rw [PiLp.norm_eq_sum hq_pos v]
    simpa using (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ ↦ ?_)
  let b : ι → ℝ := fun i ↦ ‖v i‖ + δ
  have hb (i : ι) : 0 < b i := add_pos_of_nonneg_of_pos (norm_nonneg _) hδ
  set B := (∑ i, b i ^ q.toReal) ^ (1 / q.toReal)
  have hB : 0 < B := Real.rpow_pos_of_pos
    (Finset.sum_pos (fun i _ ↦ Real.rpow_pos_of_pos (hb i) _) Finset.univ_nonempty) _
  have hBq : B ^ q.toReal = ∑ i, b i ^ q.toReal := by
    dsimp only [B]
    rw [one_div, Real.rpow_inv_rpow
      (Finset.sum_nonneg fun i _ ↦ (Real.rpow_pos_of_pos (hb i) _).le) hq_pos.ne']
  choose g' hg'_mk hg'₀ hg'₁ using fun i ↦
    exists_weighted_trace (C i) ⟨hθ.1.le, hθ.2.le⟩ hc (hb i) hB (lt_add_of_pos_right ‖v i‖ hδ)
  let G : (piLp q₀ q₁ C).stripTraces :=
    ∑ i, stripTracesMap (piLpSingleCLM q₀ X₀ i) (piLpSingleCLM q₁ X₁ i) (piLp_single_compat C i)
      (g' i)
  have hmk : ComplexMethodSpace.mk θ G = piLpFromCoord q₀ q₁ θ C v.ofLp := by
    rw [piLpFromCoord, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [piLpSingle, ← hg'_mk i, ComplexMethodSpace.map_mk]
  rw [← hmk]
  refine (ComplexMethodSpace.norm_mk_le G).trans ?_
  rw [← Submodule.norm_coe]
  refine norm_prod_le_iff.2 ⟨?_, ?_⟩
  · refine (ZeroAtInftyContinuousMap.norm_le hB.le).2 fun t ↦ ?_
    rw [← toLp_ofLp q₀ ((G : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 t)]
    exact piLp_norm_le_of_coord_le q₀ hb hB hBq _ fun j ↦ by
      rw [sum_stripTracesMap_fst_apply]; exact hg'₀ j t
  · refine (ZeroAtInftyContinuousMap.norm_le hB.le).2 fun t ↦ ?_
    rw [← toLp_ofLp q₁ ((G : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 t)]
    exact piLp_norm_le_of_coord_le q₁ hb hB hBq _ fun j ↦ by
      rw [sum_stripTracesMap_snd_apply]; exact hg'₁ j t

/-! ### Main linear isometry equivalences -/

/-- **Complex interpolation of finite vector-valued `ℓ^q` products** (Bergh–Löfström,
Theorem 5.1.2). For `0 < θ < 1`, `1 ≤ q₀, q₁, q ≤ ∞`, and `1 / q = (1 - θ) / q₀ + θ / q₁`, the
coordinate projections assemble into a surjective linear isometry
`[PiLp q₀ X₀, PiLp q₁ X₁]_θ ≃ₗᵢ[ℂ] PiLp q (fun i ↦ [X₀ i, X₁ i]_θ)`. -/
def piLpComplexMethodEquiv [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) :
    (piLp q₀ q₁ C).ComplexMethodSpace θ ≃ₗᵢ[ℂ] PiLp q (fun i ↦ (C i).ComplexMethodSpace θ) :=
  LinearIsometryEquiv.ofBounds
    { toFun u := toLp q (fun i ↦ piLpCoord θ C i u)
      invFun v := piLpFromCoord q₀ q₁ θ C v.ofLp
      left_inv := piLpFromCoord_piLpCoord (q₀ := q₀) (q₁ := q₁) θ C
      right_inv v := PiLp.ext fun i ↦
        piLpCoord_piLpFromCoord (q₀ := q₀) (q₁ := q₁) θ C v.ofLp i
      map_add' u u' := PiLp.ext fun i ↦ map_add (piLpCoord θ C i) u u'
      map_smul' c u := PiLp.ext fun i ↦ map_smul (piLpCoord θ C i) c u }
    (norm_toLp_piLpCoord_le hθ hq C)
    (norm_piLpFromCoord_le hθ hq C)

/-- `piLpComplexMethodEquiv` acts by `piLpCoord` on each coordinate. -/
@[simp]
theorem piLpComplexMethodEquiv_apply [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (u : (piLp q₀ q₁ C).ComplexMethodSpace θ) (i : ι) :
    piLpComplexMethodEquiv hθ hq C u i = piLpCoord θ C i u := by
  rfl

/-- Applying `piLpCoord` to `(piLpComplexMethodEquiv hθ hq C).symm v` recovers `v i`. -/
@[simp]
theorem piLpCoord_piLpComplexMethodEquiv_symm [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (v : PiLp q (fun i ↦ (C i).ComplexMethodSpace θ)) (i : ι) :
    piLpCoord θ C i ((piLpComplexMethodEquiv hθ hq C).symm v) = v i := by
  exact piLpCoord_piLpFromCoord (q₀ := q₀) (q₁ := q₁) θ C v.ofLp i

/-- **Constant-fiber complex interpolation of finite `ℓ^q` spaces.**
For a complex normed space `X`, `0 < θ < 1`, and `1 / q = (1 - θ) / q₀ + θ / q₁`,
`[PiLp q₀ (fun _ : ι ↦ X), PiLp q₁ (fun _ : ι ↦ X)]_θ ≃ₗᵢ[ℂ] PiLp q (fun _ : ι ↦ X)`. -/
def piLpReflComplexMethodEquiv (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
    [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) :
    (piLp q₀ q₁ fun _ : ι ↦ refl ℂ X).ComplexMethodSpace θ ≃ₗᵢ[ℂ] PiLp q (fun _ : ι ↦ X) :=
  (piLpComplexMethodEquiv hθ hq fun _ : ι ↦ refl ℂ X).trans
    (LinearIsometryEquiv.piLpCongrRight q fun _ ↦
      ComplexMethodSpace.reflEquiv ⟨hθ.1.le, hθ.2.le⟩)

/-- `piLpReflComplexMethodEquiv` evaluates each coordinate in `X`. -/
@[simp]
theorem piLpReflComplexMethodEquiv_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (u : (piLp q₀ q₁ fun _ : ι ↦ refl ℂ X).ComplexMethodSpace θ) (i : ι) :
    piLpReflComplexMethodEquiv X hθ hq u i =
      (piLp q₀ q₁ fun _ : ι ↦ refl ℂ X).sumSpaceEmbed (ComplexMethodSpace.toSum u) i := by
  simp only [piLpReflComplexMethodEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrRight_apply, ofLp_toLp, piLpComplexMethodEquiv_apply]
  exact sumSpaceEmbed_toSum_piLpCoord θ (fun _ : ι ↦ refl ℂ X) i u

/-- The inverse of `piLpReflComplexMethodEquiv` embeds into `ι → X` by coordinate evaluation. -/
@[simp]
theorem sumSpaceEmbed_toSum_piLpReflComplexMethodEquiv_symm
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (v : PiLp q (fun _ : ι ↦ X)) (i : ι) :
    (piLp q₀ q₁ fun _ : ι ↦ refl ℂ X).sumSpaceEmbed
        (ComplexMethodSpace.toSum ((piLpReflComplexMethodEquiv X hθ hq).symm v)) i = v i := by
  rw [← piLpReflComplexMethodEquiv_apply hθ hq, LinearIsometryEquiv.apply_symm_apply]

end ComplexPiLp

end TauCeti.CompatibleCouple

end
