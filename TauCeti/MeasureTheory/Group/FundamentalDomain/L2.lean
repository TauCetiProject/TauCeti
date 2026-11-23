/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# `L²` of a space tiled by a fundamental domain

Let a countable group `Γ` act measurably on `α`, preserving a measure `μ`, and let `D` be a
fundamental domain for this action. The translates `γ⁻¹ • D` tile `α` up to null sets, so a
function `f ∈ L²(α, μ)` is the same as the family of its translates `x ↦ f (γ • x)` restricted to
`D`, and `‖f‖² = ∑ γ, ‖f (γ • ·)|_D‖²`. This file proves that this is an isometric isomorphism

`L²(α, μ; E) ≃ ℓ²(Γ, L²(D, μ; E))`, `f ↦ (γ ↦ f (γ • ·)|_D)`.

For a countable subgroup `Γ` of a locally compact group `G` acting by right translation (the action
of `Γᵐᵒᵖ`, `x ↦ x * γ`) and a fundamental domain `D` for it, this is the decomposition
`L²(G) ≃ ℓ²(Γ) ⊗ L²(D)` of Layer 9 of the VonNeumannAlgebras roadmap.

## Main definitions

* `MeasureTheory.Lp.restrictSMul 𝕜 D γ`: the continuous linear map
  `Lp E 2 μ →L[𝕜] Lp E 2 (μ.restrict D)`, `f ↦ f (γ • ·)|_D`.
* `MeasureTheory.IsFundamentalDomain.l2Equiv 𝕜 h`: for a fundamental domain `D`, the linear
  isometry equivalence `Lp E 2 μ ≃ₗᵢ[𝕜] lp (fun _ : Γ ↦ Lp E 2 (μ.restrict D)) 2` whose
  `γ`-component is `MeasureTheory.Lp.restrictSMul 𝕜 D γ`.

## Main results

* `MeasureTheory.IsFundamentalDomain.hasSum_norm_restrictSMul_sq`:
  `∑ γ, ‖f (γ • ·)|_D‖² = ‖f‖²`.
* `MeasureTheory.IsFundamentalDomain.l2Equiv_apply`,
  `MeasureTheory.IsFundamentalDomain.coeFn_l2Equiv_apply`: the components of `l2Equiv`.
-/

public section

open scoped ENNReal Pointwise
open Set

namespace MeasureTheory

variable {Γ α E : Type*} (𝕜 : Type*) [Group Γ] [MulAction Γ α] [MeasurableSpace α]
  [MeasurableConstSMul Γ α] {μ : Measure α} [SMulInvariantMeasure Γ α μ]
  [NormedAddCommGroup E] [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

namespace Lp

/-- The restriction to `D` of the translate `x ↦ f (γ • x)` of `f ∈ L²(α, μ)`, as a continuous
linear map `Lp E 2 μ →L[𝕜] Lp E 2 (μ.restrict D)`. -/
noncomputable def restrictSMul (D : Set α) (γ : Γ) : Lp E 2 μ →L[𝕜] Lp E 2 (μ.restrict D) :=
  (LpToLpRestrictCLM α E 𝕜 μ 2 D).comp
    (compMeasurePreservingₗᵢ 𝕜 (γ • · : α → α) (measurePreserving_smul γ μ)).toContinuousLinearMap

/-- `restrictSMul 𝕜 D γ f` is `x ↦ f (γ • x)` almost everywhere on `D`. -/
theorem coeFn_restrictSMul (D : Set α) (γ : Γ) (f : Lp E 2 μ) :
    restrictSMul 𝕜 D γ f =ᵐ[μ.restrict D] fun x ↦ f (γ • x) :=
  (LpToLpRestrictCLM_coeFn 𝕜 D _).trans
    (ae_restrict_of_ae (coeFn_compMeasurePreserving f (measurePreserving_smul γ μ)))

omit [MeasurableConstSMul Γ α] [SMulInvariantMeasure Γ α μ] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] in
/-- The square of the `L²` norm as an integral. -/
private theorem norm_sq_eq_lintegral {ν : Measure α} (f : Lp E 2 ν) :
    ‖f‖ ^ 2 = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ν).toReal := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero (Lp.aestronglyMeasurable f)
  push_cast at h
  rw [Lp.norm_def, ← h, ← ENNReal.toReal_rpow, Real.rpow_two]

omit [MeasurableConstSMul Γ α] [SMulInvariantMeasure Γ α μ] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] in
/-- The squared norm of an `L²` function has finite integral. -/
private theorem lintegral_ne_top {ν : Measure α} (f : Lp E 2 ν) :
    ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ν ≠ ∞ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero (Lp.aestronglyMeasurable f)
  push_cast at h
  rw [← h]
  exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (Lp.eLpNorm_ne_top f)

/-- The squared norm of `restrictSMul 𝕜 D γ f` is `∫⁻ x in D, ‖f (γ • x)‖ₑ ^ 2`. -/
theorem norm_restrictSMul_sq (D : Set α) (γ : Γ) (f : Lp E 2 μ) :
    ‖restrictSMul 𝕜 D γ f‖ ^ 2 = (∫⁻ x in D, ‖f (γ • x)‖ₑ ^ (2 : ℝ) ∂μ).toReal := by
  rw [norm_sq_eq_lintegral,
    lintegral_congr_ae ((coeFn_restrictSMul 𝕜 D γ f).mono fun x hx ↦ by rw [hx])]

end Lp

namespace IsFundamentalDomain

variable [Countable Γ] {D : Set α}

open Lp

/-- **Parseval for a fundamental domain.** The squared norms of the restrictions to `D` of the
translates of `f` sum to the squared norm of `f`. -/
theorem hasSum_norm_restrictSMul_sq (h : IsFundamentalDomain Γ D μ) (f : Lp E 2 μ) :
    HasSum (fun γ : Γ ↦ ‖restrictSMul 𝕜 D γ f‖ ^ 2) (‖f‖ ^ 2) := by
  have hsum := h.lintegral_eq_tsum'' fun x ↦ ‖f x‖ₑ ^ (2 : ℝ)
  have hne : ∑' γ : Γ, ∫⁻ x in D, ‖f (γ • x)‖ₑ ^ (2 : ℝ) ∂μ ≠ ∞ := hsum ▸ lintegral_ne_top f
  simp only [norm_restrictSMul_sq, norm_sq_eq_lintegral f, hsum]
  rw [ENNReal.tsum_toReal_eq fun γ ↦ ne_top_of_tsum_ne_top hne γ]
  exact (ENNReal.summable_toReal hne).hasSum

variable {𝕜}

private theorem memℓp_restrictSMul (h : IsFundamentalDomain Γ D μ) (f : Lp E 2 μ) :
    Memℓp (fun γ : Γ ↦ restrictSMul 𝕜 D γ f) 2 :=
  (memℓp_gen_iff (by norm_num)).2 <| by
    simpa using (h.hasSum_norm_restrictSMul_sq 𝕜 f).summable

/-- The isometry `f ↦ (γ ↦ f (γ • ·)|_D)` from `L²(α, μ)` to `ℓ²(Γ, L²(D, μ))`. -/
private noncomputable def toL2 (h : IsFundamentalDomain Γ D μ) :
    Lp E 2 μ →ₗᵢ[𝕜] lp (fun _ : Γ ↦ Lp E 2 (μ.restrict D)) 2 where
  toFun f := ⟨fun γ : Γ ↦ restrictSMul 𝕜 D γ f, h.memℓp_restrictSMul f⟩
  map_add' f g := lp.ext <| funext fun γ ↦ map_add (restrictSMul 𝕜 D γ) f g
  map_smul' c f := lp.ext <| funext fun γ ↦ map_smul (restrictSMul 𝕜 D γ) c f
  norm_map' f := by
    refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
      (⟨fun γ : Γ ↦ restrictSMul 𝕜 D γ f, h.memℓp_restrictSMul f⟩ :
        lp (fun _ : Γ ↦ Lp E 2 (μ.restrict D)) 2)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at this
    exact this.trans (h.hasSum_norm_restrictSMul_sq 𝕜 f).tsum_eq

omit [Countable Γ] in
/-- On a fundamental domain `D`, the extension by zero of `g ∈ L²(D, μ)` has translates restricting
to `g` at `γ = 1` and to `0` at every other `γ`. -/
private theorem exists_restrictSMul_eq_single [DecidableEq Γ] (h : IsFundamentalDomain Γ D μ)
    (g : Lp E 2 (μ.restrict D)) :
    ∃ f : Lp E 2 μ, ∀ γ : Γ, restrictSMul 𝕜 D γ f = if γ = 1 then g else 0 := by
  have hmem : MemLp (D.indicator g) 2 μ :=
    (memLp_indicator_iff_restrict h.nullMeasurableSet).2 (Lp.memLp g)
  refine ⟨hmem.toLp _, fun γ ↦ ?_⟩
  refine Lp.ext ((coeFn_restrictSMul 𝕜 D γ _).trans ?_)
  have hcomp : (fun x ↦ hmem.toLp _ (γ • x)) =ᵐ[μ] fun x ↦ D.indicator g (γ • x) :=
    (measurePreserving_smul γ μ).quasiMeasurePreserving.ae_eq_comp hmem.coeFn_toLp
  refine Filter.EventuallyEq.trans (ae_restrict_of_ae hcomp) ?_
  split_ifs with hγ
  · subst hγ
    filter_upwards [ae_restrict_mem₀ h.nullMeasurableSet] with x hx
    simp [indicator_of_mem hx]
  · -- Almost no point of `D` is moved into `D` by `γ ≠ 1`.
    have hdisj : ∀ᵐ x ∂μ.restrict D, x ∉ γ⁻¹ • D := by
      have := h.aedisjoint (inv_ne_one.2 hγ).symm
      rw [ae_iff, Measure.restrict_apply₀' h.nullMeasurableSet]
      simpa [AEDisjoint, inter_comm] using this
    filter_upwards [hdisj, (Lp.coeFn_zero E 2 (μ.restrict D))] with x hx hx0
    rw [hx0, Pi.zero_apply, indicator_of_notMem fun hγx ↦ hx ?_]
    exact mem_inv_smul_set_iff.2 hγx

omit [Countable Γ] in
/-- Restricting the translates of `f (γ⁻¹ • ·)` shifts the index by `γ⁻¹`. -/
private theorem restrictSMul_compMeasurePreserving (D : Set α) (γ δ : Γ) (f : Lp E 2 μ) :
    restrictSMul 𝕜 D δ (Lp.compMeasurePreserving (γ⁻¹ • · : α → α)
      (measurePreserving_smul γ⁻¹ μ) f) = restrictSMul 𝕜 D (γ⁻¹ * δ) f := by
  refine Lp.ext ((coeFn_restrictSMul 𝕜 D δ _).trans ?_)
  refine Filter.EventuallyEq.trans (ae_restrict_of_ae ?_) (coeFn_restrictSMul 𝕜 D _ f).symm
  have := (measurePreserving_smul δ μ).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving f (measurePreserving_smul γ⁻¹ μ))
  filter_upwards [this] with x hx
  simpa [mul_smul] using hx

variable [CompleteSpace E]

private theorem surjective_toL2 (h : IsFundamentalDomain Γ D μ) :
    Function.Surjective (h.toL2 (𝕜 := 𝕜) (E := E)) := by
  classical
  -- The range is closed, being the image of a complete space under an isometry.
  have hclosed : IsClosed (range (h.toL2 (𝕜 := 𝕜) (E := E))) :=
    h.toL2.isometry.isUniformInducing.isComplete_range.isClosed
  -- It contains the elements `lp.single 2 γ g`, the translates of extensions by zero.
  have hsingle (γ : Γ) (g : Lp E 2 (μ.restrict D)) :
      ∃ f, h.toL2 (𝕜 := 𝕜) f = lp.single 2 γ g := by
    obtain ⟨f, hf⟩ := h.exists_restrictSMul_eq_single (𝕜 := 𝕜) g
    refine ⟨Lp.compMeasurePreserving (γ⁻¹ • · : α → α) (measurePreserving_smul γ⁻¹ μ) f,
      lp.ext <| funext fun δ ↦ ?_⟩
    change restrictSMul 𝕜 D δ _ = (lp.single 2 γ g : (_ : Γ) → Lp E 2 (μ.restrict D)) δ
    rw [restrictSMul_compMeasurePreserving, hf, lp.single_apply, Pi.single_apply, inv_mul_eq_one,
      eq_comm (a := γ)]
  intro x
  refine hclosed.mem_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top x)
    (Filter.Eventually.of_forall fun s ↦ ⟨∑ γ ∈ s, (hsingle γ (x γ)).choose, ?_⟩)
  simp only [map_sum, fun γ ↦ (hsingle γ (x γ)).choose_spec]

variable (𝕜)

/-- **`L²` of a space tiled by a fundamental domain.** For a fundamental domain `D` of a countable
group `Γ` acting measurably on `α` and preserving `μ`, the linear isometry equivalence
`L²(α, μ; E) ≃ ℓ²(Γ, L²(D, μ; E))` sending `f` to the family of restrictions to `D` of its
translates `x ↦ f (γ • x)`. -/
noncomputable def l2Equiv (h : IsFundamentalDomain Γ D μ) :
    Lp E 2 μ ≃ₗᵢ[𝕜] lp (fun _ : Γ ↦ Lp E 2 (μ.restrict D)) 2 :=
  LinearIsometryEquiv.ofSurjective h.toL2 h.surjective_toL2

/-- The `γ`-component of `l2Equiv 𝕜 h f` is the restriction to `D` of `x ↦ f (γ • x)`. -/
@[simp]
theorem l2Equiv_apply (h : IsFundamentalDomain Γ D μ) (f : Lp E 2 μ) (γ : Γ) :
    h.l2Equiv 𝕜 f γ = restrictSMul 𝕜 D γ f :=
  (rfl)

/-- The `γ`-component of `l2Equiv 𝕜 h f` is `x ↦ f (γ • x)` almost everywhere on `D`. -/
theorem coeFn_l2Equiv_apply (h : IsFundamentalDomain Γ D μ) (f : Lp E 2 μ) (γ : Γ) :
    h.l2Equiv 𝕜 f γ =ᵐ[μ.restrict D] fun x ↦ f (γ • x) :=
  coeFn_restrictSMul 𝕜 D γ f

end IsFundamentalDomain

end MeasureTheory
