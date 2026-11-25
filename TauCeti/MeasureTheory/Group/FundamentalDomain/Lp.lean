/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.MeasureTheory.Function.Lp.ExtendByZero
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# `Lᵖ` of a space tiled by a fundamental domain

Let a countable group `Γ` act measurably on `α`, preserving a measure `μ`, and let `D` be a
fundamental domain for this action. The translates `γ⁻¹ • D` tile `α` up to null sets, so for
`1 ≤ p < ∞` a function `f ∈ Lᵖ(α, μ)` is the same as the family of its translates `x ↦ f (γ • x)`
restricted to `D`, and `‖f‖ ^ p = ∑ γ, ‖f (γ • ·)|_D‖ ^ p`. This file proves that this is an
isometric isomorphism

`Lᵖ(α, μ; E) ≃ ℓᵖ(Γ, Lᵖ(D, μ; E))`, `f ↦ (γ ↦ f (γ • ·)|_D)`,

together with its additive version for `IsAddFundamentalDomain`.

For a countable subgroup `Γ` of a group `G` carrying a right-invariant measure (for instance a
right Haar measure), acting by right translation (the action of `Γᵐᵒᵖ`, `x ↦ x * γ`), and a
fundamental domain `D` for it, this gives `L²(G) ≃ ℓ²(Γ, L²(D))`.

## Main definitions

* `MeasureTheory.Lp.restrictSMul 𝕜 p D γ`: the continuous linear map
  `Lp E p μ →L[𝕜] Lp E p (μ.restrict D)`, `f ↦ f (γ • ·)|_D`.
* `MeasureTheory.IsFundamentalDomain.lpEquiv 𝕜 h hp`: for a fundamental domain `D` and `p ≠ ∞`,
  the linear isometry equivalence `Lp E p μ ≃ₗᵢ[𝕜] lp (fun _ : Γ ↦ Lp E p (μ.restrict D)) p`
  whose `γ`-component is `MeasureTheory.Lp.restrictSMul 𝕜 p D γ`.

## Main results

* `MeasureTheory.IsFundamentalDomain.hasSum_norm_restrictSMul_rpow`:
  `∑ γ, ‖f (γ • ·)|_D‖ ^ p = ‖f‖ ^ p`.
* `MeasureTheory.IsFundamentalDomain.lpEquiv_apply`,
  `MeasureTheory.IsFundamentalDomain.coeFn_lpEquiv_apply`: the components of `lpEquiv`.
* `MeasureTheory.IsFundamentalDomain.lpEquiv_mk_smul_apply`: `lpEquiv` turns the translation
  `DomMulAct.mk γ • f` by `γ` into the shift of the index by `γ`.
* `MeasureTheory.IsFundamentalDomain.lpEquiv_symm_single`,
  `MeasureTheory.IsFundamentalDomain.coeFn_lpEquiv_symm_single`: the inverse of `lpEquiv` sends
  `g` placed at index `γ` to the translate by `γ⁻¹` of the extension of `g` by zero.
-/

public section

open scoped ENNReal Pointwise
open Set TauCeti

namespace MeasureTheory

variable {Γ α E : Type*} (𝕜 : Type*) [Group Γ] [MulAction Γ α] [MeasurableSpace α]
  [MeasurableConstSMul Γ α] {μ : Measure α} [SMulInvariantMeasure Γ α μ]
  [NormedAddCommGroup E] [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace Lp

variable (p) in
/-- The restriction to `D` of the translate `x ↦ f (γ • x)` of `f ∈ Lᵖ(α, μ)`, as a continuous
linear map `Lp E p μ →L[𝕜] Lp E p (μ.restrict D)`. -/
@[to_additive (dont_translate := 𝕜) /-- The restriction to `D` of the translate `x ↦ f (γ +ᵥ x)`
of `f ∈ Lᵖ(α, μ)`, as a continuous linear map `Lp E p μ →L[𝕜] Lp E p (μ.restrict D)`. -/]
noncomputable def restrictSMul (D : Set α) (γ : Γ) : Lp E p μ →L[𝕜] Lp E p (μ.restrict D) :=
  (LpToLpRestrictCLM α E 𝕜 μ p D).comp
    (compMeasurePreservingₗᵢ 𝕜 (γ • · : α → α) (measurePreserving_smul γ μ)).toContinuousLinearMap

/-- `restrictSMul 𝕜 p D γ f` is the restriction to `D` of the `DomMulAct` translate
`DomMulAct.mk γ • f`. -/
@[to_additive (dont_translate := 𝕜) /-- `restrictVAdd 𝕜 p D γ f` is the restriction to `D` of
the `DomAddAct` translate `DomAddAct.mk γ +ᵥ f`. -/]
theorem restrictSMul_apply (D : Set α) (γ : Γ) (f : Lp E p μ) :
    restrictSMul 𝕜 p D γ f = LpToLpRestrictCLM α E 𝕜 μ p D (DomMulAct.mk γ • f) :=
  (rfl)

/-- `restrictSMul 𝕜 p D γ f` is `x ↦ f (γ • x)` almost everywhere on `D`. -/
@[to_additive (dont_translate := 𝕜)
  /-- `restrictVAdd 𝕜 p D γ f` is `x ↦ f (γ +ᵥ x)` almost everywhere on `D`. -/]
theorem coeFn_restrictSMul (D : Set α) (γ : Γ) (f : Lp E p μ) :
    restrictSMul 𝕜 p D γ f =ᵐ[μ.restrict D] fun x ↦ f (γ • x) := by
  rw [restrictSMul_apply]
  exact (LpToLpRestrictCLM_coeFn 𝕜 D _).trans (ae_restrict_of_ae (DomMulAct.smul_Lp_ae_eq _ f))

/-- The `p`-th power of the norm of `restrictSMul 𝕜 p D γ f` is
`∫⁻ x in D, ‖f (γ • x)‖ₑ ^ p`. -/
@[to_additive (dont_translate := 𝕜) /-- The `p`-th power of the norm of
`restrictVAdd 𝕜 p D γ f` is `∫⁻ x in D, ‖f (γ +ᵥ x)‖ₑ ^ p`. -/]
theorem norm_restrictSMul_rpow (hp : p ≠ ∞) (D : Set α) (γ : Γ) (f : Lp E p μ) :
    ‖restrictSMul 𝕜 p D γ f‖ ^ p.toReal =
      (∫⁻ x in D, ‖f (γ • x)‖ₑ ^ p.toReal ∂μ).toReal := by
  rw [Lp.norm_def, ENNReal.toReal_rpow, ← lintegral_rpow_enorm_eq_eLpNorm_rpow
      (zero_lt_one.trans_le Fact.out).ne' hp (Lp.aestronglyMeasurable _),
    lintegral_congr_ae ((coeFn_restrictSMul 𝕜 D γ f).mono fun x hx ↦ by rw [hx])]

/-- Restricting the translates of `DomMulAct.mk γ • f` shifts the index by `γ`. -/
@[to_additive (dont_translate := 𝕜)
  /-- Restricting the translates of `DomAddAct.mk γ +ᵥ f` shifts the index by `γ`. -/]
theorem restrictSMul_mk_smul (D : Set α) (γ δ : Γ) (f : Lp E p μ) :
    restrictSMul 𝕜 p D δ (DomMulAct.mk γ • f) = restrictSMul 𝕜 p D (γ * δ) f := by
  rw [restrictSMul_apply, restrictSMul_apply, smul_smul, ← DomMulAct.mk_mul]

end Lp

namespace IsFundamentalDomain

variable [Countable Γ] {D : Set α}

open Lp

/-- **Parseval for a fundamental domain.** The `p`-th powers of the norms of the restrictions to
`D` of the translates of `f` sum to the `p`-th power of the norm of `f`. -/
@[to_additive (dont_translate := 𝕜) /-- **Parseval for an additive fundamental domain.** The
`p`-th powers of the norms of the restrictions to `D` of the translates of `f` sum to the `p`-th
power of the norm of `f`. -/]
theorem hasSum_norm_restrictSMul_rpow (h : IsFundamentalDomain Γ D μ) (hp : p ≠ ∞)
    (f : Lp E p μ) :
    HasSum (fun γ : Γ ↦ ‖restrictSMul 𝕜 p D γ f‖ ^ p.toReal) (‖f‖ ^ p.toReal) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hsum := h.lintegral_eq_tsum'' fun x ↦ ‖f x‖ₑ ^ p.toReal
  have hne : ∑' γ : Γ, ∫⁻ x in D, ‖f (γ • x)‖ₑ ^ p.toReal ∂μ ≠ ∞ :=
    hsum ▸ (lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hp0 hp (Lp.eLpNorm_lt_top f)).ne
  simp only [norm_restrictSMul_rpow 𝕜 hp]
  rw [Lp.norm_def, ENNReal.toReal_rpow,
    ← lintegral_rpow_enorm_eq_eLpNorm_rpow hp0 hp (Lp.aestronglyMeasurable f), hsum,
    ENNReal.tsum_toReal_eq fun γ ↦ ne_top_of_tsum_ne_top hne γ]
  exact (ENNReal.summable_toReal hne).hasSum

variable {𝕜}

/-- The isometry `f ↦ (γ ↦ f (γ • ·)|_D)` from `Lᵖ(α, μ)` to `ℓᵖ(Γ, Lᵖ(D, μ))`. -/
@[to_additive (dont_translate := 𝕜)
  /-- The isometry `f ↦ (γ ↦ f (γ +ᵥ ·)|_D)` from `Lᵖ(α, μ)` to `ℓᵖ(Γ, Lᵖ(D, μ))`. -/]
private noncomputable def toLpₗᵢ (h : IsFundamentalDomain Γ D μ) (hp : p ≠ ∞) :
    Lp E p μ →ₗᵢ[𝕜] lp (fun _ : Γ ↦ Lp E p (μ.restrict D)) p where
  toFun f := ⟨fun γ : Γ ↦ restrictSMul 𝕜 p D γ f,
    (memℓp_gen_iff (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp)).2
      (h.hasSum_norm_restrictSMul_rpow 𝕜 hp f).summable⟩
  map_add' f g := lp.ext <| funext fun γ ↦ map_add (restrictSMul 𝕜 p D γ) f g
  map_smul' c f := lp.ext <| funext fun γ ↦ map_smul (restrictSMul 𝕜 p D γ) c f
  norm_map' f := by
    have hp' := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
    rw [← Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) hp'.ne', lp.norm_rpow_eq_tsum hp']
    exact (h.hasSum_norm_restrictSMul_rpow 𝕜 hp f).tsum_eq

@[to_additive (dont_translate := 𝕜)]
private theorem toLpₗᵢ_apply (h : IsFundamentalDomain Γ D μ) (hp : p ≠ ∞) (f : Lp E p μ)
    (γ : Γ) : h.toLpₗᵢ (𝕜 := 𝕜) hp f γ = restrictSMul 𝕜 p D γ f :=
  rfl

omit [Countable Γ] in
/-- On a fundamental domain `D`, the extension by zero of `g ∈ Lᵖ(D, μ)` has translates restricting
to `g` at `γ = 1` and to `0` at every other `γ`. -/
@[to_additive (dont_translate := 𝕜) /-- On an additive fundamental domain `D`, the extension by
zero of `g ∈ Lᵖ(D, μ)` has translates restricting to `g` at `γ = 0` and to `0` at every other
`γ`. -/]
private theorem restrictSMul_castLpₗᵢ_extendByZeroLpₗᵢ [DecidableEq Γ]
    (h : IsFundamentalDomain Γ D μ) (γ : Γ) (g : Lp E p (μ.restrict D)) :
    restrictSMul 𝕜 p D γ (castLpₗᵢ (𝕜 := 𝕜) Measure.restrict_univ
      (extendByZeroLpₗᵢ 𝕜 μ h.nullMeasurableSet (subset_univ D) g)) = if γ = 1 then g else 0 := by
  refine Lp.ext ((coeFn_restrictSMul 𝕜 D γ _).trans ?_)
  refine Filter.EventuallyEq.trans (ae_restrict_of_ae ((measurePreserving_smul γ μ)
    |>.quasiMeasurePreserving.ae_eq_comp (coeFn_castLpₗᵢ_extendByZeroLpₗᵢ 𝕜 h.nullMeasurableSet g)))
    ?_
  split_ifs with hγ
  · subst hγ
    simpa only [Function.comp_def, one_smul] using indicator_ae_eq_restrict h.nullMeasurableSet
  · -- Almost no point of `D` is moved into `D` by `γ ≠ 1`.
    have hdisj : ∀ᵐ x ∂μ.restrict D, x ∉ γ⁻¹ • D := by
      have := h.aedisjoint (inv_ne_one.2 hγ).symm
      rw [ae_iff, Measure.restrict_apply₀' h.nullMeasurableSet]
      simpa [AEDisjoint, inter_comm] using this
    filter_upwards [hdisj, (Lp.coeFn_zero E p (μ.restrict D))] with x hx hx0
    rw [hx0, Pi.zero_apply, Function.comp_apply, indicator_of_notMem fun hγx ↦ hx ?_]
    exact mem_inv_smul_set_iff.2 hγx

/-- The translate by `γ⁻¹` of the extension by zero of `g` is sent by `toLpₗᵢ` to `g` placed at
index `γ`. -/
@[to_additive (dont_translate := 𝕜) /-- The translate by `-γ` of the extension by zero of `g` is
sent by `toLpₗᵢ` to `g` placed at index `γ`. -/]
private theorem toLpₗᵢ_mk_smul_extendByZeroLpₗᵢ [DecidableEq Γ]
    (h : IsFundamentalDomain Γ D μ) (hp : p ≠ ∞) (γ : Γ)
    (g : Lp E p (μ.restrict D)) :
    h.toLpₗᵢ (𝕜 := 𝕜) hp (DomMulAct.mk γ⁻¹ • castLpₗᵢ (𝕜 := 𝕜) Measure.restrict_univ
      (extendByZeroLpₗᵢ 𝕜 μ h.nullMeasurableSet (subset_univ D) g)) = lp.single p γ g := by
  refine lp.ext <| funext fun δ ↦ ?_
  rw [toLpₗᵢ_apply, restrictSMul_mk_smul, h.restrictSMul_castLpₗᵢ_extendByZeroLpₗᵢ,
    lp.single_apply, Pi.single_apply]
  simp only [inv_mul_eq_one, eq_comm (a := γ)]

variable [CompleteSpace E]

@[to_additive (dont_translate := 𝕜)]
private theorem surjective_toLpₗᵢ (h : IsFundamentalDomain Γ D μ) (hp : p ≠ ∞) :
    Function.Surjective (h.toLpₗᵢ (𝕜 := 𝕜) (E := E) hp) := by
  classical
  -- The range is closed, being the image of a complete space under an isometry.
  have hclosed : IsClosed (range (h.toLpₗᵢ (𝕜 := 𝕜) (E := E) hp)) :=
    (h.toLpₗᵢ hp).isometry.isUniformInducing.isComplete_range.isClosed
  -- It contains the elements `lp.single p γ g`, the translates of extensions by zero.
  intro x
  refine hclosed.mem_of_tendsto (lp.hasSum_single hp x) (Filter.Eventually.of_forall fun s ↦
    ⟨∑ γ ∈ s, DomMulAct.mk γ⁻¹ • castLpₗᵢ (𝕜 := 𝕜) Measure.restrict_univ
      (extendByZeroLpₗᵢ 𝕜 μ h.nullMeasurableSet (subset_univ D) (x γ)), ?_⟩)
  simp only [map_sum, toLpₗᵢ_mk_smul_extendByZeroLpₗᵢ]

variable (𝕜)

/-- **`Lᵖ` of a space tiled by a fundamental domain.** For a fundamental domain `D` of a countable
group `Γ` acting measurably on `α` and preserving `μ`, and `1 ≤ p < ∞`, the linear isometry
equivalence `Lᵖ(α, μ; E) ≃ ℓᵖ(Γ, Lᵖ(D, μ; E))` sending `f` to the family of restrictions to `D` of
its translates `x ↦ f (γ • x)`. -/
@[to_additive (dont_translate := 𝕜) /-- **`Lᵖ` of a space tiled by an additive fundamental
domain.** For a fundamental domain `D` of a countable additive group `Γ` acting measurably on `α`
and preserving `μ`, and `1 ≤ p < ∞`, the linear isometry equivalence
`Lᵖ(α, μ; E) ≃ ℓᵖ(Γ, Lᵖ(D, μ; E))` sending `f` to the family of restrictions to `D` of its
translates `x ↦ f (γ +ᵥ x)`. -/]
noncomputable def lpEquiv (h : IsFundamentalDomain Γ D μ) (hp : p ≠ ∞) :
    Lp E p μ ≃ₗᵢ[𝕜] lp (fun _ : Γ ↦ Lp E p (μ.restrict D)) p :=
  LinearIsometryEquiv.ofSurjective (h.toLpₗᵢ hp) (h.surjective_toLpₗᵢ hp)

/-- The `γ`-component of `lpEquiv 𝕜 h hp f` is the restriction to `D` of `x ↦ f (γ • x)`. -/
@[to_additive (attr := simp) (dont_translate := 𝕜) /-- The `γ`-component of
`lpEquiv 𝕜 h hp f` is the restriction to `D` of `x ↦ f (γ +ᵥ x)`. -/]
theorem lpEquiv_apply (h : IsFundamentalDomain Γ D μ) (hp : p ≠ ∞) (f : Lp E p μ) (γ : Γ) :
    h.lpEquiv 𝕜 hp f γ = restrictSMul 𝕜 p D γ f := by
  rw [lpEquiv, LinearIsometryEquiv.coe_ofSurjective, toLpₗᵢ_apply]

/-- The `γ`-component of `lpEquiv 𝕜 h hp f` is `x ↦ f (γ • x)` almost everywhere on `D`. -/
@[to_additive (dont_translate := 𝕜) /-- The `γ`-component of `lpEquiv 𝕜 h hp f` is
`x ↦ f (γ +ᵥ x)` almost everywhere on `D`. -/]
theorem coeFn_lpEquiv_apply (h : IsFundamentalDomain Γ D μ) (hp : p ≠ ∞) (f : Lp E p μ)
    (γ : Γ) : h.lpEquiv 𝕜 hp f γ =ᵐ[μ.restrict D] fun x ↦ f (γ • x) := by
  rw [lpEquiv_apply]
  exact coeFn_restrictSMul 𝕜 D γ f

/-- `lpEquiv` turns the translation `DomMulAct.mk γ • f` into the shift of the index by `γ`. -/
@[to_additive (dont_translate := 𝕜) /-- `lpEquiv` turns the translation `DomAddAct.mk γ +ᵥ f`
into the shift of the index by `γ`. -/]
theorem lpEquiv_mk_smul_apply (h : IsFundamentalDomain Γ D μ) (hp : p ≠ ∞)
    (γ δ : Γ) (f : Lp E p μ) :
    h.lpEquiv 𝕜 hp (DomMulAct.mk γ • f) δ = h.lpEquiv 𝕜 hp f (γ * δ) := by
  rw [lpEquiv_apply, lpEquiv_apply, restrictSMul_mk_smul]

/-- The inverse of `lpEquiv` sends `g ∈ Lᵖ(D, μ)` placed at index `γ` to the translate by `γ⁻¹` of
the extension of `g` by zero. -/
@[to_additive (dont_translate := 𝕜) /-- The inverse of `lpEquiv` sends `g ∈ Lᵖ(D, μ)` placed at
index `γ` to the translate by `-γ` of the extension of `g` by zero. -/]
theorem lpEquiv_symm_single [DecidableEq Γ] (h : IsFundamentalDomain Γ D μ) (hp : p ≠ ∞)
    (γ : Γ) (g : Lp E p (μ.restrict D)) :
    (h.lpEquiv 𝕜 hp).symm (lp.single p γ g) =
      DomMulAct.mk γ⁻¹ • castLpₗᵢ (𝕜 := 𝕜) Measure.restrict_univ
        (extendByZeroLpₗᵢ 𝕜 μ h.nullMeasurableSet (subset_univ D) g) :=
  (LinearIsometryEquiv.symm_apply_eq _).2 (h.toLpₗᵢ_mk_smul_extendByZeroLpₗᵢ hp γ g).symm

/-- The inverse of `lpEquiv` sends `g ∈ Lᵖ(D, μ)` placed at index `γ` to `x ↦ g (γ⁻¹ • x)` on
`γ • D`, extended by zero. -/
@[to_additive (dont_translate := 𝕜) /-- The inverse of `lpEquiv` sends `g ∈ Lᵖ(D, μ)` placed at
index `γ` to `x ↦ g (-γ +ᵥ x)` on `γ +ᵥ D`, extended by zero. -/]
theorem coeFn_lpEquiv_symm_single [DecidableEq Γ] (h : IsFundamentalDomain Γ D μ) (hp : p ≠ ∞)
    (γ : Γ) (g : Lp E p (μ.restrict D)) :
    (h.lpEquiv 𝕜 hp).symm (lp.single p γ g) =ᵐ[μ] fun x ↦ D.indicator g (γ⁻¹ • x) := by
  rw [lpEquiv_symm_single]
  exact (DomMulAct.smul_Lp_ae_eq _ _).trans
    ((measurePreserving_smul γ⁻¹ μ).quasiMeasurePreserving.ae_eq_comp
      (coeFn_castLpₗᵢ_extendByZeroLpₗᵢ 𝕜 h.nullMeasurableSet g))

end IsFundamentalDomain

end MeasureTheory
