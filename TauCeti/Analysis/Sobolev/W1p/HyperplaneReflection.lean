/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HyperplaneReflection
public import TauCeti.Analysis.Normed.Affine.Isometry.Basic
public import TauCeti.Analysis.Sobolev.W1p.ChangeOfVariables
import TauCeti.Analysis.Sobolev.W1p.Localization
import TauCeti.Analysis.Sobolev.W1p.VanishingBoundary

/-!
# Sobolev functions under the reflection in a hyperplane

Let `ρ = TauCeti.hyperplaneReflection ν c` be the reflection in the hyperplane `{x | ⟪x, ν⟫ = c}`
of a finite-dimensional real inner product space, and let `U` be an open set with `ρ U ⊆ U`. For
`1 ≤ p < ∞`, precomposition with `ρ` is a bounded operator `W1p.compHyperplaneReflectionL` on
`W^{1,p}(U)`, an involution, with value `u ∘ ρ` and weak gradient `R (∇u ∘ ρ)`, where
`R = (ℝ ∙ ν)ᗮ.reflection` is the linear part of `ρ`.

Let `H = {x | c < ⟪x, ν⟫}` be the open half-space on one side of the hyperplane. For
`φ ∈ W^{1,p}_0(U)` the restriction of `φ - φ ∘ ρ` to `U ∩ H` lies in `W^{1,p}_0(U ∩ H)`
(`TauCeti.W1p.restrictL_sub_compHyperplaneReflectionL_mem_w1p0Submodule`): it vanishes on the
hyperplane, which `ρ` fixes, and on the rest of the boundary of `U ∩ H` because `φ` does. This is
what makes the odd reflection of a solution of a divergence-form equation on `U ∩ H` with zero
boundary values on the flat part a solution on all of `U`: the reflected equation tested against
`φ` is the original equation tested against `φ - φ ∘ ρ`. The bounded operator
`W1p0.restrictSubCompHyperplaneReflectionL` packages this map
`W^{1,p}_0(U) → W^{1,p}_0(U ∩ H)`.

## The argument

The set of `φ ∈ W^{1,p}(U)` whose image lies in `W^{1,p}_0(U ∩ H)` is closed, so it suffices to
treat test functions `φ`. Then `g = φ - φ ∘ ρ` is continuous and vanishes outside the compact set
`K = tsupport φ ∪ ρ (tsupport φ) ⊆ U`. On the bounded open set `U ∩ H ∩ B`, for a ball `B ⊇ K`,
it vanishes on the frontier: frontier points outside `U ∩ B` lie outside `K`, and those inside
lie on the hyperplane, where `g x = φ x - φ (ρ x) = 0`. So the restriction of `g` lies in
`W^{1,p}_0(U ∩ H ∩ B)` (`TauCeti.W1p.mem_w1p0Submodule_of_continuousOn_closure`), and since it
vanishes near `∂B` its extension by zero lies in `W^{1,p}_0(U ∩ H)`
(`TauCeti.W1p.mem_w1p0Submodule_of_inter_eq_of_isCompact`).

## Main declarations

* `TauCeti.W1p.compHyperplaneReflectionL`: precomposition with the hyperplane reflection.
* `TauCeti.W1p.compHyperplaneReflectionL_compHyperplaneReflectionL`: it is an involution.
* `TauCeti.W1p.value_sub_compHyperplaneReflectionL_ae`: the odd reflection `u - u ∘ ρ` of a
  function vanishing off `H` agrees with it on `U ∩ H`.
* `TauCeti.W1p.restrictL_sub_compHyperplaneReflectionL_mem_w1p0Submodule`: the restriction of
  `φ - φ ∘ ρ` to `U ∩ H` has zero boundary values when `φ` does.
* `TauCeti.W1p0.restrictSubCompHyperplaneReflectionL`: the bounded operator
  `φ ↦ (φ - φ ∘ ρ)|_{U ∩ H}` from `W^{1,p}_0(U)` to `W^{1,p}_0(U ∩ H)`, and
  `TauCeti.W1p.value_restrictL_sub_compHyperplaneReflectionL_ae`: the value of
  `(u - u ∘ ρ)|_{U ∩ H}` is `u - u ∘ ρ`.
* `TauCeti.W1p0.setIntegral_mul_value_restrictSubCompHyperplaneReflectionL`: integrating a
  function `f` against `(φ - φ ∘ ρ)|_{U ∩ H}` is integrating its odd reflection against `φ`.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Metric InnerProductSpace
open scoped Distributions

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {U H : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {ν : E} {c : ℝ}

/-- **Precomposition with the reflection in a hyperplane**, as a bounded operator on
`W^{1,p}(U)` for an open set `U` mapped into itself by the reflection. Its value is `u ∘ ρ`
(`TauCeti.W1p.value_compHyperplaneReflectionL_ae`) and its weak gradient is `R (∇u ∘ ρ)`, where
`R` is the linear part of `ρ` (`TauCeti.W1p.gradient_compHyperplaneReflectionL_ae`). -/
def W1p.compHyperplaneReflectionL (hp : p ≠ ⊤) (ν : E) (c : ℝ)
    (hU : MapsTo (hyperplaneReflection ν c) U U) : W1p mu U p →L[ℝ] W1p mu U p :=
  W1p.compL (hyperplaneReflection ν c) hp
    (differentiable_hyperplaneReflection ν c).differentiableOn
    (hyperplaneReflection ν c).injective.injOn hU
    (fun x _ => AffineIsometryEquiv.norm_fderiv_le _ x) one_pos
    (fun x _ => (abs_det_fderiv_hyperplaneReflection ν c x).ge)

/-- Precomposition with the hyperplane reflection is the change of variables `W1p.compL` along
the reflection, which is differentiable and injective with derivative of norm at most one and
determinant of absolute value one. -/
theorem W1p.compHyperplaneReflectionL_eq_compL (hp : p ≠ ⊤)
    (hU : MapsTo (hyperplaneReflection ν c) U U) :
    W1p.compHyperplaneReflectionL (mu := mu) hp ν c hU =
      W1p.compL (hyperplaneReflection ν c) hp
        (differentiable_hyperplaneReflection ν c).differentiableOn
        (hyperplaneReflection ν c).injective.injOn hU
        (fun x _ => AffineIsometryEquiv.norm_fderiv_le _ x) one_pos
        (fun x _ => (abs_det_fderiv_hyperplaneReflection ν c x).ge) := by
  rw [W1p.compHyperplaneReflectionL]

/-- The value of `u ∘ ρ` is the composition of the value of `u` with `ρ`. -/
theorem W1p.value_compHyperplaneReflectionL_ae (hp : p ≠ ⊤)
    (hU : MapsTo (hyperplaneReflection ν c) U U) (u : W1p mu U p) :
    W1p.value (W1p.compHyperplaneReflectionL hp ν c hU u) =ᵐ[mu.restrict U]
      fun x => W1p.value u (hyperplaneReflection ν c x) := by
  rw [W1p.compHyperplaneReflectionL]
  exact W1p.value_compL_ae _ _ _ _ _ _ _ _ u

/-- The weak gradient of `u ∘ ρ` is the gradient of `u` at `ρ x`, reflected by the linear part
`(ℝ ∙ ν)ᗮ.reflection` of `ρ`. -/
theorem W1p.gradient_compHyperplaneReflectionL_ae (hp : p ≠ ⊤)
    (hU : MapsTo (hyperplaneReflection ν c) U U) (u : W1p mu U p) :
    W1p.gradient (W1p.compHyperplaneReflectionL hp ν c hU u) =ᵐ[mu.restrict U]
      fun x => (ℝ ∙ ν)ᗮ.reflection (W1p.gradient u (hyperplaneReflection ν c x)) := by
  rw [W1p.compHyperplaneReflectionL]
  filter_upwards [W1p.gradient_compL_ae _ _ _ _ _ _ _ _ u] with x hx
  rw [hx, fderiv_hyperplaneReflection,
    (Submodule.isSelfAdjoint_reflection _).adjoint_eq, LinearIsometryEquiv.coe_coe'']

/-- Precomposition with the hyperplane reflection is an involution. -/
@[simp]
theorem W1p.compHyperplaneReflectionL_compHyperplaneReflectionL (hp : p ≠ ⊤)
    (hU : MapsTo (hyperplaneReflection ν c) U U) (u : W1p mu U p) :
    W1p.compHyperplaneReflectionL hp ν c hU (W1p.compHyperplaneReflectionL hp ν c hU u) = u := by
  rw [W1p.compHyperplaneReflectionL]
  exact W1p.compL_compL_of_leftInvOn _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun x _ => hyperplaneReflection_hyperplaneReflection ν c x) u

/-- **The odd reflection extends a function vanishing off the half-space.** If `u ∈ W^{1,p}(U)`
vanishes on `U ∖ H`, where `H = {x | c < ⟪x, ν⟫}`, then `u - u ∘ ρ` agrees with `u` on `U ∩ H`. -/
theorem W1p.value_sub_compHyperplaneReflectionL_ae (hp : p ≠ ⊤) (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c < ⟪x, ν⟫_ℝ) (hU : MapsTo (hyperplaneReflection ν c) U U)
    {u : W1p mu U p} (hu0 : ∀ᵐ x ∂mu.restrict U, x ∉ H → W1p.value u x = 0) :
    W1p.value (u - W1p.compHyperplaneReflectionL hp ν c hU u) =ᵐ[mu.restrict (U ⊓ H)]
      W1p.value u := by
  have hρ : ∀ᵐ x ∂mu.restrict U,
      hyperplaneReflection ν c x ∉ H → W1p.value u (hyperplaneReflection ν c x) = 0 :=
    (measurePreserving_restrict_hyperplaneReflection hU
      U.isOpen.measurableSet).quasiMeasurePreserving.ae hu0
  have h : ∀ᵐ x ∂mu.restrict U, x ∈ H →
      W1p.value (u - W1p.compHyperplaneReflectionL hp ν c hU u) x = W1p.value u x := by
    filter_upwards [W1p.value_sub_ae u (W1p.compHyperplaneReflectionL hp ν c hU u),
      W1p.value_compHyperplaneReflectionL_ae hp hU u, hρ] with x h1 h2 h3 hxH
    have hρH : hyperplaneReflection ν c x ∉ H := fun h =>
      lt_asymm ((inner_hyperplaneReflection_lt_iff hν c).2 ((hH x).1 hxH)) ((hH _).1 h)
    rw [h1, Pi.sub_apply, h2, h3 hρH, sub_zero]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left h,
    ae_restrict_mem (U ⊓ H).isOpen.measurableSet] with x hx hxUH
  exact hx (Opens.mem_inf.1 hxUH).2

/-- The restriction of `u - u ∘ ρ` to `U ∩ H` has value `u - u ∘ ρ`. -/
theorem W1p.value_restrictL_sub_compHyperplaneReflectionL_ae (hp : p ≠ ⊤)
    (hU : MapsTo (hyperplaneReflection ν c) U U) (u : W1p mu U p) :
    W1p.value (W1p.restrictL (inf_le_left : U ⊓ H ≤ U)
      (u - W1p.compHyperplaneReflectionL hp ν c hU u)) =ᵐ[mu.restrict (U ⊓ H : Opens E)]
        fun x => W1p.value u x - W1p.value u (hyperplaneReflection ν c x) := by
  have hU' : ∀ᵐ x ∂mu.restrict U, W1p.value (u - W1p.compHyperplaneReflectionL hp ν c hU u) x =
      W1p.value u x - W1p.value u (hyperplaneReflection ν c x) := by
    filter_upwards [W1p.value_sub_ae u (W1p.compHyperplaneReflectionL hp ν c hU u),
      W1p.value_compHyperplaneReflectionL_ae hp hU u] with x h1 h2
    rw [h1, Pi.sub_apply, h2]
  filter_upwards [W1p.value_restrictL_ae (inf_le_left : U ⊓ H ≤ U)
      (u - W1p.compHyperplaneReflectionL hp ν c hU u),
    ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 inf_le_left) hU'] with x h1 h2
  rw [h1, h2]

/-- For a test function `φ`, the restriction of `φ - φ ∘ ρ` to `U ∩ H` has value `φ - φ ∘ ρ`. -/
private theorem value_restrictL_sub_compHyperplaneReflectionL_ofTestFunction_ae (hp : p ≠ ⊤)
    (hU : MapsTo (hyperplaneReflection ν c) U U) (φ : 𝓓(U, ℝ)) :
    W1p.value (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) (W1p.ofTestFunctionₗ mu U p φ -
      W1p.compHyperplaneReflectionL hp ν c hU (W1p.ofTestFunctionₗ mu U p φ))) =ᵐ[mu.restrict
        (U ⊓ H : Opens E)] fun x => φ x - φ (hyperplaneReflection ν c x) := by
  set ψ := W1p.ofTestFunctionₗ mu U p φ
  have hψ := W1p.value_ofTestFunctionₗ_ae (mu := mu) (p := p) φ
  have hcomp : (fun x => W1p.value ψ (hyperplaneReflection ν c x)) =ᵐ[mu.restrict U]
      fun x => φ (hyperplaneReflection ν c x) :=
    (measurePreserving_restrict_hyperplaneReflection hU
      U.isOpen.measurableSet).quasiMeasurePreserving.ae_eq_comp hψ
  have hUH : ((U ⊓ H : Opens E) : Set E) ⊆ U := SetLike.coe_subset_coe.2 inf_le_left
  filter_upwards [W1p.value_restrictL_sub_compHyperplaneReflectionL_ae hp hU ψ,
    ae_restrict_of_ae_restrict_of_subset hUH hψ, ae_restrict_of_ae_restrict_of_subset hUH hcomp]
    with x h1 h2 h3
  rw [h1, h2, h3]

/-- For a test function `φ`, the restriction of `φ - φ ∘ ρ` to `U ∩ H` lies in
`W^{1,p}_0(U ∩ H)`. -/
private theorem restrictL_sub_compHyperplaneReflectionL_ofTestFunction_mem (hp : p ≠ ⊤)
    (hH : ∀ x, x ∈ H ↔ c < ⟪x, ν⟫_ℝ) (hU : MapsTo (hyperplaneReflection ν c) U U)
    (φ : 𝓓(U, ℝ)) :
    W1p.restrictL (inf_le_left : U ⊓ H ≤ U) (W1p.ofTestFunctionₗ mu U p φ -
      W1p.compHyperplaneReflectionL hp ν c hU (W1p.ofTestFunctionₗ mu U p φ)) ∈
        w1p0Submodule mu (U ⊓ H) p := by
  set ρ := hyperplaneReflection ν c
  set ψ := W1p.ofTestFunctionₗ mu U p φ
  set w := W1p.restrictL (inf_le_left : U ⊓ H ≤ U) (ψ - W1p.compHyperplaneReflectionL hp ν c hU ψ)
  set g : E → ℝ := fun x => φ x - φ (ρ x)
  have hg : Continuous g := φ.continuous.sub (φ.continuous.comp ρ.continuous)
  -- `g` vanishes outside the compact set `K = tsupport φ ∪ ρ (tsupport φ) ⊆ U`.
  set K := tsupport (φ : E → ℝ) ∪ ρ '' tsupport (φ : E → ℝ)
  have hK : IsCompact K := φ.hasCompactSupport.isCompact.union
    (φ.hasCompactSupport.isCompact.image ρ.continuous)
  have hKU : K ⊆ U :=
    union_subset φ.tsupport_subset ((image_mono φ.tsupport_subset).trans hU.image_subset)
  have hg0 : ∀ x ∉ K, g x = 0 := fun x hx => by
    have h1 : x ∉ tsupport (φ : E → ℝ) := fun h => hx (Or.inl h)
    have h2 : ρ x ∉ tsupport (φ : E → ℝ) := fun h =>
      hx (Or.inr ⟨ρ x, h, hyperplaneReflection_hyperplaneReflection ν c x⟩)
    simp [g, image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]
  -- The value of `w` is `g` almost everywhere on `U ∩ H`.
  have hwg : W1p.value w =ᵐ[mu.restrict (U ⊓ H : Opens E)] g :=
    value_restrictL_sub_compHyperplaneReflectionL_ofTestFunction_ae hp hU φ
  -- Cut off far away: a ball `B ⊇ K` makes the domain bounded.
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : E)
  let B : Opens E := ⟨ball 0 R, isOpen_ball⟩
  let Ω : Opens E := (U ⊓ H) ⊓ B
  have hΩ : Ω ≤ U ⊓ H := inf_le_left
  have hKB : K ⊆ (B : Set E) := hR
  have hmemΩ : W1p.restrictL hΩ w ∈ w1p0Submodule mu Ω p := by
    refine W1p.mem_w1p0Submodule_of_continuousOn_closure hp
      (isBounded_ball.subset fun x (hx : x ∈ (Ω : Set E)) => hx.2) hg.continuousOn
      (fun x hx => ?_) ?_
    · -- On the frontier of `Ω`, `g` vanishes.
      by_cases hxUB : x ∈ (U : Set E) ∩ B
      · have hxΩ : x ∉ (Ω : Set E) := fun h => (Ω.isOpen.frontier_eq ▸ hx).2 h
        have hxH : x ∉ (H : Set E) := fun h => hxΩ ⟨⟨hxUB.1, h⟩, hxUB.2⟩
        have hΩH : (Ω : Set E) ⊆ H := fun y hy => hy.1.2
        have hxc : x ∈ closure (H : Set E) := closure_mono hΩH (frontier_subset_closure hx)
        have hρx : ρ x = x := hyperplaneReflection_eq_self_of_mem_closure hH hxc hxH
        simp [g, hρx]
      · exact hg0 x fun hxK => hxUB ⟨hKU hxK, hKB hxK⟩
    · filter_upwards [W1p.value_restrictL_ae hΩ w,
        ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 hΩ) hwg] with x h1 h2
      rw [h1, h2]
  refine W1p.mem_w1p0Submodule_of_inter_eq_of_isCompact (U := B) ?_ hK hKB hmemΩ ?_ ?_
  · ext x
    simp only [Ω, Opens.coe_inf, mem_inter_iff]
    tauto
  · filter_upwards [W1p.value_restrictL_ae hΩ w,
      ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 hΩ) hwg] with x h1 h2 hxK
    rw [h1, h2, hg0 x hxK]
  · filter_upwards [hwg, ae_restrict_of_ae ((ae_restrict_iff' Ω.isOpen.measurableSet).1
      (W1p.value_restrictL_ae hΩ w)), ae_restrict_mem (U ⊓ H).isOpen.measurableSet]
      with x hx hres hxUH
    by_cases hxB : x ∈ (B : Set E)
    · rw [indicator_of_mem (⟨hxUH, hxB⟩ : x ∈ (Ω : Set E)), hres ⟨hxUH, hxB⟩]
    · rw [hx, hg0 x fun hxK => hxB (hKB hxK),
        indicator_of_notMem fun (h : x ∈ (Ω : Set E)) => hxB h.2]

/-- **Zero boundary values of the reflected difference.** Let `H = {x | c < ⟪x, ν⟫}` and let `U`
be an open set mapped into itself by the reflection `ρ` in the hyperplane `∂H`. For
`φ ∈ W^{1,p}_0(U)`, `p < ∞`, the restriction of `φ - φ ∘ ρ` to `U ∩ H` lies in
`W^{1,p}_0(U ∩ H)`. -/
theorem W1p.restrictL_sub_compHyperplaneReflectionL_mem_w1p0Submodule (hp : p ≠ ⊤)
    (hH : ∀ x, x ∈ H ↔ c < ⟪x, ν⟫_ℝ) (hU : MapsTo (hyperplaneReflection ν c) U U)
    {φ : W1p mu U p} (hφ : φ ∈ w1p0Submodule mu U p) :
    W1p.restrictL (inf_le_left : U ⊓ H ≤ U) (φ - W1p.compHyperplaneReflectionL hp ν c hU φ) ∈
      w1p0Submodule mu (U ⊓ H) p := by
  let T : W1p mu U p →L[ℝ] W1p mu (U ⊓ H) p := (W1p.restrictL inf_le_left).comp
    (ContinuousLinearMap.id ℝ _ - W1p.compHyperplaneReflectionL hp ν c hU)
  exact w1p0Submodule_subset_of_isClosed
    ((w1p0Submodule mu (U ⊓ H) p).isClosed.preimage T.continuous)
    (restrictL_sub_compHyperplaneReflectionL_ofTestFunction_mem hp hH hU) hφ

/-- The bounded operator `φ ↦ (φ - φ ∘ ρ)|_{U ∩ H}` from `W^{1,p}_0(U)` to `W^{1,p}_0(U ∩ H)`,
where `ρ` is the reflection in the boundary hyperplane of the half-space
`H = {x | c < ⟪x, ν⟫}` and `U` is mapped into itself by `ρ`
(`TauCeti.W1p.restrictL_sub_compHyperplaneReflectionL_mem_w1p0Submodule`). -/
def W1p0.restrictSubCompHyperplaneReflectionL (hp : p ≠ ⊤) (hH : ∀ x, x ∈ H ↔ c < ⟪x, ν⟫_ℝ)
    (hU : MapsTo (hyperplaneReflection ν c) U U) : W1p0 mu U p →L[ℝ] W1p0 mu (U ⊓ H) p :=
  ContinuousLinearMap.codRestrict
    ((W1p.restrictL (inf_le_left : U ⊓ H ≤ U)).comp
      ((ContinuousLinearMap.id ℝ (W1p mu U p) - W1p.compHyperplaneReflectionL hp ν c hU).comp
        (w1p0Submodule mu U p).toSubmodule.subtypeL))
    (w1p0Submodule mu (U ⊓ H) p).toSubmodule
    fun φ => by
      simpa using W1p.restrictL_sub_compHyperplaneReflectionL_mem_w1p0Submodule hp hH hU φ.2

/-- The underlying Sobolev function of `(φ - φ ∘ ρ)|_{U ∩ H}`. -/
theorem W1p0.coe_restrictSubCompHyperplaneReflectionL (hp : p ≠ ⊤)
    (hH : ∀ x, x ∈ H ↔ c < ⟪x, ν⟫_ℝ) (hU : MapsTo (hyperplaneReflection ν c) U U)
    (φ : W1p0 mu U p) :
    (W1p0.restrictSubCompHyperplaneReflectionL hp hH hU φ : W1p mu (U ⊓ H) p) =
      W1p.restrictL (inf_le_left : U ⊓ H ≤ U)
        ((φ : W1p mu U p) - W1p.compHyperplaneReflectionL hp ν c hU φ) := by
  simp [W1p0.restrictSubCompHyperplaneReflectionL]

/-- **Testing against the reflected difference.** Let `H = {x | c < ⟪x, ν⟫}` and let `U` be an
open set mapped into itself by the reflection `ρ` in the hyperplane `∂H`. For `φ ∈ W^{1,p}_0(U)`,
`p < ∞`, and `f ∈ L^q(U ∩ H)` with `1/q + 1/p = 1`, integrating `f` against the restriction of
`φ - φ ∘ ρ` to `U ∩ H` is integrating the odd reflection `x ↦ 1_H f x - 1_H f (ρ x)` of `f`
against `φ` on `U`:

`∫_{U ∩ H} f (φ - φ ∘ ρ) = ∫_U (1_H f - 1_H f ∘ ρ) φ`.

This turns a right-hand side `f` of an equation on `U ∩ H` into the right-hand side of the
reflected equation on `U`. -/
theorem W1p0.setIntegral_mul_value_restrictSubCompHyperplaneReflectionL (hp : p ≠ ⊤)
    (hH : ∀ x, x ∈ H ↔ c < ⟪x, ν⟫_ℝ) (hU : MapsTo (hyperplaneReflection ν c) U U)
    {q : ENNReal} [q.HolderTriple p 1] {f : E → ℝ} (hf : MemLp f q (mu.restrict (U ⊓ H)))
    (φ : W1p0 mu U p) :
    ∫ x in U ⊓ H, f x * W1p.value
        (W1p0.restrictSubCompHyperplaneReflectionL hp hH hU φ : W1p mu (U ⊓ H) p) x ∂mu =
      ∫ x in U, ((H : Set E).indicator f x -
        (H : Set E).indicator f (hyperplaneReflection ν c x)) *
          W1p.value (φ : W1p mu U p) x ∂mu := by
  set ρ := hyperplaneReflection ν c
  set g := (H : Set E).indicator f
  set v : E → ℝ := ⇑(W1p.value (φ : W1p mu U p))
  have hρ : MeasurePreserving ρ (mu.restrict U) (mu.restrict U) :=
    measurePreserving_restrict_hyperplaneReflection hU U.isOpen.measurableSet
  have hHm : MeasurableSet (H : Set E) := H.isOpen.measurableSet
  have hg : MemLp g q (mu.restrict U) := by
    rw [memLp_indicator_iff_restrict hHm.nullMeasurableSet, Measure.restrict_restrict hHm,
      inter_comm]
    exact hf
  have hv : MemLp v p (mu.restrict U) := Lp.memLp _
  have hvρ : MemLp (v ∘ ρ) p (mu.restrict U) := hv.comp_measurePreserving hρ
  -- The value of the reflected difference is `v - v ∘ ρ` on `U ∩ H`.
  have hval : W1p.value
      (W1p0.restrictSubCompHyperplaneReflectionL hp hH hU φ : W1p mu (U ⊓ H) p) =ᵐ[mu.restrict
        (U ⊓ H : Opens E)] fun x => v x - v (ρ x) := by
    rw [W1p0.coe_restrictSubCompHyperplaneReflectionL]
    exact W1p.value_restrictL_sub_compHyperplaneReflectionL_ae hp hU _
  have hgv : Integrable (fun x => g x * v x) (mu.restrict U) := hg.integrable_mul hv
  -- Testing `g` against `v ∘ ρ` is testing `g ∘ ρ` against `v`, since `ρ` is an involution.
  have hswap : ∫ x in U, g x * v (ρ x) ∂mu = ∫ x in U, g (ρ x) * v x ∂mu := by
    have h := MeasurePreserving.integral_comp hρ ρ.toHomeomorph.measurableEmbedding
      fun x => g (ρ x) * v x
    simpa only [AffineIsometryEquiv.coe_toHomeomorph, ρ, hyperplaneReflection_hyperplaneReflection]
      using h
  calc ∫ x in U ⊓ H, f x * W1p.value
          (W1p0.restrictSubCompHyperplaneReflectionL hp hH hU φ : W1p mu (U ⊓ H) p) x ∂mu
      = ∫ x in U ⊓ H, f x * (v x - v (ρ x)) ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [hval] with x hx
        rw [hx]
    _ = ∫ x in U, g x * (v x - v (ρ x)) ∂mu := by
        rw [← setIntegral_indicator hHm]
        exact integral_congr_ae (ae_of_all _ fun x => indicator_mul_left _ _ _)
    _ = ∫ x in U, g x * v x ∂mu - ∫ x in U, g (ρ x) * v x ∂mu := by
        rw [← hswap, ← integral_sub (f := fun x => g x * v x) (g := fun x => g x * v (ρ x)) hgv
          (hg.integrable_mul hvρ)]
        simp_rw [mul_sub]
    _ = ∫ x in U, (g x - g (ρ x)) * v x ∂mu := by
        rw [← integral_sub (f := fun x => g x * v x) (g := fun x => g (ρ x) * v x) hgv
          ((hg.comp_measurePreserving hρ).integrable_mul hv)]
        simp_rw [sub_mul]

end TauCeti
