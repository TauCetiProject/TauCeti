/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart
public import TauCeti.Analysis.Sobolev.W1p.ChangeOfVariables
public import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Changes of variables in the spaces `W^{1,p}_Γ(Ω)`

The space `W^{1,p}_Γ(Ω)` of Sobolev functions vanishing on `Γ`
(`TauCeti.w1pVanishingOnSubmodule`) is transported by changes of variables: if `Φ` is smooth,
proper and maps `U` injectively into `V`, and `u ∈ W^{1,p}_Γ(V)`, then
`u ∘ Φ ∈ W^{1,p}_{Φ⁻¹(Γ)}(U)` (`TauCeti.W1p.compL_mem_w1pVanishingOnSubmodule`). The composite
`φ ∘ Φ` of a generator `φ` is again a generator, since `tsupport (φ ∘ Φ) ⊆ Φ⁻¹(tsupport φ)` misses
`Φ⁻¹(closure Γ) ⊇ closure (Φ⁻¹(Γ))`, and the composition operator is continuous.

With an inverse change of variables this is an equivalence. For an affine change of variables
`x ↦ A x + b`, with `A` a continuous linear equivalence, it gives the invariance of `W^{1,p}_Γ`
under the rigid motions and the dilations of the pair `(Ω, Γ)`, for finite `p`
(`TauCeti.W1p.compL_affine_mem_w1pVanishingOnSubmodule_iff`). For rigid motions the invariance
also holds at `p = ∞`, through the composition operator of an affine isometry
(`TauCeti.W1p.compAffineIsometryEquivL_mem_w1pVanishingOnSubmodule_iff`).

## Main results

* `TauCeti.W1p.compL_mem_w1pVanishingOnSubmodule`: precomposition with a smooth proper change of
  variables maps `W^{1,p}_Γ(V)` into `W^{1,p}_{Φ⁻¹(Γ)}(U)`.
* `TauCeti.W1p.compL_mem_w1pVanishingOnSubmodule_iff`: the equivalence for a change of variables
  with a smooth proper inverse.
* `TauCeti.W1p.compL_affine_mem_w1pVanishingOnSubmodule_iff`: the affine case, which contains the
  rigid motions and the dilations.
* `TauCeti.W1p.compAffineIsometryEquivL_mem_w1pVanishingOnSubmodule_iff`: rigid motions for every
  exponent `1 ≤ p ≤ ∞`.
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Topology ContDiff

namespace TauCeti

/-- The composite `φ ∘ Φ` of a generator `φ` of `W^{1,p}_Γ` with a smooth proper map `Φ` is a
generator for `Φ⁻¹(Γ)`: its support misses `closure (Φ⁻¹(Γ))`. -/
private theorem disjoint_tsupport_compOfIsProperMap {D D' : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup D'] [NormedSpace ℝ D'] {Φ : D → D'}
    (hΦc : ContDiff ℝ ∞ Φ) (hΦp : IsProperMap Φ) {Γ : Set D'} {φ : 𝓓((⊤ : Opens D'), ℝ)}
    (hφ : Disjoint (tsupport φ) (closure Γ)) :
    Disjoint (tsupport (φ.compOfIsProperMap hΦc hΦp (subset_univ _) : 𝓓((⊤ : Opens D), ℝ)))
      (closure (Φ ⁻¹' Γ)) :=
  ((hφ.preimage Φ).mono_left (φ.tsupport_compOfIsProperMap_subset hΦc hΦp _)).mono_right
    (hΦp.continuous.closure_preimage_subset Γ)

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {U V : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Γ : Set E}

section ChangeOfVariables

variable {L c : ℝ} (Φ : E → E) (hp : p ≠ ⊤) (hΦ : DifferentiableOn ℝ Φ U) (hinj : InjOn Φ U)
  (hmaps : MapsTo Φ U V) (hL : ∀ x ∈ (U : Set E), ‖fderiv ℝ Φ x‖ ≤ L) (hc : 0 < c)
  (hdet : ∀ x ∈ (U : Set E), c ≤ |(fderiv ℝ Φ x).det|)

/-- **Changes of variables preserve vanishing on a boundary part.** If `Φ` is smooth and proper,
precomposition with `Φ` maps `W^{1,p}_Γ(V)` into `W^{1,p}_{Φ⁻¹(Γ)}(U)`. -/
theorem W1p.compL_mem_w1pVanishingOnSubmodule (hΦc : ContDiff ℝ ∞ Φ) (hΦp : IsProperMap Φ)
    {u : W1p mu V p} (hu : u ∈ w1pVanishingOnSubmodule mu V p Γ) :
    W1p.compL Φ hp hΦ hinj hmaps hL hc hdet u ∈ w1pVanishingOnSubmodule mu U p (Φ ⁻¹' Γ) := by
  refine w1pVanishingOnSubmodule_subset_of_isClosed
    ((w1pVanishingOnSubmodule mu U p (Φ ⁻¹' Γ)).isClosed.preimage
      (W1p.compL Φ hp hΦ hinj hmaps hL hc hdet).continuous) (fun φ hφ => ?_) hu
  -- The composite `φ ∘ Φ` is a generator for `Φ⁻¹(Γ)`.
  set ψ : 𝓓((⊤ : Opens E), ℝ) := φ.compOfIsProperMap hΦc hΦp (subset_univ _)
  have hψ : Disjoint (tsupport ψ) (closure (Φ ⁻¹' Γ)) :=
    disjoint_tsupport_compOfIsProperMap hΦc hΦp hφ
  have heq : W1p.compL Φ hp hΦ hinj hmaps hL hc hdet
      (W1p.restrictL (le_top : V ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p φ)) =
      W1p.restrictL (le_top : U ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p ψ) := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_compL_ae Φ hp hΦ hinj hmaps hL hc hdet _,
      ae_comp_of_map_absolutelyContinuous (hΦ.continuousOn.aemeasurable U.isOpen.measurableSet)
        (Measure.absolutelyContinuous_of_le_smul
          (map_restrict_le_smul_restrict_of_differentiableOn mu U.isOpen hΦ hinj hmaps hc hdet))
        (W1p.value_restrictL_ofTestFunctionₗ_ae (mu := mu) (p := p) (le_top : V ≤ ⊤) φ),
      W1p.value_restrictL_ofTestFunctionₗ_ae (mu := mu) (p := p) (le_top : U ≤ ⊤) ψ]
      with x h1 h2 h3
    rw [h1, h2, h3, TestFunction.compOfIsProperMap_apply]
  rw [mem_preimage, heq]
  exact W1p.restrictL_ofTestFunctionₗ_mem_w1pVanishingOnSubmodule hψ

/-- **Invariance of `W^{1,p}_Γ` under changes of variables.** If `Φ` and `Ψ` are smooth and proper,
`Φ` maps `U` injectively into `V`, `Ψ` maps `V` into `U` and `Φ ∘ Ψ = id`, then `u ∘ Φ` lies in
`W^{1,p}_{Φ⁻¹(Γ)}(U)` exactly when `u` lies in `W^{1,p}_Γ(V)`. -/
theorem W1p.compL_mem_w1pVanishingOnSubmodule_iff {Ψ : E → E} {L' c' : ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) (hΦp : IsProperMap Φ) (hΨc : ContDiff ℝ ∞ Ψ) (hΨp : IsProperMap Ψ)
    (hΨ : DifferentiableOn ℝ Ψ V) (hΨinj : InjOn Ψ V) (hΨmaps : MapsTo Ψ V U)
    (hΨL : ∀ y ∈ (V : Set E), ‖fderiv ℝ Ψ y‖ ≤ L') (hc' : 0 < c')
    (hΨdet : ∀ y ∈ (V : Set E), c' ≤ |(fderiv ℝ Ψ y).det|) (hΦΨ : Function.RightInverse Ψ Φ)
    {u : W1p mu V p} :
    W1p.compL Φ hp hΦ hinj hmaps hL hc hdet u ∈ w1pVanishingOnSubmodule mu U p (Φ ⁻¹' Γ) ↔
      u ∈ w1pVanishingOnSubmodule mu V p Γ := by
  refine ⟨fun hu => ?_, W1p.compL_mem_w1pVanishingOnSubmodule Φ hp hΦ hinj hmaps hL hc hdet
    hΦc hΦp⟩
  have h := W1p.compL_mem_w1pVanishingOnSubmodule Ψ hp hΨ hΨinj hΨmaps hΨL hc' hΨdet hΨc hΨp hu
  rwa [← preimage_comp, hΦΨ.comp_eq_id, preimage_id,
    W1p.compL_compL_of_leftInvOn Ψ hp hΨ hΨinj hΨmaps hΨL hc' hΨdet hΦ hinj hmaps hL hc hdet
      (fun y _ => hΦΨ y)] at h

end ChangeOfVariables

/-! ### Affine changes of variables: rigid motions and dilations -/

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
/-- The derivative of the affine map `x ↦ A x + b` is `A` everywhere. -/
private theorem fderiv_affine (A : E ≃L[ℝ] E) (b x : E) :
    fderiv ℝ (fun y => A y + b) x = (A : E →L[ℝ] E) := by
  rw [fderiv_add_const, ContinuousLinearEquiv.fderiv]

/-- **Invariance of `W^{1,p}_Γ` under affine changes of variables**, among them the rigid motions
and the dilations: for a continuous linear equivalence `A`, `b ∈ E`, `Φ x = A x + b` and
`U = Φ⁻¹(V)`, the function `u ∘ Φ` lies in `W^{1,p}_{Φ⁻¹(Γ)}(U)` exactly when `u` lies in
`W^{1,p}_Γ(V)`, for `1 ≤ p < ∞`. The regularity hypotheses of `TauCeti.W1p.compL` are arguments,
since they appear in the statement; each holds for every such `Φ`. -/
theorem W1p.compL_affine_mem_w1pVanishingOnSubmodule_iff {L c : ℝ} (hp : p ≠ ⊤) (A : E ≃L[ℝ] E)
    (b : E) (hUV : (U : Set E) = (fun x => A x + b) ⁻¹' V)
    (hΦ : DifferentiableOn ℝ (fun x => A x + b) U) (hinj : InjOn (fun x => A x + b) U)
    (hmaps : MapsTo (fun x => A x + b) U V)
    (hL : ∀ x ∈ (U : Set E), ‖fderiv ℝ (fun x => A x + b) x‖ ≤ L) (hc : 0 < c)
    (hdet : ∀ x ∈ (U : Set E), c ≤ |(fderiv ℝ (fun x => A x + b) x).det|) {u : W1p mu V p} :
    W1p.compL (fun x => A x + b) hp hΦ hinj hmaps hL hc hdet u ∈
        w1pVanishingOnSubmodule mu U p ((fun x => A x + b) ⁻¹' Γ) ↔
      u ∈ w1pVanishingOnSubmodule mu V p Γ := by
  have hΦc : ContDiff ℝ ∞ (fun x => A x + b) := (A : E →L[ℝ] E).contDiff.add contDiff_const
  have hΨc : ContDiff ℝ ∞ (fun y => A.symm y + -A.symm b) :=
    (A.symm : E →L[ℝ] E).contDiff.add contDiff_const
  have hΦp : IsProperMap (fun x => A x + b) :=
    ((A.toHomeomorph).trans (Homeomorph.addRight b)).isProperMap
  have hΨp : IsProperMap (fun y => A.symm y + -A.symm b) :=
    ((A.symm.toHomeomorph).trans (Homeomorph.addRight (-A.symm b))).isProperMap
  have hdet' : (A.symm : E →L[ℝ] E).det ≠ 0 :=
    (LinearEquiv.isUnit_det' A.symm.toLinearEquiv).ne_zero
  refine W1p.compL_mem_w1pVanishingOnSubmodule_iff _ hp hΦ hinj hmaps hL hc hdet hΦc hΦp hΨc hΨp
    (hΨc.differentiable (by simp)).differentiableOn
    (fun y₁ _ y₂ _ h => A.symm.injective (add_right_cancel h))
    (fun y hy => by
      rw [SetLike.mem_coe, ← SetLike.mem_coe, hUV, mem_preimage]
      simpa using hy)
    (L' := ‖(A.symm : E →L[ℝ] E)‖) (fun y _ => (congrArg norm (fderiv_affine A.symm _ y)).le)
    (abs_pos.2 hdet') (fun y _ => (fderiv_affine A.symm _ y).symm ▸ le_rfl) fun y => by simp

/-! ### Rigid motions at every exponent -/

section AffineIsometry

variable {F F' : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
  [FiniteDimensional ℝ F'] [MeasurableSpace F'] [BorelSpace F'] {U : Opens F} {V : Opens F'}

/-- **Rigid motions preserve vanishing on a boundary part**, for every exponent: for an affine
isometry `g` and `U = g⁻¹(V)`, precomposition with `g` maps `W^{1,p}_Γ(V)` into
`W^{1,p}_{g⁻¹(Γ)}(U)`. -/
theorem W1p.compAffineIsometryEquivL_mem_w1pVanishingOnSubmodule (g : F ≃ᵃⁱ[ℝ] F')
    (hUV : (U : Set F) = g ⁻¹' V) {Γ : Set F'} {u : W1p volume V p}
    (hu : u ∈ w1pVanishingOnSubmodule volume V p Γ) :
    W1p.compAffineIsometryEquivL g hUV u ∈ w1pVanishingOnSubmodule volume U p (g ⁻¹' Γ) := by
  refine w1pVanishingOnSubmodule_subset_of_isClosed
    ((w1pVanishingOnSubmodule volume U p (g ⁻¹' Γ)).isClosed.preimage
      (W1p.compAffineIsometryEquivL g hUV).continuous) (fun φ hφ => ?_) hu
  -- The composite `φ ∘ g` is a generator for `g⁻¹(Γ)`.
  have hgc : ContDiff ℝ ∞ g := g.toAffineIsometry.toContinuousAffineMap.contDiff
  set ψ : 𝓓((⊤ : Opens F), ℝ) := φ.compOfIsProperMap hgc g.toHomeomorph.isProperMap (subset_univ _)
  have hψ : Disjoint (tsupport ψ) (closure (g ⁻¹' Γ)) :=
    disjoint_tsupport_compOfIsProperMap hgc g.toHomeomorph.isProperMap hφ
  have heq : W1p.compAffineIsometryEquivL g hUV
      (W1p.restrictL (le_top : V ≤ ⊤) (W1p.ofTestFunctionₗ volume ⊤ p φ)) =
      W1p.restrictL (le_top : U ≤ ⊤) (W1p.ofTestFunctionₗ volume ⊤ p ψ) := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_compAffineIsometryEquivL_ae (p := p) g hUV _,
      (hUV ▸ g.measurePreserving.restrict_preimage V.isOpen.measurableSet :
        MeasurePreserving g (volume.restrict (U : Set F))
          (volume.restrict (V : Set F'))).quasiMeasurePreserving.ae
        (W1p.value_restrictL_ofTestFunctionₗ_ae (mu := volume) (p := p) (le_top : V ≤ ⊤) φ),
      W1p.value_restrictL_ofTestFunctionₗ_ae (mu := volume) (p := p) (le_top : U ≤ ⊤) ψ]
      with x h1 h2 h3
    rw [h1, h2, h3, TestFunction.compOfIsProperMap_apply φ hgc g.toHomeomorph.isProperMap]
  rw [mem_preimage, heq]
  exact W1p.restrictL_ofTestFunctionₗ_mem_w1pVanishingOnSubmodule hψ

/-- **Invariance of `W^{1,p}_Γ` under rigid motions**, for every exponent: for an affine isometry
`g` and `U = g⁻¹(V)`, the function `u ∘ g` lies in `W^{1,p}_{g⁻¹(Γ)}(U)` exactly when `u` lies in
`W^{1,p}_Γ(V)`. -/
theorem W1p.compAffineIsometryEquivL_mem_w1pVanishingOnSubmodule_iff (g : F ≃ᵃⁱ[ℝ] F')
    (hUV : (U : Set F) = g ⁻¹' V) {Γ : Set F'} {u : W1p volume V p} :
    W1p.compAffineIsometryEquivL g hUV u ∈ w1pVanishingOnSubmodule volume U p (g ⁻¹' Γ) ↔
      u ∈ w1pVanishingOnSubmodule volume V p Γ := by
  have hVU : (V : Set F') = g.symm ⁻¹' U := by
    rw [hUV, ← preimage_comp]
    ext x
    simp
  refine ⟨fun hu => ?_, W1p.compAffineIsometryEquivL_mem_w1pVanishingOnSubmodule g hUV⟩
  have h := W1p.compAffineIsometryEquivL_mem_w1pVanishingOnSubmodule g.symm hVU hu
  rwa [W1p.compAffineIsometryEquivL_symm_compAffineIsometryEquivL, ← preimage_comp,
    show ⇑g ∘ ⇑g.symm = id from funext g.apply_symm_apply, preimage_id] at h

end AffineIsometry

end TauCeti
