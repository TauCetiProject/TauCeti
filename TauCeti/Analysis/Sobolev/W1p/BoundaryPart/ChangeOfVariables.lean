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
import TauCeti.Analysis.Normed.Affine.Isometry.Basic
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Changes of variables in the spaces `W^{1,p}_Γ(Ω)`

The space `W^{1,p}_Γ(Ω)` of Sobolev functions vanishing on `Γ`
(`TauCeti.w1pVanishingOnSubmodule`) is transported by changes of variables: if `p < ∞`, `Φ` is
smooth and proper, maps `U` injectively into `V`, has derivative bounded on `U` and Jacobian
determinant bounded away from zero on `U`, and `u ∈ W^{1,p}_Γ(V)`, then
`u ∘ Φ ∈ W^{1,p}_{Φ⁻¹(Γ)}(U)` (`TauCeti.W1p.compL_mem_w1pVanishingOnSubmodule`). The composite
`φ ∘ Φ` of a generator `φ` is again a generator, since `tsupport (φ ∘ Φ) ⊆ Φ⁻¹(tsupport φ)` misses
`Φ⁻¹(closure Γ) ⊇ closure (Φ⁻¹(Γ))`, and the composition operator is continuous.

With an inverse change of variables this is an equivalence. For an affine change of variables
`x ↦ A x + b`, with `A` a continuous linear equivalence, it gives the invariance of `W^{1,p}_Γ`
under the rigid motions and the dilations of the pair `(Ω, Γ)`, for finite `p`
(`TauCeti.W1p.compL_affine_mem_w1pVanishingOnSubmodule_iff`). For smooth proper measure-preserving
changes of variables, in particular rigid motions, the transport also holds at `p = ∞`
(`TauCeti.W1p.compMeasurePreservingL_mem_w1pVanishingOnSubmodule`), and for rigid motions it is an
equivalence (`TauCeti.W1p.compAffineIsometryEquivL_mem_w1pVanishingOnSubmodule_iff`).

## Main results

* `TauCeti.W1p.compL_mem_w1pVanishingOnSubmodule`: for `p < ∞`, precomposition with a smooth
  proper change of variables admissible for `W1p.compL` maps `W^{1,p}_Γ(V)` into
  `W^{1,p}_{Φ⁻¹(Γ)}(U)`.
* `TauCeti.W1p.compL_mem_w1pVanishingOnSubmodule_iff`: the equivalence for a change of variables
  with a smooth proper inverse.
* `TauCeti.W1p.compL_affine_mem_w1pVanishingOnSubmodule_iff`: the affine case, which contains the
  rigid motions and the dilations.
* `TauCeti.W1p.compMeasurePreservingL_mem_w1pVanishingOnSubmodule`: smooth proper measure-preserving
  changes of variables, for every exponent `1 ≤ p ≤ ∞`.
* `TauCeti.W1p.compAffineIsometryEquivL_mem_w1pVanishingOnSubmodule_iff`: rigid motions for every
  exponent `1 ≤ p ≤ ∞`.
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Topology ContDiff

namespace TauCeti

/-- **The generator argument.** A continuous linear operator `T : W^{1,p}(V) → W^{1,p}(U)` that
sends the restriction of each test function `φ` to the restriction of `φ ∘ Φ`, for a smooth proper
`Φ`, maps `W^{1,p}_Γ(V)` into `W^{1,p}_{Φ⁻¹(Γ)}(U)`: the support of `φ ∘ Φ` lies in
`Φ⁻¹(tsupport φ)`, which misses `Φ⁻¹(closure Γ) ⊇ closure (Φ⁻¹(Γ))`. -/
private theorem map_mem_w1pVanishingOnSubmodule_of_compOfIsProperMap {D D' : Type*}
    [MeasurableSpace D] [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
    [BorelSpace D] {mu : Measure D} [mu.IsAddHaarMeasure] [MeasurableSpace D']
    [NormedAddCommGroup D'] [InnerProductSpace ℝ D'] [FiniteDimensional ℝ D'] [BorelSpace D']
    {nu : Measure D'} [nu.IsAddHaarMeasure] {U : Opens D} {V : Opens D'} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {Φ : D → D'} (hΦc : ContDiff ℝ ∞ Φ) (hΦp : IsProperMap Φ)
    (T : W1p nu V p →L[ℝ] W1p mu U p)
    (hT : ∀ φ : 𝓓((⊤ : Opens D'), ℝ),
      T (W1p.restrictL (le_top : V ≤ ⊤) (W1p.ofTestFunctionₗ nu ⊤ p φ)) =
        W1p.restrictL (le_top : U ≤ ⊤)
          (W1p.ofTestFunctionₗ mu ⊤ p (φ.compOfIsProperMap hΦc hΦp (subset_univ _))))
    {Γ : Set D'} {u : W1p nu V p} (hu : u ∈ w1pVanishingOnSubmodule nu V p Γ) :
    T u ∈ w1pVanishingOnSubmodule mu U p (Φ ⁻¹' Γ) := by
  refine w1pVanishingOnSubmodule_subset_of_isClosed
    ((w1pVanishingOnSubmodule mu U p (Φ ⁻¹' Γ)).isClosed.preimage T.continuous)
    (fun φ hφ => ?_) hu
  rw [mem_preimage, hT]
  exact W1p.restrictL_ofTestFunctionₗ_mem_w1pVanishingOnSubmodule
    (((hφ.preimage Φ).mono_left (φ.tsupport_compOfIsProperMap_subset hΦc hΦp _)).mono_right
      (hΦp.continuous.closure_preimage_subset Γ))

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {U V : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Γ : Set E}

section ChangeOfVariables

variable {L c : ℝ} (Φ : E → E) (hp : p ≠ ⊤) (hΦ : DifferentiableOn ℝ Φ U) (hinj : InjOn Φ U)
  (hmaps : MapsTo Φ U V) (hL : ∀ x ∈ (U : Set E), ‖fderiv ℝ Φ x‖ ≤ L) (hc : 0 < c)
  (hdet : ∀ x ∈ (U : Set E), c ≤ |(fderiv ℝ Φ x).det|)

/-- **Changes of variables preserve vanishing on a boundary part.** Let `p < ∞`, and let `Φ` be
a change of variables admissible for `W1p.compL`: it maps `U` injectively into `V`, with
`‖fderiv Φ‖ ≤ L` and `0 < c ≤ |det fderiv Φ|` on `U`. If `Φ` is moreover smooth and proper,
precomposition with `Φ` maps `W^{1,p}_Γ(V)` into `W^{1,p}_{Φ⁻¹(Γ)}(U)`. -/
theorem W1p.compL_mem_w1pVanishingOnSubmodule (hΦc : ContDiff ℝ ∞ Φ) (hΦp : IsProperMap Φ)
    {u : W1p mu V p} (hu : u ∈ w1pVanishingOnSubmodule mu V p Γ) :
    W1p.compL Φ hp hΦ hinj hmaps hL hc hdet u ∈ w1pVanishingOnSubmodule mu U p (Φ ⁻¹' Γ) := by
  refine map_mem_w1pVanishingOnSubmodule_of_compOfIsProperMap hΦc hΦp _ (fun φ => ?_) hu
  refine W1p.ext_value (Lp.ext ?_)
  filter_upwards [W1p.value_compL_ae Φ hp hΦ hinj hmaps hL hc hdet _,
    ae_comp_of_map_absolutelyContinuous (hΦ.continuousOn.aemeasurable U.isOpen.measurableSet)
      (Measure.absolutelyContinuous_of_le_smul
        (map_restrict_le_smul_restrict_of_differentiableOn mu U.isOpen hΦ hinj hmaps hc hdet))
      (W1p.value_restrictL_ofTestFunctionₗ_ae (mu := mu) (p := p) (le_top : V ≤ ⊤) φ),
    W1p.value_restrictL_ofTestFunctionₗ_ae (mu := mu) (p := p) (le_top : U ≤ ⊤) _]
    with x h1 h2 h3
  rw [h1, h2, h3, TestFunction.compOfIsProperMap_apply]

/-- **Invariance of `W^{1,p}_Γ` under changes of variables.** Let `p < ∞`. If `Φ` and `Ψ` are
smooth and proper, `Φ` maps `U` injectively into `V`, `Ψ` maps `V` into `U`, both have bounded
derivative and Jacobian determinant bounded away from zero on their domains, and `Φ ∘ Ψ = id`,
then `u ∘ Φ` lies in `W^{1,p}_{Φ⁻¹(Γ)}(U)` exactly when `u` lies in `W^{1,p}_Γ(V)`. -/
theorem W1p.compL_mem_w1pVanishingOnSubmodule_iff {Ψ : E → E} {L' c' : ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) (hΦp : IsProperMap Φ) (hΨc : ContDiff ℝ ∞ Ψ) (hΨp : IsProperMap Ψ)
    (hΨmaps : MapsTo Ψ V U) (hΨL : ∀ y ∈ (V : Set E), ‖fderiv ℝ Ψ y‖ ≤ L') (hc' : 0 < c')
    (hΨdet : ∀ y ∈ (V : Set E), c' ≤ |(fderiv ℝ Ψ y).det|) (hΦΨ : Function.RightInverse Ψ Φ)
    {u : W1p mu V p} :
    W1p.compL Φ hp hΦ hinj hmaps hL hc hdet u ∈ w1pVanishingOnSubmodule mu U p (Φ ⁻¹' Γ) ↔
      u ∈ w1pVanishingOnSubmodule mu V p Γ := by
  refine ⟨fun hu => ?_, W1p.compL_mem_w1pVanishingOnSubmodule Φ hp hΦ hinj hmaps hL hc hdet
    hΦc hΦp⟩
  have hΨ : DifferentiableOn ℝ Ψ V := (hΨc.differentiable (by simp)).differentiableOn
  have hΨinj : InjOn Ψ V := hΦΨ.injective.injOn
  have h := W1p.compL_mem_w1pVanishingOnSubmodule Ψ hp hΨ hΨinj hΨmaps hΨL hc' hΨdet hΨc hΨp hu
  rwa [← preimage_comp, hΦΨ.comp_eq_id, preimage_id,
    W1p.compL_compL_of_leftInvOn Ψ hp hΨ hΨinj hΨmaps hΨL hc' hΨdet hΦ hinj hmaps hL hc hdet
      (fun y _ => hΦΨ y)] at h

end ChangeOfVariables

/-! ### Affine changes of variables: rigid motions and dilations -/

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
    (fun y hy => by rw [hUV]; simpa using hy)
    (L' := ‖(A.symm : E →L[ℝ] E)‖)
    (fun y _ => by rw [fderiv_add_const, ContinuousLinearEquiv.fderiv]) (abs_pos.2 hdet')
    (fun y _ => by rw [fderiv_add_const, ContinuousLinearEquiv.fderiv]) fun y => by simp

/-! ### Measure-preserving changes of variables and rigid motions at every exponent -/

section MeasurePreserving

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E'] {nu : Measure E'} [nu.IsAddHaarMeasure] {V : Opens E'}
  {Φ : E → E'} {M : ℝ}

/-- **Measure-preserving changes of variables preserve vanishing on a boundary part**, for every
exponent: if `Φ` is smooth, proper and measure-preserving and `U = Φ⁻¹(V)`, precomposition with
`Φ` maps `W^{1,p}_Γ(V)` into `W^{1,p}_{Φ⁻¹(Γ)}(U)`. -/
theorem W1p.compMeasurePreservingL_mem_w1pVanishingOnSubmodule (hΦc : ContDiff ℝ ∞ Φ)
    (hΦp : IsProperMap Φ) (hΦ : MeasurePreserving Φ mu nu) (hUV : (U : Set E) = Φ ⁻¹' V)
    (hΦl : LocallyLipschitzOn U Φ) (hM : ∀ x ∈ (U : Set E), ‖fderiv ℝ Φ x‖ ≤ M) {Γ : Set E'}
    {u : W1p nu V p} (hu : u ∈ w1pVanishingOnSubmodule nu V p Γ) :
    W1p.compMeasurePreservingL hΦ hUV hΦl hM u ∈ w1pVanishingOnSubmodule mu U p (Φ ⁻¹' Γ) := by
  refine map_mem_w1pVanishingOnSubmodule_of_compOfIsProperMap hΦc hΦp _ (fun φ => ?_) hu
  refine W1p.ext_value (Lp.ext ?_)
  filter_upwards [W1p.value_compMeasurePreservingL_ae (p := p) hΦ hUV hΦl hM _,
    (hUV ▸ hΦ.restrict_preimage V.isOpen.measurableSet :
      MeasurePreserving Φ (mu.restrict U) (nu.restrict V)).quasiMeasurePreserving.ae
      (W1p.value_restrictL_ofTestFunctionₗ_ae (mu := nu) (p := p) (le_top : V ≤ ⊤) φ),
    W1p.value_restrictL_ofTestFunctionₗ_ae (mu := mu) (p := p) (le_top : U ≤ ⊤) _]
    with x h1 h2 h3
  rw [h1, h2, h3, TestFunction.compOfIsProperMap_apply]

end MeasurePreserving

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
  -- `u ∘ g` is the measure-preserving composite of `u` with `g`; the body of
  -- `W1p.compAffineIsometryEquivL` is not exposed outside its module, so compare values.
  have h : W1p.compAffineIsometryEquivL g hUV u = W1p.compMeasurePreservingL (M := 1)
      g.measurePreserving hUV g.lipschitzWith.locallyLipschitz.locallyLipschitzOn
      (fun x _ => g.norm_fderiv_le x) u :=
    W1p.ext_value (Lp.ext ((W1p.value_compAffineIsometryEquivL_ae g hUV u).trans
      (W1p.value_compMeasurePreservingL_ae _ _ _ _ u).symm))
  rw [h]
  exact W1p.compMeasurePreservingL_mem_w1pVanishingOnSubmodule
    g.toAffineIsometry.toContinuousAffineMap.contDiff g.toHomeomorph.isProperMap _ _ _ _ hu

/-- **Invariance of `W^{1,p}_Γ` under rigid motions**, for every exponent: for an affine isometry
`g` and `U = g⁻¹(V)`, the function `u ∘ g` lies in `W^{1,p}_{g⁻¹(Γ)}(U)` exactly when `u` lies in
`W^{1,p}_Γ(V)`. -/
@[simp]
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
