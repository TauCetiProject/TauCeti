/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Frontier
public import TauCeti.Analysis.Sobolev.W1p.AddHaar
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import TauCeti.Analysis.InnerProductSpace.OfLinearIsometry
import TauCeti.Analysis.Normed.Module.DiamFrontier
import TauCeti.Analysis.Sobolev.LipschitzDomain.GlobalExtension
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The trace on a bounded Lipschitz domain of a Euclidean space

Let `F` be a finite-dimensional real inner product space of dimension `n + 1 ≥ 1`, such as
`EuclideanSpace ℝ (Fin (n + 1))`, let `μ` be an additive Haar measure on `F`, and let `Ω ⊆ F` be a
bounded open set satisfying the intrinsic Lipschitz-domain condition
`(Ω : Set F).IsLipschitzDomain E` (at each frontier point, in rigid coordinates, `Ω` is locally the
region above the graph of a Lipschitz function on the tangential model `E`). Let
`σ = μHE[n]` be normalized `n`-dimensional Euclidean Hausdorff measure, restricted to
`frontier Ω`. For `1 ≤ p < ∞` this file proves the **trace theorem**: there is a bounded linear
operator

`TauCeti.W1p.frontierTraceOfIsLipschitzDomain : W^{1,p}_μ(Ω) →L[ℝ] Lᵖ(frontier Ω, σ)`

that sends every function continuous up to the boundary to its restriction to the frontier
(`TauCeti.W1p.frontierTraceOfIsLipschitzDomain_ae_eq_of_continuousOn`), and whose kernel is exactly
`W^{1,p}_0(Ω)` (`TauCeti.W1p.ker_frontierTraceOfIsLipschitzDomain`). It is the only bounded
operator sending the restriction of each test function on `F` to its restriction to the frontier
(`TauCeti.W1p.eq_frontierTraceOfIsLipschitzDomain`), because these restrictions are dense in
`W^{1,p}_μ(Ω)` (`TauCeti.W1p.denseRange_restrictL_ofTestFunctionₗ_top_of_isLipschitzDomain`).

This is the form of the trace used by boundary-value problems on Euclidean domains, where energy
forms and weak solutions live on `EuclideanSpace ℝ ι` with an arbitrary Haar measure: a Neumann
datum on `frontier Ω` is paired with the trace of a test function through `σ`.

## The argument

The trace is constructed in the model space `ℝ × E` (`TauCeti.W1p.frontierTrace`, for Lebesgue
measure and the global Lipschitz-domain predicate `Set.IsLipschitzDomainWith`), and transported.
A boundary chart of `Ω` is an affine isometry `g : F ≃ᵃⁱ[ℝ] ℝ × E`. It embeds `E` isometrically in
`F` (`LinearIsometryEquiv.symmInr`), which gives `E` the inner product
(`InnerProductSpace.ofLinearIsometry`), finite dimension and Borel structure that the model-space
theory needs, with `dim E = dim F - 1`. The image `g '' Ω` is a bounded Lipschitz domain of the
model space, with compact frontier, so it satisfies the global predicate
(`Set.IsLipschitzDomain.exists_isLipschitzDomainWith_image`). Then:

* precomposition with `g⁻¹` carries `W^{1,p}(Ω)` to `W^{1,p}(g '' Ω)`
  (`TauCeti.W1p.compAffineIsometryEquivL`), preserving and reflecting `W^{1,p}_0`;
* `g` is an isometry, so it carries Hausdorff measure on `frontier Ω` to Hausdorff measure on
  `frontier (g '' Ω)`
  (`IsometryEquiv.measurePreserving_euclideanHausdorffMeasure_restrict_frontier`), and
  precomposition with `g` is a linear isometry between the `Lᵖ` spaces of the two frontiers;
* the change of Haar measure (`TauCeti.W1p.addHaarEquivL`) passes from Lebesgue measure to `μ`.

When the frontier is empty, `Ω` is empty, since it is bounded and `F` is nontrivial
(`Bornology.IsBounded.eq_empty_of_frontier_eq_empty`).

## Main declarations

* `TauCeti.W1p.exists_frontierTrace_of_isLipschitzDomain`: the trace theorem.
* `TauCeti.W1p.frontierTraceOfIsLipschitzDomain`: the trace operator, with
  `TauCeti.W1p.frontierTraceOfIsLipschitzDomain_ae_eq_of_continuousOn`,
  `TauCeti.W1p.eq_frontierTraceOfIsLipschitzDomain`,
  `TauCeti.W1p.mem_w1p0Submodule_iff_frontierTraceOfIsLipschitzDomain_eq_zero` and
  `TauCeti.W1p.ker_frontierTraceOfIsLipschitzDomain`.
* `TauCeti.W1p.denseRange_restrictL_ofTestFunctionₗ_top_of_isLipschitzDomain`: restrictions of
  test functions on `F` are dense in `W^{1,p}_μ(Ω)`.
* `TauCeti.W1p.frontierTraceOfIsLipschitzDomain_ae_eq_frontierTrace_compAffineIsometryEquivL`: for
  Lebesgue measure, in the coordinates of any affine isometry carrying `Ω` onto a bounded Lipschitz
  domain of the model space, the trace is the model-space trace, so results about
  `TauCeti.W1p.frontierTrace` transfer to Euclidean domains.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5, Theorems 1 and 2.
* J. Nečas, *Direct Methods in the Theory of Elliptic Equations*, Chapter 2, §4.
* P. Grisvard, *Elliptic Problems in Nonsmooth Domains*, Definition 1.2.1.1 and Theorem 1.5.1.3.
-/

public section

noncomputable section

open Bornology MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal Distributions

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {Ω : Opens F} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Isometric copies of Lipschitz domains of the model space -/

section ModelSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Density of the restrictions of test functions on an open set `Ω ⊆ F` that an affine isometry
`g` carries onto a bounded Lipschitz domain `W` of the model space, for Lebesgue measure. -/
private theorem denseRange_restrictL_ofTestFunctionₗ_top_of_image (hp : p ≠ ⊤) {L : ℝ≥0}
    (g : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) {W : Opens (WithLp 2 (ℝ × E))}
    (hΩW : (Ω : Set F) = g ⁻¹' W) (hW : (W : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hbW : IsBounded (W : Set (WithLp 2 (ℝ × E)))) :
    DenseRange fun φ : 𝓓((⊤ : Opens F), ℝ) =>
      W1p.restrictL (le_top : Ω ≤ ⊤) (W1p.ofTestFunctionₗ volume ⊤ p φ) := by
  have hWΩ : (W : Set (WithLp 2 (ℝ × E))) = g.symm ⁻¹' Ω := by
    rw [hΩW, ← Set.preimage_comp]
    ext x
    simp
  have hmpΩ : MeasurePreserving g (volume.restrict (Ω : Set F))
      (volume.restrict (W : Set (WithLp 2 (ℝ × E)))) := by
    rw [hΩW]
    exact g.measurePreserving.restrict_preimage W.isOpen.measurableSet
  -- Precomposition with `g` is onto, and pulls back the dense restrictions on `W`.
  have hsurj : Function.Surjective (W1p.compAffineIsometryEquivL (p := p) g hΩW) := fun u =>
    ⟨W1p.compAffineIsometryEquivL g.symm hWΩ u,
      W1p.compAffineIsometryEquivL_symm_compAffineIsometryEquivL g.symm hWΩ hΩW u⟩
  refine Dense.mono ?_ (hsurj.denseRange.comp (W1p.denseRange_restrictL_ofTestFunctionₗ_top hp
    hW hbW) (W1p.compAffineIsometryEquivL g hΩW).continuous)
  rintro _ ⟨φ, rfl⟩
  let ψ : 𝓓((⊤ : Opens F), ℝ) := TestFunction.mk (fun x => φ (g x))
    (φ.contDiff.comp g.toAffineIsometry.toContinuousAffineMap.contDiff)
    (φ.hasCompactSupport.comp_homeomorph g.toHomeomorph) (subset_univ _)
  refine ⟨ψ, W1p.ext_value (Lp.ext ?_)⟩
  filter_upwards [W1p.value_restrictL_ofTestFunctionₗ_ae (mu := volume) (p := p) le_top ψ,
    W1p.value_compAffineIsometryEquivL_ae g hΩW
      (W1p.restrictL le_top (W1p.ofTestFunctionₗ volume ⊤ p φ)),
    hmpΩ.quasiMeasurePreserving.ae
      (W1p.value_restrictL_ofTestFunctionₗ_ae (mu := volume) (p := p) le_top φ)]
    with x h1 h2 h3
  rw [h1, Function.comp_apply, h2, h3]
  exact congrFun (TestFunction.coe_mk (f := fun x => φ (g x))) x

/-- The trace of `u ∘ g⁻¹` on `frontier W`, read back on `F` through `g`, is a representative `f`
of `u` continuous up to the boundary, for every measure carried by `g` to surface measure on
`frontier W`. -/
private theorem compMeasurePreserving_frontierTrace_compAffineIsometryEquivL_ae_eq (hp : p ≠ ⊤)
    {L : ℝ≥0} (g : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) {W : Opens (WithLp 2 (ℝ × E))}
    (hWΩ : (W : Set (WithLp 2 (ℝ × E))) = g.symm ⁻¹' Ω)
    (hW : (W : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hbW : IsBounded (W : Set (WithLp 2 (ℝ × E)))) {σ : Measure F}
    (hmp : MeasurePreserving g σ
      ((μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict (frontier (W : Set _))))
    {u : W1p volume Ω p} {f : F → ℝ} (hf : ContinuousOn f (closure (Ω : Set F)))
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set F)] f) :
    Lp.compMeasurePreserving g hmp
      (W1p.frontierTrace hp hW hbW (W1p.compAffineIsometryEquivL g.symm hWΩ u)) =ᵐ[σ] f := by
  have hmpW : MeasurePreserving g.symm (volume.restrict (W : Set (WithLp 2 (ℝ × E))))
      (volume.restrict (Ω : Set F)) := by
    rw [hWΩ]
    exact g.symm.measurePreserving.restrict_preimage Ω.isOpen.measurableSet
  -- Transport the representative through `g`.
  have hae : W1p.value (W1p.compAffineIsometryEquivL g.symm hWΩ u) =ᵐ[volume.restrict
      (W : Set (WithLp 2 (ℝ × E)))] f ∘ g.symm :=
    (W1p.value_compAffineIsometryEquivL_ae g.symm hWΩ u).trans
      (hmpW.quasiMeasurePreserving.ae_eq_comp hu)
  have hcont : ContinuousOn (f ∘ g.symm) (closure (W : Set (WithLp 2 (ℝ × E)))) := by
    rw [hWΩ, ← g.symm.coe_toHomeomorph, ← Homeomorph.preimage_closure]
    exact hf.comp g.symm.continuous.continuousOn (mapsTo_preimage _ _)
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (W1p.frontierTrace hp hW hbW (W1p.compAffineIsometryEquivL g.symm hWΩ u)) hmp,
    hmp.quasiMeasurePreserving.ae_eq_comp
      (W1p.frontierTrace_ae_eq_of_continuousOn hp hW hbW hcont hae)] with x h1 h2
  rw [h1, h2]
  simp

/-- The trace theorem, with density, for Lebesgue measure on an open set `Ω ⊆ F` that an affine
isometry `g` carries onto a bounded Lipschitz domain of the model space. -/
private theorem exists_frontierTrace_of_isLipschitzDomainWith_image (hp : p ≠ ⊤) {L : ℝ≥0}
    (g : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (hΩ : (g '' (Ω : Set F)).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set F)) :
    ∃ T : W1p volume Ω p →L[ℝ]
        Lp ℝ p ((μHE[finrank ℝ E] : Measure F).restrict (frontier (Ω : Set F))),
      (∀ (u : W1p volume Ω p) (f : F → ℝ), ContinuousOn f (closure (Ω : Set F)) →
        W1p.value u =ᵐ[volume.restrict (Ω : Set F)] f →
        T u =ᵐ[(μHE[finrank ℝ E] : Measure F).restrict (frontier (Ω : Set F))] f) ∧
      (∀ u : W1p volume Ω p, T u = 0 ↔ u ∈ w1p0Submodule volume Ω p) ∧
      DenseRange fun φ : 𝓓((⊤ : Opens F), ℝ) =>
        W1p.restrictL (le_top : Ω ≤ ⊤) (W1p.ofTestFunctionₗ volume ⊤ p φ) := by
  let W : Opens (WithLp 2 (ℝ × E)) :=
    ⟨g '' (Ω : Set F), ((isLipschitzDomainWith_iff _ _).1 hΩ).1⟩
  have hW : (W : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L := hΩ
  have hWΩ : (W : Set (WithLp 2 (ℝ × E))) = g.symm ⁻¹' Ω :=
    g.toHomeomorph.image_eq_preimage_symm _
  have hΩW : (Ω : Set F) = g ⁻¹' W := (g.toHomeomorph.preimage_image _).symm
  have hbW : IsBounded (W : Set (WithLp 2 (ℝ × E))) := g.lipschitzWith.isBounded_image hb
  have hmp : MeasurePreserving g ((μHE[finrank ℝ E] : Measure F).restrict (frontier (Ω : Set F)))
      ((μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict (frontier (W : Set _))) :=
    g.toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure_restrict_frontier hΩW _
  -- The trace of `u ∘ g⁻¹` on `frontier W`, read back on `frontier Ω` through `g`.
  let B := Lp.compMeasurePreservingₗᵢ (E := ℝ) (p := p) ℝ g hmp
  refine ⟨B.toContinuousLinearMap.comp
    ((W1p.frontierTrace hp hW hbW).comp (W1p.compAffineIsometryEquivL g.symm hWΩ)), ?_, ?_,
    denseRange_restrictL_ofTestFunctionₗ_top_of_image hp g hΩW hW hbW⟩
  · intro u f hf hu
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap, B,
      Lp.compMeasurePreservingₗᵢ_apply]
    exact compMeasurePreserving_frontierTrace_compAffineIsometryEquivL_ae_eq hp g hWΩ hW hbW hmp
      hf hu
  · -- The kernel: `B` is injective, and zero trace in rigid coordinates is `W^{1,p}_0`.
    intro u
    rw [W1p.mem_w1p0Submodule_iff_frontierTrace_compAffineIsometryEquivL_eq_zero hp hW hbW g hWΩ]
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
    exact map_eq_zero_iff B B.injective

end ModelSpace

/-! ### Bounded Lipschitz domains -/

section Intrinsic

variable [Nontrivial F] {mu : Measure F} [mu.IsAddHaarMeasure]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The trace theorem, with density, for Lebesgue measure. -/
private theorem exists_frontierTrace_volume (hp : p ≠ ⊤)
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F)) :
    ∃ T : W1p volume Ω p →L[ℝ]
        Lp ℝ p ((μHE[finrank ℝ F - 1] : Measure F).restrict (frontier (Ω : Set F))),
      (∀ (u : W1p volume Ω p) (f : F → ℝ), ContinuousOn f (closure (Ω : Set F)) →
        W1p.value u =ᵐ[volume.restrict (Ω : Set F)] f →
        T u =ᵐ[(μHE[finrank ℝ F - 1] : Measure F).restrict (frontier (Ω : Set F))] f) ∧
      (∀ u : W1p volume Ω p, T u = 0 ↔ u ∈ w1p0Submodule volume Ω p) ∧
      DenseRange fun φ : 𝓓((⊤ : Opens F), ℝ) =>
        W1p.restrictL (le_top : Ω ≤ ⊤) (W1p.ofTestFunctionₗ volume ⊤ p φ) := by
  rcases (frontier (Ω : Set F)).eq_empty_or_nonempty with hfr | hne
  · -- `Ω` is empty, so `W^{1,p}(Ω)` is zero and the zero operator is the trace.
    have hΩe := hb.eq_empty_of_frontier_eq_empty hfr
    have hsub (u v : W1p volume Ω p) : u = v :=
      W1p.ext_value (Lp.ext (by simp [hΩe, Filter.EventuallyEq]))
    refine ⟨0, fun u f _ _ => by simp [hfr, Filter.EventuallyEq], fun u => ?_,
      fun u => subset_closure ⟨0, hsub _ u⟩⟩
    simp [hsub u 0]
  -- A boundary chart `g` embeds `E` isometrically in `F`.
  obtain ⟨g, L, hL⟩ := hΩ.exists_isLipschitzDomainWith_image hb hne
  -- Give `E` the inner product, finite dimension and Borel structure of its image in `F`.
  let e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E) := g.linearIsometryEquiv
  let _ : InnerProductSpace ℝ E := .ofLinearIsometry e.symmInr
  have _ : FiniteDimensional ℝ E := e.finiteDimensional_snd
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  rw [← e.finrank_snd]
  exact exists_frontierTrace_of_isLipschitzDomainWith_image hp g hL hb

/-- **Density of functions smooth up to the boundary.** On a bounded Lipschitz domain of a
nontrivial finite-dimensional real inner product space, for every additive Haar measure and
`p < ∞`, the restrictions to `Ω` of test functions on the whole space are dense in
`W^{1,p}(Ω)`. -/
theorem W1p.denseRange_restrictL_ofTestFunctionₗ_top_of_isLipschitzDomain (hp : p ≠ ⊤)
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F)) :
    DenseRange fun φ : 𝓓((⊤ : Opens F), ℝ) =>
      W1p.restrictL (le_top : Ω ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p φ) := by
  obtain ⟨-, -, -, hd⟩ := exists_frontierTrace_volume hp hΩ hb
  refine Dense.mono ?_ ((W1p.addHaarEquivL volume mu).surjective.denseRange.comp hd
    (W1p.addHaarEquivL volume mu).continuous)
  rintro _ ⟨φ, rfl⟩
  exact ⟨φ, by
    rw [Function.comp_apply, W1p.addHaarEquivL_restrictL, W1p.addHaarEquivL_ofTestFunctionₗ]⟩

/-- **The trace theorem.** Let `Ω` be a bounded Lipschitz domain in a nontrivial
finite-dimensional real inner product space `F`, let `μ` be an additive Haar measure on `F` and
let `1 ≤ p < ∞`. There is a bounded linear operator from `W^{1,p}(Ω)` to `Lᵖ` of the frontier for
normalized `(dim F - 1)`-dimensional Euclidean Hausdorff measure which sends every function
continuous up to the boundary to its restriction to the frontier, and whose kernel is exactly
`W^{1,p}_0(Ω)`. -/
theorem W1p.exists_frontierTrace_of_isLipschitzDomain (hp : p ≠ ⊤)
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F)) :
    ∃ T : W1p mu Ω p →L[ℝ]
        Lp ℝ p ((μHE[finrank ℝ F - 1] : Measure F).restrict (frontier (Ω : Set F))),
      (∀ (u : W1p mu Ω p) (f : F → ℝ), ContinuousOn f (closure (Ω : Set F)) →
        W1p.value u =ᵐ[mu.restrict (Ω : Set F)] f →
        T u =ᵐ[(μHE[finrank ℝ F - 1] : Measure F).restrict (frontier (Ω : Set F))] f) ∧
      LinearMap.ker T.toLinearMap = (w1p0Submodule mu Ω p).toSubmodule := by
  obtain ⟨T, hT, hker, -⟩ := exists_frontierTrace_volume hp hΩ hb
  refine ⟨T.comp ((W1p.addHaarEquivL mu volume : W1p mu Ω p ≃L[ℝ] W1p volume Ω p) :
      W1p mu Ω p →L[ℝ] W1p volume Ω p),
    fun u f hf hu => hT _ f hf ?_, ?_⟩
  · exact (W1p.value_addHaarEquivL_ae mu volume u).trans
      (hu.filter_mono ((Measure.absolutelyContinuous_isAddHaarMeasure _ _).restrict _).ae_le)
  · ext u
    simp [hker]

/-- **The trace operator of a bounded Lipschitz domain** `Ω` of a nontrivial finite-dimensional
real inner product space `F`, from `W^{1,p}(Ω)` for an additive Haar measure `μ` and `p < ∞` to
`Lᵖ` of the frontier for normalized `(dim F - 1)`-dimensional Euclidean Hausdorff measure. It is
the unique bounded operator sending the restriction of every test function to its restriction to
the frontier (`TauCeti.W1p.frontierTraceOfIsLipschitzDomain_ae_eq_of_continuousOn`,
`TauCeti.W1p.eq_frontierTraceOfIsLipschitzDomain`), and its kernel is `W^{1,p}_0(Ω)`
(`TauCeti.W1p.ker_frontierTraceOfIsLipschitzDomain`). -/
def W1p.frontierTraceOfIsLipschitzDomain (hp : p ≠ ⊤) (hΩ : (Ω : Set F).IsLipschitzDomain E)
    (hb : IsBounded (Ω : Set F)) :
    W1p mu Ω p →L[ℝ]
      Lp ℝ p ((μHE[finrank ℝ F - 1] : Measure F).restrict (frontier (Ω : Set F))) :=
  (W1p.exists_frontierTrace_of_isLipschitzDomain hp hΩ hb).choose

/-- **The trace of a function continuous up to the boundary is its boundary restriction.** -/
theorem W1p.frontierTraceOfIsLipschitzDomain_ae_eq_of_continuousOn (hp : p ≠ ⊤)
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F)) {u : W1p mu Ω p}
    {f : F → ℝ} (hf : ContinuousOn f (closure (Ω : Set F)))
    (hu : W1p.value u =ᵐ[mu.restrict (Ω : Set F)] f) :
    W1p.frontierTraceOfIsLipschitzDomain hp hΩ hb u =ᵐ[(μHE[finrank ℝ F - 1] : Measure F).restrict
      (frontier (Ω : Set F))] f :=
  (W1p.exists_frontierTrace_of_isLipschitzDomain hp hΩ hb).choose_spec.1 u f hf hu

/-- **The kernel of the trace is `W^{1,p}_0(Ω)`.** -/
theorem W1p.ker_frontierTraceOfIsLipschitzDomain (hp : p ≠ ⊤)
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F)) :
    LinearMap.ker (W1p.frontierTraceOfIsLipschitzDomain (mu := mu) hp hΩ hb).toLinearMap =
      (w1p0Submodule mu Ω p).toSubmodule :=
  (W1p.exists_frontierTrace_of_isLipschitzDomain hp hΩ hb).choose_spec.2

/-- **The functions of zero trace are those of `W^{1,p}_0(Ω)`.** -/
theorem W1p.mem_w1p0Submodule_iff_frontierTraceOfIsLipschitzDomain_eq_zero (hp : p ≠ ⊤)
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F)) (u : W1p mu Ω p) :
    u ∈ w1p0Submodule mu Ω p ↔ W1p.frontierTraceOfIsLipschitzDomain hp hΩ hb u = 0 := by
  rw [← ClosedSubmodule.mem_toSubmodule_iff, ← W1p.ker_frontierTraceOfIsLipschitzDomain hp hΩ hb,
    LinearMap.mem_ker, ContinuousLinearMap.coe_coe]

/-- **Uniqueness of the trace.** A bounded linear operator from `W^{1,p}(Ω)` to `Lᵖ` of the
frontier that sends the restriction to `Ω` of every test function on the whole space to its
restriction to the frontier is the trace operator. -/
theorem W1p.eq_frontierTraceOfIsLipschitzDomain (hp : p ≠ ⊤)
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F))
    (T : W1p mu Ω p →L[ℝ]
      Lp ℝ p ((μHE[finrank ℝ F - 1] : Measure F).restrict (frontier (Ω : Set F))))
    (hT : ∀ φ : 𝓓((⊤ : Opens F), ℝ),
      T (W1p.restrictL (le_top : Ω ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p φ)) =ᵐ[
        (μHE[finrank ℝ F - 1] : Measure F).restrict (frontier (Ω : Set F))] φ) :
    T = W1p.frontierTraceOfIsLipschitzDomain hp hΩ hb := by
  refine DFunLike.coe_injective <|
    (W1p.denseRange_restrictL_ofTestFunctionₗ_top_of_isLipschitzDomain hp hΩ hb).equalizer
      T.continuous (W1p.frontierTraceOfIsLipschitzDomain hp hΩ hb).continuous
      (funext fun φ => ?_)
  exact Lp.ext ((hT φ).trans (W1p.frontierTraceOfIsLipschitzDomain_ae_eq_of_continuousOn hp hΩ hb
    φ.continuous.continuousOn (W1p.value_restrictL_ofTestFunctionₗ_ae le_top φ)).symm)

variable {E₀ : Type*} [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  [MeasurableSpace E₀] [BorelSpace E₀]

/-- **The trace in rigid coordinates.** Let `Ω` be a bounded Lipschitz domain of a nontrivial
finite-dimensional real inner product space `F`, and let an affine isometry `g` carry `Ω` onto a
bounded Lipschitz domain `W` of the model space `ℝ × E₀`, as a boundary chart of `Ω` does
(`Set.IsLipschitzDomain.exists_isLipschitzDomainWith_image`). For `1 ≤ p < ∞` and
`u ∈ W^{1,p}(Ω)`, the trace of `u` at almost every frontier point `x` is the model-space trace
(`TauCeti.W1p.frontierTrace`) of `u ∘ g⁻¹ ∈ W^{1,p}(W)` at `g x`. So statements about the
model-space trace transfer to `TauCeti.W1p.frontierTraceOfIsLipschitzDomain`. -/
theorem W1p.frontierTraceOfIsLipschitzDomain_ae_eq_frontierTrace_compAffineIsometryEquivL
    (hp : p ≠ ⊤) (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F))
    (g : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E₀)) {W : Opens (WithLp 2 (ℝ × E₀))} {L : ℝ≥0}
    (hW : (W : Set (WithLp 2 (ℝ × E₀))).IsLipschitzDomainWith L)
    (hbW : IsBounded (W : Set (WithLp 2 (ℝ × E₀))))
    (hWΩ : (W : Set (WithLp 2 (ℝ × E₀))) = g.symm ⁻¹' Ω) (u : W1p volume Ω p) :
    W1p.frontierTraceOfIsLipschitzDomain hp hΩ hb u =ᵐ[(μHE[finrank ℝ F - 1] : Measure F).restrict
      (frontier (Ω : Set F))]
      fun x => W1p.frontierTrace hp hW hbW (W1p.compAffineIsometryEquivL g.symm hWΩ u) (g x) := by
  have hΩW : (Ω : Set F) = g ⁻¹' W := by
    rw [hWΩ]; ext; simp
  have hmp := g.measurePreserving_euclideanHausdorffMeasure_finrank_sub_one_restrict_frontier hΩW
  -- The model-space trace read back through `g` is a trace operator, hence the trace.
  let T : W1p volume Ω p →L[ℝ]
      Lp ℝ p ((μHE[finrank ℝ F - 1] : Measure F).restrict (frontier (Ω : Set F))) :=
    (Lp.compMeasurePreservingₗᵢ (E := ℝ) (p := p) ℝ g hmp).toContinuousLinearMap.comp
      ((W1p.frontierTrace hp hW hbW).comp (W1p.compAffineIsometryEquivL g.symm hWΩ))
  have hTu (v : W1p volume Ω p) : T v = Lp.compMeasurePreserving g hmp
      (W1p.frontierTrace hp hW hbW (W1p.compAffineIsometryEquivL g.symm hWΩ v)) := by
    simp only [T, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      Lp.compMeasurePreservingₗᵢ_apply]
  have hT : T = W1p.frontierTraceOfIsLipschitzDomain hp hΩ hb :=
    W1p.eq_frontierTraceOfIsLipschitzDomain hp hΩ hb T fun φ => by
      rw [hTu]
      exact compMeasurePreserving_frontierTrace_compAffineIsometryEquivL_ae_eq hp g hWΩ hW hbW hmp
        φ.continuous.continuousOn (W1p.value_restrictL_ofTestFunctionₗ_ae le_top φ)
  rw [← hT, hTu]
  exact Lp.coeFn_compMeasurePreserving _ hmp

end Intrinsic

end TauCeti
